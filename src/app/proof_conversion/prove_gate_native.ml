(* Native cross-process admission control for the kimchi FFI prover.

   When [PICKLES_PROVE_SLOTS=K] is set, install a gate (K [flock] files in the
   shared socket dir) so that at most K pickles proofs hold the multi-threaded
   prover at once -- bounding both core oversubscription and peak RAM -- while
   the single-threaded witness generation of every other worker runs freely.

   This module deliberately does NOT [open Core_kernel], so it sees the standard
   [Unix] module (file locks). It is injected into pickles via the JS-safe
   [Pickles.Common.Prove_gate] hook, keeping pickles core Unix-free. *)

let setup ~socket_path =
  match Sys.getenv_opt "PICKLES_PROVE_SLOTS" with
  | None -> ()
  | Some s -> (
      match int_of_string_opt s with
      | None | Some 0 ->
          ()
      | Some k ->
          let dir =
            match Sys.getenv_opt "PICKLES_PROVE_SLOT_DIR" with
            | Some d ->
                d
            | None ->
                Filename.dirname socket_path
          in
          (* Grab the first free of [k] slot locks; returns the held fd or None.
             An fcntl write-lock is released when the fd is closed or the holding
             process dies, so a crashed worker never leaks a slot. *)
          let try_grab () =
            let rec go i =
              if i >= k then None
              else
                let path =
                  Filename.concat dir (Printf.sprintf "prove_slot.%d" i)
                in
                let fd = Unix.openfile path [ Unix.O_CREAT; Unix.O_RDWR ] 0o644 in
                match Unix.lockf fd Unix.F_TLOCK 0 with
                | () ->
                    Some fd
                | exception _ ->
                    Unix.close fd ;
                    go (i + 1)
            in
            go 0
          in
          let timing = Sys.getenv_opt "GATE_TIMING" <> None in
          let wrap_priority = Sys.getenv_opt "GATE_WRAP_PRIORITY" <> None in
          (* When [wrap_priority], a waiting wrap registers a marker file here so
             that steps (which start new proofs) defer to it -- finishing
             committed proofs before admitting less-important new ones. *)
          let wrap_dir = Filename.concat dir "wrap_waiting" in
          ( try Unix.mkdir wrap_dir 0o755 with _ -> () ) ;
          let wraps_waiting () =
            try Array.length (Sys.readdir wrap_dir) > 0 with _ -> false
          in
          Printf.eprintf "Prove daemon: admission gate ON (%d slots in %s%s)\n%!"
            k dir
            (if wrap_priority then ", wrap-priority" else "") ;
          Pickles.Common.Prove_gate.acquire :=
            fun stage ->
              Promise.run_in_thread (fun () ->
                  let t0 = Unix.gettimeofday () in
                  let is_wrap = String.equal stage "wrap" in
                  let marker =
                    if wrap_priority && is_wrap then (
                      try Some (Filename.temp_file ~temp_dir:wrap_dir "w" "")
                      with _ -> None )
                    else None
                  in
                  let rec loop () =
                    if wrap_priority && (not is_wrap) && wraps_waiting () then (
                      Unix.sleepf 0.02 ;
                      loop () )
                    else
                      match try_grab () with
                      | Some fd ->
                          fd
                      | None ->
                          Unix.sleepf 0.02 ;
                          loop ()
                  in
                  let fd = loop () in
                  ( match marker with
                  | Some m -> ( try Sys.remove m with _ -> () )
                  | None -> () ) ;
                  if timing then
                    Printf.eprintf "[gate] %s acquired after %.0f ms wait\n%!"
                      stage
                      ((Unix.gettimeofday () -. t0) *. 1000.) ;
                  fun () ->
                    ( try Unix.lockf fd Unix.F_ULOCK 0 with _ -> () ) ;
                    try Unix.close fd with _ -> () ) )
