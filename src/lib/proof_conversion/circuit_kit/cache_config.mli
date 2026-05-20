(** Global cache configuration for proof conversion.

    When a directory is set, all Pickles [compile_promise] calls in the
    proof-conversion libraries cache proving/verification keys to disk
    there, so long-lived daemon workers avoid recompiling. *)

(** Set the cache directory. Keys are read from and written to it. *)
val set_cache_dir : string -> unit

(** The current cache spec passed to [Pickles.compile_promise], or [[]]
    if no directory has been set. *)
val get_cache : unit -> Key_cache.Spec.t list
