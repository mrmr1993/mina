(** Global cache configuration for proof conversion.

    When set, all Pickles compile_promise calls will use the specified
    directory for caching proving/verification keys on disk. *)

(** The cache spec list passed to Pickles.compile_promise. *)
let cache : Key_cache.Spec.t list ref = ref []

(** Set the cache directory. Keys will be read from and written to this dir. *)
let set_cache_dir dir =
  cache := [ Key_cache.Spec.On_disk { directory = dir; should_write = true } ]

(** Get the current cache spec. Returns [] if no cache dir is set. *)
let get_cache () = !cache
