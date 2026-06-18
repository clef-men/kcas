type t

val noop :
  t

val add :
  (unit -> unit) -> t -> t

val run :
  t -> unit
