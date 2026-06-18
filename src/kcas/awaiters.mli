type awaiter =
  unit -> unit

type t

val empty :
  t

val is_empty :
  t -> bool

val add :
  awaiter -> t -> t

val remove :
  awaiter -> t -> bool * t

val resume :
  t -> unit
