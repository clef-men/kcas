type t

val id :
  Mode.t -> t
val ids :
  Mode.t -> int -> t

val mode :
  t -> Mode.t

val add :
  t -> int -> t
