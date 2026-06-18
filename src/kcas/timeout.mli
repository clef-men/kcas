exception Timeout

type alive

type t

val check :
  t -> unit

val alloc :
  float option -> t

val await :
  t -> (unit -> unit) -> alive

val unawait :
  t -> alive -> unit

val cancel_alive :
  alive -> unit

val cancel :
  t -> unit
