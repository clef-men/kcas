type t =
  int

let neg_id =
  Atomic.make (-1)
let neg_ids n =
  Atomic.fetch_and_add neg_id (- n)
let neg_id () =
  neg_ids 1

let pos_id =
  Atomic.make Int.max_int
let pos_ids n =
  Atomic.fetch_and_add pos_id (- n)
let pos_id () =
  pos_ids 1

let id mode =
  if mode == Mode.Obstruction_free then
    pos_id ()
  else
    neg_id ()

let ids mode n =
  if mode == Mode.Obstruction_free then
    pos_ids n
  else
    neg_ids n
let ids mode n =
  ids mode n - (n - 1)

let mode t =
  if t < 0 then
    Mode.Lock_free
  else
    Mode.Obstruction_free

let add t n =
  t + n
