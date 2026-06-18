type t =
  unit -> unit

let noop () =
  ()

let add action t =
  if t == noop then
    action
  else
    fun () ->
      t () ;
      action ()

let run t =
  t ()
