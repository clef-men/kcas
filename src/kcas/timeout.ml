exception Timeout

let timeout () =
  raise Timeout

type state =
  | Elapsed
  | Call of (unit -> unit)

type _ tdt =
  | Unset : [> `Unset] tdt
  | Set :
    { mutable state : state [@atomic]
    } ->
    [> `Set] tdt

type t =
  [`Unset | `Set] tdt

type alive =
  state

let check t =
  match t with
  | Unset ->
      ()
  | Set set_r ->
      if set_r.state == Elapsed then
        timeout ()

let call_id =
  Call Fun.id
let alloc timeoutf =
  let (Set set_r as t : [`Set] tdt) = Set { state= call_id } in
  let cancel =
    Domain_local_timeout.set_timeoutf timeoutf @@ fun () ->
      match Atomic.Loc.exchange [%atomic.loc set_r.state] Elapsed with
      | Elapsed ->
          (* unreachable *)
          ()
      | Call release_or_cancel ->
          release_or_cancel ()
  in
  if not @@ Atomic.Loc.compare_and_set [%atomic.loc set_r.state] call_id (Call cancel) then
    timeout () ;
  t
let alloc = function
  | None ->
      Unset
  | Some timeoutf ->
      alloc timeoutf

let await (Set set_r : [< `Set] tdt) release =
  match set_r.state with
  | Elapsed ->
      timeout ()
  | Call cancel as alive ->
      if Atomic.Loc.compare_and_set [%atomic.loc set_r.state] alive (Call release) then
        Call cancel
      else
        timeout ()
let await t release =
  match t with
  | Unset ->
      Elapsed
  | Set _ as t ->
      await t release

let unawait (Set set_r : [< `Set] tdt) alive =
  match set_r.state with
  | Elapsed ->
      timeout ()
  | Call _ as await ->
      if not @@ Atomic.Loc.compare_and_set [%atomic.loc set_r.state] await alive then
        timeout ()
let unawait t alive =
  match t with
  | Unset ->
      ()
  | Set _ as t ->
      unawait t alive

let cancel_alive alive =
  match alive with
  | Elapsed ->
      ()
  | Call cancel ->
      cancel ()

let cancel t =
  match t with
  | Unset ->
      ()
  | Set set_r ->
      match set_r.state with
      | Elapsed ->
          ()
      | Call cancel ->
          cancel ()
