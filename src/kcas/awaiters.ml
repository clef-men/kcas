let[@tail_mod_cons] rec remove_first x removed = function
  | [] ->
      removed := false ;
      []
  | x' :: xs ->
      if x == x' then
        xs
      else
        x' :: remove_first x removed xs
let remove_first x xs =
  let removed = ref true in
  let xs = remove_first x removed xs in
  !removed, xs

type awaiter =
  unit -> unit

type t =
  awaiter list

let empty =
  []

let is_empty t =
  t == []

let add awaiter t =
  awaiter :: t

let remove =
  remove_first

let resume =
  List.iter (fun awaiter -> awaiter ())
