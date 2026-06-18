exception Later

let later () =
  raise_notrace Later
let unless condition =
  if not condition then
    later ()

exception Invalid

let invalid () =
  raise_notrace Invalid
