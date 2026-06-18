(*
 * Copyright (c) 2017, Nicolas ASSOUAD <nicolas.assouad@ens.fr>
 * Copyright (c) 2023, Vesa Karvonen <vesa.a.j.k@gmail.com>
 *)

module Retry =
  Retry
module Timeout =
  Timeout

type mode = Mode.t =
  | Lock_free
  | Obstruction_free

type 'a state =
  { mutable before: 'a
  ; mutable after: 'a
  ; mutable which: which
  ; awaiters: Awaiters.t
  }

(** Tagged GADT for representing both the state of MCAS operations and of the
    transaction log or splay [tree].  Different subsets of this GADT are used in
    different contexts.  See the [root], [tree], and [which] existentials. *)
and _ tdt =
  | Before : [> `Before] tdt
    (** The result has been determined to be the [before] value. *)
  | After : [> `After] tdt
    (** The result has been determined to be the [after] value. *)
  | Xt :
    { mutable root: root [@atomic]
    ; timeout: Timeout.t
    ; mode: mode
    ; mutable validate_counter: int
    ; mutable post_commit: Action.t
    } ->
    [> `Xt] tdt
    (** The result might not yet have been determined.  The [root] either says
        which it is or points to the root of the transaction log or [tree].

        Note that if/when local/stack allocation mode becomes available in
        OCaml, the transaction log should be mostly stack allocated. *)
  | Leaf : [> `Leaf] tdt  (** Leaf node in the transaction log or [tree]. *)
  | Node :
    { loc: 'a loc
    ; state: 'a state
    ; lt: tree
    ; gt: tree
    ; mutable awaiters: Awaiters.t
    } ->
    [> `Node] tdt
    (** Branch node in the transaction log or [tree] that specifies a single
        [CAS] or [CMP] operation. *)

and tree =
  T : [< `Leaf | `Node] tdt -> tree
  [@@unboxed]
and root =
  R : [< `Before | `After | `Leaf | `Node] tdt -> root
  [@@unboxed]
and which =
  W : [< `Before | `After | `Xt] tdt -> which
  [@@unboxed]

and 'a loc =
  { mutable state: 'a state [@atomic]
  ; id: Id.t
  }

let tree_as_root : tree -> root =
  Obj.magic
let root_as_tree : root -> tree =
  Obj.magic

let new_state_with_awaiters after awaiters =
  { before= Obj.magic ()
  ; after
  ; which= W After
  ; awaiters
  }
let new_state after =
  new_state_with_awaiters after Awaiters.empty

let make_loc padded state id =
  let record = { state; id } in
  if padded then
    Multicore_magic.copy_as_padded record
  else
    record

let is_node tree =
  tree != T Leaf
let is_cmp which state =
  state.which != W which
let is_cas which state =
  state.which == W which

let is_after (status : [< `Before | `After] tdt) =
  match status with
  | Before ->
      false
  | After ->
      true

let get state success =
  if success then
    state.after
  else
    state.before

let isnt_int x =
  not Obj.(is_int @@ repr x)

let clear_other state (status : [< `Before | `After] tdt) =
  match status with
  | Before ->
      if isnt_int state.after then
        state.after <- Obj.magic ()
  | After ->
      if isnt_int state.before then
        state.before <- Obj.magic ()

let is_determined (Xt xt_r : [`Xt] tdt) =
  match xt_r.root with
  | R Leaf
  | R (Node _) ->
      false
  | R After
  | R Before ->
      true

let rec release_rec which status = function
  | T Leaf ->
      ()
  | T (Node node_r) ->
      release which status (Node node_r)
and release which status (Node node_r : [< `Node] tdt) =
  release_rec which status node_r.lt ;
  let state = node_r.state in
  if is_cas which state then (
    state.which <- W status ;
    clear_other state status ;
    Awaiters.resume node_r.awaiters
  ) ;
  release_rec which status node_r.gt

let rec verify_rec which = function
  | T Leaf ->
      After
  | T (Node node_r) ->
      verify which (Node node_r)
and verify which (Node node_r : [< `Node] tdt) =
  let status = verify_rec which node_r.lt in
  if status == After then
    if is_cmp which node_r.state
    && node_r.loc.state != node_r.state
    then
      Before
    else
      verify_rec which node_r.gt
  else
    status

let finish (Xt xt_r as xt : [`Xt] tdt) root status =
  if Atomic.Loc.compare_and_set [%atomic.loc xt_r.root] (R root) (R status) then (
    release xt status root ;
    is_after status
  ) else (
    xt_r.root == R After
  )

let a_cmp =
  1
let a_cas =
  2
let a_cmp_followed_by_a_cas =
  4

let next_status a_cas_or_a_cmp status =
  let a_cmp_followed_by_a_cas = (a_cas_or_a_cmp * 2) land (status * 4) in
  status lor a_cas_or_a_cmp lor a_cmp_followed_by_a_cas
let rec determine_rec which status = function
  | T Leaf ->
      status
  | T (Node node_r) ->
      determine which status (Node node_r)
and determine which status (Node node_r as node : [< `Node] tdt) =
  let status = determine_rec which status node_r.lt in
  if status < 0 then
    status
  else
    determine_eq Backoff.default which status node
and determine_eq backoff which status (Node node_r as eq : [< `Node] tdt) =
  let current = node_r.loc.state in
  let state = node_r.state in
  if state == current then (
    let a_cas_or_a_cmp = 1 + Bool.to_int (is_cas which state) in
    if is_determined which then
      raise_notrace Exit ;
    determine_rec which (next_status a_cas_or_a_cmp status) node_r.gt
  ) else (
    let matches_expected () =
      let current =
        match current.which with
        | W ((Before | After) as which) ->
            get current (is_after which)
        | W (Xt _ as xt) ->
            get current (determine_bool xt)
      in
      state.before == current
    in
    if is_cas which state && matches_expected () then (
      if is_determined which then
        raise_notrace Exit ;
      (* We now know that the operation wasn't finished when we read [current],
         but it is possible that the [loc]ation has been updated since then by
         some other domain helping us (or even by some later operation).  If so,
         then the [compare_and_set] below fails.  Copying the awaiters from
         [current] is safe in either case, because we know that we have the
         [current] state that our operation is interested in.  By doing the
         copying here, we at most duplicate work already done by some other
         domain.  However, it is necessary to do the copy before the
         [compare_and_set], because afterwards is too late as some other domain
         might finish the operation after the [compare_and_set] and miss the
         awaiters. *)
      if not @@ Awaiters.is_empty current.awaiters then
        node_r.awaiters <- current.awaiters ;
      if Atomic.Loc.compare_and_set [%atomic.loc node_r.loc.state] current state then
        determine_rec which (next_status a_cas status) node_r.gt
      else
        determine_eq (Backoff.once backoff) which status eq
    ) else (
      -1
    )
  )
and determine_bool (Xt xt_r as xt : [`Xt] tdt) =
  match xt_r.root with
  | R Before ->
      false
  | R After ->
      true
  | R Leaf ->
      (* unreachable *)
      true
  | R (Node node_r) ->
      let root = Node node_r in
      match determine xt 0 root with
      | status ->
          finish xt root
            ( if a_cmp_followed_by_a_cas < status then
                verify xt root
              else if 0 <= status then
                After
              else
                Before
            )
      | exception Exit ->
          xt_r.root == R After

let eval state =
  match state.which with
  | W ((Before | After) as which) ->
      get state (is_after which)
  | W (Xt _ as xt) ->
      get state (determine_bool xt)

let make_node loc state lt gt =
  T (Node { loc; state; lt; gt; awaiters= Awaiters.empty })

let rec splay ~hit_parent id = function
  | T Leaf ->
      T Leaf, T Leaf, T Leaf
  | T (Node { loc; state= s; lt= l; gt= r; _ }) as t ->
      if id < loc.id && ((not hit_parent) || is_node l) then
        match l with
        | T Leaf ->
            T Leaf, T Leaf, t
        | T (Node { loc= loc'; state= ps; lt= ll; gt= lr; _ }) ->
            if id < loc'.id && ((not hit_parent) || is_node ll) then
              let lll, n, llr = splay ~hit_parent id ll in
              lll, n, make_node loc' ps llr (make_node loc s lr r)
            else if loc'.id < id && ((not hit_parent) || is_node lr) then
              let lrl, n, lrr = splay ~hit_parent id lr in
              make_node loc' ps ll lrl, n, make_node loc s lrr r
            else
              ll, l, make_node loc s lr r
      else if loc.id < id && ((not hit_parent) || is_node r) then
        match r with
        | T Leaf ->
            t, T Leaf, T Leaf
        | T (Node { loc= loc'; state= ps; lt= rl; gt= rr; _ }) ->
            if id < loc'.id && ((not hit_parent) || is_node rl) then
              let rll, n, rlr = splay ~hit_parent id rl in
              make_node loc s l rll, n, make_node loc' ps rlr rr
            else if loc'.id < id && ((not hit_parent) || is_node rr) then
              let rrl, n, rrr = splay ~hit_parent id rr in
              make_node loc' ps (make_node loc s l rl) rrl, n, rrr
            else
              make_node loc s l rl, r, rr
      else
        l, t, r

let add_awaiter loc before awaiter =
  let state = loc.state in
  if before != eval state then
    false
  else
    let awaiters = Awaiters.add awaiter state.awaiters in
    let new_state = new_state_with_awaiters before awaiters in
    Atomic.Loc.compare_and_set [%atomic.loc loc.state] state new_state

let rec remove_awaiter backoff loc before awaiter =
  let state = loc.state in
  if before == eval state then
    let removed, awaiters = Awaiters.remove awaiter state.awaiters in
    if removed then
      let new_state = new_state_with_awaiters before awaiters in
      if not @@ Atomic.Loc.compare_and_set [%atomic.loc loc.state] state new_state then
        remove_awaiter (Backoff.once backoff) loc before awaiter
let remove_awaiter loc before awaiter =
  remove_awaiter Backoff.default loc before awaiter

let block timeout loc before =
  let t = Domain_local_await.prepare_for_await () in
  let alive = Timeout.await timeout t.release in
  if add_awaiter loc before t.release then (
    try
      t.await ()
    with cancellation_exn ->
      remove_awaiter loc before t.release ;
      Timeout.cancel_alive alive ;
      raise cancellation_exn
  ) ;
  Timeout.unawait timeout alive

let rec update_with_state timeout backoff loc new_state fn =
  let state = loc.state in
  let before = eval state in
  match fn before with
  | after ->
      if before == after then (
        Timeout.cancel timeout ;
        before
      ) else (
        new_state.after <- after ;
        if Atomic.Loc.compare_and_set [%atomic.loc loc.state] state new_state then (
          Awaiters.resume state.awaiters ;
          Timeout.cancel timeout ;
          before
        ) else (
          update_with_state timeout (Backoff.once backoff) loc new_state fn
        )
      )
  | exception Retry.Later ->
      block timeout loc before ;
      update_with_state timeout backoff loc new_state fn
  | exception exn ->
      Timeout.cancel timeout ;
      raise exn
let update timeout backoff loc fn =
  let state = loc.state in
  let before = eval state in
  match fn before with
  | after ->
      if before == after then (
        Timeout.cancel timeout ;
        before
      ) else (
        let new_state = new_state after in
        if Atomic.Loc.compare_and_set [%atomic.loc loc.state] state new_state then (
          Awaiters.resume state.awaiters ;
          Timeout.cancel timeout ;
          before
        ) else (
          update_with_state timeout (Backoff.once backoff) loc new_state fn
        )
      )
  | exception Retry.Later ->
      let new_state = new_state before in
      block timeout loc before ;
      update_with_state timeout backoff loc new_state fn
  | exception exn ->
      Timeout.cancel timeout ;
      raise exn

let rec exchange_with_state backoff loc new_state =
  let state = loc.state in
  let before = eval state in
  if before == new_state.after then (
    before
  ) else if Atomic.Loc.compare_and_set [%atomic.loc loc.state] state new_state then (
    Awaiters.resume state.awaiters ;
    before
  ) else (
    exchange_with_state (Backoff.once backoff) loc new_state
  )
let exchange backoff loc v =
  exchange_with_state backoff loc (new_state v)

let rec compare_and_set_with_state backoff loc before new_state =
  let state = loc.state in
  before == eval state &&
  ( before == new_state.after
    ||
     if Atomic.Loc.compare_and_set [%atomic.loc loc.state] state new_state then (
       Awaiters.resume state.awaiters ;
       true
     ) else (
       (* We must retry, because compare is by value rather than by state.  In
          other words, we should not fail spuriously due to some other thread
          having installed or removed a waiter. *)
       compare_and_set_with_state (Backoff.once backoff) loc before new_state
     )
  )
let compare_and_set backoff loc before after =
  compare_and_set_with_state backoff loc before (new_state after)

module Loc = struct
  type !'a t =
    'a loc

  let make ?(padded = false) ?(mode = Obstruction_free) after =
    let state = new_state after in
    let id = Id.id mode in
    make_loc padded state id

  let make_contended ?mode after =
    make ~padded:true ?mode after

  let make_array ?(padded = false) ?(mode = Obstruction_free) n after =
    assert (0 <= n) ;
    let state = new_state after in
    let id = Id.ids mode n in
    Array.init n @@ fun i ->
      make_loc padded state (Id.add id i)

  let mode t =
    Id.mode t.id

  let get t =
    eval t.state

  let rec get_as timeout fn t =
    let before = eval t.state in
    match fn before with
    | v ->
        Timeout.cancel timeout ;
        v
    | exception Retry.Later ->
        block timeout t before ;
        get_as timeout fn t
    | exception exn ->
        Timeout.cancel timeout ;
        raise exn
  let get_as ?timeoutf fn t =
    get_as (Timeout.alloc timeoutf) fn t

  let compare_and_set ?(backoff = Backoff.default) t before after =
    compare_and_set backoff t before after

  let update ?timeoutf ?(backoff = Backoff.default) t fn =
    let timeout = Timeout.alloc timeoutf in
    update timeout backoff t fn

  let modify ?timeoutf ?backoff t fn =
    update ?timeoutf ?backoff t fn |> ignore

  let exchange ?(backoff = Backoff.default) t v =
    exchange backoff t v

  let set ?backoff t v =
    exchange ?backoff t v |> ignore

  let fetch_and_add ?backoff t n =
    if n == 0 then
      get t
    else
      update ?backoff t ((+) n)
  let fetch_and_add' ?backoff t n =
    fetch_and_add ?backoff t n |> ignore

  let incr ?backoff t =
    fetch_and_add' ?backoff t 1
  let decr ?backoff t =
    fetch_and_add' ?backoff t (-1)

  let has_awaiters t =
    not @@ Awaiters.is_empty t.state.awaiters
end

module Xt = struct
  type 'x t =
    [`Xt] tdt

  let impossible () =
    failwith "impossible"
  let invalid_retry () =
    failwith "kcas: invalid use of retry"

  let validate_one which loc state =
    let before =
      if is_cmp which state then
        eval state
      else
        state.before
    in
    if before != eval loc.state then
      Retry.invalid ()

  let rec validate_all which = function
    | T Leaf ->
        ()
    | T (Node node_r) ->
        validate_all which node_r.lt ;
        validate_one which node_r.loc node_r.state ;
        validate_all which node_r.gt

  let is_obstruction_free (Xt xt_r : _ t) loc =
    xt_r.mode == Obstruction_free &&
    Id.mode loc.id == Obstruction_free

  type (_, _) update =
    | Compare_and_swap : ('a * 'a, 'a) update
    | Fetch_and_add : (int, int) update
    | Function : ('a -> 'a, 'a) update
    | Exchange : ('a, 'a) update
    | Get : (unit, 'a) update

  let update_new : type c a. _ -> a loc -> c -> (c, a) update -> _ -> _ -> a =
    fun (Xt xt_r as xt : _ t) loc c up lt gt ->
      let state = loc.state in
      let before = eval state in
      let after : a =
        match up with
        | Compare_and_swap ->
            if fst c == before then
              snd c
            else
              before
        | Fetch_and_add ->
            before + c
        | Function ->
            let root = xt_r.root in
            begin match c before with
            | after ->
                assert (root == xt_r.root) ;
                after
            | exception exn ->
                assert (root == xt_r.root) ;
                xt_r.root <- R (Node { loc; state; lt; gt; awaiters= Awaiters.empty }) ;
                raise exn
            end
        | Exchange ->
            c
        | Get ->
            before
      in
      let state =
        if before == after && is_obstruction_free xt loc then
          state
        else
          { before; after; which= W xt; awaiters= Awaiters.empty }
      in
      xt_r.root <- R (Node { loc; state; lt; gt; awaiters= Awaiters.empty }) ;
      before

  let update_old : type c a. _ -> a loc -> c -> (c, a) update -> _ -> _ -> _ -> a =
    fun (Xt xt_r as xt : _ t) loc c up lt gt state' ->
      let c0 = xt_r.validate_counter in
      let c1 = c0 + 1 in
      xt_r.validate_counter <- c1 ;
      (* Validate whenever counter reaches next power of 2.
         The assumption is that potentially infinite loops will repeatedly access
         the same locations. *)
      if c0 land c1 = 0 then (
        Timeout.check xt_r.timeout ;
        validate_all xt (root_as_tree xt_r.root)
      ) ;
      let state : a state = Obj.magic state' in
      if is_cmp xt state then (
        let current = eval state in
        let after : a =
          match up with
          | Compare_and_swap ->
              if fst c == current then
                snd c
              else
                current
          | Fetch_and_add ->
              current + c
          | Function ->
              let root = xt_r.root in
              let after = c current in
              assert (root == xt_r.root) ;
              after
          | Exchange ->
              c
          | Get ->
              current
        in
        let state =
          if current == after then
            state
          else
            { before= current
            ; after
            ; which= W xt
            ; awaiters= Awaiters.empty
            }
        in
        xt_r.root <- R (Node { loc; state; lt; gt; awaiters= Awaiters.empty }) ;
        current
      ) else (
        let current = state.after in
        let after : a =
          match up with
          | Compare_and_swap ->
              if fst c == current then
                snd c
              else
                current
          | Fetch_and_add -> current + c
          | Function ->
              let root = xt_r.root in
              let after = c current in
              assert (root == xt_r.root) ;
              after
          | Exchange ->
              c
          | Get ->
              current
        in
        let state =
          if current == after then
            state
          else
            { before= state.before
            ; after
            ; which= W xt
            ; awaiters= Awaiters.empty
            }
        in
        xt_r.root <- R (Node { loc; state; lt; gt; awaiters= Awaiters.empty }) ;
        current
      )

  let update_as ~xt:(Xt xt_r as xt : _ t) loc c up =
    let id = loc.id in
    match root_as_tree xt_r.root with
    | T Leaf ->
        update_new xt loc c up (T Leaf) (T Leaf)
    | T (Node { loc= loc'; lt= T Leaf; _ }) as tree when id < loc'.id ->
        update_new xt loc c up (T Leaf) tree
    | T (Node { loc= loc'; gt= T Leaf; _ }) as tree when loc'.id < id ->
        update_new xt loc c up tree (T Leaf)
    | T (Node { loc= loc'; state; lt; gt; _ }) when Obj.magic loc' == loc ->
        update_old xt loc c up lt gt state
    | tree ->
        match splay ~hit_parent:false id tree with
        | lt, T Leaf, gt ->
            update_new xt loc c up lt gt
        | lt, T (Node node_r), gt ->
            update_old xt loc c up lt gt node_r.state

  let get ~xt loc =
    update_as ~xt loc () Get

  let exchange ~xt loc after =
    update_as ~xt loc after Exchange
  let set ~xt loc after =
    exchange ~xt loc after |> ignore

  let compare_and_swap ~xt loc before after =
    update_as ~xt loc (before, after) Compare_and_swap
  let compare_and_set ~xt loc before after =
    compare_and_swap ~xt loc before after == before

  let fetch_and_add ~xt loc n =
    update_as ~xt loc n Fetch_and_add
  let incr ~xt loc =
    update_as ~xt loc 1 Fetch_and_add |> ignore
  let decr ~xt loc =
    update_as ~xt loc (-1) Fetch_and_add |> ignore

  let update ~xt loc fn =
    update_as ~xt loc fn Function
  let modify ~xt loc fn =
    update ~xt loc fn |> ignore

  let swap ~xt loc1 loc2 =
    get ~xt loc1
    |> exchange ~xt loc2
    |> set ~xt loc1

  let to_blocking ~xt tx =
    match tx ~xt with
    | None ->
        Retry.later ()
    | Some v ->
        v

  let to_nonblocking ~xt tx =
    match tx ~xt with
    | v ->
        Some v
    | exception Retry.Later ->
        None

  let post_commit ~xt:(Xt xt_r : _ t) action =
    xt_r.post_commit <- Action.add action xt_r.post_commit

  type _ op =
    | Validate : unit op
    | Is_in_log : bool op

  let do_op : type r. xt:'x t -> 'a Loc.t -> r op -> r =
    fun ~xt:(Xt xt_r as xt) loc op ->
      let id = loc.id in
      match root_as_tree xt_r.root with
      | T Leaf ->
          begin match op with
          | Validate ->
              ()
          | Is_in_log ->
              false
          end
      | T (Node { loc= loc'; lt= T Leaf; _ }) when id < loc'.id ->
          begin match op with
          | Validate ->
              ()
          | Is_in_log ->
              false
          end
      | T (Node { loc= loc'; gt= T Leaf; _ }) when loc'.id < id ->
          begin match op with
          | Validate ->
              ()
          | Is_in_log ->
              false
          end
      | T (Node { loc= loc'; state; _ }) when Obj.magic loc' == loc ->
          begin match op with
          | Validate ->
              validate_one xt loc' state
          | Is_in_log ->
              true
          end
      | tree ->
          match splay ~hit_parent:true id tree with
          | lt, T (Node node_r), gt ->
              xt_r.root <- R (Node { node_r with lt; gt; awaiters= Awaiters.empty }) ;
              begin match op with
              | Validate ->
                  if Obj.magic node_r.loc == loc then
                    validate_one xt node_r.loc node_r.state
              | Is_in_log ->
                  Obj.magic node_r.loc == loc
              end
          | _, T Leaf, _ ->
              impossible ()

  let validate ~xt loc =
    do_op ~xt loc Validate

  let is_in_log ~xt loc =
    do_op ~xt loc Is_in_log

  type 'x snap =
    tree * Action.t

  let snapshot ~xt:(Xt xt_r : _ t) =
    root_as_tree xt_r.root, xt_r.post_commit

  let rec rollback which tree_snap tree =
    if tree_snap == tree then
      tree
    else
      match tree with
      | T Leaf ->
          T Leaf
      | T (Node node_r) ->
          match splay ~hit_parent:false node_r.loc.id tree_snap with
          | lt_mark, T Leaf, gt_mark ->
              let lt = rollback which lt_mark node_r.lt in
              let gt = rollback which gt_mark node_r.gt in
              let state =
                let state = node_r.state in
                if is_cmp which state then
                  state
                else
                  let current = node_r.loc.state in
                  if state.before != eval current then
                    Retry.invalid ()
                  else
                    current
              in
              T (Node { loc= node_r.loc; state; lt; gt; awaiters= Awaiters.empty })
          | lt_mark, T (Node inner_node_r), gt_mark ->
              let lt = rollback which lt_mark node_r.lt in
              let gt = rollback which gt_mark node_r.gt in
              T (Node { inner_node_r with lt; gt; awaiters= Awaiters.empty })
  let rollback ~xt:(Xt xt_r as xt : _ t) (snap, post_commit) =
    xt_r.root <- tree_as_root (rollback xt snap (root_as_tree xt_r.root)) ;
    xt_r.post_commit <- post_commit

  let rec first ~xt tx = function
    | [] ->
        tx ~xt
    | tx' :: txs ->
        match tx ~xt with
        | v ->
            v
        | exception Retry.Later ->
            first ~xt tx' txs
  let first ~xt = function
    | [] ->
        Retry.later ()
    | tx :: txs ->
        first ~xt tx txs

  type 'a tx =
    { tx: 'x. xt:'x t -> 'a
    }
    [@@unboxed]

  let call ~xt { tx } =
    tx ~xt

  let rec add_awaiters_rec awaiter which = function
    | T Leaf ->
        T Leaf
    | T (Node node_r) ->
        add_awaiters awaiter which (Node node_r)
  and add_awaiters awaiter which (Node node_r as stop : [< `Node] tdt) =
    match add_awaiters_rec awaiter which node_r.lt with
    | T Leaf ->
        let state = node_r.state in
        if
          add_awaiter
            node_r.loc
            (if is_cmp which state then eval state else state.before)
            awaiter
        then
          add_awaiters_rec awaiter which node_r.gt
        else
          T stop
    | T (Node _) as stop ->
        stop

  let rec remove_awaiters_rec awaiter which stop = function
    | T Leaf ->
        T Leaf
    | T (Node node_r) ->
        remove_awaiters awaiter which stop (Node node_r)
  and remove_awaiters awaiter which stop (Node node_r as at : [< `Node] tdt) =
    match remove_awaiters_rec awaiter which stop node_r.lt with
    | T Leaf ->
        if T at != stop then (
          let state = node_r.state in
          remove_awaiter
            node_r.loc
            (if is_cmp which state then eval state else state.before)
            awaiter ;
          remove_awaiters_rec awaiter which stop node_r.gt
        ) else (
          stop
        )
    | T (Node _) as stop ->
        stop
  let remove_awaiters awaiter which stop at =
    remove_awaiters awaiter which stop at |> ignore

  let initial_validate_period =
    4

  let create timeout mode =
    Xt
    { root= R Leaf
    ; timeout
    ; mode
    ; validate_counter= initial_validate_period
    ; post_commit= Action.noop
    }

  let reset (Xt xt_r : _ t) =
    xt_r.root <- R Leaf ;
    xt_r.validate_counter <- initial_validate_period ;
    xt_r.post_commit <- Action.noop

  let success (Xt xt_r : _ t) res =
    Timeout.cancel xt_r.timeout ;
    Action.run xt_r.post_commit ;
    res
  let rec commit backoff (Xt xt_r as xt : _ t) tx =
    match tx ~xt with
    | res ->
        begin match root_as_tree xt_r.root with
        | T Leaf ->
            success xt res
        | T (Node { loc; state; lt= T Leaf; gt= T Leaf; _ }) ->
            if is_cmp xt state then (
              success xt res
            ) else (
              state.which <- W After ;
              let before = state.before in
              if isnt_int before then
                state.before <- Obj.magic () ;
              if compare_and_set_with_state Backoff.default loc before state then
                success xt res
              else
                commit_reuse_once backoff xt tx
            )
        | T (Node node_r) ->
            let root = Node node_r in
            begin match determine xt 0 root with
            | status ->
                if a_cmp_followed_by_a_cas < status then (
                  if finish xt root (verify xt root) then
                    success xt res
                  else
                    commit_reset backoff Lock_free xt tx
                ) else (
                    if a_cmp = status
                    || finish xt root (if 0 <= status then After else Before)
                  then
                    success xt res
                  else
                    commit_reset backoff xt_r.mode xt tx
                )
            | exception Exit ->
                if xt_r.root == R After then
                  success xt res
                else
                  commit_reset backoff xt_r.mode xt tx
            end
        end
    | exception Retry.Invalid ->
        commit_reuse_once backoff xt tx
    | exception Retry.Later ->
        begin match root_as_tree xt_r.root with
        | T Leaf ->
            invalid_retry ()
        | T (Node node_r) ->
            let root = Node node_r in
            let dla = Domain_local_await.prepare_for_await () in
            let alive = Timeout.await xt_r.timeout dla.release in
            match add_awaiters dla.release xt root with
            | T Leaf ->
                begin match dla.await () with
                | () ->
                    remove_awaiters dla.release xt (T Leaf) root ;
                    Timeout.unawait xt_r.timeout alive ;
                    commit_reuse_reset backoff xt tx
                | exception cancellation_exn ->
                    remove_awaiters dla.release xt (T Leaf) root ;
                    Timeout.cancel_alive alive ;
                    raise cancellation_exn
                end
            | T (Node _) as stop ->
                remove_awaiters dla.release xt stop root ;
                Timeout.unawait xt_r.timeout alive ;
                commit_reuse_once backoff xt tx
        end
    | exception exn ->
        Timeout.cancel xt_r.timeout ;
        raise exn
  and commit_reuse backoff (Xt xt_r as xt : _ t) tx =
    reset xt ;
    Timeout.check xt_r.timeout ;
    commit backoff xt tx
  and commit_reuse_once backoff xt tx =
    commit_reuse (Backoff.once backoff) xt tx
  and commit_reuse_reset backoff xt tx =
    commit_reuse (Backoff.reset backoff) xt tx
  and commit_reset backoff mode (Xt xt_r : _ t) tx =
    let backoff = Backoff.once backoff in
    Timeout.check xt_r.timeout ;
    let xt = create xt_r.timeout mode in
    commit backoff xt tx

  let commit ?timeoutf ?(backoff = Backoff.default) ?(mode = Obstruction_free) { tx } =
    let timeout = Timeout.alloc timeoutf in
    let xt = create timeout mode in
    commit backoff xt tx
end
