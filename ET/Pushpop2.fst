module Pushpop2
open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module MO = LowStar.Modifies
open LowStar.BufferOps
open FStar.HyperStack.ST

#set-options "--__no_positivity"
noeq type rnode (a:eqtype) = B.pointer_or_null (node a)
and node (a:eqtype) = 
{
    data:a;
    next:rnode a;
}


val well_formed: #a:eqtype -> h:HS.mem -> c:rnode a -> l: G.erased (list a) -> GTot Type0 (decreases (G.reveal l))
let rec well_formed #a h c l
= B.live h c /\ (
  match G.reveal l with
  | [] -> B.g_is_null c
  | a :: q ->
    B.length c == 1 /\ (
    let { data=data; next=next } = B.get h c 0 in
    a == data /\
    well_formed h next (G.hide q)
  ))

val well_formed_lemma: #a:eqtype-> h:HS.mem -> c:rnode a -> l: G.erased (list a)
  -> Lemma(requires(well_formed #a h c l)) (ensures( B.g_is_null c <==> L.isEmpty (G.reveal l))) [SMTPat(well_formed #a h c l)]
let well_formed_lemma #a h c l = ()

val well_formed_lemma2: #a:eqtype-> h:HS.mem -> c:rnode a -> l: G.erased (list a)
  -> Lemma(requires(well_formed #a h c l /\ not(B.g_is_null c))) (ensures( (B.get h c 0).data == L.hd l)) [SMTPat(well_formed #a h c l)]
let well_formed_lemma2 #a h c l = ()

assume val well_formed_lemma3: #a:eqtype -> h:HS.mem -> c1:rnode a -> l1: G.erased (list a) -> c2:rnode a -> l2: G.erased (list a)
  -> Lemma(requires(well_formed #a h c1 l1 /\ well_formed #a h c2 l2)) (ensures( (c1 == c2) <==> (l1 == l2))) [SMTPat (well_formed h c1 l1); SMTPat (well_formed h c2 l2) ] 
//let well_formed_lemma3 #a h c1 l1 c2 l2 = ()

val length_functional: #a:eqtype -> h:HS.mem -> c:rnode a -> l1:G.erased (list a) -> l2:G.erased (list a)
-> Lemma (requires (well_formed h c l1 /\ well_formed h c l2)) (ensures (l1 == l2))
    (decreases (G.reveal l1))[SMTPat (well_formed h c l1); SMTPat (well_formed h c l2) ] 
let rec length_functional #a h c l1 l2 =
  if B.g_is_null c
  then ()
  else
    let { next = next } = B.get h c 0 in
    length_functional h next (G.hide (L.tl (G.reveal l1))) (G.hide (L.tl (G.reveal l2)))

#set-options "--max_ifuel 1 --max_fuel 2"
val footprint: #a: eqtype -> h: HS.mem -> c: rnode a -> l: G.erased (list a) -> Ghost MO.loc
  (requires (well_formed h c l ))
  (ensures (fun refs -> True))
  (decreases (G.reveal l))
let rec footprint #a h c l =
  if B.g_is_null c
  then MO.loc_none
  else
    let {next = next} = B.get h c 0 in
    let refs = footprint h next (G.hide (L.tl (G.reveal l))) in
    MO.loc_union (MO.loc_buffer c) refs
#reset-options "--max_ifuel 1 --max_fuel 2"

(*
let rec footprintDataEqual #a h c1 l1 c2 l2 =
  if not(B.g_is_null c1) && not(B.g_is_null c2) then 
    footprintDataEqual #a h (B.get h c1 0).next (G.hide(L.tl (G.reveal l1))) (B.get h c2 0).next (G.hide(L.tl (G.reveal l2)))
  else ()
*)

val modifies_disjoint_footprint: #a:eqtype -> h:HS.mem -> c:rnode a -> l:G.erased (list a) -> r:MO.loc -> h':HS.mem 
 -> Lemma (requires ( well_formed h c l /\ MO.loc_disjoint r (footprint h c l) /\ MO.modifies r h h' ))
  (ensures ( well_formed h' c l /\ ((footprint h' c l) == (footprint h c l )))) (decreases (G.reveal l))
let rec modifies_disjoint_footprint #a h c l r h'
= if B.g_is_null c
  then ()
  else begin
    let {next = next;} = B.get h c 0 in
    modifies_disjoint_footprint h next (G.hide (L.tl (G.reveal l))) r h'
  end

val well_formed_distinct_lengths_disjoint: #a:eqtype -> c1: B.pointer (node a) -> c2: B.pointer (node a) -> l1: G.erased (list a) -> l2: G.erased (list a) -> h: HS.mem
    -> Lemma(requires ( well_formed h c1 l1 /\ well_formed h c2 l2 /\ ((L.length (G.reveal l1) <> L.length (G.reveal l2)) )))
  (ensures ( B.disjoint c1 c2 ))
  (decreases (L.length (G.reveal l1) + L.length (G.reveal l2)))

let rec well_formed_distinct_lengths_disjoint #a c1 c2 l1 l2 h
    = let {next = next1;} = B.get h c1 0 in
    let {next = next2;} = B.get h c2 0 in
    let f1 () : Lemma (next1 =!= next2) = 
        if B.g_is_null next1 || B.g_is_null next2
        then ()
        else
        well_formed_distinct_lengths_disjoint next1 next2 (G.hide (L.tl (G.reveal l1))) (G.hide (L.tl (G.reveal l2))) h
    in
    f1 ();
    B.pointer_distinct_sel_disjoint c1 c2 h

val well_formed_gt_lengths_disjoint_from_list: #a:eqtype -> h:HS.mem -> c1: B.pointer_or_null (node a) -> c2: B.pointer_or_null (node a)
    -> l1: G.erased (list a) -> l2: G.erased (list a)
    -> Lemma (requires (well_formed h c1 l1 /\ well_formed h c2 l2 /\ ((L.length (G.reveal l1) > L.length (G.reveal l2)))))
  (ensures (MO.loc_disjoint (MO.loc_buffer c1) (footprint h c2 l2))) (decreases (G.reveal l2))
let rec well_formed_gt_lengths_disjoint_from_list #a h c1 c2 l1 l2 = 
    (match G.reveal l2 with
    | [] -> ()
    | _ ->
        well_formed_distinct_lengths_disjoint c1 c2 l1 l2 h;
        well_formed_gt_lengths_disjoint_from_list h c1 (B.get h c2 0).next l1 (G.hide (L.tl (G.reveal l2))))

val well_formed_head_tail_disjoint: #a:eqtype -> h:HS.mem -> c:B.pointer (node a) -> l:G.erased (list a)
    ->  Lemma (requires (well_formed h c l)) 
    (ensures ( MO.loc_disjoint (MO.loc_buffer c) (footprint h (B.get h c 0).next (G.hide (L.tl (G.reveal l))))))
let well_formed_head_tail_disjoint #a h c l
= well_formed_gt_lengths_disjoint_from_list h c (B.get h c 0).next l (G.hide (L.tl (G.reveal l)))

val unused_in_well_formed_disjoint_from_list: #a:Type -> #b:eqtype -> h: HS.mem -> r:B.buffer a -> c: B.pointer_or_null (node b) -> l:G.erased (list b)
 ->  Lemma(requires (r `B.unused_in` h /\ well_formed h c l))
  (ensures (MO.loc_disjoint (MO.loc_buffer r) (footprint h c l)))
  (decreases (G.reveal l))
let rec unused_in_well_formed_disjoint_from_list #a #b h r c l
= (match G.reveal l with
  | [] -> ()
  | _ -> unused_in_well_formed_disjoint_from_list #a #b h r (B.get h c 0).next (G.hide (L.tl (G.reveal l))))


val pop: (#a: eqtype) -> (#n: G.erased (list a)) -> (pl: B.pointer (rnode a)) ->
  Stack a
  (requires (fun h ->
    let l = B.get h pl 0 in
    B.live h pl /\
    well_formed h l n /\
    MO.loc_disjoint (MO.loc_buffer pl) (footprint h l n) /\
    Cons? (G.reveal n)
  ))
  (ensures (fun h0 v h1 ->
    let l = B.get h1 pl 0 in
    let ns = G.reveal n in  
    match ns with
    | hd::tl -> 
    let n' = G.hide tl in
    B.live h1 pl /\
    MO.modifies (MO.loc_buffer pl) h0 h1 /\
    well_formed h1 l n' /\
    MO.loc_disjoint (MO.loc_buffer pl) (footprint h1 l n')
  ))

let pop #a #n pl =
  let l = !* pl in
  let lcell = !* l in
  let h0 = get () in
  pl *= lcell.next;
  let h1 = get () in
  well_formed_head_tail_disjoint h0 l n;
  modifies_disjoint_footprint h0 l n (MO.loc_buffer pl) h1;
  lcell.data


noeq type pointers_content_data (a:eqtype) =
  | Content:
    l:G.erased (list a) -> 
    pl: rnode a -> 
    pointers_content_data a

type pointers_data (a:eqtype) = B.pointer (pointers_content_data a)

val well_formed_pointers_content_data_base: #a:eqtype -> h:HS.mem -> d:pointers_content_data a -> GTot Type0
let well_formed_pointers_content_data_base #a h d =
      well_formed h (d.pl) (d.l) /\
      not(B.g_is_null (d.pl) )

val well_formed_pointers_data_base: #a:eqtype -> h:HS.mem -> d:pointers_data a -> GTot Type0
let well_formed_pointers_data_base #a h d =
      B.live h d /\
      well_formed_pointers_content_data_base #a h (B.get h d 0) /\
      MO.loc_disjoint (MO.loc_buffer d) (footprint h ((B.get h d 0).pl) ((B.get h d 0).l))

val well_formed_listpointers_content_data_base: #a:eqtype -> h:HS.mem -> dl:list (pointers_content_data a) -> GTot Type0
let rec well_formed_listpointers_content_data_base #a h dl =
    match dl with
    | [] -> True
    | hd::tl -> (well_formed_pointers_content_data_base h hd) /\ (well_formed_listpointers_content_data_base h tl)
    
val well_formed_listpointers_data_base: #a:eqtype -> h:HS.mem -> dl:list (pointers_data a) -> GTot Type0
let rec well_formed_listpointers_data_base #a h dl =
    match dl with
    | [] -> True
    | hd::tl -> (well_formed_pointers_data_base h hd) /\ (well_formed_listpointers_data_base h tl)

val well_formed_listpointers_data_base_Lemma1: #a:eqtype -> h:HS.mem -> x:pointers_data a
-> Lemma(requires(well_formed_pointers_data_base h x))
(ensures(well_formed_listpointers_data_base h [x])) [SMTPat(well_formed_listpointers_data_base h [x])]
let well_formed_listpointers_data_base_Lemma1 #a h x = ()

val well_formed_listpointers_data_base_Lemma2: #a:eqtype -> h:HS.mem -> x:pointers_data a -> y:pointers_data a
-> Lemma(requires((well_formed_pointers_data_base h x) /\ (well_formed_pointers_data_base h y)))
(ensures(well_formed_listpointers_data_base h (x::[y]))) [SMTPat(well_formed_listpointers_data_base h (x::[y]))]
let well_formed_listpointers_data_base_Lemma2 #a h x y = 
  well_formed_listpointers_data_base_Lemma1 h x;
  well_formed_listpointers_data_base_Lemma1 h y

    (*)
val nodelast:  #a:eqtype -> h:HS.mem -> c:(rnode a){not(B.g_is_null c)} -> l:G.erased (list a){not(L.isEmpty (G.reveal l))} 
  -> Ghost (cs:(rnode a){not(B.g_is_null cs)}) (requires (
    well_formed h c l
  )) (ensures (fun r -> let hs = B.get h r 0 in (hs.data == L.last (G.reveal l))))
  (decreases (G.reveal l))
let rec nodelast #a h c l = 
  let cs = B.get h c 0 in 
  if B.g_is_null (cs.next) then c
  else nodelast h (cs.next) (G.hide (L.tl (G.reveal l)))
*)
val dataEqualSameLocationT: #a:eqtype -> h:HS.mem -> c1:(rnode a) -> l1:(G.erased (list a)) -> c2:(rnode a) -> l2:(G.erased (list a)) -> 
  Ghost Type0 (requires( well_formed h c1 l1 /\ well_formed h c2 l2 /\ not(B.g_is_null c1) /\ not(L.isEmpty (G.reveal l1)))) 
  (ensures( fun r -> True)) (decreases (G.reveal l2))
let rec dataEqualSameLocationT #a h c1 l1 c2 l2 =
  let d1 = B.get h c1 0 in 
    if not (B.g_is_null c2) then 
    let d2 = B.get h c2 0 in 
      ((d1.data = d2.data) ==> ((footprint h c1 l1) == (footprint h c2 l2)) /\ (l1 == l2) /\ (c1 == c2))
        /\ (dataEqualSameLocationT #a h c1 l1 d2.next (G.hide (L.tl (G.reveal l2))))
    else True

val listrnode_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> c:rnode a -> l:G.erased (list a) -> 
  Ghost Type0 (requires (well_formed h c l)) (ensures (fun r -> True)) (decreases (G.reveal l))
let rec listrnode_a_not_include_c #a h v c l = 
  if B.g_is_null c then True
  else 
    let d = B.get h c 0 in 
      ~(d.data = v) /\ (listrnode_a_not_include_c #a h v d.next (L.tl l))

val listrnode_a_not_include_c_equal_lemma: #a:eqtype -> h:HS.mem -> c:rnode a -> l: G.erased (list a) -> v:a ->
  Lemma(requires((well_formed h c l) /\ not(L.mem v l)))
  (ensures(listrnode_a_not_include_c h v c l)) (decreases (G.reveal l))
let rec listrnode_a_not_include_c_equal_lemma #a h c l v = 
  if B.g_is_null c then ()
  else 
    let d = B.get h c 0 in 
      listrnode_a_not_include_c_equal_lemma #a h d.next (L.tl l) v

val dataEqualSameLocationTLemma:#a:eqtype -> h:HS.mem -> c1:(rnode a) -> l1:(G.erased (list a)) -> c2:(rnode a) -> l2:(G.erased (list a)) -> 
  Lemma (requires( 
      well_formed h c1 l1 /\
      well_formed h c2 l2 /\ 
      not(B.g_is_null c1) /\ 
      not(L.isEmpty (G.reveal l1)) /\
      (let d1 = B.get h c1 0 in 
        listrnode_a_not_include_c #a h d1.data c2 l2  )
     ))
  (ensures (dataEqualSameLocationT #a h c1 l1 c2 l2)) (decreases (G.reveal l2))
let rec dataEqualSameLocationTLemma #a h c1 l1 c2 l2 =
  let d1 = B.get h c1 0 in 
      if not (B.g_is_null c2) then 
      let d2 = B.get h c2 0 in 
          (dataEqualSameLocationTLemma #a h c1 l1 d2.next (G.hide (L.tl (G.reveal l2))))
      else ()



val dataEqualSameLocation: #a:eqtype -> h:HS.mem -> c1:(rnode a) ->l1:(G.erased (list a))-> c2:(rnode a) -> l2:(G.erased (list a)) -> 
  Ghost Type0 (requires( well_formed h c1 l1 /\ well_formed h c2 l2)) 
  (ensures( fun r -> True)) (decreases (%[G.reveal l1; G.reveal l2]))
let rec dataEqualSameLocation #a h c1 l1 c2 l2 =
    if not (B.g_is_null c1) then 
      let d1 = B.get h c1 0 in 
      dataEqualSameLocationT #a h c1 l1 c2 l2 /\ 
      dataEqualSameLocation #a h d1.next (G.hide (L.tl (G.reveal l1))) c2 l2
    else True


val dataEqualSameLocation_nilLemma:#a:eqtype -> h:HS.mem -> c1:(rnode a) -> l1:(G.erased (list a)) -> c2:(rnode a) -> l2:(G.erased (list a)) -> 
  Lemma (requires( 
      well_formed h c1 l1 /\
      well_formed h c2 l2 /\ 
      not(B.g_is_null c1) /\ 
      not(L.isEmpty (G.reveal l1)) /\
      (let d1 = B.get h c1 0 in 
        let tc1n = d1.next in
        (B.g_is_null tc1n) /\
        (L.isEmpty (G.reveal (L.tl l1))) /\
        listrnode_a_not_include_c #a h d1.data c2 l2)
     ))
  (ensures (dataEqualSameLocation #a h c1 l1 c2 l2)) (decreases (G.reveal l1))
let rec dataEqualSameLocation_nilLemma #a h c1 l1 c2 l2 = dataEqualSameLocationTLemma #a h c1 l1 c2 l2

val dataEqualSameLocation_consLemma:#a:eqtype -> h:HS.mem -> c1:(rnode a) -> l1:(G.erased (list a)) -> c2:(rnode a) -> l2:(G.erased (list a)) -> 
  Lemma (requires( 
      well_formed h c1 l1 /\
      well_formed h c2 l2 /\ 
      not(B.g_is_null c1) /\ 
      not(L.isEmpty (G.reveal l1)) /\
      (let d1 = B.get h c1 0 in 
        let tc1n = d1.next in
        (not(B.g_is_null tc1n)) /\
        (not(L.isEmpty (G.reveal (L.tl l1)))) /\
        listrnode_a_not_include_c #a h d1.data c2 l2 /\ 
        well_formed h tc1n (L.tl l1) /\
          dataEqualSameLocation #a h tc1n (L.tl l1) c2 l2  )
     ))
  (ensures (dataEqualSameLocation #a h c1 l1 c2 l2)) (decreases (G.reveal l1))
let dataEqualSameLocation_consLemma #a h c1 l1 c2 l2 = dataEqualSameLocationTLemma #a h c1 l1 c2 l2

val well_formed_pointers_content_data: #a:eqtype -> h:HS.mem -> x:pointers_content_data a -> ys:list (pointers_content_data a)
    -> Ghost Type0 (requires((well_formed_pointers_content_data_base #a h x) /\ (well_formed_listpointers_content_data_base #a h ys)))
     (ensures( fun r -> True)) (decreases (ys))
let rec well_formed_pointers_content_data #a h x ys =  
  match ys with
  | [] -> True
  | hd::tl -> (dataEqualSameLocation #a h (x.pl) (x.l) (hd.pl) (hd.l)) 
    /\ well_formed_pointers_content_data #a h x tl

val pointers_data_to_pointers_content_data: #a:eqtype -> h:HS.mem -> l:list (pointers_data a)
  -> Ghost (list (pointers_content_data a)) (requires (well_formed_listpointers_data_base h l))
  (ensures(fun r -> well_formed_listpointers_content_data_base h r ))
let rec pointers_data_to_pointers_content_data #a h l =
  match l with
  | [] -> []
  | hd::tl -> (B.get h hd 0)::pointers_data_to_pointers_content_data #a h tl

val well_formed_pointers_data: #a:eqtype -> h:HS.mem -> x:pointers_data a -> ys:list (pointers_data a)
    -> Ghost Type0 (requires((
      well_formed_pointers_data_base #a h x) /\
      well_formed_listpointers_data_base h ys))
     (ensures( fun r -> True)) (decreases (ys))
let rec well_formed_pointers_data #a h x ys = 
  well_formed_pointers_content_data #a h (B.get h x 0) (pointers_data_to_pointers_content_data #a h ys) /\
  (match ys with 
  | [] -> True
  | hd::tl -> (MO.loc_disjoint (MO.loc_buffer x) (MO.loc_buffer hd)) /\ (well_formed_pointers_data #a h x tl))

val pointers_content_data_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> x:pointers_content_data a -> 
  Ghost Type0 (requires (well_formed_pointers_content_data_base h x)) (ensures (fun r -> True))
let pointers_content_data_a_not_include_c #a h v x = 
  listrnode_a_not_include_c #a h v (x.pl) (x.l) 

val pointers_content_data_a_not_include_c_equal_lemma: #a:eqtype -> h:HS.mem -> v:a -> x:pointers_content_data a -> 
  Lemma(requires ((well_formed_pointers_content_data_base h x) /\ (not(L.mem v (G.reveal x.l))))) (ensures (pointers_content_data_a_not_include_c #a h v x))
let pointers_content_data_a_not_include_c_equal_lemma #a h v x = 
  listrnode_a_not_include_c_equal_lemma #a h (x.pl) (x.l) v

val listpointers_content_data_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_content_data a) -> 
  Ghost Type0 (requires (well_formed_listpointers_content_data_base h l)) (ensures (fun r -> True))
let rec listpointers_content_data_a_not_include_c #a h v l = 
  match l with
  | [] -> True
  | hd::tl -> pointers_content_data_a_not_include_c #a h v hd /\ listpointers_content_data_a_not_include_c #a h v tl

val listpointers_content_data_a_not_include_c_equal_lemma: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_content_data a) -> 
  Lemma(requires ((well_formed_listpointers_content_data_base h l) /\ 
  (forall i. L.memP i l ==> ((well_formed_pointers_content_data_base h i) /\ (not(L.mem v (G.reveal i.l))))))) 
  (ensures ( listpointers_content_data_a_not_include_c #a h v l ))
let rec listpointers_content_data_a_not_include_c_equal_lemma #a h v l = 
  match l with
  | [] -> ()
  | hd::tl -> 
    pointers_content_data_a_not_include_c_equal_lemma #a h v hd;
    listpointers_content_data_a_not_include_c_equal_lemma #a h v tl

val pointers_data_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> x:pointers_data a -> 
  Ghost Type0 (requires (well_formed_pointers_data_base h x)) (ensures (fun r -> True))
let pointers_data_a_not_include_c #a h v x = pointers_content_data_a_not_include_c #a h v (B.get h x 0)

val pointers_data_a_not_include_c_equal_lemma: #a:eqtype -> h:HS.mem -> v:a -> x:pointers_data a -> 
  Lemma(requires ((well_formed_pointers_data_base h x) /\ (not(L.mem v (G.reveal (B.get h x 0).l)))))
   (ensures (pointers_data_a_not_include_c #a h v x))
let pointers_data_a_not_include_c_equal_lemma #a h v x = 
  pointers_content_data_a_not_include_c_equal_lemma #a h v (B.get h x 0)

val listpointers_data_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_data a) -> 
  Ghost Type0 (requires (well_formed_listpointers_data_base h l)) (ensures (fun r -> True))
let rec listpointers_data_a_not_include_c #a h v l = 
  match l with
  | [] -> True
  | hd::tl -> pointers_data_a_not_include_c #a h v hd /\ listpointers_data_a_not_include_c #a h v tl

val listpointers_data_a_not_include_c_equal_lemma: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_data a) -> 
  Lemma(requires ((well_formed_listpointers_data_base h l) /\ (forall i. L.memP i l ==> not(L.mem v (G.reveal (B.get h i 0).l))))) 
  (ensures (listpointers_data_a_not_include_c #a h v l))
let rec listpointers_data_a_not_include_c_equal_lemma #a h v l = 
  match l with
  | [] -> ()
  | hd::tl -> 
    pointers_data_a_not_include_c_equal_lemma #a h v hd;
    listpointers_data_a_not_include_c_equal_lemma #a h v tl
    
val listpointers_data_well_formed_supportLemma: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) ->
  Lemma(requires(well_formed_listpointers_data_base #a h l))
   (ensures(well_formed_listpointers_content_data_base #a h (pointers_data_to_pointers_content_data #a h l))) (decreases (l))
let rec listpointers_data_well_formed_supportLemma #a h l = 
  match l with
  | [] -> ()
  |hd::tl -> listpointers_data_well_formed_supportLemma #a h tl

val listpointers_data_a_not_include_c_supportLemma: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_data a) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ listpointers_data_a_not_include_c #a h v l))
  (ensures(listpointers_content_data_a_not_include_c #a h v (pointers_data_to_pointers_content_data #a h l))) (decreases l)
let rec listpointers_data_a_not_include_c_supportLemma #a h v l = 
  listpointers_data_well_formed_supportLemma #a h l;
  match l with
  | [] -> ()
  | hd::tl -> listpointers_data_a_not_include_c_supportLemma #a h v tl

val listpointers_data_a_not_include_c_supportLemma_r: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_data a) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ listpointers_content_data_a_not_include_c #a h v (pointers_data_to_pointers_content_data #a h l)))
  (ensures(listpointers_data_a_not_include_c #a h v l)) (decreases l)
let rec listpointers_data_a_not_include_c_supportLemma_r #a h v l = 
  listpointers_data_well_formed_supportLemma #a h l;
  match l with
  | [] -> ()
  | hd::tl -> listpointers_data_a_not_include_c_supportLemma_r #a h v tl
  
val well_formed_pointers_content_nildataLemma: #a:eqtype -> h:HS.mem -> x:pointers_content_data a -> ys:list (pointers_content_data a)
    -> Lemma (requires(
      well_formed_pointers_content_data_base #a h x /\ 
      well_formed_listpointers_content_data_base #a h ys /\
      not(B.g_is_null x.pl) /\ 
      (let r = B.get h x.pl 0 in
          (B.g_is_null r.next) /\
          (L.isEmpty (L.tl (G.reveal x.l))) /\
          (listpointers_content_data_a_not_include_c #a h r.data ys)
      )))
     (ensures( well_formed_pointers_content_data #a h x ys )) (decreases (ys))
let rec well_formed_pointers_content_nildataLemma #a h x ys 
  = match ys with
  | [] -> ()
  | hd::tl -> 
    dataEqualSameLocation_nilLemma #a h x.pl x.l hd.pl hd.l; 
    well_formed_pointers_content_nildataLemma #a h x tl

val well_formed_pointers_content_consdataLemma: #a:eqtype -> h:HS.mem -> x:pointers_content_data a -> ys:list (pointers_content_data a)
    -> Lemma (requires(
      well_formed_pointers_content_data_base #a h x /\ 
      well_formed_listpointers_content_data_base #a h ys /\
      not(B.g_is_null x.pl) /\ 
      (let r = B.get h x.pl 0 in
          not(B.g_is_null r.next) /\
          (listpointers_content_data_a_not_include_c #a h r.data ys) /\ 
          (let pdata:pointers_content_data a = Content (G.hide (L.tl (G.reveal x.l))) r.next  in 
          (well_formed_pointers_content_data #a h pdata ys))
      )))
     (ensures( well_formed_pointers_content_data #a h x ys )) (decreases (ys))
let rec well_formed_pointers_content_consdataLemma #a h x ys 
  = match ys with
  | [] -> ()
  | hd::tl -> 
    dataEqualSameLocation_consLemma #a h x.pl x.l hd.pl hd.l; 
    well_formed_pointers_content_consdataLemma #a h x tl


val well_formed_listpointers_content_data: #a:eqtype -> h:HS.mem -> l:list (pointers_content_data a) 
  -> Ghost Type0 (requires (well_formed_listpointers_content_data_base #a h l))(ensures (fun r -> True))
let rec well_formed_listpointers_content_data #a h l = 
      match l with
      | [] -> True
      | hd::tl -> (well_formed_pointers_content_data h hd tl) /\  (well_formed_listpointers_content_data #a h tl)

val well_formed_listpointers_data: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) 
  -> Ghost Type0 (requires (well_formed_listpointers_data_base #a h l))(ensures (fun r -> True))
let rec well_formed_listpointers_data #a h l = 
      match l with
      | [] -> True
      | hd::tl -> (well_formed_pointers_data h hd tl) /\  (well_formed_listpointers_data #a h tl)


val well_formed_disjoint_meet_type_from_pointers_content_data: #a:eqtype -> h: HS.mem -> r:MO.loc -> x:pointers_content_data a
  -> Ghost Type0 (requires(well_formed_pointers_content_data_base #a h x))
  (ensures (fun r -> True))
let well_formed_disjoint_meet_type_from_pointers_content_data #a h r x = MO.loc_disjoint r (footprint h x.pl x.l)

val well_formed_disjoint_meet_type_from_pointers_data: #a:eqtype -> h: HS.mem -> r:MO.loc -> x:pointers_data a
  -> Ghost Type0 (requires(well_formed_pointers_data_base #a h x))
  (ensures (fun r -> True))
let well_formed_disjoint_meet_type_from_pointers_data #a h r x 
  = (MO.loc_disjoint r (MO.loc_buffer x)) /\ well_formed_disjoint_meet_type_from_pointers_content_data #a h r (B.get h x 0)







val unused_in_well_formed_disjoint_from_pointers_content_data: #a:Type -> #b:eqtype -> h: HS.mem -> r:B.buffer a -> x:pointers_content_data b
 -> Lemma(requires (r `B.unused_in` h /\ well_formed_pointers_content_data_base #b h x))
  (ensures (well_formed_disjoint_meet_type_from_pointers_content_data #b h (MO.loc_buffer r) x))
let unused_in_well_formed_disjoint_from_pointers_content_data #a #b h r x
= unused_in_well_formed_disjoint_from_list #a #b h r (x.pl) (x.l)

val unused_in_well_formed_disjoint_from_pointers_data: #a:Type -> #b:eqtype -> h: HS.mem -> r:B.buffer a -> x:pointers_data b
 -> Lemma(requires (r `B.unused_in` h /\ well_formed_pointers_data_base #b h x))
  (ensures (well_formed_disjoint_meet_type_from_pointers_data #b h (MO.loc_buffer r) x))
let unused_in_well_formed_disjoint_from_pointers_data #a #b h r x
= unused_in_well_formed_disjoint_from_pointers_content_data #a #b h r (B.get h x 0)

val well_formed_disjoint_meet_type_from_listpointers_content_data:  #a:eqtype -> h: HS.mem -> r:MO.loc -> l: list(pointers_content_data a)
  -> Ghost Type0 (requires(well_formed_listpointers_content_data_base #a h l))
  (ensures (fun r -> True))
let rec well_formed_disjoint_meet_type_from_listpointers_content_data #a h r l
  = match l with
  | [] -> True
  | hd::tl -> 
    well_formed_disjoint_meet_type_from_pointers_content_data #a h r hd 
    /\ well_formed_disjoint_meet_type_from_listpointers_content_data #a h r tl

val well_formed_disjoint_meet_type_from_listpointers_data:  #a:eqtype -> h: HS.mem -> r:MO.loc -> l: list(pointers_data a)
  -> Ghost Type0 (requires(well_formed_listpointers_data_base #a h l))
  (ensures (fun r -> True))
let rec well_formed_disjoint_meet_type_from_listpointers_data #a h r l
  = match l with
  | [] -> True
  | hd::tl -> 
    well_formed_disjoint_meet_type_from_pointers_data #a h r hd 
    /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r tl


val well_formed_disjoint_meet_type_from_listpointers_data_supportLemma:  #a:eqtype -> h: HS.mem -> r:MO.loc -> l: list(pointers_data a)
  -> Lemma (requires(well_formed_listpointers_data_base #a h l /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r l))
  (ensures ((well_formed_listpointers_content_data_base #a h (pointers_data_to_pointers_content_data #a h l) )/\ 
  (well_formed_disjoint_meet_type_from_listpointers_content_data #a h r (pointers_data_to_pointers_content_data #a h l))))
let rec well_formed_disjoint_meet_type_from_listpointers_data_supportLemma #a h r l = 
  listpointers_data_well_formed_supportLemma #a h l;
  match l with
  | [] -> ()
  | hd::tl -> well_formed_disjoint_meet_type_from_listpointers_data_supportLemma #a h r tl


val unused_in_well_formed_disjoint_from_listpointers_content_data: #a:Type -> #b:eqtype -> h: HS.mem -> r:B.buffer a -> l: list (pointers_content_data b)
 -> Lemma(requires (r `B.unused_in` h /\ well_formed_listpointers_content_data_base #b h l))
  (ensures (well_formed_disjoint_meet_type_from_listpointers_content_data #b h (MO.loc_buffer r) l))
let rec unused_in_well_formed_disjoint_from_listpointers_content_data #a #b h r l
  = match l with
  | [] -> ()
  | hd::tl -> 
    unused_in_well_formed_disjoint_from_pointers_content_data #a #b h r hd;
    unused_in_well_formed_disjoint_from_listpointers_content_data #a #b h r tl
 
val unused_in_well_formed_disjoint_from_listpointers_data: #a:Type -> #b:eqtype -> h: HS.mem -> r:B.buffer a -> l: list (pointers_data b)
 -> Lemma(requires (r `B.unused_in` h /\ well_formed_listpointers_data_base #b h l))
  (ensures (well_formed_disjoint_meet_type_from_listpointers_data #b h (MO.loc_buffer r) l))
let rec unused_in_well_formed_disjoint_from_listpointers_data #a #b h r l
  = match l with
  | [] -> ()
  | hd::tl -> 
    unused_in_well_formed_disjoint_from_pointers_data #a #b h r hd;
    unused_in_well_formed_disjoint_from_listpointers_data #a #b h r tl


val well_formed_pointers_data_specialLemma: #a:eqtype -> h:HS.mem -> x:pointers_data a -> l:list (pointers_data a )
  -> Lemma(requires(
    well_formed_pointers_data_base #a h x /\ 
    well_formed_listpointers_data_base #a h l /\ 
    well_formed_listpointers_data #a h l /\
    well_formed_pointers_content_data #a h (B.get h x 0) (pointers_data_to_pointers_content_data #a h l) /\
    well_formed_disjoint_meet_type_from_listpointers_data #a h (MO.loc_buffer x) l
  ))
  (ensures(well_formed_pointers_data #a h x l))
let rec well_formed_pointers_data_specialLemma #a h x l = 
  match l with
  | [] -> ()
  | hd::tl -> well_formed_pointers_data_specialLemma #a h x tl





val modifies_disjoint_well_formed_pointers_content_data_and_footprint_base: #a:eqtype -> h:HS.mem -> x:pointers_content_data a -> r:MO.loc -> h':HS.mem 
 -> Lemma (requires (well_formed_pointers_content_data_base h x 
  /\ well_formed_disjoint_meet_type_from_pointers_content_data #a h r x 
  /\ MO.modifies r h h' ))
  (ensures ( well_formed_pointers_content_data_base h' x) /\ ((footprint h' (x.pl) (x.l)) == (footprint h (x.pl) (x.l))))
let modifies_disjoint_well_formed_pointers_content_data_and_footprint_base #a h x r h' = 
    modifies_disjoint_footprint #a h x.pl x.l r h'

val modifies_disjoint_well_formed_pointers_data_and_footprint_base: #a:eqtype -> h:HS.mem -> x:pointers_data a -> r:MO.loc -> h':HS.mem 
 -> Lemma (requires (well_formed_pointers_data_base h x 
  /\ well_formed_disjoint_meet_type_from_pointers_data #a h r x 
  /\ MO.modifies r h h' ))
  (ensures ( well_formed_pointers_data_base h' x) /\ ((footprint h' (B.get h' x 0).pl (B.get h' x 0).l) == (footprint h (B.get h x 0).pl (B.get h x 0).l)))
let modifies_disjoint_well_formed_pointers_data_and_footprint_base #a h x r h'
  = assert((B.get h' x 0) == (B.get h x 0));
  modifies_disjoint_well_formed_pointers_content_data_and_footprint_base #a h (B.get h x 0) r h'

val modifies_disjoint_listrnode_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> c:rnode a -> l:G.erased (list a) -> r:MO.loc -> h':HS.mem 
  -> Lemma (requires (well_formed h c l /\ 
      MO.loc_disjoint r (footprint #a h c l) /\
      MO.modifies r h h' /\
      listrnode_a_not_include_c #a h v c l
      )) (ensures (well_formed h' c l /\ listrnode_a_not_include_c #a h' v c l)) (decreases (G.reveal l))
let rec modifies_disjoint_listrnode_a_not_include_c #a h v c l r h' = 
  if B.g_is_null c then ()
  else modifies_disjoint_listrnode_a_not_include_c #a h v (B.get h c 0).next (L.tl l) r h' 


val listfootprint_content_meet_type:  #a:eqtype -> h:HS.mem -> l:list (pointers_content_data a) -> h':HS.mem 
-> Ghost Type0 (requires (
  well_formed_listpointers_content_data_base h l 
  /\ well_formed_listpointers_content_data_base h' l )) (ensures (fun r -> True)) (decreases l)
let rec listfootprint_content_meet_type #a h l h'
  = match l with
   | [] -> True
   | hd::tl -> ((footprint h hd.pl hd.l) == (footprint h' hd.pl hd.l)) /\ listfootprint_content_meet_type #a h tl h'

val listfootprint_meet_type:  #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> h':HS.mem 
-> Ghost Type0 (requires (
  well_formed_listpointers_data_base h l 
  /\ well_formed_listpointers_data_base h' l )) (ensures (fun r -> True))
let rec listfootprint_meet_type #a h l h'
  = match l with
   | [] -> True
   | hd::tl -> ((footprint h (B.get h hd 0).pl (B.get h hd 0).l) == (footprint h' (B.get h' hd 0).pl (B.get h' hd 0).l)) /\ (listfootprint_meet_type #a h tl h')

val modifies_disjoint_well_formed_listpointers_content_data_and_footprint_base: #a:eqtype -> h:HS.mem -> l:list (pointers_content_data a) -> r:MO.loc -> h':HS.mem 
 -> Lemma (requires (well_formed_listpointers_content_data_base h l 
  /\ well_formed_disjoint_meet_type_from_listpointers_content_data #a h r l
  /\ MO.modifies r h h' ))
  (ensures ( well_formed_listpointers_content_data_base h' l /\ listfootprint_content_meet_type #a h l h')) (decreases l)
let rec modifies_disjoint_well_formed_listpointers_content_data_and_footprint_base #a h l r h'
  = match l with
  | [] -> ()
  | hd::tl ->
    modifies_disjoint_well_formed_pointers_content_data_and_footprint_base #a h hd r h';
    modifies_disjoint_well_formed_listpointers_content_data_and_footprint_base #a h tl r h'

val modifies_disjoint_well_formed_listpointers_data_and_footprint_base: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> r:MO.loc -> h':HS.mem 
 -> Lemma (requires (well_formed_listpointers_data_base h l 
  /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r l
  /\ MO.modifies r h h' ))
  (ensures ( well_formed_listpointers_data_base h' l /\ listfootprint_meet_type #a h l h')) (decreases l)
let rec modifies_disjoint_well_formed_listpointers_data_and_footprint_base #a h l r h'
  = match l with
  | [] -> ()
  | hd::tl -> 
    modifies_disjoint_well_formed_pointers_data_and_footprint_base #a h hd r h';
    modifies_disjoint_well_formed_listpointers_data_and_footprint_base #a h tl r h'


val modifies_well_formed_disjoint_meet_type_from_pointers_data: #a:eqtype -> h: HS.mem -> r:MO.loc -> x:pointers_data a -> r':MO.loc -> h':HS.mem
  -> Lemma(requires(well_formed_pointers_data_base #a h x 
        /\ well_formed_disjoint_meet_type_from_pointers_data #a h r x
        /\ well_formed_disjoint_meet_type_from_pointers_data #a h r' x) 
        /\ (MO.modifies r' h h'))
    (ensures (well_formed_pointers_data_base #a h' x 
    /\ well_formed_disjoint_meet_type_from_pointers_data #a h' r x 
    /\ well_formed_disjoint_meet_type_from_pointers_data #a h' r' x))
let modifies_well_formed_disjoint_meet_type_from_pointers_data #a h r x r' h' =
  modifies_disjoint_well_formed_pointers_data_and_footprint_base #a h x r' h'

val modifies_well_formed_disjoint_meet_type_from_listpointers_data: #a:eqtype -> h: HS.mem -> r:MO.loc -> l:list (pointers_data a) -> r':MO.loc -> h':HS.mem
  -> Lemma(requires(well_formed_listpointers_data_base #a h l 
        /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r l
        /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r' l) 
        /\ (MO.modifies r' h h'))
    (ensures (well_formed_listpointers_data_base #a h' l 
    /\ well_formed_disjoint_meet_type_from_listpointers_data #a h' r l 
    /\ well_formed_disjoint_meet_type_from_listpointers_data #a h' r' l))
let rec modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h r l r' h'
  = match l with
  | [] -> ()
  | hd::tl -> 
    modifies_well_formed_disjoint_meet_type_from_pointers_data #a h r hd r' h';
    modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h r tl r' h'




val modifies_disjoint_pointers_content_data_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> x:pointers_content_data a -> r:MO.loc -> h':HS.mem 
  -> Lemma(requires(well_formed_pointers_content_data_base #a h x /\ 
  pointers_content_data_a_not_include_c #a h v x /\ 
  well_formed_disjoint_meet_type_from_pointers_content_data #a h r x /\
  MO.modifies r h h' ))
  (ensures(well_formed_pointers_content_data_base #a h' x /\ 
  pointers_content_data_a_not_include_c #a h' v x))
let modifies_disjoint_pointers_content_data_a_not_include_c #a h v x r h' = 
  modifies_disjoint_well_formed_pointers_content_data_and_footprint_base #a h x r h';
  modifies_disjoint_listrnode_a_not_include_c #a h v x.pl x.l r h'

val modifies_disjoint_listpointers_content_data_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_content_data a) -> r:MO.loc -> h':HS.mem 
  -> Lemma(requires(well_formed_listpointers_content_data_base #a h l /\ 
  listpointers_content_data_a_not_include_c #a h v l /\ 
  well_formed_disjoint_meet_type_from_listpointers_content_data #a h r l /\
  MO.modifies r h h' ))
   (ensures(well_formed_listpointers_content_data_base #a h' l /\ listpointers_content_data_a_not_include_c #a h' v l)) (decreases l)
let rec modifies_disjoint_listpointers_content_data_a_not_include_c #a h v l r h' =
  match l with
  | [] -> ()
  | hd::tl -> 
    modifies_disjoint_well_formed_pointers_content_data_and_footprint_base #a h hd r h';
    modifies_disjoint_pointers_content_data_a_not_include_c #a h v hd r h';
    modifies_disjoint_listpointers_content_data_a_not_include_c #a h v tl r h'

val modifies_disjoint_pointers_data_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> x:pointers_data a -> r:MO.loc -> h':HS.mem 
  -> Lemma(requires(well_formed_pointers_data_base #a h x /\ 
  pointers_data_a_not_include_c #a h v x /\ 
  well_formed_disjoint_meet_type_from_pointers_data #a h r x /\
  MO.modifies r h h' ))
  (ensures(well_formed_pointers_data_base #a h' x /\ 
  pointers_data_a_not_include_c #a h' v x))
let modifies_disjoint_pointers_data_a_not_include_c #a h v x r h' = 
  modifies_disjoint_well_formed_pointers_data_and_footprint_base #a h x r h';
  modifies_disjoint_listrnode_a_not_include_c #a h v (B.get h x 0).pl (B.get h x 0).l r h'

val modifies_disjoint_listpointers_data_a_not_include_c: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_data a) -> r:MO.loc -> h':HS.mem 
  -> Lemma(requires(well_formed_listpointers_data_base #a h l /\ 
  listpointers_data_a_not_include_c #a h v l /\ 
  well_formed_disjoint_meet_type_from_listpointers_data #a h r l /\
  MO.modifies r h h' ))
(ensures(well_formed_listpointers_data_base #a h' l /\ listpointers_data_a_not_include_c #a h' v l)) (decreases l)
let rec modifies_disjoint_listpointers_data_a_not_include_c #a h v l r h' =
  match l with
  | [] -> ()
  | hd::tl -> 
    modifies_disjoint_pointers_data_a_not_include_c #a h v hd r h';
    modifies_disjoint_well_formed_pointers_data_and_footprint_base #a h hd r h';
    modifies_disjoint_listpointers_data_a_not_include_c #a h v tl r h'

(*
¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥
let modifies_disjoint_listpointers_data_a_not_include_c #a h v l r h' = 
  modifies_disjoint_well_formed_listpointers_data_and_footprint_base #a h l r h';
  listpointers_data_well_formed_supportLemma #a h l;
  well_formed_disjoint_meet_type_from_listpointers_data_supportLemma #a h r l;
  listpointers_data_a_not_include_c_supportLemma #a h v l;
  assert(listpointers_content_data_a_not_include_c #a h v (pointers_data_to_pointers_content_data #a h l) );
  assert(well_formed_disjoint_meet_type_from_listpointers_content_data #a h r (pointers_data_to_pointers_content_data #a h l) );
  modifies_disjoint_listpointers_content_data_a_not_include_c #a h v (pointers_data_to_pointers_content_data #a h l) r h';
  listpointers_data_a_not_include_c_supportLemma_r #a h' v l
  ¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥
*)

val modifies_disjoint_pointers_data_to_pointers_content_data: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> r:MO.loc -> h':HS.mem
  ->Lemma(requires(well_formed_listpointers_data_base #a h l 
    /\ MO.modifies r h h' 
    /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r l))
    (ensures(well_formed_listpointers_data_base #a h' l 
    /\ well_formed_disjoint_meet_type_from_listpointers_data #a h' r l
    /\ (pointers_data_to_pointers_content_data #a h l == pointers_data_to_pointers_content_data #a h' l)))
let rec modifies_disjoint_pointers_data_to_pointers_content_data #a h l r h' = 
  modifies_disjoint_well_formed_listpointers_data_and_footprint_base #a h l r h';
  modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h r l r h';
  match l with
    | [] -> ()
    | hd::tl -> modifies_disjoint_pointers_data_to_pointers_content_data #a h tl r h'

val modifies_disjoint_dataEqualSameLocationT: #a:eqtype -> h:HS.mem -> c1:(rnode a){not(B.g_is_null c1)} ->l1:(G.erased (list a)){not(L.isEmpty (G.reveal l1))} -> c2:(rnode a) -> l2:(G.erased (list a)) -> r:MO.loc -> h':HS.mem
  -> Lemma (requires (
    well_formed h c1 l1 
    /\ well_formed h c2 l2 
    /\ MO.loc_disjoint r (footprint h c1 l1)
    /\ MO.loc_disjoint r (footprint h c2 l2)
    /\ dataEqualSameLocationT #a h c1 l1 c2 l2 
  /\ MO.modifies r h h'))
  (ensures (
    well_formed h' c1 l1 
  /\ well_formed h' c2 l2
  /\ dataEqualSameLocationT #a h' c1 l1 c2 l2)) (decreases (G.reveal l2))
let rec modifies_disjoint_dataEqualSameLocationT #a h c1 l1 c2 l2 r h' = 
  modifies_disjoint_footprint #a h c1 l1 r h';
  modifies_disjoint_footprint #a h c2 l2 r h';
  if not (B.g_is_null c2) then 
    let d2 = B.get h c2 0 in
      modifies_disjoint_dataEqualSameLocationT #a h c1 l1 d2.next (G.hide (L.tl (G.reveal l2))) r h' 
  else ()


val modifies_disjoint_dataEqualSameLocation: #a:eqtype -> h:HS.mem -> c1:(rnode a) ->l1:(G.erased (list a))-> c2:(rnode a) -> l2:(G.erased (list a)) -> r:MO.loc -> h':HS.mem
  -> Lemma (requires(
    well_formed h c1 l1 
    /\ well_formed h c2 l2 
    /\ MO.loc_disjoint r (footprint h c1 l1)
    /\ MO.loc_disjoint r (footprint h c2 l2)
    /\ dataEqualSameLocation #a h c1 l1 c2 l2 
  /\ MO.modifies r h h'
  ))
  (ensures(well_formed h' c1 l1 
    /\ well_formed h' c2 l2
    /\ dataEqualSameLocation #a h' c1 l1 c2 l2 )) (decreases (G.reveal l1))
let rec modifies_disjoint_dataEqualSameLocation #a h c1 l1 c2 l2 r h'=
    if not (B.g_is_null c1) then 
      let d1 = B.get h c1 0 in 
      modifies_disjoint_dataEqualSameLocationT #a h c1 l1 c2 l2 r h';
      modifies_disjoint_dataEqualSameLocation #a h d1.next (G.hide (L.tl (G.reveal l1))) c2 l2 r h'
    else  modifies_disjoint_footprint #a h c1 l1 r h';
          modifies_disjoint_footprint #a h c2 l2 r h'

val modifies_disjoint_well_formed_pointers_content_data: #a:eqtype -> h:HS.mem -> x:pointers_content_data a -> ys:list (pointers_content_data a) -> r:MO.loc -> h':HS.mem
  -> Lemma (requires (
    well_formed_listpointers_content_data_base h ys
    /\ well_formed_pointers_content_data_base h x 
    /\ well_formed_pointers_content_data h x ys
    /\ well_formed_disjoint_meet_type_from_listpointers_content_data #a h r ys 
    /\ well_formed_disjoint_meet_type_from_pointers_content_data #a h r x 
    /\ MO.modifies r h h'
  )) (ensures (
    well_formed_listpointers_content_data_base h' ys
    /\ well_formed_pointers_content_data_base h' x
    /\ well_formed_pointers_content_data h' x ys
    )) (decreases ys)
let rec modifies_disjoint_well_formed_pointers_content_data #a h x ys r h' = 
  modifies_disjoint_well_formed_pointers_content_data_and_footprint_base #a h x r h';
  match ys with
  | [] ->  ()
  | hd::tl ->
    modifies_disjoint_well_formed_listpointers_content_data_and_footprint_base #a h ys r h'; 
    modifies_disjoint_dataEqualSameLocation #a h x.pl x.l hd.pl hd.l r h';
    modifies_disjoint_well_formed_pointers_content_data #a h x tl r h'

val modifies_disjoint_well_formed_pointers_data: #a:eqtype -> h:HS.mem -> x:pointers_data a -> ys:list (pointers_data a) -> r:MO.loc -> h':HS.mem
  -> Lemma (requires (
    well_formed_listpointers_data_base h ys
    /\ well_formed_pointers_data_base h x 
    /\ well_formed_pointers_data h x ys
    /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r ys 
    /\ well_formed_disjoint_meet_type_from_pointers_data #a h r x 
    /\ MO.modifies r h h'
  )) (ensures (
    well_formed_listpointers_data_base h' ys
    /\ well_formed_pointers_data_base h' x
    /\ well_formed_pointers_data h' x ys
    )) (decreases ys)
let rec modifies_disjoint_well_formed_pointers_data #a h x ys r h' = 
  modifies_disjoint_well_formed_pointers_data_and_footprint_base #a h x r h';
  match ys with
  | [] ->  ()
  | hd::tl ->
    modifies_disjoint_well_formed_listpointers_data_and_footprint_base #a h ys r h'; 
    modifies_disjoint_dataEqualSameLocation #a h (B.get h x 0).pl (B.get h x 0).l (B.get h hd 0).pl (B.get h hd 0).l r h';
    modifies_disjoint_well_formed_pointers_data #a h x tl r h'

val modifies_disjoint_well_formed_listpointers_data: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> r:MO.loc -> h':HS.mem
  -> Lemma (requires (
    well_formed_listpointers_data_base h l
    /\ well_formed_listpointers_data h l
    /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r l
    /\ MO.modifies r h h'
  )) (ensures (
    well_formed_listpointers_data_base h' l
    /\ well_formed_listpointers_data h' l 
    )) (decreases l)

let rec modifies_disjoint_well_formed_listpointers_data #a h l r h' = 
  match l with
  | [] -> ()
  | hd::tl ->
    modifies_disjoint_well_formed_pointers_data #a h hd tl r h';
    modifies_disjoint_well_formed_listpointers_data #a h tl r h'


val check_well_formed_listpointers_lemma: #a:eqtype -> h:HS.mem -> l:list (pointers_data a ) -> pre:(pointers_data a) -> data:(pointers_data a)
    -> Lemma (requires(
    well_formed_listpointers_data_base #a h l /\
    well_formed_listpointers_data #a h l /\ 
    well_formed_pointers_data_base #a h pre /\ 
    well_formed_pointers_data #a h pre l /\ 
    ((B.get h data 0).pl == (B.get h pre 0).pl) /\ 
    well_formed_pointers_data_base #a h data /\ 
    well_formed_disjoint_meet_type_from_pointers_data #a h (MO.loc_buffer data) pre /\
    well_formed_disjoint_meet_type_from_listpointers_data #a h (MO.loc_buffer data) l
    ))
     (ensures(well_formed_pointers_data #a h data l)) (decreases l)
let rec check_well_formed_listpointers_lemma #a h l pre data =  
  match l with
  | [] -> ()
  | hd::tl -> check_well_formed_listpointers_lemma #a h tl pre data

val push_pointers_data:#a:eqtype -> l:list (pointers_data a) -> x:pointers_data a -> v:a
  -> ST unit (requires (fun h -> 
      well_formed_listpointers_data_base #a h l /\ 
      well_formed_listpointers_data #a h l /\ 
      well_formed_pointers_data_base #a h x /\ 
      well_formed_pointers_data #a h x l /\ 
      well_formed_disjoint_meet_type_from_listpointers_data #a h (MO.loc_buffer x) l /\
      listpointers_data_a_not_include_c #a h v l
      ))
    (ensures (fun h0 _ h1 -> 
      MO.modifies (MO.loc_buffer x) h0 h1 /\
      well_formed_listpointers_data_base #a h1 l /\ 
      well_formed_listpointers_data #a h1 l /\ 
      well_formed_pointers_data_base #a h1 x /\ 
      well_formed_disjoint_meet_type_from_listpointers_data #a h1 (MO.loc_buffer x) l /\ 
      well_formed_pointers_data #a h1 x l /\ 
      ((B.get h1 (B.get h1 x 0).pl 0).data == v) /\ 
      ((B.get h1 (B.get h1 x 0).pl 0).next == (B.get h0 x 0).pl)

    ))

let push_pointers_data #a l x v = 
  let h0 = get () in
  let t = !* x in
  let s = t.pl in
  let c = {
    data = v;
    next = s;
  }
  in
  assert(s == t.pl);
  let pc: rnode a = B.malloc HS.root c 1ul in
  unused_in_well_formed_disjoint_from_list h0 pc t.pl t.l;
  unused_in_well_formed_disjoint_from_pointers_data h0 pc x;
  unused_in_well_formed_disjoint_from_pointers_content_data h0 pc t;
  unused_in_well_formed_disjoint_from_listpointers_data h0 pc l;
  assert(well_formed_pointers_content_data #a h0 t (pointers_data_to_pointers_content_data #a h0 l));
  let h1 = get () in
  modifies_disjoint_footprint h0 t.pl t.l (MO.loc_buffer pc) h1;
  modifies_disjoint_well_formed_listpointers_data h0 l (MO.loc_buffer pc) h1;
  modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h0 (MO.loc_buffer x) l (MO.loc_buffer pc)  h1;
  modifies_disjoint_listpointers_data_a_not_include_c #a h0 v l (MO.loc_buffer pc) h1;
  listpointers_data_well_formed_supportLemma #a h0 l;
  well_formed_disjoint_meet_type_from_listpointers_data_supportLemma #a h0 (MO.loc_buffer pc ) l;
  modifies_disjoint_well_formed_pointers_content_data h0 t (pointers_data_to_pointers_content_data #a h0 l) (MO.loc_buffer pc) h1;
  modifies_disjoint_pointers_data_to_pointers_content_data #a h0 l (MO.loc_buffer pc) h1;
 // assert((B.get h0 x 0) == (B.get h1 x 0));
  //assert((pointers_data_to_pointers_content_data #a h0 l) == (pointers_data_to_pointers_content_data #a h1 l));
  listpointers_data_well_formed_supportLemma #a h1 l;
  well_formed_disjoint_meet_type_from_listpointers_data_supportLemma #a h1 (MO.loc_buffer x ) l;
  listpointers_data_a_not_include_c_supportLemma #a h1 v l;
  assert(well_formed_pointers_content_data #a h1 t (pointers_data_to_pointers_content_data #a h1 l));
  assert(s == t.pl);
  assert(listpointers_content_data_a_not_include_c #a h1 v (pointers_data_to_pointers_content_data #a h1 l));

  let nes:pointers_content_data a = {pl = pc; l = G.hide (v::(G.reveal t.l));} in
  x *= nes;
  let h2 = get () in
  //assert(((B.get h2 (B.get h2 x 0).pl.next).pl) == s);
  //assert((B.get h2 (B.get h2 x 0).pl).pl == s);
  //let s = { l = x.l; pl = x.pl;} in
  modifies_disjoint_footprint h1 t.pl t.l (MO.loc_buffer x) h2;
  modifies_disjoint_well_formed_pointers_content_data_and_footprint_base h1 t (MO.loc_buffer x) h2;
  modifies_disjoint_pointers_data_to_pointers_content_data #a h1 l (MO.loc_buffer x) h2;
  modifies_disjoint_well_formed_pointers_content_data h1 t (pointers_data_to_pointers_content_data #a h1 l) (MO.loc_buffer x) h2;
  modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h1 (MO.loc_buffer x) l  (MO.loc_buffer x) h2;
  modifies_disjoint_well_formed_listpointers_data #a h1 l (MO.loc_buffer x) h2;
  modifies_disjoint_listpointers_data_a_not_include_c #a h1 v l (MO.loc_buffer x) h2;
  listpointers_data_well_formed_supportLemma #a h2 l;
  listpointers_data_a_not_include_c_supportLemma #a h2 v l;
  well_formed_disjoint_meet_type_from_listpointers_data_supportLemma #a h2 (MO.loc_buffer x ) l;
  assert(not(B.g_is_null x));
  assert(not(B.g_is_null (B.get h2 x 0).pl));
  assert(not(B.g_is_null (B.get h2 (B.get h2 x 0).pl 0).next));
  assert(s == t.pl);
  assert((B.get h2 (B.get h2 x 0).pl 0).next == t.pl);
  assert((L.tl (G.reveal (B.get h2 x 0).l)) == ( G.reveal t.l));
//  well_formed_pointers_content_consdataLemma #a h2 (B.get h2 x 0) (pointers_data_to_pointers_content_data #a h2 l); requires確認
  assert( well_formed_pointers_content_data_base #a h2 (B.get h2 x 0));
  assert(well_formed_listpointers_content_data_base #a h2 (pointers_data_to_pointers_content_data #a h2 l));
  assert(not(B.g_is_null (B.get h2 x 0).pl));
  let r = B.get h2 (B.get h2 x 0).pl 0 in
  assert(not(B.g_is_null r.next) );
  assert(listpointers_data_a_not_include_c #a h2 r.data l);
  let k = Content (G.hide (L.tl (G.reveal (B.get h2 x 0).l))) r.next in 
  assert(k == t);
  assert(well_formed_pointers_content_data #a h2 t (pointers_data_to_pointers_content_data #a h2 l));
  assert(well_formed_pointers_content_data #a h2 k (pointers_data_to_pointers_content_data #a h2 l));
  assert(listpointers_content_data_a_not_include_c #a h2 v (pointers_data_to_pointers_content_data #a h2 l));
  well_formed_pointers_content_consdataLemma #a h2 (B.get h2 x 0) (pointers_data_to_pointers_content_data #a h2 l);
  //well_formed_pointers_data_specialLemma #a h2 x l　requires確認
  assert(well_formed_pointers_data_base #a h2 x );
  assert(well_formed_listpointers_data_base #a h2 l);
  assert(well_formed_listpointers_data #a h2 l);
  assert(well_formed_pointers_content_data #a h2 (B.get h2 x 0) (pointers_data_to_pointers_content_data #a h2 l));
  assert(well_formed_disjoint_meet_type_from_listpointers_data #a h2 (MO.loc_buffer x) l);
  well_formed_pointers_data_specialLemma #a h2 x l

val insert_pre_pl: #a:eqtype -> l:list (pointers_data a ) -> pre:(pointers_data a){L.memP pre l} -> pc:pointers_data a ->
  ST (pointers_data a) (requires (fun h -> 
    well_formed_listpointers_data_base #a h l /\
    well_formed_listpointers_data #a h l /\ 
    well_formed_pointers_data_base #a h pre /\
    well_formed_pointers_data #a h pre l /\ 
    well_formed_disjoint_meet_type_from_pointers_data #a h (MO.loc_buffer pc) pre /\
    well_formed_disjoint_meet_type_from_listpointers_data #a h (MO.loc_buffer pc) l /\ 
    B.live h pc
  ))
  (ensures(fun h0 v h1 -> 
    MO.modifies (MO.loc_buffer pc) h0 h1 /\
    well_formed_listpointers_data_base #a h1 l /\
    well_formed_listpointers_data #a h1 l /\ 
    well_formed_pointers_data_base #a h1 pre /\ 
    well_formed_pointers_data #a h1 pre l /\
    well_formed_pointers_data_base #a h1 v /\ 
    well_formed_disjoint_meet_type_from_pointers_data #a h1 (MO.loc_buffer v) pre /\
    well_formed_disjoint_meet_type_from_listpointers_data #a h1 (MO.loc_buffer v) l /\
    well_formed_pointers_data #a h1 v l /\ 
    ((MO.loc_buffer v) == (MO.loc_buffer pc)) /\ 
    ((B.get h1 v 0).pl == (B.get h1 pre 0).pl)
  ))
let insert_pre_pl #a l pre pc = 
  let h0 = get () in
  pc *= (!* pre);
  let h1 = get () in
  modifies_disjoint_well_formed_listpointers_data h0 l (MO.loc_buffer pc) h1; 
  modifies_disjoint_well_formed_pointers_data h0 pre l (MO.loc_buffer pc) h1;
  modifies_well_formed_disjoint_meet_type_from_listpointers_data h0 (MO.loc_buffer pc) l (MO.loc_buffer pc) h1;
  modifies_well_formed_disjoint_meet_type_from_pointers_data h0 (MO.loc_buffer pc) pre (MO.loc_buffer pc) h1;
  assert((B.get h1 pc 0) == (B.get h1 pre 0));
  let data = pc in
  check_well_formed_listpointers_lemma #a h1 l pre data;
  data

val insert_hd_tl_Lemma: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> x:(pointers_data a) -> 
  Lemma(requires(
    well_formed_listpointers_data_base #a h l /\ 
    well_formed_listpointers_data #a h l /\ 
    well_formed_pointers_data_base #a h x /\ 
    well_formed_pointers_data #a h x l
  ))
  (ensures(well_formed_listpointers_data_base #a h (x::l) /\ well_formed_listpointers_data #a h (x::l)))
let rec insert_hd_tl_Lemma #a h l x = 
  match l with
  | [] -> ()
  | hd::tl -> insert_hd_tl_Lemma #a h tl x

val insert_hd_tl_Lemma2: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> pre:(pointers_data a) -> x:(pointers_data a) -> 
  Lemma(requires(
    well_formed_listpointers_data_base #a h l /\ 
    well_formed_listpointers_data #a h l /\ 
    well_formed_pointers_data_base #a h x /\ 
    well_formed_pointers_data #a h x l /\ 
    well_formed_pointers_data_base #a h pre /\ 
    well_formed_pointers_data #a h pre l /\ 
    well_formed_pointers_data #a h pre [x]
  ))
  (ensures((well_formed_listpointers_data_base #a h (x::l)) /\ (well_formed_listpointers_data #a h (x::l)) /\ (L.memP pre l ==> well_formed_pointers_data #a h pre (x::l))))
let rec insert_hd_tl_Lemma2 #a h l pre x = 
  match l with
  | [] -> ()
  | hd::tl -> insert_hd_tl_Lemma2 #a h tl pre x

val memEqual_l_x_well_formed_listpointers_data_Lemma: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> y:pointers_data a -> x:pointers_data a
  -> Lemma(requires(
    well_formed_pointers_data_base #a h x
  /\ well_formed_listpointers_data_base #a h l
  /\ well_formed_listpointers_data #a h l
  /\ well_formed_pointers_data #a h x l
  /\ well_formed_listpointers_data_base #a h [y]
  /\ well_formed_listpointers_data #a h [y]
  ))
  (ensures(L.memP y l  ==> well_formed_pointers_data #a h x [y]))
let rec memEqual_l_x_well_formed_listpointers_data_Lemma #a h l y x = 
  match l with 
  | [] -> ()
  | hd::tl -> memEqual_l_x_well_formed_listpointers_data_Lemma #a h tl y x

val memEqual_well_formed_pointers_data_Lemma: #a:eqtype -> h:HS.mem -> l1:list (pointers_data a) -> l2:list(pointers_data a) -> x:pointers_data a
  -> Lemma(requires(well_formed_listpointers_data_base #a h l1 
  /\ well_formed_pointers_data_base #a h x
  /\ well_formed_listpointers_data_base #a h l1
  /\ well_formed_listpointers_data #a h l1
  /\ well_formed_pointers_data #a h x l1
  /\ well_formed_listpointers_data_base #a h l2
  /\ well_formed_listpointers_data #a h l2 
   ))
  (ensures((forall i. L.memP i l2 ==> L.memP i l1) ==> well_formed_pointers_data #a h x l2))
let rec memEqual_well_formed_pointers_data_Lemma #a h l1 l2 x = 
  match l2 with
  | [] -> ()
  | hd::tl -> 
    memEqual_l_x_well_formed_listpointers_data_Lemma #a h l1 hd x;
    memEqual_well_formed_pointers_data_Lemma #a h l1 tl x


//effect STh (a:Type) = ST a (fun _ -> True) (fun h0 _ h1 -> (h0 == h1))

//type getdetail_func_type (a:eqtype) = (a -> Tot int)//{forall (i:a) (j:a{~(i == j)}). not(f i = f j)}

val getdetail_func_type_func: #a:eqtype -> h:HS.mem -> f:(a -> Tot int) -> x:pointers_data a 
  -> Ghost int (requires(well_formed_pointers_data_base h x)) (ensures(fun _ -> True))
let getdetail_func_type_func #a h f x = 
  let s = B.get h x 0 in
    let d = B.get h s.pl 0 in
      f d.data 

val getdetail_func_type_funcST: #a:eqtype -> f:(a -> Tot int) -> x:pointers_data a 
  -> ST int (fun h -> requires(well_formed_pointers_data_base h x)) (ensures(fun h0 r h1 -> (h0 == h1) /\ (r = getdetail_func_type_func h1 f x)))
let getdetail_func_type_funcST #a f x = 
  let s = !* x in
    let d = !* s.pl in
      f d.data 

val sorted: #a:eqtype -> h:HS.mem -> l:list (pointers_data a ) -> f:(a -> Tot int)
  -> Ghost bool (requires(well_formed_listpointers_data_base h l))
  (ensures(fun _ -> True))
let rec sorted #a h l f = match l with
  | [] -> true
  | [hd] -> true
  | hd1::hd2::tl -> (getdetail_func_type_func h f hd1 >= getdetail_func_type_func h f hd2) && sorted #a h (hd2::tl) f 

val modifies_disjoint_sorted: #a:eqtype -> h:HS.mem -> l:list (pointers_data a ) -> f: (a -> Tot int) -> r:MO.loc -> h':HS.mem
  -> Lemma(requires(
    well_formed_listpointers_data_base h l /\ 
    sorted h l f /\ 
    well_formed_disjoint_meet_type_from_listpointers_data #a h r l /\
    MO.modifies r h h' 
  ))
  (ensures(
    well_formed_listpointers_data_base h' l /\
    sorted h' l f
  )) (decreases l)
let rec modifies_disjoint_sorted #a h l f r h' = 
  modifies_disjoint_well_formed_listpointers_data_and_footprint_base h l r h';
  match l with
  | [] -> ()
  | hd::tl -> 
    modifies_disjoint_sorted #a h tl f r h'

val checksorted: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> n:int -> f:(a -> Tot int) 
  -> Ghost bool (requires(well_formed_listpointers_data_base h l))
  (ensures(fun _ -> True)) (decreases l)
let rec checksorted #a h l n f = match l with
  | [] -> true
  | hd::tl -> 
     (n >= getdetail_func_type_func h f hd) && checksorted #a h tl n f 

val checksorted_lem_type: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> f:(a -> Tot int)
  -> Ghost Type0 (requires( well_formed_listpointers_data_base h l ))
  (ensures(fun _ -> True))
let rec checksorted_lem_type #a h l f = 
  match l with 
  | [] -> True
  | hd::tl -> checksorted #a h tl (getdetail_func_type_func h f hd) f /\ checksorted_lem_type #a h tl f

val sorted_lemma: #a:eqtype -> h:HS.mem -> l:list (pointers_data a){Cons? l}  -> f:(a -> Tot int) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ sorted #a h l f))
   (ensures(forall i. L.memP i (L.tl l) ==> ((well_formed_pointers_data_base h i) /\ (getdetail_func_type_func h f (L.hd l) >= getdetail_func_type_func h f i))))
let rec sorted_lemma #a h l f = 
  match l with
  | [hd] -> ()
  | hd::tl -> sorted_lemma #a h tl f

val checksorted_lemma:#a:eqtype -> h:HS.mem -> l:list (pointers_data a ) -> n:int -> f:(a -> Tot int) -> 
  Lemma(requires((well_formed_listpointers_data_base h l) /\ (forall i. L.memP i l ==> ((well_formed_pointers_data_base h i) /\ (n >= getdetail_func_type_func h f i)))))
   (ensures(checksorted #a h l n f))
let rec checksorted_lemma #a h l n f = 
  match l with
  | [] -> ()
  | hd::tl -> checksorted_lemma #a h tl n f


val checksorted_sorted_lemma:#a:eqtype -> h:HS.mem -> l:list (pointers_data a){Cons? l} -> f:(a -> Tot int) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ sorted #a h l f)) (ensures(checksorted #a h (L.tl l) (getdetail_func_type_func h f (L.hd l)) f))
let checksorted_sorted_lemma #a h l f = sorted_lemma #a h l f; checksorted_lemma #a h (L.tl l) (getdetail_func_type_func h f (L.hd l) ) f

val checksorted_lem_type_lemma: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> f:(a -> Tot int) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ sorted #a h l f)) (ensures(checksorted_lem_type #a h l f))
let rec checksorted_lem_type_lemma #a h l f = 
  match l with
  | [] -> ()
  | hd::tl -> 
    checksorted_sorted_lemma #a h l f;
    checksorted_lem_type_lemma #a h tl f


val checksorted_lem_type_lemma2: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> f:(a -> Tot int) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ checksorted_lem_type #a h l f)) (ensures(sorted #a h l f))
let rec checksorted_lem_type_lemma2 #a h l f = 
  match l with
  | [] -> ()
  | hd::tl -> 
    checksorted_lem_type_lemma2 #a h tl f

val checksorted_lem_type_lemma3: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> x:pointers_data a -> n:int -> f:(a -> Tot int) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ well_formed_pointers_data_base h x ))
   (ensures(((checksorted #a h l n f) /\ (n >= getdetail_func_type_func h f x)) <==> checksorted #a h (x::l) n f))
let rec checksorted_lem_type_lemma3 #a h l x n f = 
  match l with
  | [] -> ()
  | hd::tl -> 
    checksorted_lem_type_lemma3 #a h tl x n f

val checksorted_lem_type_lemma4: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> x:pointers_data a -> n:int -> f:(a -> Tot int) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ well_formed_pointers_data_base h x  /\ checksorted h l n f))
  (ensures(L.memP x l ==> checksorted #a h [x] n f ))
let rec checksorted_lem_type_lemma4 #a h l x n f = 
  match l with
  | [] -> ()
  | hd::tl -> checksorted_lem_type_lemma4 #a h tl x n f

val checksorted_lem_type_lemma5: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> nl:list (pointers_data a) -> n:int -> f:(a -> Tot int) -> 
  Lemma(requires(well_formed_listpointers_data_base h l /\ well_formed_listpointers_data_base h nl /\ checksorted #a h l n f))
   (ensures((forall i. L.memP i nl ==> L.memP i l) ==> checksorted #a h nl n f ))
let rec checksorted_lem_type_lemma5 #a h l nl n f = 
  match nl with
  | [] -> ()
  | hd::tl -> 
    checksorted_lem_type_lemma4 #a h l hd n f;
    checksorted_lem_type_lemma5 #a h l tl n f

(*
val dataEqualSameLocation_chenge_Lemma: #a:eqtype -> h:HS.mem -> c1:(rnode a) -> l1:(G.erased (list a)) -> c2:(rnode a) -> l2:(G.erased (list a)) -> 
  Lemma (requires( well_formed h c1 l1 /\ well_formed h c2 l2 /\ not(B.g_is_null c1) /\ (B.g_is_null (B.get h c1 0).next )))
  (ensures(dataEqualSameLocationT #a h c1 l1 c2 l2 == dataEqualSameLocation #a h c2 l2 c1 l1)) (decreases (G.reveal l2))
let rec dataEqualSameLocation_chenge_Lemma #a h c1 l1 c2 l2 =
  if B.g_is_null c2 then () else
  let d2 = B.get h c2 0 in
      dataEqualSameLocation_chenge_Lemma #a h c1 l1 d2.next (G.hide (L.tl (G.reveal l2)))
*)
assume val well_formed_pointers_data_chenge_lemma: #a:eqtype -> h:HS.mem -> x:pointers_data a -> y:pointers_data a
  -> Lemma(requires( 
    well_formed_pointers_data_base #a h x /\ 
    well_formed_pointers_data_base #a h y
    ))
  (ensures(well_formed_pointers_data #a h x [y] <==> well_formed_pointers_data #a h y [x]))







val member_disjoint_max_rnode: #a:eqtype -> h:HS.mem -> max:int -> c:rnode a -> l:G.erased (list a) -> f:(a -> int)
  -> Ghost bool (requires(well_formed h c l)) (ensures(fun r -> True)) (decreases (G.reveal l))
let rec member_disjoint_max_rnode #a h max c l f = 
  if B.g_is_null c then true
  else
    let s = B.get h c 0 in 
      (max > f s.data ) && (member_disjoint_max_rnode #a h max s.next (G.hide (L.tl (G.reveal l)))) f


val member_disjoint_max_pointers_content_data: #a:eqtype -> h:HS.mem -> max:int -> x:pointers_content_data a -> f:(a -> int)
  -> Ghost bool (requires(well_formed_pointers_content_data_base h x)) (ensures(fun r -> True))
let member_disjoint_max_pointers_content_data #a h max x f = 
    member_disjoint_max_rnode #a h max x.pl x.l f

val member_disjoint_max_pointers_data: #a:eqtype -> h:HS.mem -> max:int -> x:pointers_data a -> f:(a -> int)
  -> Ghost bool (requires(well_formed_pointers_data_base h x)) (ensures(fun r -> True))
let member_disjoint_max_pointers_data #a h max x f = 
    member_disjoint_max_pointers_content_data #a h max (B.get h x 0) f


val member_disjoint_max_listpointers_data: #a:eqtype -> h:HS.mem -> max:int -> l:list (pointers_data a) -> f:(a -> int)
  -> Ghost bool (requires(well_formed_listpointers_data_base h l)) (ensures(fun r -> True))
let rec member_disjoint_max_listpointers_data #a h max l f = 
  match l with
  | [] -> true
  | hd::tl -> 
    (member_disjoint_max_pointers_data #a h max hd f) && (member_disjoint_max_listpointers_data #a h max tl f)
  



val member_disjoint_max_rnode_lemma: #a:eqtype -> h:HS.mem -> max1:int -> max2:int -> c:rnode a -> l:G.erased (list a) -> f:(a -> int)
  -> Lemma(requires((max2 > max1) /\ (well_formed h c l) /\ (member_disjoint_max_rnode #a h max1 c l f)))
   (ensures(member_disjoint_max_rnode #a h max2 c l f)) (decreases (G.reveal l)) 
let rec member_disjoint_max_rnode_lemma #a h max1 max2 c l f = 
  if B.g_is_null c then ()
  else
    let s = B.get h c 0 in 
      member_disjoint_max_rnode_lemma #a h max1 max2 s.next (G.hide (L.tl (G.reveal l))) f

val member_disjoint_max_pointers_content_data_lemma: #a:eqtype -> h:HS.mem -> max1:int -> max2:int -> x:pointers_content_data a -> f:(a -> int)
  -> Lemma(requires((max2 > max1) /\ (well_formed_pointers_content_data_base h x) /\ (member_disjoint_max_pointers_content_data #a h max1 x f))) (ensures(member_disjoint_max_pointers_content_data #a h max2 x f))
let member_disjoint_max_pointers_content_data_lemma #a h max1 max2 x = 
  member_disjoint_max_rnode_lemma #a h max1 max2 x.pl x.l

val member_disjoint_max_pointers_data_lemma: #a:eqtype -> h:HS.mem -> max1:int -> max2:int -> x:pointers_data a -> f:(a -> int)
  -> Lemma(requires((max2 > max1) /\ (well_formed_pointers_data_base h x) /\ (member_disjoint_max_pointers_data #a h max1 x f))) (ensures(member_disjoint_max_pointers_data #a h max2 x f))
let member_disjoint_max_pointers_data_lemma #a h max1 max2 x = 
  member_disjoint_max_pointers_content_data_lemma #a h max1 max2 (B.get h x 0)

val member_disjoint_max_listpointers_data_lemma: #a:eqtype -> h:HS.mem -> max1:int -> max2:int -> l:list (pointers_data a) -> f:(a -> int)
  -> Lemma(requires((well_formed_listpointers_data_base h l) /\ (max2 > max1) /\ (member_disjoint_max_listpointers_data #a h max1 l f)))
   (ensures(member_disjoint_max_listpointers_data #a h max2 l f))
let rec member_disjoint_max_listpointers_data_lemma #a h max1 max2 l f = 
  match l with
  | [] -> ()
  | hd::tl -> 
    member_disjoint_max_pointers_data_lemma #a h max1 max2 hd f;
    member_disjoint_max_listpointers_data_lemma #a h max1 max2 tl f
  

val member_disjoint_max_include_c_rnode_lemma: #a:eqtype -> h:HS.mem -> v:a -> c:rnode a -> l:G.erased (list a) -> f:(a -> int)
  -> Lemma(requires((well_formed h c l) /\ (member_disjoint_max_rnode #a h (f v) c l f)))
   (ensures(listrnode_a_not_include_c h v c l)) (decreases (G.reveal l)) 
let rec member_disjoint_max_include_c_rnode_lemma #a h v c l f = 
  if B.g_is_null c then ()
  else
    let s = B.get h c 0 in 
      member_disjoint_max_include_c_rnode_lemma #a h v s.next (G.hide (L.tl (G.reveal l))) f

val member_disjoint_max_include_c_pointers_content_data_lemma: #a:eqtype -> h:HS.mem -> v:a -> x:pointers_content_data a -> f:(a -> int)
  -> Lemma(requires((well_formed_pointers_content_data_base h x) /\ (member_disjoint_max_pointers_content_data #a h (f v) x f))) 
  (ensures(pointers_content_data_a_not_include_c h v x))
let member_disjoint_max_include_c_pointers_content_data_lemma #a h v x = 
  member_disjoint_max_include_c_rnode_lemma #a h v x.pl x.l
    
val member_disjoint_max_include_c_pointers_data_lemma: #a:eqtype -> h:HS.mem -> v:a -> x:pointers_data a -> f:(a -> int)
  -> Lemma(requires((well_formed_pointers_data_base h x) /\ (member_disjoint_max_pointers_data #a h (f v) x f))) 
  (ensures(pointers_data_a_not_include_c h v x))
let member_disjoint_max_include_c_pointers_data_lemma #a h v x f = 
  member_disjoint_max_include_c_pointers_content_data_lemma #a h v (B.get h x 0) f

val member_disjoint_max_include_c_listpointers_data_lemma: #a:eqtype -> h:HS.mem -> v:a -> l:list (pointers_data a) -> f:(a -> int)
  -> Lemma(requires((well_formed_listpointers_data_base h l) /\ (member_disjoint_max_listpointers_data #a h (f v) l f)))
   (ensures(listpointers_data_a_not_include_c h v l))
let rec member_disjoint_max_include_c_listpointers_data_lemma #a h v l f = 
  match l with
  | [] -> ()
  | hd::tl -> 
    member_disjoint_max_include_c_pointers_data_lemma #a h v hd f;
    member_disjoint_max_include_c_listpointers_data_lemma #a h v tl f


val modifies_disjoint_max_rnode_lemma: #a:eqtype -> h:HS.mem -> n:int -> c:rnode a -> l:G.erased (list a) -> f:(a -> int) -> r:MO.loc -> h':HS.mem 
  -> Lemma(requires(well_formed #a h c l /\ 
    MO.loc_disjoint r (footprint #a h c l) /\
    MO.modifies r h h' /\ 
    member_disjoint_max_rnode #a h n c l f  ))
  (ensures(
    (well_formed #a h' c l)/\
    (member_disjoint_max_rnode #a h' n c l f)
  )) (decreases (G.reveal l))
let rec modifies_disjoint_max_rnode_lemma #a h n c l f r h' =
  if not (B.g_is_null c) then 
      let d = B.get h c 0 in 
        modifies_disjoint_footprint h c l r h';
        modifies_disjoint_max_rnode_lemma #a h n (d.next) (G.hide (L.tl (G.reveal l))) f r h'
    else ()


val modifies_disjoint_max_pointers_content_data_lemma: #a:eqtype -> h:HS.mem -> n:int -> x:pointers_content_data a -> f:(a -> int) -> r:MO.loc -> h':HS.mem 
  -> Lemma(requires(
    well_formed_pointers_content_data_base #a h x /\ 
    well_formed_disjoint_meet_type_from_pointers_content_data #a h r x /\
    MO.modifies r h h' /\ 
    member_disjoint_max_pointers_content_data #a h n x f  ))
  (ensures(
    (well_formed_pointers_content_data_base #a h' x)/\
    (member_disjoint_max_pointers_content_data #a h' n x f)
  )) 
let modifies_disjoint_max_pointers_content_data_lemma #a h n x f r h' =
  modifies_disjoint_well_formed_pointers_content_data_and_footprint_base h x r h';
  modifies_disjoint_max_rnode_lemma #a h n x.pl x.l f r h'

val modifies_disjoint_max_pointers_data_lemma: #a:eqtype -> h:HS.mem -> n:int -> x:pointers_data a -> f:(a -> int) -> r:MO.loc -> h':HS.mem 
  -> Lemma(requires(
    well_formed_pointers_data_base #a h x /\ 
    well_formed_disjoint_meet_type_from_pointers_data #a h r x /\
    MO.modifies r h h' /\ 
    member_disjoint_max_pointers_data #a h n x f  ))
  (ensures(
    (well_formed_pointers_data_base #a h' x) /\
    (member_disjoint_max_pointers_data #a h' n x f)
  )) 
let modifies_disjoint_max_pointers_data_lemma #a h n x f r h' =
  modifies_disjoint_well_formed_pointers_data_and_footprint_base h x r h';
  modifies_disjoint_max_pointers_content_data_lemma #a h n (B.get h x 0) f r h'


val modifies_disjoint_max_listpointers_data_lemma: #a:eqtype -> h:HS.mem -> n:int -> l:list(pointers_data a) -> f:(a -> int) -> r:MO.loc -> h':HS.mem 
  -> Lemma(requires(
    well_formed_listpointers_data_base #a h l /\ 
    well_formed_disjoint_meet_type_from_listpointers_data #a h r l /\
    MO.modifies r h h' /\ 
    member_disjoint_max_listpointers_data #a h n l f  ))
  (ensures(
    (well_formed_listpointers_data_base #a h' l)/\
    (member_disjoint_max_listpointers_data #a h' n l f)
  )) 
let rec modifies_disjoint_max_listpointers_data_lemma #a h n l f r h' =
  modifies_disjoint_well_formed_listpointers_data_and_footprint_base h l r h';
  match l with
  | [] -> ()
  | hd::tl -> 
    modifies_disjoint_max_pointers_data_lemma #a h n hd f r h';
    modifies_disjoint_max_listpointers_data_lemma #a h n tl f r h'


val max_chenge_rnode_lemma: #a:eqtype -> h:HS.mem -> v:a -> c1:rnode a -> l1:G.erased (list a) -> c2:rnode a -> l2:G.erased (list a) -> f:(a -> int)
  -> Lemma(requires(
    well_formed h c1 l1 /\ 
    well_formed h c2 l2 /\ 
    not(B.g_is_null c1) /\
    not(B.g_is_null c2) /\
    member_disjoint_max_rnode h (f v) c1 l1 f /\
    ((B.get h c2 0).data == v) /\ 
    ((B.get h c2 0).next == c1) 
  ))
  (ensures(
    (member_disjoint_max_rnode h ((f v)+1) c2 l2 f) /\
    not(member_disjoint_max_rnode h (f v) c2 l2 f)
     )) (decreases (G.reveal l2))
let max_chenge_rnode_lemma #a h v c1 l1 c2 l2 f =
  member_disjoint_max_rnode_lemma #a h (f v) ((f v) + 1) c1 l1 f

val max_chenge_pointers_content_data_lemma: #a:eqtype -> h:HS.mem -> v:a -> x1:pointers_content_data a -> x2:pointers_content_data a -> f:(a -> int)
  -> Lemma(requires(
    well_formed_pointers_content_data_base h x1  /\ 
    well_formed_pointers_content_data_base h x2 /\ 
    member_disjoint_max_pointers_content_data h (f v) x1 f /\
    ((B.get h x2.pl 0).data == v) /\ 
    ((B.get h x2.pl 0).next == x1.pl) 
  ))
  (ensures(
    (member_disjoint_max_pointers_content_data h ((f v)+1) x2 f) /\
    not(member_disjoint_max_pointers_content_data h (f v) x2 f)
     )) 
let max_chenge_pointers_content_data_lemma #a h v x1 x2 f =
  max_chenge_rnode_lemma #a h v x1.pl x1.l x2.pl x2.l f

val max_chenge_pointers_data_lemma: #a:eqtype -> h:HS.mem -> v:a -> x1:pointers_data a -> x2:pointers_data a -> f:(a -> int)
  -> Lemma(requires(
    well_formed_pointers_data_base h x1  /\ 
    well_formed_pointers_data_base h x2 /\ 
    member_disjoint_max_pointers_data h (f v) x1 f /\
    ((B.get h (B.get h x2 0).pl 0).data == v) /\ 
    ((B.get h (B.get h x2 0).pl 0).next == (B.get h x1 0).pl) 
  ))
  (ensures(
    (member_disjoint_max_pointers_data h ((f v)+1) x2 f) /\
    not(member_disjoint_max_pointers_data h (f v) x2 f)
     )) 
let max_chenge_pointers_data_lemma #a h v x1 x2 f =
  max_chenge_pointers_content_data_lemma #a h v (B.get h x1 0) (B.get h x2 0) f


val max_append_e_listpointers_data_lemma: #a:eqtype -> h:HS.mem -> n:int -> l:list (pointers_data a) -> x:pointers_data a -> f:(a -> int)
  -> Lemma(requires(
    well_formed_listpointers_data_base h l /\ 
    well_formed_pointers_data_base h x /\
    member_disjoint_max_listpointers_data h n l f /\
    member_disjoint_max_pointers_data h n x f
  ))
  (ensures(
    (member_disjoint_max_listpointers_data h n (x::l) f)
  ))
let rec max_append_e_listpointers_data_lemma #a h n l x f = 
  match l with
  | [] -> ()
  | hd::tl -> max_append_e_listpointers_data_lemma #a h n tl x f

val max_append_n_listpointers_data_lemma: #a:eqtype -> h:HS.mem -> n:int -> l:list (pointers_data a) -> x:pointers_data a -> f:(a -> int)
  -> Lemma(requires(
    well_formed_listpointers_data_base h l /\ 
    well_formed_pointers_data_base h x /\
    member_disjoint_max_listpointers_data h n l f /\
    not(member_disjoint_max_pointers_data h n x f)
  ))
  (ensures(
    not(member_disjoint_max_listpointers_data h n (x::l) f)
  ))
let rec max_append_n_listpointers_data_lemma #a h n l x f = 
  match l with
  | [] -> ()
  | hd::tl -> max_append_n_listpointers_data_lemma #a h n tl x f

val max_append_nn_pointers_data_lemma_s1: #a:eqtype -> h:HS.mem -> n:int -> x:pointers_data a -> y:pointers_data a -> f:(a -> int)
  -> Lemma(requires(
    well_formed_pointers_data_base h x /\
    well_formed_pointers_data_base h y /\
    (well_formed_listpointers_data_base h (x::[y])) /\
    not(member_disjoint_max_pointers_data h n x f) /\
    member_disjoint_max_pointers_data h n y f
  ))
  (ensures(
    not(member_disjoint_max_listpointers_data h n (x::[y]) f)
  ))
let max_append_nn_pointers_data_lemma_s1 #a h n x y f = ()

val max_append_nn_pointers_data_lemma_s2: #a:eqtype -> h:HS.mem -> n:int -> x:pointers_data a -> y:pointers_data a -> f:(a -> int)
  -> Lemma(requires(
    (well_formed_listpointers_data_base h (x::[y])) /\
    (well_formed_listpointers_data_base h (y::[x]))
  ))
  (ensures(
    (member_disjoint_max_listpointers_data h n (x::[y]) f) <==> (member_disjoint_max_listpointers_data h n (y::[x]) f)
  ))
let max_append_nn_pointers_data_lemma_s2 #a h n x y f = ()

assume val max_append_nn_listpointers_data_lemma: #a:eqtype -> h:HS.mem -> n:int -> l:list (pointers_data a) -> x:pointers_data a -> f:(a -> int)
  -> Lemma(requires(
    well_formed_listpointers_data_base h l /\ 
    well_formed_pointers_data_base h x /\
    not(member_disjoint_max_listpointers_data h n l f)// /\
   // member_disjoint_max_pointers_data h n x f
  ))
  (ensures(
    not(member_disjoint_max_listpointers_data h n (x::l) f)
  ))


val insert_sort_listpointers_data_s_cons: #a:eqtype -> l:list (pointers_data a) -> pre:pointers_data a ->  x:pointers_data a -> v:a -> f:(a -> Tot int) -> f':(a -> Tot int)
-> ST (list (pointers_data a))
  (requires( fun h -> 
    well_formed_listpointers_data_base #a h l /\ 
    well_formed_listpointers_data #a h l /\
    well_formed_pointers_data_base #a h x /\ 
    well_formed_pointers_data #a h x l /\
    well_formed_pointers_data_base #a h pre /\ 
    well_formed_pointers_data #a h pre l /\
    well_formed_pointers_data #a h pre [x] /\      
    sorted h l f /\ 
    member_disjoint_max_listpointers_data #a h (f' v) l f' /\ 
    member_disjoint_max_pointers_data #a h ((f' v)+1) pre f' /\ 
    member_disjoint_max_pointers_data #a h ((f' v) + 1) x f' /\ 
    not(member_disjoint_max_pointers_data #a h (f' v) x f')
  ))
  (ensures(fun h0 nl h1 -> 
    (h0 == h1) /\
    well_formed_listpointers_data_base #a h1 nl /\
    well_formed_listpointers_data #a h1 nl /\
    Cons? nl /\ 
    sorted h1 nl f /\ 
    (L.length nl = L.length l + 1) /\
    (forall i. L.memP i nl ==> L.memP i l \/ (i == x)) /\ 
    (L.memP pre l ==> well_formed_pointers_data #a h1 pre nl) /\ 
    not(member_disjoint_max_listpointers_data #a h1 (f' v) nl f') /\
    member_disjoint_max_listpointers_data #a h1 ((f' v)+1) nl f' /\
    member_disjoint_max_pointers_data #a h1 ((f' v)+1) pre f'
  ))
let rec insert_sort_listpointers_data_s_cons #a l pre x v f f' = 
  match l with
  | [] -> [x]
  | hd::tl ->
    if (getdetail_func_type_funcST f x >= getdetail_func_type_funcST f hd) then 
      let h = get () in 
        insert_hd_tl_Lemma2 h l pre x;
        member_disjoint_max_listpointers_data_lemma h (f' v) ((f' v) + 1) l f';
        max_append_n_listpointers_data_lemma h (f' v) l x f';
        max_append_e_listpointers_data_lemma h ((f' v) + 1 ) l x f';
        x::l
    else
    let h = get () in
    assert(getdetail_func_type_func h f hd >= getdetail_func_type_func h f x);
    checksorted_lem_type_lemma h l f;
    assert(checksorted_lem_type h l f);
    assert(checksorted h tl (getdetail_func_type_func h f hd) f);
    let s = insert_sort_listpointers_data_s_cons #a tl pre x v f f' in
      checksorted_lem_type_lemma5 h (x::tl) s (getdetail_func_type_func h f hd) f; 
      assert(checksorted h s (getdetail_func_type_func h f hd) f);
      checksorted_lem_type_lemma h s f;
      checksorted_lem_type_lemma2 h (hd::s) f;
      assert(getdetail_func_type_func h f hd >= getdetail_func_type_func h f (L.hd s));
      assert(well_formed_pointers_data #a h x tl);
      assert(well_formed_pointers_data #a h x [hd]);
      assert(well_formed_pointers_data #a h hd tl);
      well_formed_pointers_data_chenge_lemma h x hd;
      assert(well_formed_pointers_data #a h hd [x]);
      assert(well_formed_listpointers_data_base #a h (x::tl));
      assert(well_formed_listpointers_data #a h (x::tl));
      assert(well_formed_pointers_data #a h hd (x::tl));
      memEqual_well_formed_pointers_data_Lemma h (x::tl) s hd;
      member_disjoint_max_pointers_data_lemma h (f' v) ((f' v) + 1) hd f';
      max_append_nn_listpointers_data_lemma h (f' v) s hd f';
      max_append_e_listpointers_data_lemma h ((f' v) + 1 ) s hd f';
      hd::s

val insert_sort_listpointers_data_s_nil: #a:eqtype -> l:list (pointers_data a) ->  x:pointers_data a -> v:a -> f:(a -> Tot int) -> f':(a -> Tot int)
-> ST (list (pointers_data a))
  (requires( fun h -> 
    well_formed_listpointers_data_base #a h l /\ 
    well_formed_listpointers_data #a h l /\
    well_formed_pointers_data_base #a h x /\ 
    well_formed_pointers_data #a h x l /\   
    sorted h l f /\ 
    member_disjoint_max_listpointers_data #a h (f' v) l f' /\ 
    member_disjoint_max_pointers_data #a h ((f' v) + 1) x f' /\ 
    not(member_disjoint_max_pointers_data #a h (f' v) x f')
  ))
  (ensures(fun h0 nl h1 -> 
    (h0 == h1) /\
    well_formed_listpointers_data_base #a h1 nl /\
    well_formed_listpointers_data #a h1 nl /\
    Cons? nl /\ 
    sorted h1 nl f /\ 
    (L.length nl = L.length l + 1) /\
    (forall i. L.memP i nl ==> L.memP i l \/ (i == x)) /\ 
    not(member_disjoint_max_listpointers_data #a h1 (f' v) nl f') /\
    member_disjoint_max_listpointers_data #a h1 ((f' v)+1) nl f'
  ))
let rec insert_sort_listpointers_data_s_nil #a l x v f f' = 
  match l with
  | [] -> [x]
  | hd::tl ->
    if (getdetail_func_type_funcST f x >= getdetail_func_type_funcST f hd) then 
      let h = get () in 
        member_disjoint_max_listpointers_data_lemma h (f' v) ((f' v) + 1) l f';
        max_append_n_listpointers_data_lemma h (f' v) l x f';
        max_append_e_listpointers_data_lemma h ((f' v) + 1 ) l x f';
        x::l
    else
    let h = get () in
    assert(getdetail_func_type_func h f hd >= getdetail_func_type_func h f x);
    checksorted_lem_type_lemma h l f;
    assert(checksorted_lem_type h l f);
    assert(checksorted h tl (getdetail_func_type_func h f hd) f);
    let s = insert_sort_listpointers_data_s_nil #a tl x v f f' in
      checksorted_lem_type_lemma5 h (x::tl) s (getdetail_func_type_func h f hd) f; 
      assert(checksorted h s (getdetail_func_type_func h f hd) f);
      checksorted_lem_type_lemma h s f;
      checksorted_lem_type_lemma2 h (hd::s) f;
      assert(getdetail_func_type_func h f hd >= getdetail_func_type_func h f (L.hd s));
      assert(well_formed_pointers_data #a h x tl);
      assert(well_formed_pointers_data #a h x [hd]);
      assert(well_formed_pointers_data #a h hd tl);
      well_formed_pointers_data_chenge_lemma h x hd;
      assert(well_formed_pointers_data #a h hd [x]);
      assert(well_formed_listpointers_data_base #a h (x::tl));
      assert(well_formed_listpointers_data #a h (x::tl));
      assert(well_formed_pointers_data #a h hd (x::tl));
      memEqual_well_formed_pointers_data_Lemma h (x::tl) s hd;
      member_disjoint_max_pointers_data_lemma h (f' v) ((f' v) + 1) hd f';
      max_append_nn_listpointers_data_lemma h (f' v) s hd f';
      max_append_e_listpointers_data_lemma h ((f' v) + 1 ) s hd f';
      hd::s

val pre_data_well_formed_pointers_data_lemma1: #a:eqtype -> h:HS.mem -> l:list (pointers_data a) -> pre:(pointers_data a) -> x:pointers_data a ->
  Lemma(requires(
    well_formed_listpointers_data_base h l /\
    well_formed_listpointers_data h l /\ 
    well_formed_pointers_data_base h pre /\
    well_formed_pointers_data h pre l /\
    well_formed_pointers_data_base h x /\ 
    well_formed_pointers_data h x l 
    )) (ensures(L.memP pre l ==> well_formed_pointers_data h x [pre]))
  let rec pre_data_well_formed_pointers_data_lemma1 #a h l pre x
    = match l with
    | [] -> ()
    | hd::tl -> pre_data_well_formed_pointers_data_lemma1 #a h tl pre x


val insert_nil: #a:eqtype -> l:list (pointers_data a ) -> v:a -> f:(a -> int) -> f':(a -> int) -> 
  ST (list (pointers_data a))
  (requires(fun h -> 
      well_formed_listpointers_data_base #a h l /\ 
      well_formed_listpointers_data #a h l /\ 
      member_disjoint_max_listpointers_data #a h (f' v) l f' /\
      sorted h l f
  ))
  (ensures (fun h0 nl h1 -> 
     Cons? nl  /\ 
     // (let d = L.hd nl in 
     //(exists i. (MO.modifies (MO.loc_union (MO.loc_buffer (B.get h1 i 0).pl ) (MO.loc_buffer d)) h0 h1)) /\ 
        (*
          (not(B.g_is_null (B.get h1 d 0).pl)) /\ 
          ((B.get h1 (B.get h1 d 0).pl 0).data == v) /\
        *)
        well_formed_listpointers_data_base #a h1 nl /\ 
        well_formed_listpointers_data #a h1 nl /\ 
        not(member_disjoint_max_listpointers_data #a h1 (f' v) nl f') /\
        member_disjoint_max_listpointers_data #a h1 ((f' v)+1) nl f' /\
        sorted h1 nl f
      //)
    ))
let insert_nil #a l v f f'= 
  let h0 = get () in
  let c = {
    data = v;
    next = B.null;
  } in
  let h0 = get () in
  let newrnode:rnode a = B.malloc HS.root c 1ul in
  unused_in_well_formed_disjoint_from_listpointers_data h0 newrnode l;
  let h1 = get () in
  modifies_disjoint_well_formed_listpointers_data h0 l (MO.loc_buffer newrnode) h1; 
  modifies_disjoint_max_listpointers_data_lemma h0 (f' v) l f' (MO.loc_buffer newrnode) h1;
  modifies_disjoint_sorted h0 l f (MO.loc_buffer newrnode) h1;
  let content:pointers_content_data a = {pl = newrnode; l = [v]} in
  assert(well_formed_pointers_content_data_base h1 content);
  let data: pointers_data a = B.malloc HS.root content 1ul in 
  unused_in_well_formed_disjoint_from_listpointers_data h1 data l;
  let h2 = get () in
  modifies_disjoint_well_formed_listpointers_data h1 l (MO.loc_buffer data) h2; 
  modifies_disjoint_max_listpointers_data_lemma h1 (f' v) l f' (MO.loc_buffer data) h2;
  modifies_disjoint_sorted h1 l f (MO.loc_buffer data) h2;
  modifies_well_formed_disjoint_meet_type_from_listpointers_data h1 (MO.loc_buffer data) l (MO.loc_buffer data) h2;
  assert(well_formed_pointers_data_base #a h2 data);
  member_disjoint_max_include_c_listpointers_data_lemma h2 v l f';
  listpointers_data_well_formed_supportLemma h2 l;
  listpointers_data_a_not_include_c_supportLemma h2 v l;
  assert(well_formed_pointers_content_data_base #a h2 (B.get h2 data 0));
  assert(well_formed_listpointers_content_data_base #a h2 (pointers_data_to_pointers_content_data h2 l));
  assert(not(B.g_is_null (B.get h2 data 0).pl));
 // let r = B.get h2 (B.get h2 data 0).pl 0 in
  assert((B.g_is_null (B.get h2 (B.get h2 data 0).pl 0).next));
  assert(L.isEmpty (L.tl (G.reveal (B.get h2 data 0).l)));
  assert(listpointers_content_data_a_not_include_c #a h2 v (pointers_data_to_pointers_content_data h2 l));
  well_formed_pointers_content_nildataLemma h2 (B.get h2 data 0) (pointers_data_to_pointers_content_data h2 l);
  assert(well_formed_pointers_data_base #a h2 data);
  assert(well_formed_listpointers_data_base #a h2 l); 
  assert(well_formed_listpointers_data #a h2 l);
  assert(well_formed_pointers_content_data #a h2 (B.get h2 data 0) (pointers_data_to_pointers_content_data #a h2 l));
  assert(well_formed_disjoint_meet_type_from_listpointers_data #a h2 (MO.loc_buffer data) l);
  well_formed_pointers_data_specialLemma h2 data l;
  assert(well_formed_pointers_data_base #a h2 data);
  assert(well_formed_listpointers_data #a h2 l);
  assert(well_formed_pointers_data #a h2 data l);
  assert(sorted h2 l f);
  assert(member_disjoint_max_listpointers_data h2 (f' v) l f');
  assert(member_disjoint_max_pointers_data #a h2 ((f' v) + 1) data f'); 
  assert(not(member_disjoint_max_pointers_data #a h2 (f' v) data f'));
  insert_sort_listpointers_data_s_nil l data v f f'


(*

    well_formed_listpointers_data_base #a h l /\ 
    well_formed_listpointers_data #a h l /\
    well_formed_pointers_data_base #a h x /\ 
    well_formed_pointers_data #a h x l /\   
    sorted h l f /\ 
    member_disjoint_max_listpointers_data #a h (f' v) l f' /\ 
    member_disjoint_max_pointers_data #a h ((f' v) + 1) x f' /\ 
    not(member_disjoint_max_pointers_data #a h (f' v) x f')
*)
val insert_cons: #a:eqtype -> l:list (pointers_data a) -> pre:(pointers_data a){L.memP pre l} -> v:a -> f:(a -> int) -> f':(a -> int)
    -> ST (list (pointers_data a))
    (requires (fun h ->
      Cons? l /\
      well_formed_listpointers_data_base #a h l /\ 
      well_formed_listpointers_data #a h l /\ 
      well_formed_pointers_data_base #a h pre /\
      well_formed_pointers_data #a h pre l /\ 
      member_disjoint_max_listpointers_data #a h (f' v) l f' /\
      //listpointers_data_a_not_include_c #a h v l /\
      member_disjoint_max_pointers_data #a h (f' v) pre f' /\
     // pointers_data_a_not_include_c #a h v pre /\ 
      sorted h l f
    ))
    (ensures (fun h0 nl h1 -> 
     Cons? nl 
     /\ 
      (L.length nl = L.length l + 1) /\
     //(let d = L.hd nl in 
     //(exists i. (MO.modifies (MO.loc_union (MO.loc_buffer (B.get h1 i 0).pl ) (MO.loc_buffer d)) h0 h1)) /\ 
        (*
          (not(B.g_is_null (B.get h1 d 0).pl)) /\ 
          ((B.get h1 (B.get h1 d 0).pl 0).data == v) /\
        *)
        well_formed_listpointers_data_base #a h1 nl /\ 
        well_formed_listpointers_data #a h1 nl /\
        well_formed_pointers_data_base #a h1 pre /\
        well_formed_pointers_data #a h1 pre nl /\ 
        not(member_disjoint_max_listpointers_data #a h1 (f' v) nl f') /\
        member_disjoint_max_listpointers_data #a h1 ((f' v)+1) nl f' /\
        member_disjoint_max_pointers_data #a h1 ((f' v)+1) pre f' /\
        sorted h1 nl f
        //)
    ))
let insert_cons #a l pre v f f' = 
  let h0 = get () in
  member_disjoint_max_include_c_listpointers_data_lemma h0 v l f';
  assert(listpointers_data_a_not_include_c #a h0 v l);
  assert(member_disjoint_max_listpointers_data #a h0 (f' v) l f');
  member_disjoint_max_include_c_pointers_data_lemma h0 v pre f';
  assert(pointers_data_a_not_include_c #a h0 v pre);
  assert(member_disjoint_max_pointers_data #a h0 (f' v) pre f');
  let defaultpcdata:pointers_content_data a = {pl = B.null; l = []}  in
  let pc: B.pointer (pointers_content_data a) = B.malloc HS.root defaultpcdata 1ul in 
  unused_in_well_formed_disjoint_from_listpointers_data h0 pc l;
  unused_in_well_formed_disjoint_from_pointers_data h0 pc pre;
  let h1 = get () in
  modifies_disjoint_well_formed_listpointers_data h0 l (MO.loc_buffer pc) h1; 
  modifies_disjoint_well_formed_pointers_data h0 pre l (MO.loc_buffer pc) h1;
  modifies_well_formed_disjoint_meet_type_from_listpointers_data h0 (MO.loc_buffer pc) l  (MO.loc_buffer pc) h1;
  modifies_well_formed_disjoint_meet_type_from_pointers_data h0 (MO.loc_buffer pc) pre (MO.loc_buffer pc) h1;
  modifies_disjoint_listpointers_data_a_not_include_c h0 v l (MO.loc_buffer pc) h1;
  modifies_disjoint_pointers_data_a_not_include_c h0 v pre (MO.loc_buffer pc) h1;
  modifies_disjoint_max_listpointers_data_lemma h0 (f' v) l f' (MO.loc_buffer pc) h1;
  modifies_disjoint_max_pointers_data_lemma h0 (f' v) pre f' (MO.loc_buffer pc) h1;
  assert(member_disjoint_max_listpointers_data #a h1 (f' v) l f');
  assert(member_disjoint_max_pointers_data #a h1 (f' v) pre f');
  modifies_disjoint_sorted h0 l f (MO.loc_buffer pc) h1;
  let data = insert_pre_pl #a l pre pc in 
  let h2 = get () in
  modifies_disjoint_listpointers_data_a_not_include_c #a h1 v l (MO.loc_buffer pc) h2;
  modifies_disjoint_pointers_data_a_not_include_c #a h1 v pre (MO.loc_buffer pc) h2;
  modifies_disjoint_sorted h1 l f (MO.loc_buffer pc) h2;
  modifies_disjoint_well_formed_pointers_data h1 pre l (MO.loc_buffer pc) h2;
  modifies_disjoint_max_listpointers_data_lemma h1 (f' v) l f' (MO.loc_buffer pc) h2;
  modifies_disjoint_max_pointers_data_lemma h1 (f' v) pre f' (MO.loc_buffer pc) h2;
  assert(member_disjoint_max_listpointers_data #a h2 (f' v) l f');
  assert(member_disjoint_max_pointers_data #a h2 (f' v) pre f');
  //assert(MO.modifies (MO.loc_buffer pc) h1 h2);
  assert(well_formed_listpointers_data_base #a h2 l);
  assert(well_formed_listpointers_data #a h2 l);
  assert(well_formed_pointers_data_base #a h2 data);
  assert(well_formed_pointers_data #a h2 data l);
  assert(well_formed_disjoint_meet_type_from_listpointers_data #a h2 (MO.loc_buffer data) l);
  assert(listpointers_data_a_not_include_c #a h2 v l);
  assert((B.get h2 data 0).pl == (B.get h2 pre 0).pl);
  push_pointers_data #a l data v;
  let h3 = get () in
  modifies_disjoint_well_formed_pointers_data h2 pre l (MO.loc_buffer data) h3;
  modifies_disjoint_max_listpointers_data_lemma h2 (f' v) l f' (MO.loc_buffer data) h3;
  modifies_disjoint_max_pointers_data_lemma h2 (f' v) pre f' (MO.loc_buffer data) h3;
  assert(member_disjoint_max_listpointers_data #a h3 (f' v) l f');
  assert(member_disjoint_max_pointers_data #a h3 (f' v) pre f');
  max_chenge_pointers_data_lemma h3 v pre data f';
  assert(member_disjoint_max_pointers_data #a h3 ((f' v)+1) data f');
  assert(not(member_disjoint_max_pointers_data #a h3 (f' v) data f'));
  modifies_disjoint_sorted h2 l f (MO.loc_buffer data) h3;
  modifies_disjoint_pointers_data_a_not_include_c #a h2 v pre (MO.loc_buffer data) h3;
 // assert(MO.modifies (MO.loc_buffer data) h2 h3);
  //assert(MO.modifies (MO.loc_union (MO.loc_buffer (B.get h3 data 0).pl ) (MO.loc_buffer data)) h1 h3);
  assert(well_formed_listpointers_data_base #a h3 l);
  assert(well_formed_listpointers_data #a h3 l);
  assert(well_formed_pointers_data_base #a h3 data);
  assert(well_formed_pointers_data #a h3 data l);
  //insert_hd_tl_Lemma #a h3 l data;
  assert(well_formed_pointers_data_base #a h3 pre);
  assert(well_formed_pointers_data #a h3 pre l);
  pre_data_well_formed_pointers_data_lemma1 h3 l pre data;
  assert(well_formed_pointers_data #a h3 data [pre]);
  well_formed_pointers_data_chenge_lemma h3 data pre;
  assert(well_formed_pointers_data #a h3 pre [data]);
  insert_sort_listpointers_data_s_cons #a l pre data v f f'


val delete: #a:eqtype -> l:list (pointers_data a) -> x:(pointers_data a){L.memP x l} -> v:a -> f:(a -> int) -> f':(a -> int)
  -> ST (list (pointers_data a))
  (requires( fun h -> 
    well_formed_listpointers_data_base #a h l /\ 
    well_formed_listpointers_data #a h l /\ 
    well_formed_pointers_data_base #a h x /\
    well_formed_pointers_data #a h x l /\ 
   // not(member_disjoint_max_listpointers_data #a h (f' v) l f') /\
    member_disjoint_max_listpointers_data #a h ((f' v)+1) l f' /\
    sorted h l f
  ))
  (ensures( fun h0 nl h1 -> 
    (h0 == h1) /\ 
    well_formed_listpointers_data_base #a h1 nl /\ 
    well_formed_listpointers_data #a h1 nl /\ 
    (forall i. L.memP i nl ==> L.memP i l) /\
   // not(member_disjoint_max_listpointers_data #a h1 (f' v) nl f') /\
    member_disjoint_max_listpointers_data #a h1 ((f' v)+1) nl f' /\
    sorted h1 nl f
  ))
let rec delete #a l x v f f' = 
  match l with
  | [] -> []
  | hd::tl -> 
    if ((!* (!* x).pl).data = (!* (!* hd).pl).data) then 
      let h = get () in 
    //  assert(not(member_disjoint_max_listpointers_data #a h (f' v) tl f'));
      assert(member_disjoint_max_listpointers_data #a h ((f' v)+1) tl f');
      tl
    else 
      let s = delete #a tl x v f f' in
      let h = get () in
      assert(well_formed_listpointers_data_base #a h s);
      assert(well_formed_listpointers_data #a h s);
      assert(well_formed_pointers_data_base #a h hd);
      memEqual_well_formed_pointers_data_Lemma #a h tl s hd;
      assert(well_formed_pointers_data #a h hd s);
      insert_hd_tl_Lemma #a h s hd;
      checksorted_lem_type_lemma h l f;
      checksorted_lem_type_lemma h s f;
     // max_append_nn_listpointers_data_lemma h (f' v) s hd f';
      max_append_e_listpointers_data_lemma h ((f' v) + 1 ) s hd f';
    //  assert(not(member_disjoint_max_listpointers_data #a h (f' v) (hd::s) f'));
      assert(member_disjoint_max_listpointers_data #a h ((f' v)+1) (hd::s) f');
      checksorted_lem_type_lemma5 h tl s (getdetail_func_type_func h f hd) f; 
      //assert(checksorted h s (getdetail_func_type_func h f hd) f);
      checksorted_lem_type_lemma h s f;
      checksorted_lem_type_lemma2 h (hd::s) f;
      hd::s
