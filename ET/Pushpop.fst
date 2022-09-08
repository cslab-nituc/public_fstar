module Pushpop
open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module MO = LowStar.Modifies
open LowStar.BufferOps
open FStar.HyperStack.ST

#set-options "--__no_positivity"
noeq type rnode (a:Type0) = B.pointer_or_null (node a)
and node (a:Type0) = 
{
    data:a;
    next:rnode a;
}
val well_formed: #a:Type-> h:HS.mem -> c:rnode a -> l: G.erased (list a) -> GTot Type0 (decreases (G.reveal l))
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

val length_functional: #a:Type -> h:HS.mem -> c:rnode a -> l1:G.erased (list a) -> l2:G.erased (list a)
-> Lemma (requires (well_formed h c l1 /\ well_formed h c l2)) (ensures (l1 == l2))
    (decreases (G.reveal l1))[SMTPat (well_formed h c l1); SMTPat (well_formed h c l2) ] 
let rec length_functional #a h c l1 l2 =
  if B.g_is_null c
  then ()
  else
    let { next = next } = B.get h c 0 in
    length_functional h next (G.hide (L.tl (G.reveal l1))) (G.hide (L.tl (G.reveal l2)))

#set-options "--max_ifuel 1 --max_fuel 2"
val footprint: #a: Type -> h: HS.mem -> c: rnode a -> l: G.erased (list a) -> Ghost MO.loc
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

assume val footprintDataEqual:#a: Type -> h: HS.mem -> c1: rnode a -> l1: G.erased (list a) -> c2: rnode a -> l2: G.erased (list a) -> 
  Lemma(requires(well_formed h c1 l1 /\ well_formed h c2 l2 /\ ((footprint h c1 l1) == (footprint h c2 l2)))) 
  (ensures( c1 == c2 /\ l1 == l2)) (decreases (G.reveal l1))
(*
let rec footprintDataEqual #a h c1 l1 c2 l2 =
  if not(B.g_is_null c1) && not(B.g_is_null c2) then 
    footprintDataEqual #a h (B.get h c1 0).next (G.hide(L.tl (G.reveal l1))) (B.get h c2 0).next (G.hide(L.tl (G.reveal l2)))
  else ()
*)

val modifies_disjoint_footprint: #a:Type -> h:HS.mem -> c:rnode a -> l:G.erased (list a) -> r:MO.loc -> h':HS.mem 
 -> Lemma (requires ( well_formed h c l /\ MO.loc_disjoint r (footprint h c l) /\ MO.modifies r h h' ))
  (ensures ( well_formed h' c l /\ ((footprint h' c l) == (footprint h c l )))) (decreases (G.reveal l))
let rec modifies_disjoint_footprint #a h c l r h'
= if B.g_is_null c
  then ()
  else begin
    let {next = next;} = B.get h c 0 in
    modifies_disjoint_footprint h next (G.hide (L.tl (G.reveal l))) r h'
  end

val well_formed_distinct_lengths_disjoint: #a:Type -> c1: B.pointer (node a) -> c2: B.pointer (node a) -> l1: G.erased (list a) -> l2: G.erased (list a) -> h: HS.mem
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

val well_formed_gt_lengths_disjoint_from_list: #a:Type -> h:HS.mem -> c1: B.pointer_or_null (node a) -> c2: B.pointer_or_null (node a)
    -> l1: G.erased (list a) -> l2: G.erased (list a)
    -> Lemma (requires (well_formed h c1 l1 /\ well_formed h c2 l2 /\ ((L.length (G.reveal l1) > L.length (G.reveal l2)))))
  (ensures (MO.loc_disjoint (MO.loc_buffer c1) (footprint h c2 l2))) (decreases (G.reveal l2))
let rec well_formed_gt_lengths_disjoint_from_list #a h c1 c2 l1 l2 = 
    (match G.reveal l2 with
    | [] -> ()
    | _ ->
        well_formed_distinct_lengths_disjoint c1 c2 l1 l2 h;
        well_formed_gt_lengths_disjoint_from_list h c1 (B.get h c2 0).next l1 (G.hide (L.tl (G.reveal l2))))

val well_formed_head_tail_disjoint: #a:Type -> h:HS.mem -> c:B.pointer (node a) -> l:G.erased (list a)
    ->  Lemma (requires (well_formed h c l)) 
    (ensures ( MO.loc_disjoint (MO.loc_buffer c) (footprint h (B.get h c 0).next (G.hide (L.tl (G.reveal l))))))
let well_formed_head_tail_disjoint #a h c l
= well_formed_gt_lengths_disjoint_from_list h c (B.get h c 0).next l (G.hide (L.tl (G.reveal l)))

val unused_in_well_formed_disjoint_from_list: #a:Type -> #b:Type -> h: HS.mem -> r:B.buffer a -> c: B.pointer_or_null (node b) -> l:G.erased (list b)
 ->  Lemma(requires (r `B.unused_in` h /\ well_formed h c l))
  (ensures (MO.loc_disjoint (MO.loc_buffer r) (footprint h c l)))
  (decreases (G.reveal l))
let rec unused_in_well_formed_disjoint_from_list #a #b h r c l
= (match G.reveal l with
  | [] -> ()
  | _ -> unused_in_well_formed_disjoint_from_list #a #b h r (B.get h c 0).next (G.hide (L.tl (G.reveal l))))


val pop: (#a: Type) -> (#n: G.erased (list a)) -> (pl: B.pointer (rnode a)) ->
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

noeq type pointers_data (a:Type) =
{
  l:G.erased (list a);
  pl:B.pointer (rnode a);
}

val well_formed_pointers_data_base: #a:Type -> h:HS.mem -> d:pointers_data a -> GTot Type0
let well_formed_pointers_data_base #a h d =
      B.live h d.pl /\
      well_formed h (B.get h d.pl 0) d.l /\ 
      MO.loc_disjoint (MO.loc_buffer d.pl) (footprint h (B.get h d.pl 0) d.l) /\
      not(B.g_is_null (B.get h d.pl 0))

val well_formed_listpointers_data_base: #a:Type -> h:HS.mem -> dl:list (pointers_data a) -> GTot Type0
let rec well_formed_listpointers_data_base #a h dl =
    match dl with
    | [] -> True
    | hd::tl -> (well_formed_pointers_data_base h hd) /\ (well_formed_listpointers_data_base h tl)

val nodelast:  #a:Type -> h:HS.mem -> c:(rnode a){not(B.g_is_null c)} -> l:G.erased (list a){not(L.isEmpty (G.reveal l))} 
  -> Ghost (cs:(rnode a){not(B.g_is_null cs)}) (requires (
    well_formed h c l
  )) (ensures (fun r -> let hs = B.get h r 0 in (hs.data == L.last (G.reveal l))))
  (decreases (G.reveal l))
let rec nodelast #a h c l = 
  let cs = B.get h c 0 in 
  if B.g_is_null (cs.next) then c
  else nodelast h (cs.next) (G.hide (L.tl (G.reveal l)))

val dataEqualSameLocationT: #a:Type -> h:HS.mem -> c1:(rnode a){not(B.g_is_null c1)} ->l1:(G.erased (list a)){not(L.isEmpty (G.reveal l1))} -> c2:(rnode a) -> l2:(G.erased (list a)) -> 
  Ghost Type0 (requires( well_formed h c1 l1 /\ well_formed h c2 l2)) 
  (ensures( fun r -> True)) (decreases (G.reveal l2))
let rec dataEqualSameLocationT #a h c1 l1 c2 l2 =
  let d1 = B.get h c1 0 in 
    if not (B.g_is_null c2) then 
    let d2 = B.get h c2 0 in 
     // ((d1 == d2) ==> ((footprint h c1 l1) == (footprint h c2 l2)) /\ (l1 == l2) /\ (c1 == c2))
        ///\ 
        (dataEqualSameLocationT #a h c1 l1 d2.next (G.hide (L.tl (G.reveal l2))))
    else True

val dataEqualSameLocation: #a:Type -> h:HS.mem -> c1:(rnode a) ->l1:(G.erased (list a))-> c2:(rnode a) -> l2:(G.erased (list a)) -> 
  Ghost Type0 (requires( well_formed h c1 l1 /\ well_formed h c2 l2)) 
  (ensures( fun r -> True)) (decreases (%[G.reveal l1; G.reveal l2]))
let rec dataEqualSameLocation #a h c1 l1 c2 l2 =
    if not (B.g_is_null c1) then 
      let d1 = B.get h c1 0 in 
      dataEqualSameLocationT #a h c1 l1 c2 l2 /\ 
      dataEqualSameLocation #a h d1.next (G.hide (L.tl (G.reveal l1))) c2 l2
    else True

val well_formed_pointers_data: #a:Type -> h:HS.mem -> x:pointers_data a -> ys:list (pointers_data a)
    -> Ghost Type0 (requires((well_formed_pointers_data_base #a h x) /\ (well_formed_listpointers_data_base #a h ys)))
     (ensures( fun r -> True)) (decreases (ys))
let rec well_formed_pointers_data #a h x ys =  
  match ys with
  | [] -> True
  | hd::tl -> (dataEqualSameLocation #a h (B.get h x.pl 0) x.l (B.get h hd.pl 0) hd.l) 
  //  /\ MO.loc_disjoint (MO.loc_buffer x.pl) (MO.loc_buffer hd.pl)
    /\ well_formed_pointers_data #a h x tl

val well_formed_listpointers_data: #a:Type -> h:HS.mem -> l:list (pointers_data a) 
  -> Ghost Type0 (requires (well_formed_listpointers_data_base #a h l))(ensures (fun r -> True))
let rec well_formed_listpointers_data #a h l = 
      match l with
      | [] -> True
      | hd::tl -> (well_formed_pointers_data h hd tl) /\  (well_formed_listpointers_data #a h tl)

val well_formed_disjoint_meet_type_from_pointers_data: #a:Type -> h: HS.mem -> r:MO.loc -> x:pointers_data a
  -> Ghost Type0 (requires(well_formed_pointers_data_base #a h x))
  (ensures (fun r -> True))
let well_formed_disjoint_meet_type_from_pointers_data #a h r x 
  = (MO.loc_disjoint r (MO.loc_buffer x.pl) 
    /\ MO.loc_disjoint r (footprint h (B.get h x.pl 0) x.l))

val unused_in_well_formed_disjoint_from_pointers_data: #a:Type -> #b:Type -> h: HS.mem -> r:B.buffer a -> x:pointers_data b
 -> Lemma(requires (r `B.unused_in` h /\ well_formed_pointers_data_base #b h x))
  (ensures (well_formed_disjoint_meet_type_from_pointers_data #b h (MO.loc_buffer r) x))
let unused_in_well_formed_disjoint_from_pointers_data #a #b h r x
= unused_in_well_formed_disjoint_from_list #a #b h r (B.get h x.pl 0) (x.l)

val well_formed_disjoint_meet_type_from_listpointers_data:  #a:Type -> h: HS.mem -> r:MO.loc -> l: list(pointers_data a)
  -> Ghost Type0 (requires(well_formed_listpointers_data_base #a h l))
  (ensures (fun r -> True))
let rec well_formed_disjoint_meet_type_from_listpointers_data #a h r l
  = match l with
  | [] -> True
  | hd::tl -> 
    well_formed_disjoint_meet_type_from_pointers_data #a h r hd 
    /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r tl

val unused_in_well_formed_disjoint_from_listpointers_data: #a:Type -> #b:Type -> h: HS.mem -> r:B.buffer a -> l: list (pointers_data b)
 -> Lemma(requires (r `B.unused_in` h /\ well_formed_listpointers_data_base #b h l))
  (ensures (well_formed_disjoint_meet_type_from_listpointers_data #b h (MO.loc_buffer r) l))
let rec unused_in_well_formed_disjoint_from_listpointers_data #a #b h r l
  = match l with
  | [] -> ()
  | hd::tl -> 
    unused_in_well_formed_disjoint_from_pointers_data #a #b h r hd;
    unused_in_well_formed_disjoint_from_listpointers_data #a #b h r tl
 



val modifies_disjoint_well_formed_pointers_data_and_footprint_base: #a:Type -> h:HS.mem -> x:pointers_data a -> r:MO.loc -> h':HS.mem 
 -> Lemma (requires (well_formed_pointers_data_base h x 
  /\ well_formed_disjoint_meet_type_from_pointers_data #a h r x 
  /\ MO.modifies r h h' ))
  (ensures ( well_formed_pointers_data_base h' x) /\ ((footprint h' (B.get h' x.pl 0) (x.l)) == (footprint h (B.get h x.pl 0) (x.l))))
let modifies_disjoint_well_formed_pointers_data_and_footprint_base #a h x r h'
  = modifies_disjoint_footprint #a h (B.get h x.pl 0) x.l r h'


val listfootprint_meet_type:  #a:Type -> h:HS.mem -> l:list (pointers_data a) -> h':HS.mem 
-> Ghost Type0 (requires (
  well_formed_listpointers_data_base h l 
  /\ well_formed_listpointers_data_base h' l )) (ensures (fun r -> True)) (decreases l)
let rec listfootprint_meet_type #a h l h'
  = match l with
   | [] -> True
   | hd::tl -> ((footprint h' (B.get h' hd.pl 0) (hd.l)) == (footprint h (B.get h hd.pl 0) (hd.l))) /\ listfootprint_meet_type #a h tl h'

val modifies_disjoint_well_formed_listpointers_data_and_footprint_base: #a:Type -> h:HS.mem -> l:list (pointers_data a) -> r:MO.loc -> h':HS.mem 
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



val modifies_well_formed_disjoint_meet_type_from_pointers_data: #a:Type -> h: HS.mem -> r:MO.loc -> x:pointers_data a -> h':HS.mem
  -> Lemma(requires(well_formed_pointers_data_base #a h x 
        /\ well_formed_disjoint_meet_type_from_pointers_data #a h r x) 
        /\ (MO.modifies r h h'))
    (ensures (well_formed_pointers_data_base #a h' x /\ well_formed_disjoint_meet_type_from_pointers_data #a h' r x))
let modifies_well_formed_disjoint_meet_type_from_pointers_data #a h r x h' =
  modifies_disjoint_well_formed_pointers_data_and_footprint_base #a h x r h'


val modifies_well_formed_disjoint_meet_type_from_listpointers_data: #a:Type -> h: HS.mem -> r:MO.loc -> l:list (pointers_data a) -> h':HS.mem
  -> Lemma(requires(well_formed_listpointers_data_base #a h l 
        /\ well_formed_disjoint_meet_type_from_listpointers_data #a h r l) 
        /\ (MO.modifies r h h'))
    (ensures (well_formed_listpointers_data_base #a h' l /\ well_formed_disjoint_meet_type_from_listpointers_data #a h' r l))
let rec modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h r l h'
  = match l with
  | [] -> ()
  | hd::tl -> 
    modifies_well_formed_disjoint_meet_type_from_pointers_data #a h r hd h';
    modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h r tl h'


val modifies_disjoint_dataEqualSameLocationT: #a:Type -> h:HS.mem -> c1:(rnode a){not(B.g_is_null c1)} ->l1:(G.erased (list a)){not(L.isEmpty (G.reveal l1))} -> c2:(rnode a) -> l2:(G.erased (list a)) -> r:MO.loc -> h':HS.mem
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


val modifies_disjoint_dataEqualSameLocation: #a:Type -> h:HS.mem -> c1:(rnode a) ->l1:(G.erased (list a))-> c2:(rnode a) -> l2:(G.erased (list a)) -> r:MO.loc -> h':HS.mem
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


val modifies_disjoint_well_formed_pointers_data: #a:Type -> h:HS.mem -> x:pointers_data a -> ys:list (pointers_data a) -> r:MO.loc -> h':HS.mem
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
    modifies_disjoint_dataEqualSameLocation #a h (B.get h x.pl 0) x.l (B.get h hd.pl 0) hd.l r h';
    modifies_disjoint_well_formed_pointers_data #a h x tl r h'

val modifies_disjoint_well_formed_listpointers_data: #a:Type -> h:HS.mem -> l:list (pointers_data a) -> r:MO.loc -> h':HS.mem
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



val check_well_formed_listpointers_lemma: #a:Type -> h:HS.mem -> l:list (pointers_data a ) -> pre:(pointers_data a) -> data:(pointers_data a)
    -> Lemma (requires(
    well_formed_listpointers_data_base #a h l /\
    well_formed_listpointers_data #a h l /\ 
    well_formed_pointers_data_base #a h pre /\ 
    well_formed_pointers_data #a h pre l /\ 
    ((B.get h data.pl 0) == (B.get h pre.pl 0)) /\ 
    well_formed_pointers_data_base #a h data /\ 
    well_formed_disjoint_meet_type_from_pointers_data #a h (MO.loc_buffer data.pl) pre /\
    well_formed_disjoint_meet_type_from_listpointers_data #a h (MO.loc_buffer data.pl) l
    ))
     (ensures(well_formed_pointers_data #a h data l)) (decreases l)
let rec check_well_formed_listpointers_lemma #a h l pre data =  
  match l with
  | [] -> ()
  | hd::tl -> check_well_formed_listpointers_lemma #a h tl pre data


val insert_pre_pl: #a:Type -> l:list (pointers_data a ) -> pre:(pointers_data a){L.memP pre l} -> pc:B.pointer (rnode a) ->
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
    well_formed_disjoint_meet_type_from_pointers_data #a h1 (MO.loc_buffer v.pl) pre /\
    well_formed_disjoint_meet_type_from_listpointers_data #a h1 (MO.loc_buffer v.pl) l /\ 
    ( pc == (v.pl) ) /\ 
    well_formed_pointers_data #a h1 v l
  ))
let insert_pre_pl #a l pre pc = 
  let h0 = get () in
  pc *= (!* pre.pl);
  let h1 = get () in
  modifies_disjoint_well_formed_listpointers_data h0 l (MO.loc_buffer pc) h1; 
  modifies_disjoint_well_formed_pointers_data h0 pre l (MO.loc_buffer pc) h1;
  modifies_well_formed_disjoint_meet_type_from_listpointers_data h0 (MO.loc_buffer pc) l h1;
  modifies_well_formed_disjoint_meet_type_from_pointers_data h0 (MO.loc_buffer pc) pre h1;
  assert((B.get h1 pc 0) == (B.get h1 pre.pl 0));
  let data = {l = pre.l; pl = pc; } in
  check_well_formed_listpointers_lemma #a h1 l pre data;
  data

val push_pointers_data:#a:Type -> l:list (pointers_data a) -> x:pointers_data a -> v:a
  -> ST (pointers_data a ) (requires (fun h -> 
      well_formed_listpointers_data_base #a h l /\ 
      well_formed_listpointers_data #a h l /\ 
      well_formed_pointers_data_base #a h x /\ 
      well_formed_pointers_data #a h x l /\ 
      well_formed_disjoint_meet_type_from_listpointers_data #a h (MO.loc_buffer x.pl) l
      ))
    (ensures (fun h0 s h1 -> 
      MO.modifies (MO.loc_buffer x.pl) h0 h1 /\
      well_formed_listpointers_data_base #a h1 l /\ 
      well_formed_listpointers_data #a h1 l /\ 
      well_formed_pointers_data_base #a h1 s /\ 
      well_formed_disjoint_meet_type_from_listpointers_data #a h1 (MO.loc_buffer s.pl) l// /\ 
     // well_formed_pointers_data #a h1 s l
    ))


let push_pointers_data #a l x v = 
  let h0 = get () in
  let s = !* x.pl in
  let c = {
    data = v;
    next = s;
  }
  in
  let pc: B.pointer (node a) = B.malloc HS.root c 1ul in
  unused_in_well_formed_disjoint_from_list h0 pc s x.l;
  unused_in_well_formed_disjoint_from_pointers_data h0 pc x;
  unused_in_well_formed_disjoint_from_listpointers_data h0 pc l;
  let h1 = get () in
  modifies_disjoint_footprint h0 s x.l (MO.loc_buffer pc) h1;
  modifies_disjoint_well_formed_listpointers_data h0 l (MO.loc_buffer pc) h1;
  modifies_disjoint_well_formed_pointers_data h0 x l (MO.loc_buffer pc) h1;
  modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h0 (MO.loc_buffer x.pl) l h1;
  x.pl *= pc;
  //let s = { l = x.l; pl = x.pl;} in
  let h2 = get () in
  modifies_disjoint_footprint h1 s x.l (MO.loc_buffer x.pl) h2;
  modifies_disjoint_well_formed_listpointers_data h1 l (MO.loc_buffer x.pl) h2;
  modifies_disjoint_dataEqualSameLocation #a h1 
  modifies_well_formed_disjoint_meet_type_from_listpointers_data #a h1 (MO.loc_buffer x.pl) l h2;
  let r = {pl = x.pl; l = (G.hide (v::(G.reveal x.l)))} in
  r
  //assert(well_formed_pointers_data_base #a h2 s);


(*
val insert_hd_tl_Lemma: #a:Type -> h:HS.mem -> l:list (pointers_data a) -> x:(pointers_data a) -> 
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


val push_list_pointers: #a:Type -> l:list (pointers_data a) -> pre:(pointers_data a){L.memP pre l} -> v:a -> 
    ST (list (pointers_data a))
    (requires (fun h ->
      well_formed_listpointers_data_base #a h l /\ 
      well_formed_listpointers_data #a h l /\ 
      well_formed_pointers_data_base #a h pre /\
      well_formed_pointers_data #a h pre l
    ))
    (ensures (fun h0 nl h1 -> 
     Cons? nl 
     /\ 
      (
      let d = L.hd nl in 
     (L.length (L.tl nl) == L.length l) /\
        ((L.tl nl) == l )  /\ 
        MO.modifies (MO.loc_buffer d.pl) h0 h1 /\
        well_formed_listpointers_data_base #a h1 nl
       // ((B.get h1 (B.get h1 d.pl 0) 0) == v) /\ 
       // well_formed_listpointers_data #a h1 nl
      )
    (*
        Cons? nl /\ 
      (
      let d = L.hd nl in 
        (L.length (L.tl nl) == L.length l + 1) /\
        ((L.tl nl) == l ) /\ 
        MO.modifies (MO.loc_buffer d.pl) h0 h1 /\
        B.g_is_null d.pl /\
        ((B.get h1 d.pl 0) == v) /\ 
        well_formed_listpointers_data #a h1 nl
      )

      *)
    ))

let push_list_pointers #a l pre v = 
  let h0 = get () in
  let pc: B.pointer (rnode a) = B.malloc HS.root B.null 1ul in 
  unused_in_well_formed_disjoint_from_listpointers_data h0 pc l;
  unused_in_well_formed_disjoint_from_pointers_data h0 pc pre;
  let h1 = get () in
  modifies_disjoint_well_formed_listpointers_data h0 l (MO.loc_buffer pc) h1; 
  modifies_disjoint_well_formed_pointers_data h0 pre l (MO.loc_buffer pc) h1;
  modifies_well_formed_disjoint_meet_type_from_listpointers_data h0 (MO.loc_buffer pc) l h1;
  modifies_well_formed_disjoint_meet_type_from_pointers_data h0 (MO.loc_buffer pc) pre h1;
  let data = insert_pre_pl #a l pre pc in 
  push #a #data.l data.pl v;
  assert(well_formed_listpointers_data_base #a h1 l);
  assert(well_formed_listpointers_data #a h1 l);
  assert(well_formed_pointers_data_base #a h1 data);
  assert(well_formed_pointers_data #a h1 data l);
  insert_hd_tl_Lemma #a h1 l data;
  data::l

(*val relationNodeSupport: #a:Type -> h:HS.mem -> x:rnode a{not(B.g_is_null x)}  -> y:rnode a -> xs:G.erased a -> lx:G.erased (list a) -> ly:G.erased (list a) 
    -> GTot Type0 (decreases (G.reveal ly ))
let rec relationNodeSupport #a h x y xs lx ly =  
    let ll = (G.hide ((G.reveal xs)::(G.reveal lx))) in
    well_formed h x ll /\ well_formed h y ly /\
    (match G.reveal ly with
    | [] -> B.g_is_null y
    | hd::tl ->
        ((hd = xs) ==> ((footprint h x ll) = (footprint h y ly))) /\
        (relationNodeSupport h x (B.get h y 0).next xs lx (G.hide tl)))
(*)           
val relationnodels: #a:Type -> h:HS.mem -> x:rnode a -> y:rnode a -> l1:G.erased (list a)-> l2:G.erased (list a) -> GTot Type0
let rec relationnodels #a h x y l1 l2 =
    match G.reveal l1 with
    | [] -> G.g_is_null x
    | hd1::tl1 -> 
        match G.reveal l2 with
        | [] -> (G.g_is_null ys) /\ (relationnodels h x.next y (G.hide tl1) l2)
        | hd2::tl2 -> 
            (if hd1 = hd2 then (footprint h x l1 = footprint h y l2) else  (relationnodels h x y.next l1 (G.hide tl2)))

(*
val relationnodel: #a:Type -> h:HS.mem -> x:rnode a -> y:rnode a -> l1:G.erased (list a) -> l2:G.erased (list a) -> GTot Type0
let relationnodel #a h x y l1 l2 =
    r

val disjoint_loc_pointers_data: #a:Type -> #h:HS.mem -> x:pointers_data h -> y: pointers_data a h -> GTot Type0
let disjoint_loc_pointers_data #a h x l = 
    let xs = get x.pl h 0 in
        let ys = get y.pl h 0 in
            match x.l with
            | [] -> B.g_is_null xs
            | hd::tl -> 
                M0.loc_disjoint (MO.loc_buffer x.pl) (MO.loc_buffer y.pl) /\ 

                


type list_pointers (a:Type)
  {
    h:HS.mem;
    data:list (pointers_data a h){
      match data with
      | [] -> True
      | hd::tl -> ()
    }
  }