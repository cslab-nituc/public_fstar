module ET_MakeRootBase

open ET_Base
open ET_OtherBase
open Prims

open LengthMaxLemma

//ロボットの全移動方向
val direction_all: list direction
let direction_all = [(Direction (-1) 0);(Direction 0 (-1));(Direction 1 0);(Direction 0 1)]

type supportDirection = 
    | SDirection:
    x:direction_range->
    y:direction_range-> supportDirection

//方向(0,0)を除き、２つの方向の要素が異なるか判定する　同じfalse 異なるtrue
val compare_direction: t:supportDirection -> d:direction -> bool
let compare_direction t d =  
    if ((SDirection?.x t) = 0) && ((SDirection?.y t) = 0) then true else
        if ((SDirection?.x t) = (Direction?.x d)) || ((SDirection?.x t) = (Direction?.y d)) then false else true

//指定した方向成分以外の方向を全てリストにして返す
val getAllDirectionWithoutA: a:supportDirection->list direction
let getAllDirectionWithoutA a = 
    let l = direction_all in 
         memRemoveAllMeetFuncList (compare_direction a) l

//方向リストの中に指定している方向は含まれないかチェック
val checkRemoveDirectionList: kp:supportDirection -> l:list direction -> bool
let checkRemoveDirectionList kp l =
    memAllMeetFuncList (compare_direction kp) l

//すでに移動した方向を保持する変数(s:supportDirection)を更新させる    
val calcSupportDirection: s:supportDirection->d:direction->supportDirection
let calcSupportDirection s d = 
        let x = mod2Calc (SDirection?.x s) (-(Direction?.x d)) in
            let y = mod2Calc (SDirection?.y s) (-(Direction?.y d)) in
                SDirection x y

val check_movementxy: x:field_position -> y:field_position -> bool
let check_movementxy x y = 
    let xs = (XYPosition?.x y) - (XYPosition?.x x) in
        let ys = (XYPosition?.y y) - (XYPosition?.y x) in
            if ((xs+ys <= 1) && (xs+ys >= -1) && not(xs+ys=0)) then true else false

val check_movement: l:set_field -> bool
let rec check_movement l = 
    match l with
    | [] -> true
    | [s] -> true
    | hd1::hd2::tl -> (check_movementxy hd2 hd1)&&(check_movement (hd2::tl))

//経路情報の型 2
type root_nb (sl:set_field) (rl:set_field) = r:set_field{(notOverlaplists r sl)/\(notOverlaplists r rl)/\(check_movement r)}
////経路情報の型 1
type root_b (sl:set_field) (rl:set_field) = r:set_field{(notOverlaplistsoftl r sl)/\(notOverlaplists r rl)/\(check_movement r)}

type rr (sl:set_field) (rp:field_position) = l:list_notover field_position{(length l > 0)/\(thhd l = rp)/\(mem (Cons?.hd l)sl)/\(check_movement l)/\(notOverlaplists (Cons?.tl l) sl)}

type root_bs  (sl:set_field) (rl:set_field) = (v:(root_b sl rl){length v > 0})

//最後に返す型    
type root_s (sl:set_field) (rl:set_field) (rp:field_position) = v:root_bs sl rl{thhd v = rp}

val rpchecksum: #sl:set_field -> #rl:set_field -> rp:field_position -> root:root_nb sl rl -> bool
let rpchecksum rp root = 
    match root with
    | [] -> true
    | hd::tl -> check_movementxy rp hd

val allSetFirstSetting: #sl:set_field -> #rl:set_field -> rp:field_position -> l:list_notover (root_bs sl rl) -> bool
let rec allSetFirstSetting rp l = 
    match l with
    | [] -> true
    | hd::tl -> (thhd hd = rp)&&(allSetFirstSetting rp tl)

assume val notOverlapSupportLemma: #t:eqtype -> x:t -> l:list t -> Lemma(not(mem x l))

assume val check_movementLemma: #sl:set_field -> #rl:set_field -> rp:field_position -> root:root_nb sl rl -> Lemma(rpchecksum rp root)

(*
val notOverlaplistsoftl: l1:list field_position{notOverlap l1} -> l2:list field_position{notOverlap l2} -> bool
let notOverlaplistsoftl l1 l2 = match l1 with 
    | [] -> true
    | hd::tl -> (mem hd l1) && (notOverlaplists tl l2)
*)

//type list_notover (t:eqtype) = l:list t{notOverlap l}
//type set_field = list_notover field_position

//type root_nb (sl:set_field) = r:set_field{notOverlaplists r sl}
//type root_b (sl:set_field) = r:set_field{notOverlaplistsoftl r sl}

//ロボットの地点からそこから目標地点までとどりつく経路を全て取得する
val findRootToListAll: sl:set_field ->l:set_field->rl:set_field->root:(root_nb sl rl){(length root <= length l)/\(forall i. mem i root ==> mem i l)} -> rp:field_position{rpchecksum rp root}->Tot(list_notover (root_bs sl rl)) (decreases %[(16 - length(l));0;0]) 
val findRootToListAllSupport: sl:set_field->l:set_field->rl:set_field->root:(root_nb sl rl){(length root <= length l)/\(forall i. mem i root ==> mem i l)} -> rp:field_position->dl:list direction->Tot(list_notover (root_bs sl rl)) (decreases %[(16 - length(l));1;(length dl)])

let rec findRootToListAll sl l rl root rp = 
    if mem rp l then []
    else
        let nl = rp::l in
            if not(mem rp rl) then
                if mem rp sl then [rp::root] 
                else findRootToListAllSupport sl nl rl (rp::root) rp direction_all  
            else []

and findRootToListAllSupport sl l rl root rp dl = 
    match dl with
    | [] -> []
    | hd::tl -> 
        let x = (XYPosition?.x rp) + (Direction?.x hd) in
            let y = (XYPosition?.y rp) + (Direction?.y hd) in
                if (x >= 0) && (x <= 3) && (y >= 0) && (y <= 3) then 
                    let nrp = XYPosition x y in
                        check_movementLemma nrp root;
                        appendNotOverlap (findRootToListAll sl l rl root nrp) (findRootToListAllSupport sl l rl root rp tl)
                else findRootToListAllSupport sl l rl root rp tl


//最短距離導出

type root_xs (sl:set_field) (rl:set_field) (frp:field_position) (rp:field_position) = v:(root_s sl rl frp){Cons?.hd v = rp}

val getBestRootFromRp: (#sl:set_field) -> (#rl:set_field) -> (#frp:field_position) -> rp:robot_position -> l:list_notover (root_xs sl rl frp rp){length l > 0} -> root_xs sl rl frp rp
let rec getBestRootFromRp #sl #rl #frp rp l = 
    match l with
    | [x] -> x
    | hd::tl -> 
        let v = getBestRootFromRp #sl #rl #frp rp tl in
            if length hd < length v then hd else v

type getbestrootkeeps (sl:set_field) (rl:set_field) (frp:field_position) = 
    | GetBestRootKeeps:
    rp: field_position -> 
    root: list_notover (root_xs sl rl frp rp){length root > 0} -> 
    getbestrootkeeps sl rl frp

type getbestrootkeepslist (sl:set_field) (rl:set_field) (frp:field_position) =  l:list_notover (getbestrootkeeps sl rl frp){notOverlap (map GetBestRootKeeps?.rp l)}

val appendDivedeRoot: (#sl:set_field) -> (#rl:set_field) -> (#frp:field_position) -> l:getbestrootkeepslist sl rl frp -> rp:field_position-> v:(root_xs sl rl frp rp)-> r:(getbestrootkeepslist sl rl frp){forall i. mem i (map GetBestRootKeeps?.rp r) ==> mem i (map GetBestRootKeeps?.rp l)}
let rec appendDivedeRoot #sl #rl #frp l rp v = 
    match l with
    | [] -> []
    | hd::tl -> 
            if rp = (GetBestRootKeeps?.rp hd) 
            then (GetBestRootKeeps (GetBestRootKeeps?.rp hd) (appendNotOverlap [v] (GetBestRootKeeps?.root hd))) :: (appendDivedeRoot #sl #rl #frp tl rp v)
            else hd :: (appendDivedeRoot #sl #rl #frp tl rp v)

val divideRoot: (#sl:set_field) -> (#rl:set_field) -> (#frp:field_position) ->  l:list_notover (root_s sl rl frp) -> getbestrootkeepslist sl rl frp
let rec divideRoot #sl #rl #frp l = 
    match l with
    | [] -> []
    | hd::tl -> 
        let v = divideRoot #sl #rl #frp tl in
            if mem (Cons?.hd hd) (map GetBestRootKeeps?.rp v) 
            then appendDivedeRoot v (Cons?.hd hd) hd
            else (GetBestRootKeeps (Cons?.hd hd) [hd])::v

val appendDivedeRootBase: (#sl:set_field) -> (#rl:set_field) -> (#frp:field_position) -> l:getbestrootkeepslist sl rl frp -> v:list_notover (root_s sl rl frp){(notOverlap (map Cons?.hd v))/\(forall i. mem i (map Cons?.hd v) ==> mem i (map GetBestRootKeeps?.rp l))}
let rec appendDivedeRootBase #sl #rl #frp l = 
    match l with
    | [] -> []
    | hd::tl -> (getBestRootFromRp (GetBestRootKeeps?.rp hd) (GetBestRootKeeps?.root hd))::(appendDivedeRootBase #sl #rl #frp tl)

val getBestRootFromRoots: (#sl:set_field) -> (#rl:set_field) -> (#frp:field_position) ->  l:list_notover (root_s sl rl frp) -> v:list_notover (root_s sl rl frp){notOverlap (map Cons?.hd v)}
let getBestRootFromRoots #sl #rl #frp l = 
    let v = divideRoot #sl #rl #frp l in
        appendDivedeRootBase #sl #rl #frp v

(*
//到達可能なブロックまでの経路が最短経路ならば登録する
val getBestRootBlocksBase: (#sl:set_field) -> (#rl:set_field) -> (#rp:robot_position) -> root_s sl rl rp -> list_notover (root_s sl rl rp) -> list_notover (root_s sl rl rp)
let rec getBestRootBlocksBase r pl = 
    match pl with 
        | [] -> []
        | hd::tl -> 
            if ((Cons?.hd hd) = (Cons?.hd r)) then
                if length r < length hd 
                    then 
                        let _ = notOverlapSupportLemma r (getBestRootBlocksBase r tl) in
                        r::(getBestRootBlocksBase r tl) 
                else
                    let _ = notOverlapSupportLemma hd (getBestRootBlocksBase r tl) in  
                    hd::(getBestRootBlocksBase r tl)
            else
                let _ = notOverlapSupportLemma hd (getBestRootBlocksBase r tl) in 
                hd::(getBestRootBlocksBase r tl)

//最短経路のみを取得 2
val getBestBlocksRootSupport: (#sl:set_field) -> (#rl:set_field) -> (#rp:robot_position) -> pl:list_notover (root_s sl rl rp)  -> gl:list_notover (root_s sl rl rp) -> list_notover (root_s sl rl rp)
let rec getBestBlocksRootSupport pl gl = 
    match pl with 
    | [] -> []
    | hd::tl -> 
        let v = getBestBlocksRootSupport tl gl in getBestRootBlocksBase hd v

//最短経路のみを取得 1
val getBestBlocksRoot: (#sl:set_field) -> (#rl:set_field) -> (#rp:robot_position) -> pl:list_notover (root_s sl rl rp) -> list_notover (root_s sl rl rp) 
let getBestBlocksRoot pl = getBestBlocksRootSupport pl []
*)
assume val findRootToListAllLemma1:sl:set_field -> rl:set_field -> rp:field_position->Lemma(allSetFirstSetting rp (findRootToListAll sl [] rl [] rp)) [SMTPat(findRootToListAll sl [] rl [] rp)]

val asSetR1: #sl:set_field -> #rl:set_field -> rp:field_position -> l:list_notover (root_bs sl rl){allSetFirstSetting rp l} -> v:list_notover (root_s sl rl rp){forall i. mem i v ==> mem i l}
let rec asSetR1 rp l = 
    match l with
    | [] -> []
    | hd::tl -> hd::(asSetR1 rp tl)
    
val findRootToList: sl:set_field -> rl:set_field -> rp:field_position->Tot(list_notover (root_s sl rl rp))
let findRootToList sl rl rp = getBestRootFromRoots (asSetR1 rp (findRootToListAll sl [] rl [] rp))

//val test: (#sl:set_field) -> (#rl:set_field) -> (#rp:field_position) -> list_notover (root_s sl rl rp)

//let findRootToListLemma1 sl rl rp = ()


//最後に返す型    
type root (sl:set_field) (rl:set_field) (rp:field_position) 
    = l:list (r:set_field{(notOverlaplistsoftl r sl)/\(notOverlaplists r rl)/\(check_movement r)/\(length r > 0)}){notOverlap l}