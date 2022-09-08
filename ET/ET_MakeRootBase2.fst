module ET_MakeRootBase2

open ET_Base
open ET_OtherBase
open Prims

open LengthMaxLemma
open ET_MakeRootBase

(*
//ロボットの全移動方向
val direction_all: l:list direction{notOverlap l}
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
*)

//getfield 
//sl:(root_nb sl rl) ==> (ルート)
//rl:set_field ==> (到着位置) 
type getfield (sl:set_field) (rl:set_field) = 
    | GetField:
    r:root_nb sl rl -> 
    p:field_position{(not(mem p rl))/\(rpchecksum p r)} -> 
    getfield sl rl

//関数用のex_root ==> root_nb sl rl (ルート)　{　l:チェック済みのリスト　とルートの関係を定義}
type ex_root (sl:set_field) (rl:set_field) (l:set_field) =  root:(root_nb sl rl){(length root > 0)/\(length root <= length l)/\(forall i. mem i root ==> mem i l)}

//getfield sl r  { l:チェック済みのリスト }　ルートとチェック済みの関係
type getfield_notl (sl:set_field) (rl:set_field) (l:set_field) = v:(getfield sl rl){(not(mem (GetField?.p v) l))/\(length (GetField?.r v) <= length l)/\(forall i. mem i (GetField?.r v) ==> mem i l)}
type getfield_notl_s (sl:set_field) (rl:set_field) (l:set_field) = l:list_notover (getfield_notl sl rl l){notOverlap (map GetField?.p l)}

//getfield sl r  { l:チェック済みのリスト }　ルートとチェック済みの関係　＊到着位置がslの中に含まれる
type getfield_insl_notl (sl:set_field) (rl:set_field) (l:set_field) = v:(getfield_notl sl rl l){mem (GetField?.p v) sl}
type getfield_insl_notl_s (sl:set_field) (rl:set_field) (l:set_field) = l:list_notover (getfield_insl_notl sl rl l){notOverlap (map GetField?.p l)}

//getfield sl r  { l:チェック済みのリスト }　ルートとチェック済みの関係　＊到着位置がslの中に含まない
type getfield_ninsl_notl (sl:set_field) (rl:set_field) (l:set_field) = v:(getfield_notl sl rl l){not(mem (GetField?.p v) sl)}
type getfield_ninsl_notl_s (sl:set_field) (rl:set_field) (l:set_field) = l:list_notover (getfield_ninsl_notl sl rl l){notOverlap (map GetField?.p l)}

//現在のルートから次のルートを見つける  (2)
val getColseMatrixOverlapSupport: sl:set_field -> l:set_field -> rl:set_field -> ex_root sl rl l -> dl:list direction{notOverlap dl}-> getfield_notl_s sl rl l
let rec getColseMatrixOverlapSupport sl l rl root dl = 
    match dl with
    | [] -> []
    | hd::tl -> let x = (XYPosition?.x (Cons?.hd root)) + (Direction?.x hd) in
                    let y = (XYPosition?.y (Cons?.hd root)) + (Direction?.y hd) in
                        if (x >= 0) && (x <= 3) && (y >= 0) && (y <= 3) then
                            let v:field_position = XYPosition x y in 
                                if ((not(mem v l))&&(not(mem v rl))) then 
                                let _ = notOverlapSupportLemma v (map GetField?.p (getColseMatrixOverlapSupport sl l rl root tl)) in
                                (GetField root v)::(getColseMatrixOverlapSupport sl l rl root tl) 
                                else (getColseMatrixOverlapSupport sl l rl root tl) 
                        else (getColseMatrixOverlapSupport sl l rl root tl) 

//現在のルートから次のルートを見つける  (1)
val getColseMatrixOverlap: sl:set_field -> l:set_field -> rl:set_field -> ex_root sl rl l -> getfield_notl_s sl rl l
let getColseMatrixOverlap sl l rl root = getColseMatrixOverlapSupport sl l rl root direction_all

//(lが満たされた場合　==> (getColseMatrixOverlap sl l rl v)はNil)
val getColseMatrixOverlapLemma1: sl:set_field -> l:set_field -> rl:set_field -> v:ex_root sl rl l -> Lemma(requires(length l = 16))(ensures(Nil? (getColseMatrixOverlap sl l rl v)))
let getColseMatrixOverlapLemma1 sl l rl v = ()

//getfield_notl_s sl rl l (slがメンバーかどうかで分ける関数) ==>  最終地点に被りがないようにする分ける
val appendNotOverlapMatrix: #sl:set_field -> #l:set_field -> #rl:set_field -> getfield_notl_s sl rl l -> getfield_notl_s sl rl l -> getfield_notl_s sl rl l
let rec appendNotOverlapMatrix #sl #l #rl l1 l2 = 
    match l1 with
    | [] -> l2
    | hd::tl -> 
        let v = appendNotOverlapMatrix #sl #l #rl tl l2 in
            if not(mem (GetField?.p hd) (map GetField?.p v)) 
            then hd::v 
            else v

//既存のリストのルートの状態から次の新しい到達可能なルートを探す
val getCloseMatrix: sl:set_field -> l:set_field -> rl:set_field -> nl:list (ex_root sl rl l) -> getfield_notl_s sl rl l
let rec getCloseMatrix sl l rl nl = 
    match nl with
    | [] -> []
    | hd::tl -> 
        let v = getColseMatrixOverlap sl l rl hd in
            appendNotOverlapMatrix v (getCloseMatrix sl l rl tl)

val getColseMatrixLemma1: sl:set_field -> l:set_field -> rl:set_field -> nl:list (ex_root sl rl l) -> Lemma((length l = 16) ==> (Nil? (getCloseMatrix sl l rl nl)))
let getColseMatrixLemma1 sl l rl v = ()

//(pl ==> slが含むpl型 に分ける時の型)　(pl ==> slが含まないpl型 に分ける時の型)
type getfield_insl_notl_ssupport (sl:set_field) (l:set_field) (rl:set_field) (pl:getfield_notl_s sl rl l) = v:(getfield_insl_notl_s sl rl l){(forall i. mem i v ==> mem i pl)/\(forall i. mem i (map GetField?.p v) ==> mem i (map GetField?.p pl))}
type getfield_ninsl_notl_ssupport (sl:set_field) (l:set_field) (rl:set_field) (pl:getfield_notl_s sl rl l) = v:(getfield_ninsl_notl_s sl rl l){(forall i. mem i v ==> mem i pl)/\(forall i. mem i (map GetField?.p v) ==> mem i (map GetField?.p pl))}

//getfield_notl_tupple ==> slが含むか含まないかで分ける タプル
type getfield_notl_tupple (sl:set_field) (l:set_field) (rl:set_field) (pl:getfield_notl_s sl rl l) = 
    | Getfield_Notl_Tupple:
    insl:getfield_insl_notl_ssupport sl l rl pl -> 
    ninsl:getfield_ninsl_notl_ssupport sl l rl pl -> 
    getfield_notl_tupple sl l rl pl

//getfield_notl_tupple ==> slが含むか含まないかで分ける関数 (2)
assume val memlem: #t:eqtype -> x:t -> l:list t -> Lemma(mem x l)
assume val notmemlem: #t:eqtype -> x:t -> l:list t -> Lemma(not(mem x l))

val getRootsBaseSupport: #sl:set_field -> #l:set_field -> #rl:set_field -> #pl:getfield_notl_s sl rl l -> pls:getfield_notl_s sl rl l{forall i. mem i pls ==> mem i pl} 
    -> v:getfield_notl_tupple sl l rl pl
    //{(forall i. mem i (map GetField?.p (Getfield_Notl_Tupple?.insl v)) ==> mem i (map GetField?.p pl))/\(forall i. mem i (map GetField?.p (Getfield_Notl_Tupple?.ninsl v)) ==> mem i (map GetField?.p pl))}
let rec getRootsBaseSupport #sl #l #rl #pl pls = 
    match pls with
    | [] -> (Getfield_Notl_Tupple [] [])
    | hd::tl -> 
        let v = getRootsBaseSupport #sl #l #rl #pl tl in
            if mem (GetField?.p hd) sl then 
                let _ = notmemlem hd (Getfield_Notl_Tupple?.insl v) in
                let _ = notmemlem (GetField?.p hd) (map GetField?.p (Getfield_Notl_Tupple?.insl v)) in
                Getfield_Notl_Tupple (hd::(Getfield_Notl_Tupple?.insl v)) (Getfield_Notl_Tupple?.ninsl v)//(hd::v._1,v._2)
            else let _ = notmemlem hd (Getfield_Notl_Tupple?.ninsl v) in
                let _ = notmemlem (GetField?.p hd) (map GetField?.p (Getfield_Notl_Tupple?.ninsl v)) in
                Getfield_Notl_Tupple (Getfield_Notl_Tupple?.insl v) (hd::(Getfield_Notl_Tupple?.ninsl v))

//getfield_notl_tupple ==> slが含むか含まないかで分ける関数 (1)
val getRootsBase: #sl:set_field -> #l:set_field -> #rl:set_field -> pl:getfield_notl_s sl rl l -> getfield_notl_tupple sl l rl pl
let getRootsBase #sl #l #rl pl = getRootsBaseSupport #sl #l #rl #pl pl

//val asSetGetFieldlem: #sl:set_field -> #l:set_field -> #rl:set_field-> pl:getfield_insl_notl_s sl rl l -> v:getfield_notl_s sl rl l{(forall i. mem i v ==> mem i pl)/\(forall i. mem i (map GetField?.p v) ==> mem i (map GetField?.p pl))}
//let rec asSetGetFieldlem m = match m with | [] -> [] | hd::tl -> hd::(asSetGetFieldlem tl)

//(map GetField?.p pl) と lに重なりがない証明
val getfieldMapOverlapLemma1: #sl:set_field -> l:set_field -> #rl:set_field -> pl:getfield_notl_s sl rl l -> Lemma(notOverlaplists (map GetField?.p pl) l)
let rec getfieldMapOverlapLemma1 #sl l #rl pl = 
    match pl with
    | [] -> ()
    | hd::tl -> getfieldMapOverlapLemma1 #sl l #rl tl

// lよりも　(map GetField?.p pl) と　l　のリストが大きい証明
val getfieldMapOverlapLemma2: #sl:set_field -> l:set_field -> #rl:set_field  -> pl:getfield_notl_s sl rl l{length pl > 0} -> Lemma(length l < length (appendNotOverlap (map GetField?.p pl) l)) 
let getfieldMapOverlapLemma2 #sl l #rl pl = getfieldMapOverlapLemma1 #sl l #rl pl

//次のgetfield型(slを含まない)から __ list (ex_root sl rl (appendNotOverlap (map GetField?.p pl) l)) __型に直す
val getNextRoot: #sl:set_field -> #l:set_field -> #rl:set_field -> #pl:getfield_notl_s sl rl l -> pls:getfield_ninsl_notl_s sl rl l{forall i. mem i pls ==> mem i pl} -> list (ex_root sl rl (appendNotOverlap (map GetField?.p pl) l))
let rec getNextRoot #sl #l #rl #pl pls = match pls with
    | [] -> []
    | hd::tl -> 
        let _ = assert(length (map GetField?.p pl) >= 1) in
            getfieldMapOverlapLemma2 #sl l #rl pl;
            let s = ((GetField?.p hd)::(GetField?.r hd)) in
            s::(getNextRoot #sl #l #rl #pl tl)

//次のgetfield型(slを含まない)から __ v:list_notover (root_bs sl rl) __型に直す
val getRootsbList: #sl:set_field -> #l:set_field -> #rl:set_field -> pl:getfield_insl_notl_s sl rl l -> v:list_notover (root_bs sl rl){(notOverlap (map Cons?.hd v))/\(forall i. mem i v ==> mem (Cons?.hd i) (map GetField?.p pl))/\(forall i. mem i (map Cons?.hd v) ==> mem i (map GetField?.p pl))}
let rec getRootsbList #sl #l #rl pl = 
    match pl with
    | [] -> [] 
    | hd::tl ->
        let v = getRootsbList #sl #l #rl tl in
            let s = ((GetField?.p hd)::(GetField?.r hd)) in
                    s::v

//同じ地点を外して加える
val appendNotOverlapPl: #sl:set_field -> #l:set_field -> #rl:set_field -> l1:list_notover (root_bs sl rl){(notOverlap (map Cons?.hd l1))} -> l2:list_notover (root_bs sl rl){(notOverlap (map Cons?.hd l2))} -> l3:list_notover (root_bs sl rl){(notOverlap (map Cons?.hd l3))}
let rec appendNotOverlapPl #sl #l #rl l1 l2 = 
    match l1 with
    | [] -> l2
    | hd::tl -> 
        let v = (appendNotOverlapPl #sl #l #rl tl l2) in
        if (not(mem (Cons?.hd hd) (map Cons?.hd v))) then
            hd::v
        else v

#set-options "--z3rlimit 100"
//ルートを求める
val getRoots: sl:set_field -> l:set_field -> rl:set_field -> pl:getfield_notl_s sl rl l -> Tot(s:list_notover (root_bs sl rl){(notOverlap (map Cons?.hd s))}) (decreases %[16 - length l])
let rec getRoots sl l rl pl = 
    match pl with
    | [] -> []
    | hd::tl -> 
        let v = getRootsBase #sl #l #rl pl in //slの位置にいるものを見つける
            getfieldMapOverlapLemma2 #sl l #rl pl; 
            let nl = appendNotOverlap (map GetField?.p pl) l in //チェックしたマスを追加
                let ng = getNextRoot #sl #l #rl #pl (Getfield_Notl_Tupple?.ninsl v) in 
                    getColseMatrixLemma1 sl nl rl ng;
                    let b = getCloseMatrix sl nl rl ng in 
                        let s = getRoots sl nl rl b in 
                             appendNotOverlapPl #sl #nl #rl (getRootsbList (Getfield_Notl_Tupple?.insl v)) s
#reset-options

val getfr: #sl:set_field -> #rl:set_field -> rp:field_position{not(mem rp rl)} -> getfield_notl_s sl rl []
let getfr rp = [(GetField [] rp)]

assume val getRootsLemma1: sl:set_field -> rl:set_field -> rp:field_position{not(mem rp rl)}->Lemma(allSetFirstSetting rp (getRoots sl [] rl (getfr rp))) [SMTPat(getRoots sl [] rl (getfr rp))]

val asSetR2: #sl:set_field -> #rl:set_field -> rp:field_position -> l:list_notover (root_bs sl rl){(allSetFirstSetting rp l)/\(notOverlap (map Cons?.hd l))} -> v:list_notover (root_s sl rl rp){(notOverlap (map Cons?.hd v))/\(forall i. mem i v ==> mem i l)/\(forall i. mem i (map Cons?.hd v) ==> mem i (map Cons?.hd l))}
let rec asSetR2 rp l = 
    match l with
    | [] -> []
    | hd::tl ->hd::(asSetR2 rp tl)

val findRootToList2: sl:set_field -> rl:set_field -> rp:field_position{not(mem rp rl)}->Tot(s:list_notover (root_s sl rl rp){notOverlap (map Cons?.hd s)})
let findRootToList2 sl rl rp = asSetR2 rp (getRoots sl [] rl (getfr rp))