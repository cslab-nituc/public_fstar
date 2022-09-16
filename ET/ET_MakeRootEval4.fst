module ET_MakeRootEval4

open ET_Base
open ET_OtherBase
open Prims

open ET_MakeRootBase
open ET_MakeRootByBlock
open ET_MakeRootByCercle 
open FStar.Mul

module L = FStar.List.Tot

type blocks_type = bl:blocks{notOverlap bl}
type cercles_type = cl:cercles{notOverlap cl}

type bbl_type = bbl:blocks_type{(length bbl = 8)}
type bcl_type = bcl:cercles_type{(length bcl = 8)}
type sbl_type (bbl:blocks_type) = bl:blocks_type{(forall i. mem i bl ==> mem i bbl)} 
type scl_type (bcl:cercles_type) = cl:cercles_type{(forall i. mem i cl ==> mem i bcl)} 

type oneroot_type (bl:blocks_type) (cl:cercles_type) = 
    | OneRootType:
    block:block_sb bl -> 
    cercle:cercle_sc block cl-> 
    frp:robot_position ->
    rootblock:(block_root block frp bl) ->
    rootcercle:(cercle_root block cl cercle (removeBlocks bl block)) ->
    hrp:robot_position{Cons?.hd rootblock = hrp} ->
    lrp:robot_position{Cons?.hd rootcercle = lrp} ->
    distance:nat{distance = length rootblock + length rootcercle - 1} ->
    oneroot_type bl cl

type rootcontent_type (bbl:bbl_type) (bcl:bcl_type) = 
    | RootContent:
    #bl:sbl_type bbl -> 
    #cl:scl_type bcl ->
    content:(oneroot_type bl cl){(mem content.block bbl) /\ (mem content.cercle bcl)} ->
    level:nat -> 
    evaluation:nat ->
    rootcontent_type bbl bcl

val allroot_meet_func: #bbl:bbl_type -> #bcl:bcl_type 
    -> l:list (rootcontent_type bbl bcl){Cons? l} -> Tot Type0 (decreases (l))
let rec allroot_meet_func #bbl #bcl l = 
    match l with
    | [hd] -> ((hd.bl = bbl) && (hd.cl = bcl) && (hd.content.frp = first_robot_position))
    | hd1::hd2::tl 
        -> ((hd1.content.frp = hd2.content.lrp)
        && (mem hd1.content.block hd2.bl) && (mem hd1.content.cercle hd2.cl)) /\ 
        (hd1.bl == (removeBlocks hd2.bl hd2.content.block)) /\ (hd1.cl == (removeCercles hd2.cl hd2.content.cercle))
        /\ (allroot_meet_func (hd2::tl))

type allroot_type (bbl:bbl_type) (bcl:bcl_type)
    = l:(list (rootcontent_type bbl bcl)){match l with | [] -> True | _::_ ->  allroot_meet_func l}

type sbl_type_kps (#bbl:bbl_type) (#bcl:bcl_type) (l:allroot_type bbl bcl)
    = v:sbl_type bbl{
        (match l with
        | [] -> (v == bbl)
        | hd::_ -> (v == (removeBlocks hd.bl (hd.content.block) )))}

type scl_type_kps (#bbl:bbl_type) (#bcl:bcl_type) (l:allroot_type bbl bcl)
    = v:scl_type bcl{
        (match l with
        | [] -> (v == bcl)
        | hd::_ -> (v == (removeCercles hd.cl (hd.content.cercle) )))}

val getBlocksForNextAllRoot: bbl:bbl_type -> #bcl:bcl_type
    -> l:allroot_type bbl bcl
    -> Tot (sbl_type_kps l)  (decreases (length l))
let rec getBlocksForNextAllRoot bbl #bcl l = 
    match l with
    | [] -> bbl
    | hd::tl -> 
        let v = getBlocksForNextAllRoot bbl tl in 
            removeBlocks v (hd.content.block)

val getCerclesForNextAllRoot: #bbl:bbl_type -> bcl:bcl_type
    -> l:allroot_type bbl bcl
    -> Tot (scl_type_kps l)  (decreases (length l))
let rec getCerclesForNextAllRoot #bbl bcl l = 
    match l with
    | [] -> bcl
    | hd::tl -> 
        let v = getCerclesForNextAllRoot bcl tl in 
            removeCercles v (hd.content.cercle)

val satisfied_al_MakeAllRoot: #bbl:bbl_type -> #bcl:bcl_type
    -> #bl:sbl_type bbl
    -> #cl:scl_type bcl
    -> n:(allroot_type bbl bcl) -> al:oneroot_type bl cl -> Tot Type0
let satisfied_al_MakeAllRoot #bbl #bcl #bl #cl n a
    = match n with
        | [] -> ((bl = bbl) && (cl = bcl) && (a.frp = first_robot_position))
        | hd::tl -> ((hd.content.lrp = a.frp) && (mem a.block hd.bl) && (mem a.cercle hd.cl)) /\ 
        (bl == (removeBlocks hd.bl hd.content.block)) /\ (cl == (removeCercles hd.cl hd.content.cercle))

val satisfied_al_MakeAllRootList: #bbl:bbl_type -> #bcl:bcl_type
    -> #bl:sbl_type bbl
    -> #cl:scl_type bcl
    -> n:(allroot_type bbl bcl) -> al:list (oneroot_type bl cl) -> Tot Type0
let rec satisfied_al_MakeAllRootList #bbl #bcl #bl #cl n al 
    = match al with
    | [] -> True
    | hd::tl -> (satisfied_al_MakeAllRoot n hd) /\ (satisfied_al_MakeAllRootList n tl)

val last_setting_robot_position: #bbl:bbl_type -> #bcl:bcl_type -> l:allroot_type bbl bcl -> rp:robot_position -> Tot bool
let last_setting_robot_position #bbl #bcl l rp 
    = match l with
    | [] -> (rp = first_robot_position)
    | hd::_ -> (hd.content.lrp = rp)

    //{match n with | Some k -> True | None -> (forall i. mem i bl = mem i bbl)/\(forall i. mem i cl = mem i bcl)/\(Nil? pbl)/\(Nil? pcl)} -> 
//満たすべき性質用の満たすべき性質用のデータ型を作成
val makeOneRootTypeData: #bl:blocks_type -> #cl:cercles_type -> rp:robot_position -> bt:(block_get rp bl) -> ct:(cercle_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> (s:(oneroot_type bl cl){(s.frp = rp)&&(mem s.block bl)&&(mem s.cercle cl)})
let makeOneRootTypeData rp bt ct = OneRootType (Block_get?.b bt) (Cercle_get?.c ct) rp (Block_get?.r bt) (Cercle_get?.r ct) (Cons?.hd (Block_get?.r bt)) (Cons?.hd (Cercle_get?.r ct)) (length ((Block_get?.r bt)) + length ((Cercle_get?.r ct)) - 1)

//ブロックのルート型とサークルのルート型の２つから全てのパターンのデータを作成
val makeOneActionFromBlockToCercle: #bl:blocks_type -> #cl:cercles_type -> rp:robot_position ->  bt:(block_get rp bl) -> ctl:(cercles_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) 
-> l:(list (oneroot_type bl cl)){forall i. mem i l ==> ((i.frp = rp)&&(mem i.block bl)&&(mem i.cercle cl))}
let rec makeOneActionFromBlockToCercle rp bt ctl = 
    match ctl with
    | [] -> []
    | hd::tl -> (makeOneRootTypeData rp bt hd)::(makeOneActionFromBlockToCercle rp bt tl)

//ブロックからサークルに設置できるパターンのデータを全て作成 2
val getOneActionFromBlockToCercleSupport: #cl:cercles_type -> bl:blocks_type -> rp:robot_position ->  bt:(block_get rp bl) ->  cls:(scl_type cl){(sameColor (getListCercleColor cls) (Block?.col (Block_get?.b bt)))} 
-> l:(list (oneroot_type bl cl)){forall i. mem i l ==> ((i.frp = rp)&&(mem i.block bl)&&(mem i.cercle cl))}
let rec getOneActionFromBlockToCercleSupport #cl bl rp bt cls = 
    match cls with
    | [] -> []
    | hd::tl -> 
        let v = getBestRootByCercles2 #cl bl (Block_get?.b bt) hd (Block?.pos (Block_get?.b bt)) in
              //  let v = getBestRootByCercles1 #cl bl (Block_get?.b bt) hd (Block?.pos (Block_get?.b bt)) in
            append (makeOneActionFromBlockToCercle rp bt v) (getOneActionFromBlockToCercleSupport #cl bl rp bt tl)

val getOneActionFromBlockToCercleSupportLemma1: #cl:cercles_type -> rp:robot_position -> bt:(block_get rp []) ->Lemma(Nil? (getOneActionFromBlockToCercleSupport #cl [] rp bt [])) [SMTPat(getOneActionFromBlockToCercleSupport #cl [] rp bt [])]
let getOneActionFromBlockToCercleSupportLemma1 #cl rp bt = ()


val getBlockColorToCercleSupport: cl:cercles_type -> cls:scl_type cl -> b:block -> v:scl_type cl
let rec getBlockColorToCercleSupport cl cls b = 
    match cls with
    | [] -> cl
    | hd::tl ->
         let v = getBlockColorToCercleSupport cl tl b in
    if not(Cercle?.col hd = Block?.col b) then 
    memRemove hd v else v

assume val getBlockColorToCercleLemma: cl:cercles_type -> b:block -> l:cercles_type{(forall i. mem i l ==> mem i cl)} -> Lemma(sameColor (getListCercleColor l) (Block?.col b))// [SMTPat(getBlockColorToCercleSupport cl cl b)]

val getBlockColorToCercle: cl:cercles_type -> b:block -> v:(scl_type cl){(sameColor (getListCercleColor v) (Block?.col b))}
let getBlockColorToCercle cl b = let v = getBlockColorToCercleSupport cl cl b in let _ = getBlockColorToCercleLemma cl b v in v

 //ブロックからサークルに設置できるパターンのデータを全て作成 2           
val getOneActionFromBlockToCercle: bl:blocks_type -> cl:cercles_type -> rp:robot_position -> bt:(block_get rp bl) 
    -> l:(list (oneroot_type bl cl)){forall i. mem i l ==> ((i.frp = rp)&&(mem i.block bl)&&(mem i.cercle cl))}
let getOneActionFromBlockToCercle bl cl rp bt = 
        let cls = getBlockColorToCercle cl (Block_get?.b bt) in 
            getOneActionFromBlockToCercleSupport #cl bl rp bt cls

//１つのアクションのデータを全て取得する　2
val getOneActionSupport: bl:blocks_type -> cl:cercles_type -> rp:robot_position -> btl:(blocks_get rp bl) 
    -> l:(list (oneroot_type bl cl)){forall i. mem i l ==> ((i.frp = rp)&&(mem i.block bl)&&(mem i.cercle cl))}
let rec getOneActionSupport bl cl rp btl = 
    match btl with
    | [] -> []
    | hd::tl -> append (getOneActionFromBlockToCercle bl cl rp hd) (getOneActionSupport bl cl rp tl)


val chenge_satisfied_al_MakeAllRoot_lemma:  #bbl:bbl_type -> #bcl:bcl_type -> #l:allroot_type bbl bcl -> #bl:(sbl_type_kps l){(length bl > 0)} -> #cl:(scl_type_kps l) 
    -> #rp:robot_position{last_setting_robot_position l rp}
    -> s:(oneroot_type bl cl)
    -> Lemma(requires((s.frp = rp)&&(mem s.block bl)&&(mem s.cercle cl))) (ensures(satisfied_al_MakeAllRoot l s))
let chenge_satisfied_al_MakeAllRoot_lemma #bbl #bcl #l #bl #cl #rp s = ()

val chenge_satisfied_al_MakeAllRootList_lemma: #bbl:bbl_type -> #bcl:bcl_type -> #l:allroot_type bbl bcl -> #bl:(sbl_type_kps l){(length bl > 0)} -> #cl:(scl_type_kps l) 
    -> #rp:robot_position{last_setting_robot_position l rp}
    -> a:list (oneroot_type bl cl)
    -> Lemma(requires(forall i. mem i a ==> (i.frp = rp)&&(mem i.block bl)&&(mem i.cercle cl)))
    (ensures(satisfied_al_MakeAllRootList l a))
let rec chenge_satisfied_al_MakeAllRootList_lemma #bbl #bcl #l #bl #cl #rp a = 
    match a with
    | [] -> ()
    | hd::tl -> 
        chenge_satisfied_al_MakeAllRoot_lemma #bbl #bcl #l #bl #cl #rp hd; 
        chenge_satisfied_al_MakeAllRootList_lemma #bbl #bcl #l #bl #cl #rp tl

//(hd.content.lrp = a.frp) && (mem a.block hd.bl) && (mem a.cercle hd.cl)
//ブロックメンバー削除する
//１つのアクションのデータを全て取得する　1
val getOneAction:  #bbl:bbl_type -> #bcl:bcl_type -> #l:allroot_type bbl bcl -> bl:(sbl_type_kps l){(length bl > 0)} -> cl:(scl_type_kps l) 
    -> rp:robot_position{last_setting_robot_position l rp}
    -> (a:(list (oneroot_type bl cl)){satisfied_al_MakeAllRootList l a})
let getOneAction #bbl #bcl #l bl cl rp = 
    let v = getBestRootByBlocks2 bl rp in
   // let v = getBestRootByBlocks1 bl rp in
        let r = getOneActionSupport bl cl rp v in
            chenge_satisfied_al_MakeAllRootList_lemma #bbl #bcl #l #bl #cl #rp r;
            r

val makeAllRoot: #bbl:bbl_type -> #bcl:bcl_type
    -> #bl:sbl_type bbl
    -> #cl:scl_type bcl
    -> n:(allroot_type bbl bcl)
    -> a:(oneroot_type bl cl){ satisfied_al_MakeAllRoot n a} -> (allroot_type bbl bcl)
let makeAllRoot #bbl #bcl #bl #cl n a = 
    match n with
    | [] -> [(RootContent a 1 a.distance)]
    | hd::tl -> 
    (RootContent a (hd.level + 1) (hd.evaluation + a.distance))::n

val makeAllRootList: #bbl:bbl_type -> #bcl:bcl_type
    -> #bl:sbl_type bbl
    -> #cl:scl_type bcl
    -> n:(allroot_type bbl bcl)
    -> al:list (oneroot_type bl cl){satisfied_al_MakeAllRootList n al} -> list (allroot_type bbl bcl)
let rec makeAllRootList #bbl #bcl #bl #cl n al = 
    match al with
    | [] -> []
    | hd::tl -> 
        (makeAllRoot #bbl #bcl #bl #cl n hd)::(makeAllRootList #bbl #bcl #bl #cl n tl)

val dykstraAppendListUsualAllRoot:#bbl:bbl_type -> #bcl:bcl_type
    -> l1:list (allroot_type bbl bcl)  -> l2:list (allroot_type bbl bcl) -> v:list (allroot_type bbl bcl){forall i. mem i v = (mem i l1 || mem i l2)}
let dykstraAppendListUsualAllRoot l1 l2 = append l1 l2

val dykstraRemoveListUsualAllRoot: #bbl:bbl_type -> #bcl:bcl_type
    -> l:list (allroot_type bbl bcl) -> x:(allroot_type bbl bcl)-> v:list (allroot_type bbl bcl){(not(mem x v))/\(forall i. mem i v ==> mem i l)}
let dykstraRemoveListUsualAllRoot l x = memRemove x l

val dykstraSetListUsualAllRoot: #bbl:bbl_type -> #bcl:bcl_type
    -> l:list (allroot_type bbl bcl) -> x:allroot_type bbl bcl -> nl:list (allroot_type bbl bcl) 
    -> v:list (allroot_type bbl bcl) {(not(mem x v))/\(forall i. mem i v ==> (mem i l || mem i nl))}
let dykstraSetListUsualAllRoot l x nl = dykstraRemoveListUsualAllRoot (dykstraAppendListUsualAllRoot nl l) x


val dykstraGetBestListUsualAllRoot: bbl:bbl_type -> bcl:bcl_type
    -> l:list (allroot_type bbl bcl) -> allroot_type bbl bcl
let rec dykstraGetBestListUsualAllRoot bbl bcl l = 
    match l with
    | [] -> []
    | hd::tl -> 
        let v = dykstraGetBestListUsualAllRoot bbl bcl tl in
                match v with
                | [] -> hd
                | hd3::tl3 -> 
                match hd with
                | [] -> v
                | hd2::tl3 -> 
                    if hd2.evaluation < hd3.evaluation then hd else v

val getPositionPreviousAllRoot: #bbl:bbl_type -> #bcl:bcl_type
    -> l:allroot_type bbl bcl -> rp:robot_position{last_setting_robot_position l rp}
let getPositionPreviousAllRoot l = 
    match l with
    | [] -> first_robot_position
    | hd::tl -> hd.content.lrp

val getActionSupport: bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> kl:list (allroot_type bbl bcl)
    -> t:nat 
    -> Tot (allroot_type bbl bcl) (decreases t)
let rec getActionSupport bbl bcl kl t  =
    if t <= 0 then []
    else
    let bk = dykstraGetBestListUsualAllRoot bbl bcl kl in
        let nbl = getBlocksForNextAllRoot bbl bk in
            let ncl = getCerclesForNextAllRoot bcl bk in
                    if (length nbl = 0) then bk
                    else
                        let rp = getPositionPreviousAllRoot bk in
                            let v = getOneAction nbl ncl rp in
                                let newevals = makeAllRootList bk v in
                                    let nkl = dykstraSetListUsualAllRoot kl bk newevals in
                                        getActionSupport bbl bcl nkl (t-1)

val getAction: bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> bcl:cercles{(notOverlap bcl)/\(length bcl = 8)} -> allroot_type bbl bcl
let getAction bbl bcl = getActionSupport bbl bcl [] (bf 10)

