module ET_MakeRootEval3

open ET_Base
open ET_OtherBase
open Prims

open ET_MakeRootBase
open ET_MakeRootByBlock
open ET_MakeRootByCercle 
open FStar.Mul

module L = FStar.List.Tot

val checkHalfWayPoint: b:block -> x:robot_position -> bool
let checkHalfWayPoint b x = (Block?.pos b) = x
(*
//満たすべき性質
type oneactionmeets (bl:blocks{notOverlap bl}) (cl:cercles{notOverlap cl}) = 
    | Oneactionmeets:
    block:block_sb bl -> 
    cercle:cercle_sc block cl-> 
    frp:robot_position ->
    rootbyblock:(block_root block frp bl) ->
    rootbycercle:(cercle_root block cl cercle (removeBlocks bl block)) ->
    hrp:robot_position{Cons?.hd rootbyblock = hrp} ->
    lrp:robot_position{Cons?.hd rootbycercle = lrp} ->
    dis:nat{dis = length rootbyblock + length rootbycercle - 1} ->
    oneactionmeets bl cl
//{checkFinishPoint cercle lrpos} -> 
//評価表
//b:階層 0...7
//n:階層中の番号
//p:前回の階層中の番号
//a:その時のoneaction

type eval2 (bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}) (bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}) = 
    | None
    | Eval2:
    #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)} -> 
    #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)} ->
    a:oneactionmeets bl cl ->
    b:block{(b = (Oneactionmeets?.block a))/\(mem b bl)/\(mem b bbl)} -> 
    c:cercle{(c = (Oneactionmeets?.cercle a))/\(mem c cl)/\(mem c bcl)} -> 
    n:eval2 bbl bcl ->
    st:nat -> 
    e:nat ->
    eval2 bbl bcl



//満たすべき性質の型を通常のデータ型に移す
val makeOneActionDataFromMeetsData2: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> v:(oneactionmeets bl cl) -> oneaction
let makeOneActionDataFromMeetsData2 #bl #cl v = 
    Oneaction (Oneactionmeets?.block v) (Oneactionmeets?.cercle v) (Oneactionmeets?.frp v) (Oneactionmeets?.rootbyblock v) (Oneactionmeets?.rootbycercle v) (Oneactionmeets?.hrp v) (Oneactionmeets?.lrp v) (Oneactionmeets?.dis v)

    //{match n with | Some k -> True | None -> (forall i. mem i bl = mem i bbl)/\(forall i. mem i cl = mem i bcl)/\(Nil? pbl)/\(Nil? pcl)} -> 
//満たすべき性質用の満たすべき性質用のデータ型を作成
val makeOneActionMeetsData: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp bl) -> ct:(cercle_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> oneactionmeets bl cl
let makeOneActionMeetsData rp bt ct = Oneactionmeets (Block_get?.b bt) (Cercle_get?.c ct) rp (Block_get?.r bt) (Cercle_get?.r ct) (Cons?.hd (Block_get?.r bt)) (Cons?.hd (Cercle_get?.r ct)) (length ((Block_get?.r bt)) + length ((Cercle_get?.r ct)) - 1)

//ブロックのルート型とサークルのルート型の２つから全てのパターンのデータを作成
val makeOneActionFromBlockToCercle: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> rp:robot_position ->  bt:(block_get rp bl) -> ctl:(cercles_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> list (oneactionmeets bl cl)
let rec makeOneActionFromBlockToCercle rp bt ctl = 
    match ctl with
    | [] -> []
    | hd::tl -> (makeOneActionMeetsData rp bt hd)::(makeOneActionFromBlockToCercle rp bt tl)

//ブロックからサークルに設置できるパターンのデータを全て作成 2
val getOneActionFromBlockToCercleSupport: #cl:cercles{notOverlap cl} -> bl:blocks{notOverlap bl} -> rp:robot_position ->  bt:(block_get rp bl) ->  cls:cercles{(notOverlap cls)/\(sameColor (getListCercleColor cls) (Block?.col (Block_get?.b bt)))/\(forall i. mem i cls ==> mem i cl)} -> list (oneactionmeets bl cl)
let rec getOneActionFromBlockToCercleSupport #cl bl rp bt cls = 
    match cls with
    | [] -> []
    | hd::tl -> 
        let v = getBestRootByCercles2 #cl bl (Block_get?.b bt) hd (Block?.pos (Block_get?.b bt)) in
              //  let v = getBestRootByCercles1 #cl bl (Block_get?.b bt) hd (Block?.pos (Block_get?.b bt)) in
            append (makeOneActionFromBlockToCercle rp bt v) (getOneActionFromBlockToCercleSupport #cl bl rp bt tl)

val getOneActionFromBlockToCercleSupportLemma1: #cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp []) ->Lemma(Nil? (getOneActionFromBlockToCercleSupport #cl [] rp bt [])) [SMTPat(getOneActionFromBlockToCercleSupport #cl [] rp bt [])]
let getOneActionFromBlockToCercleSupportLemma1 #cl rp bt = ()


val getBlockColorToCercleSupport: cl:cercles{notOverlap cl} -> cls:cercles{(notOverlap cl)/\(forall i. mem i cls ==> mem i cl)} -> b:block -> v:cercles{(notOverlap v)/\(forall i. mem i v ==> mem i cl)}
let rec getBlockColorToCercleSupport cl cls b = 
    match cls with
    | [] -> cl
    | hd::tl ->
         let v = getBlockColorToCercleSupport cl tl b in
    if not(Cercle?.col hd = Block?.col b) then 
    memRemove hd v else v

assume val getBlockColorToCercleLemma: cl:cercles{notOverlap cl} -> b:block -> l:cercles{(notOverlap l)/\(forall i. mem i l ==> mem i cl)} -> Lemma(sameColor (getListCercleColor l) (Block?.col b))// [SMTPat(getBlockColorToCercleSupport cl cl b)]

val getBlockColorToCercle: cl:cercles{notOverlap cl} -> b:block -> v:cercles{(notOverlap v)/\(forall i. mem i v ==> mem i cl)/\(sameColor (getListCercleColor v) (Block?.col b))}
let getBlockColorToCercle cl b = let v = getBlockColorToCercleSupport cl cl b in let _ = getBlockColorToCercleLemma cl b v in v

 //ブロックからサークルに設置できるパターンのデータを全て作成 2           
val getOneActionFromBlockToCercle: bl:blocks{notOverlap bl} -> cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp bl)-> list (oneactionmeets bl cl)
let getOneActionFromBlockToCercle bl cl rp bt = 
        let cls = getBlockColorToCercle cl (Block_get?.b bt) in 
            getOneActionFromBlockToCercleSupport #cl bl rp bt cls

//１つのアクションのデータを全て取得する　2
val getOneActionSupport: bl:blocks{notOverlap bl} -> cl:cercles{notOverlap cl} -> rp:robot_position -> btl:(blocks_get rp bl) -> list (oneactionmeets bl cl)
let rec getOneActionSupport bl cl rp btl = 
    match btl with
    | [] -> []
    | hd::tl -> append (getOneActionFromBlockToCercle bl cl rp hd) (getOneActionSupport bl cl rp tl)


//ブロックメンバー削除する
//１つのアクションのデータを全て取得する　1
val getOneAction: bl:blocks{(notOverlap bl)/\(length bl > 0)} -> cl:cercles{notOverlap cl} -> rp:robot_position -> list (oneactionmeets bl cl)
let getOneAction bl cl rp = 
    let v = getBestRootByBlocks2 bl rp in
   // let v = getBestRootByBlocks1 bl rp in
        getOneActionSupport bl cl rp v

val makeEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> n:eval2 bbl bcl
    -> a:(oneactionmeets bl cl) -> eval2 bbl bcl
let makeEval #bbl #bcl #bl #cl n a = 
    match n with
        | Eval2 _ _ _ _ st e -> Eval2 a (Oneactionmeets?.block a) (Oneactionmeets?.cercle a) n (st+1) ((Oneactionmeets?.dis a) + e)
        | None -> Eval2 a (Oneactionmeets?.block a) (Oneactionmeets?.cercle a) None 0 (Oneactionmeets?.dis a)

val makeEvalList: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)} 
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> n:eval2 bbl bcl
    -> al:list (oneactionmeets bl cl) -> list (eval2 bbl bcl)
let rec makeEvalList #bbl #bcl #bl #cl n al = 
    match al with
    | [] -> []
    | hd::tl -> (makeEval #bbl #bcl #bl #cl n hd)::(makeEvalList #bbl #bcl #bl #cl n tl)

val dykstraAppendListUsualEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l1:list (eval2 bbl bcl)  -> l2:list (eval2 bbl bcl) -> v:list (eval2 bbl bcl){forall i. mem i v = (mem i l1 || mem i l2)}
let dykstraAppendListUsualEval l1 l2 = append l1 l2

val dykstraRemoveListUsualEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l:list (eval2 bbl bcl) -> x:(eval2 bbl bcl)-> v:list (eval2 bbl bcl){(not(mem x v))/\(forall i. mem i v ==> mem i l)}
let dykstraRemoveListUsualEval l x = memRemove x l

val dykstraSetListUsualEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l:list (eval2 bbl bcl) -> x:eval2 bbl bcl -> nl:list (eval2 bbl bcl) 
    -> v:list (eval2 bbl bcl) {(not(mem x v))/\(forall i. mem i v ==> (mem i l || mem i nl))}
let dykstraSetListUsualEval l x nl = dykstraRemoveListUsualEval (dykstraAppendListUsualEval nl l) x
 

val dykstraGetBestListUsualEval: bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l:list (eval2 bbl bcl) -> eval2 bbl bcl
let rec dykstraGetBestListUsualEval bbl bcl l = 
    match l with
    | [] -> None
    | hd::tl -> 
        let v = dykstraGetBestListUsualEval bbl bcl tl in
            match v with
            | None -> hd
            | Eval2 _ _ _ _ _ ve -> 
            match hd with
            | None -> v
            | Eval2 _ _ _ _ _ hde -> 
                if hde < ve then hd else v

val getPositionPreviousEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> e:eval2 bbl bcl -> robot_position
let getPositionPreviousEval e = 
    match e with
    | Eval2 a _ _ _ _ _ -> (Oneactionmeets?.lrp a)
    | None -> first_robot_position

//#set-options "--z3rlimit 100"
val getBlocksForNextEval: bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> e:eval2 bbl bcl
    -> Tot(v:blocks{(notOverlap v)/\(forall i. mem i v ==> mem i bbl)}) //(decreases %[8 - length ()])
let rec getBlocksForNextEval bbl #bcl e = 
    match e with
    | Eval2 _ b _ n _ _ ->     
        let v = getBlocksForNextEval bbl n in 
            memRemove b v  
    | None -> bbl

val getCerclesForNextEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> e:eval2 bbl bcl
    -> Tot(v:cercles{(notOverlap v)/\(forall i. mem i v ==> mem i bcl)})
let rec getCerclesForNextEval #bbl bcl e = 
    match e with     
        | Eval2 _ _ c n _ _ ->     
        let v = getCerclesForNextEval bcl n in 
            memRemove c v  
    | None -> bcl

val getActionSupport: bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> kl:list (eval2 bbl bcl)
    -> t:nat 
    -> Tot (eval2 bbl bcl) (decreases t)
let rec getActionSupport bbl bcl kl t  =
    if t <= 0 then None
    else
    let bk = dykstraGetBestListUsualEval bbl bcl kl in
        let nbl = getBlocksForNextEval bbl bk in
            let ncl = getCerclesForNextEval bcl bk in
                    if (length nbl = 0) then bk
                    else
                        let rp = getPositionPreviousEval bk in
                            let v = getOneAction nbl ncl rp in
                                let newevals = makeEvalList bk v in
                                    let nkl = dykstraSetListUsualEval kl bk newevals in
                                        getActionSupport bbl bcl nkl (t-1)

val getAction2: bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> bcl:cercles{(notOverlap bcl)/\(length bcl = 8)} -> eval2 bbl bcl
let getAction2 bbl bcl = getActionSupport bbl bcl [] (bf 10)


*)

type blocks_type = bl:blocks{notOverlap bl} 
type cercles_type = cl:cercles{notOverlap cl}

type bbl_type = bbl:blocks_type{(length bbl = 8)}
type bcl_type = bcl:cercles_type{(length bcl = 8)}
type sbl_type (bbl:bbl_type) = bl:blocks_type{(forall i. mem i bl ==> mem i bbl)} 
type scl_type (bcl:bcl_type) = cl:cercles_type{(forall i. mem i cl ==> mem i bcl)} 
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
    content:oneroot_type bl cl ->
    level:nat -> 
    evaluation:nat ->
    rootcontent_type bbl bcl

val allroot_meet_func: #bbl:bbl_type -> #bcl:bcl_type 
    -> l:list (rootcontent_type bbl bcl){Cons? l} -> Tot bool (decreases (l))
let rec allroot_meet_func #bbl #bcl l = 
    match l with
    | [hd] -> (hd.bl = bbl) && (hd.cl = bcl)
    | hd1::hd2::tl 
        -> (hd1.content.frp = hd2.content.lrp)
        && (L.mem hd1.content.block hd2.bl) && not(mem hd2.content.block hd1.bl)
        && (L.mem hd1.content.cercle hd2.cl) && not(mem hd2.content.cercle hd1.cl)
        && (allroot_meet_func (hd2::tl))

type allroot_type (bbl:bbl_type) (bcl:bcl_type)
    = l:(list (rootcontent_type bbl bcl)){(Cons? l) /\ allroot_meet_func l}


    //{match n with | Some k -> True | None -> (forall i. mem i bl = mem i bbl)/\(forall i. mem i cl = mem i bcl)/\(Nil? pbl)/\(Nil? pcl)} -> 
//満たすべき性質用の満たすべき性質用のデータ型を作成
val makeOneActionMeetsData: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp bl) -> ct:(cercle_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> oneactionmeets bl cl
let makeOneActionMeetsData rp bt ct = Oneactionmeets (Block_get?.b bt) (Cercle_get?.c ct) rp (Block_get?.r bt) (Cercle_get?.r ct) (Cons?.hd (Block_get?.r bt)) (Cons?.hd (Cercle_get?.r ct)) (length ((Block_get?.r bt)) + length ((Cercle_get?.r ct)) - 1)

//ブロックのルート型とサークルのルート型の２つから全てのパターンのデータを作成
val makeOneActionFromBlockToCercle: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> rp:robot_position ->  bt:(block_get rp bl) -> ctl:(cercles_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> list (oneactionmeets bl cl)
let rec makeOneActionFromBlockToCercle rp bt ctl = 
    match ctl with
    | [] -> []
    | hd::tl -> (makeOneActionMeetsData rp bt hd)::(makeOneActionFromBlockToCercle rp bt tl)

//ブロックからサークルに設置できるパターンのデータを全て作成 2
val getOneActionFromBlockToCercleSupport: #cl:cercles{notOverlap cl} -> bl:blocks{notOverlap bl} -> rp:robot_position ->  bt:(block_get rp bl) ->  cls:cercles{(notOverlap cls)/\(sameColor (getListCercleColor cls) (Block?.col (Block_get?.b bt)))/\(forall i. mem i cls ==> mem i cl)} -> list (oneactionmeets bl cl)
let rec getOneActionFromBlockToCercleSupport #cl bl rp bt cls = 
    match cls with
    | [] -> []
    | hd::tl -> 
        let v = getBestRootByCercles2 #cl bl (Block_get?.b bt) hd (Block?.pos (Block_get?.b bt)) in
              //  let v = getBestRootByCercles1 #cl bl (Block_get?.b bt) hd (Block?.pos (Block_get?.b bt)) in
            append (makeOneActionFromBlockToCercle rp bt v) (getOneActionFromBlockToCercleSupport #cl bl rp bt tl)

val getOneActionFromBlockToCercleSupportLemma1: #cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp []) ->Lemma(Nil? (getOneActionFromBlockToCercleSupport #cl [] rp bt [])) [SMTPat(getOneActionFromBlockToCercleSupport #cl [] rp bt [])]
let getOneActionFromBlockToCercleSupportLemma1 #cl rp bt = ()


val getBlockColorToCercleSupport: cl:cercles{notOverlap cl} -> cls:cercles{(notOverlap cl)/\(forall i. mem i cls ==> mem i cl)} -> b:block -> v:cercles{(notOverlap v)/\(forall i. mem i v ==> mem i cl)}
let rec getBlockColorToCercleSupport cl cls b = 
    match cls with
    | [] -> cl
    | hd::tl ->
         let v = getBlockColorToCercleSupport cl tl b in
    if not(Cercle?.col hd = Block?.col b) then 
    memRemove hd v else v

assume val getBlockColorToCercleLemma: cl:cercles{notOverlap cl} -> b:block -> l:cercles{(notOverlap l)/\(forall i. mem i l ==> mem i cl)} -> Lemma(sameColor (getListCercleColor l) (Block?.col b))// [SMTPat(getBlockColorToCercleSupport cl cl b)]

val getBlockColorToCercle: cl:cercles{notOverlap cl} -> b:block -> v:cercles{(notOverlap v)/\(forall i. mem i v ==> mem i cl)/\(sameColor (getListCercleColor v) (Block?.col b))}
let getBlockColorToCercle cl b = let v = getBlockColorToCercleSupport cl cl b in let _ = getBlockColorToCercleLemma cl b v in v

 //ブロックからサークルに設置できるパターンのデータを全て作成 2           
val getOneActionFromBlockToCercle: bl:blocks{notOverlap bl} -> cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp bl)-> list (oneactionmeets bl cl)
let getOneActionFromBlockToCercle bl cl rp bt = 
        let cls = getBlockColorToCercle cl (Block_get?.b bt) in 
            getOneActionFromBlockToCercleSupport #cl bl rp bt cls

//１つのアクションのデータを全て取得する　2
val getOneActionSupport: bl:blocks{notOverlap bl} -> cl:cercles{notOverlap cl} -> rp:robot_position -> btl:(blocks_get rp bl) -> list (oneactionmeets bl cl)
let rec getOneActionSupport bl cl rp btl = 
    match btl with
    | [] -> []
    | hd::tl -> append (getOneActionFromBlockToCercle bl cl rp hd) (getOneActionSupport bl cl rp tl)


//ブロックメンバー削除する
//１つのアクションのデータを全て取得する　1
val getOneAction: bl:blocks{(notOverlap bl)/\(length bl > 0)} -> cl:cercles{notOverlap cl} -> rp:robot_position -> list (oneactionmeets bl cl)
let getOneAction bl cl rp = 
    let v = getBestRootByBlocks2 bl rp in
   // let v = getBestRootByBlocks1 bl rp in
        getOneActionSupport bl cl rp v

val makeEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> n:eval2 bbl bcl
    -> a:(oneactionmeets bl cl) -> eval2 bbl bcl
let makeEval #bbl #bcl #bl #cl n a = 
    match n with
        | Eval2 _ _ _ _ st e -> Eval2 a (Oneactionmeets?.block a) (Oneactionmeets?.cercle a) n (st+1) ((Oneactionmeets?.dis a) + e)
        | None -> Eval2 a (Oneactionmeets?.block a) (Oneactionmeets?.cercle a) None 0 (Oneactionmeets?.dis a)

val makeEvalList: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)} 
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> n:eval2 bbl bcl
    -> al:list (oneactionmeets bl cl) -> list (eval2 bbl bcl)
let rec makeEvalList #bbl #bcl #bl #cl n al = 
    match al with
    | [] -> []
    | hd::tl -> (makeEval #bbl #bcl #bl #cl n hd)::(makeEvalList #bbl #bcl #bl #cl n tl)

val dykstraAppendListUsualEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l1:list (eval2 bbl bcl)  -> l2:list (eval2 bbl bcl) -> v:list (eval2 bbl bcl){forall i. mem i v = (mem i l1 || mem i l2)}
let dykstraAppendListUsualEval l1 l2 = append l1 l2

val dykstraRemoveListUsualEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l:list (eval2 bbl bcl) -> x:(eval2 bbl bcl)-> v:list (eval2 bbl bcl){(not(mem x v))/\(forall i. mem i v ==> mem i l)}
let dykstraRemoveListUsualEval l x = memRemove x l

val dykstraSetListUsualEval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l:list (eval2 bbl bcl) -> x:eval2 bbl bcl -> nl:list (eval2 bbl bcl) 
    -> v:list (eval2 bbl bcl) {(not(mem x v))/\(forall i. mem i v ==> (mem i l || mem i nl))}
let dykstraSetListUsualEval l x nl = dykstraRemoveListUsualEval (dykstraAppendListUsualEval nl l) x
 