module ET_MakeRootEval 

open ET_Base
open ET_OtherBase
open Prims

open ET_MakeRootBase
open ET_MakeRootByBlock
open ET_MakeRootByCercle 

val checkHalfWayPoint: b:block -> x:robot_position -> bool
let checkHalfWayPoint b x = (Block?.pos b) = x

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

type eval = 
    | Eval:
    a:oneaction -> 
    b:nat -> 
    n:list eval -> 
    e:nat ->
    eval

//type cercle_get2 (b:block) (c:cercle) (bl:blocks{notOverlap bl}) =  (tuple2 (x:cercle{(Cercle?.col x) = (Block?.col b)}) (cercle_root c bl))

//満たすべき性質用の満たすべき性質用のデータ型を作成
val makeOneActionMeetsData: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp bl) -> ct:(cercle_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> (oneactionmeets bl cl)
let makeOneActionMeetsData rp bt ct = Oneactionmeets (Block_get?.b bt) (Cercle_get?.c ct) rp (Block_get?.r bt) (Cercle_get?.r ct) (Cons?.hd (Block_get?.r bt)) (Cons?.hd (Cercle_get?.r ct)) (length ((Block_get?.r bt)) + length ((Cercle_get?.r ct)) - 1)

//満たすべき性質の型を通常のデータ型に移す
val makeOneActionDataFromMeetsData: #bl:blocks{notOverlap bl} -> (#cl:cercles{notOverlap cl}) -> v:(oneactionmeets bl cl) -> oneaction
let makeOneActionDataFromMeetsData #bl #cl v = 
    Oneaction (Oneactionmeets?.block v) (Oneactionmeets?.cercle v) (Oneactionmeets?.frp v) (Oneactionmeets?.rootbyblock v) (Oneactionmeets?.rootbycercle v) (Oneactionmeets?.hrp v) (Oneactionmeets?.lrp v) (Oneactionmeets?.dis v)

//通常のデータ型を作成(保証のために満たすべき性質のデータ型に一度移す)
val makeOneAction: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp bl) -> ct:(cercle_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> oneaction
let makeOneAction rp bt ct = 
    let v = makeOneActionMeetsData rp bt ct in
        makeOneActionDataFromMeetsData v 

//ブロックのルート型とサークルのルート型の２つから全てのパターンのデータを作成
val makeOneActionFromBlockToCercle: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> rp:robot_position ->  bt:(block_get rp bl) -> ctl:(cercles_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> list oneaction
let rec makeOneActionFromBlockToCercle rp bt ctl = 
    match ctl with
    | [] -> []
    | hd::tl -> (makeOneAction rp bt hd)::(makeOneActionFromBlockToCercle rp bt tl)
    
//ブロックからサークルに設置できるパターンのデータを全て作成 2
val getOneActionFromBlockToCercleSupport: #cl:cercles{notOverlap cl} -> bl:blocks{notOverlap bl} -> rp:robot_position ->  bt:(block_get rp bl) ->  cls:cercles{(notOverlap cls)/\(sameColor (getListCercleColor cls) (Block?.col (Block_get?.b bt)))/\(forall i. mem i cls ==> mem i cl)} -> list oneaction
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
val getOneActionFromBlockToCercle: bl:blocks{notOverlap bl} -> cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp bl)-> list oneaction
let getOneActionFromBlockToCercle bl cl rp bt = 
        let cls = getBlockColorToCercle cl (Block_get?.b bt) in 
            getOneActionFromBlockToCercleSupport #cl bl rp bt cls

//１つのアクションのデータを全て取得する　2
val getOneActionSupport: bl:blocks{notOverlap bl} -> cl:cercles{notOverlap cl} -> rp:robot_position -> btl:(blocks_get rp bl) -> list oneaction
let rec getOneActionSupport bl cl rp btl = 
    match btl with
    | [] -> []
    | hd::tl -> append (getOneActionFromBlockToCercle bl cl rp hd) (getOneActionSupport bl cl rp tl)


//ブロックメンバー削除する
//１つのアクションのデータを全て取得する　1
val getOneAction: bl:blocks{(notOverlap bl)/\(length bl > 0)} -> cl:cercles{notOverlap cl} -> rp:robot_position -> list oneaction
let getOneAction bl cl rp = 
    let v = getBestRootByBlocks2 bl rp in
   // let v = getBestRootByBlocks1 bl rp in
        getOneActionSupport bl cl rp v
        
val makeEval: a:oneaction -> b:nat -> n:list eval -> eval
let makeEval a b n = Eval a b n (Oneaction?.dis a)

val getAction: bl:blocks{notOverlap bl} -> cl:cercles{(notOverlap cl)/\(length bl = length cl)} -> rp:robot_position -> n:nat -> Tot(list eval)(decreases %[length bl; length cl; 1; 0])
val getActionSupport: bl:blocks{notOverlap bl} -> cl:cercles{(notOverlap cl)/\(length bl = length cl)} -> l:list oneaction -> rp:robot_position -> n:nat ->Tot(list eval) (decreases %[length bl; length cl; 0; length l; ])

assume val memls: #t:eqtype -> x:t -> l:list t -> Lemma(mem x l)

//ある地点から全てのEvalを求める
let rec getAction bl cl rp n = 
    match bl with
    | [] -> []
    | hd::tl -> 
        let v = getOneAction bl cl rp in 
            getActionSupport bl cl v rp n
and getActionSupport bl cl l rp n = 
    match l with
    | [] -> []
    | hd::tl -> 
    //これは必ず成り立つ。oneactionmeetsならば必ず成り立つため証明省略
    memls (Oneaction?.block hd) bl; memls (Oneaction?.cercle hd) cl;
    let nbl = (removeBlocks bl (Oneaction?.block hd)) in
        let ncl = (removeCercles cl (Oneaction?.cercle hd)) in
            let v = (getAction nbl ncl (Oneaction?.lrpos hd) (n+1)) in
                let s = makeEval hd n v in
                    s::(getActionSupport bl cl tl rp n)

//最初の地点から全てのEvalを求める
val getActionAll: bl:blocks{notOverlap bl} -> cl:cercles{(notOverlap cl)/\(length bl = length cl)} -> list eval
let getActionAll bl cl = getAction bl cl first_robot_position 0

type evls =
    | Evls:
    h:nat -> 
    el:list eval -> 
    evls
//最適な評価値を取得する
val getBestEval: l:list eval -> evls
let rec getBestEval l = 
    match l with
     | [] -> (Evls 0 [])
     | hd::tl -> 
        let v = getBestEval tl in
            let s = getBestEval (Eval?.n hd) in
                if (Evls?.h v) = 0 then Evls ((Eval?.e hd) + (Evls?.h s))  (hd::(Evls?.el s))
                else
                    if (Eval?.e hd) + (Evls?.h s) < (Evls?.h v) 
                    then Evls ((Eval?.e hd) + (Evls?.h s))  (hd::(Evls?.el s))
                    else v 

