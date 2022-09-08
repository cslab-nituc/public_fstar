module ET_MakeRootEval2
open LowStar.BufferOps
open ET_Base
open ET_OtherBase
open Prims

open ET_MakeRootBase
open ET_MakeRootByBlock
open ET_MakeRootByCercle 
open FStar.Mul

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module MO = LowStar.Modifies
open LowStar.BufferOps
open FStar.HyperStack.ST

module P = Pushpop2
open Pushpop2

val checkHalfWayPoint: b:block -> x:robot_position -> bool
let checkHalfWayPoint b x = (Block?.pos b) = x

//満たすべき性質
type oneactionmeets (bl:blocks{notOverlap bl}) (cl:cercles{notOverlap cl}) = 
{
    block:(block_sb bl);
    cercle:(cercle_sc block cl); 
    frp:robot_position;
    rootbyblock:(block_root block frp bl);
    rootbycercle:(cercle_root block cl cercle (removeBlocks bl block));
    hrp:(hrp:robot_position{Cons?.hd rootbyblock = hrp});
    lrp:(lrp:robot_position{Cons?.hd rootbycercle = lrp});
    dis:(dis:nat{dis = length rootbyblock + length rootbycercle - 1});
}
//{checkFinishPoint cercle lrpos} -> 
//評価表
//b:階層 0...7
//n:階層中の番号
//p:前回の階層中の番号
//a:その時のoneaction
type value (bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}) (bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}) = 
  | Value:
    #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)} -> 
    #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)} -> 
    a:(oneactionmeets bl cl) -> 
    b:block{(b = a.block)/\(mem b bl)/\(mem b bbl)} -> 
    c:cercle{(c = a.cercle)/\(mem c cl)/\(mem c bcl)} -> 
    st:nat -> 
    e:nat -> 
    n:nat -> 
    value bbl bcl

type eval (bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}) (bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}) = P.pointers_data (value bbl bcl)

//#set-options "--lax"
    //{match n with | Some k -> True | None -> (forall i. mem i bl = mem i bbl)/\(forall i. mem i cl = mem i bcl)/\(Nil? pbl)/\(Nil? pcl)} -> 
//満たすべき性質用の満たすべき性質用のデータ型を作成
val makeOneActionMeetsData: #bl:blocks{notOverlap bl} -> #cl:cercles{notOverlap cl} -> rp:robot_position -> bt:(block_get rp bl) -> ct:(cercle_get (Block_get?.b bt) cl (removeBlocks bl (Block_get?.b bt))) -> oneactionmeets bl cl
let makeOneActionMeetsData rp bt ct = {block=(Block_get?.b bt); cercle=(Cercle_get?.c ct); frp=rp; rootbyblock=(Block_get?.r bt); rootbycercle=(Cercle_get?.r ct); hrp=(Cons?.hd (Block_get?.r bt)); lrp=(Cons?.hd (Cercle_get?.r ct)); dis=(length ((Block_get?.r bt)) + length ((Cercle_get?.r ct)) - 1);}

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

val oneActionToEvalData_cons: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}
    -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> pre:value bbl bcl -> x:oneactionmeets bl cl -> n:nat -> Tot (value bbl bcl)
let oneActionToEvalData_cons #bbl #bcl #bl #cl pre x n
   = { a = x; b = x.block; c = x.cercle; st = (pre.st + 1); e = x.dis + pre.e; n = n;}

val oneActionToEvalData_nil: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}
    -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> x:oneactionmeets bl cl -> n:nat -> Tot (value bbl bcl)
let oneActionToEvalData_nil #bbl #bcl #bl #cl x n
   = { a = x; b = x.block; c = x.cercle; st = 1; e = x.dis; n = n;} 

val oneActionToEvalData_cons_Lemma: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}
    -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> pre:value bbl bcl-> x:oneactionmeets bl cl -> n:nat ->
    Lemma(let s = oneActionToEvalData_cons #bbl #bcl #bl #cl pre x n in (s.a = x) /\ (s.n = n) /\ (s.st = pre.st + 1) /\ (s.e >= pre.e)) [SMTPat (oneActionToEvalData_cons #bbl #bcl #bl #cl pre x n)]
let oneActionToEvalData_cons_Lemma #bbl #bcl #bl #cl pre x n = ()

val oneActionToEvalData_nil_Lemma: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}
    -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> x:oneactionmeets bl cl -> n:nat -> 
    Lemma(let s = oneActionToEvalData_nil #bbl #bcl #bl #cl x n in (s.a = x) /\ (s.n = n) ) [SMTPat (oneActionToEvalData_nil #bbl #bcl #bl #cl x n)]
let oneActionToEvalData_nil_Lemma #bbl #bcl #bl #cl x n = ()


val insert_eval_cons: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l: list (eval bbl bcl)
    -> pre:eval bbl bcl{L.memP pre l}
    -> v:value bbl bcl 
     -> ST (nl:list (eval bbl bcl)) (requires ( fun h -> 
      P.well_formed_listpointers_data_base h l  /\
      P.well_formed_listpointers_data h l /\
      P.well_formed_pointers_data_base h pre /\
      P.well_formed_pointers_data h pre l /\
      P.member_disjoint_max_listpointers_data h (Value?.n v) l Value?.n  /\
      P.member_disjoint_max_pointers_data h (Value?.n v) pre Value?.n /\
      P.sorted h l Value?.e
     ))
      (ensures (fun h0 nl h1 -> 
        P.well_formed_listpointers_data_base h1 nl  /\
        P.well_formed_listpointers_data h1 nl /\
        P.well_formed_pointers_data_base h1 pre /\
        P.well_formed_pointers_data h1 pre nl /\ 
        not(P.member_disjoint_max_listpointers_data h1 (Value?.n v) nl Value?.n) /\
        P.member_disjoint_max_listpointers_data h1 ((Value?.n v)+1) nl Value?.n /\
        P.member_disjoint_max_pointers_data h1 ((Value?.n v)+1) pre Value?.n /\
        P.sorted h1 nl Value?.e
      ))
let insert_eval_cons #bbl #bcl l pre v = 
  P.insert_cons l pre v Value?.e Value?.n

val insert_eval_nil: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l: list (eval bbl bcl)
    -> v:value bbl bcl 
     -> ST (nl:list (eval bbl bcl)) (requires ( fun h -> 
      P.well_formed_listpointers_data_base h l  /\
      P.well_formed_listpointers_data h l /\
      P.member_disjoint_max_listpointers_data h (Value?.n v) l Value?.n /\
      P.sorted h l Value?.e
     ))
      (ensures (fun h0 nl h1 -> 
      Cons? nl /\ 
        P.well_formed_listpointers_data_base h1 nl /\ 
        P.well_formed_listpointers_data h1 nl /\ 
        not(P.member_disjoint_max_listpointers_data h1 (Value?.n v) nl Value?.n ) /\
        P.member_disjoint_max_listpointers_data h1 ((Value?.n v)+1) nl Value?.n /\
        P.sorted h1 nl Value?.e
      ))
let insert_eval_nil #bbl #bcl l v = 
  P.insert_nil l v Value?.e Value?.n

val update_eval_cons: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}
    -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> l: list (eval bbl bcl)
    -> pre:eval bbl bcl{L.memP pre l}
    -> x:oneactionmeets bl cl
    -> n:nat
     -> ST (nl:list (eval bbl bcl)) (requires ( fun h -> 
      P.well_formed_listpointers_data_base h l  /\
      P.well_formed_listpointers_data h l /\
      P.well_formed_pointers_data_base h pre /\
      P.well_formed_pointers_data h pre l /\
      P.member_disjoint_max_listpointers_data h n l Value?.n /\
      P.member_disjoint_max_pointers_data h n pre Value?.n /\
      P.sorted h l Value?.e
     ))
      (ensures (fun h0 nl h1 -> 
        P.well_formed_listpointers_data_base h1 nl  /\
        P.well_formed_listpointers_data h1 nl /\
        P.well_formed_pointers_data_base h1 pre /\
        P.well_formed_pointers_data h1 pre nl /\ 
        not(P.member_disjoint_max_listpointers_data h1 n nl Value?.n) /\
        P.member_disjoint_max_listpointers_data h1 (n+1) nl Value?.n /\
        P.member_disjoint_max_pointers_data h1 (n+1) pre Value?.n /\
        P.sorted h1 nl Value?.e
      ))
let update_eval_cons #bbl #bcl #bl #cl l pre x n = 
  let s = !* pre in
  let d = !* s.pl in
  let v = oneActionToEvalData_cons #bbl #bcl #bl #cl d.data x n in
    insert_eval_cons #bbl #bcl l pre v


val update_eval_nil: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}
    -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> l: list (eval bbl bcl)
    -> x:oneactionmeets bl cl
    -> n:nat
     -> ST (nl:list (eval bbl bcl)) (requires ( fun h -> 
        P.well_formed_listpointers_data_base h l  /\
        P.well_formed_listpointers_data h l /\
        P.member_disjoint_max_listpointers_data h n l Value?.n /\
        P.sorted h l Value?.e
     ))
      (ensures (fun h0 nl h1 -> 
        Cons? nl /\
        P.well_formed_listpointers_data_base h1 nl  /\
        P.well_formed_listpointers_data h1 nl /\
        not(P.member_disjoint_max_listpointers_data h1 n nl Value?.n) /\
        P.member_disjoint_max_listpointers_data h1 (n+1) nl Value?.n /\
        P.sorted h1 nl Value?.e
      ))
let update_eval_nil #bbl #bcl #bl #cl l x n = 
  let v = oneActionToEvalData_nil #bbl #bcl #bl #cl x n in
    insert_eval_nil #bbl #bcl l v

  
#set-options "--max_ifuel 100 --max_fuel 200"
val update_listeval_nil: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}
    -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> l: list (eval bbl bcl)
    -> xl:list(oneactionmeets bl cl)
    -> n:nat
     -> ST (nl:list (eval bbl bcl)) (requires ( fun h -> 
        Cons? xl /\
        P.well_formed_listpointers_data_base h l  /\
        P.well_formed_listpointers_data h l /\
        P.member_disjoint_max_listpointers_data h n l Value?.n /\
        P.sorted h l Value?.e
     ))
      (ensures (fun h0 nl h1 -> 
        Cons? nl /\
      //  Cons? xl /\ 
        P.well_formed_listpointers_data_base h1 nl  /\
        P.well_formed_listpointers_data h1 nl /\
  //      not(P.member_disjoint_max_listpointers_data h1 n nl Value?.n) /\
        //P.member_disjoint_max_listpointers_data h1 (n+2) nl Value?.n /\
        P.sorted h1 nl Value?.e
      )) //(decreases xl)

let rec update_listeval_nil #bbl #bcl #bl #cl l xl n = 
  if (length xl = 1) then update_eval_nil #bbl #bcl #bl #cl l (Cons?.hd xl) n
  else 
      let s = update_eval_nil #bbl #bcl #bl #cl l (Cons?.hd xl) n in
        let t = update_listeval_nil #bbl #bcl #bl #cl s (Cons?.tl xl) (n+1) in
        t
         
      

(*
val update_listeval: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}
    -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> #bl:blocks{(notOverlap bl)/\(forall i. mem i bl ==> mem i bbl)}
    -> #cl:cercles{(notOverlap cl)/\(forall i. mem i cl ==> mem i bcl)}
    -> l: list (eval bbl bcl)
    -> pre:option (eval bbl bcl)
    -> xl:list (oneactionmeets bl cl)
    -> n:nat
     -> ST (nl:list (eval bbl bcl)) (requires ( fun h -> 
      Cons? xl /\
      P.well_formed_listpointers_data_base h l  /\
      P.well_formed_listpointers_data h l /\
      (match pre with
      | None -> True
      | Some k -> 
          (Cons? l) /\ 
          (L.memP k l) /\
          (P.well_formed_pointers_data_base h k) /\
          (P.well_formed_pointers_data h k l) /\ 
          (P.member_disjoint_max_pointers_data h n k Value?.n)
      ) /\
      P.member_disjoint_max_listpointers_data h n l Value?.n /\
      P.sorted h l Value?.e
     ))
      (ensures (fun h0 nl h1 -> 
        Cons? nl /\
        P.well_formed_listpointers_data_base h1 nl  /\
        P.well_formed_listpointers_data h1 nl /\
        (match pre with
          | None -> True
          | Some k -> 
            (Cons? l) /\ 
            (L.memP k l) /\
            (P.well_formed_pointers_data_base h1 k) /\
            (P.well_formed_pointers_data h1 k nl) /\ 
            (P.member_disjoint_max_pointers_data h1 (n+1) k Value?.n)
      ) /\
        not(P.member_disjoint_max_listpointers_data h1 n nl Value?.n) /\
        P.member_disjoint_max_listpointers_data h1 (n+1) nl Value?.n /\
        P.sorted h1 nl Value?.e
      ))
let update_listeval #bbl #bcl #bl #cl l pre x n = 
  match pre with
  | None -> 
    match lupdate_eval_nil l x n
  | hd::tl -> 
  
(*)
(*)
(*)
val makelist_eval_cons: #bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> #bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> l: list (eval bbl bcl)
    -> p:option (pre:eval bbl bcl{L.memP pre l})
    -> v:list (oneaction)
     -> ST (nl:list (eval bbl bcl)) (requires ( fun h -> 
     (match p with
     | None -> Nil? l
     | Some k -> Cons? l) /\
      P.well_formed_listpointers_data_base h l  /\
      P.well_formed_listpointers_data h l /\
      P.well_formed_pointers_data_base h pre /\
      P.well_formed_pointers_data h pre l /\
      P.member_disjoint_max_listpointers_data h (Value?.nv) l Value?.n/\
      P.member_disjoint_max_pointers_data h (Value?.nv) pre Value?.n/\
      P.sorted h l getDetailEvalContent_e
     ))
      (ensures (fun h0 nl h1 -> 
        P.well_formed_listpointers_data_base h1 nl  /\
        P.well_formed_listpointers_data h1 nl /\
        P.well_formed_pointers_data_base h1 pre /\
        P.well_formed_pointers_data h1 pre nl /\ 
        not(P.member_disjoint_max_listpointers_data h1 (Value?.nv) nl getDetailEvalContent_n) /\
        P.member_disjoint_max_listpointers_data h1 ((Value?.nv)+1) nl Value?.n/\
        P.member_disjoint_max_pointers_data h1 ((Value?.nv)+1) pre Value?.n/\
        P.sorted h1 nl Value?.e
      ))


(*)
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