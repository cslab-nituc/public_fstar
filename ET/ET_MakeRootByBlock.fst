module ET_MakeRootByBlock
open ET_Base
open ET_OtherBase
open Prims

open ET_MakeRootBase

open ET_MakeRootBase2

//open ET_MakeRootBase2 
//ブロックの経路情報の型
type block_sb (bl:blocks{notOverlap bl}) = v:block{mem v bl}

type block_root_s (rp:field_position) (bl:blocks{notOverlap bl}) = root_s (getListBlockPosition bl) [] rp

type block_root (b:block) (rp:field_position) (bl:blocks{notOverlap bl}) = v:block_root_s rp bl{(Block?.pos b) = (Cons?.hd v)}

type block_get (rp:field_position) (bl:blocks{notOverlap bl}) = 
    | Block_get:
    b:block_sb bl ->
    r:block_root b rp bl ->
    block_get rp bl

type blocks_get (rp:field_position) (bl:blocks{notOverlap bl}) = list_notover (block_get rp bl)

//その地点にブロックが存在するかチェックして、あれば返す                
val findBlocks: bl:blocks{length bl > 0} -> rp:field_position{mem rp (getListBlockPosition bl)}->b:block{(rp = (Block?.pos b))/\(mem b bl)}
let rec findBlocks bl rp = 
    match bl with 
    | hd::tl -> if (Block?.pos hd) = rp then hd else (findBlocks tl rp)

//val findBlocksLemma: bl:blocks -> rp:field_position -> Lemma()
//ロボットの現位置から次の取得できるブロックまでの経路を全て取得する
//(Not Dykstra)
val getBlocksRoot1: #rp:field_position -> bl:blocks{notOverlap bl} -> rp:robot_position -> Tot(list_notover (block_root_s rp bl))
let getBlocksRoot1 bl rp = findRootToList (getListBlockPosition bl) [] rp

//(Dykstra)
val getBlocksRoot2: #rp:field_position -> bl:blocks{notOverlap bl} -> rp:robot_position -> Tot(list_notover (block_root_s rp bl))
let getBlocksRoot2 bl rp = findRootToList2 (getListBlockPosition bl) [] rp

val includehdbllems1: bl:blocks{notOverlap bl} -> brl:root_nb (getListBlockPosition bl) [] -> Lemma(forall i. mem i (getListBlockPosition bl) ==> not(mem i brl))
let rec includehdbllems1 bl brl = 
    match brl with
    | [] -> ()
     | hd::tl -> includehdbllems1 bl tl

assume val includehdbllems2: rpl:set_field -> r:set_field{(length r > 0)/\(notOverlaplistsoftl r rpl)} -> Lemma(mem (Cons?.hd r) rpl)
(*
let rec includehdbllems2 rpl r = 
    match r with
    | [] -> ()
    | hd::tl -> let _ = assert(mem hd rpl) in admit()
*)

val includehdbllems3: #rp:field_position -> bl:blocks{notOverlap bl} -> r:(block_root_s rp bl){length r > 0} -> Lemma(mem (Cons?.hd r ) (getListBlockPosition bl))
let includehdbllems3 #rp bl r = includehdbllems2 (getListBlockPosition bl) r

//経路情報から(ブロック,経路)の形に直す
val getBlocksRootToTuple2: #rp:field_position -> bl:blocks{(notOverlap bl)/\(length bl > 0)} -> list_notover (block_root_s rp bl) -> (blocks_get rp bl)
let rec getBlocksRootToTuple2 #rp bl l = 
    match l with
    | [] -> []
    | hd::tl -> 
        let _ = includehdbllems3 #rp bl hd in
        let v = findBlocks bl (Cons?.hd hd) in
            let _ = notOverlapSupportLemma (Block_get v hd) (getBlocksRootToTuple2 bl tl) in
            (Block_get v hd)::(getBlocksRootToTuple2 bl tl)


//最短経路の導出 (Not Dykstra)
val getBestRootByBlocks1: bl:blocks{(notOverlap bl)/\(length bl > 0)} -> rp:robot_position ->  (blocks_get rp bl)
let getBestRootByBlocks1 bl rp = 
    let v = getBlocksRoot1 #rp bl rp in
        getBlocksRootToTuple2 bl v

//最短経路の導出 (Dykstra)
val getBestRootByBlocks2: bl:blocks{(notOverlap bl)/\(length bl > 0)} -> rp:robot_position ->  (blocks_get rp bl)
let getBestRootByBlocks2 bl rp = 
    let v = getBlocksRoot2 #rp bl rp in
        getBlocksRootToTuple2 bl v