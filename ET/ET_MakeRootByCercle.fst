module ET_MakeRootByCercle
open ET_Base
open ET_OtherBase
open Prims

open ET_MakeRootBase
open ET_MakeRootBase2

type cercle_direction_support = n:int{(-1 <= n)/\(n <= 0)}

type supportCercleDirection = 
    | SCDirection:
    x:cercle_direction_support ->
    y:cercle_direction_support -> supportCercleDirection

//サークル座標からフィールド座標に置き換えるときの型
val cercle_direction_all : list_notover supportCercleDirection
let cercle_direction_all = [(SCDirection (-1) (-1));(SCDirection (-1) 0);(SCDirection 0 (-1));(SCDirection 0 0)]

val checkFinishPointSuuport: dl:list_notover supportCercleDirection -> c:cercle -> rp:robot_position -> bool
let rec checkFinishPointSuuport dl c rp = 
    match dl with 
    | [] -> false
    | hd::tl -> 
        let pos = (Cercle?.pos c) in
            let x = (XYPosition?.x pos) + (SCDirection?.x hd) in
                let y = (XYPosition?.y pos) + (SCDirection?.y hd) in
                    let v = XYPosition x y in
                        (rp = v) || (checkFinishPointSuuport tl c rp) 
                        
val checkFinishPoint: c:cercle -> x:robot_position -> bool
let checkFinishPoint c x = checkFinishPointSuuport cercle_direction_all c x

//サークルから隣接するブロックの座標を４つのタプルで返す 2
val getCercleToBlockPositionSupport: c:cercle -> dl:list_notover supportCercleDirection -> vl:set_field{length vl = length dl}
let rec getCercleToBlockPositionSupport c dl = 
    match dl with 
    | [] -> [] 
    | hd::tl -> 
        let pos = (Cercle?.pos c) in
            let x = (XYPosition?.x pos) + (SCDirection?.x hd) in
                let y = (XYPosition?.y pos) + (SCDirection?.y hd) in
                    let v = XYPosition x y in
                        let _ = notOverlapSupportLemma v (getCercleToBlockPositionSupport c tl) in
                            v::(getCercleToBlockPositionSupport c tl) 


//サークルから隣接するブロックの座標をリストで返す 1
val getCercleToBlockPosition: c:cercle -> l:set_field{length l = 4}
let getCercleToBlockPosition c = getCercleToBlockPositionSupport c cercle_direction_all 

type cercle_sc (b:block) (cl:cercles{notOverlap cl}) = c:cercle{(Cercle?.col c = Block?.col b)/\(mem c cl)}
type cercles_sc (b:block) (cl:cercles{notOverlap cl}) = list_notover (cercle_sc b cl)

//サークルの経路情報の型
type cercle_root (b:block) (cl:cercles{notOverlap cl}) (c:cercle_sc b cl) (bl:blocks{notOverlap bl}) =  root_s (getCercleToBlockPosition c) (getListBlockPosition bl) (Block?.pos b)

type cercle_get (b:block) (cl:cercles{notOverlap cl}) (bl:blocks{notOverlap bl}) =  
    | Cercle_get:
    c:cercle_sc b cl ->
    r:cercle_root b cl c bl -> 
    cercle_get b cl bl

type cercles_get (b:block) (cl:cercles{notOverlap cl}) (bl:blocks{notOverlap bl}) = list_notover (cercle_get b cl bl)

//ブロックの現位置からサークルに設置できるブロックであるか判定
//Not Dykstra
val getCerclesRoot1: #b:block -> #cl:cercles{notOverlap cl} -> bl:blocks{notOverlap bl} -> c:cercle_sc b cl -> rp:robot_position{rp = Block?.pos b} -> list_notover (cercle_root b cl c bl)
let getCerclesRoot1 bl c rp = findRootToList (getCercleToBlockPosition c) (getListBlockPosition bl) rp
//Dykstra
val getCerclesRoot2: #b:block -> #cl:cercles{notOverlap cl} -> bl:blocks{notOverlap bl} -> c:cercle_sc b cl -> rp:robot_position{(rp = Block?.pos b)/\(not(mem rp (getListBlockPosition bl)))} -> list_notover (cercle_root b cl c bl)
let getCerclesRoot2 bl c rp = findRootToList2 (getCercleToBlockPosition c) (getListBlockPosition bl) rp

//経路情報から(サークル,経路)の形に直す
val getCercleRootToTuple2: #b:block -> (#cl:cercles{notOverlap cl}) -> (#bl:blocks{notOverlap bl}) -> c:cercle_sc b cl -> list_notover (cercle_root b cl c bl) -> (cercles_get b cl bl)
let rec getCercleRootToTuple2 #bl #cl c l = 
    match l with
    | [] -> []
    | hd::tl -> 
        let _ = notOverlapSupportLemma (Cercle_get c hd) (getCercleRootToTuple2 #bl #cl c tl) in
            (Cercle_get c hd)::(getCercleRootToTuple2 #bl #cl c tl)

val removeCercleBestRootFromRoots: (#sl:set_field) -> (#rl:set_field) -> (#frp:field_position) ->  l:list_notover (root_s sl rl frp){(notOverlap (map Cons?.hd l))/\(length l > 0)} -> v:(root_s sl rl frp){mem v l}
let rec removeCercleBestRootFromRoots #sl #rl #frp l = 
    match l with
    | [x] -> x
    | hd::tl -> 
        let v = removeCercleBestRootFromRoots #sl #rl #frp tl in 
            if length hd < length v then hd else v


val removeBlocksLemma1: bl:blocks{notOverlap bl} -> b:block{mem b bl} -> Lemma(not(mem b (removeBlocks bl b)))[SMTPat(removeBlocks bl b)]
let removeBlocksLemma1 bl b = ()

assume val removeBlocksLemma2: bl:blocks{notOverlap bl} -> b:block{mem b bl} -> Lemma(not(mem (Block?.pos b) (map Block?.pos (removeBlocks bl b))))[SMTPat(removeBlocks bl b)]
//let rec removeBlocksLemma2 bl b = ()

//最短経路の導出 Not Dykstra
val getBestRootByCercles1: #cl:cercles{notOverlap cl} -> bl:blocks{notOverlap bl} -> b:block{mem b bl} -> c:cercle_sc b cl -> rp:robot_position{rp = Block?.pos b} -> l:(cercles_get b cl (removeBlocks bl b)){length l <= 1}
let getBestRootByCercles1 #cl bl b c rp = 
    let v = getCerclesRoot1 (removeBlocks bl b) c rp in
        if Nil? v then []
        else
            let s = removeCercleBestRootFromRoots v in
            getCercleRootToTuple2 c [s]

//最短経路の導出 Dykstra
val getBestRootByCercles2: #cl:cercles{notOverlap cl} -> bl:blocks{notOverlap bl} -> b:block{mem b bl} -> c:cercle_sc b cl -> rp:robot_position{rp = Block?.pos b} -> l:(cercles_get b cl (removeBlocks bl b)){length l <= 1}
let getBestRootByCercles2 #cl bl b c rp = 
    let v = getCerclesRoot2 (removeBlocks bl b) c rp in
        if Nil? v then []
        else
            let s = removeCercleBestRootFromRoots v in
            getCercleRootToTuple2 c [s]