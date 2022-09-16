module ET_Base

open ET_OtherBase
//ベース

//有限なnat型
type finites (a:nat) (b:nat{a<=b}) = n:nat{(a<=n)/\(n<=b)}

type xyposition (a:nat) (b:nat{a<=b}) (c:nat) (d:nat{c<=d})  = 
    | XYPosition:
    x:finites a b ->
    y:finites c d -> xyposition a b c d

//ビンゴの左下を(0,0)とした時のフィールド全体のますの構成の二次方向(x,y軸)に対する最大範囲
type field_position = xyposition 0 3 0 3

type robot_position = field_position

//ブロックの全体範囲(x,y軸)
type block_position = field_position

//サークルの全体範囲(x,y軸)
type cercle_position = xyposition 1 3 1 3

//ロボットの移動手段　一次方向に対してどれだけ移動するか
type direction_range = n:int{(n >= -1) /\ (n <= 1)}

//ロボットの移動手段　2次方向(x,y軸)に対してどれだけ移動するか
type direction = 
    | Direction:
    x:direction_range->
    y:direction_range{(x+y <= 1) /\ (x+y >= -1) /\ not(x+y=0)} -> direction

//(ブロックをキャッチする,ブロックを離す)の２状態をキープする変数
type evalution_state = tuple2 bool bool 

//ブロックを並べる最大数
type evalution_range = finites 0 8

//(ブロックをキャッチする最大回数,ブロックを離す最大回数)
type evalution = 
    | Evalution:
    catch:evalution_range->
    put:evalution_range-> evalution

type real_evalution = 
    | Realevalution:
    catch:int->
    put:int-> real_evalution

//最初のロボットの位置
let first_robot_position : robot_position = XYPosition 1 0

//黒サークルの位置
let black_cercle_position : cercle_position = XYPosition 1 1

//色
type color = name:string{(name = "yellow") \/ (name = "green") \/ (name = "blue") \/ (name = "red")}

//被りがないlistの型
type list_notover (t:eqtype) = l:list t{notOverlap l}
//フィールドのリスト型 (保持用)
type set_field = list_notover field_position

//サークル
type cercle = 
    | Cercle:
    pos:cercle_position -> 
    col:color->
    cercle

//ブロック
type block = 
    | Block:
    pos:block_position -> 
    col:color ->
    block

//ルート
type oneaction = 
    | Oneaction:
    block:block -> 
    cercle:cercle ->
    frpos:robot_position ->
    rootbyblock:set_field ->
    rootbycercle:set_field ->
    hrpos:robot_position ->
    lrpos:robot_position -> 
    dis:nat ->
    oneaction
    
//サークルリストから位置リストをゲットする
val getListCerclePosition: l:list cercle->list cercle_position
let getListCerclePosition l = map Cercle?.pos l

//サークルリストからカラーリストをゲットする
val getListCercleColor: l:list cercle->list color
let getListCercleColor l = map Cercle?.col l

val getListBlockPosition: l:list block->list block_position
let getListBlockPosition l = map Block?.pos l
        
//ブロックリストからカラーリストをゲットする
val getListBlockColor: l:list block->list color
let getListBlockColor l = map Block?.col l


//リストから色を数える
val memCountColor: l:list color->m:color -> nat
let memCountColor l m = memCount l m

//カラーがそれぞれの色が２つセットされているかチェック
val colorTwiceSetingU: l:list color -> bool
let colorTwiceSetingU l = 
    let yc = memCountColor l "yellow" in
        let rc = memCountColor l "red" in
            let gc = memCountColor l "green" in
                let bc = memCountColor l "blue" in
                    if (yc <= 2) && (rc <= 2) && (gc <= 2) && (bc <= 2) then true else false
                
//それぞれの色が２つセットされているかチェック
val colorTwiceSetingS: l:list color -> bool
let colorTwiceSetingS l = 
    let yc = memCountColor l "yellow" in
        let rc = memCountColor l "red" in
            let gc = memCountColor l "green" in
                let bc = memCountColor l "blue" in
                    if (yc = 2) && (rc = 2) && (gc = 2) && (bc = 2) then true else false

val sameColor: l:list color -> c:color -> bool
let rec sameColor l c = 
    match l with
    | [] -> true
    | hd::tl -> (hd = c)&&(sameColor tl c)

//サークル上(2,2)のところに設置されているかチェック (2,2)にあったら→false , なかったらtrue
val checkNotCercle22: l:list cercle_position -> bool
let rec checkNotCercle22 l = 
    match l with
    | [] -> true
    | hd::tl -> if black_cercle_position = hd then false else checkNotCercle22 tl

//ブロックをゲットする
// 1...:<最初のみに適用>length l = 8   ....... ブロックの数が8 <最初のみに適用>
// 2...:notOverlap  l   ....... ブロックの位置に重なりがない
// 3...:colorTwiceSeting (getListBlockColor l)  ........ブロックの色が黄,赤,青,緑の2種類ずつになっている

type blocks = l:list_notover block{(length l <= 8) /\ (notOverlap  (getListBlockPosition l)) /\ (colorTwiceSetingU  (getListBlockColor l))}
assume val get_blocks: unit -> l:blocks{(notOverlap l) /\ (length l = 8) /\ (colorTwiceSetingS (getListBlockColor l))}

//サークルをゲットする
// 1...:<最初のみに適用>length l = 8   ....... ブロックの数が8
// 2...:(notOverlap (getListCerclePosition l))  ....... サークルの位置に重なりがない
// 3...:colorTwiceSeting (getListCercleColor l)  ........ サークルの色が黄,赤,青,緑の2種類ずつになっている
type cercles = l:list_notover cercle{(length l <= 8)/\ (notOverlap (getListCerclePosition l)) /\ colorTwiceSetingU (getListCercleColor l)}
assume val get_cercles: unit -> l:cercles{(notOverlap l) /\ (length l = 8) /\ (colorTwiceSetingS (getListCercleColor l))}


//その位置のブロックを取得する mem po (getListBlockPosition bl)によって、リストの中に要素が含まれていることが既知である。
val getBlockFromPosition: po:block_position->bl:list block{~(Nil? bl) /\ mem po (getListBlockPosition bl)} -> block
let rec getBlockFromPosition po bl = 
    match bl with
        | hd::tl -> if (Block?.pos hd) = po then hd else getBlockFromPosition po tl



///removeLemma
val removeBlocksLemma1: b:block -> bl:list block -> Lemma(requires(notOverlap (getListBlockPosition bl)))(ensures(notOverlap (getListBlockPosition (memRemove b bl))))[SMTPat(notOverlap (getListBlockPosition (memRemove b bl)))]
let rec removeBlocksLemma1 b bl = 
    match bl with
    | [] -> ()
    | hd::tl ->removeBlocksLemma1 b tl

val removeBlocksLemma2: bl:list block -> b:block -> col:color -> n:nat -> Lemma(requires(memCountColor (getListBlockColor bl) col <= n))(ensures(memCountColor (memRemove (Block?.col b) (getListBlockColor bl)) col <= n))
let rec removeBlocksLemma2 bl b col n = 
    match bl with
    | [] -> ()
    | hd::tl -> removeBlocksLemma2 tl b col n

val removeBlocksLemma3: bl:list block -> b:block -> col:color -> Lemma(requires(memCountColor (getListBlockColor bl) col <= 2))(ensures(memCountColor (getListBlockColor (memRemove b bl)) col <= 2)) [SMTPat(memCountColor (getListBlockColor (memRemove b bl)) col)]
let rec removeBlocksLemma3 bl b col = 
    match bl with
    | [] -> ()
    | hd::tl -> removeBlocksLemma2 tl b col 2;removeBlocksLemma3 tl b col

val removeCerclesLemma1: c:cercle -> cl:list cercle -> Lemma(requires(notOverlap (getListCerclePosition cl)))(ensures(notOverlap (getListCerclePosition (memRemove c cl))))[SMTPat(notOverlap (getListCerclePosition (memRemove c cl)))]
let rec removeCerclesLemma1 c cl = 
    match cl with
    | [] -> ()
    | hd::tl ->removeCerclesLemma1 c tl

val removeCerclesLemma2: cl:list cercle -> c:cercle -> col:color -> n:nat -> Lemma(requires(memCountColor (getListCercleColor cl) col <= n))(ensures(memCountColor (memRemove (Cercle?.col c) (getListCercleColor cl)) col <= n))
let rec removeCerclesLemma2 cl c col n = 
    match cl with
    | [] -> ()
    | hd::tl -> removeCerclesLemma2 tl c col n

val removeCerclesLemma3: cl:list cercle -> c:cercle -> col:color -> Lemma(requires(memCountColor (getListCercleColor cl) col <= 2))(ensures(memCountColor (getListCercleColor (memRemove c cl)) col <= 2)) [SMTPat(memCountColor (getListCercleColor (memRemove c cl)) col)]
let rec removeCerclesLemma3 cl c col = 
    match cl with
    | [] -> ()
    | hd::tl -> removeCerclesLemma2 tl c col 2; removeCerclesLemma3 tl c col

//remove
val removeBlocks: bl:blocks{notOverlap bl} -> b:block{mem b bl} -> l:blocks{(notOverlap l) /\(length bl = length l + 1)/\(forall i. mem i l ==> mem i bl)/\(not(mem b l))}
let removeBlocks bl b = memRemove b bl 

val removeCercles: cl:cercles{notOverlap cl} -> c:cercle{mem c cl} -> l:cercles{(notOverlap l)/\(length cl = length l + 1)/\(forall i. mem i l ==> mem i cl)/\(not(mem c l))}
let removeCercles cl c = memRemove c cl 
