module ET_OtherBase
open FStar.Mul

type nat = n:int{n>=0}

//リストを追加
val append: list 'a -> list 'a -> list 'a
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

//配列の長さを求める
val length: list 'a -> nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

//要素がリストに含まれる
val mem: #t:eqtype -> t -> list t -> bool
let rec mem #t a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

val appendLemma1: #t:eqtype -> l1:list t -> l2:list t -> Lemma(length l1 + length l2 = length (append l1 l2)) [SMTPat(append l1 l2)]
let rec appendLemma1 #t l1 l2 = 
  match l1 with
    | [] -> ()
    | hd :: tl -> appendLemma1 #t tl l2

val appendLemma2: #t:eqtype -> l1:list t -> l2:list t -> Lemma(forall i. mem i (append l1 l2) = (mem i l1 || mem i l2 )) [SMTPat(append l1 l2)]
let rec appendLemma2 #t l1 l2 = 
  match l1 with
    | [] -> ()
    | hd :: tl -> appendLemma2 #t tl l2

//要素が部分集合であるか判定する l1 <- l2
val memSubset: #t:eqtype -> l1:list t -> l2:list t -> bool
let rec memSubset #t l1 l2 = match l1 with
  | [] -> true
  | hd::tl -> (mem hd l2) && (memSubset tl l2)

//リストの要素に重なりがない
val notOverlap:  #t:eqtype -> list t -> bool
let rec notOverlap l = match l with
    | [] -> true
    | hd::tl -> (not (mem hd tl)) && notOverlap tl

//リストの被りをなくす
val chengeNotOverlap: #t:eqtype -> list t -> l:list t{ notOverlap l}
let rec chengeNotOverlap l = match l with
  | [] -> []
  | hd::tl -> let value = chengeNotOverlap tl in if not(mem hd value) then hd::value else value

//リストのメンバーの変化なし
val chengeNotOverlapLemma1: #t:eqtype -> l:list t -> Lemma(forall i. mem i l = mem i (chengeNotOverlap l)) [SMTPat(chengeNotOverlap l)]
let rec chengeNotOverlapLemma1 l = match l with
  | [] -> ()
  | hd::tl -> chengeNotOverlapLemma1 tl

//リスト被りなく追加
val appendNotOverlap: #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{notOverlap l2} -> l:list t{notOverlap l}
let rec appendNotOverlap l1 l2 = 
  match l1 with 
  | [] -> l2
  | hd::tl -> 
      let v = appendNotOverlap tl l2 in
        if not(mem hd v) then hd::v else v 

////リストのメンバーの変化なし
val appendNotOverlapLemma1: #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{notOverlap l2} -> Lemma(forall i. mem i (append l1 l2) = mem i (appendNotOverlap l1 l2)) [SMTPat(appendNotOverlap l1 l2)]
let rec appendNotOverlapLemma1 l1 l2 = 
  match l1 with
  | [] -> ()
  | hd::tl -> appendNotOverlapLemma1 tl l2

////リストのメンバーの変化なし
val appendNotOverlapLemma2: #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{notOverlap l2} -> Lemma(forall i. mem i (appendNotOverlap l1 l2) ==> (mem i l1) \/ (mem i l2)) [SMTPat(appendNotOverlap l1 l2)]
let rec appendNotOverlapLemma2 l1 l2 = 
  match l1 with
  | [] -> ()
  | hd::tl -> appendNotOverlapLemma2 tl l2

val appendNotOverlapLemma3 : #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{notOverlap l2} -> Lemma((forall i. mem i l1 ==>  mem i (appendNotOverlap l1 l2))/\(forall i. mem i l2 ==> mem i (appendNotOverlap l1 l2))) [SMTPat(appendNotOverlap l1 l2)]
let rec appendNotOverlapLemma3 l1 l2 = 
  match l1 with
  | [] -> ()
  | hd::tl -> appendNotOverlapLemma3 tl l2

//filter
val filter : #a:eqtype -> f:(a -> Tot bool) -> l: list a -> Tot (m:list a{(forall x. mem x m ==> mem x l)/\(forall i. mem i m ==> f i)})
let rec filter #a f = function
  | [] -> []
  | hd::tl -> if f hd then hd::filter f tl else filter f tl

val filterLemma1: #t:eqtype -> l:list t -> f:(t -> Tot bool)-> Lemma(requires(notOverlap l))(ensures(notOverlap (filter f l))) [SMTPat(filter f l)]
let rec filterLemma1 l f = 
        match l with
        | [] -> ()
        | hd::tl -> 
            filterLemma1 tl f

val filterLemma2 : #t:eqtype -> f:(t -> Tot bool) -> l:list t -> Lemma(length l >= (length (filter f l))) [SMTPat(filter f l)]
let rec filterLemma2 #t x l =
  match l with
  | [] -> ()
  | hd::tl -> filterLemma2 x tl

//map
val map: #t:eqtype -> #a:eqtype -> f:(t -> Tot a) -> l:list t -> Tot (v:list a{forall i. mem i l ==> mem (f i) v})
let rec map #t #a f l = match l with
  | [] -> []
  | hd::tl -> (f hd)::map f tl

//filterが常にnotOvrlapであることの証明
val filterLemma3:#t:eqtype -> l:list t -> fb:(t -> bool) -> Lemma(requires(notOverlap l))(ensures(notOverlap (filter fb l))) [SMTPat(filter fb l)]
let rec filterLemma3 #t l fb = 
    match l with
    | [] -> ()
    | hd::tl ->filterLemma3 #t tl fb

//t -> boolの関数を a->boolに移し替える
val cC: #t:eqtype -> #a:eqtype -> fb:(a -> bool) -> (f:t -> a) -> (fr:t -> bool)
let cC #t #a fb f = (function (x:t) -> fb (f x))

//filterとmapのLennma　（notOverlapについて）
val filterMapLemma1:#t:eqtype -> #a:eqtype -> l:list t -> fb:(a -> bool) -> f:(t -> a) -> Lemma(requires(notOverlap (map f l)))(ensures(notOverlap (filter fb (map f l)))) [SMTPat(filter fb (map f l))]
let filterMapLemma1 #t #a l fb f = ()

val filterMapLemma2: #t:eqtype -> #a:eqtype -> l:list t -> fb:(a -> bool) -> f:(t -> a) -> Lemma(filter fb (map f l) = map f (filter (cC fb f) l)) [SMTPat(filter (cC fb f) l)]
let rec filterMapLemma2 l fb f = 
    match l with
    | [] -> ()
    | hd::tl -> filterMapLemma2 tl fb f

val filterMapLemma3:#t:eqtype -> #a:eqtype -> l:list t -> fb:(a -> bool) -> f:(t -> a) -> Lemma(requires(notOverlap (map f l)))(ensures(notOverlap (map f (filter (cC fb f) l)))) [SMTPat(map f (filter (cC fb f) l))]
let filterMapLemma3 #t #a l fb f = ()

//removeするためのfilter
val removefilter: #t:eqtype -> x:t -> (t -> bool)
let removefilter (#t:eqtype) (x:t) = (function (s:t) -> not(s = x))

//forall x. (cC (removefilter (f x)) f) x = removefilter xの証明
val removefilterLemma1: #t:eqtype -> #a:eqtype -> x:t -> f:(t->a) -> Lemma(requires(forall (i:t) (j:t). not(i = j) <==> not(f i = f j)))(ensures(forall (i:t). ((removefilter x) i)  = (cC (removefilter (f x)) f) i)) [SMTPat(cC (removefilter (f x)) f)]
let removefilterLemma1 x f = ()

//この補題は難しいためassumeしておく f:(t->a)が単射である時の性質を利用するから (f:t->a)は常に単射の性質を持つと仮定
assume val flem: #t:eqtype -> #a:eqtype -> f:(t->a) -> Lemma(forall (i:t) (j:t). not(i = j) <==> not(f i = f j))
//let flem f = ()

val filterMapLemma4:#t:eqtype -> #a:eqtype -> x:t -> l:list t -> f:(t -> a) -> Lemma(requires(notOverlap (map f l)))(ensures(notOverlap (map f (filter (cC (removefilter (f x)) f) l)))) [SMTPat(map f (filter (cC (removefilter (f x)) f) l))]
let filterMapLemma4 #t #a x l f = ()

//filterがremovefilterを引数に持つときの補題
val filterMapLemma5:#t:eqtype -> #a:eqtype -> x:t -> l:list t -> f:(t -> a) -> Lemma(filter (removefilter x) l = filter (cC (removefilter (f x)) f) l)// [SMTPat(filter (cC (removefilter (f x)) f) l)]
let rec filterMapLemma5 x l f = 
  flem f;
  match l with
  | [] -> ()
  | hd::tl -> filterMapLemma5 x tl f

//最終的な補題　（注意：この関数ではfが単射でなくともこの性質を満たす）
val filterMapLemma6:#t:eqtype -> #a:eqtype -> x:t -> l:list t -> f:(t -> a) -> Lemma(requires(notOverlap (map f l)))(ensures(notOverlap (map f (filter (removefilter x) l)))) [SMTPat(map f (filter (removefilter x) l))]
let filterMapLemma6 #t #a x l f = flem f;filterMapLemma5 x l f

//要素を削除する関数
val memRemove : #t:eqtype -> x:t -> l:list t -> Tot (m:list t{(forall i. mem i m ==> mem i l)/\(forall i. mem i m ==> (not(x = i)))})
let memRemove #t x l = filter (removefilter x) l  

//削除後の要素にいない
val memRemoveLemma1 : #a:eqtype -> x:a -> l:list a ->  Lemma(requires(mem x l)) (ensures(not(mem x (memRemove x l)))) [SMTPat(memRemove x l)]
let memRemoveLemma1 #a x l = ()

//被りがない
val memRemoveLemma2 : #a:eqtype -> x:a -> l:list a ->  Lemma(requires(notOverlap l))(ensures((notOverlap (memRemove x l )))) [SMTPat(memRemove x l)]
let memRemoveLemma2 x l = ()

//長さが１つも減らない not(mem x l)の時
val memRemoveLemma3 : #t:eqtype -> x:t -> l:list t ->  Lemma(requires(not(mem x l)))(ensures(length l = (length (memRemove x l)))) [SMTPat(memRemove x l)]
let rec memRemoveLemma3 #t x l = 
  match l with 
  | [] -> ()
  | hd::tl -> memRemoveLemma3 x tl

//長さが１減る notOverlap かつ mem x lの時
val memRemoveLemma4 : #t:eqtype -> x:t -> l:list t -> Lemma(requires((notOverlap l)/\(mem x l)))(ensures(length l = length (memRemove x l) + 1)) [SMTPat(memRemove x l)]
let rec memRemoveLemma4 #t x l = 
  match l with 
  | [] -> ()
  | hd::tl -> 
    if hd = x then let _ = assert(not(mem hd tl)) in memRemoveLemma3 x tl 
    else memRemoveLemma4 x tl

//f:(t->a)によって移されても成り立つ notOverlapが成り立つ。
val memRemoveLemma5 : #t:eqtype -> #a:eqtype -> x:t -> l:list t -> f:(t -> a) ->Lemma(requires((notOverlap (map f l))))(ensures(notOverlap (map f (memRemove x l)))) [SMTPat(map f (memRemove x l))]
let rec memRemoveLemma5 #t #a x l f = 
  match l with
  | [] -> ()
  | hd::tl -> memRemoveLemma5 #t #a x tl f 

(*
//特定の要素のみを取得する関数
val getMeml: #t:eqtype -> #a:eqtype -> x:a -> l:list t -> f:(t -> a) -> Tot (m:list t{(forall i. mem i m ==> mem i l)/\(forall i. mem i m ==> (x = f i))})
let getMeml #t #a x l f = filter (cC (function (h:a) -> h=x) f) l  

//削除後の要素にいない
val getMemlLemma1 : #t:eqtype -> #a:eqtype -> x:a -> l:list t -> f:(t -> a) -> Lemma(requires(notOverlap l)) (ensures(notOverlap (getMeml x l f)))// [SMTPat(memRemove x l)]
let rec getMemlLemma1 #a x l f = 
  match l with
  | [] -> ()
  | hd::tl -> getMemlLemma1 #a x tl f
*)

//２つのリストの要素に重なりがない
val notOverlaplists:  #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{notOverlap l2} -> bool
let rec notOverlaplists l1 l2 = match l1 with
    | [] -> true
    | hd::tl -> (not (mem hd l2)) && notOverlaplists tl l2

val notOverlaplistsLemma1: #t:eqtype -> l1:list t{notOverlap l1} ->Lemma(notOverlaplists l1 []) [SMTPat (notOverlaplists l1 [])]
let rec notOverlaplistsLemma1 l1 = match l1 with 
  | [] -> ()
  | hd::tl -> notOverlaplistsLemma1 tl

//先頭以外のリストが要素に被りがない判定をする
val notOverlaplistsoftl: #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{notOverlap l2} -> bool
let notOverlaplistsoftl l1 l2 = match l1 with 
    | [] -> true
    | hd::tl -> (mem hd l2) && (notOverlaplists tl l2)

val notOverlaplistsoftlLemma2: #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{(notOverlap l2)/\(notOverlaplists l1 l2)} -> Lemma(forall i. mem i l1 ==> not(mem i l2))
let rec notOverlaplistsoftlLemma2 #t l1 l2 = match l1 with 
    | [] -> ()
    | hd::tl -> notOverlaplistsoftlLemma2 #t tl l2

val notOverlaplistsoftlLemma1: #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{(notOverlap l2)/\(notOverlaplistsoftl l2 l1)/\(length l2 > 0)} -> Lemma(mem (Cons?.hd l2) l1) [SMTPat(mem (Cons?.hd l2) l1)]
let notOverlaplistsoftlLemma1 #t l1 l2 = ()

//リストから条件を全て満たすかチェックする
val memAllMeetFuncList: #a:Type ->  f:(a -> bool) -> list a -> bool
let rec memAllMeetFuncList #a f l= 
    match l with
    | [] -> true
    | hd::tl -> if f hd then memAllMeetFuncList #a f tl else false

//リストから条件を満たすもの以外は除外する
val memRemoveAllMeetFuncList: #a:Type ->  f:(a -> bool) -> list a -> list a
let rec memRemoveAllMeetFuncList #a f l= 
    match l with
    | [] -> []
    | hd::tl -> if f hd then hd::memRemoveAllMeetFuncList #a f tl else memRemoveAllMeetFuncList #a f tl 

//mod2の足し算 (マイナス含む)
val mod2Calc: i:int{(i>=(-1)) /\ (i<=1)}->j:int{(j>=(-1)) /\ (j<=1)}->n:int{(n>=(-1)) /\ (n<=1)}
let mod2Calc i j = 
    if i + j >= 2 then 1
    else if i + j <= -2 then -1  else i + j

//stateの計算
val allStateTrue: l:list bool -> bool
let rec allStateTrue l = 
    match l with
      | [] -> true
      | hd::tl -> not(hd) && (allStateTrue tl)

//全ての要素で成り立つか判定
val allMemF: #t:eqtype -> l:list t -> f:(t -> bool) -> bool
let rec allMemF l f = 
  match l with
  | [] -> true
  | hd::tl -> (f hd) && (allMemF tl f)

//最後の要素のみを返す
val thhd: #t:eqtype -> l:list t{length l > 0} -> t
let rec thhd l 
    = match l with
    | [x] -> x
    | hd::tl -> thhd tl


//要素を数える
val memCount: #t:eqtype -> list t -> t -> nat
let rec memCount l m = 
    match l with
        | [] -> 0
        | hd::tl -> if hd=m then 1 + memCount tl m else memCount tl m

val memCountLemma1: #t:eqtype ->  l:list t -> m:t -> x:t -> Lemma(memCount l m >= memCount (memRemove x l) m) [SMTPat(memCount (memRemove x l) m)]
let rec memCountLemma1 l m x = 
    match l with
    | [] -> ()
    | hd::tl -> memCountLemma1 tl m x 

val memCountLemma2: #t:eqtype -> #a:eqtype -> x:t -> l:list t -> f:(t->a)-> Lemma(memRemove (f x) (map f l) = map f (memRemove x l)) [SMTPat(memRemove (f x) (map f l))]
let rec memCountLemma2 x l f =
    flem f;
    match l with
    | [] -> ()
    | hd::tl -> memCountLemma2 x tl f


val appnedNotOverlapLemma3: #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{notOverlap l2} -> Lemma(requires(notOverlaplists l1 l2))(ensures(appendNotOverlap l1 l2 = append l1 l2)) [SMTPat(appendNotOverlap l1 l2); SMTPat(append l1 l2)]
let rec appnedNotOverlapLemma3 #t l1 l2 = 
    match l1 with
    | [] -> ()
    | hd::tl -> appnedNotOverlapLemma3 #t tl l2

val appnedNotOverlapLemma4: #t:eqtype -> l1:list t{notOverlap l1} -> l2:list t{notOverlap l2} -> Lemma(requires(notOverlaplists l1 l2))(ensures(length (appendNotOverlap l1 l2) = length l1 + length l2)) [SMTPat(appendNotOverlap l1 l2)]
let appnedNotOverlapLemma4 #t l1 l2 = ()

val bf: nat -> nat
let rec bf a = 
    if a > 0 then a * ( bf (a-1) )
    else 1