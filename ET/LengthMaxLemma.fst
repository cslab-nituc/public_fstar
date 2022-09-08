module LengthMaxLemma

open FStar.Seq
open FStar.Ref
open FStar.Mul

open ET_OtherBase
open ET_Base

//ここから
val length_f: (#a:nat) -> (#b:nat{a<=b}) -> x:(finites a b) -> l:list (finites a b) -> k:nat{k <= (x - a + 1)}
let rec length_f #a #b x l = 
  if a < x then 
    if mem x l then length_f (x-1) l + 1
    else length_f (x-1) l
  else 
    if mem x l then 1
    else 0

val length_f_lemma: (#a:nat) -> (#b:nat{a<=b}) -> x:(finites a b) -> l:list (finites a b) -> Lemma((forall (i:(finites a b){i<=x}). mem i l)<==>(length_f x l = x - a + 1))
let rec length_f_lemma #a #b x l = if a < x then length_f_lemma (x-1) l else ()

val length_f_lemmab: (#a:nat) -> (#b:nat{a<=b}) -> l:list (finites a b) -> Lemma((forall i. mem i l)<==>(length_f b l = b - a + 1))
let length_f_lemmab #a #b l = length_f_lemma b l

//val checks31: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b -> Lemma(length_f #a #b x [a] = 1)
//let rec checks31 #a #b x = if a < x then checks31 #a #b (x-1) else () 

//length_f #a #b b [x] = 1
val length_f_xy0: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b -> y:finites a b -> Lemma(requires(x<y))(ensures(length_f #a #b x [y] = 0))
let rec length_f_xy0 #a #b x y = if a < x then length_f_xy0 #a #b (x-1) y else () 

val length_f_xy1: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b -> y:finites a b -> Lemma(requires(x=y))(ensures(length_f #a #b x [y] = 1))
let length_f_xy1 #a #b x y = if a < x then length_f_xy0 #a #b (x-1) y else () 

val length_f_xy2: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b -> Lemma(length_f #a #b x [x] = 1)
let length_f_xy2 #a #b x = let _ = length_f_xy1 x x in ()

val length_f_xy3: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b -> y:finites a b->  Lemma(requires(x>=y))(ensures(length_f #a #b x [y] = 1))
let rec length_f_xy3 #a #b x y = if x > y then length_f_xy3 (x-1) y else length_f_xy1 x y 

val onelemma_lengthf: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b ->  Lemma(ensures(length_f #a #b b [x] = 1))
let onelemma_lengthf #a #b x = length_f_xy3 b x

//length_f #a #b b [] = 0
val length_f_empty_xy0: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b -> Lemma(length_f #a #b x [] = 0)
let rec length_f_empty_xy0 #a #b x = if a < x then length_f_empty_xy0 #a #b (x-1)else () 

val zerolemma_lengthf: a:nat -> b:nat{a<=b} ->  Lemma(ensures(length_f #a #b b [] = 0))
let zerolemma_lengthf a b = length_f_empty_xy0 #a #b b

//今のところ必要なし？
val meml01: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b -> hd:finites a b -> tl:list (finites a b) -> Lemma(requires(x < hd))(ensures(mem x (hd::tl) = mem x tl))
let meml01 x hd tl = ()

val meml02: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b -> hd:finites a b -> tl:list (finites a b) -> Lemma(requires(x > hd))(ensures(mem x (hd::tl) = mem x tl))
let meml02 x hd tl = ()

val checks38: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b ->  hd:finites a b -> tl:list (finites a b) ->  Lemma(requires((notOverlap tl) /\ (x < hd)))(ensures(length_f #a #b x (hd::tl) = length_f #a #b x tl)) 
let rec checks38 #a #b x hd tl = if a < x then checks38 #a #b (x-1) hd tl else ()

//val checks39: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b-> hd:finites a b -> tl:list (finites a b) ->  Lemma(requires((notOverlap tl) /\ (x = hd)))(ensures(length_f #a #b x (hd::tl) = length_f #a #b x tl)) //[SMTPat(length_f #a #b b (hd::tl))]
//let rec checks39 #a #b x hd tl = ()//if a < x then checks39 #a #b (x-1) hd tl else ()

//val checks3a: (#a:nat) -> (#b:nat{a<=b}) -> x:finites a b ->  hd:finites a b -> tl:list (finites a b) ->  Lemma(requires((notOverlap tl) /\ (x > hd)))(ensures(length_f #a #b x (hd::tl) = length_f #a #b x tl)) //[SMTPat(length_f #a #b b (hd::tl))]
//let rec checks3a #a #b x hd tl = if a < x then checks3a #a #b (x-1) hd tl else ()

//必要補題
assume val length_f_devision_lemma: (#a:nat) -> (#b:nat{a<=b}) -> hd:finites a b -> tl:list (finites a b) ->  Lemma(requires(notOverlap tl))(ensures(length_f #a #b b (hd::tl) = length_f #a #b b [hd] + length_f #a #b b tl))// [SMTPat(length_f #a #b b (hd::tl))]


val length_equal_lemma: (#a:nat) -> (#b:nat{a<=b}) -> l:list (finites a b) -> Lemma(requires(notOverlap l))(ensures(length l = length_f b l))
let rec length_equal_lemma #a #b l = match l with 
  | [] -> zerolemma_lengthf a b
  | hd::tl -> let _ = length_f_devision_lemma hd tl in let _ = onelemma_lengthf hd in length_equal_lemma #a #b tl


val finitesLemma: (#a:nat) -> (#b:nat{a<=b}) -> l:list (finites a b) -> Lemma(requires(notOverlap l))(ensures((forall i. mem i l)<==>(length l = b - a + 1)))
let finitesLemma #a #b l = let _ = length_f_lemmab l in length_equal_lemma l








val get_valueofrange: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> x:finites a b -> y:finites c d -> n:nat{(1 <= n) /\ (n <= ((b - a + 1) * (d - c + 1)))}
let get_valueofrange #a #b #c #d x y = (d - c + 1)*(x - a) + (y - c + 1)

val get_valueofrangeLennma1: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> x:finites a b -> y:finites c d -> Lemma(requires(x > a))(ensures(get_valueofrange #a #b #c #d (x-1) y < get_valueofrange #a #b #c #d x y))// [SMTPat(get_valueofrange #a #b #c #d x (x-1))]
let get_valueofrangeLennma1 #a #b #c #d x y = ()

val get_valueofrangeLennma2: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> x:finites a b -> y:finites c d -> Lemma(requires(y > c))(ensures(get_valueofrange #a #b #c #d x (y-1) < get_valueofrange #a #b #c #d x y)) //[SMTPat(get_valueofrange #a #b #c #d (y-1) y)]
let get_valueofrangeLennma2 #a #b #c #d x y = ()

val get_valueofrangeLennma3: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> x:finites a b -> y:finites c d -> Lemma(requires((x > a)/\(y > c)))(ensures(get_valueofrange #a #b #c #d (x-1) y < get_valueofrange #a #b #c #d x (y-1))) //[SMTPat(get_valueofrange #a #b #c #d x (y-1)); SMTPat(get_valueofrange #a #b #c #d (x-1) y);]
let get_valueofrangeLennma3 #a #b #c #d x y = ()

val get_valueofrangeposition: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> p:xyposition a b c d -> n:nat{(1 <= n) /\ (n <= ((b - a + 1) * (d - c + 1)))}
let get_valueofrangeposition #a #b #c #d p = get_valueofrange #a #b #c #d (XYPosition?.x p) (XYPosition?.y p)

//val get_valueofrangeLemma1: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> x:finites a b -> y:finites c d -> Lemma(forall (i:(finites a b){not(i=x)}) (j:(finites c d ){not(j=y)}). not(get_valueofrange i j = get_valueofrange x y) )
//let get_valueofrangeLemma1 #a #b #c #d x y = ()

//val get_inverse_valueofrange: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> n:nat{(1 <= n) /\ (n <= ((b - a + 1) * (d - c + 1)))} -> xyposition a b c d 
//let get_inverse_valueofrange #a #b #c #d n = let ans:xyposition a b c d = XYPosition (((n-1) / (d - c + 1)) + a) (((n-1) % (d - c + 1)) + c) in ans

//val get_valueofrangeLemma1: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> p:xyposition a b c d -> Lemma()
//let get_valueofrangeLemma1 #a #b #c #d p = ()

//assume val get_valueofrangeLemma1: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> p:xyposition a b c d -> Lemma(forall (i:(xyposition a b c d){not(i=p)}). not(get_valueofrangeposition i = get_valueofrangeposition p) )
//let get_valueofrangeLemma1 #a #b #c #d p = ()

val makeOverRange: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> l:list (xyposition a b c d) -> list (finites 1 ((b - a + 1)*(d - c + 1)))
let rec makeOverRange #a #b #c #d l = match l with 
    | [] -> []
    | hd::tl -> (get_valueofrangeposition hd)::(makeOverRange #a #b #c #d tl)

assume val makeOverRangeLemma1: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> l:list (xyposition a b c d) -> Lemma(requires(notOverlap l))(ensures(notOverlap (makeOverRange l))) // [SMTPat(notOverlap (makeOverRange l))]
(*
let rec makeOverRangeLemma1 #a #b #c #d l = match l with 
    | [] -> ()
    | hd::tl -> makeOverRangeLemma1 #a #b #c #d tl
*)

val makeOverRangeLemma2: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> l:list (xyposition a b c d) -> Lemma(length (makeOverRange l) = length l)//[SMTPat(length (makeOverRange l))]
let rec makeOverRangeLemma2 #a #b #c #d l = match l with 
    | [] -> ()
    | hd::tl -> makeOverRangeLemma2 #a #b #c #d tl
    
assume val makeOverRangeLemma3: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> l:list (xyposition a b c d) -> Lemma((forall (i:xyposition a b c d). mem i l)<==>(forall (i:finites 1 ((b - a + 1)*(d - c + 1))). mem i (makeOverRange l))) //[SMTPat(mem i (makeOverRange l))]

(*
let rec makeOverRangeLemma3 #a #b #c #d l = match l with 
    | [] -> ()
    | hd::tl -> makeOverRangeLemma3 #a #b #c #d tl

*)
val xypositionLemma: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> l:list (xyposition a b c d) -> Lemma(requires(notOverlap l))(ensures((length l = (b - a + 1)*(d - c + 1)) ==> (forall i. mem i l)))[SMTPat(notOverlap l)]
let xypositionLemma #a #b #c #d l = let _ = makeOverRangeLemma1 l in let _ = makeOverRangeLemma2 l in let gl = makeOverRange l in let _ = makeOverRangeLemma3 l in finitesLemma gl

val xypositionLemma2: (#a:nat) -> (#b:nat{a<=b}) -> (#c:nat) -> (#d:nat{c<=d}) -> l:list (xyposition a b c d){notOverlap l} -> Lemma(length l <= (b - a + 1)*(d - c + 1)) [SMTPat(notOverlap l)]
let rec xypositionLemma2 #a #b #c #d l = match l with
  | [] -> ()
  | hd::tl -> xypositionLemma2 tl