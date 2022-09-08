open Prims
type nat = Prims.int
let rec append : 'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun l1 ->
    fun l2 -> match l1 with | [] -> l2 | hd::tl -> hd :: (append tl l2)
let rec length : 'a . 'a Prims.list -> nat =
  fun l ->
    match l with
    | [] -> Prims.int_zero
    | uu___::tl -> Prims.int_one + (length tl)
let rec mem : 't . 't -> 't Prims.list -> Prims.bool =
  fun a ->
    fun l -> match l with | [] -> false | hd::tl -> (hd = a) || (mem a tl)


let rec memSubset : 't . 't Prims.list -> 't Prims.list -> Prims.bool =
  fun l1 ->
    fun l2 ->
      match l1 with | [] -> true | hd::tl -> (mem hd l2) && (memSubset tl l2)
let rec notOverlap : 'uuuuu . 'uuuuu Prims.list -> Prims.bool =
  fun l ->
    match l with
    | [] -> true
    | hd::tl -> (Prims.op_Negation (mem hd tl)) && (notOverlap tl)
let rec chengeNotOverlap : 'uuuuu . 'uuuuu Prims.list -> 'uuuuu Prims.list =
  fun l ->
    match l with
    | [] -> []
    | hd::tl ->
        let value = chengeNotOverlap tl in
        if Prims.op_Negation (mem hd value) then hd :: value else value

let rec appendNotOverlap :
  'uuuuu . 'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list =
  fun l1 ->
    fun l2 ->
      match l1 with
      | [] -> l2
      | hd::tl ->
          let v = appendNotOverlap tl l2 in
          if Prims.op_Negation (mem hd v) then hd :: v else v



let rec filter : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> []
      | hd::tl -> if f hd then hd :: (filter f tl) else filter f tl


let rec map : 't 'a . ('t -> 'a) -> 't Prims.list -> 'a Prims.list =
  fun f -> fun l -> match l with | [] -> [] | hd::tl -> (f hd) :: (map f tl)

let cC : 't 'a . ('a -> Prims.bool) -> ('t -> 'a) -> 't -> Prims.bool =
  fun fb -> fun f -> fun uu___ -> let x = uu___ in fb (f x)



let removefilter : 't . 't -> 't -> Prims.bool =
  fun x -> fun uu___ -> let s = uu___ in Prims.op_Negation (s = x)




let memRemove : 't . 't -> 't Prims.list -> 't Prims.list =
  fun x -> fun l -> filter (removefilter x) l





let rec notOverlaplists :
  'uuuuu . 'uuuuu Prims.list -> 'uuuuu Prims.list -> Prims.bool =
  fun l1 ->
    fun l2 ->
      match l1 with
      | [] -> true
      | hd::tl -> (Prims.op_Negation (mem hd l2)) && (notOverlaplists tl l2)

let notOverlaplistsoftl :
  'uuuuu . 'uuuuu Prims.list -> 'uuuuu Prims.list -> Prims.bool =
  fun l1 ->
    fun l2 ->
      match l1 with
      | [] -> true
      | hd::tl -> (mem hd l2) && (notOverlaplists tl l2)


let rec memAllMeetFuncList :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> true
      | hd::tl -> if f hd then memAllMeetFuncList f tl else false
let rec memRemoveAllMeetFuncList :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd::tl ->
          if f hd
          then hd :: (memRemoveAllMeetFuncList f tl)
          else memRemoveAllMeetFuncList f tl
let (mod2Calc : Prims.int -> Prims.int -> Prims.int) =
  fun i ->
    fun j ->
      if (i + j) >= (Prims.of_int (2))
      then Prims.int_one
      else
        if (i + j) <= (Prims.of_int (-2)) then (Prims.of_int (-1)) else i + j
let rec (allStateTrue : Prims.bool Prims.list -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | hd::tl -> (Prims.op_Negation hd) && (allStateTrue tl)
let rec allMemF :
  'uuuuu . 'uuuuu Prims.list -> ('uuuuu -> Prims.bool) -> Prims.bool =
  fun l ->
    fun f -> match l with | [] -> true | hd::tl -> (f hd) && (allMemF tl f)
let rec thhd : 'uuuuu . 'uuuuu Prims.list -> 'uuuuu =
  fun l -> match l with | x::[] -> x | hd::tl -> thhd tl
let rec memCount : 'uuuuu . 'uuuuu Prims.list -> 'uuuuu -> nat =
  fun l ->
    fun m ->
      match l with
      | [] -> Prims.int_zero
      | hd::tl ->
          if hd = m then Prims.int_one + (memCount tl m) else memCount tl m




let rec (bf : nat -> nat) =
  fun a ->
    if a > Prims.int_zero
    then a * (bf (a - Prims.int_one))
    else Prims.int_one