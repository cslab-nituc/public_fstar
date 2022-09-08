open Prims
type ('sl, 'rl) getfield =
  | GetField of (unit, unit) ET_MakeRootBase.root_nb * ET_Base.field_position 
let (uu___is_GetField :
  ET_Base.set_field ->
    ET_Base.set_field -> (unit, unit) getfield -> Prims.bool)
  = fun sl -> fun rl -> fun projectee -> true
let (__proj__GetField__item__r :
  ET_Base.set_field ->
    ET_Base.set_field ->
      (unit, unit) getfield -> (unit, unit) ET_MakeRootBase.root_nb)
  =
  fun sl ->
    fun rl -> fun projectee -> match projectee with | GetField (r, p) -> r
let (__proj__GetField__item__p :
  ET_Base.set_field ->
    ET_Base.set_field -> (unit, unit) getfield -> ET_Base.field_position)
  =
  fun sl ->
    fun rl -> fun projectee -> match projectee with | GetField (r, p) -> p
type ('sl, 'rl, 'l) ex_root = (unit, unit) ET_MakeRootBase.root_nb
type ('sl, 'rl, 'l) getfield_notl = (unit, unit) getfield
type ('sl, 'rl, 'l) getfield_notl_s =
  (unit, unit, unit) getfield_notl ET_Base.list_notover
type ('sl, 'rl, 'l) getfield_insl_notl = (unit, unit, unit) getfield_notl
type ('sl, 'rl, 'l) getfield_insl_notl_s =
  (unit, unit, unit) getfield_insl_notl ET_Base.list_notover
type ('sl, 'rl, 'l) getfield_ninsl_notl = (unit, unit, unit) getfield_notl
type ('sl, 'rl, 'l) getfield_ninsl_notl_s =
  (unit, unit, unit) getfield_ninsl_notl ET_Base.list_notover
let rec (getColseMatrixOverlapSupport :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) ex_root ->
          ET_Base.direction Prims.list -> (unit, unit, unit) getfield_notl_s)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun root ->
          fun dl ->
            match dl with
            | [] -> []
            | hd::tl ->
                let x =
                  (ET_Base.__proj__XYPosition__item__x Prims.int_zero
                     (Prims.of_int (3)) Prims.int_zero (Prims.of_int (3))
                     (Prims.__proj__Cons__item__hd root))
                    + (ET_Base.__proj__Direction__item__x hd) in
                let y =
                  (ET_Base.__proj__XYPosition__item__y Prims.int_zero
                     (Prims.of_int (3)) Prims.int_zero (Prims.of_int (3))
                     (Prims.__proj__Cons__item__hd root))
                    + (ET_Base.__proj__Direction__item__y hd) in
                if
                  (((x >= Prims.int_zero) && (x <= (Prims.of_int (3)))) &&
                     (y >= Prims.int_zero))
                    && (y <= (Prims.of_int (3)))
                then
                  let v = ET_Base.XYPosition (x, y) in
                  (if
                     (Prims.op_Negation (ET_OtherBase.mem v l)) &&
                       (Prims.op_Negation (ET_OtherBase.mem v rl))
                   then (GetField (root, v)) ::
                     (getColseMatrixOverlapSupport sl l rl root tl)
                   else getColseMatrixOverlapSupport sl l rl root tl)
                else getColseMatrixOverlapSupport sl l rl root tl
let (getColseMatrixOverlap :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) ex_root -> (unit, unit, unit) getfield_notl_s)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun root ->
          getColseMatrixOverlapSupport sl l rl root
            ET_MakeRootBase.direction_all

let rec (appendNotOverlapMatrix :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_notl_s ->
          (unit, unit, unit) getfield_notl_s ->
            (unit, unit, unit) getfield_notl_s)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun l1 ->
          fun l2 ->
            match l1 with
            | [] -> l2
            | hd::tl ->
                let v = appendNotOverlapMatrix sl l rl tl l2 in
                if
                  Prims.op_Negation
                    (ET_OtherBase.mem (__proj__GetField__item__p sl rl hd)
                       (ET_OtherBase.map (__proj__GetField__item__p sl rl) v))
                then hd :: v
                else v
let rec (getCloseMatrix :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) ex_root Prims.list ->
          (unit, unit, unit) getfield_notl_s)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun nl ->
          match nl with
          | [] -> []
          | hd::tl ->
              let v = getColseMatrixOverlap sl l rl hd in
              appendNotOverlapMatrix sl l rl v (getCloseMatrix sl l rl tl)

type ('sl, 'l, 'rl, 'pl) getfield_insl_notl_ssupport =
  (unit, unit, unit) getfield_insl_notl_s
type ('sl, 'l, 'rl, 'pl) getfield_ninsl_notl_ssupport =
  (unit, unit, unit) getfield_ninsl_notl_s
type ('sl, 'l, 'rl, 'pl) getfield_notl_tupple =
  | Getfield_Notl_Tupple of (unit, unit, unit, unit)
  getfield_insl_notl_ssupport * (unit, unit, unit, unit)
  getfield_ninsl_notl_ssupport 
let (uu___is_Getfield_Notl_Tupple :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_notl_s ->
          (unit, unit, unit, unit) getfield_notl_tupple -> Prims.bool)
  = fun sl -> fun l -> fun rl -> fun pl -> fun projectee -> true
let (__proj__Getfield_Notl_Tupple__item__insl :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_notl_s ->
          (unit, unit, unit, unit) getfield_notl_tupple ->
            (unit, unit, unit, unit) getfield_insl_notl_ssupport)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun pl ->
          fun projectee ->
            match projectee with | Getfield_Notl_Tupple (insl, ninsl) -> insl
let (__proj__Getfield_Notl_Tupple__item__ninsl :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_notl_s ->
          (unit, unit, unit, unit) getfield_notl_tupple ->
            (unit, unit, unit, unit) getfield_ninsl_notl_ssupport)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun pl ->
          fun projectee ->
            match projectee with
            | Getfield_Notl_Tupple (insl, ninsl) -> ninsl
let rec (getRootsBaseSupport :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_notl_s ->
          (unit, unit, unit) getfield_notl_s ->
            (unit, unit, unit, unit) getfield_notl_tupple)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun pl ->
          fun pls ->
            match pls with
            | [] -> Getfield_Notl_Tupple ([], [])
            | hd::tl ->
                let v = getRootsBaseSupport sl l rl pl tl in
                if ET_OtherBase.mem (__proj__GetField__item__p sl rl hd) sl
                then
                  Getfield_Notl_Tupple
                    ((hd ::
                      (__proj__Getfield_Notl_Tupple__item__insl sl l rl pl v)),
                      (__proj__Getfield_Notl_Tupple__item__ninsl sl l rl pl v))
                else
                  Getfield_Notl_Tupple
                    ((__proj__Getfield_Notl_Tupple__item__insl sl l rl pl v),
                      (hd ::
                      (__proj__Getfield_Notl_Tupple__item__ninsl sl l rl pl v)))
let (getRootsBase :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_notl_s ->
          (unit, unit, unit, unit) getfield_notl_tupple)
  = fun sl -> fun l -> fun rl -> fun pl -> getRootsBaseSupport sl l rl pl pl


let rec (getNextRoot :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_notl_s ->
          (unit, unit, unit) getfield_ninsl_notl_s ->
            (unit, unit, unit) ex_root Prims.list)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun pl ->
          fun pls ->
            match pls with
            | [] -> []
            | hd::tl ->
                let s = (__proj__GetField__item__p sl rl hd) ::
                  (__proj__GetField__item__r sl rl hd) in
                s :: (getNextRoot sl l rl pl tl)
let rec (getRootsbList :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_insl_notl_s ->
          (unit, unit) ET_MakeRootBase.root_bs ET_Base.list_notover)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun pl ->
          match pl with
          | [] -> []
          | hd::tl ->
              let v = getRootsbList sl l rl tl in
              let s = (__proj__GetField__item__p sl rl hd) ::
                (__proj__GetField__item__r sl rl hd) in
              s :: v
let rec (appendNotOverlapPl :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit) ET_MakeRootBase.root_bs ET_Base.list_notover ->
          (unit, unit) ET_MakeRootBase.root_bs ET_Base.list_notover ->
            (unit, unit) ET_MakeRootBase.root_bs ET_Base.list_notover)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun l1 ->
          fun l2 ->
            match l1 with
            | [] -> l2
            | hd::tl ->
                let v = appendNotOverlapPl sl l rl tl l2 in
                if
                  Prims.op_Negation
                    (ET_OtherBase.mem (Prims.__proj__Cons__item__hd hd)
                       (ET_OtherBase.map Prims.__proj__Cons__item__hd v))
                then hd :: v
                else v
let rec (getRoots :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit, unit) getfield_notl_s ->
          (unit, unit) ET_MakeRootBase.root_bs ET_Base.list_notover)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun pl ->
          match pl with
          | [] -> []
          | hd::tl ->
              let v = getRootsBase sl l rl pl in
              let nl =
                ET_OtherBase.appendNotOverlap
                  (ET_OtherBase.map (__proj__GetField__item__p sl rl) pl) l in
              let ng =
                getNextRoot sl l rl pl
                  (__proj__Getfield_Notl_Tupple__item__ninsl sl l rl pl v) in
              let b = getCloseMatrix sl nl rl ng in
              let s = getRoots sl nl rl b in
              appendNotOverlapPl sl nl rl
                (getRootsbList sl l rl
                   (__proj__Getfield_Notl_Tupple__item__insl sl l rl pl v)) s
let (getfr :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position -> (unit, unit, unit) getfield_notl_s)
  = fun uu___ -> fun uu___1 -> fun rp -> [GetField ([], rp)]
let rec (asSetR2 :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit) ET_MakeRootBase.root_bs ET_Base.list_notover ->
          (unit, unit, unit) ET_MakeRootBase.root_s ET_Base.list_notover)
  =
  fun uu___ ->
    fun uu___1 ->
      fun rp ->
        fun l ->
          match l with
          | [] -> []
          | hd::tl -> hd :: (asSetR2 uu___ uu___1 rp tl)
let (findRootToList2 :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) ET_MakeRootBase.root_s ET_Base.list_notover)
  =
  fun sl ->
    fun rl -> fun rp -> asSetR2 sl rl rp (getRoots sl [] rl (getfr sl rl rp))