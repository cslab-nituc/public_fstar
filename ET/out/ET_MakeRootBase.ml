open Prims
let (direction_all : ET_Base.direction Prims.list) =
  [ET_Base.Direction ((Prims.of_int (-1)), Prims.int_zero);
  ET_Base.Direction (Prims.int_zero, (Prims.of_int (-1)));
  ET_Base.Direction (Prims.int_one, Prims.int_zero);
  ET_Base.Direction (Prims.int_zero, Prims.int_one)]
type supportDirection =
  | SDirection of ET_Base.direction_range * ET_Base.direction_range 
let (uu___is_SDirection : supportDirection -> Prims.bool) =
  fun projectee -> true
let (__proj__SDirection__item__x :
  supportDirection -> ET_Base.direction_range) =
  fun projectee -> match projectee with | SDirection (x, y) -> x
let (__proj__SDirection__item__y :
  supportDirection -> ET_Base.direction_range) =
  fun projectee -> match projectee with | SDirection (x, y) -> y
let (compare_direction : supportDirection -> ET_Base.direction -> Prims.bool)
  =
  fun t ->
    fun d ->
      if
        ((__proj__SDirection__item__x t) = Prims.int_zero) &&
          ((__proj__SDirection__item__y t) = Prims.int_zero)
      then true
      else
        if
          ((__proj__SDirection__item__x t) =
             (ET_Base.__proj__Direction__item__x d))
            ||
            ((__proj__SDirection__item__x t) =
               (ET_Base.__proj__Direction__item__y d))
        then false
        else true
let (getAllDirectionWithoutA :
  supportDirection -> ET_Base.direction Prims.list) =
  fun a ->
    let l = direction_all in
    ET_OtherBase.memRemoveAllMeetFuncList (compare_direction a) l
let (checkRemoveDirectionList :
  supportDirection -> ET_Base.direction Prims.list -> Prims.bool) =
  fun kp -> fun l -> ET_OtherBase.memAllMeetFuncList (compare_direction kp) l
let (calcSupportDirection :
  supportDirection -> ET_Base.direction -> supportDirection) =
  fun s ->
    fun d ->
      let x =
        ET_OtherBase.mod2Calc (__proj__SDirection__item__x s)
          (- (ET_Base.__proj__Direction__item__x d)) in
      let y =
        ET_OtherBase.mod2Calc (__proj__SDirection__item__y s)
          (- (ET_Base.__proj__Direction__item__y d)) in
      SDirection (x, y)
let (check_movementxy :
  ET_Base.field_position -> ET_Base.field_position -> Prims.bool) =
  fun x ->
    fun y ->
      let xs =
        (ET_Base.__proj__XYPosition__item__x Prims.int_zero
           (Prims.of_int (3)) Prims.int_zero (Prims.of_int (3)) y)
          -
          (ET_Base.__proj__XYPosition__item__x Prims.int_zero
             (Prims.of_int (3)) Prims.int_zero (Prims.of_int (3)) x) in
      let ys =
        (ET_Base.__proj__XYPosition__item__y Prims.int_zero
           (Prims.of_int (3)) Prims.int_zero (Prims.of_int (3)) y)
          -
          (ET_Base.__proj__XYPosition__item__y Prims.int_zero
             (Prims.of_int (3)) Prims.int_zero (Prims.of_int (3)) x) in
      if
        (((xs + ys) <= Prims.int_one) && ((xs + ys) >= (Prims.of_int (-1))))
          && (Prims.op_Negation ((xs + ys) = Prims.int_zero))
      then true
      else false
let rec (check_movement : ET_Base.set_field -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | s::[] -> true
    | hd1::hd2::tl ->
        (check_movementxy hd2 hd1) && (check_movement (hd2 :: tl))
type ('sl, 'rl) root_nb = ET_Base.set_field
type ('sl, 'rl) root_b = ET_Base.set_field
type ('sl, 'rp) rr = ET_Base.field_position ET_Base.list_notover
type ('sl, 'rl) root_bs = (unit, unit) root_b
type ('sl, 'rl, 'rp) root_s = (unit, unit) root_bs
let (rpchecksum :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position -> (unit, unit) root_nb -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun rp ->
        fun root ->
          match root with | [] -> true | hd::tl -> check_movementxy rp hd
let rec (allSetFirstSetting :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit) root_bs ET_Base.list_notover -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      fun rp ->
        fun l ->
          match l with
          | [] -> true
          | hd::tl ->
              ((ET_OtherBase.thhd hd) = rp) &&
                (allSetFirstSetting uu___ uu___1 rp tl)
let rec (findRootToListAll :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit) root_nb ->
          ET_Base.field_position -> (unit, unit) root_bs ET_Base.list_notover)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun root ->
          fun rp ->
            if ET_OtherBase.mem rp l
            then []
            else
              (let nl = rp :: l in
               if Prims.op_Negation (ET_OtherBase.mem rp rl)
               then
                 (if ET_OtherBase.mem rp sl
                  then [rp :: root]
                  else
                    findRootToListAllSupport sl nl rl (rp :: root) rp
                      direction_all)
               else [])
and (findRootToListAllSupport :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.set_field ->
        (unit, unit) root_nb ->
          ET_Base.field_position ->
            ET_Base.direction Prims.list ->
              (unit, unit) root_bs ET_Base.list_notover)
  =
  fun sl ->
    fun l ->
      fun rl ->
        fun root ->
          fun rp ->
            fun dl ->
              match dl with
              | [] -> []
              | hd::tl ->
                  let x =
                    (ET_Base.__proj__XYPosition__item__x Prims.int_zero
                       (Prims.of_int (3)) Prims.int_zero (Prims.of_int (3))
                       rp)
                      + (ET_Base.__proj__Direction__item__x hd) in
                  let y =
                    (ET_Base.__proj__XYPosition__item__y Prims.int_zero
                       (Prims.of_int (3)) Prims.int_zero (Prims.of_int (3))
                       rp)
                      + (ET_Base.__proj__Direction__item__y hd) in
                  if
                    (((x >= Prims.int_zero) && (x <= (Prims.of_int (3)))) &&
                       (y >= Prims.int_zero))
                      && (y <= (Prims.of_int (3)))
                  then
                    let nrp = ET_Base.XYPosition (x, y) in
                    ET_OtherBase.appendNotOverlap
                      (findRootToListAll sl l rl root nrp)
                      (findRootToListAllSupport sl l rl root rp tl)
                  else findRootToListAllSupport sl l rl root rp tl
type ('sl, 'rl, 'frp, 'rp) root_xs = (unit, unit, unit) root_s
let rec (getBestRootFromRp :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        ET_Base.robot_position ->
          (unit, unit, unit, unit) root_xs ET_Base.list_notover ->
            (unit, unit, unit, unit) root_xs)
  =
  fun sl ->
    fun rl ->
      fun frp ->
        fun rp ->
          fun l ->
            match l with
            | x::[] -> x
            | hd::tl ->
                let v = getBestRootFromRp sl rl frp rp tl in
                if (ET_OtherBase.length hd) < (ET_OtherBase.length v)
                then hd
                else v
type ('sl, 'rl, 'frp) getbestrootkeeps =
  | GetBestRootKeeps of ET_Base.field_position * (unit, unit, unit, unit)
  root_xs ET_Base.list_notover 
let (uu___is_GetBestRootKeeps :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) getbestrootkeeps -> Prims.bool)
  = fun sl -> fun rl -> fun frp -> fun projectee -> true
let (__proj__GetBestRootKeeps__item__rp :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) getbestrootkeeps -> ET_Base.field_position)
  =
  fun sl ->
    fun rl ->
      fun frp ->
        fun projectee ->
          match projectee with | GetBestRootKeeps (rp, root) -> rp
let (__proj__GetBestRootKeeps__item__root :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) getbestrootkeeps ->
          (unit, unit, unit, unit) root_xs ET_Base.list_notover)
  =
  fun sl ->
    fun rl ->
      fun frp ->
        fun projectee ->
          match projectee with | GetBestRootKeeps (rp, root) -> root
type ('sl, 'rl, 'frp) getbestrootkeepslist =
  (unit, unit, unit) getbestrootkeeps ET_Base.list_notover
let rec (appendDivedeRoot :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) getbestrootkeepslist ->
          ET_Base.field_position ->
            (unit, unit, unit, unit) root_xs ->
              (unit, unit, unit) getbestrootkeepslist)
  =
  fun sl ->
    fun rl ->
      fun frp ->
        fun l ->
          fun rp ->
            fun v ->
              match l with
              | [] -> []
              | hd::tl ->
                  if rp = (__proj__GetBestRootKeeps__item__rp sl rl frp hd)
                  then
                    (GetBestRootKeeps
                       ((__proj__GetBestRootKeeps__item__rp sl rl frp hd),
                         (ET_OtherBase.appendNotOverlap [v]
                            (__proj__GetBestRootKeeps__item__root sl rl frp
                               hd))))
                    :: (appendDivedeRoot sl rl frp tl rp v)
                  else hd :: (appendDivedeRoot sl rl frp tl rp v)
let rec (divideRoot :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) root_s ET_Base.list_notover ->
          (unit, unit, unit) getbestrootkeepslist)
  =
  fun sl ->
    fun rl ->
      fun frp ->
        fun l ->
          match l with
          | [] -> []
          | hd::tl ->
              let v = divideRoot sl rl frp tl in
              if
                ET_OtherBase.mem (Prims.__proj__Cons__item__hd hd)
                  (ET_OtherBase.map
                     (__proj__GetBestRootKeeps__item__rp sl rl frp) v)
              then
                appendDivedeRoot sl rl frp v
                  (Prims.__proj__Cons__item__hd hd) hd
              else
                (GetBestRootKeeps ((Prims.__proj__Cons__item__hd hd), [hd]))
                :: v
let rec (appendDivedeRootBase :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) getbestrootkeepslist ->
          (unit, unit, unit) root_s ET_Base.list_notover)
  =
  fun sl ->
    fun rl ->
      fun frp ->
        fun l ->
          match l with
          | [] -> []
          | hd::tl ->
              (getBestRootFromRp sl rl frp
                 (__proj__GetBestRootKeeps__item__rp sl rl frp hd)
                 (__proj__GetBestRootKeeps__item__root sl rl frp hd))
              :: (appendDivedeRootBase sl rl frp tl)
let (getBestRootFromRoots :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) root_s ET_Base.list_notover ->
          (unit, unit, unit) root_s ET_Base.list_notover)
  =
  fun sl ->
    fun rl ->
      fun frp ->
        fun l ->
          let v = divideRoot sl rl frp l in appendDivedeRootBase sl rl frp v
let rec (asSetR1 :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit) root_bs ET_Base.list_notover ->
          (unit, unit, unit) root_s ET_Base.list_notover)
  =
  fun uu___ ->
    fun uu___1 ->
      fun rp ->
        fun l ->
          match l with
          | [] -> []
          | hd::tl -> hd :: (asSetR1 uu___ uu___1 rp tl)
let (findRootToList :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) root_s ET_Base.list_notover)
  =
  fun sl ->
    fun rl ->
      fun rp ->
        getBestRootFromRoots sl rl rp
          (asSetR1 sl rl rp (findRootToListAll sl [] rl [] rp))