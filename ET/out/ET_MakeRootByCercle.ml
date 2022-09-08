open Prims
type cercle_direction_support = Prims.int
type supportCercleDirection =
  | SCDirection of cercle_direction_support * cercle_direction_support 
let (uu___is_SCDirection : supportCercleDirection -> Prims.bool) =
  fun projectee -> true
let (__proj__SCDirection__item__x :
  supportCercleDirection -> cercle_direction_support) =
  fun projectee -> match projectee with | SCDirection (x, y) -> x
let (__proj__SCDirection__item__y :
  supportCercleDirection -> cercle_direction_support) =
  fun projectee -> match projectee with | SCDirection (x, y) -> y
let (cercle_direction_all : supportCercleDirection ET_Base.list_notover) =
  [SCDirection ((Prims.of_int (-1)), (Prims.of_int (-1)));
  SCDirection ((Prims.of_int (-1)), Prims.int_zero);
  SCDirection (Prims.int_zero, (Prims.of_int (-1)));
  SCDirection (Prims.int_zero, Prims.int_zero)]
let rec (checkFinishPointSuuport :
  supportCercleDirection ET_Base.list_notover ->
    ET_Base.cercle -> ET_Base.robot_position -> Prims.bool)
  =
  fun dl ->
    fun c ->
      fun rp ->
        match dl with
        | [] -> false
        | hd::tl ->
            let pos = ET_Base.__proj__Cercle__item__pos c in
            let x =
              (ET_Base.__proj__XYPosition__item__x Prims.int_one
                 (Prims.of_int (3)) Prims.int_one (Prims.of_int (3)) pos)
                + (__proj__SCDirection__item__x hd) in
            let y =
              (ET_Base.__proj__XYPosition__item__y Prims.int_one
                 (Prims.of_int (3)) Prims.int_one (Prims.of_int (3)) pos)
                + (__proj__SCDirection__item__y hd) in
            let v = ET_Base.XYPosition (x, y) in
            (rp = v) || (checkFinishPointSuuport tl c rp)
let (checkFinishPoint :
  ET_Base.cercle -> ET_Base.robot_position -> Prims.bool) =
  fun c -> fun x -> checkFinishPointSuuport cercle_direction_all c x
let rec (getCercleToBlockPositionSupport :
  ET_Base.cercle ->
    supportCercleDirection ET_Base.list_notover -> ET_Base.set_field)
  =
  fun c ->
    fun dl ->
      match dl with
      | [] -> []
      | hd::tl ->
          let pos = ET_Base.__proj__Cercle__item__pos c in
          let x =
            (ET_Base.__proj__XYPosition__item__x Prims.int_one
               (Prims.of_int (3)) Prims.int_one (Prims.of_int (3)) pos)
              + (__proj__SCDirection__item__x hd) in
          let y =
            (ET_Base.__proj__XYPosition__item__y Prims.int_one
               (Prims.of_int (3)) Prims.int_one (Prims.of_int (3)) pos)
              + (__proj__SCDirection__item__y hd) in
          let v = ET_Base.XYPosition (x, y) in v ::
            (getCercleToBlockPositionSupport c tl)
let (getCercleToBlockPosition : ET_Base.cercle -> ET_Base.set_field) =
  fun c -> getCercleToBlockPositionSupport c cercle_direction_all
type ('b, 'cl) cercle_sc = ET_Base.cercle
type ('b, 'cl) cercles_sc = (unit, unit) cercle_sc ET_Base.list_notover
type ('b, 'cl, 'c, 'bl) cercle_root =
  (unit, unit, unit) ET_MakeRootBase.root_s
type ('b, 'cl, 'bl) cercle_get =
  | Cercle_get of (unit, unit) cercle_sc * (unit, unit, unit, unit)
  cercle_root 
let (uu___is_Cercle_get :
  ET_Base.block ->
    ET_Base.cercles ->
      ET_Base.blocks -> (unit, unit, unit) cercle_get -> Prims.bool)
  = fun b -> fun cl -> fun bl -> fun projectee -> true
let (__proj__Cercle_get__item__c :
  ET_Base.block ->
    ET_Base.cercles ->
      ET_Base.blocks ->
        (unit, unit, unit) cercle_get -> (unit, unit) cercle_sc)
  =
  fun b ->
    fun cl ->
      fun bl ->
        fun projectee -> match projectee with | Cercle_get (c, r) -> c
let (__proj__Cercle_get__item__r :
  ET_Base.block ->
    ET_Base.cercles ->
      ET_Base.blocks ->
        (unit, unit, unit) cercle_get -> (unit, unit, unit, unit) cercle_root)
  =
  fun b ->
    fun cl ->
      fun bl ->
        fun projectee -> match projectee with | Cercle_get (c, r) -> r
type ('b, 'cl, 'bl) cercles_get =
  (unit, unit, unit) cercle_get ET_Base.list_notover
let (getCerclesRoot1 :
  ET_Base.block ->
    ET_Base.cercles ->
      ET_Base.blocks ->
        (unit, unit) cercle_sc ->
          ET_Base.robot_position ->
            (unit, unit, unit, unit) cercle_root ET_Base.list_notover)
  =
  fun uu___ ->
    fun uu___1 ->
      fun bl ->
        fun c ->
          fun rp ->
            ET_MakeRootBase.findRootToList (getCercleToBlockPosition c)
              (ET_Base.getListBlockPosition bl) rp
let (getCerclesRoot2 :
  ET_Base.block ->
    ET_Base.cercles ->
      ET_Base.blocks ->
        (unit, unit) cercle_sc ->
          ET_Base.robot_position ->
            (unit, unit, unit, unit) cercle_root ET_Base.list_notover)
  =
  fun uu___ ->
    fun uu___1 ->
      fun bl ->
        fun c ->
          fun rp ->
            ET_MakeRootBase2.findRootToList2 (getCercleToBlockPosition c)
              (ET_Base.getListBlockPosition bl) rp
let rec (getCercleRootToTuple2 :
  ET_Base.block ->
    ET_Base.cercles ->
      ET_Base.blocks ->
        (unit, unit) cercle_sc ->
          (unit, unit, unit, unit) cercle_root ET_Base.list_notover ->
            (unit, unit, unit) cercles_get)
  =
  fun bl ->
    fun cl ->
      fun uu___ ->
        fun c ->
          fun l ->
            match l with
            | [] -> []
            | hd::tl -> (Cercle_get (c, hd)) ::
                (getCercleRootToTuple2 bl cl uu___ c tl)
let rec (removeCercleBestRootFromRoots :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.field_position ->
        (unit, unit, unit) ET_MakeRootBase.root_s ET_Base.list_notover ->
          (unit, unit, unit) ET_MakeRootBase.root_s)
  =
  fun sl ->
    fun rl ->
      fun frp ->
        fun l ->
          match l with
          | x::[] -> x
          | hd::tl ->
              let v = removeCercleBestRootFromRoots sl rl frp tl in
              if (ET_OtherBase.length hd) < (ET_OtherBase.length v)
              then hd
              else v

let (getBestRootByCercles1 :
  ET_Base.cercles ->
    ET_Base.blocks ->
      ET_Base.block ->
        (unit, unit) cercle_sc ->
          ET_Base.robot_position -> (unit, unit, unit) cercles_get)
  =
  fun cl ->
    fun bl ->
      fun b ->
        fun c ->
          fun rp ->
            let v = getCerclesRoot1 b cl (ET_Base.removeBlocks bl b) c rp in
            if Prims.uu___is_Nil v
            then []
            else
              (let s =
                 removeCercleBestRootFromRoots (getCercleToBlockPosition c)
                   (ET_Base.getListBlockPosition (ET_Base.removeBlocks bl b))
                   (ET_Base.__proj__Block__item__pos b) v in
               getCercleRootToTuple2 b cl (ET_Base.removeBlocks bl b) c [s])
let (getBestRootByCercles2 :
  ET_Base.cercles ->
    ET_Base.blocks ->
      ET_Base.block ->
        (unit, unit) cercle_sc ->
          ET_Base.robot_position -> (unit, unit, unit) cercles_get)
  =
  fun cl ->
    fun bl ->
      fun b ->
        fun c ->
          fun rp ->
            let v = getCerclesRoot2 b cl (ET_Base.removeBlocks bl b) c rp in
            if Prims.uu___is_Nil v
            then []
            else
              (let s =
                 removeCercleBestRootFromRoots (getCercleToBlockPosition c)
                   (ET_Base.getListBlockPosition (ET_Base.removeBlocks bl b))
                   (ET_Base.__proj__Block__item__pos b) v in
               getCercleRootToTuple2 b cl (ET_Base.removeBlocks bl b) c [s])