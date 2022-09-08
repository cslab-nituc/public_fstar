open Prims
let (checkHalfWayPoint :
  ET_Base.block -> ET_Base.robot_position -> Prims.bool) =
  fun b -> fun x -> (ET_Base.__proj__Block__item__pos b) = x
type ('bl, 'cl) oneactionmeets =
  | Oneactionmeets of unit ET_MakeRootByBlock.block_sb * (unit, unit)
  ET_MakeRootByCercle.cercle_sc * ET_Base.robot_position * (unit, unit, 
  unit) ET_MakeRootByBlock.block_root * (unit, unit, unit, unit)
  ET_MakeRootByCercle.cercle_root * ET_Base.robot_position *
  ET_Base.robot_position * Prims.nat 
let (uu___is_Oneactionmeets :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) oneactionmeets -> Prims.bool)
  = fun bl -> fun cl -> fun projectee -> true
let (__proj__Oneactionmeets__item__block :
  ET_Base.blocks ->
    ET_Base.cercles ->
      (unit, unit) oneactionmeets -> unit ET_MakeRootByBlock.block_sb)
  =
  fun bl ->
    fun cl ->
      fun projectee ->
        match projectee with
        | Oneactionmeets
            (block, cercle, frp, rootbyblock, rootbycercle, hrp, lrp, dis) ->
            block
let (__proj__Oneactionmeets__item__cercle :
  ET_Base.blocks ->
    ET_Base.cercles ->
      (unit, unit) oneactionmeets ->
        (unit, unit) ET_MakeRootByCercle.cercle_sc)
  =
  fun bl ->
    fun cl ->
      fun projectee ->
        match projectee with
        | Oneactionmeets
            (block, cercle, frp, rootbyblock, rootbycercle, hrp, lrp, dis) ->
            cercle
let (__proj__Oneactionmeets__item__frp :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) oneactionmeets -> ET_Base.robot_position)
  =
  fun bl ->
    fun cl ->
      fun projectee ->
        match projectee with
        | Oneactionmeets
            (block, cercle, frp, rootbyblock, rootbycercle, hrp, lrp, dis) ->
            frp
let (__proj__Oneactionmeets__item__rootbyblock :
  ET_Base.blocks ->
    ET_Base.cercles ->
      (unit, unit) oneactionmeets ->
        (unit, unit, unit) ET_MakeRootByBlock.block_root)
  =
  fun bl ->
    fun cl ->
      fun projectee ->
        match projectee with
        | Oneactionmeets
            (block, cercle, frp, rootbyblock, rootbycercle, hrp, lrp, dis) ->
            rootbyblock
let (__proj__Oneactionmeets__item__rootbycercle :
  ET_Base.blocks ->
    ET_Base.cercles ->
      (unit, unit) oneactionmeets ->
        (unit, unit, unit, unit) ET_MakeRootByCercle.cercle_root)
  =
  fun bl ->
    fun cl ->
      fun projectee ->
        match projectee with
        | Oneactionmeets
            (block, cercle, frp, rootbyblock, rootbycercle, hrp, lrp, dis) ->
            rootbycercle
let (__proj__Oneactionmeets__item__hrp :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) oneactionmeets -> ET_Base.robot_position)
  =
  fun bl ->
    fun cl ->
      fun projectee ->
        match projectee with
        | Oneactionmeets
            (block, cercle, frp, rootbyblock, rootbycercle, hrp, lrp, dis) ->
            hrp
let (__proj__Oneactionmeets__item__lrp :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) oneactionmeets -> ET_Base.robot_position)
  =
  fun bl ->
    fun cl ->
      fun projectee ->
        match projectee with
        | Oneactionmeets
            (block, cercle, frp, rootbyblock, rootbycercle, hrp, lrp, dis) ->
            lrp
let (__proj__Oneactionmeets__item__dis :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) oneactionmeets -> Prims.nat)
  =
  fun bl ->
    fun cl ->
      fun projectee ->
        match projectee with
        | Oneactionmeets
            (block, cercle, frp, rootbyblock, rootbycercle, hrp, lrp, dis) ->
            dis
type ('bbl, 'bcl) eval2 =
  | Eval2 of ET_Base.blocks * ET_Base.cercles * (unit, unit) oneactionmeets *
  ET_Base.block * ET_Base.cercle * (unit, unit) eval2 FStar_ST.ref *
  Prims.nat * Prims.nat 
let (uu___is_Eval2 :
  ET_Base.blocks -> ET_Base.cercles -> (unit, unit) eval2 -> Prims.bool) =
  fun bbl -> fun bcl -> fun projectee -> true
let (__proj__Eval2__item__bl :
  ET_Base.blocks -> ET_Base.cercles -> (unit, unit) eval2 -> ET_Base.blocks)
  =
  fun bbl ->
    fun bcl ->
      fun projectee ->
        match projectee with | Eval2 (bl, cl, a, b, c, n, st, e) -> bl
let (__proj__Eval2__item__cl :
  ET_Base.blocks -> ET_Base.cercles -> (unit, unit) eval2 -> ET_Base.cercles)
  =
  fun bbl ->
    fun bcl ->
      fun projectee ->
        match projectee with | Eval2 (bl, cl, a, b, c, n, st, e) -> cl
let (__proj__Eval2__item__a :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) eval2 -> (unit, unit) oneactionmeets)
  =
  fun bbl ->
    fun bcl ->
      fun projectee ->
        match projectee with | Eval2 (bl, cl, a, b, c, n, st, e) -> a
let (__proj__Eval2__item__b :
  ET_Base.blocks -> ET_Base.cercles -> (unit, unit) eval2 -> ET_Base.block) =
  fun bbl ->
    fun bcl ->
      fun projectee ->
        match projectee with | Eval2 (bl, cl, a, b, c, n, st, e) -> b
let (__proj__Eval2__item__c :
  ET_Base.blocks -> ET_Base.cercles -> (unit, unit) eval2 -> ET_Base.cercle)
  =
  fun bbl ->
    fun bcl ->
      fun projectee ->
        match projectee with | Eval2 (bl, cl, a, b, c, n, st, e) -> c
let (__proj__Eval2__item__n :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) eval2 -> (unit, unit) eval2 FStar_ST.ref)
  =
  fun bbl ->
    fun bcl ->
      fun projectee ->
        match projectee with | Eval2 (bl, cl, a, b, c, n, st, e) -> n
let (__proj__Eval2__item__st :
  ET_Base.blocks -> ET_Base.cercles -> (unit, unit) eval2 -> Prims.nat) =
  fun bbl ->
    fun bcl ->
      fun projectee ->
        match projectee with | Eval2 (bl, cl, a, b, c, n, st, e) -> st
let (__proj__Eval2__item__e :
  ET_Base.blocks -> ET_Base.cercles -> (unit, unit) eval2 -> Prims.nat) =
  fun bbl ->
    fun bcl ->
      fun projectee ->
        match projectee with | Eval2 (bl, cl, a, b, c, n, st, e) -> e
type ('bbl, 'bcl) eval2L =
  | L of (unit, unit) eval2 * (unit, unit) eval2 FStar_ST.ref * (unit, 
  unit) eval2 FStar_ST.ref 
let (uu___is_L :
  ET_Base.blocks -> ET_Base.cercles -> (unit, unit) eval2L -> Prims.bool) =
  fun bbl -> fun bcl -> fun projectee -> true
let (__proj__L__item__e :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) eval2L -> (unit, unit) eval2)
  =
  fun bbl ->
    fun bcl -> fun projectee -> match projectee with | L (e, p, l) -> e
let (__proj__L__item__p :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) eval2L -> (unit, unit) eval2 FStar_ST.ref)
  =
  fun bbl ->
    fun bcl -> fun projectee -> match projectee with | L (e, p, l) -> p
let (__proj__L__item__l :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) eval2L -> (unit, unit) eval2 FStar_ST.ref)
  =
  fun bbl ->
    fun bcl -> fun projectee -> match projectee with | L (e, p, l) -> l
let (makeOneActionMeetsData :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.robot_position ->
        (unit, unit) ET_MakeRootByBlock.block_get ->
          (unit, unit, unit) ET_MakeRootByCercle.cercle_get ->
            (unit, unit) oneactionmeets)
  =
  fun uu___ ->
    fun uu___1 ->
      fun rp ->
        fun bt ->
          fun ct ->
            Oneactionmeets
              ((ET_MakeRootByBlock.__proj__Block_get__item__b rp uu___ bt),
                (ET_MakeRootByCercle.__proj__Cercle_get__item__c
                   (ET_MakeRootByBlock.__proj__Block_get__item__b rp uu___ bt)
                   uu___1
                   (ET_Base.removeBlocks uu___
                      (ET_MakeRootByBlock.__proj__Block_get__item__b rp uu___
                         bt)) ct), rp,
                (ET_MakeRootByBlock.__proj__Block_get__item__r rp uu___ bt),
                (ET_MakeRootByCercle.__proj__Cercle_get__item__r
                   (ET_MakeRootByBlock.__proj__Block_get__item__b rp uu___ bt)
                   uu___1
                   (ET_Base.removeBlocks uu___
                      (ET_MakeRootByBlock.__proj__Block_get__item__b rp uu___
                         bt)) ct),
                (Prims.__proj__Cons__item__hd
                   (ET_MakeRootByBlock.__proj__Block_get__item__r rp uu___ bt)),
                (Prims.__proj__Cons__item__hd
                   (ET_MakeRootByCercle.__proj__Cercle_get__item__r
                      (ET_MakeRootByBlock.__proj__Block_get__item__b rp uu___
                         bt) uu___1
                      (ET_Base.removeBlocks uu___
                         (ET_MakeRootByBlock.__proj__Block_get__item__b rp
                            uu___ bt)) ct)),
                (((ET_OtherBase.length
                     (ET_MakeRootByBlock.__proj__Block_get__item__r rp uu___
                        bt))
                    +
                    (ET_OtherBase.length
                       (ET_MakeRootByCercle.__proj__Cercle_get__item__r
                          (ET_MakeRootByBlock.__proj__Block_get__item__b rp
                             uu___ bt) uu___1
                          (ET_Base.removeBlocks uu___
                             (ET_MakeRootByBlock.__proj__Block_get__item__b
                                rp uu___ bt)) ct)))
                   - Prims.int_one))
let rec (makeOneActionFromBlockToCercle :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.robot_position ->
        (unit, unit) ET_MakeRootByBlock.block_get ->
          (unit, unit, unit) ET_MakeRootByCercle.cercles_get ->
            (unit, unit) oneactionmeets Prims.list)
  =
  fun uu___ ->
    fun uu___1 ->
      fun rp ->
        fun bt ->
          fun ctl ->
            match ctl with
            | [] -> []
            | hd::tl -> (makeOneActionMeetsData uu___ uu___1 rp bt hd) ::
                (makeOneActionFromBlockToCercle uu___ uu___1 rp bt tl)
let rec (getOneActionFromBlockToCercleSupport :
  ET_Base.cercles ->
    ET_Base.blocks ->
      ET_Base.robot_position ->
        (unit, unit) ET_MakeRootByBlock.block_get ->
          ET_Base.cercles -> (unit, unit) oneactionmeets Prims.list)
  =
  fun cl ->
    fun bl ->
      fun rp ->
        fun bt ->
          fun cls ->
            match cls with
            | [] -> []
            | hd::tl ->
                let v =
                  ET_MakeRootByCercle.getBestRootByCercles2 cl bl
                    (ET_MakeRootByBlock.__proj__Block_get__item__b rp bl bt)
                    hd
                    (ET_Base.__proj__Block__item__pos
                       (ET_MakeRootByBlock.__proj__Block_get__item__b rp bl
                          bt)) in
                ET_OtherBase.append
                  (makeOneActionFromBlockToCercle bl cl rp bt v)
                  (getOneActionFromBlockToCercleSupport cl bl rp bt tl)

let rec (getBlockColorToCercleSupport :
  ET_Base.cercles -> ET_Base.cercles -> ET_Base.block -> ET_Base.cercles) =
  fun cl ->
    fun cls ->
      fun b ->
        match cls with
        | [] -> cl
        | hd::tl ->
            let v = getBlockColorToCercleSupport cl tl b in
            if
              Prims.op_Negation
                ((ET_Base.__proj__Cercle__item__col hd) =
                   (ET_Base.__proj__Block__item__col b))
            then ET_OtherBase.memRemove hd v
            else v
let (getBlockColorToCercle :
  ET_Base.cercles -> ET_Base.block -> ET_Base.cercles) =
  fun cl -> fun b -> let v = getBlockColorToCercleSupport cl cl b in v
let (getOneActionFromBlockToCercle :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.robot_position ->
        (unit, unit) ET_MakeRootByBlock.block_get ->
          (unit, unit) oneactionmeets Prims.list)
  =
  fun bl ->
    fun cl ->
      fun rp ->
        fun bt ->
          let cls =
            getBlockColorToCercle cl
              (ET_MakeRootByBlock.__proj__Block_get__item__b rp bl bt) in
          getOneActionFromBlockToCercleSupport cl bl rp bt cls
let rec (getOneActionSupport :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.robot_position ->
        (unit, unit) ET_MakeRootByBlock.blocks_get ->
          (unit, unit) oneactionmeets Prims.list)
  =
  fun bl ->
    fun cl ->
      fun rp ->
        fun btl ->
          match btl with
          | [] -> []
          | hd::tl ->
              ET_OtherBase.append (getOneActionFromBlockToCercle bl cl rp hd)
                (getOneActionSupport bl cl rp tl)
let (getOneAction :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.robot_position -> (unit, unit) oneactionmeets Prims.list)
  =
  fun bl ->
    fun cl ->
      fun rp ->
        let v = ET_MakeRootByBlock.getBestRootByBlocks2 bl rp in
        getOneActionSupport bl cl rp v
let (makeEval :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.blocks ->
        ET_Base.cercles ->
          (unit, unit) eval2 FStar_ST.ref ->
            (unit, unit) oneactionmeets -> (unit, unit) eval2)
  =
  fun bbl ->
    fun bcl ->
      fun bl ->
        fun cl ->
          fun n ->
            fun a ->
              Eval2
                (bl, cl, a, (__proj__Oneactionmeets__item__block bl cl a),
                  (__proj__Oneactionmeets__item__cercle bl cl a), n,
                  Prims.int_zero, (Prims.of_int (9)))