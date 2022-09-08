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
type eval =
  | Eval of ET_Base.oneaction * Prims.nat * eval Prims.list * Prims.nat 
let (uu___is_Eval : eval -> Prims.bool) = fun projectee -> true
let (__proj__Eval__item__a : eval -> ET_Base.oneaction) =
  fun projectee -> match projectee with | Eval (a, b, n, e) -> a
let (__proj__Eval__item__b : eval -> Prims.nat) =
  fun projectee -> match projectee with | Eval (a, b, n, e) -> b
let (__proj__Eval__item__n : eval -> eval Prims.list) =
  fun projectee -> match projectee with | Eval (a, b, n, e) -> n
let (__proj__Eval__item__e : eval -> Prims.nat) =
  fun projectee -> match projectee with | Eval (a, b, n, e) -> e
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
let (makeOneActionDataFromMeetsData :
  ET_Base.blocks ->
    ET_Base.cercles -> (unit, unit) oneactionmeets -> ET_Base.oneaction)
  =
  fun bl ->
    fun cl ->
      fun v ->
        ET_Base.Oneaction
          ((__proj__Oneactionmeets__item__block bl cl v),
            (__proj__Oneactionmeets__item__cercle bl cl v),
            (__proj__Oneactionmeets__item__frp bl cl v),
            (__proj__Oneactionmeets__item__rootbyblock bl cl v),
            (__proj__Oneactionmeets__item__rootbycercle bl cl v),
            (__proj__Oneactionmeets__item__hrp bl cl v),
            (__proj__Oneactionmeets__item__lrp bl cl v),
            (__proj__Oneactionmeets__item__dis bl cl v))
let (makeOneAction :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.robot_position ->
        (unit, unit) ET_MakeRootByBlock.block_get ->
          (unit, unit, unit) ET_MakeRootByCercle.cercle_get ->
            ET_Base.oneaction)
  =
  fun uu___ ->
    fun uu___1 ->
      fun rp ->
        fun bt ->
          fun ct ->
            let v = makeOneActionMeetsData uu___ uu___1 rp bt ct in
            makeOneActionDataFromMeetsData uu___ uu___1 v
let rec (makeOneActionFromBlockToCercle :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.robot_position ->
        (unit, unit) ET_MakeRootByBlock.block_get ->
          (unit, unit, unit) ET_MakeRootByCercle.cercles_get ->
            ET_Base.oneaction Prims.list)
  =
  fun uu___ ->
    fun uu___1 ->
      fun rp ->
        fun bt ->
          fun ctl ->
            match ctl with
            | [] -> []
            | hd::tl -> (makeOneAction uu___ uu___1 rp bt hd) ::
                (makeOneActionFromBlockToCercle uu___ uu___1 rp bt tl)
let rec (getOneActionFromBlockToCercleSupport :
  ET_Base.cercles ->
    ET_Base.blocks ->
      ET_Base.robot_position ->
        (unit, unit) ET_MakeRootByBlock.block_get ->
          ET_Base.cercles -> ET_Base.oneaction Prims.list)
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
          ET_Base.oneaction Prims.list)
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
          ET_Base.oneaction Prims.list)
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
    ET_Base.cercles -> ET_Base.robot_position -> ET_Base.oneaction Prims.list)
  =
  fun bl ->
    fun cl ->
      fun rp ->
        let v = ET_MakeRootByBlock.getBestRootByBlocks2 bl rp in
        getOneActionSupport bl cl rp v
let (makeEval : ET_Base.oneaction -> Prims.nat -> eval Prims.list -> eval) =
  fun a ->
    fun b ->
      fun n -> Eval (a, b, n, (ET_Base.__proj__Oneaction__item__dis a))
let rec (getAction :
  ET_Base.blocks ->
    ET_Base.cercles -> ET_Base.robot_position -> Prims.nat -> eval Prims.list)
  =
  fun bl ->
    fun cl ->
      fun rp ->
        fun n ->
          match bl with
          | [] -> []
          | hd::tl ->
              let v = getOneAction bl cl rp in getActionSupport bl cl v rp n
and (getActionSupport :
  ET_Base.blocks ->
    ET_Base.cercles ->
      ET_Base.oneaction Prims.list ->
        ET_Base.robot_position -> Prims.nat -> eval Prims.list)
  =
  fun bl ->
    fun cl ->
      fun l ->
        fun rp ->
          fun n ->
            match l with
            | [] -> []
            | hd::tl ->
                let nbl =
                  ET_Base.removeBlocks bl
                    (ET_Base.__proj__Oneaction__item__block hd) in
                let ncl =
                  ET_Base.removeCercles cl
                    (ET_Base.__proj__Oneaction__item__cercle hd) in
                let v =
                  getAction nbl ncl
                    (ET_Base.__proj__Oneaction__item__lrpos hd)
                    (n + Prims.int_one) in
                let s = makeEval hd n v in s ::
                  (getActionSupport bl cl tl rp n)
let (getActionAll : ET_Base.blocks -> ET_Base.cercles -> eval Prims.list) =
  fun bl ->
    fun cl -> getAction bl cl ET_Base.first_robot_position Prims.int_zero
type evls =
  | Evls of Prims.nat * eval Prims.list 
let (uu___is_Evls : evls -> Prims.bool) = fun projectee -> true
let (__proj__Evls__item__h : evls -> Prims.nat) =
  fun projectee -> match projectee with | Evls (h, el) -> h
let (__proj__Evls__item__el : evls -> eval Prims.list) =
  fun projectee -> match projectee with | Evls (h, el) -> el
let rec (getBestEval : eval Prims.list -> evls) =
  fun l ->
    match l with
    | [] -> Evls (Prims.int_zero, [])
    | hd::tl ->
        let v = getBestEval tl in
        let s = getBestEval (__proj__Eval__item__n hd) in
        if (__proj__Evls__item__h v) = Prims.int_zero
        then
          Evls
            (((__proj__Eval__item__e hd) + (__proj__Evls__item__h s)), (hd ::
              (__proj__Evls__item__el s)))
        else
          if
            ((__proj__Eval__item__e hd) + (__proj__Evls__item__h s)) <
              (__proj__Evls__item__h v)
          then
            Evls
              (((__proj__Eval__item__e hd) + (__proj__Evls__item__h s)), (hd
                :: (__proj__Evls__item__el s)))
          else v