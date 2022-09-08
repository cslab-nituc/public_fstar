open Prims
type 'bl block_sb = ET_Base.block
type ('rp, 'bl) block_root_s = (unit, unit, unit) ET_MakeRootBase.root_s
type ('b, 'rp, 'bl) block_root = (unit, unit) block_root_s
type ('rp, 'bl) block_get =
  | Block_get of unit block_sb * (unit, unit, unit) block_root 
let (uu___is_Block_get :
  ET_Base.field_position ->
    ET_Base.blocks -> (unit, unit) block_get -> Prims.bool)
  = fun rp -> fun bl -> fun projectee -> true
let (__proj__Block_get__item__b :
  ET_Base.field_position ->
    ET_Base.blocks -> (unit, unit) block_get -> unit block_sb)
  =
  fun rp ->
    fun bl -> fun projectee -> match projectee with | Block_get (b, r) -> b
let (__proj__Block_get__item__r :
  ET_Base.field_position ->
    ET_Base.blocks -> (unit, unit) block_get -> (unit, unit, unit) block_root)
  =
  fun rp ->
    fun bl -> fun projectee -> match projectee with | Block_get (b, r) -> r
type ('rp, 'bl) blocks_get = (unit, unit) block_get ET_Base.list_notover
let rec (findBlocks :
  ET_Base.blocks -> ET_Base.field_position -> ET_Base.block) =
  fun bl ->
    fun rp ->
      match bl with
      | hd::tl ->
          if (ET_Base.__proj__Block__item__pos hd) = rp
          then hd
          else findBlocks tl rp
let (getBlocksRoot1 :
  ET_Base.field_position ->
    ET_Base.blocks ->
      ET_Base.robot_position ->
        (unit, unit) block_root_s ET_Base.list_notover)
  =
  fun uu___ ->
    fun bl ->
      fun rp ->
        ET_MakeRootBase.findRootToList (ET_Base.getListBlockPosition bl) []
          rp
let (getBlocksRoot2 :
  ET_Base.field_position ->
    ET_Base.blocks ->
      ET_Base.robot_position ->
        (unit, unit) block_root_s ET_Base.list_notover)
  =
  fun uu___ ->
    fun bl ->
      fun rp ->
        ET_MakeRootBase2.findRootToList2 (ET_Base.getListBlockPosition bl) []
          rp


let rec (getBlocksRootToTuple2 :
  ET_Base.field_position ->
    ET_Base.blocks ->
      (unit, unit) block_root_s ET_Base.list_notover ->
        (unit, unit) blocks_get)
  =
  fun rp ->
    fun bl ->
      fun l ->
        match l with
        | [] -> []
        | hd::tl ->
            let v = findBlocks bl (Prims.__proj__Cons__item__hd hd) in
            (Block_get (v, hd)) :: (getBlocksRootToTuple2 rp bl tl)
let (getBestRootByBlocks1 :
  ET_Base.blocks -> ET_Base.robot_position -> (unit, unit) blocks_get) =
  fun bl ->
    fun rp ->
      let v = getBlocksRoot1 rp bl rp in getBlocksRootToTuple2 rp bl v
let (getBestRootByBlocks2 :
  ET_Base.blocks -> ET_Base.robot_position -> (unit, unit) blocks_get) =
  fun bl ->
    fun rp ->
      let v = getBlocksRoot2 rp bl rp in getBlocksRootToTuple2 rp bl v