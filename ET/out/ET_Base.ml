open Prims
type ('a, 'b) finites = ET_OtherBase.nat
type ('a, 'b, 'c, 'd) xyposition =
  | XYPosition of (unit, unit) finites * (unit, unit) finites 
let (uu___is_XYPosition :
  ET_OtherBase.nat ->
    ET_OtherBase.nat ->
      ET_OtherBase.nat ->
        ET_OtherBase.nat -> (unit, unit, unit, unit) xyposition -> Prims.bool)
  = fun a -> fun b -> fun c -> fun d -> fun projectee -> true
let (__proj__XYPosition__item__x :
  ET_OtherBase.nat ->
    ET_OtherBase.nat ->
      ET_OtherBase.nat ->
        ET_OtherBase.nat ->
          (unit, unit, unit, unit) xyposition -> (unit, unit) finites)
  =
  fun a ->
    fun b ->
      fun c ->
        fun d ->
          fun projectee -> match projectee with | XYPosition (x, y) -> x
let (__proj__XYPosition__item__y :
  ET_OtherBase.nat ->
    ET_OtherBase.nat ->
      ET_OtherBase.nat ->
        ET_OtherBase.nat ->
          (unit, unit, unit, unit) xyposition -> (unit, unit) finites)
  =
  fun a ->
    fun b ->
      fun c ->
        fun d ->
          fun projectee -> match projectee with | XYPosition (x, y) -> y
type field_position = (unit, unit, unit, unit) xyposition
type robot_position = field_position
type block_position = field_position
type cercle_position = (unit, unit, unit, unit) xyposition
type direction_range = Prims.int
type direction =
  | Direction of direction_range * direction_range 
let (uu___is_Direction : direction -> Prims.bool) = fun projectee -> true
let (__proj__Direction__item__x : direction -> direction_range) =
  fun projectee -> match projectee with | Direction (x, y) -> x
let (__proj__Direction__item__y : direction -> direction_range) =
  fun projectee -> match projectee with | Direction (x, y) -> y
type evalution_state = (Prims.bool * Prims.bool)
type evalution_range = (unit, unit) finites
type evalution =
  | Evalution of evalution_range * evalution_range 
let (uu___is_Evalution : evalution -> Prims.bool) = fun projectee -> true
let (__proj__Evalution__item__catch : evalution -> evalution_range) =
  fun projectee -> match projectee with | Evalution (catch, put) -> catch
let (__proj__Evalution__item__put : evalution -> evalution_range) =
  fun projectee -> match projectee with | Evalution (catch, put) -> put
type real_evalution =
  | Realevalution of Prims.int * Prims.int 
let (uu___is_Realevalution : real_evalution -> Prims.bool) =
  fun projectee -> true
let (__proj__Realevalution__item__catch : real_evalution -> Prims.int) =
  fun projectee -> match projectee with | Realevalution (catch, put) -> catch
let (__proj__Realevalution__item__put : real_evalution -> Prims.int) =
  fun projectee -> match projectee with | Realevalution (catch, put) -> put
let (first_robot_position : robot_position) =
  XYPosition (Prims.int_one, Prims.int_zero)
let (black_cercle_position : cercle_position) =
  XYPosition (Prims.int_one, Prims.int_one)
type color = Prims.string
type 't list_notover = 't Prims.list
type set_field = field_position list_notover
type cercle =
  | Cercle of cercle_position * color 
let (uu___is_Cercle : cercle -> Prims.bool) = fun projectee -> true
let (__proj__Cercle__item__pos : cercle -> cercle_position) =
  fun projectee -> match projectee with | Cercle (pos, col) -> pos
let (__proj__Cercle__item__col : cercle -> color) =
  fun projectee -> match projectee with | Cercle (pos, col) -> col
type block =
  | Block of block_position * color 
let (uu___is_Block : block -> Prims.bool) = fun projectee -> true
let (__proj__Block__item__pos : block -> block_position) =
  fun projectee -> match projectee with | Block (pos, col) -> pos
let (__proj__Block__item__col : block -> color) =
  fun projectee -> match projectee with | Block (pos, col) -> col
type oneaction =
  | Oneaction of block * cercle * robot_position * set_field * set_field *
  robot_position * robot_position * ET_OtherBase.nat 
let (uu___is_Oneaction : oneaction -> Prims.bool) = fun projectee -> true
let (__proj__Oneaction__item__block : oneaction -> block) =
  fun projectee ->
    match projectee with
    | Oneaction
        (block1, cercle1, frpos, rootbyblock, rootbycercle, hrpos, lrpos,
         dis)
        -> block1
let (__proj__Oneaction__item__cercle : oneaction -> cercle) =
  fun projectee ->
    match projectee with
    | Oneaction
        (block1, cercle1, frpos, rootbyblock, rootbycercle, hrpos, lrpos,
         dis)
        -> cercle1
let (__proj__Oneaction__item__frpos : oneaction -> robot_position) =
  fun projectee ->
    match projectee with
    | Oneaction
        (block1, cercle1, frpos, rootbyblock, rootbycercle, hrpos, lrpos,
         dis)
        -> frpos
let (__proj__Oneaction__item__rootbyblock : oneaction -> set_field) =
  fun projectee ->
    match projectee with
    | Oneaction
        (block1, cercle1, frpos, rootbyblock, rootbycercle, hrpos, lrpos,
         dis)
        -> rootbyblock
let (__proj__Oneaction__item__rootbycercle : oneaction -> set_field) =
  fun projectee ->
    match projectee with
    | Oneaction
        (block1, cercle1, frpos, rootbyblock, rootbycercle, hrpos, lrpos,
         dis)
        -> rootbycercle
let (__proj__Oneaction__item__hrpos : oneaction -> robot_position) =
  fun projectee ->
    match projectee with
    | Oneaction
        (block1, cercle1, frpos, rootbyblock, rootbycercle, hrpos, lrpos,
         dis)
        -> hrpos
let (__proj__Oneaction__item__lrpos : oneaction -> robot_position) =
  fun projectee ->
    match projectee with
    | Oneaction
        (block1, cercle1, frpos, rootbyblock, rootbycercle, hrpos, lrpos,
         dis)
        -> lrpos
let (__proj__Oneaction__item__dis : oneaction -> ET_OtherBase.nat) =
  fun projectee ->
    match projectee with
    | Oneaction
        (block1, cercle1, frpos, rootbyblock, rootbycercle, hrpos, lrpos,
         dis)
        -> dis
let (getListCerclePosition : cercle Prims.list -> cercle_position Prims.list)
  = fun l -> ET_OtherBase.map __proj__Cercle__item__pos l
let (getListCercleColor : cercle Prims.list -> color Prims.list) =
  fun l -> ET_OtherBase.map __proj__Cercle__item__col l
let (getListBlockPosition : block Prims.list -> block_position Prims.list) =
  fun l -> ET_OtherBase.map __proj__Block__item__pos l
let (getListBlockColor : block Prims.list -> color Prims.list) =
  fun l -> ET_OtherBase.map __proj__Block__item__col l
let (memCountColor : color Prims.list -> color -> ET_OtherBase.nat) =
  fun l -> fun m -> ET_OtherBase.memCount l m
let (colorTwiceSetingU : color Prims.list -> Prims.bool) =
  fun l ->
    let yc = memCountColor l "yellow" in
    let rc = memCountColor l "red" in
    let gc = memCountColor l "green" in
    let bc = memCountColor l "blue" in
    if
      (((yc <= (Prims.of_int (2))) && (rc <= (Prims.of_int (2)))) &&
         (gc <= (Prims.of_int (2))))
        && (bc <= (Prims.of_int (2)))
    then true
    else false
let (colorTwiceSetingS : color Prims.list -> Prims.bool) =
  fun l ->
    let yc = memCountColor l "yellow" in
    let rc = memCountColor l "red" in
    let gc = memCountColor l "green" in
    let bc = memCountColor l "blue" in
    if
      (((yc = (Prims.of_int (2))) && (rc = (Prims.of_int (2)))) &&
         (gc = (Prims.of_int (2))))
        && (bc = (Prims.of_int (2)))
    then true
    else false
let rec (sameColor : color Prims.list -> color -> Prims.bool) =
  fun l ->
    fun c ->
      match l with | [] -> true | hd::tl -> (hd = c) && (sameColor tl c)
let rec (checkNotCercle22 : cercle_position Prims.list -> Prims.bool) =
  fun l ->
    match l with
    | [] -> true
    | hd::tl ->
        if black_cercle_position = hd then false else checkNotCercle22 tl
type blocks = block list_notover
let (get_blocks : unit -> blocks) =
  fun uu___ -> failwith "Not yet implemented:get_blocks"
type cercles = cercle list_notover
let (get_cercles : unit -> cercles) =
  fun uu___ -> failwith "Not yet implemented:get_cercles"
let rec (getBlockFromPosition : block_position -> block Prims.list -> block)
  =
  fun po ->
    fun bl ->
      match bl with
      | hd::tl ->
          if (__proj__Block__item__pos hd) = po
          then hd
          else getBlockFromPosition po tl






let (removeBlocks : blocks -> block -> blocks) =
  fun bl -> fun b -> ET_OtherBase.memRemove b bl
let (removeCercles : cercles -> cercle -> cercles) =
  fun cl -> fun c -> ET_OtherBase.memRemove c cl