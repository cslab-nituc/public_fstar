open Prims
let rec (length_f :
  ET_OtherBase.nat ->
    ET_OtherBase.nat ->
      (unit, unit) ET_Base.finites ->
        (unit, unit) ET_Base.finites Prims.list -> ET_OtherBase.nat)
  =
  fun a ->
    fun b ->
      fun x ->
        fun l ->
          if a < x
          then
            (if ET_OtherBase.mem x l
             then (length_f a b (x - Prims.int_one) l) + Prims.int_one
             else length_f a b (x - Prims.int_one) l)
          else if ET_OtherBase.mem x l then Prims.int_one else Prims.int_zero














let (get_valueofrange :
  ET_OtherBase.nat ->
    ET_OtherBase.nat ->
      ET_OtherBase.nat ->
        ET_OtherBase.nat ->
          (unit, unit) ET_Base.finites ->
            (unit, unit) ET_Base.finites -> ET_OtherBase.nat)
  =
  fun a ->
    fun b ->
      fun c ->
        fun d ->
          fun x ->
            fun y ->
              (((d - c) + Prims.int_one) * (x - a)) +
                ((y - c) + Prims.int_one)



let (get_valueofrangeposition :
  ET_OtherBase.nat ->
    ET_OtherBase.nat ->
      ET_OtherBase.nat ->
        ET_OtherBase.nat ->
          (unit, unit, unit, unit) ET_Base.xyposition -> ET_OtherBase.nat)
  =
  fun a ->
    fun b ->
      fun c ->
        fun d ->
          fun p ->
            get_valueofrange a b c d
              (ET_Base.__proj__XYPosition__item__x a b c d p)
              (ET_Base.__proj__XYPosition__item__y a b c d p)
let rec (makeOverRange :
  ET_OtherBase.nat ->
    ET_OtherBase.nat ->
      ET_OtherBase.nat ->
        ET_OtherBase.nat ->
          (unit, unit, unit, unit) ET_Base.xyposition Prims.list ->
            (unit, unit) ET_Base.finites Prims.list)
  =
  fun a ->
    fun b ->
      fun c ->
        fun d ->
          fun l ->
            match l with
            | [] -> []
            | hd::tl -> (get_valueofrangeposition a b c d hd) ::
                (makeOverRange a b c d tl)


