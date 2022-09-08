open Prims
let (cast_ntoui8 : ET_OtherBase.nat -> FStar_UInt8.t) =
  fun x -> FStar_UInt8.uint_to_t x
let (cast_ntoui64 : ET_OtherBase.nat -> FStar_UInt64.t) =
  fun x -> FStar_UInt64.uint_to_t x
let (print_over : (unit, unit) ET_Base.finites -> unit) =
  fun x -> FStar_IO.print_string (FStar_UInt64.to_string (cast_ntoui64 x))
let (print_length : (unit, unit) ET_Base.finites -> unit) =
  fun x -> FStar_IO.print_string (FStar_UInt64.to_string (cast_ntoui64 x))
let (print_fieldp : (unit, unit) ET_Base.finites -> unit) =
  fun x -> FStar_IO.print_string (FStar_UInt64.to_string (cast_ntoui64 x))
let (print_cerclep : (unit, unit) ET_Base.finites -> unit) =
  fun x -> FStar_IO.print_string (FStar_UInt64.to_string (cast_ntoui64 x))
let (print_nat : ET_OtherBase.nat -> unit) =
  fun n ->
    if n < (Prims.parse_int "100000000000")
    then print_over n
    else FStar_IO.print_string "over!!!!!"
let (printField : ET_Base.field_position -> unit) =
  fun f ->
    FStar_IO.print_string " ( ";
    print_fieldp
      (ET_Base.__proj__XYPosition__item__x Prims.int_zero (Prims.of_int (3))
         Prims.int_zero (Prims.of_int (3)) f);
    FStar_IO.print_string " , ";
    print_fieldp
      (ET_Base.__proj__XYPosition__item__y Prims.int_zero (Prims.of_int (3))
         Prims.int_zero (Prims.of_int (3)) f);
    FStar_IO.print_string " ) "
let (printCercleField : ET_Base.cercle_position -> unit) =
  fun f ->
    FStar_IO.print_string " ( ";
    print_cerclep
      (ET_Base.__proj__XYPosition__item__x Prims.int_one (Prims.of_int (3))
         Prims.int_one (Prims.of_int (3)) f);
    FStar_IO.print_string " , ";
    print_cerclep
      (ET_Base.__proj__XYPosition__item__y Prims.int_one (Prims.of_int (3))
         Prims.int_one (Prims.of_int (3)) f);
    FStar_IO.print_string " ) "
let rec (printSetfield : ET_Base.field_position Prims.list -> unit) =
  fun l ->
    match l with
    | [] -> ()
    | hd::tl ->
        (printField hd; FStar_IO.print_string " , "; printSetfield tl)
let rec (printCercleSetfield : ET_Base.cercle_position Prims.list -> unit) =
  fun l ->
    match l with
    | [] -> ()
    | hd::tl ->
        (printCercleField hd;
         FStar_IO.print_string " , ";
         printCercleSetfield tl)
let rec (printRoot :
  ET_Base.set_field ->
    ET_Base.set_field ->
      ET_Base.robot_position ->
        (unit, unit, unit) ET_MakeRootBase.root_s ET_Base.list_notover ->
          unit)
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun l ->
          match l with
          | [] -> ()
          | hd::tl ->
              (FStar_IO.print_string "\n rooot st\n";
               printSetfield hd;
               printRoot uu___ uu___1 uu___2 tl)
let (printBlock : ET_Base.block -> unit) =
  fun b ->
    FStar_IO.print_string "\n-------block-----\n";
    FStar_IO.print_string "position:";
    printField (ET_Base.__proj__Block__item__pos b);
    FStar_IO.print_string "\n";
    FStar_IO.print_string "color:";
    FStar_IO.print_string (ET_Base.__proj__Block__item__col b);
    FStar_IO.print_string "\n\n"
let (printCercle : ET_Base.cercle -> unit) =
  fun c ->
    FStar_IO.print_string "\n-------cercle-----\n";
    FStar_IO.print_string "position:";
    printCercleField (ET_Base.__proj__Cercle__item__pos c);
    FStar_IO.print_string "\n";
    FStar_IO.print_string "color:";
    FStar_IO.print_string (ET_Base.__proj__Cercle__item__col c);
    FStar_IO.print_string "\n\n"
let rec (printBlocks : ET_Base.block Prims.list -> unit) =
  fun bl ->
    match bl with | [] -> () | hd::tl -> (printBlock hd; printBlocks tl)
let rec (printCercles : ET_Base.cercle Prims.list -> unit) =
  fun bl ->
    match bl with | [] -> () | hd::tl -> (printCercle hd; printCercles tl)
let (printBlockGet :
  ET_Base.blocks ->
    ET_Base.robot_position ->
      (unit, unit) ET_MakeRootByBlock.block_get -> unit)
  =
  fun uu___ ->
    fun uu___1 ->
      fun v ->
        FStar_IO.print_string "\n----block_get----\n";
        printBlock
          (ET_MakeRootByBlock.__proj__Block_get__item__b uu___1 uu___ v);
        printSetfield
          (ET_MakeRootByBlock.__proj__Block_get__item__r uu___1 uu___ v);
        FStar_IO.print_string "\n"
let (printCercleGet :
  ET_Base.block ->
    ET_Base.cercles ->
      ET_Base.blocks ->
        (unit, unit, unit) ET_MakeRootByCercle.cercle_get -> unit)
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun v ->
          FStar_IO.print_string "\n----cercle_get----\n";
          printCercle
            (ET_MakeRootByCercle.__proj__Cercle_get__item__c uu___ uu___1
               uu___2 v);
          printSetfield
            (ET_MakeRootByCercle.__proj__Cercle_get__item__r uu___ uu___1
               uu___2 v);
          FStar_IO.print_string "\n"
let rec (printBlocksGet :
  ET_Base.blocks ->
    ET_Base.robot_position ->
      (unit, unit) ET_MakeRootByBlock.blocks_get -> unit)
  =
  fun uu___ ->
    fun uu___1 ->
      fun l ->
        match l with
        | [] -> ()
        | hd::tl ->
            (printBlockGet uu___ uu___1 hd; printBlocksGet uu___ uu___1 tl)
let rec (printCerclesGet :
  ET_Base.block ->
    ET_Base.cercles ->
      ET_Base.blocks ->
        (unit, unit, unit) ET_MakeRootByCercle.cercles_get -> unit)
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun l ->
          match l with
          | [] -> ()
          | hd::tl ->
              (printCercleGet uu___ uu___1 uu___2 hd;
               printCerclesGet uu___ uu___1 uu___2 tl)
let (printOneAction : ET_Base.oneaction -> unit) =
  fun v ->
    FStar_IO.print_string
      "\n---------------******* OneAction [S]*******-------------------\n";
    printBlock (ET_Base.__proj__Oneaction__item__block v);
    printCercle (ET_Base.__proj__Oneaction__item__cercle v);
    FStar_IO.print_string "\n---- firstrobotposition ------\n";
    printField (ET_Base.__proj__Oneaction__item__frpos v);
    FStar_IO.print_string "\n---- halfrobotposition ------\n";
    printField (ET_Base.__proj__Oneaction__item__hrpos v);
    FStar_IO.print_string "\n---- lastrobotposition ------\n";
    printField (ET_Base.__proj__Oneaction__item__lrpos v);
    FStar_IO.print_string "\n---- rootbyblock ------\n";
    printSetfield (ET_Base.__proj__Oneaction__item__rootbyblock v);
    FStar_IO.print_string "\n---- rootbycercle ------\n";
    printSetfield (ET_Base.__proj__Oneaction__item__rootbycercle v);
    FStar_IO.print_string "\n---- distance ------\n";
    (let v1 = ET_Base.__proj__Oneaction__item__dis v in
     if v1 > (Prims.of_int (63))
     then
       (FStar_IO.print_string "\nlength over!!!!!!\n";
        FStar_IO.print_string
          "\n---------------******* OneAction [F]*******-------------------\n")
     else
       (print_length v1;
        FStar_IO.print_string
          "\n---------------******* OneAction [F]*******-------------------\n"))
let rec (printOneActions : ET_Base.oneaction Prims.list -> unit) =
  fun l ->
    match l with
    | [] -> ()
    | hd::tl -> (printOneAction hd; printOneActions tl)
let (printEval : ET_MakeRootEval.eval -> unit) =
  fun v ->
    FStar_IO.print_string
      "\n\n--------------------------***********\194\165\194\165\194\165\194\165\194\165\194\165 Eval \194\165\194\165\194\165\194\165\194\165\194\165*********-----------------------------\n\n";
    printOneAction (ET_MakeRootEval.__proj__Eval__item__a v);
    FStar_IO.print_string "eval:";
    print_nat (ET_MakeRootEval.__proj__Eval__item__e v);
    FStar_IO.print_string "\n";
    FStar_IO.print_string "number:";
    print_nat (ET_MakeRootEval.__proj__Eval__item__b v)
let rec (printEvalList : ET_MakeRootEval.eval Prims.list -> unit) =
  fun l ->
    match l with | [] -> () | hd::tl -> (printEval hd; printEvalList tl)
let rec (printEvalAll : ET_MakeRootEval.eval -> unit) =
  fun v ->
    printEval v; printEvalAlls (ET_MakeRootEval.__proj__Eval__item__n v)
and (printEvalAlls : ET_MakeRootEval.eval Prims.list -> unit) =
  fun l ->
    match l with | [] -> () | hd::tl -> (printEvalAll hd; printEvalAlls tl)
let rec (evalLengthAlls :
  ET_MakeRootEval.eval Prims.list -> ET_OtherBase.nat) =
  fun l ->
    match l with
    | [] -> Prims.int_zero
    | hd::tl ->
        (Prims.int_one +
           (evalLengthAlls (ET_MakeRootEval.__proj__Eval__item__n hd)))
          + (evalLengthAlls tl)
let (printEvls : ET_MakeRootEval.evls -> unit) =
  fun v ->
    FStar_IO.print_string
      "\n\n----------------------------------------BEST--------------------------------------------\n\n";
    FStar_IO.print_string "LEN:::::";
    print_nat (ET_MakeRootEval.__proj__Evls__item__h v);
    FStar_IO.print_string
      "\n ---------------------------------------------------------\n";
    FStar_IO.print_string
      "\n ----------------------- BESAT EVAL --------------------------\n";
    printEvalList (ET_MakeRootEval.__proj__Evls__item__el v)
let (printAll :
  ET_Base.blocks -> ET_Base.cercles -> ET_Base.robot_position -> unit) =
  fun bl ->
    fun cl ->
      fun frp ->
        FStar_IO.print_string
          "\n\n\n[[[[[[[[[[[[[[[[[[[[[\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
        FStar_IO.print_string
          "\n[[[[[[[[[[[[[[[[[[[[[\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
        FStar_IO.print_string
          "\n[[[[[[[[[[[[[[[[[[[[[                All Eval GET                       ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
        FStar_IO.print_string
          "\n[[[[[[[[[[[[[[[[[[[[[\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
        FStar_IO.print_string
          "\n[[[[[[[[[[[[[[[[[[[[[\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n\n\n";
        FStar_IO.print_string
          "\n-----------------------------------------------------------------------------------------------------------------------------\n";
        (let v = ET_MakeRootEval.getAction bl cl frp Prims.int_zero in
         FStar_IO.print_string
           "\n                                              All Eval Length::::=>  ";
         print_nat (evalLengthAlls v);
         FStar_IO.print_string "\n";
         FStar_IO.print_string
           "\n-----------------------------------------------------------------------------------------------------------------------------\n";
         FStar_IO.print_string
           "\n\n\n[[[[[[[[[[[[[[[[[[[[[\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
         FStar_IO.print_string
           "\n[[[[[[[[[[[[[[[[[[[[[\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
         FStar_IO.print_string
           "\n[[[[[[[[[[[[[[[[[[[[[                Best Eval GET                       ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
         FStar_IO.print_string
           "\n[[[[[[[[[[[[[[[[[[[[[\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
         FStar_IO.print_string
           "\n[[[[[[[[[[[[[[[[[[[[[\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165\194\165]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n\n\n";
         (let s = ET_MakeRootEval.getBestEval v in printEvls s))
let (main : unit) =
  FStar_IO.print_string
    "\n--------------------------------***************************************************************-----------------------------\n";
  FStar_IO.print_string
    "\n--------------------------------***************************************************************-----------------------------\n";
  FStar_IO.print_string
    "\n--------------------------------**********************   ET_Test.exe **************************-----------------------------\n";
  FStar_IO.print_string
    "\n--------------------------------***************************************************************-----------------------------\n";
  FStar_IO.print_string
    "\n--------------------------------***************************************************************-----------------------------\n";
  FStar_IO.print_string
    "\n\n                                              START                                                  \n";
  (let blt1 =
     [ET_Base.Block
        ((ET_Base.XYPosition (Prims.int_zero, Prims.int_one)), "red");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_zero, (Prims.of_int (3)))), "green");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, Prims.int_one)), "green");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (2)))), "yellow");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "blue");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (2)))),
         "blue");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "red");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (3)))),
         "yellow")] in
   let blt2 =
     [ET_Base.Block
        ((ET_Base.XYPosition (Prims.int_zero, Prims.int_zero)), "blue");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_zero, (Prims.of_int (3)))), "red");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (2)))), "green");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "yellow");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_zero)), "blue");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))), "red");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "yellow");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (2)))),
         "green")] in
   let blt3 =
     [ET_Base.Block
        ((ET_Base.XYPosition (Prims.int_zero, (Prims.of_int (3)))), "green");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, Prims.int_one)), "green");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "blue");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_one)), "yellow");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (2)))),
         "blue");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))), "red");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_zero)), "red");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "yellow")] in
   let blt4 =
     [ET_Base.Block
        ((ET_Base.XYPosition (Prims.int_zero, (Prims.of_int (2)))), "green");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, Prims.int_one)), "blue");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_zero)), "green");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_one)), "yellow");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))), "red");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "blue");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (2)))),
         "yellow");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (3)))), "red")] in
   let blt5 =
     [ET_Base.Block
        ((ET_Base.XYPosition (Prims.int_zero, Prims.int_zero)), "red");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_zero, (Prims.of_int (2)))), "blue");
     ET_Base.Block
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "green");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (2)))),
         "blue");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))),
         "yellow");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_zero)), "red");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "green");
     ET_Base.Block
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (2)))),
         "yellow")] in
   let clt1 =
     [ET_Base.Cercle
        ((ET_Base.XYPosition (Prims.int_one, Prims.int_one)), "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (2)))), "green");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_one)), "green");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))),
         "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (2)))),
         "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (3)))),
         "blue")] in
   let clt2 =
     [ET_Base.Cercle
        ((ET_Base.XYPosition (Prims.int_one, Prims.int_one)), "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (2)))), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "green");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_one)), "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))),
         "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (2)))),
         "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (3)))),
         "green")] in
   let clt3 =
     [ET_Base.Cercle
        ((ET_Base.XYPosition (Prims.int_one, Prims.int_one)), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (2)))), "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_one)), "green");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (2)))),
         "green");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (3)))),
         "yellow")] in
   let clt4 =
     [ET_Base.Cercle
        ((ET_Base.XYPosition (Prims.int_one, Prims.int_one)), "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (2)))), "green");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_one)), "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))),
         "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (2)))),
         "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (3)))),
         "green")] in
   let clt5 =
     [ET_Base.Cercle
        ((ET_Base.XYPosition (Prims.int_one, Prims.int_one)), "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (2)))), "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition (Prims.int_one, (Prims.of_int (3)))), "yellow");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), Prims.int_one)), "green");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (2)), (Prims.of_int (3)))),
         "blue");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), Prims.int_one)), "green");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (2)))), "red");
     ET_Base.Cercle
       ((ET_Base.XYPosition ((Prims.of_int (3)), (Prims.of_int (3)))), "red")] in
   let rpt = ET_Base.XYPosition (Prims.int_one, Prims.int_zero) in
   printAll blt1 clt1 rpt;
   printAll blt2 clt2 rpt;
   printAll blt3 clt3 rpt;
   printAll blt4 clt4 rpt;
   printAll blt5 clt5 rpt;
   FStar_IO.print_string
     "\n\n                                               FINISH                                               \n")