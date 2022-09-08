module ET_Test

open ET_OtherBase
open ET_Base
open ET_MakeRootBase
open ET_MakeRootBase2
open ET_MakeRootByBlock
open ET_MakeRootByCercle
open ET_MakeRootEval
//open ET_MakeRootEval3

open FStar.IO
open FStar.UInt
open FStar.All
open FStar.UInt8
open FStar.UInt64

val cast_ntoui8: x:nat{(x<64)} -> FStar.UInt8.t
let cast_ntoui8 x = FStar.UInt8.uint_to_t x

val cast_ntoui64: x:nat{(x<=100000000000)} -> FStar.UInt64.t
let cast_ntoui64 x = FStar.UInt64.uint_to_t x

let print_over (x:finites 0 100000000000) = print_string (to_string (cast_ntoui64 x))
let print_length (x:finites 0 63) = print_string (to_string (cast_ntoui64 x))
let print_fieldp (x:finites 0 3) = print_string (to_string (cast_ntoui64 x))
let print_cerclep (x:finites 1 3) = print_string (to_string (cast_ntoui64 x))

val print_nat: n:nat -> ML unit
let print_nat n = 
    if n < 100000000000 then print_over n
    else print_string "over!!!!!"

val printField: f:field_position -> ML unit
let printField f = 
        print_string " ( ";
        print_fieldp (XYPosition?.x f);
        print_string " , ";
        print_fieldp (XYPosition?.y f);
        print_string " ) "

val printCercleField: f:cercle_position -> ML unit
let printCercleField f = 
        print_string " ( ";
        print_cerclep (XYPosition?.x f);
        print_string " , ";
        print_cerclep (XYPosition?.y f);
        print_string " ) "

val printSetfield: l:list field_position -> ML unit
let rec printSetfield l = 
    match l with
    | [] -> ()
    | hd::tl -> 
        printField hd;
        print_string " , ";
        printSetfield tl

val printCercleSetfield: l:list cercle_position -> ML unit
let rec printCercleSetfield l = 
    match l with
    | [] -> ()
    | hd::tl -> 
        printCercleField hd;
        print_string " , ";
        printCercleSetfield tl

val printRoot: #sl:set_field -> #rl:set_field -> #rp:robot_position->l:list_notover (root_s sl rl rp) -> ML unit
let rec printRoot l = 
    match l with
        | [] -> ()
        | hd::tl -> 
            print_string "\n rooot st\n";
            printSetfield hd;
            printRoot tl

val printBlock: b:block -> ML unit
let printBlock b = 
    print_string "\n-------block-----\n";
    print_string "position:";
    printField (Block?.pos b);
    print_string "\n";
    print_string "color:";
    print_string (Block?.col b);
    print_string "\n\n"

val printCercle: c:cercle -> ML unit
let printCercle c = 
    print_string "\n-------cercle-----\n";
    print_string "position:";
    printCercleField (Cercle?.pos c);
    print_string "\n";
    print_string "color:";
    print_string (Cercle?.col c);
    print_string "\n\n"

val printBlocks: bl:list block -> ML unit
let rec printBlocks bl = 
    match bl with
    | [] -> ()
    | hd::tl -> printBlock hd; printBlocks tl

val printCercles: bl:list cercle -> ML unit
let rec printCercles bl = 
    match bl with
    | [] -> ()
    | hd::tl -> printCercle hd; printCercles tl

val printBlockGet: #bl:blocks{notOverlap bl} -> #rp:robot_position -> v:block_get rp bl -> ML unit
let printBlockGet v = 
    print_string "\n----block_get----\n";
    printBlock (Block_get?.b v);
    printSetfield (Block_get?.r v);
    print_string "\n"

val printCercleGet: #b:block -> #cl:cercles{notOverlap cl} -> #bl:blocks{notOverlap bl} -> v:cercle_get b cl bl -> ML unit
let printCercleGet v = 
    print_string "\n----cercle_get----\n";
    printCercle (Cercle_get?.c v);
    printSetfield (Cercle_get?.r v);
    print_string "\n"

val printBlocksGet: #bl:blocks{notOverlap bl} -> #rp:robot_position -> l:blocks_get rp bl -> ML unit
let rec printBlocksGet l = 
    match l with
    | [] -> ()
    | hd :: tl -> printBlockGet hd; printBlocksGet tl

val printCerclesGet: #b:block -> #cl:cercles{notOverlap cl} -> #bl:blocks{notOverlap bl} -> l:cercles_get b cl bl -> ML unit
let rec printCerclesGet l = 
    match l with
    | [] -> ()
    | hd :: tl -> printCercleGet hd; printCerclesGet tl

val printOneAction: oneaction -> ML unit
let printOneAction v = 
    print_string "\n---------------******* OneAction [S]*******-------------------\n";
    printBlock (Oneaction?.block v);
    printCercle (Oneaction?.cercle v);
    print_string "\n---- firstrobotposition ------\n";
    printField (Oneaction?.frpos v);
    print_string "\n---- halfrobotposition ------\n";
    printField (Oneaction?.hrpos v);
    print_string "\n---- lastrobotposition ------\n";
    printField (Oneaction?.lrpos v);
    print_string "\n---- rootbyblock ------\n";
    printSetfield (Oneaction?.rootbyblock v);
    print_string "\n---- rootbycercle ------\n";
    printSetfield (Oneaction?.rootbycercle v);
    print_string "\n---- distance ------\n";
    let v = (Oneaction?.dis v) in
        if v > 63 then 
           let _ = print_string "\nlength over!!!!!!\n" in
            print_string "\n---------------******* OneAction [F]*******-------------------\n"
        else
            let _ = print_length v in
            print_string "\n---------------******* OneAction [F]*******-------------------\n"

val printOneActions: list oneaction -> ML unit
let rec printOneActions l = 
    match l with
    | [] -> ()
    | hd::tl -> printOneAction hd; printOneActions tl
//(*
val printEval: eval -> ML unit
let printEval v = 
    print_string "\n\n--------------------------***********¥¥¥¥¥¥ Eval ¥¥¥¥¥¥*********-----------------------------\n\n";
    printOneAction (Eval?.a v);
    print_string "eval:";
    print_nat (Eval?.e v);
    print_string "\n";
    print_string "number:";
    print_nat (Eval?.b v)
//*)
(*
val printEval2Base: (bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}) -> (bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}) -> eval2 bbl bcl -> ML unit
let rec printEval2Base bbl bcl v = 
    match v with
    | Eval2 a _ _ n st e -> 
        printOneAction (makeOneActionDataFromMeetsData2 a);
        print_string "eval:";
        print_nat e;
        print_string "\n";
        print_string "number:";
        print_nat st;
        printEval2Base bbl bcl n
    | None -> 
        print_string "\n^^^first^^^^\n"

val printEval2: (bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}) -> (bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}) -> eval2 bbl bcl -> ML unit
let printEval2 bbl bcl v = 
    print_string "\n-----------EVAL2_DATA-s----------\n";
    printEval2Base bbl bcl v;
    print_string "\n----------------------f----------\n"

val printEval2List: (bbl:blocks{(notOverlap bbl)/\(length bbl = 8)}) -> (bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}) -> list (eval2 bbl bcl) -> ML unit
let rec printEval2List bbl bcl l = 
    match l with
    | [] -> ()
    | hd::tl ->
        print_string "\nSSSSSSSSSSSSSS\n";
        printEval2 bbl bcl hd;
        print_string "\nFFFFFFFFFFFFFF\n";
        printEval2List bbl bcl tl
*)  
//(*
val printEvalList: list eval -> ML unit
let rec printEvalList l = 
    match l with
    | [] -> ()
    | hd::tl -> printEval hd; printEvalList tl

val printEvalAll: eval -> ML unit
val printEvalAlls: list eval -> ML unit

let rec printEvalAll v = 
    printEval v;
    printEvalAlls (Eval?.n v)
and printEvalAlls l = 
    match l with
    | [] -> ()
    | hd::tl -> printEvalAll hd; printEvalAlls tl

val evalLengthAlls: list eval -> nat
let rec evalLengthAlls l = 
    match l with
    | [] -> 0
    | hd::tl -> 1 +  evalLengthAlls (Eval?.n hd)  + evalLengthAlls tl

val printEvls: evls -> ML unit
let printEvls v = 
    print_string "\n\n----------------------------------------BEST--------------------------------------------\n\n";
    print_string "LEN:::::";
    print_nat (Evls?.h v);
    print_string "\n ---------------------------------------------------------\n";
    print_string "\n ----------------------- BESAT EVAL --------------------------\n";
    printEvalList (Evls?.el v)
//*)

//Test
(*
#set-options "--lax"
val getActionSupportT: bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> bcl:cercles{(notOverlap bcl)/\(length bcl = 8)}
    -> kl:list (eval2 bbl bcl)
    -> t:nat
    -> ML (eval2 bbl bcl)
let rec getActionSupportT bbl bcl kl t  =
        print_string "m_num:";
        print_over ((bf 10) - t);
        print_string "\n";
    if t <= 0 then 
    let _ = print_string "\n************* cannot catch **************\n" in
    None
    else
    let bk = dykstraGetBestListUsualEval bbl bcl kl in
        print_string "                          kl count:";
        print_nat (length kl);
        print_string "\n";
        printEval2List bbl bcl kl;
        print_string "\n\n               bk is \n";
        printEval2 bbl bcl bk;
        print_string "\n";
        print_string "turgetnum:1\n";
        let nbl = getBlocksForNextEval bbl bk in
            print_string "turgetnum:2\n";
            let ncl = getCerclesForNextEval bcl bk in
                print_string "turgetnum:3\n";
                    if (length nbl = 0) then let _ = print_string "turgetnum:4\n" in bk
                    else
                        let rp = getPositionPreviousEval bk in
                            print_string "turgetnum:5\n";
                            let v = getOneAction nbl ncl rp in
                                print_string "turgetnum:6\n";
                                let newevals = makeEvalList bk v in
                                    print_string "turgetnum:7\n";
                                    let nkl = dykstraSetListUsualEval kl bk newevals in
                                        print_string "turgetnum:8  <return call> \n";
                                        getActionSupportT bbl bcl nkl (t-1)

val getAction2T: bbl:blocks{(notOverlap bbl)/\(length bbl = 8)} -> bcl:cercles{(notOverlap bcl)/\(length bcl = 8)} -> ML (eval2 bbl bcl)
let getAction2T bbl bcl = getActionSupportT bbl bcl [] (bf 10)
#reset-options "--lax"



*)







val printAll: bl:blocks{(notOverlap bl)/\(length bl = 8)} -> cl:cercles{(notOverlap cl)/\(length cl = 8)} -> frp:robot_position -> ML unit
let printAll bl cl frp = 
    print_string "\n\n\n[[[[[[[[[[[[[[[[[[[[[¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
    print_string "\n[[[[[[[[[[[[[[[[[[[[[¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
    print_string "\n[[[[[[[[[[[[[[[[[[[[[                All Eval GET                       ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
    print_string "\n[[[[[[[[[[[[[[[[[[[[[¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
    print_string "\n[[[[[[[[[[[[[[[[[[[[[¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n\n\n";
    print_string "\n-----------------------------------------------------------------------------------------------------------------------------\n";
    let v = getAction bl cl frp 0 in
        //printEvalAlls v;
        print_string "\n                                              All Eval Length::::=>  ";
        print_nat (evalLengthAlls v);
        print_string "\n";
        print_string "\n-----------------------------------------------------------------------------------------------------------------------------\n";
        print_string "\n\n\n[[[[[[[[[[[[[[[[[[[[[¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
        print_string "\n[[[[[[[[[[[[[[[[[[[[[¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
        print_string "\n[[[[[[[[[[[[[[[[[[[[[                Best Eval GET                       ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
        print_string "\n[[[[[[[[[[[[[[[[[[[[[¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n";
        print_string "\n[[[[[[[[[[[[[[[[[[[[[¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥¥]]]]]]]]]]]]]]]]]]]]]]]]]]]]]\n\n\n";
        let s = getBestEval v in
            printEvls s

assume val blocksDesu: l:list block -> Lemma((notOverlap l)/\(notOverlap  (getListBlockPosition l)) /\ (colorTwiceSetingU  (getListBlockColor l))/\(length l = 8))
assume val cerclesDesu: l:list cercle-> Lemma((notOverlap l)/\(notOverlap (getListCerclePosition l)) /\ colorTwiceSetingU (getListCercleColor l)/\(length l = 8))
assume val cerclesDesu2: bl:blocks{notOverlap bl} -> cl:cercles{notOverlap cl}-> Lemma(length bl = length cl)
assume val cerclescDesu: b:block -> cl:cercles{notOverlap cl} -> c:cercle -> Lemma((Cercle?.col c = Block?.col b)/\(mem c cl))

let main = 
    print_string "\n--------------------------------***************************************************************-----------------------------\n";
    print_string "\n--------------------------------***************************************************************-----------------------------\n";
    print_string "\n--------------------------------**********************   ET_Test.exe **************************-----------------------------\n";
    print_string "\n--------------------------------***************************************************************-----------------------------\n";
    print_string "\n--------------------------------***************************************************************-----------------------------\n";
    print_string "\n\n                                              START                                                  \n";
    let (blt1:list block) = [(Block (XYPosition 0 1) "red");(Block (XYPosition 0 3) "green");(Block (XYPosition 1 1) "green");(Block (XYPosition 1 2) "yellow" );(Block (XYPosition 1 3) "blue");(Block (XYPosition 2 2) "blue" );(Block (XYPosition 3 1) "red");(Block  (XYPosition 3 3) "yellow")] in
    let (blt2:list block) = [(Block (XYPosition 0 0) "blue");(Block (XYPosition 0 3) "red");(Block (XYPosition 1 2) "green");(Block (XYPosition 1 3) "yellow" );(Block (XYPosition 2 0) "blue");(Block (XYPosition 2 3) "red" );(Block (XYPosition 3 1) "yellow");(Block  (XYPosition 3 2) "green")] in
    let (blt3:list block) = [(Block (XYPosition 0 3) "green");(Block (XYPosition 1 1) "green");(Block (XYPosition 1 3) "blue");(Block (XYPosition 2 1) "yellow" );(Block (XYPosition 2 2) "blue");(Block (XYPosition 2 3) "red" );(Block (XYPosition 3 0) "red");(Block  (XYPosition 3 1) "yellow")] in
    let (blt4:list block) = [(Block (XYPosition 0 2) "green" );(Block (XYPosition 1 1) "blue");(Block (XYPosition 2 0) "green");(Block (XYPosition 2 1) "yellow" );(Block (XYPosition 2 3) "red");(Block (XYPosition 3 1) "blue" );(Block (XYPosition 3 2) "yellow");(Block  (XYPosition 3 3) "red")] in
    let (blt5:list block) = [(Block (XYPosition 0 0) "red" );(Block (XYPosition 0 2) "blue");(Block (XYPosition 1 3) "green");(Block (XYPosition 2 2) "blue" );(Block (XYPosition 2 3) "yellow");(Block (XYPosition 3 0) "red" );(Block (XYPosition 3 1) "green");(Block  (XYPosition 3 2) "yellow")] in
 // let (blt:list block) = [(Block (XYPosition 0 1) "red" );(Block (XYPosition 0 3) "green")]  in
    //let (blt:list block) = [(Block (XYPosition 0 1) "red" );(Block (XYPosition 0 3) "green");(Block (XYPosition 2 2) "blue" );(Block (XYPosition 3 1) "red");(Block  (XYPosition 3 3) "yellow")] in
  //  let (clt:list cercle) = [(Cercle (XYPosition 1 3) "red");(Cercle (XYPosition 2 1) "green" );(Cercle (XYPosition 3 1) "red" );(Cercle (XYPosition 3 2) "green")] in  
    let (clt1:list cercle) = [(Cercle (XYPosition 1 1) "yellow" );(Cercle (XYPosition 1 2) "green");(Cercle (XYPosition 1 3) "red");(Cercle (XYPosition 2 1) "green" );(Cercle (XYPosition 2 3) "blue");(Cercle (XYPosition 3 1) "red" );(Cercle (XYPosition 3 2) "yellow");(Cercle (XYPosition 3 3) "blue")] in
    let (clt2:list cercle) = [(Cercle (XYPosition 1 1) "blue" );(Cercle (XYPosition 1 2) "red");(Cercle (XYPosition 1 3) "green");(Cercle (XYPosition 2 1) "yellow" );(Cercle (XYPosition 2 3) "blue");(Cercle (XYPosition 3 1) "red" );(Cercle (XYPosition 3 2) "yellow");(Cercle (XYPosition 3 3) "green")] in
    let (clt3:list cercle) = [(Cercle (XYPosition 1 1) "red" );(Cercle (XYPosition 1 2) "blue");(Cercle (XYPosition 1 3) "blue");(Cercle (XYPosition 2 1) "green" );(Cercle (XYPosition 2 3) "red");(Cercle (XYPosition 3 1) "yellow" );(Cercle (XYPosition 3 2) "green");(Cercle (XYPosition 3 3) "yellow")] in
    let (clt4:list cercle) = [(Cercle (XYPosition 1 1) "blue" );(Cercle (XYPosition 1 2) "green");(Cercle (XYPosition 1 3) "red");(Cercle (XYPosition 2 1) "yellow" );(Cercle (XYPosition 2 3) "blue");(Cercle (XYPosition 3 1) "red" );(Cercle (XYPosition 3 2) "yellow");(Cercle (XYPosition 3 3) "green")] in
    let (clt5:list cercle) = [(Cercle (XYPosition 1 1) "yellow" );(Cercle (XYPosition 1 2) "blue");(Cercle (XYPosition 1 3) "yellow");(Cercle (XYPosition 2 1) "green" );(Cercle (XYPosition 2 3) "blue");(Cercle (XYPosition 3 1) "green" );(Cercle (XYPosition 3 2) "red");(Cercle (XYPosition 3 3) "red")] in
    
    //let (bt:block) = (Block (XYPosition 0 1) "red" ) in
    //let (ct:cercle) = (Cercle (XYPosition 1 3) "red") in
  // let slt:set_field = [(XYPosition 0 1);(XYPosition 1 1);(XYPosition 2 2);(XYPosition 3 1)] in
   // let rlt:set_field = [] in 
            blocksDesu blt1;
            cerclesDesu clt1;
            cerclesDesu2 blt1 clt1;
            blocksDesu blt2;
            cerclesDesu clt2;
            cerclesDesu2 blt2 clt2;
            blocksDesu blt3;
            cerclesDesu clt3;
            cerclesDesu2 blt3 clt3;
            blocksDesu blt4;
            cerclesDesu clt4;
            cerclesDesu2 blt4 clt4;
            blocksDesu blt5;
            cerclesDesu clt5;
            cerclesDesu2 blt5 clt5;
          //  cerclescDesu bt clt ct;
            let (rpt:robot_position) = (XYPosition 1 0) in
                    printAll blt1 clt1 rpt;
                    printAll blt2 clt2 rpt;
                    printAll blt3 clt3 rpt;
                    printAll blt4 clt4 rpt;
                    printAll blt5 clt5 rpt;
             //   let v:blocks_get rpt blt = getBestRootByBlocks1 blt rpt in
                   // printBlocksGet v; 
    print_string "\n\n                                               FINISH                                               \n"