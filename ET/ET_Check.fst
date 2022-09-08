module ET_Check
open ET_Base

val boolToInt: n:bool -> n:int{(n==0)\/(n==1)}
let boolToInt n =
    match n with
        | true -> 1
        | false -> 0
    
val notOverRangeState: l: list direction -> bool
let rec notOverRangeState l = 
     match l with
        | [] -> true
        | hd::tl -> ((Direction?.x hd)>=0) && ((Direction?.x hd)<=3) && ((Direction?.y hd)>=0) && ((Direction?.y hd)<=3) && notOverRangeState tl
        | hd1::hd2::tl -> ((Direction?.x hd1)+(Direction?.x hd2)>=0) && ((Direction?.x hd1)+(Direction?.x hd2)<=3) && ((Direction?.y hd1)+(Direction?.y hd2)>=0) && ((Direction?.y hd1)+(Direction?.y hd2)<=3) && notOverRangeState (hd2::tl)
(*
val makeRoot: l:list direction{notOverRangeState l} -> list robot_position
let rec makeRoot l = 
    match l with
        | [] -> [first_robot_position]
        | hd::tl -> ((Direction?.x hd),(Direction?.y hd)) :: makeRoot tl
        | hd1::hd2::tl -> ((Direction?.x hd1) + (Direction?.x hd2),(Direction?.y hd1) + (Direction?.y hd2)) :: makeRoot (hd2::tl)


assume val evalution_check: x:robot_position -> evalution_state

val checking: l:list robot_position -> real_evalution
let rec checking l =
    match l with
        | [] -> Realevalution 0 0
        | hd::tl -> 
            let state = evalution_check hd in
                //assert(!(state.fst /\ state.snd))
                let ctl = checking tl in
                    ((boolToInt state._1) + (Realevalution?.catch ctl),(boolToInt state._2) + (Realevalution?.put ctl)) 


*) 

    

