module ET_OtherData
open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module MO = LowStar.Modifies
open LowStar.BufferOps
open FStar.HyperStack.ST
type s =
  | Content:
    pl: list int ->
    l: int ->  
    s


let main (a:eqtype) (s:a)= 
        assert(s = s)
//assume val findBlocksAppendLemma0: l1:blocks{notOverlap l1}->l2:blocks{notOverlap l2}->Lemma(notOverlaplists l1 l2)
(*
val findBlocksAppendLemma1: l1:blocks{notOverlap l1}->l2:blocks{notOverlap l2}->Lemma(notOverlap (appendNotOverlap l1 l2))
let rec findBlocksAppendLemma1 l1 l2 = match l1 with 
    | [] -> ()
    | hd::tl -> findBlocksAppendLemma1 tl l2

assume val findBlocksAppendLemma2: l1:blocks{notOverlap l1}->l2:blocks{notOverlap l2}->Lemma(notOverlap (getListBlockPosition (appendNotOverlap l1 l2)))

let rec findBlocksAppendLemma2 l1 l2 = match l1 with 
    | [] -> ()
    | hd::tl -> findBlocksAppendLemma2 tl l2

assume val findBlocksAppendLemma3: l1:blocks{notOverlap l1}->l2:blocks{notOverlap l2}->Lemma(colorBlockTwiceSeting (getListBlockColor (appendNotOverlap l1 l2)))

let rec findBlocksAppendLemma3 l1 l2 = match l1 with 
    | [] -> ()
    | hd::tl -> findBlocksAppendLemma3 tl l2
*)
(*
val findBlocksToList: bl:blocks{(length bl <= 8) /\ (length bl >= 0)}->l:list robot_position{(length l) <= 16 /\ notOverlap l}->rp:robot_position->Tot(gl:blocks{notOverlap gl}) (decreases %[(16 - length(l));0;0]) 
val findBlocksToListSupport: bl:blocks{(length bl <= 8) /\ (length bl >= 0)}->l:list robot_position{(length l) <= 16 /\ notOverlap l}->rp:robot_position->dl:list direction->Tot(gl:blocks{notOverlap gl}) (decreases %[(16 - length(l));1;(length dl)])

//forall (i:robot_position). mem i l ==> length l = 16
//notOvrelap l = (not (mem hd tl)) /\ notOverlap tl 
//(length l = 16) ==> forall (i:robot_position). mem i l (==> mem rp l)
//[r] notOverlap l /\ (length l <= 16) /\ 

let rec findBlocksToList bl l rp = 
    xypositionLemma l;
    if mem rp l then []
    else
        let nl = rp::l in
            let block_item = (findBlocks bl rp) in
                match block_item with 
                | None -> findBlocksToListSupport bl nl rp direction_all
                | Some v-> [v]     
and findBlocksToListSupport bl l rp dl = 
    match dl with
    | [] -> []
    | hd::tl -> 
        let x = (XYPosition?.x rp) + (Direction?.x hd) in
            let y = (XYPosition?.y rp) + (Direction?.y hd) in
                if (x >= 0) && (x <= 3) && (y >= 0) && (y <= 3) then 
                    let nrp = XYPosition x y in
                        findBlocksAppendLemma1 (findBlocksToList bl l nrp) (findBlocksToListSupport bl l rp tl);
                        findBlocksAppendLemma2 (findBlocksToList bl l nrp) (findBlocksToListSupport bl l rp tl);
                        findBlocksAppendLemma3 (findBlocksToList bl l nrp) (findBlocksToListSupport bl l rp tl);
                        appendNotOverlap (findBlocksToList bl l nrp) (findBlocksToListSupport bl l rp tl)
                else []


                *)