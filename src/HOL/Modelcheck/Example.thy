(*  Title:      HOL/Modelcheck/Example.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen

Example:

    000    --->   100    ---> 110
           <---    
*)

Example = CTL + MCSyn + 


types
    state = "bool * bool * bool"

consts

  INIT :: "state pred"
  N    :: "[state,state] => bool"
  reach,restart,infinitely,toggle:: "state pred"

defs
  
  INIT_def "INIT x == ~(fst x)&~(fst (snd x))&~(snd (snd x))"

   N_def   "N      == % (x1,x2,x3) (y1,y2,y3).
                        (~x1 & ~x2 & ~x3 &   y1 & ~y2 & ~y3) |   
	                ( x1 & ~x2 & ~x3 &  ~y1 & ~y2 & ~y3) |   
	                ( x1 & ~x2 & ~x3 &   y1 &  y2 &  y3)    "
  
  reach_def "reach  == mu (%Q x. INIT x | (? y. Q y & N y x))"

  (* always possible to return to the start state: has to be false *)
  restart_def "restart == AG N (EF N (%x. INIT x))"

  (* infinitily often through the second state: has to be true *)
  inf_def "infinitely == AG N (AF N (%x. fst x & ~ fst (snd x) & ~ snd (snd x)))"

  (* There is a path on which toggling between the first and second state that passes 
     infinitely often the first state: should be true, nested fixpoints!! *)
  toggle_def "toggle == FairEF N (%x. ~ fst (snd x) & ~ snd (snd x)) INIT"

end

