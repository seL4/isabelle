(*  Title:      HOL/Modelcheck/MuckeExample1.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

MuckeExample1 = MuckeSyn + 



types
    state = "bool * bool * bool"

consts

  INIT :: "state pred"
  N    :: "[state,state] => bool"
  reach:: "state pred"

defs
  
  INIT_def "INIT x ==  ~(fst x)&~(fst (snd x))&~(snd (snd x))"

  N_def   "N x y == let x1 = fst(x); x2 = fst(snd(x)); x3 = snd(snd(x));   
	                  y1 = fst(y); y2 = fst(snd(y)); y3 = snd(snd(y)) 
                     in (~x1&~x2&~x3 & y1&~y2&~y3) |   
	                (x1&~x2&~x3 & ~y1&~y2&~y3) |   
	                (x1&~x2&~x3 & y1&y2&y3)    "
  
  reach_def "reach  == mu (%Q x. INIT x | (? y. Q y & N y x))"
  

end

