(*  Title:      HOL/Modelcheck/MuckeExample1.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

theory MuckeExample1
imports MuckeSyn
begin

types
  state = "bool * bool * bool"

constdefs
  INIT :: "state pred"
  "INIT x ==  ~(fst x)&~(fst (snd x))&~(snd (snd x))"
  N    :: "[state,state] => bool"
  "N x y == let x1 = fst(x); x2 = fst(snd(x)); x3 = snd(snd(x));
                y1 = fst(y); y2 = fst(snd(y)); y3 = snd(snd(y))
            in (~x1&~x2&~x3 & y1&~y2&~y3) |
               (x1&~x2&~x3 & ~y1&~y2&~y3) |
               (x1&~x2&~x3 & y1&y2&y3)"
  reach:: "state pred"
  "reach  == mu (%Q x. INIT x | (? y. Q y & N y x))"

lemmas reach_rws = INIT_def N_def reach_def

lemma reach_ex1: "reach (True,True,True)"
  apply (tactic {* simp_tac (Mucke_ss addsimps (thms "reach_rws")) 1 *})
  apply (tactic {* mc_mucke_tac [] 1 *})
  done

(*alternative*)
lemma reach_ex' "reach (True,True,True)"
  by (tactic {* mc_mucke_tac (thms "reach_rws") 1 *})

end
