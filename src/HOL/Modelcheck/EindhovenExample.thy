(*  Title:      HOL/Modelcheck/EindhovenExample.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

theory EindhovenExample
imports EindhovenSyn CTL
begin

types
  state = "bool * bool * bool"

constdefs
  INIT :: "state pred"
  "INIT x == ~(fst x)&~(fst (snd x))&~(snd (snd x))"

  N :: "[state,state] => bool"
  "N == % (x1,x2,x3) (y1,y2,y3).
      (~x1 & ~x2 & ~x3 &   y1 & ~y2 & ~y3) |
      ( x1 & ~x2 & ~x3 &  ~y1 & ~y2 & ~y3) |
      ( x1 & ~x2 & ~x3 &   y1 &  y2 &  y3)"

  reach:: "state pred"
  "reach  == mu (%Q x. INIT x | (? y. Q y & N y x))"

lemma init_state: "INIT (a, b, c) = (~a & ~b &~c)"
  by (simp add: INIT_def)


lemmas reach_rws = reach_def INIT_def N_def

lemma reach_ex: "reach (True, True, True)"
  apply (tactic {* simp_tac (Eindhoven_ss addsimps (thms "reach_rws")) 1 *})
  txt {* the current proof state using the model checker syntax: @{subgoals [mode=Eindhoven]} *}
  pr (Eindhoven)
  txt {* actually invoke the model checker, try out after installing
    the model checker: see the README file *}
  apply (tactic {* mc_eindhoven_tac 1 *})
  done

end
