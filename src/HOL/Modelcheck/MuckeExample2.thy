(*  Title:      HOL/Modelcheck/MuckeExample2.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

theory MuckeExample2
imports MuckeSyn
begin

constdefs
  Init  :: "bool pred"
  "Init x == x"
  R     :: "[bool,bool] => bool"
  "R x y == (x & ~y) | (~x & y)"
  Reach :: "bool pred"
  "Reach == mu (%Q x. Init x | (? y. Q y & R y x))"
  Reach2:: "bool pred"
  "Reach2 == mu (%Q x. Reach x | (? y. Q y & R y x))"

lemmas Reach_rws = Init_def R_def Reach_def Reach2_def

lemma Reach: "Reach2 True"
  apply (tactic {* simp_tac (Mucke_ss addsimps (thms "Reach_rws")) 1 *})
  apply (tactic {* mc_mucke_tac [] 1 *})
  done

(*alternative:*)
lemma Reach': "Reach2 True"
  by (tactic {* mc_mucke_tac (thms "Reach_rws") 1 *})

end
