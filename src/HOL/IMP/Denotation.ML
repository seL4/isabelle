(*  Title: 	HOL/IMP/Denotation.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

open Denotation;

(**** Rewrite Rules for A,B,C ****)

val B_simps = map (fn t => t RS eq_reflection)
     [B_true,B_false,B_op,B_not,B_and,B_or]

val C_simps = map (fn t => t RS eq_reflection)
  [C_skip,C_assign,C_comp,C_if,C_while]; 

(**** mono (Gamma(b,c)) ****)

qed_goalw "Gamma_mono" Denotation.thy [mono_def,Gamma_def]
	"mono (Gamma b c)"
     (fn _ => [(best_tac comp_cs 1)]);
