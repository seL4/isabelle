(*  Title:      HOL/IMP/Denotation.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Copyright   1994 TUM
*)

open Denotation;

val denotation_cs =  comp_cs addss (!simpset addsimps evalc.intrs);


(**** Rewrite Rules for C ****)

val C_simps = map (fn t => t RS eq_reflection)
  [C_skip,C_assign,C_comp,C_if,C_while]; 


(**** mono (Gamma(b,c)) ****)

qed_goalw "Gamma_mono" Denotation.thy [mono_def,Gamma_def]
        "mono (Gamma b c)"
     (fn _ => [(best_tac comp_cs 1)]);


goal Denotation.thy "C(WHILE b DO c) = C(IF b THEN c;WHILE b DO c ELSE SKIP)";
by(Simp_tac 1);
by(EVERY[stac (Gamma_mono RS lfp_Tarski) 1,
          stac (Gamma_def RS meta_eq_to_obj_eq RS fun_cong) 1,
	  Simp_tac 1,
	  IF_UNSOLVED no_tac]);
qed "C_While_If";


(* Operational Semantics implies Denotational Semantics *)

goal Denotation.thy "!!c s t. <c,s> -c-> t ==> (s,t) : C(c)";

(* start with rule induction *)
by (etac evalc.induct 1);
by (rewrite_tac (Gamma_def::C_simps));
  (* simplification with HOL_ss too agressive *)
(* skip *)
by (fast_tac denotation_cs 1);
(* assign *)
by (fast_tac denotation_cs 1);
(* comp *)
by (fast_tac denotation_cs 1);
(* if *)
by (fast_tac denotation_cs 1);
by (fast_tac denotation_cs 1);
(* while *)
by (rtac (rewrite_rule [Gamma_def] (Gamma_mono RS lfp_Tarski RS ssubst)) 1);
by (fast_tac denotation_cs 1);
by (rtac (rewrite_rule [Gamma_def] (Gamma_mono RS lfp_Tarski RS ssubst)) 1);
by (fast_tac denotation_cs 1);

qed "com1";


(* Denotational Semantics implies Operational Semantics *)

goal Denotation.thy "!s t. (s,t):C(c) --> <c,s> -c-> t";
by (com.induct_tac "c" 1);
by (rewrite_tac C_simps);
by (ALLGOALS (TRY o fast_tac denotation_cs));

(* while *)
by (strip_tac 1);
by (etac (Gamma_mono RSN (2,induct)) 1);
by (rewtac Gamma_def);  
by (fast_tac denotation_cs 1);

qed_spec_mp "com2";


(**** Proof of Equivalence ****)

goal Denotation.thy "(s,t) : C(c)  =  (<c,s> -c-> t)";
by (fast_tac (set_cs addEs [com2] addDs [com1]) 1);
qed "denotational_is_natural";
