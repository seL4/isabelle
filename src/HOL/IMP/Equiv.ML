(*  Title:      HOL/IMP/Equiv.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

goal Equiv.thy "!n. (<a,s> -a-> n) = (n = A a s)";
by (aexp.induct_tac "a" 1);                               (* struct. ind. *)
by (ALLGOALS Simp_tac);                                   (* rewr. Den.   *)
by (TRYALL (fast_tac (set_cs addSIs (evala.intrs@prems)
                             addSEs evala_elim_cases)));
bind_thm("aexp_iff", result() RS spec);

goal Equiv.thy "!w. (<b,s> -b-> w) = (w = B b s)";
by (bexp.induct_tac "b" 1);
by (ALLGOALS(asm_simp_tac (!simpset addcongs [conj_cong]
                                    addsimps (aexp_iff::evalb_simps))));
bind_thm("bexp_iff", result() RS spec);

val equiv_cs =
 comp_cs addss (simpset_of "Prod" addsimps (aexp_iff::bexp_iff::evalc.intrs));

goal Equiv.thy "!!c. <c,s> -c-> t ==> (s,t) : C(c)";

(* start with rule induction *)
by (etac (evalc.mutual_induct RS spec RS spec RS spec RSN (2,rev_mp)) 1);
by (rewrite_tac (Gamma_def::C_simps));
  (* simplification with HOL_ss again too agressive *)
(* skip *)
by (fast_tac equiv_cs 1);
(* assign *)
by (fast_tac equiv_cs 1);
(* comp *)
by (fast_tac equiv_cs 1);
(* if *)
by (fast_tac equiv_cs 1);
by (fast_tac equiv_cs 1);
(* while *)
by (rtac (rewrite_rule [Gamma_def] (Gamma_mono RS lfp_Tarski RS ssubst)) 1);
by (fast_tac equiv_cs 1);
by (rtac (rewrite_rule [Gamma_def] (Gamma_mono RS lfp_Tarski RS ssubst)) 1);
by (fast_tac equiv_cs 1);

qed "com1";


goal Equiv.thy "!s t. (s,t):C(c) --> <c,s> -c-> t";
by (com.induct_tac "c" 1);
by (rewrite_tac C_simps);
by (ALLGOALS (TRY o fast_tac equiv_cs));

(* while *)
by (strip_tac 1);
by (etac (Gamma_mono RSN (2,induct)) 1);
by (rewtac Gamma_def);  
by (fast_tac equiv_cs 1);

bind_thm("com2", result() RS spec RS spec RS mp);


(**** Proof of Equivalence ****)

goal Equiv.thy "(s,t) : C(c)  =  (<c,s> -c-> t)";
by (fast_tac (set_cs addEs [com2] addDs [com1]) 1);
qed "com_equivalence";
