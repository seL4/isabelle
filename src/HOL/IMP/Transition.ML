(*  Title:      HOL/IMP/Transition.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner, TUM
    Copyright   1996 TUM

Equivalence of Natural and Transition semantics
*)

open Transition;

val relpow_cs = rel_cs addSEs [rel_pow_0_E];

val evalc1_elim_cases = map (evalc1.mk_cases com.simps)
   ["(SKIP,s) -1-> t", "(x:=a,s) -1-> t", "(c1;c2, s) -1-> t",
    "(IF b THEN c1 ELSE c2, s) -1-> t", "(WHILE b DO c,s) -1-> t"];

val evalc1_cs = relpow_cs addIs (evalc.intrs@evalc1.intrs);

goal Transition.thy "!!c. (c,s) -(0)-> (SKIP,u) ==> c = SKIP & s = u";
by(fast_tac evalc1_cs 1);
val hlemma1 = result();

goal Transition.thy "!!s. (SKIP,s) -(m)-> (SKIP,t) ==> s = t & m = 0";
be rel_pow_E2 1;
by (Asm_full_simp_tac 1);
by (eresolve_tac evalc1_elim_cases 1);
val hlemma2 = result();


goal Transition.thy
  "!s t u c d. (c,s) -(n)-> (SKIP,t) --> (d,t) -*-> (SKIP,u) --> \
\              (c;d, s) -*-> (SKIP, u)";
by(nat_ind_tac "n" 1);
 (* case n = 0 *)
 by(fast_tac (evalc1_cs addIs [rtrancl_into_rtrancl2])1);
(* induction step *)
by (safe_tac (HOL_cs addSDs [rel_pow_Suc_D2]));
by(split_all_tac 1);
by(fast_tac (evalc1_cs addIs [rtrancl_into_rtrancl2]) 1);
qed_spec_mp "lemma1";


goal Transition.thy "!c s s1. <c,s> -c-> s1 --> (c,s) -*-> (SKIP,s1)";
br evalc.mutual_induct 1;

(* SKIP *)
br rtrancl_refl 1;

(* ASSIGN *)
by (fast_tac (evalc1_cs addSIs [r_into_rtrancl]) 1);

(* SEMI *)
by (fast_tac (set_cs addDs [rtrancl_imp_UN_rel_pow] addIs [lemma1]) 1);

(* IF *)
by (fast_tac (evalc1_cs addIs [rtrancl_into_rtrancl2]) 1);
by (fast_tac (evalc1_cs addIs [rtrancl_into_rtrancl2]) 1);

(* WHILE *)
by (fast_tac (evalc1_cs addSIs [r_into_rtrancl]) 1);
by (fast_tac (evalc1_cs addDs [rtrancl_imp_UN_rel_pow]
                        addIs [rtrancl_into_rtrancl2,lemma1]) 1);

qed_spec_mp "evalc_impl_evalc1";


goal Transition.thy
  "!c d s u. (c;d,s) -(n)-> (SKIP,u) --> \
\            (? t m. (c,s) -*-> (SKIP,t) & (d,t) -(m)-> (SKIP,u) & m <= n)";
by(nat_ind_tac "n" 1);
 (* case n = 0 *)
 by (fast_tac (HOL_cs addSDs [hlemma1] addss !simpset) 1);
(* induction step *)
by (fast_tac (HOL_cs addSIs [rtrancl_refl,le_SucI,le_refl]
                     addSDs [rel_pow_Suc_D2]
                     addSEs (evalc1_elim_cases@
                             [rel_pow_imp_rtrancl,rtrancl_into_rtrancl2])) 1);
qed_spec_mp "lemma2";

goal Transition.thy "!s t. (c,s) -*-> (SKIP,t) --> <c,s> -c-> t";
by (com.induct_tac "c" 1);
by (safe_tac (evalc1_cs addSDs [rtrancl_imp_UN_rel_pow]));

(* SKIP *)
by (fast_tac (evalc1_cs addSEs rel_pow_E2::evalc1_elim_cases) 1);

(* ASSIGN *)
by (fast_tac (evalc1_cs addSDs [hlemma2]
                        addSEs rel_pow_E2::evalc1_elim_cases
                        addss !simpset) 1);

(* SEMI *)
by (fast_tac (evalc1_cs addSDs [lemma2,rel_pow_imp_rtrancl]) 1);

(* IF *)
be rel_pow_E2 1;
by (Asm_full_simp_tac 1);
by (fast_tac (evalc1_cs addSDs[rel_pow_imp_rtrancl]addEs evalc1_elim_cases) 1);

(* WHILE, induction on the length of the computation *)
by(rotate_tac 1 1);
by (etac rev_mp 1);
by (res_inst_tac [("x","s")] spec 1);
by(res_inst_tac [("n","n")] less_induct 1);
by (strip_tac 1);
be rel_pow_E2 1;
 by (Asm_full_simp_tac 1);
by (eresolve_tac evalc1_elim_cases 1);

(* WhileFalse *)
 by (fast_tac (evalc1_cs addSDs [hlemma2]) 1);

(* WhileTrue *)
by(fast_tac(evalc1_cs addSDs[lemma2,le_imp_less_or_eq,less_Suc_eq RS iffD2])1);

qed_spec_mp "evalc1_impl_evalc";


(**** proof of the equivalence of evalc and evalc1 ****)

goal Transition.thy "((c, s) -*-> (SKIP, t)) = (<c,s> -c-> t)";
by (fast_tac (HOL_cs addSEs [evalc1_impl_evalc,evalc_impl_evalc1]) 1);
qed "evalc1_eq_evalc";
