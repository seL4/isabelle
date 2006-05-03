(*  Title:      HOLCF/IOA/meta_theory/Sequence.ML
    ID:         $Id$
    Author:     Olaf Mller
*)

(* ----------------------------------------------------------------------------------- *)

fun Seq_case_tac s i = res_inst_tac [("x",s)] Seq_cases i
          THEN hyp_subst_tac i THEN hyp_subst_tac (i+1) THEN hyp_subst_tac (i+2);

(* on a>>s only simp_tac, as full_simp_tac is uncomplete and often causes errors *)
fun Seq_case_simp_tac s i = Seq_case_tac s i THEN Asm_simp_tac (i+2)
                                             THEN Asm_full_simp_tac (i+1)
                                             THEN Asm_full_simp_tac i;

(* rws are definitions to be unfolded for admissibility check *)
fun Seq_induct_tac s rws i = res_inst_tac [("x",s)] Seq_induct i
                         THEN (REPEAT_DETERM (CHANGED (Asm_simp_tac (i+1))))
                         THEN simp_tac (simpset() addsimps rws) i;

fun Seq_Finite_induct_tac i = etac Seq_Finite_ind i
                              THEN (REPEAT_DETERM (CHANGED (Asm_simp_tac i)));

fun pair_tac s = res_inst_tac [("p",s)] PairE
                          THEN' hyp_subst_tac THEN' Asm_full_simp_tac;

(* induction on a sequence of pairs with pairsplitting and simplification *)
fun pair_induct_tac s rws i =
           res_inst_tac [("x",s)] Seq_induct i
           THEN pair_tac "a" (i+3)
           THEN (REPEAT_DETERM (CHANGED (Simp_tac (i+1))))
           THEN simp_tac (simpset() addsimps rws) i;
