(*  Title:      Sequents/LK.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Axiom to express monotonicity (a variant of the deduction theorem).  Makes the
link between |- and ==>, needed for instance to prove imp_cong.

Axiom left_cong allows the simplifier to use left-side formulas.  Ideally it
should be derived from lower-level axioms.

CANNOT be added to LK0.thy because modal logic is built upon it, and
various modal rules would become inconsistent.
*)

theory LK
imports LK0
uses ("simpdata.ML")
begin

axiomatization where
  monotonic:  "($H |- P ==> $H |- Q) ==> $H, P |- Q" and

  left_cong:  "[| P == P';  |- P' ==> ($H |- $F) == ($H' |- $F') |]
               ==> (P, $H |- $F) == (P', $H' |- $F')"


subsection {* Rewrite rules *}

lemma conj_simps:
  "|- P & True <-> P"
  "|- True & P <-> P"
  "|- P & False <-> False"
  "|- False & P <-> False"
  "|- P & P <-> P"
  "|- P & P & Q <-> P & Q"
  "|- P & ~P <-> False"
  "|- ~P & P <-> False"
  "|- (P & Q) & R <-> P & (Q & R)"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemma disj_simps:
  "|- P | True <-> True"
  "|- True | P <-> True"
  "|- P | False <-> P"
  "|- False | P <-> P"
  "|- P | P <-> P"
  "|- P | P | Q <-> P | Q"
  "|- (P | Q) | R <-> P | (Q | R)"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemma not_simps:
  "|- ~ False <-> True"
  "|- ~ True <-> False"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemma imp_simps:
  "|- (P --> False) <-> ~P"
  "|- (P --> True) <-> True"
  "|- (False --> P) <-> True"
  "|- (True --> P) <-> P"
  "|- (P --> P) <-> True"
  "|- (P --> ~P) <-> ~P"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemma iff_simps:
  "|- (True <-> P) <-> P"
  "|- (P <-> True) <-> P"
  "|- (P <-> P) <-> True"
  "|- (False <-> P) <-> ~P"
  "|- (P <-> False) <-> ~P"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemma quant_simps:
  "!!P. |- (ALL x. P) <-> P"
  "!!P. |- (ALL x. x=t --> P(x)) <-> P(t)"
  "!!P. |- (ALL x. t=x --> P(x)) <-> P(t)"
  "!!P. |- (EX x. P) <-> P"
  "!!P. |- (EX x. x=t & P(x)) <-> P(t)"
  "!!P. |- (EX x. t=x & P(x)) <-> P(t)"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done


subsection {* Miniscoping: pushing quantifiers in *}

text {*
  We do NOT distribute of ALL over &, or dually that of EX over |
  Baaz and Leitsch, On Skolemization and Proof Complexity (1994)
  show that this step can increase proof length!
*}

text {*existential miniscoping*}
lemma ex_simps:
  "!!P Q. |- (EX x. P(x) & Q) <-> (EX x. P(x)) & Q"
  "!!P Q. |- (EX x. P & Q(x)) <-> P & (EX x. Q(x))"
  "!!P Q. |- (EX x. P(x) | Q) <-> (EX x. P(x)) | Q"
  "!!P Q. |- (EX x. P | Q(x)) <-> P | (EX x. Q(x))"
  "!!P Q. |- (EX x. P(x) --> Q) <-> (ALL x. P(x)) --> Q"
  "!!P Q. |- (EX x. P --> Q(x)) <-> P --> (EX x. Q(x))"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

text {*universal miniscoping*}
lemma all_simps:
  "!!P Q. |- (ALL x. P(x) & Q) <-> (ALL x. P(x)) & Q"
  "!!P Q. |- (ALL x. P & Q(x)) <-> P & (ALL x. Q(x))"
  "!!P Q. |- (ALL x. P(x) --> Q) <-> (EX x. P(x)) --> Q"
  "!!P Q. |- (ALL x. P --> Q(x)) <-> P --> (ALL x. Q(x))"
  "!!P Q. |- (ALL x. P(x) | Q) <-> (ALL x. P(x)) | Q"
  "!!P Q. |- (ALL x. P | Q(x)) <-> P | (ALL x. Q(x))"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

text {*These are NOT supplied by default!*}
lemma distrib_simps:
  "|- P & (Q | R) <-> P&Q | P&R"
  "|- (Q | R) & P <-> Q&P | R&P"
  "|- (P | Q --> R) <-> (P --> R) & (Q --> R)"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemma P_iff_F: "|- ~P ==> |- (P <-> False)"
  apply (erule thinR [THEN cut])
  apply (tactic {* fast_tac LK_pack 1 *})
  done

lemmas iff_reflection_F = P_iff_F [THEN iff_reflection]

lemma P_iff_T: "|- P ==> |- (P <-> True)"
  apply (erule thinR [THEN cut])
  apply (tactic {* fast_tac LK_pack 1 *})
  done

lemmas iff_reflection_T = P_iff_T [THEN iff_reflection]


lemma LK_extra_simps:
  "|- P | ~P"
  "|- ~P | P"
  "|- ~ ~ P <-> P"
  "|- (~P --> P) <-> P"
  "|- (~P <-> ~Q) <-> (P<->Q)"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done


subsection {* Named rewrite rules *}

lemma conj_commute: "|- P&Q <-> Q&P"
  and conj_left_commute: "|- P&(Q&R) <-> Q&(P&R)"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemmas conj_comms = conj_commute conj_left_commute

lemma disj_commute: "|- P|Q <-> Q|P"
  and disj_left_commute: "|- P|(Q|R) <-> Q|(P|R)"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemmas disj_comms = disj_commute disj_left_commute

lemma conj_disj_distribL: "|- P&(Q|R) <-> (P&Q | P&R)"
  and conj_disj_distribR: "|- (P|Q)&R <-> (P&R | Q&R)"

  and disj_conj_distribL: "|- P|(Q&R) <-> (P|Q) & (P|R)"
  and disj_conj_distribR: "|- (P&Q)|R <-> (P|R) & (Q|R)"

  and imp_conj_distrib: "|- (P --> (Q&R)) <-> (P-->Q) & (P-->R)"
  and imp_conj: "|- ((P&Q)-->R)   <-> (P --> (Q --> R))"
  and imp_disj: "|- (P|Q --> R)   <-> (P-->R) & (Q-->R)"

  and imp_disj1: "|- (P-->Q) | R <-> (P-->Q | R)"
  and imp_disj2: "|- Q | (P-->R) <-> (P-->Q | R)"

  and de_Morgan_disj: "|- (~(P | Q)) <-> (~P & ~Q)"
  and de_Morgan_conj: "|- (~(P & Q)) <-> (~P | ~Q)"

  and not_iff: "|- ~(P <-> Q) <-> (P <-> ~Q)"
  apply (tactic {* ALLGOALS (fast_tac (LK_pack add_safes @{thms subst})) *})
  done

lemma imp_cong:
  assumes p1: "|- P <-> P'"
    and p2: "|- P' ==> |- Q <-> Q'"
  shows "|- (P-->Q) <-> (P'-->Q')"
  apply (tactic {* lemma_tac @{thm p1} 1 *})
  apply (tactic {* safe_tac LK_pack 1 *})
   apply (tactic {*
     REPEAT (rtac @{thm cut} 1 THEN
       DEPTH_SOLVE_1
         (resolve_tac [@{thm thinL}, @{thm thinR}, @{thm p2} COMP @{thm monotonic}] 1) THEN
           safe_tac LK_pack 1) *})
  done

lemma conj_cong:
  assumes p1: "|- P <-> P'"
    and p2: "|- P' ==> |- Q <-> Q'"
  shows "|- (P&Q) <-> (P'&Q')"
  apply (tactic {* lemma_tac @{thm p1} 1 *})
  apply (tactic {* safe_tac LK_pack 1 *})
   apply (tactic {*
     REPEAT (rtac @{thm cut} 1 THEN
       DEPTH_SOLVE_1
         (resolve_tac [@{thm thinL}, @{thm thinR}, @{thm p2} COMP @{thm monotonic}] 1) THEN
           safe_tac LK_pack 1) *})
  done

lemma eq_sym_conv: "|- (x=y) <-> (y=x)"
  apply (tactic {* fast_tac (LK_pack add_safes @{thms subst}) 1 *})
  done

use "simpdata.ML"
setup {* Simplifier.map_simpset_global (K LK_ss) *}


text {* To create substition rules *}

lemma eq_imp_subst: "|- a=b ==> $H, A(a), $G |- $E, A(b), $F"
  apply (tactic {* asm_simp_tac LK_basic_ss 1 *})
  done

lemma split_if: "|- P(if Q then x else y) <-> ((Q --> P(x)) & (~Q --> P(y)))"
  apply (rule_tac P = Q in cut)
   apply (tactic {* simp_tac (@{simpset} addsimps @{thms if_P}) 2 *})
  apply (rule_tac P = "~Q" in cut)
   apply (tactic {* simp_tac (@{simpset} addsimps @{thms if_not_P}) 2 *})
  apply (tactic {* fast_tac LK_pack 1 *})
  done

lemma if_cancel: "|- (if P then x else x) = x"
  apply (tactic {* lemma_tac @{thm split_if} 1 *})
  apply (tactic {* fast_tac LK_pack 1 *})
  done

lemma if_eq_cancel: "|- (if x=y then y else x) = x"
  apply (tactic {* lemma_tac @{thm split_if} 1 *})
  apply (tactic {* safe_tac LK_pack 1 *})
  apply (rule symL)
  apply (rule basic)
  done

end
