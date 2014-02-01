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
  by (fast add!: subst)+

lemma disj_simps:
  "|- P | True <-> True"
  "|- True | P <-> True"
  "|- P | False <-> P"
  "|- False | P <-> P"
  "|- P | P <-> P"
  "|- P | P | Q <-> P | Q"
  "|- (P | Q) | R <-> P | (Q | R)"
  by (fast add!: subst)+

lemma not_simps:
  "|- ~ False <-> True"
  "|- ~ True <-> False"
  by (fast add!: subst)+

lemma imp_simps:
  "|- (P --> False) <-> ~P"
  "|- (P --> True) <-> True"
  "|- (False --> P) <-> True"
  "|- (True --> P) <-> P"
  "|- (P --> P) <-> True"
  "|- (P --> ~P) <-> ~P"
  by (fast add!: subst)+

lemma iff_simps:
  "|- (True <-> P) <-> P"
  "|- (P <-> True) <-> P"
  "|- (P <-> P) <-> True"
  "|- (False <-> P) <-> ~P"
  "|- (P <-> False) <-> ~P"
  by (fast add!: subst)+

lemma quant_simps:
  "!!P. |- (ALL x. P) <-> P"
  "!!P. |- (ALL x. x=t --> P(x)) <-> P(t)"
  "!!P. |- (ALL x. t=x --> P(x)) <-> P(t)"
  "!!P. |- (EX x. P) <-> P"
  "!!P. |- (EX x. x=t & P(x)) <-> P(t)"
  "!!P. |- (EX x. t=x & P(x)) <-> P(t)"
  by (fast add!: subst)+


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
  by (fast add!: subst)+

text {*universal miniscoping*}
lemma all_simps:
  "!!P Q. |- (ALL x. P(x) & Q) <-> (ALL x. P(x)) & Q"
  "!!P Q. |- (ALL x. P & Q(x)) <-> P & (ALL x. Q(x))"
  "!!P Q. |- (ALL x. P(x) --> Q) <-> (EX x. P(x)) --> Q"
  "!!P Q. |- (ALL x. P --> Q(x)) <-> P --> (ALL x. Q(x))"
  "!!P Q. |- (ALL x. P(x) | Q) <-> (ALL x. P(x)) | Q"
  "!!P Q. |- (ALL x. P | Q(x)) <-> P | (ALL x. Q(x))"
  by (fast add!: subst)+

text {*These are NOT supplied by default!*}
lemma distrib_simps:
  "|- P & (Q | R) <-> P&Q | P&R"
  "|- (Q | R) & P <-> Q&P | R&P"
  "|- (P | Q --> R) <-> (P --> R) & (Q --> R)"
  by (fast add!: subst)+

lemma P_iff_F: "|- ~P ==> |- (P <-> False)"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemmas iff_reflection_F = P_iff_F [THEN iff_reflection]

lemma P_iff_T: "|- P ==> |- (P <-> True)"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemmas iff_reflection_T = P_iff_T [THEN iff_reflection]


lemma LK_extra_simps:
  "|- P | ~P"
  "|- ~P | P"
  "|- ~ ~ P <-> P"
  "|- (~P --> P) <-> P"
  "|- (~P <-> ~Q) <-> (P<->Q)"
  by (fast add!: subst)+


subsection {* Named rewrite rules *}

lemma conj_commute: "|- P&Q <-> Q&P"
  and conj_left_commute: "|- P&(Q&R) <-> Q&(P&R)"
  by (fast add!: subst)+

lemmas conj_comms = conj_commute conj_left_commute

lemma disj_commute: "|- P|Q <-> Q|P"
  and disj_left_commute: "|- P|(Q|R) <-> Q|(P|R)"
  by (fast add!: subst)+

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
  by (fast add!: subst)+

lemma imp_cong:
  assumes p1: "|- P <-> P'"
    and p2: "|- P' ==> |- Q <-> Q'"
  shows "|- (P-->Q) <-> (P'-->Q')"
  apply (lem p1)
  apply safe
   apply (tactic {*
     REPEAT (rtac @{thm cut} 1 THEN
       DEPTH_SOLVE_1
         (resolve_tac [@{thm thinL}, @{thm thinR}, @{thm p2} COMP @{thm monotonic}] 1) THEN
           Cla.safe_tac @{context} 1) *})
  done

lemma conj_cong:
  assumes p1: "|- P <-> P'"
    and p2: "|- P' ==> |- Q <-> Q'"
  shows "|- (P&Q) <-> (P'&Q')"
  apply (lem p1)
  apply safe
   apply (tactic {*
     REPEAT (rtac @{thm cut} 1 THEN
       DEPTH_SOLVE_1
         (resolve_tac [@{thm thinL}, @{thm thinR}, @{thm p2} COMP @{thm monotonic}] 1) THEN
           Cla.safe_tac @{context} 1) *})
  done

lemma eq_sym_conv: "|- (x=y) <-> (y=x)"
  by (fast add!: subst)

ML_file "simpdata.ML"
setup {* map_theory_simpset (put_simpset LK_ss) *}
setup {* Simplifier.method_setup [] *}


text {* To create substition rules *}

lemma eq_imp_subst: "|- a=b ==> $H, A(a), $G |- $E, A(b), $F"
  by simp

lemma split_if: "|- P(if Q then x else y) <-> ((Q --> P(x)) & (~Q --> P(y)))"
  apply (rule_tac P = Q in cut)
   prefer 2
   apply (simp add: if_P)
  apply (rule_tac P = "~Q" in cut)
   prefer 2
   apply (simp add: if_not_P)
  apply fast
  done

lemma if_cancel: "|- (if P then x else x) = x"
  apply (lem split_if)
  apply fast
  done

lemma if_eq_cancel: "|- (if x=y then y else x) = x"
  apply (lem split_if)
  apply safe
  apply (rule symL)
  apply (rule basic)
  done

end
