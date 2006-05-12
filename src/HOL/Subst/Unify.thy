(*  ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

*)

header{*Unification Algorithm*}

theory Unify
imports Unifier
begin

text{*
Substitution and Unification in Higher-Order Logic.

Implements Manna and Waldinger's formalization, with Paulson's simplifications,
and some new simplifications by Slind.

Z Manna and R Waldinger, Deductive Synthesis of the Unification Algorithm.
SCP 1 (1981), 5-48

L C Paulson, Verifying the Unification Algorithm in LCF. SCP 5 (1985), 143-170
*}

consts

   unifyRel :: "(('a uterm * 'a uterm) * ('a uterm * 'a uterm)) set"
   unify    :: "'a uterm * 'a uterm => ('a * 'a uterm) list option"

defs
  unifyRel_def:
       "unifyRel == inv_image (finite_psubset <*lex*> measure uterm_size)
                               (%(M,N). (vars_of M Un vars_of N, M))"
   --{*Termination relation for the Unify function:
         either the set of variables decreases,
         or the first argument does (in fact, both do) *}

text{* Wellfoundedness of unifyRel *}
lemma wf_unifyRel [iff]: "wf unifyRel"
by (simp add: unifyRel_def wf_lex_prod wf_finite_psubset)


recdef (permissive) unify "unifyRel"
 unify_CC: "unify(Const m, Const n)  = (if (m=n) then Some[] else None)"
 unify_CB: "unify(Const m, Comb M N) = None"
 unify_CV: "unify(Const m, Var v)    = Some[(v,Const m)]"
 unify_V:  "unify(Var v, M) = (if (Var v \<prec> M) then None else Some[(v,M)])"
 unify_BC: "unify(Comb M N, Const x) = None"
 unify_BV: "unify(Comb M N, Var v)   = (if (Var v \<prec> Comb M N) then None
                                        else Some[(v,Comb M N)])"
 unify_BB:
  "unify(Comb M1 N1, Comb M2 N2) =
      (case unify(M1,M2)
        of None       => None
         | Some theta => (case unify(N1 \<lhd> theta, N2 \<lhd> theta)
                            of None       => None
                             | Some sigma => Some (theta \<lozenge> sigma)))"
  (hints recdef_wf: wf_unifyRel)


text{* This file defines a nested unification algorithm, then proves that it
 terminates, then proves 2 correctness theorems: that when the algorithm
 succeeds, it 1) returns an MGU; and 2) returns an idempotent substitution.
 Although the proofs may seem long, they are actually quite direct, in that
 the correctness and termination properties are not mingled as much as in
 previous proofs of this algorithm.*}

(*---------------------------------------------------------------------------
 * Our approach for nested recursive functions is as follows:
 *
 *    0. Prove the wellfoundedness of the termination relation.
 *    1. Prove the non-nested termination conditions.
 *    2. Eliminate (0) and (1) from the recursion equations and the
 *       induction theorem.
 *    3. Prove the nested termination conditions by using the induction
 *       theorem from (2) and by using the recursion equations from (2).
 *       These are constrained by the nested termination conditions, but
 *       things work out magically (by wellfoundedness of the termination
 *       relation).
 *    4. Eliminate the nested TCs from the results of (2).
 *    5. Prove further correctness properties using the results of (4).
 *
 * Deeper nestings require iteration of steps (3) and (4).
 *---------------------------------------------------------------------------*)

text{*The non-nested TC (terminiation condition).*}
recdef_tc unify_tc1: unify (1)
apply (simp add: unifyRel_def wf_lex_prod wf_finite_psubset, safe)
apply (simp add: finite_psubset_def finite_vars_of lex_prod_def inv_image_def)
apply (rule monotone_vars_of [THEN subset_iff_psubset_eq [THEN iffD1]])
done


text{*Termination proof.*}

lemma trans_unifyRel: "trans unifyRel"
by (simp add: unifyRel_def measure_def trans_inv_image trans_lex_prod
              trans_finite_psubset)


text{*The following lemma is used in the last step of the termination proof
for the nested call in Unify.  Loosely, it says that unifyRel doesn't care
about term structure.*}
lemma Rassoc:
  "((X,Y), (Comb A (Comb B C), Comb D (Comb E F))) \<in> unifyRel  ==>
   ((X,Y), (Comb (Comb A B) C, Comb (Comb D E) F)) \<in> unifyRel"
by (simp add: less_eq inv_image_def add_assoc Un_assoc
              unifyRel_def lex_prod_def)


text{*This lemma proves the nested termination condition for the base cases
 * 3, 4, and 6.*}
lemma var_elimR:
  "~(Var x \<prec> M) ==>
    ((N1 \<lhd> [(x,M)], N2 \<lhd> [(x,M)]), (Comb M N1, Comb(Var x) N2)) \<in> unifyRel
  & ((N1 \<lhd> [(x,M)], N2 \<lhd> [(x,M)]), (Comb(Var x) N1, Comb M N2)) \<in> unifyRel"
apply (case_tac "Var x = M", clarify, simp)
apply (case_tac "x \<in> (vars_of N1 Un vars_of N2)")
txt{*uterm_less case*}
apply (simp add: less_eq unifyRel_def lex_prod_def inv_image_def)
apply blast
txt{*@{text finite_psubset} case*}
apply (simp add: unifyRel_def lex_prod_def inv_image_def)
apply (simp add: finite_psubset_def finite_vars_of psubset_def)
apply blast
txt{*Final case, also @{text finite_psubset}*}
apply (simp add: finite_vars_of unifyRel_def finite_psubset_def lex_prod_def
                 inv_image_def)
apply (cut_tac s = "[(x,M)]" and v = x and t = N2 in Var_elim)
apply (cut_tac [3] s = "[(x,M)]" and v = x and t = N1 in Var_elim)
apply (simp_all (no_asm_simp) add: srange_iff vars_iff_occseq)
apply (auto elim!: Var_intro [THEN disjE] simp add: srange_iff)
done


text{*Eliminate tc1 from the recursion equations and the induction theorem.*}

lemmas unify_nonrec [simp] =
       unify_CC unify_CB unify_CV unify_V unify_BC unify_BV

lemmas unify_simps0 = unify_nonrec unify_BB [OF unify_tc1]

lemmas unify_induct0 = unify.induct [OF unify_tc1]

text{*The nested TC. The (2) requests the second one.
      Proved by recursion induction.*}
recdef_tc unify_tc2: unify (2)
txt{*The extracted TC needs the scope of its quantifiers adjusted, so our
 first step is to restrict the scopes of N1 and N2.*}
apply (subgoal_tac "\<forall>M1 M2 theta. unify (M1, M2) = Some theta -->
      (\<forall>N1 N2.((N1\<lhd>theta, N2\<lhd>theta), (Comb M1 N1, Comb M2 N2)) \<in> unifyRel)")
apply blast
apply (rule allI)
apply (rule allI)
txt{*Apply induction on this still-quantified formula*}
apply (rule_tac u = M1 and v = M2 in unify_induct0)
      apply (simp_all (no_asm_simp) add: var_elimR unify_simps0)
 txt{*Const-Const case*}
 apply (simp add: unifyRel_def lex_prod_def inv_image_def less_eq)
txt{*Comb-Comb case*}
apply (simp (no_asm_simp) split add: option.split)
apply (intro strip)
apply (rule trans_unifyRel [THEN transD], blast)
apply (simp only: subst_Comb [symmetric])
apply (rule Rassoc, blast)
done


text{* Now for elimination of nested TC from unify.simps and induction.*}

text{*Desired rule, copied from the theory file.*}
lemma unifyCombComb [simp]:
    "unify(Comb M1 N1, Comb M2 N2) =
       (case unify(M1,M2)
         of None => None
          | Some theta => (case unify(N1 \<lhd> theta, N2 \<lhd> theta)
                             of None => None
                              | Some sigma => Some (theta \<lozenge> sigma)))"
by (simp add: unify_tc2 unify_simps0 split add: option.split)

text{*The ML version had this, but it can't be used: we get
*** exception THM raised: transfer: not a super theory
All we can do is state the desired induction rule in full and prove it.*}
ML{*
bind_thm ("unify_induct",
	  rule_by_tactic
	     (ALLGOALS (full_simp_tac (simpset() addsimps [thm"unify_tc2"])))
	     (thm"unify_induct0"));
*}


text{*Correctness. Notice that idempotence is not needed to prove that the
algorithm terminates and is not needed to prove the algorithm correct, if you
are only interested in an MGU.  This is in contrast to the approach of M&W,
who used idempotence and MGU-ness in the termination proof.*}

theorem unify_gives_MGU [rule_format]:
     "\<forall>theta. unify(M,N) = Some theta --> MGUnifier theta M N"
apply (rule_tac u = M and v = N in unify_induct0)
    apply (simp_all (no_asm_simp))
    txt{*Const-Const case*}
    apply (simp add: MGUnifier_def Unifier_def)
   txt{*Const-Var case*}
   apply (subst mgu_sym)
   apply (simp add: MGUnifier_Var)
  txt{*Var-M case*}
  apply (simp add: MGUnifier_Var)
 txt{*Comb-Var case*}
 apply (subst mgu_sym)
 apply (simp add: MGUnifier_Var)
txt{*Comb-Comb case*}
apply (simp add: unify_tc2)
apply (simp (no_asm_simp) split add: option.split)
apply (intro strip)
apply (simp add: MGUnifier_def Unifier_def MoreGeneral_def)
apply (safe, rename_tac theta sigma gamma)
apply (erule_tac x = gamma in allE, erule (1) notE impE)
apply (erule exE, rename_tac delta)
apply (erule_tac x = delta in allE)
apply (subgoal_tac "N1 \<lhd> theta \<lhd> delta = N2 \<lhd> theta \<lhd> delta")
 apply (blast intro: subst_trans intro!: subst_cong comp_assoc[THEN subst_sym])
apply (simp add: subst_eq_iff)
done


text{*Unify returns idempotent substitutions, when it succeeds.*}
theorem unify_gives_Idem [rule_format]:
     "\<forall>theta. unify(M,N) = Some theta --> Idem theta"
apply (rule_tac u = M and v = N in unify_induct0)
apply (simp_all add: Var_Idem unify_tc2 split add: option.split)
txt{*Comb-Comb case*}
apply safe
apply (drule spec, erule (1) notE impE)+
apply (safe dest!: unify_gives_MGU [unfolded MGUnifier_def])
apply (rule Idem_comp, assumption+)
apply (force simp add: MoreGeneral_def subst_eq_iff Idem_def)
done

end
