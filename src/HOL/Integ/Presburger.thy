(*  Title:      HOL/Integ/Presburger.thy
    ID:         $Id$
    Author:     Amine Chaieb, Tobias Nipkow and Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

File containing necessary theorems for the proof
generation for Cooper Algorithm  
*)

header {* Presburger Arithmetic: Cooper Algorithm *}

theory Presburger = NatSimprocs + SetInterval
files
  ("cooper_dec.ML")
  ("cooper_proof.ML")
  ("qelim.ML")
  ("presburger.ML"):

text {* Theorem for unitifying the coeffitients of @{text x} in an existential formula*}

theorem unity_coeff_ex: "(\<exists>x::int. P (l * x)) = (\<exists>x. l dvd (1*x+0) \<and> P x)"
  apply (rule iffI)
  apply (erule exE)
  apply (rule_tac x = "l * x" in exI)
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply (erule dvdE)
  apply (rule_tac x = k in exI)
  apply simp
  done

lemma uminus_dvd_conv: "(d dvd (t::int)) = (-d dvd t)"
apply(unfold dvd_def)
apply(rule iffI)
apply(clarsimp)
apply(rename_tac k)
apply(rule_tac x = "-k" in exI)
apply simp
apply(clarsimp)
apply(rename_tac k)
apply(rule_tac x = "-k" in exI)
apply simp
done

lemma uminus_dvd_conv': "(d dvd (t::int)) = (d dvd -t)"
apply(unfold dvd_def)
apply(rule iffI)
apply(clarsimp)
apply(rule_tac x = "-k" in exI)
apply simp
apply(clarsimp)
apply(rule_tac x = "-k" in exI)
apply simp
done



text {*Theorems for the combination of proofs of the equality of @{text P} and @{text P_m} for integers @{text x} less than some integer @{text z}.*}

theorem eq_minf_conjI: "\<exists>z1::int. \<forall>x. x < z1 \<longrightarrow> (A1 x = A2 x) \<Longrightarrow>
  \<exists>z2::int. \<forall>x. x < z2 \<longrightarrow> (B1 x = B2 x) \<Longrightarrow>
  \<exists>z::int. \<forall>x. x < z \<longrightarrow> ((A1 x \<and> B1 x) = (A2 x \<and> B2 x))"
  apply (erule exE)+
  apply (rule_tac x = "min z1 z2" in exI)
  apply simp
  done


theorem eq_minf_disjI: "\<exists>z1::int. \<forall>x. x < z1 \<longrightarrow> (A1 x = A2 x) \<Longrightarrow>
  \<exists>z2::int. \<forall>x. x < z2 \<longrightarrow> (B1 x = B2 x) \<Longrightarrow>
  \<exists>z::int. \<forall>x. x < z \<longrightarrow> ((A1 x \<or> B1 x) = (A2 x \<or> B2 x))"

  apply (erule exE)+
  apply (rule_tac x = "min z1 z2" in exI)
  apply simp
  done


text {*Theorems for the combination of proofs of the equality of @{text P} and @{text P_m} for integers @{text x} greather than some integer @{text z}.*}

theorem eq_pinf_conjI: "\<exists>z1::int. \<forall>x. z1 < x \<longrightarrow> (A1 x = A2 x) \<Longrightarrow>
  \<exists>z2::int. \<forall>x. z2 < x \<longrightarrow> (B1 x = B2 x) \<Longrightarrow>
  \<exists>z::int. \<forall>x. z < x \<longrightarrow> ((A1 x \<and> B1 x) = (A2 x \<and> B2 x))"
  apply (erule exE)+
  apply (rule_tac x = "max z1 z2" in exI)
  apply simp
  done


theorem eq_pinf_disjI: "\<exists>z1::int. \<forall>x. z1 < x \<longrightarrow> (A1 x = A2 x) \<Longrightarrow>
  \<exists>z2::int. \<forall>x. z2 < x \<longrightarrow> (B1 x = B2 x) \<Longrightarrow>
  \<exists>z::int. \<forall>x. z < x  \<longrightarrow> ((A1 x \<or> B1 x) = (A2 x \<or> B2 x))"
  apply (erule exE)+
  apply (rule_tac x = "max z1 z2" in exI)
  apply simp
  done

text {*
  \medskip Theorems for the combination of proofs of the modulo @{text
  D} property for @{text "P plusinfinity"}

  FIXME: This is THE SAME theorem as for the @{text minusinf} version,
  but with @{text "+k.."} instead of @{text "-k.."} In the future
  replace these both with only one. *}

theorem modd_pinf_conjI: "\<forall>(x::int) k. A x = A (x+k*d) \<Longrightarrow>
  \<forall>(x::int) k. B x = B (x+k*d) \<Longrightarrow>
  \<forall>(x::int) (k::int). (A x \<and> B x) = (A (x+k*d) \<and> B (x+k*d))"
  by simp

theorem modd_pinf_disjI: "\<forall>(x::int) k. A x = A (x+k*d) \<Longrightarrow>
  \<forall>(x::int) k. B x = B (x+k*d) \<Longrightarrow>
  \<forall>(x::int) (k::int). (A x \<or> B x) = (A (x+k*d) \<or> B (x+k*d))"
  by simp

text {*
  This is one of the cases where the simplifed formula is prooved to
  habe some property (in relation to @{text P_m}) but we need to prove
  the property for the original formula (@{text P_m})

  FIXME: This is exaclty the same thm as for @{text minusinf}. *}

lemma pinf_simp_eq: "ALL x. P(x) = Q(x) ==> (EX (x::int). P(x)) --> (EX (x::int). F(x))  ==> (EX (x::int). Q(x)) --> (EX (x::int). F(x)) "
  by blast


text {*
  \medskip Theorems for the combination of proofs of the modulo @{text D}
  property for @{text "P minusinfinity"} *}

theorem modd_minf_conjI: "\<forall>(x::int) k. A x = A (x-k*d) \<Longrightarrow>
  \<forall>(x::int) k. B x = B (x-k*d) \<Longrightarrow>
  \<forall>(x::int) (k::int). (A x \<and> B x) = (A (x-k*d) \<and> B (x-k*d))"
  by simp

theorem modd_minf_disjI: "\<forall>(x::int) k. A x = A (x-k*d) \<Longrightarrow>
  \<forall>(x::int) k. B x = B (x-k*d) \<Longrightarrow>
  \<forall>(x::int) (k::int). (A x \<or> B x) = (A (x-k*d) \<or> B (x-k*d))"
  by simp

text {*
  This is one of the cases where the simplifed formula is prooved to
  have some property (in relation to @{text P_m}) but we need to
  prove the property for the original formula (@{text P_m}). *}

lemma minf_simp_eq: "ALL x. P(x) = Q(x) ==> (EX (x::int). P(x)) --> (EX (x::int). F(x))  ==> (EX (x::int). Q(x)) --> (EX (x::int). F(x)) "
  by blast

text {*
  Theorem needed for proving at runtime divide properties using the
  arithmetic tactic (which knows only about modulo = 0). *}

lemma zdvd_iff_zmod_eq_0: "(m dvd n) = (n mod m = (0::int))"
  by(simp add:dvd_def zmod_eq_0_iff)

text {*
  \medskip Theorems used for the combination of proof for the
  backwards direction of Cooper's Theorem. They rely exclusively on
  Predicate calculus.*}

lemma not_ast_p_disjI: "(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> P1(x) --> P1(x + d))
==>
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> P2(x) --> P2(x + d))
==>
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) -->(P1(x) \<or> P2(x)) --> (P1(x + d) \<or> P2(x + d))) "
  by blast


lemma not_ast_p_conjI: "(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a- j)) --> P1(x) --> P1(x + d))
==>
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> P2(x) --> P2(x + d))
==>
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) -->(P1(x) \<and> P2(x)) --> (P1(x + d)
\<and> P2(x + d))) "
  by blast

lemma not_ast_p_Q_elim: "
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) -->P(x) --> P(x + d))
==> ( P = Q )
==> (ALL x. ~(EX (j::int) : {1..d}. EX (a::int) : A. P(a - j)) -->P(x) --> P(x + d))"
  by blast

text {*
  \medskip Theorems used for the combination of proof for the
  backwards direction of Cooper's Theorem. They rely exclusively on
  Predicate calculus.*}

lemma not_bst_p_disjI: "(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> P1(x) --> P1(x - d))
==>
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> P2(x) --> P2(x - d))
==>
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) -->(P1(x) \<or> P2(x)) --> (P1(x - d)
\<or> P2(x-d))) "
  by blast

lemma not_bst_p_conjI: "(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> P1(x) --> P1(x - d))
==>
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> P2(x) --> P2(x - d))
==>
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) -->(P1(x) \<and> P2(x)) --> (P1(x - d)
\<and> P2(x-d))) "
  by blast

lemma not_bst_p_Q_elim: "
(ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) -->P(x) --> P(x - d)) 
==> ( P = Q )
==> (ALL x. ~(EX (j::int) : {1..d}. EX (b::int) : B. P(b+j)) -->P(x) --> P(x - d))"
  by blast

text {* \medskip This is the first direction of Cooper's Theorem. *}
lemma cooper_thm: "(R --> (EX x::int. P x))  ==> (Q -->(EX x::int.  P x )) ==> ((R|Q) --> (EX x::int. P x )) "
  by blast

text {*
  \medskip The full Cooper's Theorem in its equivalence Form. Given
  the premises it is trivial too, it relies exclusively on prediacte calculus.*}
lemma cooper_eq_thm: "(R --> (EX x::int. P x))  ==> (Q -->(EX x::int.  P x )) ==> ((~Q)
--> (EX x::int. P x ) --> R) ==> (EX x::int. P x) = R|Q "
  by blast

text {*
  \medskip Some of the atomic theorems generated each time the atom
  does not depend on @{text x}, they are trivial.*}

lemma  fm_eq_minf: "EX z::int. ALL x. x < z --> (P = P) "
  by blast

lemma  fm_modd_minf: "ALL (x::int). ALL (k::int). (P = P)"
  by blast

lemma not_bst_p_fm: "ALL (x::int). Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> fm --> fm"
  by blast

lemma  fm_eq_pinf: "EX z::int. ALL x. z < x --> (P = P) "
  by blast

text {* The next two thms are the same as the @{text minusinf} version. *}

lemma  fm_modd_pinf: "ALL (x::int). ALL (k::int). (P = P)"
  by blast

lemma not_ast_p_fm: "ALL (x::int). Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> fm --> fm"
  by blast

text {* Theorems to be deleted from simpset when proving simplified formulaes. *}

lemma P_eqtrue: "(P=True) = P"
  by rules

lemma P_eqfalse: "(P=False) = (~P)"
  by rules

text {*
  \medskip Theorems for the generation of the bachwards direction of
  Cooper's Theorem.

  These are the 6 interesting atomic cases which have to be proved relying on the
  properties of B-set and the arithmetic and contradiction proofs. *}

lemma not_bst_p_lt: "0 < (d::int) ==>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> ( 0 < -x + a) --> (0 < -(x - d) + a )"
  by arith

lemma not_bst_p_gt: "\<lbrakk> (g::int) \<in> B; g = -a \<rbrakk> \<Longrightarrow>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> (0 < (x) + a) --> ( 0 < (x - d) + a)"
apply clarsimp
apply(rule ccontr)
apply(drule_tac x = "x+a" in bspec)
apply(simp add:atLeastAtMost_iff)
apply(drule_tac x = "-a" in bspec)
apply assumption
apply(simp)
done

lemma not_bst_p_eq: "\<lbrakk> 0 < d; (g::int) \<in> B; g = -a - 1 \<rbrakk> \<Longrightarrow>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> (0 = x + a) --> (0 = (x - d) + a )"
apply clarsimp
apply(subgoal_tac "x = -a")
 prefer 2 apply arith
apply(drule_tac x = "1" in bspec)
apply(simp add:atLeastAtMost_iff)
apply(drule_tac x = "-a- 1" in bspec)
apply assumption
apply(simp)
done


lemma not_bst_p_ne: "\<lbrakk> 0 < d; (g::int) \<in> B; g = -a \<rbrakk> \<Longrightarrow>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> ~(0 = x + a) --> ~(0 = (x - d) + a)"
apply clarsimp
apply(subgoal_tac "x = -a+d")
 prefer 2 apply arith
apply(drule_tac x = "d" in bspec)
apply(simp add:atLeastAtMost_iff)
apply(drule_tac x = "-a" in bspec)
apply assumption
apply(simp)
done


lemma not_bst_p_dvd: "(d1::int) dvd d ==>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> d1 dvd (x + a) --> d1 dvd ((x - d) + a )"
apply(clarsimp simp add:dvd_def)
apply(rename_tac m)
apply(rule_tac x = "m - k" in exI)
apply(simp add:int_distrib)
done

lemma not_bst_p_ndvd: "(d1::int) dvd d ==>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (b::int) : B. Q(b+j)) --> ~(d1 dvd (x + a)) --> ~(d1 dvd ((x - d) + a ))"
apply(clarsimp simp add:dvd_def)
apply(rename_tac m)
apply(erule_tac x = "m + k" in allE)
apply(simp add:int_distrib)
done

text {*
  \medskip Theorems for the generation of the bachwards direction of
  Cooper's Theorem.

  These are the 6 interesting atomic cases which have to be proved
  relying on the properties of A-set ant the arithmetic and
  contradiction proofs. *}

lemma not_ast_p_gt: "0 < (d::int) ==>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> ( 0 < x + t) --> (0 < (x + d) + t )"
  by arith

lemma not_ast_p_lt: "\<lbrakk>0 < d ;(t::int) \<in> A \<rbrakk> \<Longrightarrow>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> (0 < -x + t) --> ( 0 < -(x + d) + t)"
  apply clarsimp
  apply (rule ccontr)
  apply (drule_tac x = "t-x" in bspec)
  apply simp
  apply (drule_tac x = "t" in bspec)
  apply assumption
  apply simp
  done

lemma not_ast_p_eq: "\<lbrakk> 0 < d; (g::int) \<in> A; g = -t + 1 \<rbrakk> \<Longrightarrow>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> (0 = x + t) --> (0 = (x + d) + t )"
  apply clarsimp
  apply (drule_tac x="1" in bspec)
  apply simp
  apply (drule_tac x="- t + 1" in bspec)
  apply assumption
  apply(subgoal_tac "x = -t")
  prefer 2 apply arith
  apply simp
  done

lemma not_ast_p_ne: "\<lbrakk> 0 < d; (g::int) \<in> A; g = -t \<rbrakk> \<Longrightarrow>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> ~(0 = x + t) --> ~(0 = (x + d) + t)"
  apply clarsimp
  apply (subgoal_tac "x = -t-d")
  prefer 2 apply arith
  apply (drule_tac x = "d" in bspec)
  apply simp
  apply (drule_tac x = "-t" in bspec)
  apply assumption
  apply simp
  done

lemma not_ast_p_dvd: "(d1::int) dvd d ==>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> d1 dvd (x + t) --> d1 dvd ((x + d) + t )"
  apply(clarsimp simp add:dvd_def)
  apply(rename_tac m)
  apply(rule_tac x = "m + k" in exI)
  apply(simp add:int_distrib)
  done

lemma not_ast_p_ndvd: "(d1::int) dvd d ==>
 ALL x. Q(x::int) \<and> ~(EX (j::int) : {1..d}. EX (a::int) : A. Q(a - j)) --> ~(d1 dvd (x + t)) --> ~(d1 dvd ((x + d) + t ))"
  apply(clarsimp simp add:dvd_def)
  apply(rename_tac m)
  apply(erule_tac x = "m - k" in allE)
  apply(simp add:int_distrib)
  done

text {*
  \medskip These are the atomic cases for the proof generation for the
  modulo @{text D} property for @{text "P plusinfinity"}

  They are fully based on arithmetics. *}

lemma  dvd_modd_pinf: "((d::int) dvd d1) ==>
 (ALL (x::int). ALL (k::int). (((d::int) dvd (x + t)) = (d dvd (x+k*d1 + t))))"
  apply(clarsimp simp add:dvd_def)
  apply(rule iffI)
  apply(clarsimp)
  apply(rename_tac n m)
  apply(rule_tac x = "m + n*k" in exI)
  apply(simp add:int_distrib)
  apply(clarsimp)
  apply(rename_tac n m)
  apply(rule_tac x = "m - n*k" in exI)
  apply(simp add:int_distrib mult_ac)
  done

lemma  not_dvd_modd_pinf: "((d::int) dvd d1) ==>
 (ALL (x::int). ALL k. (~((d::int) dvd (x + t))) = (~(d dvd (x+k*d1 + t))))"
  apply(clarsimp simp add:dvd_def)
  apply(rule iffI)
  apply(clarsimp)
  apply(rename_tac n m)
  apply(erule_tac x = "m - n*k" in allE)
  apply(simp add:int_distrib mult_ac)
  apply(clarsimp)
  apply(rename_tac n m)
  apply(erule_tac x = "m + n*k" in allE)
  apply(simp add:int_distrib mult_ac)
  done

text {*
  \medskip These are the atomic cases for the proof generation for the
  equivalence of @{text P} and @{text "P plusinfinity"} for integers
  @{text x} greater than some integer @{text z}.

  They are fully based on arithmetics. *}

lemma  eq_eq_pinf: "EX z::int. ALL x. z < x --> (( 0 = x +t ) = False )"
  apply(rule_tac x = "-t" in exI)
  apply simp
  done

lemma  neq_eq_pinf: "EX z::int. ALL x.  z < x --> ((~( 0 = x +t )) = True )"
  apply(rule_tac x = "-t" in exI)
  apply simp
  done

lemma  le_eq_pinf: "EX z::int. ALL x.  z < x --> ( 0 < x +t  = True )"
  apply(rule_tac x = "-t" in exI)
  apply simp
  done

lemma  len_eq_pinf: "EX z::int. ALL x. z < x  --> (0 < -x +t  = False )"
  apply(rule_tac x = "t" in exI)
  apply simp
  done

lemma  dvd_eq_pinf: "EX z::int. ALL x.  z < x --> ((d dvd (x + t)) = (d dvd (x + t))) "
  by simp

lemma  not_dvd_eq_pinf: "EX z::int. ALL x. z < x  --> ((~(d dvd (x + t))) = (~(d dvd (x + t)))) "
  by simp

text {*
  \medskip These are the atomic cases for the proof generation for the
  modulo @{text D} property for @{text "P minusinfinity"}.

  They are fully based on arithmetics. *}

lemma  dvd_modd_minf: "((d::int) dvd d1) ==>
 (ALL (x::int). ALL (k::int). (((d::int) dvd (x + t)) = (d dvd (x-k*d1 + t))))"
apply(clarsimp simp add:dvd_def)
apply(rule iffI)
apply(clarsimp)
apply(rename_tac n m)
apply(rule_tac x = "m - n*k" in exI)
apply(simp add:int_distrib)
apply(clarsimp)
apply(rename_tac n m)
apply(rule_tac x = "m + n*k" in exI)
apply(simp add:int_distrib mult_ac)
done


lemma  not_dvd_modd_minf: "((d::int) dvd d1) ==>
 (ALL (x::int). ALL k. (~((d::int) dvd (x + t))) = (~(d dvd (x-k*d1 + t))))"
apply(clarsimp simp add:dvd_def)
apply(rule iffI)
apply(clarsimp)
apply(rename_tac n m)
apply(erule_tac x = "m + n*k" in allE)
apply(simp add:int_distrib mult_ac)
apply(clarsimp)
apply(rename_tac n m)
apply(erule_tac x = "m - n*k" in allE)
apply(simp add:int_distrib mult_ac)
done

text {*
  \medskip These are the atomic cases for the proof generation for the
  equivalence of @{text P} and @{text "P minusinfinity"} for integers
  @{text x} less than some integer @{text z}.

  They are fully based on arithmetics. *}

lemma  eq_eq_minf: "EX z::int. ALL x. x < z --> (( 0 = x +t ) = False )"
apply(rule_tac x = "-t" in exI)
apply simp
done

lemma  neq_eq_minf: "EX z::int. ALL x. x < z --> ((~( 0 = x +t )) = True )"
apply(rule_tac x = "-t" in exI)
apply simp
done

lemma  le_eq_minf: "EX z::int. ALL x. x < z --> ( 0 < x +t  = False )"
apply(rule_tac x = "-t" in exI)
apply simp
done


lemma  len_eq_minf: "EX z::int. ALL x. x < z --> (0 < -x +t  = True )"
apply(rule_tac x = "t" in exI)
apply simp
done

lemma  dvd_eq_minf: "EX z::int. ALL x. x < z --> ((d dvd (x + t)) = (d dvd (x + t))) "
  by simp

lemma  not_dvd_eq_minf: "EX z::int. ALL x. x < z --> ((~(d dvd (x + t))) = (~(d dvd (x + t)))) "
  by simp

text {*
  \medskip This Theorem combines whithnesses about @{text "P
  minusinfinity"} to show one component of the equivalence proof for
  Cooper's Theorem.

  FIXME: remove once they are part of the distribution. *}

theorem int_ge_induct[consumes 1,case_names base step]:
  assumes ge: "k \<le> (i::int)" and
        base: "P(k)" and
        step: "\<And>i. \<lbrakk>k \<le> i; P i\<rbrakk> \<Longrightarrow> P(i+1)"
  shows "P i"
proof -
  { fix n have "\<And>i::int. n = nat(i-k) \<Longrightarrow> k <= i \<Longrightarrow> P i"
    proof (induct n)
      case 0
      hence "i = k" by arith
      thus "P i" using base by simp
    next
      case (Suc n)
      hence "n = nat((i - 1) - k)" by arith
      moreover
      have ki1: "k \<le> i - 1" using Suc.prems by arith
      ultimately
      have "P(i - 1)" by(rule Suc.hyps)
      from step[OF ki1 this] show ?case by simp
    qed
  }
  from this ge show ?thesis by fast
qed

theorem int_gr_induct[consumes 1,case_names base step]:
  assumes gr: "k < (i::int)" and
        base: "P(k+1)" and
        step: "\<And>i. \<lbrakk>k < i; P i\<rbrakk> \<Longrightarrow> P(i+1)"
  shows "P i"
apply(rule int_ge_induct[of "k + 1"])
  using gr apply arith
 apply(rule base)
apply(rule step)
 apply simp+
done

lemma decr_lemma: "0 < (d::int) \<Longrightarrow> x - (abs(x-z)+1) * d < z"
apply(induct rule: int_gr_induct)
 apply simp
 apply arith
apply (simp add:int_distrib)
apply arith
done

lemma incr_lemma: "0 < (d::int) \<Longrightarrow> z < x + (abs(x-z)+1) * d"
apply(induct rule: int_gr_induct)
 apply simp
 apply arith
apply (simp add:int_distrib)
apply arith
done

lemma  minusinfinity:
  assumes "0 < d" and
    P1eqP1: "ALL x k. P1 x = P1(x - k*d)" and
    ePeqP1: "EX z::int. ALL x. x < z \<longrightarrow> (P x = P1 x)"
  shows "(EX x. P1 x) \<longrightarrow> (EX x. P x)"
proof
  assume eP1: "EX x. P1 x"
  then obtain x where P1: "P1 x" ..
  from ePeqP1 obtain z where P1eqP: "ALL x. x < z \<longrightarrow> (P x = P1 x)" ..
  let ?w = "x - (abs(x-z)+1) * d"
  show "EX x. P x"
  proof
    have w: "?w < z" by(rule decr_lemma)
    have "P1 x = P1 ?w" using P1eqP1 by blast
    also have "\<dots> = P(?w)" using w P1eqP by blast
    finally show "P ?w" using P1 by blast
  qed
qed

text {*
  \medskip This Theorem combines whithnesses about @{text "P
  minusinfinity"} to show one component of the equivalence proof for
  Cooper's Theorem. *}

lemma plusinfinity:
  assumes "0 < d" and
    P1eqP1: "ALL (x::int) (k::int). P1 x = P1 (x + k * d)" and
    ePeqP1: "EX z::int. ALL x. z < x  --> (P x = P1 x)"
  shows "(EX x::int. P1 x) --> (EX x::int. P x)"
proof
  assume eP1: "EX x. P1 x"
  then obtain x where P1: "P1 x" ..
  from ePeqP1 obtain z where P1eqP: "ALL x. z < x \<longrightarrow> (P x = P1 x)" ..
  let ?w = "x + (abs(x-z)+1) * d"
  show "EX x. P x"
  proof
    have w: "z < ?w" by(rule incr_lemma)
    have "P1 x = P1 ?w" using P1eqP1 by blast
    also have "\<dots> = P(?w)" using w P1eqP by blast
    finally show "P ?w" using P1 by blast
  qed
qed
 
text {*
  \medskip Theorem for periodic function on discrete sets. *}

lemma minf_vee:
  assumes dpos: "(0::int) < d" and modd: "ALL x k. P x = P(x - k*d)"
  shows "(EX x. P x) = (EX j : {1..d}. P j)"
  (is "?LHS = ?RHS")
proof
  assume ?LHS
  then obtain x where P: "P x" ..
  have "x mod d = x - (x div d)*d"
    by(simp add:zmod_zdiv_equality mult_ac eq_diff_eq)
  hence Pmod: "P x = P(x mod d)" using modd by simp
  show ?RHS
  proof (cases)
    assume "x mod d = 0"
    hence "P 0" using P Pmod by simp
    moreover have "P 0 = P(0 - (-1)*d)" using modd by blast
    ultimately have "P d" by simp
    moreover have "d : {1..d}" using dpos by(simp add:atLeastAtMost_iff)
    ultimately show ?RHS ..
  next
    assume not0: "x mod d \<noteq> 0"
    have "P(x mod d)" using dpos P Pmod by(simp add:pos_mod_sign pos_mod_bound)
    moreover have "x mod d : {1..d}"
    proof -
      have "0 \<le> x mod d" by(rule pos_mod_sign)
      moreover have "x mod d < d" by(rule pos_mod_bound)
      ultimately show ?thesis using not0 by(simp add:atLeastAtMost_iff)
    qed
    ultimately show ?RHS ..
  qed
next
  assume ?RHS thus ?LHS by blast
qed

text {*
  \medskip Theorem for periodic function on discrete sets. *}

lemma pinf_vee:
  assumes dpos: "0 < (d::int)" and modd: "ALL (x::int) (k::int). P x = P (x+k*d)"
  shows "(EX x::int. P x) = (EX (j::int) : {1..d} . P j)"
  (is "?LHS = ?RHS")
proof
  assume ?LHS
  then obtain x where P: "P x" ..
  have "x mod d = x + (-(x div d))*d"
    by(simp add:zmod_zdiv_equality mult_ac eq_diff_eq)
  hence Pmod: "P x = P(x mod d)" using modd by (simp only:)
  show ?RHS
  proof (cases)
    assume "x mod d = 0"
    hence "P 0" using P Pmod by simp
    moreover have "P 0 = P(0 + 1*d)" using modd by blast
    ultimately have "P d" by simp
    moreover have "d : {1..d}" using dpos by(simp add:atLeastAtMost_iff)
    ultimately show ?RHS ..
  next
    assume not0: "x mod d \<noteq> 0"
    have "P(x mod d)" using dpos P Pmod by(simp add:pos_mod_sign pos_mod_bound)
    moreover have "x mod d : {1..d}"
    proof -
      have "0 \<le> x mod d" by(rule pos_mod_sign)
      moreover have "x mod d < d" by(rule pos_mod_bound)
      ultimately show ?thesis using not0 by(simp add:atLeastAtMost_iff)
    qed
    ultimately show ?RHS ..
  qed
next
  assume ?RHS thus ?LHS by blast
qed

lemma decr_mult_lemma:
  assumes dpos: "(0::int) < d" and
          minus: "ALL x::int. P x \<longrightarrow> P(x - d)" and
          knneg: "0 <= k"
  shows "ALL x. P x \<longrightarrow> P(x - k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  show ?case
  proof
    fix x
    have "P x \<longrightarrow> P (x - i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x - (i + 1) * d)"
      using minus[THEN spec, of "x - i * d"]
      by (simp add:int_distrib OrderedGroup.diff_diff_eq[symmetric])
    ultimately show "P x \<longrightarrow> P(x - (i + 1) * d)" by blast
  qed
qed

lemma incr_mult_lemma:
  assumes dpos: "(0::int) < d" and
          plus: "ALL x::int. P x \<longrightarrow> P(x + d)" and
          knneg: "0 <= k"
  shows "ALL x. P x \<longrightarrow> P(x + k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  show ?case
  proof
    fix x
    have "P x \<longrightarrow> P (x + i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x + (i + 1) * d)"
      using plus[THEN spec, of "x + i * d"]
      by (simp add:int_distrib zadd_ac)
    ultimately show "P x \<longrightarrow> P(x + (i + 1) * d)" by blast
  qed
qed

lemma cpmi_eq: "0 < D \<Longrightarrow> (EX z::int. ALL x. x < z --> (P x = P1 x))
==> ALL x.~(EX (j::int) : {1..D}. EX (b::int) : B. P(b+j)) --> P (x) --> P (x - D) 
==> (ALL (x::int). ALL (k::int). ((P1 x)= (P1 (x-k*D))))
==> (EX (x::int). P(x)) = ((EX (j::int) : {1..D} . (P1(j))) | (EX (j::int) : {1..D}. EX (b::int) : B. P (b+j)))"
apply(rule iffI)
prefer 2
apply(drule minusinfinity)
apply assumption+
apply(fastsimp)
apply clarsimp
apply(subgoal_tac "!!k. 0<=k \<Longrightarrow> !x. P x \<longrightarrow> P (x - k*D)")
apply(frule_tac x = x and z=z in decr_lemma)
apply(subgoal_tac "P1(x - (\<bar>x - z\<bar> + 1) * D)")
prefer 2
apply(subgoal_tac "0 <= (\<bar>x - z\<bar> + 1)")
prefer 2 apply arith
 apply fastsimp
apply(drule (1) minf_vee)
apply blast
apply(blast dest:decr_mult_lemma)
done

text {* Cooper Theorem, plus infinity version. *}
lemma cppi_eq: "0 < D \<Longrightarrow> (EX z::int. ALL x. z < x --> (P x = P1 x))
==> ALL x.~(EX (j::int) : {1..D}. EX (a::int) : A. P(a - j)) --> P (x) --> P (x + D) 
==> (ALL (x::int). ALL (k::int). ((P1 x)= (P1 (x+k*D))))
==> (EX (x::int). P(x)) = ((EX (j::int) : {1..D} . (P1(j))) | (EX (j::int) : {1..D}. EX (a::int) : A. P (a - j)))"
  apply(rule iffI)
  prefer 2
  apply(drule plusinfinity)
  apply assumption+
  apply(fastsimp)
  apply clarsimp
  apply(subgoal_tac "!!k. 0<=k \<Longrightarrow> !x. P x \<longrightarrow> P (x + k*D)")
  apply(frule_tac x = x and z=z in incr_lemma)
  apply(subgoal_tac "P1(x + (\<bar>x - z\<bar> + 1) * D)")
  prefer 2
  apply(subgoal_tac "0 <= (\<bar>x - z\<bar> + 1)")
  prefer 2 apply arith
  apply fastsimp
  apply(drule (1) pinf_vee)
  apply blast
  apply(blast dest:incr_mult_lemma)
  done


text {*
  \bigskip Theorems for the quantifier elminination Functions. *}

lemma qe_ex_conj: "(EX (x::int). A x) = R
		==> (EX (x::int). P x) = (Q & (EX x::int. A x))
		==> (EX (x::int). P x) = (Q & R)"
by blast

lemma qe_ex_nconj: "(EX (x::int). P x) = (True & Q)
		==> (EX (x::int). P x) = Q"
by blast

lemma qe_conjI: "P1 = P2 ==> Q1 = Q2 ==> (P1 & Q1) = (P2 & Q2)"
by blast

lemma qe_disjI: "P1 = P2 ==> Q1 = Q2 ==> (P1 | Q1) = (P2 | Q2)"
by blast

lemma qe_impI: "P1 = P2 ==> Q1 = Q2 ==> (P1 --> Q1) = (P2 --> Q2)"
by blast

lemma qe_eqI: "P1 = P2 ==> Q1 = Q2 ==> (P1 = Q1) = (P2 = Q2)"
by blast

lemma qe_Not: "P = Q ==> (~P) = (~Q)"
by blast

lemma qe_ALL: "(EX x. ~P x) = R ==> (ALL x. P x) = (~R)"
by blast

text {* \bigskip Theorems for proving NNF *}

lemma nnf_im: "((~P) = P1) ==> (Q=Q1) ==> ((P --> Q) = (P1 | Q1))"
by blast

lemma nnf_eq: "((P & Q) = (P1 & Q1)) ==> (((~P) & (~Q)) = (P2 & Q2)) ==> ((P = Q) = ((P1 & Q1)|(P2 & Q2)))"
by blast

lemma nnf_nn: "(P = Q) ==> ((~~P) = Q)"
  by blast
lemma nnf_ncj: "((~P) = P1) ==> ((~Q) = Q1) ==> ((~(P & Q)) = (P1 | Q1))"
by blast

lemma nnf_ndj: "((~P) = P1) ==> ((~Q) = Q1) ==> ((~(P | Q)) = (P1 & Q1))"
by blast
lemma nnf_nim: "(P = P1) ==> ((~Q) = Q1) ==> ((~(P --> Q)) = (P1 & Q1))"
by blast
lemma nnf_neq: "((P & (~Q)) = (P1 & Q1)) ==> (((~P) & Q) = (P2 & Q2)) ==> ((~(P = Q)) = ((P1 & Q1)|(P2 & Q2)))"
by blast
lemma nnf_sdj: "((A & (~B)) = (A1 & B1)) ==> ((C & (~D)) = (C1 & D1)) ==> (A = (~C)) ==> ((~((A & B) | (C & D))) = ((A1 & B1) | (C1 & D1)))"
by blast


lemma qe_exI2: "A = B ==> (EX (x::int). A(x)) = (EX (x::int). B(x))"
  by simp

lemma qe_exI: "(!!x::int. A x = B x) ==> (EX (x::int). A(x)) = (EX (x::int). B(x))"
  by rules

lemma qe_ALLI: "(!!x::int. A x = B x) ==> (ALL (x::int). A(x)) = (ALL (x::int). B(x))"
  by rules

lemma cp_expand: "(EX (x::int). P (x)) = (EX (j::int) : {1..d}. EX (b::int) : B. (P1 (j) | P(b+j)))
==>(EX (x::int). P (x)) = (EX (j::int) : {1..d}. EX (b::int) : B. (P1 (j) | P(b+j))) "
by blast

lemma cppi_expand: "(EX (x::int). P (x)) = (EX (j::int) : {1..d}. EX (a::int) : A. (P1 (j) | P(a - j)))
==>(EX (x::int). P (x)) = (EX (j::int) : {1..d}. EX (a::int) : A. (P1 (j) | P(a - j))) "
by blast


lemma simp_from_to: "{i..j::int} = (if j < i then {} else insert i {i+1..j})"
apply(simp add:atLeastAtMost_def atLeast_def atMost_def)
apply(fastsimp)
done

text {* \bigskip Theorems required for the @{text adjustcoeffitienteq} *}

lemma ac_dvd_eq: assumes not0: "0 ~= (k::int)"
shows "((m::int) dvd (c*n+t)) = (k*m dvd ((k*c)*n+(k*t)))" (is "?P = ?Q")
proof
  assume ?P
  thus ?Q
    apply(simp add:dvd_def)
    apply clarify
    apply(rename_tac d)
    apply(drule_tac f = "op * k" in arg_cong)
    apply(simp only:int_distrib)
    apply(rule_tac x = "d" in exI)
    apply(simp only:mult_ac)
    done
next
  assume ?Q
  then obtain d where "k * c * n + k * t = (k*m)*d" by(fastsimp simp:dvd_def)
  hence "(c * n + t) * k = (m*d) * k" by(simp add:int_distrib mult_ac)
  hence "((c * n + t) * k) div k = ((m*d) * k) div k" by(rule arg_cong[of _ _ "%t. t div k"])
  hence "c*n+t = m*d" by(simp add: zdiv_zmult_self1[OF not0[symmetric]])
  thus ?P by(simp add:dvd_def)
qed

lemma ac_lt_eq: assumes gr0: "0 < (k::int)"
shows "((m::int) < (c*n+t)) = (k*m <((k*c)*n+(k*t)))" (is "?P = ?Q")
proof
  assume P: ?P
  show ?Q using zmult_zless_mono2[OF P gr0] by(simp add: int_distrib mult_ac)
next
  assume ?Q
  hence "0 < k*(c*n + t - m)" by(simp add: int_distrib mult_ac)
  with gr0 have "0 < (c*n + t - m)" by(simp add: zero_less_mult_iff)
  thus ?P by(simp)
qed

lemma ac_eq_eq : assumes not0: "0 ~= (k::int)" shows "((m::int) = (c*n+t)) = (k*m =((k*c)*n+(k*t)) )" (is "?P = ?Q")
proof
  assume ?P
  thus ?Q
    apply(drule_tac f = "op * k" in arg_cong)
    apply(simp only:int_distrib)
    done
next
  assume ?Q
  hence "m * k = (c*n + t) * k" by(simp add:int_distrib mult_ac)
  hence "((m) * k) div k = ((c*n + t) * k) div k" by(rule arg_cong[of _ _ "%t. t div k"])
  thus ?P by(simp add: zdiv_zmult_self1[OF not0[symmetric]])
qed

lemma ac_pi_eq: assumes gr0: "0 < (k::int)" shows "(~((0::int) < (c*n + t))) = (0 < ((-k)*c)*n + ((-k)*t + k))"
proof -
  have "(~ (0::int) < (c*n + t)) = (0<1-(c*n + t))" by arith
  also have  "(1-(c*n + t)) = (-1*c)*n + (-t+1)" by(simp add: int_distrib mult_ac)
  also have "0<(-1*c)*n + (-t+1) = (0 < (k*(-1*c)*n) + (k*(-t+1)))" by(rule ac_lt_eq[of _ 0,OF gr0,simplified])
  also have "(k*(-1*c)*n) + (k*(-t+1)) = ((-k)*c)*n + ((-k)*t + k)" by(simp add: int_distrib mult_ac)
  finally show ?thesis .
qed

lemma binminus_uminus_conv: "(a::int) - b = a + (-b)"
by arith

lemma  linearize_dvd: "(t::int) = t1 ==> (d dvd t) = (d dvd t1)"
by simp

lemma lf_lt: "(l::int) = ll ==> (r::int) = lr ==> (l < r) =(ll < lr)"
by simp

lemma lf_eq: "(l::int) = ll ==> (r::int) = lr ==> (l = r) =(ll = lr)"
by simp

lemma lf_dvd: "(l::int) = ll ==> (r::int) = lr ==> (l dvd r) =(ll dvd lr)"
by simp

text {* \bigskip Theorems for transforming predicates on nat to predicates on @{text int}*}

theorem all_nat: "(\<forall>x::nat. P x) = (\<forall>x::int. 0 <= x \<longrightarrow> P (nat x))"
  by (simp split add: split_nat)

theorem ex_nat: "(\<exists>x::nat. P x) = (\<exists>x::int. 0 <= x \<and> P (nat x))"
  apply (simp split add: split_nat)
  apply (rule iffI)
  apply (erule exE)
  apply (rule_tac x = "int x" in exI)
  apply simp
  apply (erule exE)
  apply (rule_tac x = "nat x" in exI)
  apply (erule conjE)
  apply (erule_tac x = "nat x" in allE)
  apply simp
  done

theorem zdiff_int_split: "P (int (x - y)) =
  ((y \<le> x \<longrightarrow> P (int x - int y)) \<and> (x < y \<longrightarrow> P 0))"
  apply (case_tac "y \<le> x")
  apply (simp_all add: zdiff_int)
  done

theorem zdvd_int: "(x dvd y) = (int x dvd int y)"
  apply (simp only: dvd_def ex_nat int_int_eq [symmetric] zmult_int [symmetric]
    nat_0_le cong add: conj_cong)
  apply (rule iffI)
  apply rules
  apply (erule exE)
  apply (case_tac "x=0")
  apply (rule_tac x=0 in exI)
  apply simp
  apply (case_tac "0 \<le> k")
  apply rules
  apply (simp add: linorder_not_le)
  apply (drule mult_strict_left_mono_neg [OF iffD2 [OF zero_less_int_conv]])
  apply assumption
  apply (simp add: mult_ac)
  done

theorem number_of1: "(0::int) <= number_of n \<Longrightarrow> (0::int) <= number_of (n BIT b)"
  by simp

theorem number_of2: "(0::int) <= number_of bin.Pls" by simp

theorem Suc_plus1: "Suc n = n + 1" by simp

text {*
  \medskip Specific instances of congruence rules, to prevent
  simplifier from looping. *}

theorem imp_le_cong: "(0 <= x \<Longrightarrow> P = P') \<Longrightarrow> (0 <= (x::int) \<longrightarrow> P) = (0 <= x \<longrightarrow> P')"
  by simp

theorem conj_le_cong: "(0 <= x \<Longrightarrow> P = P') \<Longrightarrow> (0 <= (x::int) \<and> P) = (0 <= x \<and> P')"
  by (simp cong: conj_cong)

use "cooper_dec.ML"
use "cooper_proof.ML"
use "qelim.ML"
use "presburger.ML"

setup "Presburger.setup"

end
