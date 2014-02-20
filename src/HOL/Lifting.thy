(*  Title:      HOL/Lifting.thy
    Author:     Brian Huffman and Ondrej Kuncar
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Lifting package *}

theory Lifting
imports Equiv_Relations Transfer
keywords
  "parametric" and
  "print_quot_maps" "print_quotients" :: diag and
  "lift_definition" :: thy_goal and
  "setup_lifting" "lifting_forget" "lifting_update" :: thy_decl
begin

subsection {* Function map *}

context
begin
interpretation lifting_syntax .

lemma map_fun_id:
  "(id ---> id) = id"
  by (simp add: fun_eq_iff)

subsection {* Other predicates on relations *}

definition left_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "left_total R \<longleftrightarrow> (\<forall>x. \<exists>y. R x y)"

lemma left_totalI:
  "(\<And>x. \<exists>y. R x y) \<Longrightarrow> left_total R"
unfolding left_total_def by blast

lemma left_totalE:
  assumes "left_total R"
  obtains "(\<And>x. \<exists>y. R x y)"
using assms unfolding left_total_def by blast

lemma bi_total_iff: "bi_total A = (right_total A \<and> left_total A)"
unfolding left_total_def right_total_def bi_total_def by blast

lemma bi_total_conv_left_right: "bi_total R \<longleftrightarrow> left_total R \<and> right_total R"
by(simp add: left_total_def right_total_def bi_total_def)

definition left_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "left_unique R \<longleftrightarrow> (\<forall>x y z. R x z \<longrightarrow> R y z \<longrightarrow> x = y)"

lemma left_unique_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total A"
  assumes [transfer_rule]: "right_total B"
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> B ===> op=) ===> implies) left_unique left_unique"
using assms unfolding left_unique_def[abs_def] right_total_def bi_unique_def fun_rel_def
by metis

lemma bi_unique_iff: "bi_unique A = (right_unique A \<and> left_unique A)"
unfolding left_unique_def right_unique_def bi_unique_def by blast

lemma bi_unique_conv_left_right: "bi_unique R \<longleftrightarrow> left_unique R \<and> right_unique R"
by(auto simp add: left_unique_def right_unique_def bi_unique_def)

lemma left_uniqueI: "(\<And>x y z. \<lbrakk> A x z; A y z \<rbrakk> \<Longrightarrow> x = y) \<Longrightarrow> left_unique A"
unfolding left_unique_def by blast

lemma left_uniqueD: "\<lbrakk> left_unique A; A x z; A y z \<rbrakk> \<Longrightarrow> x = y"
unfolding left_unique_def by blast

lemma left_total_fun:
  "\<lbrakk>left_unique A; left_total B\<rbrakk> \<Longrightarrow> left_total (A ===> B)"
  unfolding left_total_def fun_rel_def
  apply (rule allI, rename_tac f)
  apply (rule_tac x="\<lambda>y. SOME z. B (f (THE x. A x y)) z" in exI)
  apply clarify
  apply (subgoal_tac "(THE x. A x y) = x", simp)
  apply (rule someI_ex)
  apply (simp)
  apply (rule the_equality)
  apply assumption
  apply (simp add: left_unique_def)
  done

lemma left_unique_fun:
  "\<lbrakk>left_total A; left_unique B\<rbrakk> \<Longrightarrow> left_unique (A ===> B)"
  unfolding left_total_def left_unique_def fun_rel_def
  by (clarify, rule ext, fast)

lemma left_total_eq: "left_total op=" unfolding left_total_def by blast

lemma left_unique_eq: "left_unique op=" unfolding left_unique_def by blast

lemma [simp]:
  shows left_unique_conversep: "left_unique A\<inverse>\<inverse> \<longleftrightarrow> right_unique A"
  and right_unique_conversep: "right_unique A\<inverse>\<inverse> \<longleftrightarrow> left_unique A"
by(auto simp add: left_unique_def right_unique_def)

lemma [simp]:
  shows left_total_conversep: "left_total A\<inverse>\<inverse> \<longleftrightarrow> right_total A"
  and right_total_conversep: "right_total A\<inverse>\<inverse> \<longleftrightarrow> left_total A"
by(simp_all add: left_total_def right_total_def)

subsection {* Quotient Predicate *}

definition
  "Quotient R Abs Rep T \<longleftrightarrow>
     (\<forall>a. Abs (Rep a) = a) \<and> 
     (\<forall>a. R (Rep a) (Rep a)) \<and>
     (\<forall>r s. R r s \<longleftrightarrow> R r r \<and> R s s \<and> Abs r = Abs s) \<and>
     T = (\<lambda>x y. R x x \<and> Abs x = y)"

lemma QuotientI:
  assumes "\<And>a. Abs (Rep a) = a"
    and "\<And>a. R (Rep a) (Rep a)"
    and "\<And>r s. R r s \<longleftrightarrow> R r r \<and> R s s \<and> Abs r = Abs s"
    and "T = (\<lambda>x y. R x x \<and> Abs x = y)"
  shows "Quotient R Abs Rep T"
  using assms unfolding Quotient_def by blast

context
  fixes R Abs Rep T
  assumes a: "Quotient R Abs Rep T"
begin

lemma Quotient_abs_rep: "Abs (Rep a) = a"
  using a unfolding Quotient_def
  by simp

lemma Quotient_rep_reflp: "R (Rep a) (Rep a)"
  using a unfolding Quotient_def
  by blast

lemma Quotient_rel:
  "R r r \<and> R s s \<and> Abs r = Abs s \<longleftrightarrow> R r s" -- {* orientation does not loop on rewriting *}
  using a unfolding Quotient_def
  by blast

lemma Quotient_cr_rel: "T = (\<lambda>x y. R x x \<and> Abs x = y)"
  using a unfolding Quotient_def
  by blast

lemma Quotient_refl1: "R r s \<Longrightarrow> R r r"
  using a unfolding Quotient_def
  by fast

lemma Quotient_refl2: "R r s \<Longrightarrow> R s s"
  using a unfolding Quotient_def
  by fast

lemma Quotient_rel_rep: "R (Rep a) (Rep b) \<longleftrightarrow> a = b"
  using a unfolding Quotient_def
  by metis

lemma Quotient_rep_abs: "R r r \<Longrightarrow> R (Rep (Abs r)) r"
  using a unfolding Quotient_def
  by blast

lemma Quotient_rep_abs_fold_unmap: 
  assumes "x' \<equiv> Abs x" and "R x x" and "Rep x' \<equiv> Rep' x'" 
  shows "R (Rep' x') x"
proof -
  have "R (Rep x') x" using assms(1-2) Quotient_rep_abs by auto
  then show ?thesis using assms(3) by simp
qed

lemma Quotient_Rep_eq:
  assumes "x' \<equiv> Abs x" 
  shows "Rep x' \<equiv> Rep x'"
by simp

lemma Quotient_rel_abs: "R r s \<Longrightarrow> Abs r = Abs s"
  using a unfolding Quotient_def
  by blast

lemma Quotient_rel_abs2:
  assumes "R (Rep x) y"
  shows "x = Abs y"
proof -
  from assms have "Abs (Rep x) = Abs y" by (auto intro: Quotient_rel_abs)
  then show ?thesis using assms(1) by (simp add: Quotient_abs_rep)
qed

lemma Quotient_symp: "symp R"
  using a unfolding Quotient_def using sympI by (metis (full_types))

lemma Quotient_transp: "transp R"
  using a unfolding Quotient_def using transpI by (metis (full_types))

lemma Quotient_part_equivp: "part_equivp R"
by (metis Quotient_rep_reflp Quotient_symp Quotient_transp part_equivpI)

end

lemma identity_quotient: "Quotient (op =) id id (op =)"
unfolding Quotient_def by simp 

text {* TODO: Use one of these alternatives as the real definition. *}

lemma Quotient_alt_def:
  "Quotient R Abs Rep T \<longleftrightarrow>
    (\<forall>a b. T a b \<longrightarrow> Abs a = b) \<and>
    (\<forall>b. T (Rep b) b) \<and>
    (\<forall>x y. R x y \<longleftrightarrow> T x (Abs x) \<and> T y (Abs y) \<and> Abs x = Abs y)"
apply safe
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (rule QuotientI)
apply simp
apply metis
apply simp
apply (rule ext, rule ext, metis)
done

lemma Quotient_alt_def2:
  "Quotient R Abs Rep T \<longleftrightarrow>
    (\<forall>a b. T a b \<longrightarrow> Abs a = b) \<and>
    (\<forall>b. T (Rep b) b) \<and>
    (\<forall>x y. R x y \<longleftrightarrow> T x (Abs y) \<and> T y (Abs x))"
  unfolding Quotient_alt_def by (safe, metis+)

lemma Quotient_alt_def3:
  "Quotient R Abs Rep T \<longleftrightarrow>
    (\<forall>a b. T a b \<longrightarrow> Abs a = b) \<and> (\<forall>b. T (Rep b) b) \<and>
    (\<forall>x y. R x y \<longleftrightarrow> (\<exists>z. T x z \<and> T y z))"
  unfolding Quotient_alt_def2 by (safe, metis+)

lemma Quotient_alt_def4:
  "Quotient R Abs Rep T \<longleftrightarrow>
    (\<forall>a b. T a b \<longrightarrow> Abs a = b) \<and> (\<forall>b. T (Rep b) b) \<and> R = T OO conversep T"
  unfolding Quotient_alt_def3 fun_eq_iff by auto

lemma fun_quotient:
  assumes 1: "Quotient R1 abs1 rep1 T1"
  assumes 2: "Quotient R2 abs2 rep2 T2"
  shows "Quotient (R1 ===> R2) (rep1 ---> abs2) (abs1 ---> rep2) (T1 ===> T2)"
  using assms unfolding Quotient_alt_def2
  unfolding fun_rel_def fun_eq_iff map_fun_apply
  by (safe, metis+)

lemma apply_rsp:
  fixes f g::"'a \<Rightarrow> 'c"
  assumes q: "Quotient R1 Abs1 Rep1 T1"
  and     a: "(R1 ===> R2) f g" "R1 x y"
  shows "R2 (f x) (g y)"
  using a by (auto elim: fun_relE)

lemma apply_rsp':
  assumes a: "(R1 ===> R2) f g" "R1 x y"
  shows "R2 (f x) (g y)"
  using a by (auto elim: fun_relE)

lemma apply_rsp'':
  assumes "Quotient R Abs Rep T"
  and "(R ===> S) f f"
  shows "S (f (Rep x)) (f (Rep x))"
proof -
  from assms(1) have "R (Rep x) (Rep x)" by (rule Quotient_rep_reflp)
  then show ?thesis using assms(2) by (auto intro: apply_rsp')
qed

subsection {* Quotient composition *}

lemma Quotient_compose:
  assumes 1: "Quotient R1 Abs1 Rep1 T1"
  assumes 2: "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (T1 OO R2 OO conversep T1) (Abs2 \<circ> Abs1) (Rep1 \<circ> Rep2) (T1 OO T2)"
  using assms unfolding Quotient_alt_def4 by fastforce

lemma equivp_reflp2:
  "equivp R \<Longrightarrow> reflp R"
  by (erule equivpE)

subsection {* Respects predicate *}

definition Respects :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set"
  where "Respects R = {x. R x x}"

lemma in_respects: "x \<in> Respects R \<longleftrightarrow> R x x"
  unfolding Respects_def by simp

subsection {* Invariant *}

definition invariant :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "invariant R = (\<lambda>x y. R x \<and> x = y)"

lemma invariant_to_eq:
  assumes "invariant P x y"
  shows "x = y"
using assms by (simp add: invariant_def)

lemma fun_rel_eq_invariant:
  shows "((invariant R) ===> S) = (\<lambda>f g. \<forall>x. R x \<longrightarrow> S (f x) (g x))"
by (auto simp add: invariant_def fun_rel_def)

lemma invariant_same_args:
  shows "invariant P x x \<equiv> P x"
using assms by (auto simp add: invariant_def)

lemma invariant_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> op=) ===> A ===> A ===> op=) Lifting.invariant Lifting.invariant"
unfolding invariant_def[abs_def] by transfer_prover

lemma UNIV_typedef_to_Quotient:
  assumes "type_definition Rep Abs UNIV"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (op =) Abs Rep T"
proof -
  interpret type_definition Rep Abs UNIV by fact
  from Abs_inject Rep_inverse Abs_inverse T_def show ?thesis 
    by (fastforce intro!: QuotientI fun_eq_iff)
qed

lemma UNIV_typedef_to_equivp:
  fixes Abs :: "'a \<Rightarrow> 'b"
  and Rep :: "'b \<Rightarrow> 'a"
  assumes "type_definition Rep Abs (UNIV::'a set)"
  shows "equivp (op=::'a\<Rightarrow>'a\<Rightarrow>bool)"
by (rule identity_equivp)

lemma typedef_to_Quotient:
  assumes "type_definition Rep Abs S"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (invariant (\<lambda>x. x \<in> S)) Abs Rep T"
proof -
  interpret type_definition Rep Abs S by fact
  from Rep Abs_inject Rep_inverse Abs_inverse T_def show ?thesis
    by (auto intro!: QuotientI simp: invariant_def fun_eq_iff)
qed

lemma typedef_to_part_equivp:
  assumes "type_definition Rep Abs S"
  shows "part_equivp (invariant (\<lambda>x. x \<in> S))"
proof (intro part_equivpI)
  interpret type_definition Rep Abs S by fact
  show "\<exists>x. invariant (\<lambda>x. x \<in> S) x x" using Rep by (auto simp: invariant_def)
next
  show "symp (invariant (\<lambda>x. x \<in> S))" by (auto intro: sympI simp: invariant_def)
next
  show "transp (invariant (\<lambda>x. x \<in> S))" by (auto intro: transpI simp: invariant_def)
qed

lemma open_typedef_to_Quotient:
  assumes "type_definition Rep Abs {x. P x}"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (invariant P) Abs Rep T"
  using typedef_to_Quotient [OF assms] by simp

lemma open_typedef_to_part_equivp:
  assumes "type_definition Rep Abs {x. P x}"
  shows "part_equivp (invariant P)"
  using typedef_to_part_equivp [OF assms] by simp

text {* Generating transfer rules for quotients. *}

context
  fixes R Abs Rep T
  assumes 1: "Quotient R Abs Rep T"
begin

lemma Quotient_right_unique: "right_unique T"
  using 1 unfolding Quotient_alt_def right_unique_def by metis

lemma Quotient_right_total: "right_total T"
  using 1 unfolding Quotient_alt_def right_total_def by metis

lemma Quotient_rel_eq_transfer: "(T ===> T ===> op =) R (op =)"
  using 1 unfolding Quotient_alt_def fun_rel_def by simp

lemma Quotient_abs_induct:
  assumes "\<And>y. R y y \<Longrightarrow> P (Abs y)" shows "P x"
  using 1 assms unfolding Quotient_def by metis

end

text {* Generating transfer rules for total quotients. *}

context
  fixes R Abs Rep T
  assumes 1: "Quotient R Abs Rep T" and 2: "reflp R"
begin

lemma Quotient_bi_total: "bi_total T"
  using 1 2 unfolding Quotient_alt_def bi_total_def reflp_def by auto

lemma Quotient_id_abs_transfer: "(op = ===> T) (\<lambda>x. x) Abs"
  using 1 2 unfolding Quotient_alt_def reflp_def fun_rel_def by simp

lemma Quotient_total_abs_induct: "(\<And>y. P (Abs y)) \<Longrightarrow> P x"
  using 1 2 assms unfolding Quotient_alt_def reflp_def by metis

lemma Quotient_total_abs_eq_iff: "Abs x = Abs y \<longleftrightarrow> R x y"
  using Quotient_rel [OF 1] 2 unfolding reflp_def by simp

end

text {* Generating transfer rules for a type defined with @{text "typedef"}. *}

context
  fixes Rep Abs A T
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>(x::'a) (y::'b). x = Rep y)"
begin

lemma typedef_left_unique: "left_unique T"
  unfolding left_unique_def T_def
  by (simp add: type_definition.Rep_inject [OF type])

lemma typedef_bi_unique: "bi_unique T"
  unfolding bi_unique_def T_def
  by (simp add: type_definition.Rep_inject [OF type])

(* the following two theorems are here only for convinience *)

lemma typedef_right_unique: "right_unique T"
  using T_def type Quotient_right_unique typedef_to_Quotient 
  by blast

lemma typedef_right_total: "right_total T"
  using T_def type Quotient_right_total typedef_to_Quotient 
  by blast

lemma typedef_rep_transfer: "(T ===> op =) (\<lambda>x. x) Rep"
  unfolding fun_rel_def T_def by simp

end

text {* Generating the correspondence rule for a constant defined with
  @{text "lift_definition"}. *}

lemma Quotient_to_transfer:
  assumes "Quotient R Abs Rep T" and "R c c" and "c' \<equiv> Abs c"
  shows "T c c'"
  using assms by (auto dest: Quotient_cr_rel)

text {* Proving reflexivity *}

lemma Quotient_to_left_total:
  assumes q: "Quotient R Abs Rep T"
  and r_R: "reflp R"
  shows "left_total T"
using r_R Quotient_cr_rel[OF q] unfolding left_total_def by (auto elim: reflpE)

lemma Quotient_composition_ge_eq:
  assumes "left_total T"
  assumes "R \<ge> op="
  shows "(T OO R OO T\<inverse>\<inverse>) \<ge> op="
using assms unfolding left_total_def by fast

lemma Quotient_composition_le_eq:
  assumes "left_unique T"
  assumes "R \<le> op="
  shows "(T OO R OO T\<inverse>\<inverse>) \<le> op="
using assms unfolding left_unique_def by blast

lemma left_total_composition: "left_total R \<Longrightarrow> left_total S \<Longrightarrow> left_total (R OO S)"
unfolding left_total_def OO_def by fast

lemma left_unique_composition: "left_unique R \<Longrightarrow> left_unique S \<Longrightarrow> left_unique (R OO S)"
unfolding left_unique_def OO_def by blast

lemma invariant_le_eq:
  "invariant P \<le> op=" unfolding invariant_def by blast

lemma reflp_ge_eq:
  "reflp R \<Longrightarrow> R \<ge> op=" unfolding reflp_def by blast

lemma ge_eq_refl:
  "R \<ge> op= \<Longrightarrow> R x x" by blast

text {* Proving a parametrized correspondence relation *}

definition POS :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
"POS A B \<equiv> A \<le> B"

definition  NEG :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
"NEG A B \<equiv> B \<le> A"

(*
  The following two rules are here because we don't have any proper
  left-unique ant left-total relations. Left-unique and left-total
  assumptions show up in distributivity rules for the function type.
*)

lemma bi_unique_left_unique[transfer_rule]: "bi_unique R \<Longrightarrow> left_unique R"
unfolding bi_unique_def left_unique_def by blast

lemma bi_total_left_total[transfer_rule]: "bi_total R \<Longrightarrow> left_total R"
unfolding bi_total_def left_total_def by blast

lemma pos_OO_eq:
  shows "POS (A OO op=) A"
unfolding POS_def OO_def by blast

lemma pos_eq_OO:
  shows "POS (op= OO A) A"
unfolding POS_def OO_def by blast

lemma neg_OO_eq:
  shows "NEG (A OO op=) A"
unfolding NEG_def OO_def by auto

lemma neg_eq_OO:
  shows "NEG (op= OO A) A"
unfolding NEG_def OO_def by blast

lemma POS_trans:
  assumes "POS A B"
  assumes "POS B C"
  shows "POS A C"
using assms unfolding POS_def by auto

lemma NEG_trans:
  assumes "NEG A B"
  assumes "NEG B C"
  shows "NEG A C"
using assms unfolding NEG_def by auto

lemma POS_NEG:
  "POS A B \<equiv> NEG B A"
  unfolding POS_def NEG_def by auto

lemma NEG_POS:
  "NEG A B \<equiv> POS B A"
  unfolding POS_def NEG_def by auto

lemma POS_pcr_rule:
  assumes "POS (A OO B) C"
  shows "POS (A OO B OO X) (C OO X)"
using assms unfolding POS_def OO_def by blast

lemma NEG_pcr_rule:
  assumes "NEG (A OO B) C"
  shows "NEG (A OO B OO X) (C OO X)"
using assms unfolding NEG_def OO_def by blast

lemma POS_apply:
  assumes "POS R R'"
  assumes "R f g"
  shows "R' f g"
using assms unfolding POS_def by auto

text {* Proving a parametrized correspondence relation *}

lemma fun_mono:
  assumes "A \<ge> C"
  assumes "B \<le> D"
  shows   "(A ===> B) \<le> (C ===> D)"
using assms unfolding fun_rel_def by blast

lemma pos_fun_distr: "((R ===> S) OO (R' ===> S')) \<le> ((R OO R') ===> (S OO S'))"
unfolding OO_def fun_rel_def by blast

lemma functional_relation: "right_unique R \<Longrightarrow> left_total R \<Longrightarrow> \<forall>x. \<exists>!y. R x y"
unfolding right_unique_def left_total_def by blast

lemma functional_converse_relation: "left_unique R \<Longrightarrow> right_total R \<Longrightarrow> \<forall>y. \<exists>!x. R x y"
unfolding left_unique_def right_total_def by blast

lemma neg_fun_distr1:
assumes 1: "left_unique R" "right_total R"
assumes 2: "right_unique R'" "left_total R'"
shows "(R OO R' ===> S OO S') \<le> ((R ===> S) OO (R' ===> S')) "
  using functional_relation[OF 2] functional_converse_relation[OF 1]
  unfolding fun_rel_def OO_def
  apply clarify
  apply (subst all_comm)
  apply (subst all_conj_distrib[symmetric])
  apply (intro choice)
  by metis

lemma neg_fun_distr2:
assumes 1: "right_unique R'" "left_total R'"
assumes 2: "left_unique S'" "right_total S'"
shows "(R OO R' ===> S OO S') \<le> ((R ===> S) OO (R' ===> S'))"
  using functional_converse_relation[OF 2] functional_relation[OF 1]
  unfolding fun_rel_def OO_def
  apply clarify
  apply (subst all_comm)
  apply (subst all_conj_distrib[symmetric])
  apply (intro choice)
  by metis

subsection {* Domains *}

lemma pcr_Domainp_par_left_total:
  assumes "Domainp B = P"
  assumes "left_total A"
  assumes "(A ===> op=) P' P"
  shows "Domainp (A OO B) = P'"
using assms
unfolding Domainp_iff[abs_def] OO_def bi_unique_def left_total_def fun_rel_def 
by (fast intro: fun_eq_iff)

lemma pcr_Domainp_par:
assumes "Domainp B = P2"
assumes "Domainp A = P1"
assumes "(A ===> op=) P2' P2"
shows "Domainp (A OO B) = (inf P1 P2')"
using assms unfolding fun_rel_def Domainp_iff[abs_def] OO_def
by (fast intro: fun_eq_iff)

definition rel_pred_comp :: "('a => 'b => bool) => ('b => bool) => 'a => bool"
where "rel_pred_comp R P \<equiv> \<lambda>x. \<exists>y. R x y \<and> P y"

lemma pcr_Domainp:
assumes "Domainp B = P"
shows "Domainp (A OO B) = (\<lambda>x. \<exists>y. A x y \<and> P y)"
using assms by blast

lemma pcr_Domainp_total:
  assumes "bi_total B"
  assumes "Domainp A = P"
  shows "Domainp (A OO B) = P"
using assms unfolding bi_total_def 
by fast

lemma Quotient_to_Domainp:
  assumes "Quotient R Abs Rep T"
  shows "Domainp T = (\<lambda>x. R x x)"  
by (simp add: Domainp_iff[abs_def] Quotient_cr_rel[OF assms])

lemma invariant_to_Domainp:
  assumes "Quotient (Lifting.invariant P) Abs Rep T"
  shows "Domainp T = P"
by (simp add: invariant_def Domainp_iff[abs_def] Quotient_cr_rel[OF assms])

end

subsection {* ML setup *}

ML_file "Tools/Lifting/lifting_util.ML"

ML_file "Tools/Lifting/lifting_info.ML"
setup Lifting_Info.setup

lemmas [reflexivity_rule] = 
  order_refl[of "op="] invariant_le_eq Quotient_composition_le_eq
  Quotient_composition_ge_eq
  left_total_eq left_unique_eq left_total_composition left_unique_composition
  left_total_fun left_unique_fun

(* setup for the function type *)
declare fun_quotient[quot_map]
declare fun_mono[relator_mono]
lemmas [relator_distr] = pos_fun_distr neg_fun_distr1 neg_fun_distr2

ML_file "Tools/Lifting/lifting_term.ML"

ML_file "Tools/Lifting/lifting_def.ML"

ML_file "Tools/Lifting/lifting_setup.ML"

hide_const (open) invariant POS NEG

end
