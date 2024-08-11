(*  Title:      HOL/Lifting.thy
    Author:     Brian Huffman and Ondrej Kuncar
    Author:     Cezary Kaliszyk and Christian Urban
*)

section \<open>Lifting package\<close>

theory Lifting
imports Equiv_Relations Transfer
keywords
  "parametric" and
  "print_quot_maps" "print_quotients" :: diag and
  "lift_definition" :: thy_goal_defn and
  "setup_lifting" "lifting_forget" "lifting_update" :: thy_decl
begin

subsection \<open>Function map\<close>

context includes lifting_syntax
begin

lemma map_fun_id:
  "(id ---> id) = id"
  by (simp add: fun_eq_iff)

subsection \<open>Quotient Predicate\<close>

definition Quotient :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where
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
  "R r r \<and> R s s \<and> Abs r = Abs s \<longleftrightarrow> R r s" \<comment> \<open>orientation does not loop on rewriting\<close>
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

lemma Quotient_rep_abs_eq: "R t t \<Longrightarrow> R \<le> (=) \<Longrightarrow> Rep (Abs t) = t"
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

lemma identity_quotient: "Quotient (=) id id (=)"
unfolding Quotient_def by simp

text \<open>TODO: Use one of these alternatives as the real definition.\<close>

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

lemma Quotient_alt_def5:
  "Quotient R Abs Rep T \<longleftrightarrow>
    T \<le> BNF_Def.Grp UNIV Abs \<and> BNF_Def.Grp UNIV Rep \<le> T\<inverse>\<inverse> \<and> R = T OO T\<inverse>\<inverse>"
  unfolding Quotient_alt_def4 Grp_def by blast

lemma fun_quotient:
  assumes 1: "Quotient R1 abs1 rep1 T1"
  assumes 2: "Quotient R2 abs2 rep2 T2"
  shows "Quotient (R1 ===> R2) (rep1 ---> abs2) (abs1 ---> rep2) (T1 ===> T2)"
  using assms unfolding Quotient_alt_def2
  unfolding rel_fun_def fun_eq_iff map_fun_apply
  by (safe, metis+)

lemma apply_rsp:
  fixes f g::"'a \<Rightarrow> 'c"
  assumes q: "Quotient R1 Abs1 Rep1 T1"
  and     a: "(R1 ===> R2) f g" "R1 x y"
  shows "R2 (f x) (g y)"
  using a by (auto elim: rel_funE)

lemma apply_rsp':
  assumes a: "(R1 ===> R2) f g" "R1 x y"
  shows "R2 (f x) (g y)"
  using a by (auto elim: rel_funE)

lemma apply_rsp'':
  assumes "Quotient R Abs Rep T"
  and "(R ===> S) f f"
  shows "S (f (Rep x)) (f (Rep x))"
proof -
  from assms(1) have "R (Rep x) (Rep x)" by (rule Quotient_rep_reflp)
  then show ?thesis using assms(2) by (auto intro: apply_rsp')
qed

subsection \<open>Quotient composition\<close>

lemma Quotient_compose:
  assumes 1: "Quotient R1 Abs1 Rep1 T1"
  assumes 2: "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (T1 OO R2 OO conversep T1) (Abs2 \<circ> Abs1) (Rep1 \<circ> Rep2) (T1 OO T2)"
  using assms unfolding Quotient_alt_def4 by fastforce

lemma equivp_reflp2:
  "equivp R \<Longrightarrow> reflp R"
  by (erule equivpE)

subsection \<open>Respects predicate\<close>

definition Respects :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set"
  where "Respects R = {x. R x x}"

lemma in_respects: "x \<in> Respects R \<longleftrightarrow> R x x"
  unfolding Respects_def by simp

lemma UNIV_typedef_to_Quotient:
  assumes "type_definition Rep Abs UNIV"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (=) Abs Rep T"
proof -
  interpret type_definition Rep Abs UNIV by fact
  from Abs_inject Rep_inverse Abs_inverse T_def show ?thesis
    by (fastforce intro!: QuotientI fun_eq_iff)
qed

lemma UNIV_typedef_to_equivp:
  fixes Abs :: "'a \<Rightarrow> 'b"
  and Rep :: "'b \<Rightarrow> 'a"
  assumes "type_definition Rep Abs (UNIV::'a set)"
  shows "equivp ((=) ::'a\<Rightarrow>'a\<Rightarrow>bool)"
by (rule identity_equivp)

lemma typedef_to_Quotient:
  assumes "type_definition Rep Abs S"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (eq_onp (\<lambda>x. x \<in> S)) Abs Rep T"
proof -
  interpret type_definition Rep Abs S by fact
  from Rep Abs_inject Rep_inverse Abs_inverse T_def show ?thesis
    by (auto intro!: QuotientI simp: eq_onp_def fun_eq_iff)
qed

lemma typedef_to_part_equivp:
  assumes "type_definition Rep Abs S"
  shows "part_equivp (eq_onp (\<lambda>x. x \<in> S))"
proof (intro part_equivpI)
  interpret type_definition Rep Abs S by fact
  show "\<exists>x. eq_onp (\<lambda>x. x \<in> S) x x" using Rep by (auto simp: eq_onp_def)
next
  show "symp (eq_onp (\<lambda>x. x \<in> S))" by (auto intro: sympI simp: eq_onp_def)
next
  show "transp (eq_onp (\<lambda>x. x \<in> S))" by (auto intro: transpI simp: eq_onp_def)
qed

lemma open_typedef_to_Quotient:
  assumes "type_definition Rep Abs {x. P x}"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (eq_onp P) Abs Rep T"
  using typedef_to_Quotient [OF assms] by simp

lemma open_typedef_to_part_equivp:
  assumes "type_definition Rep Abs {x. P x}"
  shows "part_equivp (eq_onp P)"
  using typedef_to_part_equivp [OF assms] by simp

lemma type_definition_Quotient_not_empty: "Quotient (eq_onp P) Abs Rep T \<Longrightarrow> \<exists>x. P x"
unfolding eq_onp_def by (drule Quotient_rep_reflp) blast

lemma type_definition_Quotient_not_empty_witness: "Quotient (eq_onp P) Abs Rep T \<Longrightarrow> P (Rep undefined)"
unfolding eq_onp_def by (drule Quotient_rep_reflp) blast


text \<open>Generating transfer rules for quotients.\<close>

context
  fixes R Abs Rep T
  assumes 1: "Quotient R Abs Rep T"
begin

lemma Quotient_right_unique: "right_unique T"
  using 1 unfolding Quotient_alt_def right_unique_def by metis

lemma Quotient_right_total: "right_total T"
  using 1 unfolding Quotient_alt_def right_total_def by metis

lemma Quotient_rel_eq_transfer: "(T ===> T ===> (=)) R (=)"
  using 1 unfolding Quotient_alt_def rel_fun_def by simp

lemma Quotient_abs_induct:
  assumes "\<And>y. R y y \<Longrightarrow> P (Abs y)" shows "P x"
  using 1 assms unfolding Quotient_def by metis

end

text \<open>Generating transfer rules for total quotients.\<close>

context
  fixes R Abs Rep T
  assumes 1: "Quotient R Abs Rep T" and 2: "reflp R"
begin

lemma Quotient_left_total: "left_total T"
  using 1 2 unfolding Quotient_alt_def left_total_def reflp_def by auto

lemma Quotient_bi_total: "bi_total T"
  using 1 2 unfolding Quotient_alt_def bi_total_def reflp_def by auto

lemma Quotient_id_abs_transfer: "((=) ===> T) (\<lambda>x. x) Abs"
  using 1 2 unfolding Quotient_alt_def reflp_def rel_fun_def by simp

lemma Quotient_total_abs_induct: "(\<And>y. P (Abs y)) \<Longrightarrow> P x"
  using 1 2 unfolding Quotient_alt_def reflp_def by metis

lemma Quotient_total_abs_eq_iff: "Abs x = Abs y \<longleftrightarrow> R x y"
  using Quotient_rel [OF 1] 2 unfolding reflp_def by simp

end

text \<open>Generating transfer rules for a type defined with \<open>typedef\<close>.\<close>

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

lemma typedef_rep_transfer: "(T ===> (=)) (\<lambda>x. x) Rep"
  unfolding rel_fun_def T_def by simp

end

text \<open>Generating the correspondence rule for a constant defined with
  \<open>lift_definition\<close>.\<close>

lemma Quotient_to_transfer:
  assumes "Quotient R Abs Rep T" and "R c c" and "c' \<equiv> Abs c"
  shows "T c c'"
  using assms by (auto dest: Quotient_cr_rel)

text \<open>Proving reflexivity\<close>

lemma Quotient_to_left_total:
  assumes q: "Quotient R Abs Rep T"
  and r_R: "reflp R"
  shows "left_total T"
using r_R Quotient_cr_rel[OF q] unfolding left_total_def by (auto elim: reflpE)

lemma Quotient_composition_ge_eq:
  assumes "left_total T"
  assumes "R \<ge> (=)"
  shows "(T OO R OO T\<inverse>\<inverse>) \<ge> (=)"
using assms unfolding left_total_def by fast

lemma Quotient_composition_le_eq:
  assumes "left_unique T"
  assumes "R \<le> (=)"
  shows "(T OO R OO T\<inverse>\<inverse>) \<le> (=)"
using assms unfolding left_unique_def by blast

lemma eq_onp_le_eq:
  "eq_onp P \<le> (=)" unfolding eq_onp_def by blast

lemma reflp_ge_eq:
  "reflp R \<Longrightarrow> R \<ge> (=)" unfolding reflp_def by blast

text \<open>Proving a parametrized correspondence relation\<close>

definition POS :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
"POS A B \<equiv> A \<le> B"

definition  NEG :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
"NEG A B \<equiv> B \<le> A"

lemma pos_OO_eq:
  shows "POS (A OO (=)) A"
unfolding POS_def OO_def by blast

lemma pos_eq_OO:
  shows "POS ((=) OO A) A"
unfolding POS_def OO_def by blast

lemma neg_OO_eq:
  shows "NEG (A OO (=)) A"
unfolding NEG_def OO_def by auto

lemma neg_eq_OO:
  shows "NEG ((=) OO A) A"
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

text \<open>Proving a parametrized correspondence relation\<close>

lemma fun_mono:
  assumes "A \<ge> C"
  assumes "B \<le> D"
  shows   "(A ===> B) \<le> (C ===> D)"
using assms unfolding rel_fun_def by blast

lemma pos_fun_distr: "((R ===> S) OO (R' ===> S')) \<le> ((R OO R') ===> (S OO S'))"
unfolding OO_def rel_fun_def by blast

lemma functional_relation: "right_unique R \<Longrightarrow> left_total R \<Longrightarrow> \<forall>x. \<exists>!y. R x y"
unfolding right_unique_def left_total_def by blast

lemma functional_converse_relation: "left_unique R \<Longrightarrow> right_total R \<Longrightarrow> \<forall>y. \<exists>!x. R x y"
unfolding left_unique_def right_total_def by blast

lemma neg_fun_distr1:
assumes 1: "left_unique R" "right_total R"
assumes 2: "right_unique R'" "left_total R'"
shows "(R OO R' ===> S OO S') \<le> ((R ===> S) OO (R' ===> S')) "
  using functional_relation[OF 2] functional_converse_relation[OF 1]
  unfolding rel_fun_def OO_def
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
  unfolding rel_fun_def OO_def
  apply clarify
  apply (subst all_comm)
  apply (subst all_conj_distrib[symmetric])
  apply (intro choice)
  by metis

subsection \<open>Domains\<close>

lemma composed_equiv_rel_eq_onp:
  assumes "left_unique R"
  assumes "(R ===> (=)) P P'"
  assumes "Domainp R = P''"
  shows "(R OO eq_onp P' OO R\<inverse>\<inverse>) = eq_onp (inf P'' P)"
using assms unfolding OO_def conversep_iff Domainp_iff[abs_def] left_unique_def rel_fun_def eq_onp_def
fun_eq_iff by blast

lemma composed_equiv_rel_eq_eq_onp:
  assumes "left_unique R"
  assumes "Domainp R = P"
  shows "(R OO (=) OO R\<inverse>\<inverse>) = eq_onp P"
using assms unfolding OO_def conversep_iff Domainp_iff[abs_def] left_unique_def eq_onp_def
fun_eq_iff is_equality_def by metis

lemma pcr_Domainp_par_left_total:
  assumes "Domainp B = P"
  assumes "left_total A"
  assumes "(A ===> (=)) P' P"
  shows "Domainp (A OO B) = P'"
using assms
unfolding Domainp_iff[abs_def] OO_def bi_unique_def left_total_def rel_fun_def
by (fast intro: fun_eq_iff)

lemma pcr_Domainp_par:
assumes "Domainp B = P2"
assumes "Domainp A = P1"
assumes "(A ===> (=)) P2' P2"
shows "Domainp (A OO B) = (inf P1 P2')"
using assms unfolding rel_fun_def Domainp_iff[abs_def] OO_def
by (fast intro: fun_eq_iff)

definition rel_pred_comp :: "('a => 'b => bool) => ('b => bool) => 'a => bool"
where "rel_pred_comp R P \<equiv> \<lambda>x. \<exists>y. R x y \<and> P y"

lemma pcr_Domainp:
assumes "Domainp B = P"
shows "Domainp (A OO B) = (\<lambda>x. \<exists>y. A x y \<and> P y)"
using assms by blast

lemma pcr_Domainp_total:
  assumes "left_total B"
  assumes "Domainp A = P"
  shows "Domainp (A OO B) = P"
using assms unfolding left_total_def
by fast

lemma Quotient_to_Domainp:
  assumes "Quotient R Abs Rep T"
  shows "Domainp T = (\<lambda>x. R x x)"
by (simp add: Domainp_iff[abs_def] Quotient_cr_rel[OF assms])

lemma eq_onp_to_Domainp:
  assumes "Quotient (eq_onp P) Abs Rep T"
  shows "Domainp T = P"
by (simp add: eq_onp_def Domainp_iff[abs_def] Quotient_cr_rel[OF assms])

end

(* needed for lifting_def_code_dt.ML (moved from Lifting_Set) *)
lemma right_total_UNIV_transfer:
  assumes "right_total A"
  shows "(rel_set A) (Collect (Domainp A)) UNIV"
  using assms unfolding right_total_def rel_set_def Domainp_iff by blast

subsection \<open>ML setup\<close>

ML_file \<open>Tools/Lifting/lifting_util.ML\<close>

named_theorems relator_eq_onp
  "theorems that a relator of an eq_onp is an eq_onp of the corresponding predicate"
ML_file \<open>Tools/Lifting/lifting_info.ML\<close>

(* setup for the function type *)
declare fun_quotient[quot_map]
declare fun_mono[relator_mono]
lemmas [relator_distr] = pos_fun_distr neg_fun_distr1 neg_fun_distr2

ML_file \<open>Tools/Lifting/lifting_bnf.ML\<close>
ML_file \<open>Tools/Lifting/lifting_term.ML\<close>
ML_file \<open>Tools/Lifting/lifting_def.ML\<close>
ML_file \<open>Tools/Lifting/lifting_setup.ML\<close>
ML_file \<open>Tools/Lifting/lifting_def_code_dt.ML\<close>

lemma pred_prod_beta: "pred_prod P Q xy \<longleftrightarrow> P (fst xy) \<and> Q (snd xy)"
by(cases xy) simp

lemma pred_prod_split: "P (pred_prod Q R xy) \<longleftrightarrow> (\<forall>x y. xy = (x, y) \<longrightarrow> P (Q x \<and> R y))"
by(cases xy) simp

hide_const (open) POS NEG

end
