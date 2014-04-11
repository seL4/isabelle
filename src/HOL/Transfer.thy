(*  Title:      HOL/Transfer.thy
    Author:     Brian Huffman, TU Muenchen
    Author:     Ondrej Kuncar, TU Muenchen
*)

header {* Generic theorem transfer using relations *}

theory Transfer
imports Hilbert_Choice Basic_BNFs BNF_FP_Base Metis Option
begin

(* We include Option here altough it's not needed here. 
   By doing this, we avoid a diamond problem for BNF and 
   FP sugar interpretation defined in this file. *)

subsection {* Relator for function space *}

locale lifting_syntax
begin
  notation rel_fun (infixr "===>" 55)
  notation map_fun (infixr "--->" 55)
end

context
begin
interpretation lifting_syntax .

lemma rel_funD2:
  assumes "rel_fun A B f g" and "A x x"
  shows "B (f x) (g x)"
  using assms by (rule rel_funD)

lemma rel_funE:
  assumes "rel_fun A B f g" and "A x y"
  obtains "B (f x) (g y)"
  using assms by (simp add: rel_fun_def)

lemmas rel_fun_eq = fun.rel_eq

lemma rel_fun_eq_rel:
shows "rel_fun (op =) R = (\<lambda>f g. \<forall>x. R (f x) (g x))"
  by (simp add: rel_fun_def)


subsection {* Transfer method *}

text {* Explicit tag for relation membership allows for
  backward proof methods. *}

definition Rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  where "Rel r \<equiv> r"

text {* Handling of equality relations *}

definition is_equality :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_equality R \<longleftrightarrow> R = (op =)"

lemma is_equality_eq: "is_equality (op =)"
  unfolding is_equality_def by simp

text {* Reverse implication for monotonicity rules *}

definition rev_implies where
  "rev_implies x y \<longleftrightarrow> (y \<longrightarrow> x)"

text {* Handling of meta-logic connectives *}

definition transfer_forall where
  "transfer_forall \<equiv> All"

definition transfer_implies where
  "transfer_implies \<equiv> op \<longrightarrow>"

definition transfer_bforall :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transfer_bforall \<equiv> (\<lambda>P Q. \<forall>x. P x \<longrightarrow> Q x)"

lemma transfer_forall_eq: "(\<And>x. P x) \<equiv> Trueprop (transfer_forall (\<lambda>x. P x))"
  unfolding atomize_all transfer_forall_def ..

lemma transfer_implies_eq: "(A \<Longrightarrow> B) \<equiv> Trueprop (transfer_implies A B)"
  unfolding atomize_imp transfer_implies_def ..

lemma transfer_bforall_unfold:
  "Trueprop (transfer_bforall P (\<lambda>x. Q x)) \<equiv> (\<And>x. P x \<Longrightarrow> Q x)"
  unfolding transfer_bforall_def atomize_imp atomize_all ..

lemma transfer_start: "\<lbrakk>P; Rel (op =) P Q\<rbrakk> \<Longrightarrow> Q"
  unfolding Rel_def by simp

lemma transfer_start': "\<lbrakk>P; Rel (op \<longrightarrow>) P Q\<rbrakk> \<Longrightarrow> Q"
  unfolding Rel_def by simp

lemma transfer_prover_start: "\<lbrakk>x = x'; Rel R x' y\<rbrakk> \<Longrightarrow> Rel R x y"
  by simp

lemma untransfer_start: "\<lbrakk>Q; Rel (op =) P Q\<rbrakk> \<Longrightarrow> P"
  unfolding Rel_def by simp

lemma Rel_eq_refl: "Rel (op =) x x"
  unfolding Rel_def ..

lemma Rel_app:
  assumes "Rel (A ===> B) f g" and "Rel A x y"
  shows "Rel B (f x) (g y)"
  using assms unfolding Rel_def rel_fun_def by fast

lemma Rel_abs:
  assumes "\<And>x y. Rel A x y \<Longrightarrow> Rel B (f x) (g y)"
  shows "Rel (A ===> B) (\<lambda>x. f x) (\<lambda>y. g y)"
  using assms unfolding Rel_def rel_fun_def by fast

subsection {* Predicates on relations, i.e. ``class constraints'' *}

definition left_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "left_total R \<longleftrightarrow> (\<forall>x. \<exists>y. R x y)"

definition left_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "left_unique R \<longleftrightarrow> (\<forall>x y z. R x z \<longrightarrow> R y z \<longrightarrow> x = y)"

definition right_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "right_total R \<longleftrightarrow> (\<forall>y. \<exists>x. R x y)"

definition right_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "right_unique R \<longleftrightarrow> (\<forall>x y z. R x y \<longrightarrow> R x z \<longrightarrow> y = z)"

definition bi_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "bi_total R \<longleftrightarrow> (\<forall>x. \<exists>y. R x y) \<and> (\<forall>y. \<exists>x. R x y)"

definition bi_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "bi_unique R \<longleftrightarrow>
    (\<forall>x y z. R x y \<longrightarrow> R x z \<longrightarrow> y = z) \<and>
    (\<forall>x y z. R x z \<longrightarrow> R y z \<longrightarrow> x = y)"

lemma left_uniqueI: "(\<And>x y z. \<lbrakk> A x z; A y z \<rbrakk> \<Longrightarrow> x = y) \<Longrightarrow> left_unique A"
unfolding left_unique_def by blast

lemma left_uniqueD: "\<lbrakk> left_unique A; A x z; A y z \<rbrakk> \<Longrightarrow> x = y"
unfolding left_unique_def by blast

lemma left_totalI:
  "(\<And>x. \<exists>y. R x y) \<Longrightarrow> left_total R"
unfolding left_total_def by blast

lemma left_totalE:
  assumes "left_total R"
  obtains "(\<And>x. \<exists>y. R x y)"
using assms unfolding left_total_def by blast

lemma bi_uniqueDr: "\<lbrakk> bi_unique A; A x y; A x z \<rbrakk> \<Longrightarrow> y = z"
by(simp add: bi_unique_def)

lemma bi_uniqueDl: "\<lbrakk> bi_unique A; A x y; A z y \<rbrakk> \<Longrightarrow> x = z"
by(simp add: bi_unique_def)

lemma right_uniqueI: "(\<And>x y z. \<lbrakk> A x y; A x z \<rbrakk> \<Longrightarrow> y = z) \<Longrightarrow> right_unique A"
unfolding right_unique_def by fast

lemma right_uniqueD: "\<lbrakk> right_unique A; A x y; A x z \<rbrakk> \<Longrightarrow> y = z"
unfolding right_unique_def by fast

lemma right_total_alt_def2:
  "right_total R \<longleftrightarrow> ((R ===> op \<longrightarrow>) ===> op \<longrightarrow>) All All"
  unfolding right_total_def rel_fun_def
  apply (rule iffI, fast)
  apply (rule allI)
  apply (drule_tac x="\<lambda>x. True" in spec)
  apply (drule_tac x="\<lambda>y. \<exists>x. R x y" in spec)
  apply fast
  done

lemma right_unique_alt_def2:
  "right_unique R \<longleftrightarrow> (R ===> R ===> op \<longrightarrow>) (op =) (op =)"
  unfolding right_unique_def rel_fun_def by auto

lemma bi_total_alt_def2:
  "bi_total R \<longleftrightarrow> ((R ===> op =) ===> op =) All All"
  unfolding bi_total_def rel_fun_def
  apply (rule iffI, fast)
  apply safe
  apply (drule_tac x="\<lambda>x. \<exists>y. R x y" in spec)
  apply (drule_tac x="\<lambda>y. True" in spec)
  apply fast
  apply (drule_tac x="\<lambda>x. True" in spec)
  apply (drule_tac x="\<lambda>y. \<exists>x. R x y" in spec)
  apply fast
  done

lemma bi_unique_alt_def2:
  "bi_unique R \<longleftrightarrow> (R ===> R ===> op =) (op =) (op =)"
  unfolding bi_unique_def rel_fun_def by auto

lemma [simp]:
  shows left_unique_conversep: "left_unique A\<inverse>\<inverse> \<longleftrightarrow> right_unique A"
  and right_unique_conversep: "right_unique A\<inverse>\<inverse> \<longleftrightarrow> left_unique A"
by(auto simp add: left_unique_def right_unique_def)

lemma [simp]:
  shows left_total_conversep: "left_total A\<inverse>\<inverse> \<longleftrightarrow> right_total A"
  and right_total_conversep: "right_total A\<inverse>\<inverse> \<longleftrightarrow> left_total A"
by(simp_all add: left_total_def right_total_def)

lemma bi_unique_conversep [simp]: "bi_unique R\<inverse>\<inverse> = bi_unique R"
by(auto simp add: bi_unique_def)

lemma bi_total_conversep [simp]: "bi_total R\<inverse>\<inverse> = bi_total R"
by(auto simp add: bi_total_def)

lemma right_unique_alt_def: "right_unique R = (conversep R OO R \<le> op=)" unfolding right_unique_def by blast
lemma left_unique_alt_def: "left_unique R = (R OO (conversep R) \<le> op=)" unfolding left_unique_def by blast

lemma right_total_alt_def: "right_total R = (conversep R OO R \<ge> op=)" unfolding right_total_def by blast
lemma left_total_alt_def: "left_total R = (R OO conversep R \<ge> op=)" unfolding left_total_def by blast

lemma bi_total_alt_def: "bi_total A = (left_total A \<and> right_total A)"
unfolding left_total_def right_total_def bi_total_def by blast

lemma bi_unique_alt_def: "bi_unique A = (left_unique A \<and> right_unique A)"
unfolding left_unique_def right_unique_def bi_unique_def by blast

lemma bi_totalI: "left_total R \<Longrightarrow> right_total R \<Longrightarrow> bi_total R"
unfolding bi_total_alt_def ..

lemma bi_uniqueI: "left_unique R \<Longrightarrow> right_unique R \<Longrightarrow> bi_unique R"
unfolding bi_unique_alt_def ..

end

subsection {* Equality restricted by a predicate *}

definition eq_onp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "eq_onp R = (\<lambda>x y. R x \<and> x = y)"

lemma eq_onp_Grp: "eq_onp P = BNF_Util.Grp (Collect P) id" 
unfolding eq_onp_def Grp_def by auto 

lemma eq_onp_to_eq:
  assumes "eq_onp P x y"
  shows "x = y"
using assms by (simp add: eq_onp_def)

lemma eq_onp_same_args:
  shows "eq_onp P x x = P x"
using assms by (auto simp add: eq_onp_def)

lemma Ball_Collect: "Ball A P = (A \<subseteq> (Collect P))"
by (metis mem_Collect_eq subset_eq)

ML_file "Tools/Transfer/transfer.ML"
setup Transfer.setup
declare refl [transfer_rule]

hide_const (open) Rel

context
begin
interpretation lifting_syntax .

text {* Handling of domains *}

lemma Domainp_iff: "Domainp T x \<longleftrightarrow> (\<exists>y. T x y)"
  by auto

lemma Domaimp_refl[transfer_domain_rule]:
  "Domainp T = Domainp T" ..

lemma Domainp_prod_fun_eq[relator_domain]:
  "Domainp (op= ===> T) = (\<lambda>f. \<forall>x. (Domainp T) (f x))"
by (auto intro: choice simp: Domainp_iff rel_fun_def fun_eq_iff)

text {* Properties are preserved by relation composition. *}

lemma OO_def: "R OO S = (\<lambda>x z. \<exists>y. R x y \<and> S y z)"
  by auto

lemma bi_total_OO: "\<lbrakk>bi_total A; bi_total B\<rbrakk> \<Longrightarrow> bi_total (A OO B)"
  unfolding bi_total_def OO_def by fast

lemma bi_unique_OO: "\<lbrakk>bi_unique A; bi_unique B\<rbrakk> \<Longrightarrow> bi_unique (A OO B)"
  unfolding bi_unique_def OO_def by blast

lemma right_total_OO:
  "\<lbrakk>right_total A; right_total B\<rbrakk> \<Longrightarrow> right_total (A OO B)"
  unfolding right_total_def OO_def by fast

lemma right_unique_OO:
  "\<lbrakk>right_unique A; right_unique B\<rbrakk> \<Longrightarrow> right_unique (A OO B)"
  unfolding right_unique_def OO_def by fast

lemma left_total_OO: "left_total R \<Longrightarrow> left_total S \<Longrightarrow> left_total (R OO S)"
unfolding left_total_def OO_def by fast

lemma left_unique_OO: "left_unique R \<Longrightarrow> left_unique S \<Longrightarrow> left_unique (R OO S)"
unfolding left_unique_def OO_def by blast


subsection {* Properties of relators *}

lemma left_total_eq[transfer_rule]: "left_total op=" 
  unfolding left_total_def by blast

lemma left_unique_eq[transfer_rule]: "left_unique op=" 
  unfolding left_unique_def by blast

lemma right_total_eq [transfer_rule]: "right_total op="
  unfolding right_total_def by simp

lemma right_unique_eq [transfer_rule]: "right_unique op="
  unfolding right_unique_def by simp

lemma bi_total_eq[transfer_rule]: "bi_total (op =)"
  unfolding bi_total_def by simp

lemma bi_unique_eq[transfer_rule]: "bi_unique (op =)"
  unfolding bi_unique_def by simp

lemma left_total_fun[transfer_rule]:
  "\<lbrakk>left_unique A; left_total B\<rbrakk> \<Longrightarrow> left_total (A ===> B)"
  unfolding left_total_def rel_fun_def
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

lemma left_unique_fun[transfer_rule]:
  "\<lbrakk>left_total A; left_unique B\<rbrakk> \<Longrightarrow> left_unique (A ===> B)"
  unfolding left_total_def left_unique_def rel_fun_def
  by (clarify, rule ext, fast)

lemma right_total_fun [transfer_rule]:
  "\<lbrakk>right_unique A; right_total B\<rbrakk> \<Longrightarrow> right_total (A ===> B)"
  unfolding right_total_def rel_fun_def
  apply (rule allI, rename_tac g)
  apply (rule_tac x="\<lambda>x. SOME z. B z (g (THE y. A x y))" in exI)
  apply clarify
  apply (subgoal_tac "(THE y. A x y) = y", simp)
  apply (rule someI_ex)
  apply (simp)
  apply (rule the_equality)
  apply assumption
  apply (simp add: right_unique_def)
  done

lemma right_unique_fun [transfer_rule]:
  "\<lbrakk>right_total A; right_unique B\<rbrakk> \<Longrightarrow> right_unique (A ===> B)"
  unfolding right_total_def right_unique_def rel_fun_def
  by (clarify, rule ext, fast)

lemma bi_total_fun[transfer_rule]:
  "\<lbrakk>bi_unique A; bi_total B\<rbrakk> \<Longrightarrow> bi_total (A ===> B)"
  unfolding bi_unique_alt_def bi_total_alt_def
  by (blast intro: right_total_fun left_total_fun)

lemma bi_unique_fun[transfer_rule]:
  "\<lbrakk>bi_total A; bi_unique B\<rbrakk> \<Longrightarrow> bi_unique (A ===> B)"
  unfolding bi_unique_alt_def bi_total_alt_def
  by (blast intro: right_unique_fun left_unique_fun)

end

ML_file "Tools/Transfer/transfer_bnf.ML" 

declare pred_fun_def [simp]
declare rel_fun_eq [relator_eq]

subsection {* Transfer rules *}

context
begin
interpretation lifting_syntax .

lemma Domainp_forall_transfer [transfer_rule]:
  assumes "right_total A"
  shows "((A ===> op =) ===> op =)
    (transfer_bforall (Domainp A)) transfer_forall"
  using assms unfolding right_total_def
  unfolding transfer_forall_def transfer_bforall_def rel_fun_def Domainp_iff
  by fast

text {* Transfer rules using implication instead of equality on booleans. *}

lemma transfer_forall_transfer [transfer_rule]:
  "bi_total A \<Longrightarrow> ((A ===> op =) ===> op =) transfer_forall transfer_forall"
  "right_total A \<Longrightarrow> ((A ===> op =) ===> implies) transfer_forall transfer_forall"
  "right_total A \<Longrightarrow> ((A ===> implies) ===> implies) transfer_forall transfer_forall"
  "bi_total A \<Longrightarrow> ((A ===> op =) ===> rev_implies) transfer_forall transfer_forall"
  "bi_total A \<Longrightarrow> ((A ===> rev_implies) ===> rev_implies) transfer_forall transfer_forall"
  unfolding transfer_forall_def rev_implies_def rel_fun_def right_total_def bi_total_def
  by fast+

lemma transfer_implies_transfer [transfer_rule]:
  "(op =        ===> op =        ===> op =       ) transfer_implies transfer_implies"
  "(rev_implies ===> implies     ===> implies    ) transfer_implies transfer_implies"
  "(rev_implies ===> op =        ===> implies    ) transfer_implies transfer_implies"
  "(op =        ===> implies     ===> implies    ) transfer_implies transfer_implies"
  "(op =        ===> op =        ===> implies    ) transfer_implies transfer_implies"
  "(implies     ===> rev_implies ===> rev_implies) transfer_implies transfer_implies"
  "(implies     ===> op =        ===> rev_implies) transfer_implies transfer_implies"
  "(op =        ===> rev_implies ===> rev_implies) transfer_implies transfer_implies"
  "(op =        ===> op =        ===> rev_implies) transfer_implies transfer_implies"
  unfolding transfer_implies_def rev_implies_def rel_fun_def by auto

lemma eq_imp_transfer [transfer_rule]:
  "right_unique A \<Longrightarrow> (A ===> A ===> op \<longrightarrow>) (op =) (op =)"
  unfolding right_unique_alt_def2 .

text {* Transfer rules using equality. *}

lemma left_unique_transfer [transfer_rule]:
  assumes "right_total A"
  assumes "right_total B"
  assumes "bi_unique A"
  shows "((A ===> B ===> op=) ===> implies) left_unique left_unique"
using assms unfolding left_unique_def[abs_def] right_total_def bi_unique_def rel_fun_def
by metis

lemma eq_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> A ===> op =) (op =) (op =)"
  using assms unfolding bi_unique_def rel_fun_def by auto

lemma right_total_Ex_transfer[transfer_rule]:
  assumes "right_total A"
  shows "((A ===> op=) ===> op=) (Bex (Collect (Domainp A))) Ex"
using assms unfolding right_total_def Bex_def rel_fun_def Domainp_iff[abs_def]
by fast

lemma right_total_All_transfer[transfer_rule]:
  assumes "right_total A"
  shows "((A ===> op =) ===> op =) (Ball (Collect (Domainp A))) All"
using assms unfolding right_total_def Ball_def rel_fun_def Domainp_iff[abs_def]
by fast

lemma All_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> op =) ===> op =) All All"
  using assms unfolding bi_total_def rel_fun_def by fast

lemma Ex_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> op =) ===> op =) Ex Ex"
  using assms unfolding bi_total_def rel_fun_def by fast

lemma If_transfer [transfer_rule]: "(op = ===> A ===> A ===> A) If If"
  unfolding rel_fun_def by simp

lemma Let_transfer [transfer_rule]: "(A ===> (A ===> B) ===> B) Let Let"
  unfolding rel_fun_def by simp

lemma id_transfer [transfer_rule]: "(A ===> A) id id"
  unfolding rel_fun_def by simp

lemma comp_transfer [transfer_rule]:
  "((B ===> C) ===> (A ===> B) ===> (A ===> C)) (op \<circ>) (op \<circ>)"
  unfolding rel_fun_def by simp

lemma fun_upd_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> B) ===> A ===> B ===> A ===> B) fun_upd fun_upd"
  unfolding fun_upd_def [abs_def] by transfer_prover

lemma case_nat_transfer [transfer_rule]:
  "(A ===> (op = ===> A) ===> op = ===> A) case_nat case_nat"
  unfolding rel_fun_def by (simp split: nat.split)

lemma rec_nat_transfer [transfer_rule]:
  "(A ===> (op = ===> A ===> A) ===> op = ===> A) rec_nat rec_nat"
  unfolding rel_fun_def by (clarsimp, rename_tac n, induct_tac n, simp_all)

lemma funpow_transfer [transfer_rule]:
  "(op = ===> (A ===> A) ===> (A ===> A)) compow compow"
  unfolding funpow_def by transfer_prover

lemma mono_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
  assumes [transfer_rule]: "(A ===> A ===> op=) op\<le> op\<le>"
  assumes [transfer_rule]: "(B ===> B ===> op=) op\<le> op\<le>"
  shows "((A ===> B) ===> op=) mono mono"
unfolding mono_def[abs_def] by transfer_prover

lemma right_total_relcompp_transfer[transfer_rule]: 
  assumes [transfer_rule]: "right_total B"
  shows "((A ===> B ===> op=) ===> (B ===> C ===> op=) ===> A ===> C ===> op=) 
    (\<lambda>R S x z. \<exists>y\<in>Collect (Domainp B). R x y \<and> S y z) op OO"
unfolding OO_def[abs_def] by transfer_prover

lemma relcompp_transfer[transfer_rule]: 
  assumes [transfer_rule]: "bi_total B"
  shows "((A ===> B ===> op=) ===> (B ===> C ===> op=) ===> A ===> C ===> op=) op OO op OO"
unfolding OO_def[abs_def] by transfer_prover

lemma right_total_Domainp_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total B"
  shows "((A ===> B ===> op=) ===> A ===> op=) (\<lambda>T x. \<exists>y\<in>Collect(Domainp B). T x y) Domainp"
apply(subst(2) Domainp_iff[abs_def]) by transfer_prover

lemma Domainp_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_total B"
  shows "((A ===> B ===> op=) ===> A ===> op=) Domainp Domainp"
unfolding Domainp_iff[abs_def] by transfer_prover

lemma reflp_transfer[transfer_rule]: 
  "bi_total A \<Longrightarrow> ((A ===> A ===> op=) ===> op=) reflp reflp"
  "right_total A \<Longrightarrow> ((A ===> A ===> implies) ===> implies) reflp reflp"
  "right_total A \<Longrightarrow> ((A ===> A ===> op=) ===> implies) reflp reflp"
  "bi_total A \<Longrightarrow> ((A ===> A ===> rev_implies) ===> rev_implies) reflp reflp"
  "bi_total A \<Longrightarrow> ((A ===> A ===> op=) ===> rev_implies) reflp reflp"
using assms unfolding reflp_def[abs_def] rev_implies_def bi_total_def right_total_def rel_fun_def 
by fast+

lemma right_unique_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total A"
  assumes [transfer_rule]: "right_total B"
  assumes [transfer_rule]: "bi_unique B"
  shows "((A ===> B ===> op=) ===> implies) right_unique right_unique"
using assms unfolding right_unique_def[abs_def] right_total_def bi_unique_def rel_fun_def
by metis

lemma rel_fun_eq_eq_onp: "(op= ===> eq_onp P) = eq_onp (\<lambda>f. \<forall>x. P(f x))"
unfolding eq_onp_def rel_fun_def by auto

lemma rel_fun_eq_onp_rel:
  shows "((eq_onp R) ===> S) = (\<lambda>f g. \<forall>x. R x \<longrightarrow> S (f x) (g x))"
by (auto simp add: eq_onp_def rel_fun_def)

lemma eq_onp_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> op=) ===> A ===> A ===> op=) eq_onp eq_onp"
unfolding eq_onp_def[abs_def] by transfer_prover

end

end
