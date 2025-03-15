(*  Title:      HOL/Transfer.thy
    Author:     Brian Huffman, TU Muenchen
    Author:     Ondrej Kuncar, TU Muenchen
*)

section \<open>Generic theorem transfer using relations\<close>

theory Transfer
imports Basic_BNF_LFPs Hilbert_Choice Metis
begin

subsection \<open>Relator for function space\<close>

bundle lifting_syntax
begin
notation rel_fun  (infixr \<open>===>\<close> 55)
notation map_fun  (infixr \<open>--->\<close> 55)
end

context includes lifting_syntax
begin

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
shows "rel_fun (=) R = (\<lambda>f g. \<forall>x. R (f x) (g x))"
  by (simp add: rel_fun_def)


subsection \<open>Transfer method\<close>

text \<open>Explicit tag for relation membership allows for
  backward proof methods.\<close>

definition Rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  where "Rel r \<equiv> r"

text \<open>Handling of equality relations\<close>

definition is_equality :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "is_equality R \<longleftrightarrow> R = (=)"

lemma is_equality_eq: "is_equality (=)"
  unfolding is_equality_def by simp

text \<open>Reverse implication for monotonicity rules\<close>

definition rev_implies where
  "rev_implies x y \<longleftrightarrow> (y \<longrightarrow> x)"

text \<open>Handling of meta-logic connectives\<close>

definition transfer_forall where
  "transfer_forall \<equiv> All"

definition transfer_implies where
  "transfer_implies \<equiv> (\<longrightarrow>)"

definition transfer_bforall :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transfer_bforall \<equiv> (\<lambda>P Q. \<forall>x. P x \<longrightarrow> Q x)"

lemma transfer_forall_eq: "(\<And>x. P x) \<equiv> Trueprop (transfer_forall (\<lambda>x. P x))"
  unfolding atomize_all transfer_forall_def ..

lemma transfer_implies_eq: "(A \<Longrightarrow> B) \<equiv> Trueprop (transfer_implies A B)"
  unfolding atomize_imp transfer_implies_def ..

lemma transfer_bforall_unfold:
  "Trueprop (transfer_bforall P (\<lambda>x. Q x)) \<equiv> (\<And>x. P x \<Longrightarrow> Q x)"
  unfolding transfer_bforall_def atomize_imp atomize_all ..

lemma transfer_start: "\<lbrakk>P; Rel (=) P Q\<rbrakk> \<Longrightarrow> Q"
  unfolding Rel_def by simp

lemma transfer_start': "\<lbrakk>P; Rel (\<longrightarrow>) P Q\<rbrakk> \<Longrightarrow> Q"
  unfolding Rel_def by simp

lemma transfer_prover_start: "\<lbrakk>x = x'; Rel R x' y\<rbrakk> \<Longrightarrow> Rel R x y"
  by simp

lemma untransfer_start: "\<lbrakk>Q; Rel (=) P Q\<rbrakk> \<Longrightarrow> P"
  unfolding Rel_def by simp

lemma Rel_eq_refl: "Rel (=) x x"
  unfolding Rel_def ..

lemma Rel_app:
  assumes "Rel (A ===> B) f g" and "Rel A x y"
  shows "Rel B (f x) (g y)"
  using assms unfolding Rel_def rel_fun_def by fast

lemma Rel_abs:
  assumes "\<And>x y. Rel A x y \<Longrightarrow> Rel B (f x) (g y)"
  shows "Rel (A ===> B) (\<lambda>x. f x) (\<lambda>y. g y)"
  using assms unfolding Rel_def rel_fun_def by fast

subsection \<open>Predicates on relations, i.e. ``class constraints''\<close>

definition left_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "left_total R \<longleftrightarrow> (\<forall>x. \<exists>y. R x y)"

definition right_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "right_total R \<longleftrightarrow> (\<forall>y. \<exists>x. R x y)"

definition bi_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "bi_total R \<longleftrightarrow> (\<forall>x. \<exists>y. R x y) \<and> (\<forall>y. \<exists>x. R x y)"

definition bi_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "bi_unique R \<longleftrightarrow>
    (\<forall>x y z. R x y \<longrightarrow> R x z \<longrightarrow> y = z) \<and>
    (\<forall>x y z. R x z \<longrightarrow> R y z \<longrightarrow> x = y)"

lemma left_unique_iff: "left_unique R \<longleftrightarrow> (\<forall>z. \<exists>\<^sub>\<le>\<^sub>1x. R x z)"
  unfolding Uniq_def left_unique_def by force

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

lemma bi_unique_iff: "bi_unique R \<longleftrightarrow> (\<forall>z. \<exists>\<^sub>\<le>\<^sub>1x. R x z) \<and> (\<forall>z. \<exists>\<^sub>\<le>\<^sub>1x. R z x)"
  unfolding Uniq_def bi_unique_def by force

lemma right_unique_iff: "right_unique R \<longleftrightarrow> (\<forall>z. \<exists>\<^sub>\<le>\<^sub>1x. R z x)"
  unfolding Uniq_def right_unique_def by force

lemma right_totalI: "(\<And>y. \<exists>x. A x y) \<Longrightarrow> right_total A"
by(simp add: right_total_def)

lemma right_totalE:
  assumes "right_total A"
  obtains x where "A x y"
using assms by(auto simp add: right_total_def)

lemma right_total_alt_def2:
  "right_total R \<longleftrightarrow> ((R ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) All All" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    unfolding right_total_def rel_fun_def by blast
next
  assume \<section>: ?rhs
  show ?lhs
    using \<section> [unfolded rel_fun_def, rule_format, of "\<lambda>x. True" "\<lambda>y. \<exists>x. R x y"]
    unfolding right_total_def by blast
qed

lemma right_unique_alt_def2:
  "right_unique R \<longleftrightarrow> (R ===> R ===> (\<longrightarrow>)) (=) (=)"
  unfolding right_unique_def rel_fun_def by auto

lemma bi_total_alt_def2:
  "bi_total R \<longleftrightarrow> ((R ===> (=)) ===> (=)) All All" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    unfolding bi_total_def rel_fun_def by blast
next
  assume \<section>: ?rhs
  show ?lhs
    using \<section> [unfolded rel_fun_def, rule_format, of "\<lambda>x. \<exists>y. R x y" "\<lambda>y. True"]
    using \<section> [unfolded rel_fun_def, rule_format, of "\<lambda>x. True" "\<lambda>y. \<exists>x. R x y"]
    by (auto simp: bi_total_def)
qed

lemma bi_unique_alt_def2:
  "bi_unique R \<longleftrightarrow> (R ===> R ===> (=)) (=) (=)"
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

lemma right_unique_alt_def: "right_unique R = (conversep R OO R \<le> (=))" unfolding right_unique_def by blast
lemma left_unique_alt_def: "left_unique R = (R OO (conversep R) \<le> (=))" unfolding left_unique_def by blast

lemma right_total_alt_def: "right_total R = (conversep R OO R \<ge> (=))" unfolding right_total_def by blast
lemma left_total_alt_def: "left_total R = (R OO conversep R \<ge> (=))" unfolding left_total_def by blast

lemma bi_total_alt_def: "bi_total A = (left_total A \<and> right_total A)"
unfolding left_total_def right_total_def bi_total_def by blast

lemma bi_unique_alt_def: "bi_unique A = (left_unique A \<and> right_unique A)"
unfolding left_unique_def right_unique_def bi_unique_def by blast

lemma bi_totalI: "left_total R \<Longrightarrow> right_total R \<Longrightarrow> bi_total R"
unfolding bi_total_alt_def ..

lemma bi_uniqueI: "left_unique R \<Longrightarrow> right_unique R \<Longrightarrow> bi_unique R"
unfolding bi_unique_alt_def ..

end


lemma is_equality_lemma: "(\<And>R. is_equality R \<Longrightarrow> PROP (P R)) \<equiv> PROP (P (=))"
  unfolding is_equality_def
proof (rule equal_intr_rule)
  show "(\<And>R. R = (=) \<Longrightarrow> PROP P R) \<Longrightarrow> PROP P (=)"
    apply (drule meta_spec)
    apply (erule meta_mp [OF _ refl])
    done
qed simp

lemma Domainp_lemma: "(\<And>R. Domainp T = R \<Longrightarrow> PROP (P R)) \<equiv> PROP (P (Domainp T))"
proof (rule equal_intr_rule)
  show "(\<And>R. Domainp T = R \<Longrightarrow> PROP P R) \<Longrightarrow> PROP P (Domainp T)"
    apply (drule meta_spec)
    apply (erule meta_mp [OF _ refl])
    done
qed simp

ML_file \<open>Tools/Transfer/transfer.ML\<close>
declare refl [transfer_rule]

hide_const (open) Rel

context includes lifting_syntax
begin

text \<open>Handling of domains\<close>

lemma Domainp_iff: "Domainp T x \<longleftrightarrow> (\<exists>y. T x y)"
  by auto

lemma Domainp_refl[transfer_domain_rule]:
  "Domainp T = Domainp T" ..

lemma Domain_eq_top[transfer_domain_rule]: "Domainp (=) = top" by auto

lemma Domainp_pred_fun_eq[relator_domain]:
  assumes "left_unique T"
  shows "Domainp (T ===> S) = pred_fun (Domainp T) (Domainp S)"   (is "?lhs = ?rhs")
proof (intro ext iffI)
  fix x
  assume "?lhs x"
  then show "?rhs x"
    using assms unfolding rel_fun_def pred_fun_def by blast
next
  fix x
  assume "?rhs x"
  then have "\<exists>g. \<forall>y xa. T xa y \<longrightarrow> S (x xa) (g y)"
    using assms unfolding Domainp_iff left_unique_def  pred_fun_def
    by (intro choice) blast
  then show "?lhs x"
    by blast
qed

text \<open>Properties are preserved by relation composition.\<close>

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


subsection \<open>Properties of relators\<close>

lemma left_total_eq[transfer_rule]: "left_total (=)"
  unfolding left_total_def by blast

lemma left_unique_eq[transfer_rule]: "left_unique (=)"
  unfolding left_unique_def by blast

lemma right_total_eq [transfer_rule]: "right_total (=)"
  unfolding right_total_def by simp

lemma right_unique_eq [transfer_rule]: "right_unique (=)"
  unfolding right_unique_def by simp

lemma bi_total_eq[transfer_rule]: "bi_total (=)"
  unfolding bi_total_def by simp

lemma bi_unique_eq[transfer_rule]: "bi_unique (=)"
  unfolding bi_unique_def by simp

lemma left_total_fun[transfer_rule]:
  assumes "left_unique A" "left_total B"
  shows "left_total (A ===> B)"
  unfolding left_total_def 
proof
  fix f
  show "Ex ((A ===> B) f)"
    unfolding rel_fun_def
  proof (intro exI strip)
    fix x y
    assume A: "A x y"
    have "(THE x. A x y) = x"
      using A assms by (simp add: left_unique_def the_equality)
    then show "B (f x) (SOME z. B (f (THE x. A x y)) z)"
      using assms by (force simp: left_total_def intro: someI_ex)
  qed
qed

lemma left_unique_fun[transfer_rule]:
  "\<lbrakk>left_total A; left_unique B\<rbrakk> \<Longrightarrow> left_unique (A ===> B)"
  unfolding left_total_def left_unique_def rel_fun_def
  by (clarify, rule ext, fast)

lemma right_total_fun [transfer_rule]:
  assumes "right_unique A" "right_total B"
  shows "right_total (A ===> B)"
  unfolding right_total_def 
proof
  fix g
  show "\<exists>x. (A ===> B) x g"
    unfolding rel_fun_def
  proof (intro exI strip)
    fix x y
    assume A: "A x y"
    have "(THE y. A x y) = y"
      using A assms by (simp add: right_unique_def the_equality)
    then show "B (SOME z. B z (g (THE y. A x y))) (g y)"
      using assms by (force simp: right_total_def intro: someI_ex)
  qed
qed

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

lemma if_conn:
  "(if P \<and> Q then t else e) = (if P then if Q then t else e else e)"
  "(if P \<or> Q then t else e) = (if P then t else if Q then t else e)"
  "(if P \<longrightarrow> Q then t else e) = (if P then if Q then t else e else t)"
  "(if \<not> P then t else e) = (if P then e else t)"
by auto

ML_file \<open>Tools/Transfer/transfer_bnf.ML\<close>
ML_file \<open>Tools/BNF/bnf_fp_rec_sugar_transfer.ML\<close>

declare pred_fun_def [simp]
declare rel_fun_eq [relator_eq]

(* Delete the automated generated rule from the bnf command;
  we have a more general rule (Domainp_pred_fun_eq) that subsumes it. *)
declare fun.Domainp_rel[relator_domain del]

subsection \<open>Transfer rules\<close>

context includes lifting_syntax
begin

lemma Domainp_forall_transfer [transfer_rule]:
  assumes "right_total A"
  shows "((A ===> (=)) ===> (=))
    (transfer_bforall (Domainp A)) transfer_forall"
  using assms unfolding right_total_def
  unfolding transfer_forall_def transfer_bforall_def rel_fun_def Domainp_iff
  by fast

text \<open>Transfer rules using implication instead of equality on booleans.\<close>

lemma transfer_forall_transfer [transfer_rule]:
  "bi_total A \<Longrightarrow> ((A ===> (=)) ===> (=)) transfer_forall transfer_forall"
  "right_total A \<Longrightarrow> ((A ===> (=)) ===> implies) transfer_forall transfer_forall"
  "right_total A \<Longrightarrow> ((A ===> implies) ===> implies) transfer_forall transfer_forall"
  "bi_total A \<Longrightarrow> ((A ===> (=)) ===> rev_implies) transfer_forall transfer_forall"
  "bi_total A \<Longrightarrow> ((A ===> rev_implies) ===> rev_implies) transfer_forall transfer_forall"
  unfolding transfer_forall_def rev_implies_def rel_fun_def right_total_def bi_total_def
  by fast+

lemma transfer_implies_transfer [transfer_rule]:
  "((=)        ===> (=)        ===> (=)       ) transfer_implies transfer_implies"
  "(rev_implies ===> implies     ===> implies    ) transfer_implies transfer_implies"
  "(rev_implies ===> (=)        ===> implies    ) transfer_implies transfer_implies"
  "((=)        ===> implies     ===> implies    ) transfer_implies transfer_implies"
  "((=)        ===> (=)        ===> implies    ) transfer_implies transfer_implies"
  "(implies     ===> rev_implies ===> rev_implies) transfer_implies transfer_implies"
  "(implies     ===> (=)        ===> rev_implies) transfer_implies transfer_implies"
  "((=)        ===> rev_implies ===> rev_implies) transfer_implies transfer_implies"
  "((=)        ===> (=)        ===> rev_implies) transfer_implies transfer_implies"
  unfolding transfer_implies_def rev_implies_def rel_fun_def by auto

lemma eq_imp_transfer [transfer_rule]:
  "right_unique A \<Longrightarrow> (A ===> A ===> (\<longrightarrow>)) (=) (=)"
  unfolding right_unique_alt_def2 .

text \<open>Transfer rules using equality.\<close>

lemma left_unique_transfer [transfer_rule]:
  assumes "right_total A"
  assumes "right_total B"
  assumes "bi_unique A"
  shows "((A ===> B ===> (=)) ===> implies) left_unique left_unique"
  using assms unfolding left_unique_def right_total_def bi_unique_def rel_fun_def
  by metis

lemma eq_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> A ===> (=)) (=) (=)"
  using assms unfolding bi_unique_def rel_fun_def by auto

lemma right_total_Ex_transfer[transfer_rule]:
  assumes "right_total A"
  shows "((A ===> (=)) ===> (=)) (Bex (Collect (Domainp A))) Ex"
  using assms unfolding right_total_def Bex_def rel_fun_def Domainp_iff
  by fast

lemma right_total_All_transfer[transfer_rule]:
  assumes "right_total A"
  shows "((A ===> (=)) ===> (=)) (Ball (Collect (Domainp A))) All"
  using assms unfolding right_total_def Ball_def rel_fun_def Domainp_iff
  by fast

context
  includes lifting_syntax
begin

lemma right_total_fun_eq_transfer:
  assumes [transfer_rule]: "right_total A" "bi_unique B"
  shows "((A ===> B) ===> (A ===> B) ===> (=)) (\<lambda>f g. \<forall>x\<in>Collect(Domainp A). f x = g x) (=)"
  unfolding fun_eq_iff
  by transfer_prover

end

lemma All_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> (=)) ===> (=)) All All"
  using assms unfolding bi_total_def rel_fun_def by fast

lemma Ex_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "((A ===> (=)) ===> (=)) Ex Ex"
  using assms unfolding bi_total_def rel_fun_def by fast

lemma Ex1_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "bi_total A"
  shows "((A ===> (=)) ===> (=)) Ex1 Ex1"
unfolding Ex1_def by transfer_prover

declare If_transfer [transfer_rule]

lemma Let_transfer [transfer_rule]: "(A ===> (A ===> B) ===> B) Let Let"
  unfolding rel_fun_def by simp

declare id_transfer [transfer_rule]

declare comp_transfer [transfer_rule]

lemma curry_transfer [transfer_rule]:
  "((rel_prod A B ===> C) ===> A ===> B ===> C) curry curry"
  unfolding curry_def by transfer_prover

lemma fun_upd_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> B) ===> A ===> B ===> A ===> B) fun_upd fun_upd"
  unfolding fun_upd_def  by transfer_prover

lemma case_nat_transfer [transfer_rule]:
  "(A ===> ((=) ===> A) ===> (=) ===> A) case_nat case_nat"
  unfolding rel_fun_def by (simp split: nat.split)

lemma rec_nat_transfer [transfer_rule]:
  "(A ===> ((=) ===> A ===> A) ===> (=) ===> A) rec_nat rec_nat"
  unfolding rel_fun_def
  apply safe
  subgoal for _ _ _ _ _ n
    by (induction n) simp_all
  done


lemma funpow_transfer [transfer_rule]:
  "((=) ===> (A ===> A) ===> (A ===> A)) compow compow"
  unfolding funpow_def by transfer_prover

lemma mono_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
  assumes [transfer_rule]: "(A ===> A ===> (=)) (\<le>) (\<le>)"
  assumes [transfer_rule]: "(B ===> B ===> (=)) (\<le>) (\<le>)"
  shows "((A ===> B) ===> (=)) mono mono"
unfolding mono_def by transfer_prover

lemma right_total_relcompp_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total B"
  shows "((A ===> B ===> (=)) ===> (B ===> C ===> (=)) ===> A ===> C ===> (=))
    (\<lambda>R S x z. \<exists>y\<in>Collect (Domainp B). R x y \<and> S y z) (OO)"
unfolding OO_def by transfer_prover

lemma relcompp_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_total B"
  shows "((A ===> B ===> (=)) ===> (B ===> C ===> (=)) ===> A ===> C ===> (=)) (OO) (OO)"
unfolding OO_def by transfer_prover

lemma right_total_Domainp_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total B"
  shows "((A ===> B ===> (=)) ===> A ===> (=)) (\<lambda>T x. \<exists>y\<in>Collect(Domainp B). T x y) Domainp"
apply(subst(2) Domainp_iff[abs_def]) by transfer_prover

lemma Domainp_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_total B"
  shows "((A ===> B ===> (=)) ===> A ===> (=)) Domainp Domainp"
unfolding Domainp_iff by transfer_prover

lemma reflp_transfer[transfer_rule]:
  "bi_total A \<Longrightarrow> ((A ===> A ===> (=)) ===> (=)) reflp reflp"
  "right_total A \<Longrightarrow> ((A ===> A ===> implies) ===> implies) reflp reflp"
  "right_total A \<Longrightarrow> ((A ===> A ===> (=)) ===> implies) reflp reflp"
  "bi_total A \<Longrightarrow> ((A ===> A ===> rev_implies) ===> rev_implies) reflp reflp"
  "bi_total A \<Longrightarrow> ((A ===> A ===> (=)) ===> rev_implies) reflp reflp"
unfolding reflp_def rev_implies_def bi_total_def right_total_def rel_fun_def
by fast+

lemma right_unique_transfer [transfer_rule]:
  "\<lbrakk> right_total A; right_total B; bi_unique B \<rbrakk>
  \<Longrightarrow> ((A ===> B ===> (=)) ===> implies) right_unique right_unique"
unfolding right_unique_def right_total_def bi_unique_def rel_fun_def
by metis

lemma left_total_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_total B"
  shows "((A ===> B ===> (=)) ===> (=)) left_total left_total"
unfolding left_total_def by transfer_prover

lemma right_total_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_total B"
  shows "((A ===> B ===> (=)) ===> (=)) right_total right_total"
unfolding right_total_def by transfer_prover

lemma left_unique_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "bi_total A" "bi_total B"
  shows "((A ===> B ===> (=)) ===> (=)) left_unique left_unique"
unfolding left_unique_def by transfer_prover

lemma prod_pred_parametric [transfer_rule]:
  "((A ===> (=)) ===> (B ===> (=)) ===> rel_prod A B ===> (=)) pred_prod pred_prod"
unfolding prod.pred_set Basic_BNFs.fsts_def Basic_BNFs.snds_def fstsp.simps sndsp.simps 
by simp transfer_prover

lemma apfst_parametric [transfer_rule]:
  "((A ===> B) ===> rel_prod A C ===> rel_prod B C) apfst apfst"
unfolding apfst_def by transfer_prover

lemma rel_fun_eq_eq_onp: "((=) ===> eq_onp P) = eq_onp (\<lambda>f. \<forall>x. P(f x))"
unfolding eq_onp_def rel_fun_def by auto

lemma rel_fun_eq_onp_rel:
  shows "((eq_onp R) ===> S) = (\<lambda>f g. \<forall>x. R x \<longrightarrow> S (f x) (g x))"
by (auto simp add: eq_onp_def rel_fun_def)

lemma eq_onp_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> (=)) ===> A ===> A ===> (=)) eq_onp eq_onp"
unfolding eq_onp_def by transfer_prover

lemma rtranclp_parametric [transfer_rule]:
  assumes "bi_unique A" "bi_total A"
  shows "((A ===> A ===> (=)) ===> A ===> A ===> (=)) rtranclp rtranclp"
proof(rule rel_funI iffI)+
  fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and R' x y x' y'
  assume R: "(A ===> A ===> (=)) R R'" and "A x x'"
  {
    assume "R\<^sup>*\<^sup>* x y" "A y y'"
    thus "R'\<^sup>*\<^sup>* x' y'"
    proof(induction arbitrary: y')
      case base
      with \<open>bi_unique A\<close> \<open>A x x'\<close> have "x' = y'" by(rule bi_uniqueDr)
      thus ?case by simp
    next
      case (step y z z')
      from \<open>bi_total A\<close> obtain y' where "A y y'" unfolding bi_total_def by blast
      hence "R'\<^sup>*\<^sup>* x' y'" by(rule step.IH)
      moreover from R \<open>A y y'\<close> \<open>A z z'\<close> \<open>R y z\<close>
      have "R' y' z'" by(auto dest: rel_funD)
      ultimately show ?case ..
    qed
  next
    assume "R'\<^sup>*\<^sup>* x' y'" "A y y'"
    thus "R\<^sup>*\<^sup>* x y"
    proof(induction arbitrary: y)
      case base
      with \<open>bi_unique A\<close> \<open>A x x'\<close> have "x = y" by(rule bi_uniqueDl)
      thus ?case by simp
    next
      case (step y' z' z)
      from \<open>bi_total A\<close> obtain y where "A y y'" unfolding bi_total_def by blast
      hence "R\<^sup>*\<^sup>* x y" by(rule step.IH)
      moreover from R \<open>A y y'\<close> \<open>A z z'\<close> \<open>R' y' z'\<close>
      have "R y z" by(auto dest: rel_funD)
      ultimately show ?case ..
    qed
  }
qed

lemma right_unique_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A" "bi_unique B" "bi_total B"
  shows "((A ===> B ===> (=)) ===> (=)) right_unique right_unique"
  unfolding right_unique_def by transfer_prover

lemma map_fun_parametric [transfer_rule]:
  "((A ===> B) ===> (C ===> D) ===> (B ===> C) ===> A ===> D) map_fun map_fun"
  unfolding map_fun_def by transfer_prover

end


subsection \<open>\<^const>\<open>of_bool\<close> and \<^const>\<open>of_nat\<close>\<close>

context
  includes lifting_syntax
begin

lemma transfer_rule_of_bool:
  \<open>((\<longleftrightarrow>) ===> (\<cong>)) of_bool of_bool\<close>
    if [transfer_rule]: \<open>0 \<cong> 0\<close> \<open>1 \<cong> 1\<close>
    for R :: \<open>'a::zero_neq_one \<Rightarrow> 'b::zero_neq_one \<Rightarrow> bool\<close>  (infix \<open>\<cong>\<close> 50)
  unfolding of_bool_def by transfer_prover

lemma transfer_rule_of_nat:
  "((=) ===> (\<cong>)) of_nat of_nat"
    if [transfer_rule]: \<open>0 \<cong> 0\<close> \<open>1 \<cong> 1\<close>
    \<open>((\<cong>) ===> (\<cong>) ===> (\<cong>)) (+) (+)\<close>
  for R :: \<open>'a::semiring_1 \<Rightarrow> 'b::semiring_1 \<Rightarrow> bool\<close>  (infix \<open>\<cong>\<close> 50)
  unfolding of_nat_def by transfer_prover

end

end
