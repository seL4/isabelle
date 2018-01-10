(*  Title:      HOL/Types_To_Sets/Examples/Finite.thy
    Author:     Ondřej Kunčar, TU München
*)

theory Finite
  imports "../Types_To_Sets" Prerequisites
begin

section \<open>The Type-Based Theorem\<close>

text\<open>This example file shows how we perform the relativization in presence of axiomatic
  type classes: we internalize them.\<close>

definition injective :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "injective f \<equiv> (\<forall>x y. f x = f y \<longrightarrow> x = y)"

text\<open>We want to relativize the following type-based theorem using the type class finite.\<close>

lemma type_based: "\<exists>f :: 'a::finite \<Rightarrow> nat. injective f"
  unfolding injective_def
  using finite_imp_inj_to_nat_seg[of "UNIV::'a set", unfolded inj_on_def] by auto

section \<open>Definitions and Setup for The Relativization\<close>

text\<open>We have to define what being injective on a set means.\<close>

definition injective_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "injective_on A f \<equiv> \<forall>x \<in> A. \<forall>y \<in> A. f x = f y \<longrightarrow> x = y"

text\<open>The predicate injective_on is the relativization of the predicate injective.\<close>

lemma injective_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T"
  assumes [transfer_rule]: "bi_unique T"
  shows "((T ===> (=)) ===> (=)) (injective_on (Collect(Domainp T))) injective"
  unfolding injective_on_def[abs_def] injective_def[abs_def] by transfer_prover

text\<open>Similarly, we define the relativization of the internalization
     of the type class finite, class.finite\<close>

definition finite_on :: "'a set => bool" where "finite_on A = finite A"

lemma class_finite_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total (T::'a\<Rightarrow>'b\<Rightarrow>bool)"
  assumes [transfer_rule]: "bi_unique T"
  shows "(=) (finite_on (Collect(Domainp T))) (class.finite TYPE('b))"
  unfolding finite_on_def class.finite_def by transfer_prover

text\<open>The aforementioned development can be automated. The main part is already automated
     by the transfer_prover.\<close>

section \<open>The Relativization to The Set-Based Theorem\<close>

lemmas internalized = type_based[internalize_sort "'a::finite"]
text\<open>We internalized the type class finite and thus reduced the task to the
  original relativization algorithm.\<close>
thm internalized

text\<open>This is the set-based variant.\<close>

lemma set_based:
  assumes "(A::'a set) \<noteq> {}"
  shows "finite_on A \<longrightarrow> (\<exists>f :: 'a \<Rightarrow> nat. injective_on A f)"
proof -
  {
    text\<open>We define the type 'b to be isomorphic to A.\<close>
    assume T: "\<exists>(Rep :: 'b \<Rightarrow> 'a) Abs. type_definition Rep Abs A"
    from T obtain rep :: "'b \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'b" where t: "type_definition rep abs A"
      by auto

    text\<open>Setup for the Transfer tool.\<close>
    define cr_b where "cr_b == \<lambda>r a. r = rep a"
    note type_definition_Domainp[OF t cr_b_def, transfer_domain_rule]
    note typedef_right_total[OF t cr_b_def, transfer_rule]
    note typedef_bi_unique[OF t cr_b_def, transfer_rule]

    have ?thesis
      text\<open>Relativization by the Transfer tool.\<close>
      using internalized[where 'a = 'b, untransferred, simplified]
      by blast
  } note * = this[cancel_type_definition, OF assms] text\<open>We removed the definition of 'b.\<close>

  show ?thesis by (rule *)
qed

text\<open>The Final Result. We can compare the type-based and the set-based statement.\<close>
thm type_based set_based

end
