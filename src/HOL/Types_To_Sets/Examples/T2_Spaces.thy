(*  Title:      HOL/Types_To_Sets/Examples/T2_Spaces.thy
    Author:     Ondřej Kunčar, TU München
*)

theory T2_Spaces
  imports Complex_Main "../Types_To_Sets" Prerequisites
begin

section \<open>The Type-Based Theorem\<close>

text\<open>We relativize a theorem that contains a type class with an associated (overloaded) operation.
     The key technique is to compile out the overloaded operation by the dictionary construction
     using the Unoverloading rule.\<close>

text\<open>This is the type-based statement that we want to relativize.\<close>
thm compact_imp_closed
text\<open>The type is class a T2 typological space.\<close>
typ "'a :: t2_space"
text\<open>The associated operation is the predicate open that determines the open sets in the T2 space.\<close>
term "open"

section \<open>Definitions and Setup for The Relativization\<close>

text\<open>We gradually define relativization of topological spaces, t2 spaces, compact and closed
     predicates and prove that they are indeed the relativization of the original predicates.\<close>

definition topological_space_on_with :: "'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> bool"
  where "topological_space_on_with A \<equiv> \<lambda>open. open A \<and>
    (\<forall>S \<subseteq> A. \<forall>T \<subseteq> A. open S \<longrightarrow> open T \<longrightarrow> open (S \<inter> T))
    \<and> (\<forall>K \<subseteq> Pow A. (\<forall>S\<in>K. open S) \<longrightarrow> open (\<Union>K))"

lemma topological_space_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> (=)) (topological_space_on_with (Collect (Domainp T)))
    class.topological_space"
  unfolding topological_space_on_with_def[abs_def] class.topological_space_def[abs_def]
  apply transfer_prover_start
  apply transfer_step+
  unfolding Pow_def Ball_Collect[symmetric]
  by blast

definition t2_space_on_with :: "'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> bool"
  where "t2_space_on_with A \<equiv> \<lambda>open. topological_space_on_with A open \<and>
  (\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y \<longrightarrow> (\<exists>U\<subseteq>A. \<exists>V\<subseteq>A. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))"

lemma t2_space_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> (=)) (t2_space_on_with (Collect (Domainp T))) class.t2_space"
  unfolding t2_space_on_with_def[abs_def] class.t2_space_def[abs_def]
    class.t2_space_axioms_def[abs_def]
  apply transfer_prover_start
  apply transfer_step+
  unfolding Ball_Collect[symmetric]
  by blast

definition closed_with :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "closed_with \<equiv> \<lambda>open S. open (- S)"

lemma closed_closed_with: "closed s = closed_with open s"
  unfolding closed_with_def closed_def[abs_def] ..

definition closed_on_with :: "'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "closed_on_with A \<equiv> \<lambda>open S. open (-S \<inter> A)"

lemma closed_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> rel_set T===> (=)) (closed_on_with (Collect (Domainp T)))
    closed_with"
  unfolding closed_with_def closed_on_with_def by transfer_prover

definition compact_with :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "compact_with \<equiv> \<lambda>open S. (\<forall>C. (\<forall>c\<in>C. open c) \<and> S \<subseteq> \<Union>C \<longrightarrow> (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D))"

lemma compact_compact_with: "compact s = compact_with open s"
  unfolding compact_with_def compact_eq_heine_borel[abs_def] ..

definition compact_on_with :: "'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "compact_on_with A \<equiv> \<lambda>open S. (\<forall>C\<subseteq>Pow A. (\<forall>c\<in>C. open c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
    (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D))"

lemma compact_on_with_subset_trans: "(\<forall>C\<subseteq>Pow A. (\<forall>c\<in>C. open' c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
  (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D)) =
  ((\<forall>C\<subseteq>Pow A. (\<forall>c\<in>C. open' c) \<and> S \<subseteq> \<Union>C \<longrightarrow> (\<exists>D\<subseteq>Pow A. D\<subseteq>C \<and> finite D \<and> S \<subseteq> \<Union>D)))"
  by (meson subset_trans)

lemma compact_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total T" "bi_unique T"
  shows "((rel_set T ===> (=)) ===> rel_set T===> (=)) (compact_on_with (Collect (Domainp T)))
    compact_with"
  unfolding compact_with_def compact_on_with_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding compact_on_with_subset_trans
  unfolding Pow_def Ball_Collect[symmetric] Ball_def Bex_def mem_Collect_eq
  by blast

setup \<open>Sign.add_const_constraint
  (@{const_name "open"}, SOME @{typ "'a set \<Rightarrow> bool"})\<close>

text\<open>The aforementioned development can be automated. The main part is already automated
     by the transfer_prover.\<close>

section \<open>The Relativization to The Set-Based Theorem\<close>

text\<open>The first step of the dictionary construction.\<close>
lemmas dictionary_first_step = compact_imp_closed[unfolded compact_compact_with closed_closed_with]
thm dictionary_first_step

text\<open>Internalization of the type class t2_space.\<close>
lemmas internalized_sort = dictionary_first_step[internalize_sort "'a::t2_space"]
thm internalized_sort

text\<open>We unoverload the overloaded constant open and thus finish compiling out of it.\<close>
lemmas dictionary_second_step =  internalized_sort[unoverload "open :: 'a set \<Rightarrow> bool"]
text\<open>The theorem with internalized type classes and compiled out operations is the starting point
     for the original relativization algorithm.\<close>
thm dictionary_second_step

text \<open>Alternative construction using \<open>unoverload_type\<close>
  (This does not require fiddling with \<open>Sign.add_const_constraint\<close>).\<close>
lemmas dictionary_second_step' = dictionary_first_step[unoverload_type 'a]

text\<open>This is the set-based variant of the theorem compact_imp_closed.\<close>
lemma compact_imp_closed_set_based:
  assumes "(A::'a set) \<noteq> {}"
  shows "\<forall>open. t2_space_on_with A open \<longrightarrow> (\<forall>S\<subseteq>A. compact_on_with A open S \<longrightarrow>
    closed_on_with A open S)"
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
      using dictionary_second_step[where 'a = 'b, untransferred, simplified]
      by blast

  } note * = this[cancel_type_definition, OF assms]

  show ?thesis by (rule *)
qed

setup \<open>Sign.add_const_constraint
  (@{const_name "open"}, SOME @{typ "'a::topological_space set \<Rightarrow> bool"})\<close>

text\<open>The Final Result. We can compare the type-based and the set-based statement.\<close>
thm compact_imp_closed compact_imp_closed_set_based

declare [[show_sorts]]
text\<open>The Final Result. This time with explicitly shown type-class annotations.\<close>
thm compact_imp_closed compact_imp_closed_set_based

end
