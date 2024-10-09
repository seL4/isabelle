(*
  File:    Going_To_Filter.thy
  Author:  Manuel Eberl, TU München

  A filter describing the points x such that f(x) tends to some other filter.
*)

section \<open>The \<open>going_to\<close> filter\<close>

theory Going_To_Filter
  imports Complex_Main
begin

definition going_to_within :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b filter \<Rightarrow> 'a set \<Rightarrow> 'a filter"
    (\<open>(\<open>open_block notation=\<open>mixfix going_to_within\<close>\<close>(_)/ going'_to (_)/ within (_))\<close> [1000,60,60] 60)
  where "f going_to F within A = inf (filtercomap f F) (principal A)"

abbreviation going_to :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b filter \<Rightarrow> 'a filter"
    (infix \<open>going'_to\<close> 60)
    where "f going_to F \<equiv> f going_to F within UNIV"

text \<open>
  The \<open>going_to\<close> filter is, in a sense, the opposite of \<^term>\<open>filtermap\<close>. 
  It corresponds to the intuition of, given a function $f: A \to B$ and a filter $F$ on the 
  range of $B$, looking at such values of $x$ that $f(x)$ approaches $F$. This can be 
  written as \<^term>\<open>f going_to F\<close>.
  
  A classic example is the \<^term>\<open>at_infinity\<close> filter, which describes the neigbourhood
  of infinity (i.\,e.\ all values sufficiently far away from the zero). This can also be written
  as \<^term>\<open>norm going_to at_top\<close>.

  Additionally, the \<open>going_to\<close> filter can be restricted with an optional `within' parameter.
  For instance, if one would would want to consider the filter of complex numbers near infinity
  that do not lie on the negative real line, one could write 
  \<^term>\<open>norm going_to at_top within - complex_of_real ` {..0}\<close>.

  A third, less mathematical example lies in the complexity analysis of algorithms.
  Suppose we wanted to say that an algorithm on lists takes $O(n^2)$ time where $n$ is 
  the length of the input list. We can write this using the Landau symbols from the AFP,
  where the underlying filter is \<^term>\<open>length going_to at_top\<close>. If, on the other hand,
  we want to look the complexity of the algorithm on sorted lists, we could use the filter
  \<^term>\<open>length going_to at_top within {xs. sorted xs}\<close>.
\<close>

lemma going_to_def: "f going_to F = filtercomap f F"
  by (simp add: going_to_within_def)

lemma eventually_going_toI [intro]: 
  assumes "eventually P F"
  shows   "eventually (\<lambda>x. P (f x)) (f going_to F)"
  using assms by (auto simp: going_to_def)

lemma filterlim_going_toI_weak [intro]: "filterlim f F (f going_to F within A)"
  unfolding going_to_within_def
  by (meson filterlim_filtercomap filterlim_iff inf_le1 le_filter_def)

lemma going_to_mono: "F \<le> G \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f going_to F within A \<le> f going_to G within B"
  unfolding going_to_within_def by (intro inf_mono filtercomap_mono) simp_all

lemma going_to_inf: 
  "f going_to (inf F G) within A = inf (f going_to F within A) (f going_to G within A)"
  by (simp add: going_to_within_def filtercomap_inf inf_assoc inf_commute inf_left_commute)

lemma going_to_sup: 
  "f going_to (sup F G) within A \<ge> sup (f going_to F within A) (f going_to G within A)"
  by (auto simp: going_to_within_def intro!: inf.coboundedI1 filtercomap_sup filtercomap_mono)

lemma going_to_top [simp]: "f going_to top within A = principal A"
  by (simp add: going_to_within_def)
    
lemma going_to_bot [simp]: "f going_to bot within A = bot"
  by (simp add: going_to_within_def)
    
lemma going_to_principal: 
  "f going_to principal A within B = principal (f -` A \<inter> B)"
  by (simp add: going_to_within_def)
    
lemma going_to_within_empty [simp]: "f going_to F within {} = bot"
  by (simp add: going_to_within_def)

lemma going_to_within_union [simp]: 
  "f going_to F within (A \<union> B) = sup (f going_to F within A) (f going_to F within B)"
  by (simp add: going_to_within_def flip: inf_sup_distrib1)

lemma eventually_going_to_at_top_linorder:
  fixes f :: "'a \<Rightarrow> 'b :: linorder"
  shows "eventually P (f going_to at_top within A) \<longleftrightarrow> (\<exists>C. \<forall>x\<in>A. f x \<ge> C \<longrightarrow> P x)"
  unfolding going_to_within_def eventually_filtercomap 
    eventually_inf_principal eventually_at_top_linorder by fast

lemma eventually_going_to_at_bot_linorder:
  fixes f :: "'a \<Rightarrow> 'b :: linorder"
  shows "eventually P (f going_to at_bot within A) \<longleftrightarrow> (\<exists>C. \<forall>x\<in>A. f x \<le> C \<longrightarrow> P x)"
  unfolding going_to_within_def eventually_filtercomap 
    eventually_inf_principal eventually_at_bot_linorder by fast

lemma eventually_going_to_at_top_dense:
  fixes f :: "'a \<Rightarrow> 'b :: {linorder,no_top}"
  shows "eventually P (f going_to at_top within A) \<longleftrightarrow> (\<exists>C. \<forall>x\<in>A. f x > C \<longrightarrow> P x)"
  unfolding going_to_within_def eventually_filtercomap 
    eventually_inf_principal eventually_at_top_dense by fast

lemma eventually_going_to_at_bot_dense:
  fixes f :: "'a \<Rightarrow> 'b :: {linorder,no_bot}"
  shows "eventually P (f going_to at_bot within A) \<longleftrightarrow> (\<exists>C. \<forall>x\<in>A. f x < C \<longrightarrow> P x)"
  unfolding going_to_within_def eventually_filtercomap 
    eventually_inf_principal eventually_at_bot_dense by fast
               
lemma eventually_going_to_nhds:
  "eventually P (f going_to nhds a within A) \<longleftrightarrow> 
     (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>A. f x \<in> S \<longrightarrow> P x))"
  unfolding going_to_within_def eventually_filtercomap eventually_inf_principal
    eventually_nhds by fast

lemma eventually_going_to_at:
  "eventually P (f going_to (at a within B) within A) \<longleftrightarrow> 
     (\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>A. f x \<in> B \<inter> S - {a} \<longrightarrow> P x))"
  unfolding at_within_def going_to_inf eventually_inf_principal
            eventually_going_to_nhds going_to_principal by fast

lemma norm_going_to_at_top_eq: "norm going_to at_top = at_infinity"
  by (simp add: eventually_at_infinity eventually_going_to_at_top_linorder filter_eq_iff)

lemmas at_infinity_altdef = norm_going_to_at_top_eq [symmetric]

end
