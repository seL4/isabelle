(*  
  Title:    Random_Permutations.thy
  Author:   Manuel Eberl, TU München

  Random permutations and folding over them.
  This provides the basic theory for the concept of doing something
  in a random order, e.g. inserting elements from a fixed set into a 
  data structure in random order.
*)

section \<open>Random Permutations\<close>

theory Random_Permutations
imports 
  "HOL-Combinatorics.Multiset_Permutations"
  Probability_Mass_Function
begin

text \<open>
  Choosing a set permutation (i.e. a distinct list with the same elements as the set)
  uniformly at random is the same as first choosing the first element of the list
  and then choosing the rest of the list as a permutation of the remaining set.
\<close>
lemma random_permutation_of_set:
  assumes "finite A" "A \<noteq> {}"
  shows   "pmf_of_set (permutations_of_set A) = 
             do {
               x \<leftarrow> pmf_of_set A;
               xs \<leftarrow> pmf_of_set (permutations_of_set (A - {x})); 
               return_pmf (x#xs)
             }" (is "?lhs = ?rhs")
proof -
  from assms have "permutations_of_set A = (\<Union>x\<in>A. (#) x ` permutations_of_set (A - {x}))"
    by (simp add: permutations_of_set_nonempty)
  also from assms have "pmf_of_set \<dots> = ?rhs"
    by (subst pmf_of_set_UN[where n = "fact (card A - 1)"])
       (auto simp: card_image disjoint_family_on_def map_pmf_def [symmetric] map_pmf_of_set_inj)
  finally show ?thesis .
qed


text \<open>
  A generic fold function that takes a function, an initial state, and a set 
  and chooses a random order in which it then traverses the set in the same 
  fashion as a left fold over a list.
    We first give a recursive definition.
\<close>
function fold_random_permutation :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b pmf" where
  "fold_random_permutation f x {} = return_pmf x"
| "\<not>finite A \<Longrightarrow> fold_random_permutation f x A = return_pmf x"
| "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> 
     fold_random_permutation f x A = 
       pmf_of_set A \<bind> (\<lambda>a. fold_random_permutation f (f a x) (A - {a}))"
  by simp_all fastforce
termination proof (relation "Wellfounded.measure (\<lambda>(_,_,A). card A)")
  fix A :: "'a set" and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and x :: 'b and y :: 'a
  assume A: "finite A" "A \<noteq> {}" "y \<in> set_pmf (pmf_of_set A)"
  then have "card A > 0" by (simp add: card_gt_0_iff)
  with A show "((f, f y x, A - {y}), f, x, A) \<in> Wellfounded.measure (\<lambda>(_, _, A). card A)"
    by simp
qed simp_all


text \<open>
  We can now show that the above recursive definition is equivalent to 
  choosing a random set permutation and folding over it (in any direction).
\<close>
lemma fold_random_permutation_foldl:
  assumes "finite A"
  shows   "fold_random_permutation f x A =
             map_pmf (foldl (\<lambda>x y. f y x) x) (pmf_of_set (permutations_of_set A))"
using assms
proof (induction f x A rule: fold_random_permutation.induct [case_names empty infinite remove])
  case (remove A f x)
  from remove 
    have "fold_random_permutation f x A = 
            pmf_of_set A \<bind> (\<lambda>a. fold_random_permutation f (f a x) (A - {a}))" by simp
  also from remove
    have "\<dots> = pmf_of_set A \<bind> (\<lambda>a. map_pmf (foldl (\<lambda>x y. f y x) x)
                 (map_pmf ((#) a) (pmf_of_set (permutations_of_set (A - {a})))))"
      by (intro bind_pmf_cong) (simp_all add: pmf.map_comp o_def)
  also from remove have "\<dots> = map_pmf (foldl (\<lambda>x y. f y x) x) (pmf_of_set (permutations_of_set A))"
    by (simp_all add: random_permutation_of_set map_bind_pmf map_pmf_def [symmetric])
  finally show ?case .
qed (simp_all add: pmf_of_set_singleton)

lemma fold_random_permutation_foldr:
  assumes "finite A"
  shows   "fold_random_permutation f x A =
             map_pmf (\<lambda>xs. foldr f xs x) (pmf_of_set (permutations_of_set A))"
proof -
  have "fold_random_permutation f x A =
          map_pmf (foldl (\<lambda>x y. f y x) x \<circ> rev) (pmf_of_set (permutations_of_set A))"
    using assms by (subst fold_random_permutation_foldl [OF assms])
                   (simp_all add: pmf.map_comp [symmetric] map_pmf_of_set_inj)
  also have "foldl (\<lambda>x y. f y x) x \<circ> rev = (\<lambda>xs. foldr f xs x)"
    by (intro ext) (simp add: foldl_conv_foldr)
  finally show ?thesis .
qed

lemma fold_random_permutation_fold:
  assumes "finite A"
  shows   "fold_random_permutation f x A =
             map_pmf (\<lambda>xs. fold f xs x) (pmf_of_set (permutations_of_set A))"
  by (subst fold_random_permutation_foldl [OF assms], intro map_pmf_cong)
     (simp_all add: foldl_conv_fold)
     
lemma fold_random_permutation_code [code]: 
  "fold_random_permutation f x (set xs) =
     map_pmf (foldl (\<lambda>x y. f y x) x) (pmf_of_set (permutations_of_set (set xs)))"
  by (simp add: fold_random_permutation_foldl)

text \<open>
  We now introduce a slightly generalised version of the above fold 
  operation that does not simply return the result in the end, but applies
  a monadic bind to it.
    This may seem somewhat arbitrary, but it is a common use case, e.g. 
  in the Social Decision Scheme of Random Serial Dictatorship, where 
  voters narrow down a set of possible winners in a random order and 
  the winner is chosen from the remaining set uniformly at random.
\<close>
function fold_bind_random_permutation 
    :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c pmf) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'c pmf" where
  "fold_bind_random_permutation f g x {} = g x"
| "\<not>finite A \<Longrightarrow> fold_bind_random_permutation f g x A = g x"
| "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> 
     fold_bind_random_permutation f g x A = 
       pmf_of_set A \<bind> (\<lambda>a. fold_bind_random_permutation f g (f a x) (A - {a}))"
  by simp_all fastforce
termination proof (relation "Wellfounded.measure (\<lambda>(_,_,_,A). card A)")
  fix A :: "'a set" and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and x :: 'b 
    and y :: 'a and g :: "'b \<Rightarrow> 'c pmf"
  assume A: "finite A" "A \<noteq> {}" "y \<in> set_pmf (pmf_of_set A)"
  then have "card A > 0" by (simp add: card_gt_0_iff)
  with A show "((f, g, f y x, A - {y}), f, g, x, A) \<in> Wellfounded.measure (\<lambda>(_, _, _, A). card A)"
    by simp
qed simp_all

text \<open>
  We now show that the recursive definition is equivalent to 
  a random fold followed by a monadic bind.
\<close>
lemma fold_bind_random_permutation_altdef [code]:
  "fold_bind_random_permutation f g x A = fold_random_permutation f x A \<bind> g"
proof (induction f x A rule: fold_random_permutation.induct [case_names empty infinite remove])
  case (remove A f x)
  from remove have "pmf_of_set A \<bind> (\<lambda>a. fold_bind_random_permutation f g (f a x) (A - {a})) =
                      pmf_of_set A \<bind> (\<lambda>a. fold_random_permutation f (f a x) (A - {a}) \<bind> g)"
    by (intro bind_pmf_cong) simp_all
  with remove show ?case by (simp add: bind_return_pmf bind_assoc_pmf)
qed (simp_all add: bind_return_pmf)


text \<open>
  We can now derive the following nice monadic representations of the 
  combined fold-and-bind:
\<close>
lemma fold_bind_random_permutation_foldl:
  assumes "finite A"
  shows   "fold_bind_random_permutation f g x A =
             do {xs \<leftarrow> pmf_of_set (permutations_of_set A); g (foldl (\<lambda>x y. f y x) x xs)}"
  using assms by (simp add: fold_bind_random_permutation_altdef bind_assoc_pmf
                            fold_random_permutation_foldl bind_return_pmf map_pmf_def)

lemma fold_bind_random_permutation_foldr:
  assumes "finite A"
  shows   "fold_bind_random_permutation f g x A =
             do {xs \<leftarrow> pmf_of_set (permutations_of_set A); g (foldr f xs x)}"
  using assms by (simp add: fold_bind_random_permutation_altdef bind_assoc_pmf
                            fold_random_permutation_foldr bind_return_pmf map_pmf_def)

lemma fold_bind_random_permutation_fold:
  assumes "finite A"
  shows   "fold_bind_random_permutation f g x A =
             do {xs \<leftarrow> pmf_of_set (permutations_of_set A); g (fold f xs x)}"
  using assms by (simp add: fold_bind_random_permutation_altdef bind_assoc_pmf
                            fold_random_permutation_fold bind_return_pmf map_pmf_def)

text \<open>
  The following useful lemma allows us to swap partitioning a set w.\,r.\,t.\ a 
  predicate and drawing a random permutation of that set.
\<close>
lemma partition_random_permutations:
  assumes "finite A"
  shows   "map_pmf (partition P) (pmf_of_set (permutations_of_set A)) = 
             pair_pmf (pmf_of_set (permutations_of_set {x\<in>A. P x}))
                      (pmf_of_set (permutations_of_set {x\<in>A. \<not>P x}))" (is "?lhs = ?rhs")
proof (rule pmf_eqI, clarify, goal_cases)
  case (1 xs ys)
  show ?case
  proof (cases "xs \<in> permutations_of_set {x\<in>A. P x} \<and> ys \<in> permutations_of_set {x\<in>A. \<not>P x}")
    case True
    let ?n1 = "card {x\<in>A. P x}" and ?n2 = "card {x\<in>A. \<not>P x}"
    have card_eq: "card A = ?n1 + ?n2"
    proof -
      have "?n1 + ?n2 = card ({x\<in>A. P x} \<union> {x\<in>A. \<not>P x})"
        using assms by (intro card_Un_disjoint [symmetric]) auto
      also have "{x\<in>A. P x} \<union> {x\<in>A. \<not>P x} = A" by blast
      finally show ?thesis ..
    qed

    from True have lengths [simp]: "length xs = ?n1" "length ys = ?n2"
      by (auto intro!: length_finite_permutations_of_set)
    have "pmf ?lhs (xs, ys) = 
            real (card (permutations_of_set A \<inter> partition P -` {(xs, ys)})) / fact (card A)"
      using assms by (auto simp: pmf_map measure_pmf_of_set)
    also have "partition P -` {(xs, ys)} = shuffles xs ys" 
      using True by (intro inv_image_partition) (auto simp: permutations_of_set_def)
    also have "permutations_of_set A \<inter> shuffles xs ys = shuffles xs ys"
      using True distinct_disjoint_shuffles[of xs ys] 
      by (auto simp: permutations_of_set_def dest: set_shuffles)
    also have "card (shuffles xs ys) = length xs + length ys choose length xs"
      using True by (intro card_disjoint_shuffles) (auto simp: permutations_of_set_def)
    also have "length xs + length ys = card A" by (simp add: card_eq)
    also have "real (card A choose length xs) = fact (card A) / (fact ?n1 * fact (card A - ?n1))"
      by (subst binomial_fact) (auto intro!: card_mono assms)
    also have "\<dots> / fact (card A) = 1 / (fact ?n1 * fact ?n2)"
      by (simp add: field_split_simps card_eq)
    also have "\<dots> = pmf ?rhs (xs, ys)" using True assms by (simp add: pmf_pair)
    finally show ?thesis .
  next
    case False
    hence *: "xs \<notin> permutations_of_set {x\<in>A. P x} \<or> ys \<notin> permutations_of_set {x\<in>A. \<not>P x}" by blast
    hence eq: "permutations_of_set A \<inter> (partition P -` {(xs, ys)}) = {}"
      by (auto simp: o_def permutations_of_set_def)
    from * show ?thesis
      by (elim disjE) (insert assms eq, simp_all add: pmf_pair pmf_map measure_pmf_of_set)
  qed
qed

end
