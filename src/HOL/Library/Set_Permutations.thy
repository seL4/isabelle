(*  
  Title:    Set_Permutations.thy
  Author:   Manuel Eberl, TU München

  The set of permutations of a finite set, i.e. the set of all 
  lists that contain every element of the set once.
*)

section \<open>Set Permutations\<close>

theory Set_Permutations
imports 
  Complex_Main
  "~~/src/HOL/Library/Disjoint_Sets"
  "~~/src/HOL/Library/Permutations"
begin

subsection \<open>Definition and general facts\<close>

definition permutations_of_set :: "'a set \<Rightarrow> 'a list set" where
  "permutations_of_set A = {xs. set xs = A \<and> distinct xs}"

lemma permutations_of_setI [intro]:
  assumes "set xs = A" "distinct xs"
  shows   "xs \<in> permutations_of_set A"
  using assms unfolding permutations_of_set_def by simp
  
lemma permutations_of_setD:
  assumes "xs \<in> permutations_of_set A"
  shows   "set xs = A" "distinct xs"
  using assms unfolding permutations_of_set_def by simp_all
  
lemma permutations_of_set_lists: "permutations_of_set A \<subseteq> lists A"
  unfolding permutations_of_set_def by auto

lemma permutations_of_set_empty [simp]: "permutations_of_set {} = {[]}"
  by (auto simp: permutations_of_set_def)
  
lemma UN_set_permutations_of_set [simp]:
  "finite A \<Longrightarrow> (\<Union>xs\<in>permutations_of_set A. set xs) = A"
  using finite_distinct_list by (auto simp: permutations_of_set_def)

lemma permutations_of_set_nonempty:
  assumes "A \<noteq> {}"
  shows "permutations_of_set A = 
           (\<Union>x\<in>A. (\<lambda>xs. x # xs) ` permutations_of_set (A - {x}))" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix ys assume ys: "ys \<in> permutations_of_set A"
  with assms have "ys \<noteq> []" by (auto simp: permutations_of_set_def)
  then obtain x xs where xs: "ys = x # xs" by (cases ys) simp_all
  from xs ys have "x \<in> A" "xs \<in> permutations_of_set (A - {x})"
    by (auto simp: permutations_of_set_def)
  with xs show "ys \<in> ?rhs" by auto
next
  fix ys assume ys: "ys \<in> ?rhs"
  then obtain x xs where xs: "ys = x # xs" "x \<in> A" "xs \<in> permutations_of_set (A - {x})"
    by auto
  with ys show "ys \<in> ?lhs" by (auto simp: permutations_of_set_def)
qed

lemma permutations_of_set_singleton [simp]: "permutations_of_set {x} = {[x]}"
  by (subst permutations_of_set_nonempty) auto

lemma permutations_of_set_doubleton: 
  "x \<noteq> y \<Longrightarrow> permutations_of_set {x,y} = {[x,y], [y,x]}"
  by (subst permutations_of_set_nonempty) 
     (simp_all add: insert_Diff_if insert_commute)

lemma rev_permutations_of_set [simp]:
  "rev ` permutations_of_set A = permutations_of_set A"
proof
  have "rev ` rev ` permutations_of_set A \<subseteq> rev ` permutations_of_set A"
    unfolding permutations_of_set_def by auto
  also have "rev ` rev ` permutations_of_set A = permutations_of_set A"
    by (simp add: image_image)
  finally show "permutations_of_set A \<subseteq> rev ` permutations_of_set A" .
next
  show "rev ` permutations_of_set A \<subseteq> permutations_of_set A"
    unfolding permutations_of_set_def by auto
qed

lemma length_finite_permutations_of_set:
  "xs \<in> permutations_of_set A \<Longrightarrow> length xs = card A"
  by (auto simp: permutations_of_set_def distinct_card)

lemma permutations_of_set_infinite:
  "\<not>finite A \<Longrightarrow> permutations_of_set A = {}"
  by (auto simp: permutations_of_set_def)

lemma finite_permutations_of_set [simp]: "finite (permutations_of_set A)"
proof (cases "finite A")
  assume fin: "finite A"
  have "permutations_of_set A \<subseteq> {xs. set xs \<subseteq> A \<and> length xs = card A}"
    unfolding permutations_of_set_def by (auto simp: distinct_card)
  moreover from fin have "finite \<dots>" using finite_lists_length_eq by blast
  ultimately show ?thesis by (rule finite_subset)
qed (simp_all add: permutations_of_set_infinite)

lemma permutations_of_set_empty_iff [simp]:
  "permutations_of_set A = {} \<longleftrightarrow> \<not>finite A"
  unfolding permutations_of_set_def using finite_distinct_list[of A] by auto

lemma card_permutations_of_set [simp]:
  "finite A \<Longrightarrow> card (permutations_of_set A) = fact (card A)"
proof (induction A rule: finite_remove_induct)
  case (remove A)
  hence "card (permutations_of_set A) = 
           card (\<Union>x\<in>A. op # x ` permutations_of_set (A - {x}))"
    by (simp add: permutations_of_set_nonempty)
  also from remove.hyps have "\<dots> = (\<Sum>i\<in>A. card (op # i ` permutations_of_set (A - {i})))"
    by (intro card_UN_disjoint) auto
  also have "\<dots> = (\<Sum>i\<in>A. card (permutations_of_set (A - {i})))"
    by (intro setsum.cong) (simp_all add: card_image)
  also from remove have "\<dots> = card A * fact (card A - 1)" by simp
  also from remove.hyps have "\<dots> = fact (card A)"
    by (cases "card A") simp_all
  finally show ?case .
qed simp_all

lemma permutations_of_set_image_inj:
  assumes inj: "inj_on f A"
  shows   "permutations_of_set (f ` A) = map f ` permutations_of_set A"
proof (cases "finite A")
  assume "\<not>finite A"
  with inj show ?thesis
    by (auto simp add: permutations_of_set_infinite dest: finite_imageD)
next
  assume finite: "finite A"
  show ?thesis
  proof (rule sym, rule card_seteq)
    from inj show "map f ` permutations_of_set A \<subseteq> permutations_of_set (f ` A)" 
      by (auto simp: permutations_of_set_def distinct_map)
  
    from inj have "card (map f ` permutations_of_set A) = card (permutations_of_set A)"
      by (intro card_image inj_on_mapI) (auto simp: permutations_of_set_def)
    also from finite inj have "\<dots> = card (permutations_of_set (f ` A))" 
      by (simp add: card_image)
    finally show "card (permutations_of_set (f ` A)) \<le>
                    card (map f ` permutations_of_set A)" by simp
  qed simp_all
qed

lemma permutations_of_set_image_permutes:
  "\<sigma> permutes A \<Longrightarrow> map \<sigma> ` permutations_of_set A = permutations_of_set A"
  by (subst permutations_of_set_image_inj [symmetric])
     (simp_all add: permutes_inj_on permutes_image)


subsection \<open>Code generation\<close>

text \<open>
  We define an auxiliary version with an accumulator to avoid
  having to map over the results.
\<close>
function permutations_of_set_aux where
  "permutations_of_set_aux acc A = 
     (if \<not>finite A then {} else if A = {} then {acc} else 
        (\<Union>x\<in>A. permutations_of_set_aux (x#acc) (A - {x})))"
by auto
termination by (relation "Wellfounded.measure (card \<circ> snd)") (simp_all add: card_gt_0_iff)

lemma permutations_of_set_aux_altdef:
  "permutations_of_set_aux acc A = (\<lambda>xs. rev xs @ acc) ` permutations_of_set A"
proof (cases "finite A")
  assume "finite A"
  thus ?thesis
  proof (induction A arbitrary: acc rule: finite_psubset_induct)
    case (psubset A acc)
    show ?case
    proof (cases "A = {}")
      case False
      note [simp del] = permutations_of_set_aux.simps
      from psubset.hyps False 
        have "permutations_of_set_aux acc A = 
                (\<Union>y\<in>A. permutations_of_set_aux (y#acc) (A - {y}))"
        by (subst permutations_of_set_aux.simps) simp_all
      also have "\<dots> = (\<Union>y\<in>A. (\<lambda>xs. rev xs @ acc) ` (\<lambda>xs. y # xs) ` permutations_of_set (A - {y}))"
        by (intro SUP_cong refl, subst psubset) (auto simp: image_image)
      also from False have "\<dots> = (\<lambda>xs. rev xs @ acc) ` permutations_of_set A"
        by (subst (2) permutations_of_set_nonempty) (simp_all add: image_UN)
      finally show ?thesis .
    qed simp_all
  qed
qed (simp_all add: permutations_of_set_infinite)

declare permutations_of_set_aux.simps [simp del]

lemma permutations_of_set_aux_correct:
  "permutations_of_set_aux [] A = permutations_of_set A"
  by (simp add: permutations_of_set_aux_altdef)


text \<open>
  In another refinement step, we define a version on lists.
\<close>
declare length_remove1 [termination_simp]

fun permutations_of_set_aux_list where
  "permutations_of_set_aux_list acc xs = 
     (if xs = [] then [acc] else 
        List.bind xs (\<lambda>x. permutations_of_set_aux_list (x#acc) (List.remove1 x xs)))"

definition permutations_of_set_list where
  "permutations_of_set_list xs = permutations_of_set_aux_list [] xs"

declare permutations_of_set_aux_list.simps [simp del]

lemma permutations_of_set_aux_list_refine:
  assumes "distinct xs"
  shows   "set (permutations_of_set_aux_list acc xs) = permutations_of_set_aux acc (set xs)"
  using assms
  by (induction acc xs rule: permutations_of_set_aux_list.induct)
     (subst permutations_of_set_aux_list.simps,
      subst permutations_of_set_aux.simps,
      simp_all add: set_list_bind cong: SUP_cong)


text \<open>
  The permutation lists contain no duplicates if the inputs contain no duplicates.
  Therefore, these functions can easily be used when working with a representation of
  sets by distinct lists.
  The same approach should generalise to any kind of set implementation that supports
  a monadic bind operation, and since the results are disjoint, merging should be cheap.
\<close>
lemma distinct_permutations_of_set_aux_list:
  "distinct xs \<Longrightarrow> distinct (permutations_of_set_aux_list acc xs)"
  by (induction acc xs rule: permutations_of_set_aux_list.induct)
     (subst permutations_of_set_aux_list.simps,
      auto intro!: distinct_list_bind simp: disjoint_family_on_def 
         permutations_of_set_aux_list_refine permutations_of_set_aux_altdef)

lemma distinct_permutations_of_set_list:
    "distinct xs \<Longrightarrow> distinct (permutations_of_set_list xs)"
  by (simp add: permutations_of_set_list_def distinct_permutations_of_set_aux_list)

lemma permutations_of_list:
    "permutations_of_set (set xs) = set (permutations_of_set_list (remdups xs))"
  by (simp add: permutations_of_set_aux_correct [symmetric] 
        permutations_of_set_aux_list_refine permutations_of_set_list_def)

lemma permutations_of_list_code [code]:
  "permutations_of_set (set xs) = set (permutations_of_set_list (remdups xs))"
  "permutations_of_set (List.coset xs) = 
     Code.abort (STR ''Permutation of set complement not supported'') 
       (\<lambda>_. permutations_of_set (List.coset xs))"
  by (simp_all add: permutations_of_list)

value [code] "permutations_of_set (set ''abcd'')"

end