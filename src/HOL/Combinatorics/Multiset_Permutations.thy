(*  Author:     Manuel Eberl (TU München)

Defines the set of permutations of a given multiset (or set), i.e. the set of all lists whose 
entries correspond to the multiset (resp. set).
*)

section \<open>Permutations of a Multiset\<close>

theory Multiset_Permutations
imports
  Complex_Main
  Permutations
begin

(* TODO Move *)
lemma mset_tl: "xs \<noteq> [] \<Longrightarrow> mset (tl xs) = mset xs - {#hd xs#}"
  by (cases xs) simp_all

lemma mset_set_image_inj:
  assumes "inj_on f A"
  shows   "mset_set (f ` A) = image_mset f (mset_set A)"
proof (cases "finite A")
  case True
  from this and assms show ?thesis by (induction A) auto
qed (insert assms, simp add: finite_image_iff)

lemma multiset_remove_induct [case_names empty remove]:
  assumes "P {#}" "\<And>A. A \<noteq> {#} \<Longrightarrow> (\<And>x. x \<in># A \<Longrightarrow> P (A - {#x#})) \<Longrightarrow> P A"
  shows   "P A"
proof (induction A rule: full_multiset_induct)
  case (less A)
  hence IH: "P B" if "B \<subset># A" for B using that by blast
  show ?case
  proof (cases "A = {#}")
    case True
    thus ?thesis by (simp add: assms)
  next
    case False
    hence "P (A - {#x#})" if "x \<in># A" for x
      using that by (intro IH) (simp add: mset_subset_diff_self)
    from False and this show "P A" by (rule assms)
  qed
qed

lemma map_list_bind: "map g (List.bind xs f) = List.bind xs (map g \<circ> f)"
  by (simp add: List.bind_def map_concat)

lemma mset_eq_mset_set_imp_distinct:
  "finite A \<Longrightarrow> mset_set A = mset xs \<Longrightarrow> distinct xs"
proof (induction xs arbitrary: A)
  case (Cons x xs A)
  from Cons.prems(2) have "x \<in># mset_set A" by simp
  with Cons.prems(1) have [simp]: "x \<in> A" by simp
  from Cons.prems have "x \<notin># mset_set (A - {x})" by simp
  also from Cons.prems have "mset_set (A - {x}) = mset_set A - {#x#}"
    by (subst mset_set_Diff) simp_all
  also have "mset_set A = mset (x#xs)" by (simp add: Cons.prems)
  also have "\<dots> - {#x#} = mset xs" by simp
  finally have [simp]: "x \<notin> set xs" by (simp add: in_multiset_in_set)
  from Cons.prems show ?case by (auto intro!: Cons.IH[of "A - {x}"] simp: mset_set_Diff)
qed simp_all
(* END TODO *)


subsection \<open>Permutations of a multiset\<close>

definition permutations_of_multiset :: "'a multiset \<Rightarrow> 'a list set" where
  "permutations_of_multiset A = {xs. mset xs = A}"

lemma permutations_of_multisetI: "mset xs = A \<Longrightarrow> xs \<in> permutations_of_multiset A"
  by (simp add: permutations_of_multiset_def)

lemma permutations_of_multisetD: "xs \<in> permutations_of_multiset A \<Longrightarrow> mset xs = A"
  by (simp add: permutations_of_multiset_def)

lemma permutations_of_multiset_Cons_iff:
  "x # xs \<in> permutations_of_multiset A \<longleftrightarrow> x \<in># A \<and> xs \<in> permutations_of_multiset (A - {#x#})"
  by (auto simp: permutations_of_multiset_def)

lemma permutations_of_multiset_empty [simp]: "permutations_of_multiset {#} = {[]}"
  unfolding permutations_of_multiset_def by simp

lemma permutations_of_multiset_nonempty: 
  assumes nonempty: "A \<noteq> {#}"
  shows   "permutations_of_multiset A = 
             (\<Union>x\<in>set_mset A. ((#) x) ` permutations_of_multiset (A - {#x#}))" (is "_ = ?rhs")
proof safe
  fix xs assume "xs \<in> permutations_of_multiset A"
  hence mset_xs: "mset xs = A" by (simp add: permutations_of_multiset_def)
  hence "xs \<noteq> []" by (auto simp: nonempty)
  then obtain x xs' where xs: "xs = x # xs'" by (cases xs) simp_all
  with mset_xs have "x \<in> set_mset A" "xs' \<in> permutations_of_multiset (A - {#x#})"
    by (auto simp: permutations_of_multiset_def)
  with xs show "xs \<in> ?rhs" by auto
qed (auto simp: permutations_of_multiset_def)

lemma permutations_of_multiset_singleton [simp]: "permutations_of_multiset {#x#} = {[x]}"
  by (simp add: permutations_of_multiset_nonempty)

lemma permutations_of_multiset_doubleton: 
  "permutations_of_multiset {#x,y#} = {[x,y], [y,x]}"
  by (simp add: permutations_of_multiset_nonempty insert_commute)

lemma rev_permutations_of_multiset [simp]:
  "rev ` permutations_of_multiset A = permutations_of_multiset A"
proof
  have "rev ` rev ` permutations_of_multiset A \<subseteq> rev ` permutations_of_multiset A"
    unfolding permutations_of_multiset_def by auto
  also have "rev ` rev ` permutations_of_multiset A = permutations_of_multiset A"
    by (simp add: image_image)
  finally show "permutations_of_multiset A \<subseteq> rev ` permutations_of_multiset A" .
next
  show "rev ` permutations_of_multiset A \<subseteq> permutations_of_multiset A"
    unfolding permutations_of_multiset_def by auto
qed

lemma length_finite_permutations_of_multiset:
  "xs \<in> permutations_of_multiset A \<Longrightarrow> length xs = size A"
  by (auto simp: permutations_of_multiset_def)

lemma permutations_of_multiset_lists: "permutations_of_multiset A \<subseteq> lists (set_mset A)"
  by (auto simp: permutations_of_multiset_def)

lemma finite_permutations_of_multiset [simp]: "finite (permutations_of_multiset A)"
proof (rule finite_subset)
  show "permutations_of_multiset A \<subseteq> {xs. set xs \<subseteq> set_mset A \<and> length xs = size A}" 
    by (auto simp: permutations_of_multiset_def)
  show "finite {xs. set xs \<subseteq> set_mset A \<and> length xs = size A}" 
    by (rule finite_lists_length_eq) simp_all
qed

lemma permutations_of_multiset_not_empty [simp]: "permutations_of_multiset A \<noteq> {}"
proof -
  from ex_mset[of A] obtain xs where "mset xs = A" ..
  thus ?thesis by (auto simp: permutations_of_multiset_def)
qed

lemma permutations_of_multiset_image:
  "permutations_of_multiset (image_mset f A) = map f ` permutations_of_multiset A"
proof safe
  fix xs assume A: "xs \<in> permutations_of_multiset (image_mset f A)"
  from ex_mset[of A] obtain ys where ys: "mset ys = A" ..
  with A have "mset xs = mset (map f ys)" 
    by (simp add: permutations_of_multiset_def)
  then obtain \<sigma> where \<sigma>: "\<sigma> permutes {..<length (map f ys)}" "permute_list \<sigma> (map f ys) = xs"
    by (rule mset_eq_permutation)
  with ys have "xs = map f (permute_list \<sigma> ys)"
    by (simp add: permute_list_map)
  moreover from \<sigma> ys have "permute_list \<sigma> ys \<in> permutations_of_multiset A"
    by (simp add: permutations_of_multiset_def)
  ultimately show "xs \<in> map f ` permutations_of_multiset A" by blast
qed (auto simp: permutations_of_multiset_def)


subsection \<open>Cardinality of permutations\<close>

text \<open>
  In this section, we prove some basic facts about the number of permutations of a multiset.
\<close>

context
begin

private lemma multiset_prod_fact_insert:
  "(\<Prod>y\<in>set_mset (A+{#x#}). fact (count (A+{#x#}) y)) =
     (count A x + 1) * (\<Prod>y\<in>set_mset A. fact (count A y))"
proof -
  have "(\<Prod>y\<in>set_mset (A+{#x#}). fact (count (A+{#x#}) y)) =
          (\<Prod>y\<in>set_mset (A+{#x#}). (if y = x then count A x + 1 else 1) * fact (count A y))"
    by (intro prod.cong) simp_all
  also have "\<dots> = (count A x + 1) * (\<Prod>y\<in>set_mset (A+{#x#}). fact (count A y))"
    by (simp add: prod.distrib)
  also have "(\<Prod>y\<in>set_mset (A+{#x#}). fact (count A y)) = (\<Prod>y\<in>set_mset A. fact (count A y))"
    by (intro prod.mono_neutral_right) (auto simp: not_in_iff)
  finally show ?thesis .
qed

private lemma multiset_prod_fact_remove:
  "x \<in># A \<Longrightarrow> (\<Prod>y\<in>set_mset A. fact (count A y)) =
                   count A x * (\<Prod>y\<in>set_mset (A-{#x#}). fact (count (A-{#x#}) y))"
  using multiset_prod_fact_insert[of "A - {#x#}" x] by simp

lemma card_permutations_of_multiset_aux:
  "card (permutations_of_multiset A) * (\<Prod>x\<in>set_mset A. fact (count A x)) = fact (size A)"
proof (induction A rule: multiset_remove_induct)
  case (remove A)
  have "card (permutations_of_multiset A) = 
          card (\<Union>x\<in>set_mset A. (#) x ` permutations_of_multiset (A - {#x#}))"
    by (simp add: permutations_of_multiset_nonempty remove.hyps)
  also have "\<dots> = (\<Sum>x\<in>set_mset A. card (permutations_of_multiset (A - {#x#})))"
    by (subst card_UN_disjoint) (auto simp: card_image)
  also have "\<dots> * (\<Prod>x\<in>set_mset A. fact (count A x)) = 
               (\<Sum>x\<in>set_mset A. card (permutations_of_multiset (A - {#x#})) * 
                 (\<Prod>y\<in>set_mset A. fact (count A y)))"
    by (subst sum_distrib_right) simp_all
  also have "\<dots> = (\<Sum>x\<in>set_mset A. count A x * fact (size A - 1))"
  proof (intro sum.cong refl)
    fix x assume x: "x \<in># A"
    have "card (permutations_of_multiset (A - {#x#})) * (\<Prod>y\<in>set_mset A. fact (count A y)) = 
            count A x * (card (permutations_of_multiset (A - {#x#})) * 
              (\<Prod>y\<in>set_mset (A - {#x#}). fact (count (A - {#x#}) y)))" (is "?lhs = _")
      by (subst multiset_prod_fact_remove[OF x]) simp_all
    also note remove.IH[OF x]
    also from x have "size (A - {#x#}) = size A - 1" by (simp add: size_Diff_submset)
    finally show "?lhs = count A x * fact (size A - 1)" .
  qed
  also have "(\<Sum>x\<in>set_mset A. count A x * fact (size A - 1)) =
                size A * fact (size A - 1)"
    by (simp add: sum_distrib_right size_multiset_overloaded_eq)
  also from remove.hyps have "\<dots> = fact (size A)"
    by (cases "size A") auto
  finally show ?case .
qed simp_all

theorem card_permutations_of_multiset:
  "card (permutations_of_multiset A) = fact (size A) div (\<Prod>x\<in>set_mset A. fact (count A x))"
  "(\<Prod>x\<in>set_mset A. fact (count A x) :: nat) dvd fact (size A)"
  by (simp_all flip: card_permutations_of_multiset_aux[of A])

lemma card_permutations_of_multiset_insert_aux:
  "card (permutations_of_multiset (A + {#x#})) * (count A x + 1) = 
      (size A + 1) * card (permutations_of_multiset A)"
proof -
  note card_permutations_of_multiset_aux[of "A + {#x#}"]
  also have "fact (size (A + {#x#})) = (size A + 1) * fact (size A)" by simp
  also note multiset_prod_fact_insert[of A x]
  also note card_permutations_of_multiset_aux[of A, symmetric]
  finally have "card (permutations_of_multiset (A + {#x#})) * (count A x + 1) *
                    (\<Prod>y\<in>set_mset A. fact (count A y)) =
                (size A + 1) * card (permutations_of_multiset A) *
                    (\<Prod>x\<in>set_mset A. fact (count A x))" by (simp only: mult_ac)
  thus ?thesis by (subst (asm) mult_right_cancel) simp_all
qed

lemma card_permutations_of_multiset_remove_aux:
  assumes "x \<in># A"
  shows   "card (permutations_of_multiset A) * count A x = 
             size A * card (permutations_of_multiset (A - {#x#}))"
proof -
  from assms have A: "A - {#x#} + {#x#} = A" by simp
  from assms have B: "size A = size (A - {#x#}) + 1" 
    by (subst A [symmetric], subst size_union) simp
  show ?thesis
    using card_permutations_of_multiset_insert_aux[of "A - {#x#}" x, unfolded A] assms
    by (simp add: B)
qed

lemma real_card_permutations_of_multiset_remove:
  assumes "x \<in># A"
  shows   "real (card (permutations_of_multiset (A - {#x#}))) = 
             real (card (permutations_of_multiset A) * count A x) / real (size A)"
  using assms by (subst card_permutations_of_multiset_remove_aux[OF assms]) auto

lemma real_card_permutations_of_multiset_remove':
  assumes "x \<in># A"
  shows   "real (card (permutations_of_multiset A)) = 
             real (size A * card (permutations_of_multiset (A - {#x#}))) / real (count A x)"
  using assms by (subst card_permutations_of_multiset_remove_aux[OF assms, symmetric]) simp

end



subsection \<open>Permutations of a set\<close>

definition permutations_of_set :: "'a set \<Rightarrow> 'a list set" where
  "permutations_of_set A = {xs. set xs = A \<and> distinct xs}"

lemma permutations_of_set_altdef:
  "finite A \<Longrightarrow> permutations_of_set A = permutations_of_multiset (mset_set A)"
  by (auto simp add: permutations_of_set_def permutations_of_multiset_def mset_set_set 
        in_multiset_in_set [symmetric] mset_eq_mset_set_imp_distinct)

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

lemma permutations_of_set_infinite:
  "\<not>finite A \<Longrightarrow> permutations_of_set A = {}"
  by (auto simp: permutations_of_set_def)

lemma permutations_of_set_nonempty:
  "A \<noteq> {} \<Longrightarrow> permutations_of_set A = 
                  (\<Union>x\<in>A. (\<lambda>xs. x # xs) ` permutations_of_set (A - {x}))"
  by (cases "finite A")
     (simp_all add: permutations_of_multiset_nonempty mset_set_empty_iff mset_set_Diff 
                    permutations_of_set_altdef permutations_of_set_infinite)
    
lemma permutations_of_set_singleton [simp]: "permutations_of_set {x} = {[x]}"
  by (subst permutations_of_set_nonempty) auto

lemma permutations_of_set_doubleton: 
  "x \<noteq> y \<Longrightarrow> permutations_of_set {x,y} = {[x,y], [y,x]}"
  by (subst permutations_of_set_nonempty) 
     (simp_all add: insert_Diff_if insert_commute)

lemma rev_permutations_of_set [simp]:
  "rev ` permutations_of_set A = permutations_of_set A"
  by (cases "finite A") (simp_all add: permutations_of_set_altdef permutations_of_set_infinite)

lemma length_finite_permutations_of_set:
  "xs \<in> permutations_of_set A \<Longrightarrow> length xs = card A"
  by (auto simp: permutations_of_set_def distinct_card)

lemma finite_permutations_of_set [simp]: "finite (permutations_of_set A)"
  by (cases "finite A") (simp_all add: permutations_of_set_infinite permutations_of_set_altdef)

lemma permutations_of_set_empty_iff [simp]:
  "permutations_of_set A = {} \<longleftrightarrow> \<not>finite A"
  unfolding permutations_of_set_def using finite_distinct_list[of A] by auto

lemma card_permutations_of_set [simp]:
  "finite A \<Longrightarrow> card (permutations_of_set A) = fact (card A)"
  by (simp add: permutations_of_set_altdef card_permutations_of_multiset del: One_nat_def)

lemma permutations_of_set_image_inj:
  assumes inj: "inj_on f A"
  shows   "permutations_of_set (f ` A) = map f ` permutations_of_set A"
  by (cases "finite A")
     (simp_all add: permutations_of_set_infinite permutations_of_set_altdef
                    permutations_of_multiset_image mset_set_image_inj inj finite_image_iff)

lemma permutations_of_set_image_permutes:
  "\<sigma> permutes A \<Longrightarrow> map \<sigma> ` permutations_of_set A = permutations_of_set A"
  by (subst permutations_of_set_image_inj [symmetric])
     (simp_all add: permutes_inj_on permutes_image)


subsection \<open>Code generation\<close>

text \<open>
  First, we give code an implementation for permutations of lists.
\<close>

declare length_remove1 [termination_simp] 

fun permutations_of_list_impl where
  "permutations_of_list_impl xs = (if xs = [] then [[]] else
     List.bind (remdups xs) (\<lambda>x. map ((#) x) (permutations_of_list_impl (remove1 x xs))))"

fun permutations_of_list_impl_aux where
  "permutations_of_list_impl_aux acc xs = (if xs = [] then [acc] else
     List.bind (remdups xs) (\<lambda>x. permutations_of_list_impl_aux (x#acc) (remove1 x xs)))"

declare permutations_of_list_impl_aux.simps [simp del]    
declare permutations_of_list_impl.simps [simp del]
    
lemma permutations_of_list_impl_Nil [simp]:
  "permutations_of_list_impl [] = [[]]"
  by (simp add: permutations_of_list_impl.simps)

lemma permutations_of_list_impl_nonempty:
  "xs \<noteq> [] \<Longrightarrow> permutations_of_list_impl xs = 
     List.bind (remdups xs) (\<lambda>x. map ((#) x) (permutations_of_list_impl (remove1 x xs)))"
  by (subst permutations_of_list_impl.simps) simp_all

lemma set_permutations_of_list_impl:
  "set (permutations_of_list_impl xs) = permutations_of_multiset (mset xs)"
  by (induction xs rule: permutations_of_list_impl.induct)
     (subst permutations_of_list_impl.simps, 
      simp_all add: permutations_of_multiset_nonempty set_list_bind)

lemma distinct_permutations_of_list_impl:
  "distinct (permutations_of_list_impl xs)"
  by (induction xs rule: permutations_of_list_impl.induct, 
      subst permutations_of_list_impl.simps)
     (auto intro!: distinct_list_bind simp: distinct_map o_def disjoint_family_on_def)

lemma permutations_of_list_impl_aux_correct':
  "permutations_of_list_impl_aux acc xs = 
     map (\<lambda>xs. rev xs @ acc) (permutations_of_list_impl xs)"
  by (induction acc xs rule: permutations_of_list_impl_aux.induct,
      subst permutations_of_list_impl_aux.simps, subst permutations_of_list_impl.simps)
     (auto simp: map_list_bind intro!: list_bind_cong)
    
lemma permutations_of_list_impl_aux_correct:
  "permutations_of_list_impl_aux [] xs = map rev (permutations_of_list_impl xs)"
  by (simp add: permutations_of_list_impl_aux_correct')

lemma distinct_permutations_of_list_impl_aux:
  "distinct (permutations_of_list_impl_aux acc xs)"
  by (simp add: permutations_of_list_impl_aux_correct' distinct_map 
        distinct_permutations_of_list_impl inj_on_def)

lemma set_permutations_of_list_impl_aux:
  "set (permutations_of_list_impl_aux [] xs) = permutations_of_multiset (mset xs)"
  by (simp add: permutations_of_list_impl_aux_correct set_permutations_of_list_impl)
  
declare set_permutations_of_list_impl_aux [symmetric, code]

value [code] "permutations_of_multiset {#1,2,3,4::int#}"



text \<open>
  Now we turn to permutations of sets. We define an auxiliary version with an 
  accumulator to avoid having to map over the results.
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
        apply (rule arg_cong [of _ _ Union], rule image_cong)
         apply (simp_all add: image_image)
        apply (subst psubset)
         apply auto
        done
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
      simp_all add: set_list_bind)


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
