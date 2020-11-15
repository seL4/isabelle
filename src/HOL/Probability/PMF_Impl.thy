(*  Title:      HOL/Probability/PMF_Impl.thy
    Author:     Manuel Eberl, TU München
    
    An implementation of PMFs using Mappings, which are implemented with association lists
    by default. Also includes Quickcheck setup for PMFs.
*)

section \<open>Code generation for PMFs\<close>

theory PMF_Impl
imports Probability_Mass_Function "HOL-Library.AList_Mapping"
begin

subsection \<open>General code generation setup\<close>

definition pmf_of_mapping :: "('a, real) mapping \<Rightarrow> 'a pmf" where
  "pmf_of_mapping m = embed_pmf (Mapping.lookup_default 0 m)" 

lemma nn_integral_lookup_default:
  fixes m :: "('a, real) mapping"
  assumes "finite (Mapping.keys m)" "All_mapping m (\<lambda>_ x. x \<ge> 0)"
  shows   "nn_integral (count_space UNIV) (\<lambda>k. ennreal (Mapping.lookup_default 0 m k)) = 
             ennreal (\<Sum>k\<in>Mapping.keys m. Mapping.lookup_default 0 m k)"
proof -
  have "nn_integral (count_space UNIV) (\<lambda>k. ennreal (Mapping.lookup_default 0 m k)) = 
          (\<Sum>x\<in>Mapping.keys m. ennreal (Mapping.lookup_default 0 m x))" using assms
    by (subst nn_integral_count_space'[of "Mapping.keys m"])
       (auto simp: Mapping.lookup_default_def keys_is_none_rep Option.is_none_def)
  also from assms have "\<dots> = ennreal (\<Sum>k\<in>Mapping.keys m. Mapping.lookup_default 0 m k)"
    by (intro sum_ennreal) 
       (auto simp: Mapping.lookup_default_def All_mapping_def split: option.splits)
  finally show ?thesis .
qed

lemma pmf_of_mapping: 
  assumes "finite (Mapping.keys m)" "All_mapping m (\<lambda>_ p. p \<ge> 0)"
  assumes "(\<Sum>x\<in>Mapping.keys m. Mapping.lookup_default 0 m x) = 1"
  shows   "pmf (pmf_of_mapping m) x = Mapping.lookup_default 0 m x"
  unfolding pmf_of_mapping_def
proof (intro pmf_embed_pmf)
  from assms show "(\<integral>\<^sup>+x. ennreal (Mapping.lookup_default 0 m x) \<partial>count_space UNIV) = 1"
    by (subst nn_integral_lookup_default) (simp_all)
qed (insert assms, simp add: All_mapping_def Mapping.lookup_default_def split: option.splits)

lemma pmf_of_set_pmf_of_mapping:
  assumes "A \<noteq> {}" "set xs = A" "distinct xs"
  shows   "pmf_of_set A = pmf_of_mapping (Mapping.tabulate xs (\<lambda>_. 1 / real (length xs)))" 
           (is "?lhs = ?rhs")
  by (rule pmf_eqI, subst pmf_of_mapping)
     (insert assms, auto intro!: All_mapping_tabulate 
                         simp: Mapping.lookup_default_def lookup_tabulate distinct_card)

lift_definition mapping_of_pmf :: "'a pmf \<Rightarrow> ('a, real) mapping" is
  "\<lambda>p x. if pmf p x = 0 then None else Some (pmf p x)" .
  
lemma lookup_default_mapping_of_pmf: 
  "Mapping.lookup_default 0 (mapping_of_pmf p) x = pmf p x"
  by (simp add: mapping_of_pmf.abs_eq lookup_default_def Mapping.lookup.abs_eq)

context
begin

interpretation pmf_as_function .

lemma nn_integral_pmf_eq_1: "(\<integral>\<^sup>+ x. ennreal (pmf p x) \<partial>count_space UNIV) = 1"
  by transfer simp_all
end
  
lemma pmf_of_mapping_mapping_of_pmf [code abstype]: 
    "pmf_of_mapping (mapping_of_pmf p) = p"
  unfolding pmf_of_mapping_def
  by (rule pmf_eqI, subst pmf_embed_pmf)
     (insert nn_integral_pmf_eq_1[of p], 
      auto simp: lookup_default_mapping_of_pmf split: option.splits)

lemma mapping_of_pmfI:
  assumes "\<And>x. x \<in> Mapping.keys m \<Longrightarrow> Mapping.lookup m x = Some (pmf p x)" 
  assumes "Mapping.keys m = set_pmf p"
  shows   "mapping_of_pmf p = m"
  using assms by transfer (rule ext, auto simp: set_pmf_eq)
  
lemma mapping_of_pmfI':
  assumes "\<And>x. x \<in> Mapping.keys m \<Longrightarrow> Mapping.lookup_default 0 m x = pmf p x" 
  assumes "Mapping.keys m = set_pmf p"
  shows   "mapping_of_pmf p = m"
  using assms unfolding Mapping.lookup_default_def 
  by transfer (rule ext, force simp: set_pmf_eq)

lemma return_pmf_code [code abstract]:
  "mapping_of_pmf (return_pmf x) = Mapping.update x 1 Mapping.empty"
  by (intro mapping_of_pmfI) (auto simp: lookup_update')

lemma pmf_of_set_code_aux:
  assumes "A \<noteq> {}" "set xs = A" "distinct xs"
  shows   "mapping_of_pmf (pmf_of_set A) = Mapping.tabulate xs (\<lambda>_. 1 / real (length xs))"
  using assms
  by (intro mapping_of_pmfI, subst pmf_of_set)
     (auto simp: lookup_tabulate distinct_card)

definition pmf_of_set_impl where
  "pmf_of_set_impl A = mapping_of_pmf (pmf_of_set A)"

(* This equation can be used to easily implement pmf_of_set for other set implementations *)
lemma pmf_of_set_impl_code_alt:
  assumes "A \<noteq> {}" "finite A"
  shows   "pmf_of_set_impl A = 
             (let p = 1 / real (card A) 
              in  Finite_Set.fold (\<lambda>x. Mapping.update x p) Mapping.empty A)"
proof -
  define p where "p = 1 / real (card A)"
  let ?m = "Finite_Set.fold (\<lambda>x. Mapping.update x p) Mapping.empty A"
  interpret comp_fun_idem "\<lambda>x. Mapping.update x p"
    by standard (transfer, force simp: fun_eq_iff)+
  have keys: "Mapping.keys ?m = A"
    using assms(2) by (induction A rule: finite_induct) simp_all
  have lookup: "Mapping.lookup ?m x = Some p" if "x \<in> A" for x
    using assms(2) that by (induction A rule: finite_induct) (auto simp: lookup_update')
  from keys lookup assms show ?thesis unfolding pmf_of_set_impl_def
    by (intro mapping_of_pmfI) (simp_all add: Let_def p_def)
qed

lemma pmf_of_set_impl_code [code]:
  "pmf_of_set_impl (set xs) = 
    (if xs = [] then
         Code.abort (STR ''pmf_of_set of empty set'') (\<lambda>_. mapping_of_pmf (pmf_of_set (set xs)))
      else let xs' = remdups xs; p = 1 / real (length xs') in
         Mapping.tabulate xs' (\<lambda>_. p))"
  unfolding pmf_of_set_impl_def
  using pmf_of_set_code_aux[of "set xs" "remdups xs"] by (simp add: Let_def)

lemma pmf_of_set_code [code abstract]:
  "mapping_of_pmf (pmf_of_set A) = pmf_of_set_impl A"
  by (simp add: pmf_of_set_impl_def)


lemma pmf_of_multiset_pmf_of_mapping:
  assumes "A \<noteq> {#}" "set xs = set_mset A" "distinct xs"
  shows   "mapping_of_pmf (pmf_of_multiset A) = Mapping.tabulate xs (\<lambda>x. count A x / real (size A))" 
  using assms by (intro mapping_of_pmfI) (auto simp: lookup_tabulate)

definition pmf_of_multiset_impl where
  "pmf_of_multiset_impl A = mapping_of_pmf (pmf_of_multiset A)"  

lemma pmf_of_multiset_impl_code_alt:
  assumes "A \<noteq> {#}"
  shows   "pmf_of_multiset_impl A =
             (let p = 1 / real (size A)
              in  fold_mset (\<lambda>x. Mapping.map_default x 0 ((+) p)) Mapping.empty A)"
proof -
  define p where "p = 1 / real (size A)"
  interpret comp_fun_commute "\<lambda>x. Mapping.map_default x 0 ((+) p)"
    unfolding Mapping.map_default_def [abs_def]
    by (standard, intro mapping_eqI ext) 
       (simp_all add: o_def lookup_map_entry' lookup_default' lookup_default_def)
  let ?m = "fold_mset (\<lambda>x. Mapping.map_default x 0 ((+) p)) Mapping.empty A"
  have keys: "Mapping.keys ?m = set_mset A" by (induction A) simp_all
  have lookup: "Mapping.lookup_default 0 ?m x = real (count A x) * p" for x
    by (induction A)
       (simp_all add: lookup_map_default' lookup_default_def lookup_empty ring_distribs)
  from keys lookup assms show ?thesis unfolding pmf_of_multiset_impl_def
    by (intro mapping_of_pmfI') (simp_all add: Let_def p_def)
qed

lemma pmf_of_multiset_impl_code [code]:
  "pmf_of_multiset_impl (mset xs) =
     (if xs = [] then 
        Code.abort (STR ''pmf_of_multiset of empty multiset'') 
          (\<lambda>_. mapping_of_pmf (pmf_of_multiset (mset xs)))
      else let xs' = remdups xs; p = 1 / real (length xs) in
         Mapping.tabulate xs' (\<lambda>x. real (count (mset xs) x) * p))"
  using pmf_of_multiset_pmf_of_mapping[of "mset xs" "remdups xs"]
  by (simp add: pmf_of_multiset_impl_def)        

lemma pmf_of_multiset_code [code abstract]:
  "mapping_of_pmf (pmf_of_multiset A) = pmf_of_multiset_impl A"
  by (simp add: pmf_of_multiset_impl_def)

  
lemma bernoulli_pmf_code [code abstract]:
  "mapping_of_pmf (bernoulli_pmf p) = 
     (if p \<le> 0 then Mapping.update False 1 Mapping.empty 
      else if p \<ge> 1 then Mapping.update True 1 Mapping.empty
      else Mapping.update False (1 - p) (Mapping.update True p Mapping.empty))"
  by (intro mapping_of_pmfI) (auto simp: bernoulli_pmf.rep_eq lookup_update' set_pmf_eq)


lemma pmf_code [code]: "pmf p x = Mapping.lookup_default 0 (mapping_of_pmf p) x"
  unfolding mapping_of_pmf_def Mapping.lookup_default_def
  by (auto split: option.splits simp: id_def Mapping.lookup.abs_eq)

lemma set_pmf_code [code]: "set_pmf p = Mapping.keys (mapping_of_pmf p)"
  by transfer (auto simp: dom_def set_pmf_eq)

lemma keys_mapping_of_pmf [simp]: "Mapping.keys (mapping_of_pmf p) = set_pmf p"
  by transfer (auto simp: dom_def set_pmf_eq)
  


definition fold_combine_plus where
  "fold_combine_plus = comm_monoid_set.F (Mapping.combine ((+) :: real \<Rightarrow> _)) Mapping.empty"

context
begin

interpretation fold_combine_plus: combine_mapping_abel_semigroup "(+) :: real \<Rightarrow> _"
  by unfold_locales (simp_all add: add_ac)
  
qualified lemma lookup_default_fold_combine_plus: 
  fixes A :: "'b set" and f :: "'b \<Rightarrow> ('a, real) mapping"
  assumes "finite A"
  shows   "Mapping.lookup_default 0 (fold_combine_plus f A) x = 
             (\<Sum>y\<in>A. Mapping.lookup_default 0 (f y) x)"
  unfolding fold_combine_plus_def using assms 
    by (induction A rule: finite_induct) 
       (simp_all add: lookup_default_empty lookup_default_neutral_combine)

qualified lemma keys_fold_combine_plus: 
  "finite A \<Longrightarrow> Mapping.keys (fold_combine_plus f A) = (\<Union>x\<in>A. Mapping.keys (f x))"
  by (simp add: fold_combine_plus_def fold_combine_plus.keys_fold_combine)

qualified lemma fold_combine_plus_code [code]:
  "fold_combine_plus g (set xs) = foldr (\<lambda>x. Mapping.combine (+) (g x)) (remdups xs) Mapping.empty"
  by (simp add: fold_combine_plus_def fold_combine_plus.fold_combine_code)

private lemma lookup_default_0_map_values:
  assumes "f x 0 = 0"
  shows   "Mapping.lookup_default 0 (Mapping.map_values f m) x = f x (Mapping.lookup_default 0 m x)"
  unfolding Mapping.lookup_default_def
  using assms by transfer (auto split: option.splits)

qualified lemma mapping_of_bind_pmf:
  assumes "finite (set_pmf p)"
  shows   "mapping_of_pmf (bind_pmf p f) = 
             fold_combine_plus (\<lambda>x. Mapping.map_values (\<lambda>_. (*) (pmf p x)) 
               (mapping_of_pmf (f x))) (set_pmf p)"
  using assms
  by (intro mapping_of_pmfI')
     (auto simp: keys_fold_combine_plus lookup_default_fold_combine_plus 
                 pmf_bind integral_measure_pmf lookup_default_0_map_values 
                 lookup_default_mapping_of_pmf mult_ac)

lift_definition bind_pmf_aux :: "'a pmf \<Rightarrow> ('a \<Rightarrow> 'b pmf) \<Rightarrow> 'a set \<Rightarrow> ('b, real) mapping" is
  "\<lambda>(p :: 'a pmf) (f :: 'a \<Rightarrow> 'b pmf) (A::'a set) (x::'b). 
     if x \<in> (\<Union>y\<in>A. set_pmf (f y)) then 
       Some (measure_pmf.expectation p (\<lambda>y. indicator A y * pmf (f y) x)) 
     else None" .

lemma keys_bind_pmf_aux [simp]:
  "Mapping.keys (bind_pmf_aux p f A) = (\<Union>x\<in>A. set_pmf (f x))"
  by transfer (auto split: if_splits)

lemma lookup_default_bind_pmf_aux:
  "Mapping.lookup_default 0 (bind_pmf_aux p f A) x = 
     (if x \<in> (\<Union>y\<in>A. set_pmf (f y)) then 
        measure_pmf.expectation p (\<lambda>y. indicator A y * pmf (f y) x) else 0)"
  unfolding lookup_default_def by transfer' simp_all

lemma lookup_default_bind_pmf_aux' [simp]:
  "Mapping.lookup_default 0 (bind_pmf_aux p f (set_pmf p)) x = pmf (bind_pmf p f) x"
  unfolding lookup_default_def
  by transfer (auto simp: pmf_bind AE_measure_pmf_iff set_pmf_eq
                    intro!: integral_cong_AE integral_eq_zero_AE)
  
lemma bind_pmf_aux_correct:
  "mapping_of_pmf (bind_pmf p f) = bind_pmf_aux p f (set_pmf p)"
  by (intro mapping_of_pmfI') simp_all

lemma bind_pmf_aux_code_aux:
  assumes "finite A"
  shows   "bind_pmf_aux p f A = 
             fold_combine_plus (\<lambda>x. Mapping.map_values (\<lambda>_. (*) (pmf p x))
               (mapping_of_pmf (f x))) A" (is "?lhs = ?rhs")
proof (intro mapping_eqI'[where d = 0])
  fix x assume "x \<in> Mapping.keys ?lhs"
  then obtain y where y: "y \<in> A" "x \<in> set_pmf (f y)" by auto
  hence "Mapping.lookup_default 0 ?lhs x = 
           measure_pmf.expectation p (\<lambda>y. indicator A y * pmf (f y) x)"
    by (auto simp: lookup_default_bind_pmf_aux)
  also from assms have "\<dots> = (\<Sum>y\<in>A. pmf p y * pmf (f y) x)"
    by (subst integral_measure_pmf [of A])
       (auto simp: set_pmf_eq indicator_def mult_ac split: if_splits)
  also from assms have "\<dots> = Mapping.lookup_default 0 ?rhs x"
    by (simp add: lookup_default_fold_combine_plus lookup_default_0_map_values
          lookup_default_mapping_of_pmf)
  finally show "Mapping.lookup_default 0 ?lhs x = Mapping.lookup_default 0 ?rhs x" .
qed (insert assms, simp_all add: keys_fold_combine_plus)

lemma bind_pmf_aux_code [code]:
  "bind_pmf_aux p f (set xs) = 
     fold_combine_plus (\<lambda>x. Mapping.map_values (\<lambda>_. (*) (pmf p x))
               (mapping_of_pmf (f x))) (set xs)"
  by (rule bind_pmf_aux_code_aux) simp_all

lemmas bind_pmf_code [code abstract] = bind_pmf_aux_correct

end

hide_const (open) fold_combine_plus


lift_definition cond_pmf_impl :: "'a pmf \<Rightarrow> 'a set \<Rightarrow> ('a, real) mapping option" is
  "\<lambda>p A. if A \<inter> set_pmf p = {} then None else 
     Some (\<lambda>x. if x \<in> A \<inter> set_pmf p then Some (pmf p x / measure_pmf.prob p A) else None)" .

lemma cond_pmf_impl_code_alt:
  assumes "finite A"
  shows   "cond_pmf_impl p A = (
             let C = A \<inter> set_pmf p;
                 prob = (\<Sum>x\<in>C. pmf p x)
             in  if prob = 0 then 
                   None
                 else
                   Some (Mapping.map_values (\<lambda>_ y. y / prob) 
                     (Mapping.filter (\<lambda>k _. k \<in> C) (mapping_of_pmf p))))"
proof -
  define C where "C = A \<inter> set_pmf p"
  define prob where "prob = (\<Sum>x\<in>C. pmf p x)"
  also note C_def
  also from assms have "(\<Sum>x\<in>A \<inter> set_pmf p. pmf p x) = (\<Sum>x\<in>A. pmf p x)"
    by (intro sum.mono_neutral_left) (auto simp: set_pmf_eq)
  finally have prob1: "prob = (\<Sum>x\<in>A. pmf p x)" .
  hence prob2: "prob = measure_pmf.prob p A"
    using assms by (subst measure_measure_pmf_finite) simp_all
  have prob3: "prob = 0 \<longleftrightarrow> A \<inter> set_pmf p = {}"
    by (subst prob1, subst sum_nonneg_eq_0_iff) (auto simp: set_pmf_eq assms)
  from assms have prob4: "prob = measure_pmf.prob p C"
    unfolding prob_def by (intro measure_measure_pmf_finite [symmetric]) (simp_all add: C_def)
  
  show ?thesis
  proof (cases "prob = 0")
    case True
    hence "A \<inter> set_pmf p = {}" by (subst (asm) prob3)
    with True show ?thesis by (simp add: Let_def prob_def C_def cond_pmf_impl.abs_eq)
  next
    case False
    hence A: "C \<noteq> {}" unfolding C_def by (subst (asm) prob3) auto
    with prob3 have prob_nz: "prob \<noteq> 0" by (auto simp: C_def)
    fix x
    have "cond_pmf_impl p A = 
            Some (mapping.Mapping (\<lambda>x. if x \<in> C then 
              Some (pmf p x / measure_pmf.prob p C) else None))" 
         (is "_ = Some ?m")
      using A prob2 prob4 unfolding C_def by transfer (auto simp: fun_eq_iff)
    also have "?m = Mapping.map_values (\<lambda>_ y. y / prob) 
                 (Mapping.filter (\<lambda>k _. k \<in> C) (mapping_of_pmf p))"
      using prob_nz prob4 assms unfolding C_def
      by transfer (auto simp: fun_eq_iff set_pmf_eq)
    finally show ?thesis using False by (simp add: Let_def prob_def C_def)
  qed
qed

lemma cond_pmf_impl_code [code]:
  "cond_pmf_impl p (set xs) = (
     let C = set xs \<inter> set_pmf p;
         prob = (\<Sum>x\<in>C. pmf p x)
     in  if prob = 0 then 
           None
         else
           Some (Mapping.map_values (\<lambda>_ y. y / prob) 
             (Mapping.filter (\<lambda>k _. k \<in> C) (mapping_of_pmf p))))"
  by (rule cond_pmf_impl_code_alt) simp_all

lemma cond_pmf_code [code abstract]:
  "mapping_of_pmf (cond_pmf p A) = 
     (case cond_pmf_impl p A of
        None \<Rightarrow> Code.abort (STR ''cond_pmf with set of probability 0'')
                  (\<lambda>_. mapping_of_pmf (cond_pmf p A))
      | Some m \<Rightarrow> m)"
proof (cases "cond_pmf_impl p A")
  case (Some m)
  hence A: "set_pmf p \<inter> A \<noteq> {}" by transfer (auto split: if_splits)
  from Some have B: "Mapping.keys m = set_pmf (cond_pmf p A)"
    by (subst set_cond_pmf[OF A], transfer) (auto split: if_splits)
  with Some A have "mapping_of_pmf (cond_pmf p A) = m"
    by (intro mapping_of_pmfI[OF _ B], transfer) (auto split: if_splits simp: pmf_cond)
  with Some show ?thesis by simp
qed simp_all


lemma binomial_pmf_code [code abstract]:
  "mapping_of_pmf (binomial_pmf n p) = (
     if p < 0 \<or> p > 1 then 
       Code.abort (STR ''binomial_pmf with invalid probability'') 
         (\<lambda>_. mapping_of_pmf (binomial_pmf n p))
     else if p = 0 then Mapping.update 0 1 Mapping.empty
     else if p = 1 then Mapping.update n 1 Mapping.empty
     else Mapping.tabulate [0..<Suc n] (\<lambda>k. real (n choose k) * p ^ k * (1 - p) ^ (n - k)))"
  by (cases "p < 0 \<or> p > 1")
     (simp, intro mapping_of_pmfI, 
      auto simp: lookup_update' lookup_empty set_pmf_binomial_eq lookup_tabulate split: if_splits)


lemma pred_pmf_code [code]:
  "pred_pmf P p = (\<forall>x\<in>set_pmf p. P x)"
  by (auto simp: pred_pmf_def)


lemma mapping_of_pmf_pmf_of_list:
  assumes "\<And>x. x \<in> snd ` set xs \<Longrightarrow> x > 0" "sum_list (map snd xs) = 1"
  shows   "mapping_of_pmf (pmf_of_list xs) = 
             Mapping.tabulate (remdups (map fst xs)) 
               (\<lambda>x. sum_list (map snd (filter (\<lambda>z. fst z = x) xs)))"
proof -
  from assms have wf: "pmf_of_list_wf xs" by (intro pmf_of_list_wfI) force
  with assms have "set_pmf (pmf_of_list xs) = fst ` set xs"
    by (intro set_pmf_of_list_eq) auto
  with wf show ?thesis
    by (intro mapping_of_pmfI) (auto simp: lookup_tabulate pmf_pmf_of_list)
qed

lemma mapping_of_pmf_pmf_of_list':
  assumes "pmf_of_list_wf xs"
  defines "xs' \<equiv> filter (\<lambda>z. snd z \<noteq> 0) xs"
  shows   "mapping_of_pmf (pmf_of_list xs) = 
             Mapping.tabulate (remdups (map fst xs')) 
               (\<lambda>x. sum_list (map snd (filter (\<lambda>z. fst z = x) xs')))" (is "_ = ?rhs") 
proof -
  have wf: "pmf_of_list_wf xs'" unfolding xs'_def by (rule pmf_of_list_remove_zeros) fact
  have pos: "\<forall>x\<in>snd`set xs'. x > 0" using assms(1) unfolding xs'_def
    by (force simp: pmf_of_list_wf_def)
  from assms have "pmf_of_list xs = pmf_of_list xs'" 
    unfolding xs'_def by (subst pmf_of_list_remove_zeros) simp_all
  also from wf pos have "mapping_of_pmf \<dots> = ?rhs"
    by (intro mapping_of_pmf_pmf_of_list) (auto simp: pmf_of_list_wf_def)
  finally show ?thesis .
qed

lemma pmf_of_list_wf_code [code]:
  "pmf_of_list_wf xs \<longleftrightarrow> list_all (\<lambda>z. snd z \<ge> 0) xs \<and> sum_list (map snd xs) = 1"
  by (auto simp add: pmf_of_list_wf_def list_all_def)

lemma pmf_of_list_code [code abstract]:
  "mapping_of_pmf (pmf_of_list xs) = (
     if pmf_of_list_wf xs then
       let xs' = filter (\<lambda>z. snd z \<noteq> 0) xs
       in  Mapping.tabulate (remdups (map fst xs')) 
             (\<lambda>x. sum_list (map snd (filter (\<lambda>z. fst z = x) xs')))
     else
       Code.abort (STR ''Invalid list for pmf_of_list'') (\<lambda>_. mapping_of_pmf (pmf_of_list xs)))"
  using mapping_of_pmf_pmf_of_list'[of xs] by (simp add: Let_def)

lemma mapping_of_pmf_eq_iff [simp]:
  "mapping_of_pmf p = mapping_of_pmf q \<longleftrightarrow> p = (q :: 'a pmf)"
proof (transfer, intro iffI pmf_eqI)
  fix p q :: "'a pmf" and x :: 'a
  assume "(\<lambda>x. if pmf p x = 0 then None else Some (pmf p x)) =
            (\<lambda>x. if pmf q x = 0 then None else Some (pmf q x))"
  hence "(if pmf p x = 0 then None else Some (pmf p x)) =
           (if pmf q x = 0 then None else Some (pmf q x))" for x
    by (simp add: fun_eq_iff)
  from this[of x] show "pmf p x = pmf q x" by (auto split: if_splits)
qed (simp_all cong: if_cong)


subsection \<open>Code abbreviations for integrals and probabilities\<close>

text \<open>
  Integrals and probabilities are defined for general measures, so we cannot give any
  code equations directly. We can, however, specialise these constants them to PMFs, 
  give code equations for these specialised constants, and tell the code generator 
  to unfold the original constants to the specialised ones whenever possible.
\<close>

definition pmf_integral where
  "pmf_integral p f = lebesgue_integral (measure_pmf p) (f :: _ \<Rightarrow> real)"

definition pmf_set_integral where
  "pmf_set_integral p f A = lebesgue_integral (measure_pmf p) (\<lambda>x. indicator A x * f x :: real)"

definition pmf_prob where
  "pmf_prob p A = measure_pmf.prob p A"

lemma pmf_prob_compl: "pmf_prob p (-A) = 1 - pmf_prob p A"
  using measure_pmf.prob_compl[of A p] by (simp add: pmf_prob_def Compl_eq_Diff_UNIV)

lemma pmf_integral_pmf_set_integral [code]:
  "pmf_integral p f = pmf_set_integral p f (set_pmf p)"
  unfolding pmf_integral_def pmf_set_integral_def
  by (intro integral_cong_AE) (simp_all add: AE_measure_pmf_iff)

lemma pmf_prob_pmf_set_integral:
  "pmf_prob p A = pmf_set_integral p (\<lambda>_. 1) A"
  by (simp add: pmf_prob_def pmf_set_integral_def)
  
lemma pmf_set_integral_code_alt_finite:
  "finite A \<Longrightarrow> pmf_set_integral p f A = (\<Sum>x\<in>A. pmf p x * f x)"
  unfolding pmf_set_integral_def
  by (subst integral_measure_pmf[of A]) (auto simp: indicator_def mult_ac split: if_splits)
  
lemma pmf_set_integral_code [code]:
  "pmf_set_integral p f (set xs) = (\<Sum>x\<in>set xs. pmf p x * f x)"
  by (rule pmf_set_integral_code_alt_finite) simp_all


lemma pmf_prob_code_alt_finite:
  "finite A \<Longrightarrow> pmf_prob p A = (\<Sum>x\<in>A. pmf p x)"
  by (simp add: pmf_prob_pmf_set_integral pmf_set_integral_code_alt_finite)

lemma pmf_prob_code [code]:
  "pmf_prob p (set xs) = (\<Sum>x\<in>set xs. pmf p x)"
  "pmf_prob p (List.coset xs) = 1 - (\<Sum>x\<in>set xs. pmf p x)"
  by (simp_all add: pmf_prob_code_alt_finite pmf_prob_compl)
  

lemma pmf_prob_code_unfold [code_abbrev]: "pmf_prob p = measure_pmf.prob p"
  by (intro ext) (simp add: pmf_prob_def)

(* FIXME: Why does this not work without parameters? *)
lemma pmf_integral_code_unfold [code_abbrev]: "pmf_integral p = measure_pmf.expectation p"
  by (intro ext) (simp add: pmf_integral_def)



definition "pmf_of_alist xs = embed_pmf (\<lambda>x. case map_of xs x of Some p \<Rightarrow> p | None \<Rightarrow> 0)"

lemma pmf_of_mapping_Mapping [code_post]:
    "pmf_of_mapping (Mapping xs) = pmf_of_alist xs"
  unfolding pmf_of_mapping_def Mapping.lookup_default_def [abs_def] pmf_of_alist_def
  by transfer simp_all


instantiation pmf :: (equal) equal
begin

definition "equal_pmf p q = (mapping_of_pmf p = mapping_of_pmf (q :: 'a pmf))"

instance by standard (simp add: equal_pmf_def)
end

definition single :: "'a \<Rightarrow> 'a multiset" where
"single s = {#s#}"

instantiation pmf :: (random) random
begin

context
  includes state_combinator_syntax term_syntax
begin

definition
  pmfify :: "('b::typerep multiset \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<Rightarrow>
             'b \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
             'b pmf \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "pmfify A x =  
    Code_Evaluation.valtermify pmf_of_multiset {\<cdot>} 
      (Code_Evaluation.valtermify (+) {\<cdot>} A {\<cdot>} 
       (Code_Evaluation.valtermify single {\<cdot>} x))"

definition
  "Quickcheck_Random.random i = 
     Quickcheck_Random.random i \<circ>\<rightarrow> (\<lambda>A. 
       Quickcheck_Random.random i \<circ>\<rightarrow> (\<lambda>x. Pair (pmfify A x)))"

instance ..

end

end

instantiation pmf :: (full_exhaustive) full_exhaustive
begin

definition full_exhaustive_pmf :: "('a pmf \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "full_exhaustive_pmf f i =
     Quickcheck_Exhaustive.full_exhaustive (\<lambda>A. 
       Quickcheck_Exhaustive.full_exhaustive (\<lambda>x. f (pmfify A x)) i) i"

instance ..

end

end
