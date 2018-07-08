(*  Title:      HOL/Algebra/Cycles.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Cycles
  imports "HOL-Library.Permutations" "HOL-Library.FuncSet"
begin

section \<open>Cycles\<close>

abbreviation cycle :: "'a list \<Rightarrow> bool" where
  "cycle cs \<equiv> distinct cs"

fun cycle_of_list :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a"
  where
    "cycle_of_list (i # j # cs) = (Fun.swap i j id) \<circ> (cycle_of_list (j # cs))"
  | "cycle_of_list cs = id"


subsection\<open>Cycles as Rotations\<close>

text\<open>We start proving that the function derived from a cycle rotates its support list.\<close>

lemma id_outside_supp:
  assumes "cycle cs" and "x \<notin> set cs"
  shows "(cycle_of_list cs) x = x" using assms
proof (induction cs rule: cycle_of_list.induct)
  case (1 i j cs)
  have "cycle_of_list (i # j # cs) x = (Fun.swap i j id) (cycle_of_list (j # cs) x)" by simp
  also have " ... = (Fun.swap i j id) x"
    using "1.IH" "1.prems"(1) "1.prems"(2) by auto
  also have " ... = x" using 1(3) by simp
  finally show ?case .
next
  case "2_1" thus ?case by simp
next
  case "2_2" thus ?case by simp
qed

lemma cycle_permutes:
  assumes "cycle cs"
  shows "permutation (cycle_of_list cs)"
proof (induction rule: cycle_of_list.induct)
  case (1 i j cs) thus ?case
    by (metis cycle_of_list.simps(1) permutation_compose permutation_swap_id)
next
  case "2_1" thus ?case by simp
next
  case "2_2" thus ?case by simp
qed

theorem cyclic_rotation:
  assumes "cycle cs"
  shows "map ((cycle_of_list cs) ^^ n) cs = rotate n cs"
proof -
  { have "map (cycle_of_list cs) cs = rotate1 cs" using assms(1)
    proof (induction cs rule: cycle_of_list.induct)
      case (1 i j cs) thus ?case
      proof (cases)
        assume "cs = Nil" thus ?thesis by simp
      next
        assume "cs \<noteq> Nil" hence ge_two: "length (j # cs) \<ge> 2"
          using not_less by auto
        have "map (cycle_of_list (i # j # cs)) (i # j # cs) =
              map (Fun.swap i j id) (map (cycle_of_list (j # cs)) (i # j # cs))" by simp
        also have " ... = map (Fun.swap i j id) (i # (rotate1 (j # cs)))"
          by (metis "1.IH" "1.prems" distinct.simps(2) id_outside_supp list.simps(9))
        also have " ... = map (Fun.swap i j id) (i # (cs @ [j]))" by simp
        also have " ... = j # (map (Fun.swap i j id) cs) @ [i]" by simp
        also have " ... = j # cs @ [i]"
          by (metis "1.prems" distinct.simps(2) list.set_intros(2) map_idI swap_id_eq)
        also have " ... = rotate1 (i # j # cs)" by simp
        finally show ?thesis .
      qed
    next
      case "2_1" thus ?case by simp
    next
      case "2_2" thus ?case by simp
    qed }
  note cyclic_rotation' = this

  from assms show ?thesis
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    have "map ((cycle_of_list cs) ^^ (Suc n)) cs =
          map (cycle_of_list cs) (map ((cycle_of_list cs) ^^ n) cs)" by simp
    also have " ... = map (cycle_of_list cs) (rotate n cs)"
      by (simp add: Suc.IH assms)
    also have " ... = rotate (Suc n) cs"
      using cyclic_rotation'
      by (metis rotate1_rotate_swap rotate_Suc rotate_map)
    finally show ?case .
  qed
qed

corollary cycle_is_surj:
  assumes "cycle cs"
  shows "(cycle_of_list cs) ` (set cs) = (set cs)"
  using cyclic_rotation[OF assms, of 1] by (simp add: image_set)

corollary cycle_is_id_root:
  assumes "cycle cs"
  shows "(cycle_of_list cs) ^^ (length cs) = id"
proof -
  have "map ((cycle_of_list cs) ^^ (length cs)) cs = cs"
    by (simp add: assms cyclic_rotation)
  hence "\<And>x. x \<in> (set cs) \<Longrightarrow> ((cycle_of_list cs) ^^ (length cs)) x = x"
    using map_eq_conv by fastforce
  moreover have "\<And>n x. x \<notin> (set cs) \<Longrightarrow> ((cycle_of_list cs) ^^ n) x = x"
  proof -
    fix n show "\<And>x. x \<notin> (set cs) \<Longrightarrow> ((cycle_of_list cs) ^^ n) x = x"
    proof (induction n)
      case 0 thus ?case by simp
    next
      case (Suc n) thus ?case using id_outside_supp[OF assms] by simp
    qed
  qed
  hence "\<And>x. x \<notin> (set cs) \<Longrightarrow> ((cycle_of_list cs) ^^ (length cs)) x = x" by simp
  ultimately show ?thesis
    by (meson eq_id_iff)
qed

corollary
  assumes "cycle cs"
  shows "(cycle_of_list cs) = (cycle_of_list (rotate n cs))"
proof -
  { fix cs :: "'a list" assume A: "cycle cs"
    have "(cycle_of_list cs) = (cycle_of_list (rotate1 cs))"
    proof
      have "\<And>x. x \<in> set cs \<Longrightarrow> (cycle_of_list cs) x = (cycle_of_list (rotate1 cs)) x"
      proof -
        have "cycle (rotate1 cs)" using A by simp
        hence "map (cycle_of_list (rotate1 cs)) (rotate1 cs) = (rotate 2 cs)"
          using cyclic_rotation by (metis Suc_eq_plus1 add.left_neutral
          funpow.simps(2) funpow_simps_right(1) o_id one_add_one rotate_Suc rotate_def)
        also have " ... = map (cycle_of_list cs) (rotate1 cs)"
          using cyclic_rotation[OF A]
          by (metis One_nat_def Suc_1 funpow.simps(2) id_apply map_map rotate0 rotate_Suc)
        finally have "map (cycle_of_list (rotate1 cs)) (rotate1 cs) = 
                    map (cycle_of_list cs) (rotate1 cs)" .
        moreover fix x assume "x \<in> set cs"
        ultimately show "(cycle_of_list cs) x = (cycle_of_list (rotate1 cs)) x" by auto
      qed
      moreover have "\<And>x. x \<notin> set cs \<Longrightarrow> (cycle_of_list cs) x = (cycle_of_list (rotate1 cs)) x"
        using A by (simp add: id_outside_supp)
      ultimately show "\<And>x. (cycle_of_list cs) x = (cycle_of_list (rotate1 cs)) x" by blast
    qed }
  note rotate1_lemma = this

  show "cycle_of_list cs = cycle_of_list (rotate n cs)"
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    have "cycle (rotate n cs)" by (simp add: assms)
    thus ?case using rotate1_lemma[of "rotate n cs"]
      by (simp add: Suc.IH)
  qed
qed


subsection\<open>Conjugation of cycles\<close>

lemma conjugation_of_cycle:
  assumes "cycle cs" and "bij p"
  shows "p \<circ> (cycle_of_list cs) \<circ> (inv p) = cycle_of_list (map p cs)"
  using assms
proof (induction cs rule: cycle_of_list.induct)
  case (1 i j cs)
  have "p \<circ> cycle_of_list (i # j # cs) \<circ> inv p =
       (p \<circ> (Fun.swap i j id) \<circ> inv p) \<circ> (p \<circ> cycle_of_list (j # cs) \<circ> inv p)"
    by (simp add: assms(2) bij_is_inj fun.map_comp)
  also have " ... = (Fun.swap (p i) (p j) id) \<circ> (p \<circ> cycle_of_list (j # cs) \<circ> inv p)"
    by (simp add: "1.prems"(2) bij_is_inj bij_swap_comp comp_swap o_assoc)
  finally have "p \<circ> cycle_of_list (i # j # cs) \<circ> inv p =
               (Fun.swap (p i) (p j) id) \<circ> (cycle_of_list (map p (j # cs)))"
    using "1.IH" "1.prems"(1) assms(2) by fastforce
  thus ?case by (metis cycle_of_list.simps(1) list.simps(9))
next
  case "2_1" thus ?case
    by (metis bij_is_surj comp_id cycle_of_list.simps(2) list.simps(8) surj_iff) 
next
  case "2_2" thus ?case
    by (metis bij_is_surj comp_id cycle_of_list.simps(3) list.simps(8) list.simps(9) surj_iff) 
qed


subsection\<open>When Cycles Commute\<close>

lemma cycles_commute:
  assumes "cycle \<sigma>1" "cycle \<sigma>2" and "set \<sigma>1 \<inter> set \<sigma>2 = {}"
  shows "(cycle_of_list \<sigma>1) \<circ> (cycle_of_list \<sigma>2) = (cycle_of_list \<sigma>2) \<circ> (cycle_of_list \<sigma>1)"
proof -
  { fix \<pi>1 :: "'a list" and \<pi>2 :: "'a list" and x :: "'a"
    assume A: "cycle \<pi>1" "cycle \<pi>2" "set \<pi>1 \<inter> set \<pi>2 = {}" "x \<in> set \<pi>1" "x \<notin> set \<pi>2"
    have "((cycle_of_list \<pi>1) \<circ> (cycle_of_list \<pi>2)) x =
          ((cycle_of_list \<pi>2) \<circ> (cycle_of_list \<pi>1)) x"
    proof -
      have "((cycle_of_list \<pi>1) \<circ> (cycle_of_list \<pi>2)) x = (cycle_of_list \<pi>1) x"
        using id_outside_supp[OF A(2) A(5)] by simp
      also have " ... = ((cycle_of_list \<pi>2) \<circ> (cycle_of_list \<pi>1)) x"
        using id_outside_supp[OF A(2), of "(cycle_of_list \<pi>1) x"]
              cycle_is_surj[OF A(1)] A(3) A(4) by fastforce
      finally show ?thesis .
    qed }
  note aux_lemma = this

  let ?\<sigma>12 = "\<lambda>x. ((cycle_of_list \<sigma>1) \<circ> (cycle_of_list \<sigma>2)) x"
  let ?\<sigma>21 = "\<lambda>x. ((cycle_of_list \<sigma>2) \<circ> (cycle_of_list \<sigma>1)) x"

  show ?thesis
  proof
    fix x have "x \<in> set \<sigma>1 \<union> set \<sigma>2 \<or> x \<notin> set \<sigma>1 \<union> set \<sigma>2" by blast
    from this show "?\<sigma>12 x = ?\<sigma>21 x"
    proof 
      assume "x \<in> set \<sigma>1 \<union> set \<sigma>2"
      hence "(x \<in> set \<sigma>1 \<and> x \<notin> set \<sigma>2) \<or> (x \<notin> set \<sigma>1 \<and> x \<in> set \<sigma>2)" using assms(3) by blast
      from this show "?\<sigma>12 x = ?\<sigma>21 x"
      proof
        assume "x \<in> set \<sigma>1 \<and> x \<notin> set \<sigma>2" thus ?thesis
          using aux_lemma[OF assms(1-3)] by simp
      next
        assume "x \<notin> set \<sigma>1 \<and> x \<in> set \<sigma>2" thus ?thesis
          using assms aux_lemma inf_commute by metis
      qed
    next
      assume "x \<notin> set \<sigma>1 \<union> set \<sigma>2" thus ?thesis using id_outside_supp assms(1-2)
        by (metis UnCI comp_apply)
    qed
  qed
qed


subsection\<open>Cycles from Permutations\<close>

subsubsection\<open>Exponentiation of permutations\<close>

text\<open>Some important properties of permutations before defining how to extract its cycles\<close>

lemma exp_of_permutation1:
  assumes "p permutes S"
  shows "(p ^^ n) permutes S" using assms
proof (induction n)
  case 0 thus ?case by (simp add: permutes_def) 
next
  case (Suc n) thus ?case by (metis funpow_Suc_right permutes_compose) 
qed

lemma exp_of_permutation2:
  assumes "p permutes S"
    and "i < j" "(p ^^ j) = (p ^^ i)"
  shows "(p ^^ (j - i)) = id" using assms
proof -
  have "(p ^^ i) \<circ> (p ^^ (j - i)) = (p ^^ j)"
    by (metis add_diff_inverse_nat assms(2) funpow_add le_eq_less_or_eq not_le)
  also have " ... = (p ^^ i)" using assms(3) by simp
  finally have "(p ^^ i) \<circ> (p ^^ (j - i)) = (p ^^ i)" .
  moreover have "bij (p ^^ i)" using exp_of_permutation1[OF assms(1)]
    using permutes_bij by auto
  ultimately show ?thesis
    by (metis (no_types, lifting) bij_is_inj comp_assoc fun.map_id inv_o_cancel)
qed

lemma exp_of_permutation3:
  assumes "p permutes S" "finite S"
  shows "\<exists>n. (p ^^ n) = id \<and> n > 0"
proof (rule ccontr)
  assume "\<nexists>n. (p ^^ n) = id \<and> 0 < n"
  hence S: "\<And>n. n > 0 \<Longrightarrow> (p ^^ n) \<noteq> id" by auto
  hence "\<And>i j. \<lbrakk> i \<ge> 0; j \<ge> 0 \<rbrakk> \<Longrightarrow> i \<noteq> j \<Longrightarrow> (p ^^ i) \<noteq> (p ^^ j)"
  proof -
    fix i :: "nat" and j :: "nat" assume "i \<ge> 0" "j \<ge> 0" and Ineq: "i \<noteq> j"
    show "(p ^^ i) \<noteq> (p ^^ j)"
    proof (rule ccontr)
      assume "\<not> (p ^^ i) \<noteq> (p ^^ j)" hence Eq: "(p ^^ i) = (p ^^ j)" by simp
      have "(p ^^ (j - i)) = id" if "j > i"
        using Eq exp_of_permutation2[OF assms(1) that] by simp
      moreover have "(p ^^ (i - j)) = id" if "i > j"
        using Eq exp_of_permutation2[OF assms(1) that] by simp
      ultimately show False using Ineq S
        by (meson le_eq_less_or_eq not_le zero_less_diff)
    qed
  qed
  hence "bij_betw (\<lambda>i. (p ^^ i)) {i :: nat . i \<ge> 0} {(p ^^ i) | i :: nat . i \<ge> 0}"
    unfolding bij_betw_def inj_on_def by blast
  hence "infinite {(p ^^ i) | i :: nat . i \<ge> 0}"
    using bij_betw_finite by auto
  moreover have "{(p ^^ i) | i :: nat . i \<ge> 0} \<subseteq> {\<pi>. \<pi> permutes S}"
    using exp_of_permutation1[OF assms(1)] by blast
  hence "finite {(p ^^ i) | i :: nat . i \<ge> 0}"
    by (simp add: assms(2) finite_permutations finite_subset)
  ultimately show False ..
qed

lemma power_prop:
  assumes "(p ^^ k) x = x" 
  shows "(p ^^ (k * l)) x = x"
proof (induction l)
  case 0 thus ?case by simp
next
  case (Suc l)
  hence "(p ^^ (k * (Suc l))) x = ((p ^^ (k * l)) \<circ> (p ^^ k)) x"
    by (metis funpow_Suc_right funpow_mult)
  also have " ... = (p ^^ (k * l)) x"
    by (simp add: assms)
  also have " ... = x"
    using Suc.IH Suc.prems assms by blast
  finally show ?case . 
qed

lemma exp_of_permutation4:
  assumes "p permutes S" "finite S"
  shows "\<exists>n. (p ^^ n) = id \<and> n > m"
proof -
  obtain k where "k > 0" "(p ^^ k) = id"
    using exp_of_permutation3[OF assms] by blast
  moreover obtain n where "n * k > m"
    by (metis calculation(1) dividend_less_times_div mult.commute mult_Suc_right)
  ultimately show ?thesis
      by (metis (full_types) funpow_mult id_funpow mult.commute)
qed


subsubsection\<open>Extraction of cycles from permutations\<close>

definition
  least_power :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat"
  where "least_power f x = (LEAST n. (f ^^ n) x = x \<and> n > 0)"

abbreviation
  support :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "support p x \<equiv> map (\<lambda>i. (p ^^ i) x) [0..< (least_power p x)]"

lemma least_power_wellfounded:
  assumes "permutation p"
  shows "(p ^^ (least_power p x)) x = x"
proof -
  obtain S where "p permutes S" "finite S"
    using assms permutation_permutes by blast
  hence "\<exists>n. (p ^^ n) x = x \<and> n > 0"
    using eq_id_iff exp_of_permutation3 by metis
  thus ?thesis unfolding least_power_def
    by (metis (mono_tags, lifting) LeastI_ex)
qed

lemma least_power_gt_zero:
  assumes "permutation p"
  shows "least_power p x > 0"
proof (rule ccontr)
  obtain S where "p permutes S" "finite S"
    using assms permutation_permutes by blast
  hence Ex: "\<exists>n. (p ^^ n) x = x \<and> n > 0"
    using eq_id_iff exp_of_permutation3 by metis
  assume "\<not> 0 < least_power p x" hence "least_power p x = 0"
    using Ex unfolding least_power_def by (metis (mono_tags, lifting) LeastI)
  thus False unfolding least_power_def
    by (metis (mono_tags, lifting) Ex LeastI_ex less_irrefl) 
qed

lemma least_power_gt_one:
  assumes "permutation p" "p x \<noteq> x"
  shows "least_power p x > Suc 0"
proof (rule ccontr)
  obtain S where "p permutes S" "finite S"
    using assms permutation_permutes by blast
  hence Ex: "\<exists>n. (p ^^ n) x = x \<and> n > 0"
    using eq_id_iff exp_of_permutation3 by metis
  assume "\<not> Suc 0 < least_power p x" hence "least_power p x = (Suc 0)"
    using Ex unfolding least_power_def by (metis (mono_tags, lifting) LeastI Suc_lessI)
  hence "p x = x" using least_power_wellfounded[OF assms(1), of x] by simp
  from \<open>p x = x\<close> and \<open>p x \<noteq> x\<close> show False by simp
qed

lemma least_power_bound:
  assumes "permutation p" shows "\<exists>m > 0. (least_power p x) \<le> m"
proof -
  obtain S where "p permutes S" "finite S"
    using assms permutation_permutes by blast
  hence "\<exists>n. (p ^^ n) x = x \<and> n > 0"
    using eq_id_iff exp_of_permutation3 by metis
  then obtain m :: "nat"  where "m > 0" "m = (least_power p x)"
    unfolding least_power_def by (metis (mono_tags, lifting) LeastI_ex)
  thus ?thesis by blast
qed

lemma lt_least_power:
  assumes "Suc n = least_power p x"
    and "0 < i" "i \<le> n"
  shows "(p ^^ i) x \<noteq> x"
proof (rule ccontr)
  assume "\<not> (p ^^ i) x \<noteq> x" hence "(p ^^ i) x = x" by simp
  hence "i \<in> {n. (p ^^ n) x = x \<and> n > 0}"
    using assms(2-3) by blast
  moreover have "i < least_power p x"
    using assms(3) assms(1) by linarith
  ultimately show False unfolding least_power_def
    using not_less_Least by auto
qed

lemma least_power_welldefined:
  assumes "permutation p" and "y \<in> {(p ^^ k) x | k. k \<ge> 0}"
  shows "least_power p x = least_power p y"
proof -
  have aux_lemma: "\<And>z. least_power p z = least_power p (p z)"
  proof -
    fix z
    have "(p ^^ (least_power p z)) z = z"
      by (metis assms(1) least_power_wellfounded)
    hence "(p ^^ (least_power p z)) (p z) = (p z)"
      by (metis funpow_swap1)
    hence "least_power p z \<ge> least_power p (p z)"
      by (metis assms(1) inc_induct le_SucE least_power_gt_zero lt_least_power nat_le_linear)

    moreover have "(p ^^ (least_power p (p z))) (p z) = (p z)"
      by (simp add: assms(1) least_power_wellfounded)
    hence "(p ^^ (least_power p (p z))) z = z"
      by (metis assms(1) funpow_swap1 permutation_permutes permutes_def)
    hence "least_power p z \<le> least_power p (p z)"
      by (metis assms(1) least_power_gt_zero less_imp_Suc_add lt_least_power not_less_eq_eq)

    ultimately show "least_power p z = least_power p (p z)" by simp 
  qed

  obtain k where "k \<ge> 0" "y = (p ^^ k) x"
    using assms(2) by blast
  thus ?thesis
  proof (induction k arbitrary: x y)
    case 0 thus ?case by simp
  next
    case (Suc k)
    have "least_power p ((p ^^ k) x) = least_power p x"
      using Suc.IH by fastforce
    thus ?case using aux_lemma
      using Suc.prems(2) by auto
  qed
qed

theorem cycle_of_permutation:
  assumes "permutation p"
  shows "cycle (support p x)"
proof (rule ccontr)
  assume "\<not> cycle (support p x)"
  hence "\<exists> i j. i \<in> {0..<least_power p x} \<and> j \<in> {0..<least_power p x} \<and> i \<noteq> j \<and> (p ^^ i) x = (p ^^ j) x"
    using atLeast_upt by (simp add: distinct_conv_nth) 
  then obtain i j where ij: "0 \<le> i" "i < j" "j < least_power p x"
                    and "(p ^^ i) x = (p ^^ j) x"
    by (metis atLeast_upt le0 le_eq_less_or_eq lessThan_iff not_less set_upt)
  hence "(p ^^ i) x = (p ^^ i) ((p ^^ (j - i)) x)"
    by (metis add_diff_inverse_nat funpow_add not_less_iff_gr_or_eq o_apply)
  hence "(p ^^ (j - i)) x = x"
    using exp_of_permutation1 assms by (metis bij_pointE permutation_permutes permutes_bij)
  moreover have "0 \<le> j - i \<and> j - i < least_power p x"
    by (simp add: ij(3) less_imp_diff_less)
  hence "(p ^^ (j - i)) x \<noteq> x" using lt_least_power ij
    by (metis diff_le_self lessE less_imp_diff_less less_imp_le zero_less_diff)
  ultimately show False by simp
qed


subsection\<open>Decomposition on Cycles\<close>

text\<open>We show that a permutation can be decomposed on cycles\<close>

subsubsection\<open>Preliminaries\<close>

lemma support_set:
  assumes "permutation p"
  shows "set (support p x) = {(p ^^ k) x | k. k \<ge> 0}"
proof -
  have "{(p ^^ k) x | k. k \<ge> 0} = {(p ^^ k) x | k. 0 \<le> k \<and> k < (least_power p x)}" (is "?A = ?B")
  proof
    show "?B \<subseteq> ?A" by blast
  next
    show "?A \<subseteq> ?B"
    proof
      fix y assume "y \<in> ?A"
      then obtain k :: "nat" where k: "k \<ge> 0" "(p ^^ k) x = y" by blast
      hence "k = (least_power p x) * (k div (least_power p x)) + (k mod (least_power p x))" by simp
      hence "y = (p ^^ ((least_power p x) * (k div (least_power p x)) + (k mod (least_power p x)))) x"
        using k by auto
      hence " y = (p ^^ (k mod (least_power p x))) x"
        using power_prop[OF least_power_wellfounded[OF assms, of x], of "k div (least_power p x)"]
        by (metis add.commute funpow_add o_apply)
      moreover have "k mod (least_power p x) < least_power p x"
        using k mod_less_divisor[of "least_power p x" k, OF least_power_gt_zero[OF assms]] by simp
      ultimately show "y \<in> ?B"
        by blast
    qed
  qed

  moreover have "{(p ^^ k) x | k. 0 \<le> k \<and> k < (least_power p x)} = set (support p x)" (is "?B = ?C")
  proof
    show "?B \<subseteq> ?C"
    proof
      fix y assume "y \<in> {(p ^^ k) x | k. 0 \<le> k \<and> k < (least_power p x)}"
      then obtain k where "k \<ge> 0" "k < (least_power p x)" "y = (p ^^ k) x" by blast
      thus "y \<in> ?C" by auto
    qed
  next
    show "?C \<subseteq> ?B"
    proof
      fix y assume "y \<in> ?C"
      then obtain k where "k \<ge> 0" "k < (least_power p x)" "(support p x) ! k = y" by auto
      thus "y \<in> ?B" by auto
    qed
  qed

  ultimately show ?thesis by simp
qed

lemma disjoint_support:
  assumes "p permutes S" "finite S"
  shows "disjoint {{(p ^^ k) x | k. k \<ge> 0} | x. x \<in> S}" (is "disjoint ?A")
proof (rule disjointI)
  { fix a b assume "a \<in> ?A" "b \<in> ?A" "a \<inter> b \<noteq> {}"
    then obtain x y where x: "x \<in> S" "a = {(p ^^ k) x | k. k \<ge> 0}"
                      and y: "y \<in> S" "b = {(p ^^ k) y | k. k \<ge> 0}" by blast 
    assume "a \<inter> b \<noteq> {}"
    then obtain z kx ky where z: "kx \<ge> 0" "ky \<ge> 0" "z = (p ^^ kx) x" "z = (p ^^ ky) y"
      using x(2) y(2) by blast
    have "a \<subseteq> b"
    proof
      fix w assume "w \<in> a"
      then obtain k where k: "k \<ge> 0" "w = (p ^^ k) x" using x by blast
      define l where "l = (kx div (least_power p w)) + 1"
      hence l: "l * (least_power p w) > kx"
        using least_power_gt_zero assms One_nat_def add.right_neutral add_Suc_right
            mult.commute permutation_permutes
        by (metis dividend_less_times_div mult_Suc_right) 

      have "w = (p ^^ (l * (least_power p w))) w"
        by (metis assms least_power_wellfounded mult.commute permutation_permutes power_prop)
      also have "... = (p ^^ (l * (least_power p w) + k)) x"
        using k by (simp add: funpow_add) 
      also have " ... = (p ^^ (l * (least_power p w) + k - kx + kx)) x"
        using l by auto
      also have " ... = (p ^^ (l * (least_power p w) + k - kx)) ((p ^^ kx) x)"
        by (simp add: funpow_add)
      also have " ... = (p ^^ (l * (least_power p w) + k - kx)) ((p ^^ ky) y)" using z
        by simp
      finally have "w = (p ^^ (l * (least_power p w) + k - kx + ky)) y"
        by (simp add: funpow_add)
      thus "w \<in> b" using y by blast
    qed } note aux_lemma = this

  fix a b assume ab: "a \<in> ?A" "b \<in> ?A" "a \<noteq> b"
  show "a \<inter> b = {}"
  proof (rule ccontr)
    assume "a \<inter> b \<noteq> {}" thus False using aux_lemma ab
      by (metis (no_types, lifting) inf.absorb2 inf.orderE)
  qed
qed

lemma support_coverture:
  assumes "p permutes S" "finite S"
  shows "\<Union>{{(p ^^ k) x | k. k \<ge> 0} | x. x \<in> S} = S"
proof
  show "\<Union>{{(p ^^ k) x |k. 0 \<le> k} |x. x \<in> S} \<subseteq> S"
  proof
    fix y assume "y \<in> \<Union>{{(p ^^ k) x |k. 0 \<le> k} |x. x \<in> S}"
    then obtain x k where x: "x \<in> S" and k: "k \<ge> 0" and y: "y = (p ^^ k) x" by blast
    have "(p ^^ k) x \<in> S"
    proof (induction k)
      case 0 thus ?case using x by simp
    next
      case (Suc k) thus ?case using assms
        by (simp add: permutes_in_image) 
    qed
    thus "y \<in> S" using y by simp
  qed
next
  show "S \<subseteq> \<Union>{{(p ^^ k) x |k. 0 \<le> k} |x. x \<in> S}"
  proof
    fix x assume x: "x \<in> S"
    hence "x \<in> {(p ^^ k) x |k. 0 \<le> k}"
      by (metis (mono_tags, lifting) CollectI funpow_0 le_numeral_extra(3))
    thus "x \<in> \<Union>{{(p ^^ k) x |k. 0 \<le> k} |x. x \<in> S}" using x by blast
  qed
qed

theorem cycle_restrict:
  assumes "permutation p" "y \<in> set (support p x)"
  shows "p y = (cycle_of_list (support p x)) y"
proof -
  have "\<And> i. \<lbrakk> 0 \<le> i; i < length (support p x) - 1 \<rbrakk> \<Longrightarrow>
         p ((support p x) ! i) = (support p x) ! (i + 1)"
  proof -
    fix i assume i: "0 \<le> i" "i < length (support p x) - 1"
    hence "p ((support p x) ! i) = p ((p ^^ i) x)" by simp
    also have " ... = (p ^^ (i + 1)) x" by simp
    also have " ... = (support p x) ! (i + 1)"
      using i by simp
    finally show "p ((support p x) ! i) = (support p x) ! (i + 1)" .
  qed
  hence 1: "map p (butlast (support p x)) = tl (support p x)"
    using nth_butlast [where 'a='a] nth_tl [where 'a='a]
      nth_equalityI[of "map p (butlast (support p x))" "tl (support p x)"] by force
  have "p ((support p x) ! (length (support p x) - 1)) = p ((p ^^ (length (support p x) - 1)) x)"
    using assms(2) by auto
  also have " ... = (p ^^ (length (support p x))) x"
    by (metis (mono_tags, lifting) Suc_pred' assms(2) funpow_Suc_right
        funpow_swap1 length_pos_if_in_set o_apply)
  also have " ... = x"
    by (simp add: assms(1) least_power_wellfounded)
  also have " ... = (support p x) ! 0"
    by (simp add: assms(1) least_power_gt_zero)
  finally have "p ((support p x) ! (length (support p x) - 1)) = (support p x) ! 0" .
  hence 2: "p (last (support p x)) = hd (support p x)"
    by (metis assms(2) hd_conv_nth last_conv_nth length_greater_0_conv length_pos_if_in_set)

  have "map p (support p x) = (tl (support p x)) @ [hd (support p x)]" using 1 2
    by (metis (no_types, lifting) assms(2) last_map length_greater_0_conv
        length_pos_if_in_set list.map_disc_iff map_butlast snoc_eq_iff_butlast) 
  hence "map p (support p x) = rotate1 (support p x)"
    by (metis assms(2) length_greater_0_conv length_pos_if_in_set rotate1_hd_tl)

  moreover have "map (cycle_of_list (support p x)) (support p x) = rotate1 (support p x)"
    using cyclic_rotation[OF cycle_of_permutation[OF assms(1)], of 1 x] by simp

  ultimately show ?thesis using assms(2)
    using map_eq_conv by fastforce
qed


subsubsection\<open>Decomposition\<close>

inductive cycle_decomp :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
empty:  "cycle_decomp {} id" |
comp: "\<lbrakk> cycle_decomp I p; cycle cs; set cs \<inter> I = {} \<rbrakk> \<Longrightarrow>
         cycle_decomp (set cs \<union> I) ((cycle_of_list cs) \<circ> p)"


lemma semidecomposition:
  assumes "p permutes S" "finite S"
  shows "(\<lambda>y. if y \<in> (S - set (support p x)) then p y else y) permutes (S - set (support p x))"
    (is "?q permutes ?S'")
proof -
  have "\<And>y. y \<notin> S \<Longrightarrow> p y = y"
    by (meson assms permutes_not_in)

  moreover have cycle_surj: "(cycle_of_list (support p x)) ` set (support p x) = set (support p x)"
    using cycle_is_surj cycle_of_permutation assms permutation_permutes by metis
  hence "\<And>y. y \<in> set (support p x) \<Longrightarrow> p y \<in> set (support p x)"
    using cycle_restrict assms permutation_permutes by (metis imageI)

  ultimately
  have 1: "\<And>y. y \<notin> ?S' \<Longrightarrow> p y \<notin> ?S'" by auto
  have 2: "\<And>y. y \<in> ?S' \<Longrightarrow> p y \<in> ?S'"
  proof -
    fix y assume y: "y \<in> ?S'" show "p y \<in> ?S'"
    proof (rule ccontr)
      assume "p y \<notin> ?S'" hence "p y \<in> set (support p x)"
        using assms(1) permutes_in_image y by fastforce
      then obtain y' where y': "y' \<in> set (support p x)" "(cycle_of_list (support p x)) y' = p y"
        using cycle_surj by (metis (mono_tags, lifting) imageE)
      hence "p y' = p y"
        using cycle_restrict assms permutation_permutes by metis
      hence "y = y'" by (metis assms(1) permutes_def)
      thus False using y y' by blast
    qed
  qed
  
  have "p ` ?S' = ?S'"
  proof -
    have "\<And> y. y \<in> ?S' \<Longrightarrow> \<exists>!x. p x = y"
      by (metis assms(1) permutes_def)
    hence "\<And> y. y \<in> ?S' \<Longrightarrow> \<exists>x \<in> ?S'. p x = y" using 1 by metis
    thus ?thesis using 2 by blast
  qed
  hence "bij_betw p ?S' ?S'"
    by (metis DiffD1 assms(1) bij_betw_subset permutes_imp_bij subsetI)
  hence "bij_betw ?q ?S' ?S'"
    by (rule rev_iffD1 [OF _ bij_betw_cong]) auto
  moreover have "\<And>y. y \<notin> ?S' \<Longrightarrow> ?q y = y" by auto
  ultimately show ?thesis
    using bij_imp_permutes by blast 
qed


lemma cycle_decomposition_aux:
  assumes "p permutes S" "finite S" "card S = k"
  shows "cycle_decomp S p" using assms
proof(induct arbitrary: S p rule: less_induct)
  case (less x) thus ?case
  proof (cases "S = {}")
    case True thus ?thesis
      by (metis empty less.prems(1) permutes_empty) 
  next
    case False
    then obtain x where x: "x \<in> S" by blast
    define S' :: "'a set"   where S': "S' = S - set (support p x)"
    define q  :: "'a \<Rightarrow> 'a" where  q: "q  = (\<lambda>x. if x \<in> S' then p x else x)"
    hence q_permutes: "q permutes S'"
      using semidecomposition[OF less.prems(1-2), of x] S' q by blast
    moreover have "x \<in> set (support p x)"
      by (metis (no_types, lifting) add.left_neutral diff_zero funpow_0 in_set_conv_nth least_power_gt_zero
          length_map length_upt less.prems(1) less.prems(2) nth_map_upt permutation_permutes)
    hence "card S' < card S"
      by (metis Diff_iff S' \<open>x \<in> S\<close> card_seteq leI less.prems(2) subsetI)
    ultimately have "cycle_decomp S' q"
      using S' less.hyps less.prems(2) less.prems(3) by blast

    moreover have "p = (cycle_of_list (support p x)) \<circ> q"
    proof
      fix y show "p y = ((cycle_of_list (support p x)) \<circ> q) y"
      proof (cases)
        assume y: "y \<in> set (support p x)" hence "y \<notin> S'" using S' by simp
        hence "q y = y" using q by simp
        thus ?thesis
          using comp_apply cycle_restrict less.prems permutation_permutes y by fastforce
      next
        assume y: "y \<notin> set (support p x)" thus ?thesis
        proof (cases)
          assume "y \<in> S'"
          hence "q y \<in> S'" using q_permutes
            by (simp add: permutes_in_image)
          hence "q y \<notin> set (support p x)"
            using S' by blast
          hence "(cycle_of_list (support p x)) (q y) = (q y)"
            by (metis cycle_of_permutation id_outside_supp less.prems(1-2) permutation_permutes)
          thus ?thesis by (simp add: \<open>y \<in> S'\<close> q)
        next
          assume "y \<notin> S'" hence "y \<notin> S" using y S' by blast
          hence "(cycle_of_list (support p x) \<circ> q) y = (cycle_of_list (support p x)) y"
            by (simp add: \<open>y \<notin> S'\<close> q)
          also have " ... = y"
            by (metis cycle_of_permutation id_outside_supp less.prems(1-2) permutation_permutes y)
          also have " ... = p y"
            by (metis \<open>y \<notin> S\<close> less.prems(1) permutes_def)
          finally show ?thesis by simp
        qed
      qed
    qed
    moreover have "cycle (support p x)"
      using cycle_of_permutation less.prems permutation_permutes by fastforce
    moreover have "set (support p x) \<inter> S' = {}" using S' by simp
    moreover have "set (support p x) \<subseteq> S"
      using support_coverture[OF less.prems(1-2)] support_set[of p x] x
            permutation_permutes[of p] less.prems(1-2) by blast
    hence "S = set (support p x) \<union> S'" using S' by blast 
    ultimately show ?thesis using comp[of S' q "support p x"] by auto
  qed
qed

theorem cycle_decomposition:
  assumes "p permutes S" "finite S"
  shows "cycle_decomp S p"
  using assms cycle_decomposition_aux by blast

end
