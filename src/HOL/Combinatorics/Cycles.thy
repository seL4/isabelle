(*  Author:     Paulo Emílio de Vilhena
*)

theory Cycles
  imports
    "HOL-Library.FuncSet"
Permutations
begin

section \<open>Cycles\<close>

subsection \<open>Definitions\<close>

abbreviation cycle :: "'a list \<Rightarrow> bool"
  where "cycle cs \<equiv> distinct cs"

fun cycle_of_list :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a"
  where
    "cycle_of_list (i # j # cs) = transpose i j \<circ> cycle_of_list (j # cs)"
  | "cycle_of_list cs = id"


subsection \<open>Basic Properties\<close>

text \<open>We start proving that the function derived from a cycle rotates its support list.\<close>

lemma id_outside_supp:
  assumes "x \<notin> set cs" shows "(cycle_of_list cs) x = x"
  using assms by (induct cs rule: cycle_of_list.induct) (simp_all)

lemma permutation_of_cycle: "permutation (cycle_of_list cs)"
proof (induct cs rule: cycle_of_list.induct)
  case 1 thus ?case
    using permutation_compose[OF permutation_swap_id] unfolding comp_apply by simp
qed simp_all

lemma cycle_permutes: "(cycle_of_list cs) permutes (set cs)"
  using permutation_bijective[OF permutation_of_cycle] id_outside_supp[of _ cs]
  by (simp add: bij_iff permutes_def)

theorem cyclic_rotation:
  assumes "cycle cs" shows "map ((cycle_of_list cs) ^^ n) cs = rotate n cs"
proof -
  { have "map (cycle_of_list cs) cs = rotate1 cs" using assms(1)
    proof (induction cs rule: cycle_of_list.induct)
      case (1 i j cs)
      then have \<open>i \<notin> set cs\<close> \<open>j \<notin> set cs\<close>
        by auto
      then have \<open>map (Transposition.transpose i j) cs = cs\<close>
        by (auto intro: map_idI simp add: transpose_eq_iff)
      show ?case
      proof (cases)
        assume "cs = Nil" thus ?thesis by simp
      next
        assume "cs \<noteq> Nil" hence ge_two: "length (j # cs) \<ge> 2"
          using not_less by auto
        have "map (cycle_of_list (i # j # cs)) (i # j # cs) =
              map (transpose i j) (map (cycle_of_list (j # cs)) (i # j # cs))" by simp
        also have " ... = map (transpose i j) (i # (rotate1 (j # cs)))"
          by (metis "1.IH" "1.prems" distinct.simps(2) id_outside_supp list.simps(9))
        also have " ... = map (transpose i j) (i # (cs @ [j]))" by simp
        also have " ... = j # (map (transpose i j) cs) @ [i]" by simp
        also have " ... = j # cs @ [i]"
          using \<open>map (Transposition.transpose i j) cs = cs\<close> by simp
        also have " ... = rotate1 (i # j # cs)" by simp
        finally show ?thesis .
      qed
    qed simp_all }
  note cyclic_rotation' = this

  show ?thesis
    using cyclic_rotation' by (induct n) (auto, metis map_map rotate1_rotate_swap rotate_map)
qed

corollary cycle_is_surj:
  assumes "cycle cs" shows "(cycle_of_list cs) ` (set cs) = (set cs)"
  using cyclic_rotation[OF assms, of "Suc 0"] by (simp add: image_set)

corollary cycle_is_id_root:
  assumes "cycle cs" shows "(cycle_of_list cs) ^^ (length cs) = id"
proof -
  have "map ((cycle_of_list cs) ^^ (length cs)) cs = cs"
    unfolding cyclic_rotation[OF assms] by simp
  hence "((cycle_of_list cs) ^^ (length cs)) i = i" if "i \<in> set cs" for i
    using that map_eq_conv by fastforce
  moreover have "((cycle_of_list cs) ^^ n) i = i" if "i \<notin> set cs" for i n
    using id_outside_supp[OF that] by (induct n) (simp_all)
  ultimately show ?thesis
    by fastforce
qed

corollary cycle_of_list_rotate_independent:
  assumes "cycle cs" shows "(cycle_of_list cs) = (cycle_of_list (rotate n cs))"
proof -
  { fix cs :: "'a list" assume cs: "cycle cs"
    have "(cycle_of_list cs) = (cycle_of_list (rotate1 cs))"
    proof -
      from cs have rotate1_cs: "cycle (rotate1 cs)" by simp
      hence "map (cycle_of_list (rotate1 cs)) (rotate1 cs) = (rotate 2 cs)"
        using cyclic_rotation[OF rotate1_cs, of 1] by (simp add: numeral_2_eq_2)
      moreover have "map (cycle_of_list cs) (rotate1 cs) = (rotate 2 cs)"
        using cyclic_rotation[OF cs]
        by (metis One_nat_def Suc_1 funpow.simps(2) id_apply map_map rotate0 rotate_Suc)
      ultimately have "(cycle_of_list cs) i = (cycle_of_list (rotate1 cs)) i" if "i \<in> set cs" for i
        using that map_eq_conv unfolding sym[OF set_rotate1[of cs]] by fastforce  
      moreover have "(cycle_of_list cs) i = (cycle_of_list (rotate1 cs)) i" if "i \<notin> set cs" for i
        using that by (simp add: id_outside_supp)
      ultimately show "(cycle_of_list cs) = (cycle_of_list (rotate1 cs))"
        by blast
    qed } note rotate1_lemma = this

  show ?thesis
    using rotate1_lemma[of "rotate n cs"] by (induct n) (auto, metis assms distinct_rotate rotate1_lemma)
qed


subsection\<open>Conjugation of cycles\<close>

lemma conjugation_of_cycle:
  assumes "cycle cs" and "bij p"
  shows "p \<circ> (cycle_of_list cs) \<circ> (inv p) = cycle_of_list (map p cs)"
  using assms
proof (induction cs rule: cycle_of_list.induct)
  case (1 i j cs)
  have "p \<circ> cycle_of_list (i # j # cs) \<circ> inv p =
       (p \<circ> (transpose i j) \<circ> inv p) \<circ> (p \<circ> cycle_of_list (j # cs) \<circ> inv p)"
    by (simp add: assms(2) bij_is_inj fun.map_comp)
  also have " ... = (transpose (p i) (p j)) \<circ> (p \<circ> cycle_of_list (j # cs) \<circ> inv p)"
    using "1.prems"(2) by (simp add: bij_inv_eq_iff transpose_apply_commute fun_eq_iff bij_betw_inv_into_left)
  finally have "p \<circ> cycle_of_list (i # j # cs) \<circ> inv p =
               (transpose (p i) (p j)) \<circ> (cycle_of_list (map p (j # cs)))"
    using "1.IH" "1.prems"(1) assms(2) by fastforce
  thus ?case by (simp add: fun_eq_iff)
next
  case "2_1" thus ?case
    by (metis bij_is_surj comp_id cycle_of_list.simps(2) list.simps(8) surj_iff) 
next
  case "2_2" thus ?case
    by (metis bij_is_surj comp_id cycle_of_list.simps(3) list.simps(8) list.simps(9) surj_iff) 
qed


subsection\<open>When Cycles Commute\<close>

lemma cycles_commute:
  assumes "cycle p" "cycle q" and "set p \<inter> set q = {}"
  shows "(cycle_of_list p) \<circ> (cycle_of_list q) = (cycle_of_list q) \<circ> (cycle_of_list p)"
proof
  { fix p :: "'a list" and q :: "'a list" and i :: "'a"
    assume A: "cycle p" "cycle q" "set p \<inter> set q = {}" "i \<in> set p" "i \<notin> set q"
    have "((cycle_of_list p) \<circ> (cycle_of_list q)) i =
          ((cycle_of_list q) \<circ> (cycle_of_list p)) i"
    proof -
      have "((cycle_of_list p) \<circ> (cycle_of_list q)) i = (cycle_of_list p) i"
        using id_outside_supp[OF A(5)] by simp
      also have " ... = ((cycle_of_list q) \<circ> (cycle_of_list p)) i"
        using id_outside_supp[of "(cycle_of_list p) i"] cycle_is_surj[OF A(1)] A(3,4) by fastforce
      finally show ?thesis .
    qed } note aui_lemma = this

  fix i consider "i \<in> set p" "i \<notin> set q" | "i \<notin> set p" "i \<in> set q" | "i \<notin> set p" "i \<notin> set q"
    using \<open>set p \<inter> set q = {}\<close> by blast
  thus "((cycle_of_list p) \<circ> (cycle_of_list q)) i = ((cycle_of_list q) \<circ> (cycle_of_list p)) i"
  proof cases
    case 1 thus ?thesis
      using aui_lemma[OF assms] by simp
  next
    case 2 thus ?thesis
      using aui_lemma[OF assms(2,1)] assms(3) by (simp add: ac_simps)
  next
    case 3 thus ?thesis
      by (simp add: id_outside_supp)
  qed
qed


subsection \<open>Cycles from Permutations\<close>

subsubsection \<open>Exponentiation of permutations\<close>

text \<open>Some important properties of permutations before defining how to extract its cycles.\<close>

lemma permutation_funpow:
  assumes "permutation p" shows "permutation (p ^^ n)"
  using assms by (induct n) (simp_all add: permutation_compose)

lemma permutes_funpow:
  assumes "p permutes S" shows "(p ^^ n) permutes S"
  using assms by (induct n) (simp add: permutes_def, metis funpow_Suc_right permutes_compose)

lemma funpow_diff:
  assumes "inj p" and "i \<le> j" "(p ^^ i) a = (p ^^ j) a" shows "(p ^^ (j - i)) a = a"
proof -
  have "(p ^^ i) ((p ^^ (j - i)) a) = (p ^^ i) a"
    using assms(2-3) by (metis (no_types) add_diff_inverse_nat funpow_add not_le o_def)
  thus ?thesis
    unfolding inj_eq[OF inj_fn[OF assms(1)], of i] .
qed

lemma permutation_is_nilpotent:
  assumes "permutation p" obtains n where "(p ^^ n) = id" and "n > 0"
proof -
  obtain S where "finite S" and "p permutes S"
    using assms unfolding permutation_permutes by blast
  hence "\<exists>n. (p ^^ n) = id \<and> n > 0"
  proof (induct S arbitrary: p)
    case empty thus ?case
      using id_funpow[of 1] unfolding permutes_empty by blast
  next
    case (insert s S)
    have "(\<lambda>n. (p ^^ n) s) ` UNIV \<subseteq> (insert s S)"
      using permutes_in_image[OF permutes_funpow[OF insert(4)], of _ s] by auto
    hence "\<not> inj_on (\<lambda>n. (p ^^ n) s)  UNIV"
      using insert(1) infinite_iff_countable_subset unfolding sym[OF finite_insert, of S s] by metis
    then obtain i j where ij: "i < j" "(p ^^ i) s = (p ^^ j) s"
      unfolding inj_on_def by (metis nat_neq_iff) 
    hence "(p ^^ (j - i)) s = s"
      using funpow_diff[OF permutes_inj[OF insert(4)]] le_eq_less_or_eq by blast
    hence "p ^^ (j - i) permutes S"
      using permutes_superset[OF permutes_funpow[OF insert(4), of "j - i"], of S] by auto
    then obtain n where n: "((p ^^ (j - i)) ^^ n) = id" "n > 0"
      using insert(3) by blast
    thus ?case
      using ij(1) nat_0_less_mult_iff zero_less_diff unfolding funpow_mult by metis 
  qed
  thus thesis
    using that by blast
qed

lemma permutation_is_nilpotent':
  assumes "permutation p" obtains n where "(p ^^ n) = id" and "n > m"
proof -
  obtain n where "(p ^^ n) = id" and "n > 0"
    using permutation_is_nilpotent[OF assms] by blast
  then obtain k where "n * k > m"
    by (metis dividend_less_times_div mult_Suc_right)
  from \<open>(p ^^ n) = id\<close> have "p ^^ (n * k) = id"
    by (induct k) (simp, metis funpow_mult id_funpow)
  with \<open>n * k > m\<close> show thesis
    using that by blast
qed


subsubsection \<open>Extraction of cycles from permutations\<close>

definition least_power :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat"
  where "least_power f x = (LEAST n. (f ^^ n) x = x \<and> n > 0)"

abbreviation support :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "support p x \<equiv> map (\<lambda>i. (p ^^ i) x) [0..< (least_power p x)]"


lemma least_powerI:
  assumes "(f ^^ n) x = x" and "n > 0"
  shows "(f ^^ (least_power f x)) x = x" and "least_power f x > 0"
  using assms unfolding least_power_def by (metis (mono_tags, lifting) LeastI)+

lemma least_power_le:
  assumes "(f ^^ n) x = x" and "n > 0" shows "least_power f x \<le> n"
  using assms unfolding least_power_def by (simp add: Least_le)

lemma least_power_of_permutation:
  assumes "permutation p" shows "(p ^^ (least_power p a)) a = a" and "least_power p a > 0"
  using permutation_is_nilpotent[OF assms] least_powerI by (metis id_apply)+

lemma least_power_gt_one:
  assumes "permutation p" and "p a \<noteq> a" shows "least_power p a > Suc 0"
  using least_power_of_permutation[OF assms(1)] assms(2)
  by (metis Suc_lessI funpow.simps(2) funpow_simps_right(1) o_id) 

lemma least_power_minimal:
  assumes "(p ^^ n) a = a" shows "(least_power p a) dvd n"
proof (cases "n = 0", simp)
  let ?lpow = "least_power p"

  assume "n \<noteq> 0" then have "n > 0" by simp
  hence "(p ^^ (?lpow a)) a = a" and "least_power p a > 0"
    using assms unfolding least_power_def by (metis (mono_tags, lifting) LeastI)+
  hence aux_lemma: "(p ^^ ((?lpow a) * k)) a = a" for k :: nat
    by (induct k) (simp_all add: funpow_add)

  have "(p ^^ (n mod ?lpow a)) ((p ^^ (n - (n mod ?lpow a))) a) = (p ^^ n) a"
    by (metis add_diff_inverse_nat funpow_add mod_less_eq_dividend not_less o_apply)
  with \<open>(p ^^ n) a = a\<close> have "(p ^^ (n mod ?lpow a)) a = a"
    using aux_lemma by (simp add: minus_mod_eq_mult_div) 
  hence "?lpow a \<le> n mod ?lpow a" if "n mod ?lpow a > 0"
    using least_power_le[OF _ that, of p a] by simp
  with \<open>least_power p a > 0\<close> show "(least_power p a) dvd n"
    using mod_less_divisor not_le by blast
qed

lemma least_power_dvd:
  assumes "permutation p" shows "(least_power p a) dvd n \<longleftrightarrow> (p ^^ n) a = a"
proof
  show "(p ^^ n) a = a \<Longrightarrow> (least_power p a) dvd n"
    using least_power_minimal[of _ p] by simp
next
  have "(p ^^ ((least_power p a) * k)) a = a" for k :: nat
    using least_power_of_permutation(1)[OF assms(1)] by (induct k) (simp_all add: funpow_add)
  thus "(least_power p a) dvd n \<Longrightarrow> (p ^^ n) a = a" by blast
qed

theorem cycle_of_permutation:
  assumes "permutation p" shows "cycle (support p a)"
proof -
  have "(least_power p a) dvd (j - i)" if "i \<le> j" "j < least_power p a" and "(p ^^ i) a = (p ^^ j) a" for i j
    using funpow_diff[OF bij_is_inj that(1,3)] assms by (simp add: permutation least_power_dvd)
  moreover have "i = j" if "i \<le> j" "j < least_power p a" and "(least_power p a) dvd (j - i)" for i j
    using that le_eq_less_or_eq nat_dvd_not_less by auto
  ultimately have "inj_on (\<lambda>i. (p ^^ i) a) {..< (least_power p a)}"
    unfolding inj_on_def by (metis le_cases lessThan_iff)
  thus ?thesis
    by (simp add: atLeast_upt distinct_map)
qed


subsection \<open>Decomposition on Cycles\<close>

text \<open>We show that a permutation can be decomposed on cycles\<close>

subsubsection \<open>Preliminaries\<close>

lemma support_set:
  assumes "permutation p" shows "set (support p a) = range (\<lambda>i. (p ^^ i) a)"
proof
  show "set (support p a) \<subseteq> range (\<lambda>i. (p ^^ i) a)"
    by auto
next
  show "range (\<lambda>i. (p ^^ i) a) \<subseteq> set (support p a)"
  proof (auto)
    fix i
    have "(p ^^ i) a = (p ^^ (i mod (least_power p a))) ((p ^^ (i - (i mod (least_power p a)))) a)"
      by (metis add_diff_inverse_nat funpow_add mod_less_eq_dividend not_le o_apply)
    also have " ... = (p ^^ (i mod (least_power p a))) a"
      using least_power_dvd[OF assms] by (metis dvd_minus_mod)
    also have " ... \<in> (\<lambda>i. (p ^^ i) a) ` {0..< (least_power p a)}"
      using least_power_of_permutation(2)[OF assms] by fastforce
    finally show "(p ^^ i) a \<in> (\<lambda>i. (p ^^ i) a) ` {0..< (least_power p a)}" .
  qed
qed

lemma disjoint_support:
  assumes "permutation p" shows "disjoint (range (\<lambda>a. set (support p a)))" (is "disjoint ?A")
proof (rule disjointI)
  { fix i j a b
    assume "set (support p a) \<inter> set (support p b) \<noteq> {}" have "set (support p a) \<subseteq> set (support p b)"
      unfolding support_set[OF assms]
    proof (auto)
      from \<open>set (support p a) \<inter> set (support p b) \<noteq> {}\<close>
      obtain i j where ij: "(p ^^ i) a = (p ^^ j) b"
        by auto

      fix k
      have "(p ^^ k) a = (p ^^ (k + (least_power p a) * l)) a" for l
        using least_power_dvd[OF assms] by (induct l) (simp, metis dvd_triv_left funpow_add o_def)
      then obtain m where "m \<ge> i" and "(p ^^ m) a = (p ^^ k) a"
        using least_power_of_permutation(2)[OF assms]
        by (metis dividend_less_times_div le_eq_less_or_eq mult_Suc_right trans_less_add2)
      hence "(p ^^ m) a = (p ^^ (m - i)) ((p ^^ i) a)"
        by (metis Nat.le_imp_diff_is_add funpow_add o_apply)
      with \<open>(p ^^ m) a = (p ^^ k) a\<close> have "(p ^^ k) a = (p ^^ ((m - i) + j)) b"
        unfolding ij by (simp add: funpow_add)
      thus "(p ^^ k) a \<in> range (\<lambda>i. (p ^^ i) b)"
        by blast
    qed } note aux_lemma = this

  fix supp_a supp_b
  assume "supp_a \<in> ?A" and "supp_b \<in> ?A"
  then obtain a b where a: "supp_a = set (support p a)" and b: "supp_b = set (support p b)"
    by auto
  assume "supp_a \<noteq> supp_b" thus "supp_a \<inter> supp_b = {}"
    using aux_lemma unfolding a b by blast  
qed

lemma disjoint_support':
  assumes "permutation p"
  shows "set (support p a) \<inter> set (support p b) = {} \<longleftrightarrow> a \<notin> set (support p b)"
proof -
  have "a \<in> set (support p a)"
    using least_power_of_permutation(2)[OF assms] by force
  show ?thesis
  proof
    assume "set (support p a) \<inter> set (support p b) = {}"
    with \<open>a \<in> set (support p a)\<close> show "a \<notin> set (support p b)"
      by blast
  next
    assume "a \<notin> set (support p b)" show "set (support p a) \<inter> set (support p b) = {}"
    proof (rule ccontr)
      assume "set (support p a) \<inter> set (support p b) \<noteq> {}"
      hence "set (support p a) = set (support p b)"
        using disjoint_support[OF assms] by (meson UNIV_I disjoint_def image_iff)
      with \<open>a \<in> set (support p a)\<close> and \<open>a \<notin> set (support p b)\<close> show False
        by simp
    qed
  qed
qed

lemma support_coverture:
  assumes "permutation p" shows "\<Union> { set (support p a) | a. p a \<noteq> a } = { a. p a \<noteq> a }"
proof
  show "{ a. p a \<noteq> a } \<subseteq> \<Union> { set (support p a) | a. p a \<noteq> a }"
  proof
    fix a assume "a \<in> { a. p a \<noteq> a }"
    have "a \<in> set (support p a)"
      using least_power_of_permutation(2)[OF assms, of a] by force
    with \<open>a \<in> { a. p a \<noteq> a }\<close> show "a \<in> \<Union> { set (support p a) | a. p a \<noteq> a }"
      by blast
  qed
next
  show "\<Union> { set (support p a) | a. p a \<noteq> a } \<subseteq> { a. p a \<noteq> a }"
  proof
    fix b assume "b \<in> \<Union> { set (support p a) | a. p a \<noteq> a }"
    then obtain a i where "p a \<noteq> a" and "(p ^^ i) a = b"
      by auto
    have "p a = a" if "(p ^^ i) a = (p ^^ Suc i) a"
      using funpow_diff[OF bij_is_inj _ that] assms unfolding permutation by simp
    with \<open>p a \<noteq> a\<close> and \<open>(p ^^ i) a = b\<close> show "b \<in> { a. p a \<noteq> a }"
      by auto
  qed
qed

theorem cycle_restrict:
  assumes "permutation p" and "b \<in> set (support p a)" shows "p b = (cycle_of_list (support p a)) b"
proof -
  note least_power_props [simp] = least_power_of_permutation[OF assms(1)]

  have "map (cycle_of_list (support p a)) (support p a) = rotate1 (support p a)"
    using cyclic_rotation[OF cycle_of_permutation[OF assms(1)], of 1 a] by simp
  hence "map (cycle_of_list (support p a)) (support p a) = tl (support p a) @ [ a ]"
    by (simp add: hd_map rotate1_hd_tl)
  also have " ... = map p (support p a)"
  proof (rule nth_equalityI, auto)
    fix i assume "i < least_power p a" show "(tl (support p a) @ [a]) ! i = p ((p ^^ i) a)"
    proof (cases)
      assume i: "i = least_power p a - 1"
      hence "(tl (support p a) @ [ a ]) ! i = a"
        by (metis (no_types, lifting) diff_zero length_map length_tl length_upt nth_append_length)
      also have " ... = p ((p ^^ i) a)"
        by (metis (mono_tags, opaque_lifting) least_power_props i Suc_diff_1 funpow_simps_right(2) funpow_swap1 o_apply)
      finally show ?thesis .
    next
      assume "i \<noteq> least_power p a - 1"
      with \<open>i < least_power p a\<close> have "i < least_power p a - 1"
        by simp
      hence "(tl (support p a) @ [ a ]) ! i = (p ^^ (Suc i)) a"
        by (metis One_nat_def Suc_eq_plus1 add.commute length_map length_upt map_tl nth_append nth_map_upt tl_upt)
      thus ?thesis
        by simp
    qed
  qed
  finally have "map (cycle_of_list (support p a)) (support p a) = map p (support p a)" .
  thus ?thesis
    using assms(2) by auto
qed


subsubsection\<open>Decomposition\<close>

inductive cycle_decomp :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where
    empty:  "cycle_decomp {} id"
  | comp: "\<lbrakk> cycle_decomp I p; cycle cs; set cs \<inter> I = {} \<rbrakk> \<Longrightarrow>
             cycle_decomp (set cs \<union> I) ((cycle_of_list cs) \<circ> p)"


lemma semidecomposition:
  assumes "p permutes S" and "finite S"
  shows "(\<lambda>y. if y \<in> (S - set (support p a)) then p y else y) permutes (S - set (support p a))"
proof (rule bij_imp_permutes)
  show "(if b \<in> (S - set (support p a)) then p b else b) = b" if "b \<notin> S - set (support p a)" for b
    using that by auto
next
  have is_permutation: "permutation p"
    using assms unfolding permutation_permutes by blast

  let ?q = "\<lambda>y. if y \<in> (S - set (support p a)) then p y else y"
  show "bij_betw ?q (S - set (support p a)) (S - set (support p a))"
  proof (rule bij_betw_imageI)
    show "inj_on ?q (S - set (support p a))"
      using permutes_inj[OF assms(1)] unfolding inj_on_def by auto
  next
    have aux_lemma: "set (support p s) \<subseteq> (S - set (support p a))" if "s \<in> S - set (support p a)" for s
    proof -
      have "(p ^^ i) s \<in> S" for i
        using that unfolding permutes_in_image[OF permutes_funpow[OF assms(1)]] by simp
      thus ?thesis
        using that disjoint_support'[OF is_permutation, of s a] by auto
    qed
    have "(p ^^ 1) s \<in> set (support p s)" for s
      unfolding support_set[OF is_permutation] by blast
    hence "p s \<in> set (support p s)" for s
      by simp
    hence "p ` (S - set (support p a)) \<subseteq> S - set (support p a)"
      using aux_lemma by blast
    moreover have "(p ^^ ((least_power p s) - 1)) s \<in> set (support p s)" for s
      unfolding support_set[OF is_permutation] by blast
    hence "\<exists>s' \<in> set (support p s). p s' = s" for s
      using least_power_of_permutation[OF is_permutation] by (metis Suc_diff_1 funpow.simps(2) o_apply)
    hence "S - set (support p a) \<subseteq> p ` (S - set (support p a))"
      using aux_lemma
      by (clarsimp simp add: image_iff) (metis image_subset_iff)
    ultimately show "?q ` (S - set (support p a)) = (S - set (support p a))"
      by auto
  qed
qed

theorem cycle_decomposition:
  assumes "p permutes S" and "finite S" shows "cycle_decomp S p"
  using assms
proof(induct "card S" arbitrary: S p rule: less_induct)
  case less show ?case
  proof (cases)
    assume "S = {}" thus ?thesis
      using empty less(2) by auto
  next
    have is_permutation: "permutation p"
      using less(2-3) unfolding permutation_permutes by blast

    assume "S \<noteq> {}" then obtain s where "s \<in> S"
      by blast
    define q where "q = (\<lambda>y. if y \<in> (S - set (support p s)) then p y else y)"
    have "(cycle_of_list (support p s) \<circ> q) = p"
    proof
      fix a
      consider "a \<in> S - set (support p s)" | "a \<in> set (support p s)" | "a \<notin> S" "a \<notin> set (support p s)"
        by blast
      thus "((cycle_of_list (support p s) \<circ> q)) a = p a"
      proof cases
        case 1
        have "(p ^^ 1) a \<in> set (support p a)"
          unfolding support_set[OF is_permutation] by blast
        with \<open>a \<in> S - set (support p s)\<close> have "p a \<notin> set (support p s)"
          using disjoint_support'[OF is_permutation, of a s] by auto
        with \<open>a \<in> S - set (support p s)\<close> show ?thesis
          using id_outside_supp[of _ "support p s"] unfolding q_def by simp
      next
        case 2 thus ?thesis
          using cycle_restrict[OF is_permutation] unfolding q_def by simp
      next
        case 3 thus ?thesis
          using id_outside_supp[OF 3(2)] less(2) permutes_not_in unfolding q_def by fastforce
      qed
    qed

    moreover from \<open>s \<in> S\<close> have "(p ^^ i) s \<in> S" for i
      unfolding permutes_in_image[OF permutes_funpow[OF less(2)]] .
    hence "set (support p s) \<union> (S - set (support p s)) = S"
      by auto

    moreover have "s \<in> set (support p s)"
      using least_power_of_permutation[OF is_permutation] by force
    with \<open>s \<in> S\<close> have "card (S - set (support p s)) < card S"
      using less(3) by (metis DiffE card_seteq linorder_not_le subsetI)
    hence "cycle_decomp (S - set (support p s)) q"
      using less(1)[OF _ semidecomposition[OF less(2-3)], of s] less(3) unfolding q_def by blast

    moreover show ?thesis
      using comp[OF calculation(3) cycle_of_permutation[OF is_permutation], of s]
      unfolding calculation(1-2) by blast  
  qed
qed

end
