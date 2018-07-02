(* ************************************************************************** *)
(* Title:      Polynomials.thy                                                *)
(* Author:     Paulo Emílio de Vilhena                                        *)
(* ************************************************************************** *)

theory Polynomials
  imports Ring Ring_Divisibility Subrings

begin

section \<open>Polynomials\<close>

subsection \<open>Definitions\<close>

abbreviation lead_coeff :: "'a list \<Rightarrow> 'a"
  where "lead_coeff \<equiv> hd"

definition degree :: "'a list \<Rightarrow> nat"
  where "degree p = length p - 1"

definition polynomial :: "_ \<Rightarrow> 'a list \<Rightarrow> bool"
  where "polynomial R p \<longleftrightarrow> p = [] \<or> (set p \<subseteq> carrier R \<and> lead_coeff p \<noteq> \<zero>\<^bsub>R\<^esub>)"

definition (in ring) monon :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"
  where "monon a n = a # (replicate n \<zero>\<^bsub>R\<^esub>)"

fun (in ring) eval :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a"
  where
    "eval [] = (\<lambda>_. \<zero>)"
  | "eval p = (\<lambda>x. ((lead_coeff p) \<otimes> (x [^] (degree p))) \<oplus> (eval (tl p) x))"

fun (in ring) coeff :: "'a list \<Rightarrow> nat \<Rightarrow> 'a"
  where
    "coeff [] = (\<lambda>_. \<zero>)"
  | "coeff p = (\<lambda>i. if i = degree p then lead_coeff p else (coeff (tl p)) i)"

fun (in ring) normalize :: "'a list \<Rightarrow> 'a list"
  where
    "normalize [] = []"
  | "normalize p = (if lead_coeff p \<noteq> \<zero> then p else normalize (tl p))"

fun (in ring) poly_add :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "poly_add p1 p2 =
           (if length p1 \<ge> length p2
            then normalize (map2 (\<oplus>) p1 ((replicate (length p1 - length p2) \<zero>) @ p2))
            else poly_add p2 p1)"

fun (in ring) poly_mult :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "poly_mult [] p2 = []"
  | "poly_mult p1 p2 =
       poly_add ((map (\<lambda>a. lead_coeff p1 \<otimes> a) p2) @ (replicate (degree p1) \<zero>)) (poly_mult (tl p1) p2)"

fun (in ring) dense_repr :: "'a list \<Rightarrow> ('a \<times> nat) list"
  where
    "dense_repr [] = []"
  | "dense_repr p = (if lead_coeff p \<noteq> \<zero>
                     then (lead_coeff p, degree p) # (dense_repr (tl p))
                     else (dense_repr (tl p)))"

fun (in ring) of_dense :: "('a \<times> nat) list \<Rightarrow> 'a list"
  where "of_dense dl = foldr (\<lambda>(a, n) l. poly_add (monon a n) l) dl []"


subsection \<open>Basic Properties\<close>

context ring
begin

lemma polynomialI [intro]: "\<lbrakk> set p \<subseteq> carrier R; lead_coeff p \<noteq> \<zero> \<rbrakk> \<Longrightarrow> polynomial R p"
  unfolding polynomial_def by auto

lemma polynomial_in_carrier [intro]: "polynomial R p \<Longrightarrow> set p \<subseteq> carrier R"
  unfolding polynomial_def by auto

lemma lead_coeff_not_zero [intro]: "polynomial R (a # p) \<Longrightarrow> a \<in> carrier R - { \<zero> }"
  unfolding polynomial_def by simp

lemma zero_is_polynomial [intro]: "polynomial R []"
  unfolding polynomial_def by simp

lemma const_is_polynomial [intro]: "a \<in> carrier R - { \<zero> } \<Longrightarrow> polynomial R [ a ]"
  unfolding polynomial_def by auto

lemma monon_is_polynomial [intro]: "a \<in> carrier R - { \<zero> } \<Longrightarrow> polynomial R (monon a n)"
  unfolding polynomial_def monon_def by auto

lemma monon_in_carrier [intro]: "a \<in> carrier R \<Longrightarrow> set (monon a n) \<subseteq> carrier R"
  unfolding monon_def by auto

lemma normalize_gives_polynomial: "set p \<subseteq> carrier R \<Longrightarrow> polynomial R (normalize p)"
  by (induction p) (auto simp add: polynomial_def)

lemma normalize_in_carrier: "set p \<subseteq> carrier R \<Longrightarrow> set (normalize p) \<subseteq> carrier R"
  using normalize_gives_polynomial polynomial_in_carrier by simp

lemma normalize_idem: "polynomial R p \<Longrightarrow> normalize p = p"
  unfolding polynomial_def by (cases p) (auto)

lemma normalize_length_le: "length (normalize p) \<le> length p"
  by (induction p) (auto)

lemma eval_in_carrier: "\<lbrakk> set p \<subseteq> carrier R; x \<in> carrier R \<rbrakk> \<Longrightarrow> (eval p) x \<in> carrier R"
  by (induction p) (auto)

lemma eval_poly_in_carrier: "\<lbrakk> polynomial R p; x \<in> carrier R \<rbrakk> \<Longrightarrow> (eval p) x \<in> carrier R"
  using eval_in_carrier unfolding polynomial_def by auto

lemma coeff_in_carrier [simp]: "set p \<subseteq> carrier R \<Longrightarrow> (coeff p) i \<in> carrier R"
  by (induction p) (auto)

lemma poly_coeff_in_carrier [simp]: "polynomial R p \<Longrightarrow> coeff p i \<in> carrier R"
  using coeff_in_carrier unfolding polynomial_def by auto

lemma lead_coeff_simp [simp]: "p \<noteq> [] \<Longrightarrow> (coeff p) (degree p) = lead_coeff p"
  by (metis coeff.simps(2) list.exhaust_sel)

lemma coeff_list: "map (coeff p) (rev [0..< length p]) = p"
proof (induction p)
  case Nil thus ?case by simp
next
  case (Cons a p)
  have "map (coeff (a # p)) (rev [0..<length (a # p)]) =
        map (coeff (a # p)) ((length p) # (rev [0..<length p]))"
    by simp
  also have " ... = a # (map (coeff p) (rev [0..<length p]))"
    using degree_def[of "a # p"] by auto
  also have " ... = a # p"
    using Cons by simp
  finally show ?case . 
qed

lemma coeff_nth: "i < length p \<Longrightarrow> (coeff p) i = p ! (length p - 1 - i)"
proof -
  assume i_lt: "i < length p"
  hence "(coeff p) i = (map (coeff p) [0..< length p]) ! i"
    by simp
  also have " ... = (rev (map (coeff p) (rev [0..< length p]))) ! i"
    by (simp add: rev_map)
  also have " ... = (map (coeff p) (rev [0..< length p])) ! (length p - 1 - i)"
    using coeff_list i_lt rev_nth by auto
  also have " ... = p ! (length p - 1 - i)"
    using coeff_list[of p] by simp
  finally show "(coeff p) i = p ! (length p - 1 - i)" .
qed

lemma coeff_iff_length_cond:
  assumes "length p1 = length p2"
  shows "p1 = p2 \<longleftrightarrow> coeff p1 = coeff p2"
proof
  show "p1 = p2 \<Longrightarrow> coeff p1 = coeff p2"
    by simp
next
  assume A: "coeff p1 = coeff p2"
  have "p1 = map (coeff p1) (rev [0..< length p1])"
    using coeff_list[of p1] by simp
  also have " ... = map (coeff p2) (rev [0..< length p2])"
    using A assms by simp
  also have " ... = p2"
    using coeff_list[of p2] by simp
  finally show "p1 = p2" .
qed

lemma coeff_img_restrict: "(coeff p) ` {..< length p} = set p"
  using coeff_list[of p] by (metis atLeast_upt image_set set_rev)

lemma coeff_length: "\<And>i. i \<ge> length p \<Longrightarrow> (coeff p) i = \<zero>"
  by (induction p) (auto simp add: degree_def)

lemma coeff_degree: "\<And>i. i > degree p \<Longrightarrow> (coeff p) i = \<zero>"
  using coeff_length by (simp add: degree_def)

lemma replicate_zero_coeff [simp]: "coeff (replicate n \<zero>) = (\<lambda>_. \<zero>)"
  by (induction n) (auto)

lemma scalar_coeff: "a \<in> carrier R \<Longrightarrow> coeff (map (\<lambda>b. a \<otimes> b) p) = (\<lambda>i. a \<otimes> (coeff p) i)"
  by (induction p) (auto simp add:degree_def)

lemma monon_coeff: "coeff (monon a n) = (\<lambda>i. if i = n then a else \<zero>)"
  unfolding monon_def by (induction n) (auto simp add: degree_def)

lemma coeff_img:
  "(coeff p) ` {..< length p} = set p"
  "(coeff p) ` { length p ..} = { \<zero> }"
  "(coeff p) ` UNIV = (set p) \<union> { \<zero> }"
  using coeff_img_restrict
proof (simp)
  show coeff_img_up: "(coeff p) ` { length p ..} = { \<zero> }"
    using coeff_length[of p] unfolding degree_def by force
  from coeff_img_up and coeff_img_restrict[of p]
  show "(coeff p) ` UNIV = (set p) \<union> { \<zero> }"
    by force
qed

lemma degree_def':
  assumes "polynomial R p"
  shows "degree p = (LEAST n. \<forall>i. i > n \<longrightarrow> (coeff p) i = \<zero>)"
proof (cases p)
  case Nil thus ?thesis
    unfolding degree_def by auto
next
  define P where "P = (\<lambda>n. \<forall>i. i > n \<longrightarrow> (coeff p) i = \<zero>)"

  case (Cons a ps)
  hence "(coeff p) (degree p) \<noteq> \<zero>"
    using assms unfolding polynomial_def by auto
  hence "\<And>n. n < degree p \<Longrightarrow> \<not> P n"
    unfolding P_def by auto
  moreover have "P (degree p)"
    unfolding P_def using coeff_degree[of p] by simp
  ultimately have "degree p = (LEAST n. P n)"
    by (meson LeastI nat_neq_iff not_less_Least)
  thus ?thesis unfolding P_def .
qed

lemma coeff_iff_polynomial_cond:
  assumes "polynomial R p1" and "polynomial R p2"
  shows "p1 = p2 \<longleftrightarrow> coeff p1 = coeff p2"
proof
  show "p1 = p2 \<Longrightarrow> coeff p1 = coeff p2"
    by simp
next
  assume coeff_eq: "coeff p1 = coeff p2"
  hence deg_eq: "degree p1 = degree p2"
    using degree_def'[OF assms(1)] degree_def'[OF assms(2)] by auto
  thus "p1 = p2"
  proof (cases)
    assume "p1 \<noteq> [] \<and> p2 \<noteq> []"
    hence "length p1 = length p2"
      using deg_eq unfolding degree_def
      by (simp add: Nitpick.size_list_simp(2)) 
    thus ?thesis
      using coeff_iff_length_cond[of p1 p2] coeff_eq by simp
  next
    { fix p1 p2 assume A: "p1 = []" "coeff p1 = coeff p2" "polynomial R p2"
      have "p2 = []"
      proof (rule ccontr)
        assume "p2 \<noteq> []"
        hence "(coeff p2) (degree p2) \<noteq> \<zero>"
          using A(3) unfolding polynomial_def
          by (metis coeff.simps(2) list.collapse)
        moreover have "(coeff p1) ` UNIV = { \<zero> }"
          using A(1) by auto
        hence "(coeff p2) ` UNIV = { \<zero> }"
          using A(2) by simp
        ultimately show False
          by blast
      qed } note aux_lemma = this
    assume "\<not> (p1 \<noteq> [] \<and> p2 \<noteq> [])"
    hence "p1 = [] \<or> p2 = []" by simp
    thus ?thesis
      using assms coeff_eq aux_lemma[of p1 p2] aux_lemma[of p2 p1] by auto
  qed
qed

lemma normalize_lead_coeff:
  assumes "length (normalize p) < length p"
  shows "lead_coeff p = \<zero>"
proof (cases p)
  case Nil thus ?thesis
    using assms by simp
next
  case (Cons a ps) thus ?thesis
    using assms by (cases "a = \<zero>") (auto)
qed

lemma normalize_length_lt:
  assumes "lead_coeff p = \<zero>" and "length p > 0"
  shows "length (normalize p) < length p"
proof (cases p)
  case Nil thus ?thesis
    using assms by simp
next
  case (Cons a ps) thus ?thesis
    using normalize_length_le[of ps] assms by simp
qed

lemma normalize_length_eq:
  assumes "lead_coeff p \<noteq> \<zero>"
  shows "length (normalize p) = length p"
  using normalize_length_le[of p] assms nat_less_le normalize_lead_coeff by auto

lemma normalize_replicate_zero: "normalize ((replicate n \<zero>) @ p) = normalize p"
  by (induction n) (auto)

lemma normalize_def':
  shows   "p = (replicate (length p - length (normalize p)) \<zero>) @
                    (drop (length p - length (normalize p)) p)" (is ?statement1)
  and "normalize p = drop (length p - length (normalize p)) p"  (is ?statement2)
proof -
  show ?statement1
  proof (induction p)
    case Nil thus ?case by simp
  next
    case (Cons a p) thus ?case
    proof (cases "a = \<zero>")
      assume "a \<noteq> \<zero>" thus ?case
        using Cons by simp
    next
      assume eq_zero: "a = \<zero>"
      hence len_eq:
        "Suc (length p - length (normalize p)) = length (a # p) - length (normalize (a # p))"
        by (simp add: Suc_diff_le normalize_length_le)
      have "a # p = \<zero> # (replicate (length p - length (normalize p)) \<zero> @
                              drop (length p - length (normalize p)) p)"
        using eq_zero Cons by simp
      also have " ... = (replicate (Suc (length p - length (normalize p))) \<zero> @
                              drop (Suc (length p - length (normalize p))) (a # p))"
        by simp
      also have " ... = (replicate (length (a # p) - length (normalize (a # p))) \<zero> @
                              drop (length (a # p) - length (normalize (a # p))) (a # p))"
        using len_eq by simp
      finally show ?case .
    qed
  qed
next
  show ?statement2
  proof -
    have "\<exists>m. normalize p = drop m p"
    proof (induction p)
      case Nil thus ?case by simp
    next
      case (Cons a p) thus ?case
        apply (cases "a = \<zero>")
        apply (auto)
        apply (metis drop_Suc_Cons)
        apply (metis drop0)
        done
    qed
    then obtain m where m: "normalize p = drop m p" by auto
    hence "length (normalize p) = length p - m" by simp
    thus ?thesis
      using m by (metis rev_drop rev_rev_ident take_rev)
  qed
qed

lemma normalize_coeff: "coeff p = coeff (normalize p)"
proof (induction p)
  case Nil thus ?case by simp
next
  case (Cons a p)
  have "coeff (normalize p) (length p) = \<zero>"
    using normalize_length_le[of p] coeff_degree[of "normalize p"] unfolding degree_def
    by (metis One_nat_def coeff.simps(1) diff_less length_0_conv
        less_imp_diff_less nat_neq_iff neq0_conv not_le zero_less_Suc)
  then show ?case
    using Cons by (cases "a = \<zero>") (auto simp add: degree_def)
qed

lemma append_coeff:
  "coeff (p @ q) = (\<lambda>i. if i < length q then (coeff q) i else (coeff p) (i - length q))"
proof (induction p)
  case Nil thus ?case
    using coeff_length[of q] by auto
next
  case (Cons a p)
  have "coeff ((a # p) @ q) = (\<lambda>i. if i = length p + length q then a else (coeff (p @ q)) i)"
    by (auto simp add: degree_def)
  also have " ... = (\<lambda>i. if i = length p + length q then a
                         else if i < length q then (coeff q) i
                         else (coeff p) (i - length q))"
    using Cons by auto
  also have " ... = (\<lambda>i. if i < length q then (coeff q) i
                         else if i = length p + length q then a else (coeff p) (i - length q))"
    by auto
  also have " ... = (\<lambda>i. if i < length q then (coeff q) i
                         else if i - length q = length p then a else (coeff p) (i - length q))"
    by fastforce
  also have " ... = (\<lambda>i. if i < length q then (coeff q) i else (coeff (a # p)) (i - length q))"
    by (auto simp add: degree_def)
  finally show ?case .
qed

lemma prefix_replicate_zero_coeff: "coeff p = coeff ((replicate n \<zero>) @ p)"
  using append_coeff[of "replicate n \<zero>" p] replicate_zero_coeff[of n] coeff_length[of p] by auto

end


subsection \<open>Polynomial addition\<close>

context ring
begin

lemma poly_add_is_polynomial:
  assumes "set p1 \<subseteq> carrier R" and "set p2 \<subseteq> carrier R"
  shows "polynomial R (poly_add p1 p2)"
proof -
  { fix p1 p2 assume A: "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "length p1 \<ge> length p2"
    hence "polynomial R (poly_add p1 p2)"
    proof -
      define p2' where "p2' = (replicate (length p1 - length p2) \<zero>) @ p2"
      hence set_p2': "set p2' \<subseteq> carrier R"
        using A(2) by auto
      have "set (map (\<lambda>(a, b). a \<oplus> b) (zip p1 p2')) \<subseteq> carrier R"
      proof
        fix c assume "c \<in> set (map (\<lambda>(a, b). a \<oplus> b) (zip p1 p2'))"
        then obtain t where "t \<in> set (zip p1 p2')" and c: "c = fst t \<oplus> snd t"
          by auto
        then obtain a b where "a \<in> set p1"  "a = fst t"
                          and "b \<in> set p2'" "b = snd t"
          by (metis set_zip_leftD set_zip_rightD surjective_pairing)
        thus "c \<in> carrier R"
          using A(1) set_p2' c by auto
      qed
      thus ?thesis
        unfolding p2'_def using normalize_gives_polynomial A(3) by simp
    qed }
  thus ?thesis
    using assms by simp
qed

lemma poly_add_in_carrier:
  "\<lbrakk> set p1 \<subseteq> carrier R; set p2 \<subseteq> carrier R \<rbrakk> \<Longrightarrow> set (poly_add p1 p2) \<subseteq> carrier R"
  using poly_add_is_polynomial polynomial_in_carrier by simp

lemma poly_add_closed: "\<lbrakk> polynomial R p1; polynomial R p2 \<rbrakk> \<Longrightarrow> polynomial R (poly_add p1 p2)"
  using poly_add_is_polynomial polynomial_in_carrier by auto

lemma poly_add_length_le: "length (poly_add p1 p2) \<le> max (length p1) (length p2)"
proof -
  { fix p1 p2 :: "'a list" assume A: "length p1 \<ge> length p2"
    hence "length (poly_add p1 p2) \<le> max (length p1) (length p2)"
    proof -
      let ?p2 = "(replicate (length p1 - length p2) \<zero>) @ p2"
      have "length (map2 (\<oplus>) p1 ?p2) = length p1"
        using A by auto
      thus ?thesis
        using normalize_length_le[of "map2 (\<oplus>) p1 ?p2"] A by auto
    qed }
  thus ?thesis
    by (metis le_cases max.commute poly_add.simps)
qed

lemma poly_add_length_eq:
  assumes "polynomial R p1" "polynomial R p2" and "length p1 \<noteq> length p2"
  shows "length (poly_add p1 p2) = max (length p1) (length p2)"
proof -
  { fix p1 p2 assume A: "polynomial R p1" "polynomial R p2" "length p1 > length p2"
    hence "length (poly_add p1 p2) = max (length p1) (length p2)"
    proof -
      let ?p2 = "(replicate (length p1 - length p2) \<zero>) @ p2"
      have p1: "p1 \<noteq> []" and p2: "?p2 \<noteq> []"
        using A(3) by auto
      hence "lead_coeff (map2 (\<oplus>) p1 ?p2) = lead_coeff p1 \<oplus> lead_coeff ?p2"
        by (smt case_prod_conv list.exhaust_sel list.map(2) list.sel(1) zip_Cons_Cons)
      moreover have "lead_coeff p1 \<in> carrier R"
        using p1 A(1) unfolding polynomial_def by auto
      ultimately have "lead_coeff (map2 (\<oplus>) p1 ?p2) = lead_coeff p1"
        using A(3) by auto
      moreover have "lead_coeff p1 \<noteq> \<zero>"
        using p1 A(1) unfolding polynomial_def by simp
      ultimately have "length (normalize (map2 (\<oplus>) p1 ?p2)) = length p1"
        using normalize_length_eq by auto
      thus ?thesis
        using A(3) by auto
    qed }
  thus ?thesis
    using assms by auto
qed

lemma poly_add_degree: "degree (poly_add p1 p2) \<le> max (degree p1) (degree p2)"
  unfolding degree_def using poly_add_length_le
  by (meson diff_le_mono le_max_iff_disj)

lemma poly_add_degree_eq:
  assumes "polynomial R p1" "polynomial R p2" and "degree p1 \<noteq> degree p2"
  shows "degree (poly_add p1 p2) = max (degree p1) (degree p2)"
  using poly_add_length_eq[of p1 p2] assms
  by (smt degree_def diff_le_mono le_cases max.absorb1 max_def)

lemma poly_add_coeff_aux:
  assumes "length p1 \<ge> length p2"
  shows "coeff (poly_add p1 p2) = (\<lambda>i. ((coeff p1) i) \<oplus> ((coeff p2) i))"
proof
  fix i
  have "i < length p1 \<Longrightarrow> (coeff (poly_add p1 p2)) i = ((coeff p1) i) \<oplus> ((coeff p2) i)"
  proof -
    let ?p2 = "(replicate (length p1 - length p2) \<zero>) @ p2"
    have len_eqs: "length p1 = length ?p2" "length (map2 (\<oplus>) p1 ?p2) = length p1"
      using assms by auto
    assume i_lt: "i < length p1"
    have "(coeff (poly_add p1 p2)) i = (coeff (map2 (\<oplus>) p1 ?p2)) i"
      using normalize_coeff[of "map2 (\<oplus>) p1 ?p2"] assms by auto
    also have " ... = (map2 (\<oplus>) p1 ?p2) ! (length p1 - 1 - i)"
      using coeff_nth[of i "map2 (\<oplus>) p1 ?p2"] len_eqs(2) i_lt by auto
    also have " ... = (p1 ! (length p1 - 1 - i)) \<oplus> (?p2 ! (length ?p2 - 1 - i))"
      using len_eqs i_lt by auto
    also have " ... = ((coeff p1) i) \<oplus> ((coeff ?p2) i)"
      using coeff_nth[of i p1] coeff_nth[of i ?p2] i_lt len_eqs(1) by auto
    also have " ... = ((coeff p1) i) \<oplus> ((coeff p2) i)"
      using prefix_replicate_zero_coeff by simp
    finally show "(coeff (poly_add p1 p2)) i = ((coeff p1) i) \<oplus> ((coeff p2) i)" .
  qed
  moreover
  have "i \<ge> length p1 \<Longrightarrow> (coeff (poly_add p1 p2)) i = ((coeff p1) i) \<oplus> ((coeff p2) i)"
    using coeff_length[of "poly_add p1 p2"] coeff_length[of p1] coeff_length[of p2]
          poly_add_length_le[of p1 p2] assms by auto
  ultimately show "(coeff (poly_add p1 p2)) i = ((coeff p1) i) \<oplus> ((coeff p2) i)"
    using not_le by blast
qed

lemma poly_add_coeff:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "coeff (poly_add p1 p2) = (\<lambda>i. ((coeff p1) i) \<oplus> ((coeff p2) i))"
proof -
  have "length p1 \<ge> length p2 \<or> length p2 > length p1"
    by auto
  thus ?thesis
  proof
    assume "length p1 \<ge> length p2" thus ?thesis
      using poly_add_coeff_aux by simp
  next
    assume "length p2 > length p1"
    hence "coeff (poly_add p1 p2) = (\<lambda>i. ((coeff p2) i) \<oplus> ((coeff p1) i))"
      using poly_add_coeff_aux by simp
    thus ?thesis
      using assms by (simp add: add.m_comm)
  qed
qed

lemma poly_add_comm:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_add p1 p2 = poly_add p2 p1"
proof -
  have "coeff (poly_add p1 p2) = coeff (poly_add p2 p1)"
    using poly_add_coeff[OF assms] poly_add_coeff[OF assms(2) assms(1)]
          coeff_in_carrier[OF assms(1)] coeff_in_carrier[OF assms(2)] add.m_comm by auto
  thus ?thesis
    using coeff_iff_polynomial_cond poly_add_is_polynomial assms by auto
qed

lemma poly_add_monon:
  assumes "set p \<subseteq> carrier R" and "a \<in> carrier R - { \<zero> }"
  shows "poly_add (monon a (length p)) p = a # p"
  unfolding monon_def using assms by (induction p) (auto)

lemma poly_add_normalize_aux:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_add p1 p2 = poly_add (normalize p1) p2"
proof -
  { fix n p1 p2 assume "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
    hence "poly_add p1 p2 = poly_add ((replicate n \<zero>) @ p1) p2"
    proof (induction n)
      case 0 thus ?case by simp
    next
      { fix p1 p2 :: "'a list"
        assume in_carrier: "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
        have "poly_add p1 p2 = poly_add (\<zero> # p1) p2"
        proof -
          have "length p1 \<ge> length p2 \<Longrightarrow> ?thesis"
          proof -
            assume A: "length p1 \<ge> length p2"
            let ?p2 = "\<lambda>n. (replicate n \<zero>) @ p2"
            have "poly_add p1 p2 = normalize (map2 (\<oplus>) (\<zero> # p1) (\<zero> # ?p2 (length p1 - length p2)))"
              using A by simp
            also have " ... = normalize (map2 (\<oplus>) (\<zero> # p1) (?p2 (length (\<zero> # p1) - length p2)))"
              by (simp add: A Suc_diff_le)
            also have " ... = poly_add (\<zero> # p1) p2"
              using A by simp
            finally show ?thesis .
          qed

          moreover have "length p2 > length p1 \<Longrightarrow> ?thesis"
          proof -
            assume A: "length p2 > length p1"
            let ?f = "\<lambda>n p. (replicate n \<zero>) @ p"
            have "poly_add p1 p2 = poly_add p2 p1"
              using A by simp
            also have " ... = normalize (map2 (\<oplus>) p2 (?f (length p2 - length p1) p1))"
              using A by simp
            also have " ... = normalize (map2 (\<oplus>) p2 (?f (length p2 - Suc (length p1)) (\<zero> # p1)))"
              by (metis A Suc_diff_Suc append_Cons replicate_Suc replicate_app_Cons_same)
            also have " ... = poly_add p2 (\<zero> # p1)"
              using A by simp
            also have " ... = poly_add (\<zero> # p1) p2"
              using poly_add_comm[of p2 "\<zero> # p1"] in_carrier by auto
            finally show ?thesis .
          qed

          ultimately show ?thesis by auto
        qed } note aux_lemma = this

      case (Suc n)
      hence in_carrier: "set (replicate n \<zero> @ p1) \<subseteq> carrier R"
        by auto
      have "poly_add p1 p2 = poly_add (replicate n \<zero> @ p1) p2"
        using Suc by simp
      also have " ... = poly_add (replicate (Suc n) \<zero> @ p1) p2"
        using aux_lemma[OF in_carrier Suc(3)] by simp
      finally show ?case .
    qed } note aux_lemma = this

  have "poly_add p1 p2 =
        poly_add ((replicate (length p1 - length (normalize p1)) \<zero>) @ normalize p1) p2"
    using normalize_def'[of p1] by simp
  also have " ... = poly_add (normalize p1) p2"
    using aux_lemma[OF
          polynomial_in_carrier[OF normalize_gives_polynomial[OF assms(1)]] assms(2)] by simp
  finally show ?thesis .
qed

lemma poly_add_normalize:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_add p1 p2 = poly_add (normalize p1) p2"
    and "poly_add p1 p2 = poly_add p1 (normalize p2)"
    and "poly_add p1 p2 = poly_add (normalize p1) (normalize p2)"
proof -
  show "poly_add p1 p2 = poly_add p1 (normalize p2)"
    using poly_add_normalize_aux[OF assms(2) assms(1)] poly_add_comm
      polynomial_in_carrier normalize_gives_polynomial assms by auto
next
  show "poly_add p1 p2 = poly_add (normalize p1) p2"
    using poly_add_normalize_aux[OF assms] by simp
  also have " ... = poly_add p2 (normalize p1)"
    using poly_add_comm polynomial_in_carrier normalize_gives_polynomial assms by auto
  also have " ... = poly_add (normalize p2) (normalize p1)"
    using poly_add_normalize_aux polynomial_in_carrier normalize_gives_polynomial assms by auto
  also have " ... = poly_add (normalize p1) (normalize p2)"
    using poly_add_comm polynomial_in_carrier normalize_gives_polynomial assms by auto
  finally show "poly_add p1 p2 = poly_add (normalize p1) (normalize p2)" .
qed

lemma poly_add_zero':
  assumes "set p \<subseteq> carrier R"
  shows "poly_add p [] = normalize p" and "poly_add [] p = normalize p"
proof -
  show "poly_add p [] = normalize p" using assms
  proof (induction p)
    case Nil thus ?case by simp
  next
    { fix p assume A: "set p \<subseteq> carrier R" "lead_coeff p \<noteq> \<zero>"
      hence "polynomial R p"
        unfolding polynomial_def by simp
      moreover have "coeff (poly_add p []) = coeff p"
        using poly_add_coeff[of p "[]"] A(1) by simp
      ultimately have "poly_add p [] = p"
        using coeff_iff_polynomial_cond[OF
              poly_add_is_polynomial[OF A(1), of "[]"], of p] by simp }
    note aux_lemma = this
    case (Cons a p) thus ?case
      using aux_lemma[of "a # p"] by auto
  qed
  thus "poly_add [] p = normalize p"
    using poly_add_comm[OF assms, of "[]"] by simp
qed

lemma poly_add_zero:
  assumes "polynomial R p"
  shows "poly_add p [] = p" and "poly_add [] p = p"
  using poly_add_zero' normalize_idem polynomial_in_carrier assms by auto

lemma poly_add_replicate_zero':
  assumes "set p \<subseteq> carrier R"
  shows "poly_add p (replicate n \<zero>) = normalize p" and "poly_add (replicate n \<zero>) p = normalize p"
proof -
  have "poly_add p (replicate n \<zero>) = poly_add p []"
    using poly_add_normalize(2)[OF assms, of "replicate n \<zero>"]
          normalize_replicate_zero[of n "[]"] by force
  also have " ... = normalize p"
    using poly_add_zero'[OF assms] by simp
  finally show "poly_add p (replicate n \<zero>) = normalize p" .
  thus "poly_add (replicate n \<zero>) p = normalize p"
    using poly_add_comm[OF assms, of "replicate n \<zero>"] by force
qed

lemma poly_add_replicate_zero:
  assumes "polynomial R p"
  shows "poly_add p (replicate n \<zero>) = p" and "poly_add (replicate n \<zero>) p = p"
  using poly_add_replicate_zero' normalize_idem polynomial_in_carrier assms by auto


subsection \<open>Dense Representation\<close>

lemma dense_repr_replicate_zero: "dense_repr ((replicate n \<zero>) @ p) = dense_repr p"
  by (induction n) (auto)

lemma polynomial_dense_repr:
  assumes "polynomial R p" and "p \<noteq> []"
  shows "dense_repr p = (lead_coeff p, degree p) # dense_repr (normalize (tl p))"
proof -
  let ?len = length and ?norm = normalize
  obtain a p' where p: "p = a # p'"
    using assms(2) list.exhaust_sel by blast 
  hence a: "a \<in> carrier R - { \<zero> }" and p': "set p' \<subseteq> carrier R"
    using assms(1) unfolding p by (auto simp add: polynomial_def)
  hence "dense_repr p = (lead_coeff p, degree p) # dense_repr p'"
    unfolding p by simp
  also have " ... =
    (lead_coeff p, degree p) # dense_repr ((replicate (?len p' - ?len (?norm p')) \<zero>) @ ?norm p')"
    using normalize_def' dense_repr_replicate_zero by simp
  also have " ... = (lead_coeff p, degree p) # dense_repr (?norm p')"
    using dense_repr_replicate_zero by simp
  finally show ?thesis
    unfolding p by simp
qed

lemma monon_decomp:
  assumes "polynomial R p"
  shows "p = of_dense (dense_repr p)"
  using assms
proof (induct "length p" arbitrary: p rule: less_induct)
  case less thus ?case
  proof (cases p)
    case Nil thus ?thesis by simp
  next
    case (Cons a l)
    hence a: "a \<in> carrier R - { \<zero> }" and l: "set l \<subseteq> carrier R"
      using less(2) by (auto simp add: polynomial_def)
    hence "a # l = poly_add (monon a (degree (a # l))) l"
      using poly_add_monon by (simp add: degree_def)
    also have " ... = poly_add (monon a (degree (a # l))) (normalize l)"
      using poly_add_normalize(2)[of "monon a (degree (a # l))", OF _ l] a
      unfolding monon_def by force
    also have " ... = poly_add (monon a (degree (a # l))) (of_dense (dense_repr (normalize l)))"
      using less(1)[of "normalize l"] normalize_length_le normalize_gives_polynomial[OF l]
      unfolding Cons by (simp add: le_imp_less_Suc)
    also have " ... = of_dense ((a, degree (a # l)) # dense_repr (normalize l))"
      by simp
    also have " ... = of_dense (dense_repr (a # l))"
      using polynomial_dense_repr[OF less(2)] unfolding Cons by simp
    finally show ?thesis
      unfolding Cons by simp
  qed
qed

end


subsection \<open>Polynomial multiplication\<close>

context ring
begin

lemma poly_mult_is_polynomial:
  assumes "set p1 \<subseteq> carrier R" and "set p2 \<subseteq> carrier R"
  shows "polynomial R (poly_mult p1 p2)"
  using assms
proof (induction p1)
  case Nil thus ?case
    by (simp add: polynomial_def)
next
  case (Cons a p1)
  let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (degree (a # p1)) \<zero>)"
  
  have "set (poly_mult p1 p2) \<subseteq> carrier R"
    using Cons unfolding polynomial_def by auto

  moreover have "set ?a_p2 \<subseteq> carrier R"
  proof -
    have "set (map (\<lambda>b. a \<otimes> b) p2) \<subseteq> carrier R"
    proof
      fix c assume "c \<in> set (map (\<lambda>b. a \<otimes> b) p2)"
      then obtain b where "b \<in> set p2" "c = a \<otimes> b"
        by auto
      thus "c \<in> carrier R"
        using Cons(2-3) by auto
    qed
    thus ?thesis
      unfolding degree_def by auto
  qed

  ultimately have "polynomial R (poly_add ?a_p2 (poly_mult p1 p2))"
    using poly_add_is_polynomial by blast
  thus ?case by simp
qed

lemma poly_mult_in_carrier:
  "\<lbrakk> set p1 \<subseteq> carrier R; set p2 \<subseteq> carrier R \<rbrakk> \<Longrightarrow> set (poly_mult p1 p2) \<subseteq> carrier R"
  using poly_mult_is_polynomial polynomial_in_carrier by simp

lemma poly_mult_closed: "\<lbrakk> polynomial R p1; polynomial R p2 \<rbrakk> \<Longrightarrow> polynomial R (poly_mult p1 p2)"
  using poly_mult_is_polynomial polynomial_in_carrier by simp

lemma poly_mult_coeff:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "coeff (poly_mult p1 p2) = (\<lambda>i. \<Oplus> k \<in> {..i}. (coeff p1) k \<otimes> (coeff p2) (i - k))"
  using assms(1) 
proof (induction p1)
  case Nil thus ?case using assms(2) by auto
next
  case (Cons a p1)
  hence in_carrier:
    "a \<in> carrier R" "\<And>i. (coeff p1) i \<in> carrier R" "\<And>i. (coeff p2) i \<in> carrier R"
    using coeff_in_carrier assms(2) by auto

  let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (degree (a # p1)) \<zero>)"
  have "coeff  (replicate (degree (a # p1)) \<zero>) = (\<lambda>_. \<zero>)"
   and "length (replicate (degree (a # p1)) \<zero>) = length p1"
    using prefix_replicate_zero_coeff[of "[]" "length p1"] unfolding degree_def by auto
  hence "coeff ?a_p2 = (\<lambda>i. if i < length p1 then \<zero> else (coeff (map (\<lambda>b. a \<otimes> b) p2)) (i - length p1))"
    using append_coeff[of "map (\<lambda>b. a \<otimes> b) p2" "replicate (length p1) \<zero>"] unfolding degree_def by auto
  also have " ... = (\<lambda>i. if i < length p1 then \<zero> else a \<otimes> ((coeff p2) (i - length p1)))"
  proof -
    have "\<And>i. i < length p2 \<Longrightarrow> (coeff (map (\<lambda>b. a \<otimes> b) p2)) i = a \<otimes> ((coeff p2) i)"
    proof -
      fix i assume i_lt: "i < length p2"
      hence "(coeff (map (\<lambda>b. a \<otimes> b) p2)) i = (map (\<lambda>b. a \<otimes> b) p2) ! (length p2 - 1 - i)"
        using coeff_nth[of i "map (\<lambda>b. a \<otimes> b) p2"] by auto
      also have " ... = a \<otimes> (p2 ! (length p2 - 1 - i))"
        using i_lt by auto
      also have " ... = a \<otimes> ((coeff p2) i)"
        using coeff_nth[OF i_lt] by simp
      finally show "(coeff (map (\<lambda>b. a \<otimes> b) p2)) i = a \<otimes> ((coeff p2) i)" .
    qed
    moreover have "\<And>i. i \<ge> length p2 \<Longrightarrow> (coeff (map (\<lambda>b. a \<otimes> b) p2)) i = a \<otimes> ((coeff p2) i)"
      using coeff_length[of p2] coeff_length[of "map (\<lambda>b. a \<otimes> b) p2"] in_carrier by auto
    ultimately show ?thesis by (meson not_le)
  qed
  also have " ... = (\<lambda>i. \<Oplus> k \<in> {..i}. (if k = length p1 then a else \<zero>) \<otimes> (coeff p2) (i - k))"
  (is "?f1 = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k)))")
  proof
    fix i
    have "\<And>k. k \<in> {..i} \<Longrightarrow> ?f2 k \<otimes> ?f3 (i - k) = \<zero>" if "i < length p1"
      using in_carrier that by auto
    hence "(\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k)) = \<zero>" if "i < length p1"
      using that in_carrier
            add.finprod_cong'[of "{..i}" "{..i}" "\<lambda>k. ?f2 k \<otimes> ?f3 (i - k)" "\<lambda>i. \<zero>"]
      by auto
    hence eq_lt: "?f1 i = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k))) i" if "i < length p1"
      using that by auto

    have "\<And>k. k \<in> {..i} \<Longrightarrow>
              ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k) = (if length p1 = k then a \<otimes> coeff p2 (i - k) else \<zero>)"
      using in_carrier by auto
    hence "(\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k)) = 
           (\<Oplus> k \<in> {..i}. (if length p1 = k then a \<otimes> coeff p2 (i - k) else \<zero>))"
      using in_carrier
            add.finprod_cong'[of "{..i}" "{..i}" "\<lambda>k. ?f2 k \<otimes> ?f3 (i - k)"
                             "\<lambda>k. (if length p1 = k then a \<otimes> coeff p2 (i - k) else \<zero>)"]
      by fastforce
    also have " ... = a \<otimes> (coeff p2) (i - length p1)" if "i \<ge> length p1"
      using add.finprod_singleton[of "length p1" "{..i}" "\<lambda>j. a \<otimes> (coeff p2) (i - j)"]
            in_carrier that by auto
    finally
    have "(\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k)) =  a \<otimes> (coeff p2) (i - length p1)" if "i \<ge> length p1"
      using that by simp
    hence eq_ge: "?f1 i = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k))) i" if "i \<ge> length p1"
      using that by auto

    from eq_lt eq_ge show "?f1 i = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k))) i" by auto
  qed

  finally have coeff_a_p2:
    "coeff ?a_p2 = (\<lambda>i. \<Oplus> k \<in> {..i}. (if k = length p1 then a else \<zero>) \<otimes> (coeff p2) (i - k))" .

  have "set ?a_p2 \<subseteq> carrier R"
    using in_carrier(1) assms(2) by auto

  moreover have "set (poly_mult p1 p2) \<subseteq> carrier R"
    using poly_mult_is_polynomial[of p1 p2] polynomial_in_carrier assms(2) Cons(2) by auto 

  ultimately
  have "coeff (poly_mult (a # p1) p2) = (\<lambda>i. ((coeff ?a_p2) i) \<oplus> ((coeff (poly_mult p1 p2)) i))"
    using poly_add_coeff[of ?a_p2 "poly_mult p1 p2"] by simp
  also have " ... = (\<lambda>i. (\<Oplus> k \<in> {..i}. (if k = length p1 then a else \<zero>) \<otimes> (coeff p2) (i - k)) \<oplus>
                         (\<Oplus> k \<in> {..i}. (coeff p1) k \<otimes> (coeff p2) (i - k)))"
    using Cons  coeff_a_p2 by simp
  also have " ... = (\<lambda>i. (\<Oplus> k \<in> {..i}. ((if k = length p1 then a else \<zero>) \<otimes> (coeff p2) (i - k)) \<oplus>
                                                            ((coeff p1) k \<otimes> (coeff p2) (i - k))))"
    using add.finprod_multf in_carrier by auto
  also have " ... = (\<lambda>i. (\<Oplus> k \<in> {..i}. (coeff (a # p1) k) \<otimes> (coeff p2) (i - k)))"
   (is "(\<lambda>i. (\<Oplus> k \<in> {..i}. ?f i k)) = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?g i k))")
  proof
    fix i
    have "\<And>k. ?f i k = ?g i k"
      using in_carrier coeff_length[of p1] by (auto simp add: degree_def)
    thus "(\<Oplus> k \<in> {..i}. ?f i k) = (\<Oplus> k \<in> {..i}. ?g i k)" by simp
  qed
  finally show ?case .
qed

lemma poly_mult_zero:
  assumes "polynomial R p"
  shows "poly_mult [] p = []" and "poly_mult p [] = []"
proof -
  show "poly_mult [] p = []" by simp
next
  have "coeff (poly_mult p []) = (\<lambda>_. \<zero>)"
    using poly_mult_coeff[OF polynomial_in_carrier[OF assms], of "[]"]
          poly_coeff_in_carrier[OF assms] by auto
  thus "poly_mult p [] = []"
    using coeff_iff_polynomial_cond[OF poly_mult_closed[OF assms, of "[]"]] zero_is_polynomial by auto
qed

lemma poly_mult_l_distr':
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "set p3 \<subseteq> carrier R"
  shows "poly_mult (poly_add p1 p2) p3 = poly_add (poly_mult p1 p3) (poly_mult p2 p3)"
proof -
  let ?c1 = "coeff p1" and ?c2 = "coeff p2" and ?c3 = "coeff p3"
  have in_carrier:
    "\<And>i. ?c1 i \<in> carrier R" "\<And>i. ?c2 i \<in> carrier R" "\<And>i. ?c3 i \<in> carrier R"
    using assms coeff_in_carrier by auto

  have "coeff (poly_mult (poly_add p1 p2) p3) = (\<lambda>n. \<Oplus>i \<in> {..n}. (?c1 i \<oplus> ?c2 i) \<otimes> ?c3 (n - i))"
    using poly_mult_coeff[of "poly_add p1 p2" p3]  poly_add_coeff[OF assms(1-2)]
          poly_add_in_carrier[OF assms(1-2)] assms by auto
  also have " ... = (\<lambda>n. \<Oplus>i \<in> {..n}. (?c1 i \<otimes> ?c3 (n - i)) \<oplus> (?c2 i \<otimes> ?c3 (n - i)))"
    using in_carrier l_distr by auto
  also
  have " ... = (\<lambda>n. (\<Oplus>i \<in> {..n}. (?c1 i \<otimes> ?c3 (n - i))) \<oplus> (\<Oplus>i \<in> {..n}. (?c2 i \<otimes> ?c3 (n - i))))"
    using add.finprod_multf in_carrier by auto
  also have " ... = coeff (poly_add (poly_mult p1 p3) (poly_mult p2 p3))"
    using poly_mult_coeff[OF assms(1) assms(3)] poly_mult_coeff[OF assms(2-3)]
          poly_add_coeff[OF poly_mult_in_carrier[OF assms(1) assms(3)]]
                            poly_mult_in_carrier[OF assms(2-3)] by simp
  finally have "coeff (poly_mult (poly_add p1 p2) p3) =
                coeff (poly_add (poly_mult p1 p3) (poly_mult p2 p3))" .
  moreover have "polynomial R (poly_mult (poly_add p1 p2) p3)"
            and "polynomial R (poly_add (poly_mult p1 p3) (poly_mult p2 p3))"
    using assms poly_add_is_polynomial poly_mult_is_polynomial polynomial_in_carrier by auto
  ultimately show ?thesis
    using coeff_iff_polynomial_cond by auto 
qed

lemma poly_mult_l_distr:
  assumes "polynomial R p1" "polynomial R p2" "polynomial R p3"
  shows "poly_mult (poly_add p1 p2) p3 = poly_add (poly_mult p1 p3) (poly_mult p2 p3)"
  using poly_mult_l_distr' polynomial_in_carrier assms by auto

lemma poly_mult_append_replicate_zero:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_mult p1 p2 = poly_mult ((replicate n \<zero>) @ p1) p2"
proof -
  { fix p1 p2 assume A: "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
    hence "poly_mult p1 p2 = poly_mult (\<zero> # p1) p2"
    proof -
      let ?a_p2 = "(map ((\<otimes>) \<zero>) p2) @ (replicate (length p1) \<zero>)"
      have "?a_p2 = replicate (length p2 + length p1) \<zero>"
        using A(2) by (induction p2) (auto)
      hence "poly_mult (\<zero> # p1) p2 = poly_add (replicate (length p2 + length p1) \<zero>) (poly_mult p1 p2)"
        by (simp add: degree_def)
      also have " ... = poly_add (normalize (replicate (length p2 + length p1) \<zero>)) (poly_mult p1 p2)"
        using poly_add_normalize(1)[of "replicate (length p2 + length p1) \<zero>" "poly_mult p1 p2"]
              poly_mult_in_carrier[OF A] by force
      also have " ... = poly_mult p1 p2"
        using poly_add_zero(2)[OF poly_mult_is_polynomial[OF A]]
              normalize_replicate_zero[of "length p2 + length p1" "[]"] by auto
      finally show ?thesis by auto
    qed } note aux_lemma = this
  
  from assms show ?thesis
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n) thus ?case
      using aux_lemma[of "replicate n \<zero> @ p1" p2] by force
  qed
qed

lemma poly_mult_normalize:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_mult p1 p2 = poly_mult (normalize p1) p2"
proof -
  let ?replicate = "replicate (length p1 - length (normalize p1)) \<zero>"
  have "poly_mult p1 p2 = poly_mult (?replicate @ (normalize p1)) p2"
    using normalize_def'[of p1] by simp
  also have " ... = poly_mult (normalize p1) p2"
    using poly_mult_append_replicate_zero polynomial_in_carrier
          normalize_gives_polynomial assms by auto
  finally show ?thesis .
qed

end


subsection \<open>Properties Within a Domain\<close>

context domain
begin

lemma one_is_polynomial [intro]: "polynomial R [ \<one> ]"
  unfolding polynomial_def by auto

lemma poly_mult_comm:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_mult p1 p2 = poly_mult p2 p1"
proof -
  let ?c1 = "coeff p1" and ?c2 = "coeff p2"
  have "\<And>i. (\<Oplus>k \<in> {..i}. ?c1 k \<otimes> ?c2 (i - k)) = (\<Oplus>k \<in> {..i}. ?c2 k \<otimes> ?c1 (i - k))"
  proof -
    fix i :: nat
    let ?f = "\<lambda>k. ?c1 k \<otimes> ?c2 (i - k)"
    have in_carrier: "\<And>i. ?c1 i \<in> carrier R" "\<And>i. ?c2 i \<in> carrier R"
      using coeff_in_carrier[OF assms(1)] coeff_in_carrier[OF assms(2)] by auto

    have reindex_inj: "inj_on (\<lambda>k. i - k) {..i}"
      using inj_on_def by force
    moreover have "(\<lambda>k. i - k) ` {..i} \<subseteq> {..i}" by auto
    hence "(\<lambda>k. i - k) ` {..i} = {..i}"
      using reindex_inj endo_inj_surj[of "{..i}" "\<lambda>k. i - k"] by simp 
    ultimately have "(\<Oplus>k \<in> {..i}. ?f k) = (\<Oplus>k \<in> {..i}. ?f (i - k))"
      using add.finprod_reindex[of ?f "\<lambda>k. i - k" "{..i}"] in_carrier by auto

    moreover have "\<And>k. k \<in> {..i} \<Longrightarrow> ?f (i - k) = ?c2 k \<otimes> ?c1 (i - k)"
      using in_carrier m_comm by auto
    hence "(\<Oplus>k \<in> {..i}. ?f (i - k)) = (\<Oplus>k \<in> {..i}. ?c2 k \<otimes> ?c1 (i - k))"
      using add.finprod_cong'[of "{..i}" "{..i}"] in_carrier by auto
    ultimately show "(\<Oplus>k \<in> {..i}. ?f k) = (\<Oplus>k \<in> {..i}. ?c2 k \<otimes> ?c1 (i - k))"
      by simp
  qed
  hence "coeff (poly_mult p1 p2) = coeff (poly_mult p2 p1)"
    using poly_mult_coeff[OF assms] poly_mult_coeff[OF assms(2) assms(1)] by simp
  thus ?thesis
    using coeff_iff_polynomial_cond[OF poly_mult_is_polynomial[OF assms]
                                       poly_mult_is_polynomial[OF assms(2) assms(1)]] by simp
qed

lemma poly_mult_r_distr':
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "set p3 \<subseteq> carrier R"
  shows "poly_mult p1 (poly_add p2 p3) = poly_add (poly_mult p1 p2) (poly_mult p1 p3)"
  using poly_mult_comm[OF assms(1-2)] poly_mult_l_distr'[OF assms(2-3) assms(1)]
        poly_mult_comm[OF assms(1) assms(3)] poly_add_is_polynomial[OF assms(2-3)]
        polynomial_in_carrier poly_mult_comm[OF assms(1), of "poly_add p2 p3"] by simp

lemma poly_mult_r_distr:
  assumes "polynomial R p1" "polynomial R p2" "polynomial R p3"
  shows "poly_mult p1 (poly_add p2 p3) = poly_add (poly_mult p1 p2) (poly_mult p1 p3)"
  using poly_mult_r_distr' polynomial_in_carrier assms by auto

lemma poly_mult_replicate_zero:
  assumes "set p \<subseteq> carrier R"
  shows "poly_mult (replicate n \<zero>) p = []"
    and "poly_mult p (replicate n \<zero>) = []"
proof -
  have in_carrier: "\<And>n. set (replicate n \<zero>) \<subseteq> carrier R" by auto
  show "poly_mult (replicate n \<zero>) p = []" using assms
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    hence "poly_mult (replicate (Suc n) \<zero>) p = poly_mult (\<zero> # (replicate n \<zero>)) p"
      by simp
    also have " ... = poly_add ((map (\<lambda>a. \<zero> \<otimes> a) p) @ (replicate n \<zero>)) []"
      using Suc by (simp add: degree_def)
    also have " ... = poly_add ((map (\<lambda>a. \<zero>) p) @ (replicate n \<zero>)) []"
      using Suc(2) by (smt map_eq_conv ring_simprules(24) subset_code(1))
    also have " ... = poly_add (replicate (length p + n) \<zero>) []"
      by (simp add: map_replicate_const replicate_add)
    also have " ... = poly_add [] []"
      using poly_add_normalize(1)[of "replicate (length p + n) \<zero>" "[]"]
            normalize_replicate_zero[of "length p + n" "[]"] by auto
    also have " ... = []" by simp
    finally show ?case . 
  qed
  thus "poly_mult p (replicate n \<zero>) = []"
    using poly_mult_comm[OF assms in_carrier] by simp
qed

lemma poly_mult_const:
  assumes "polynomial R p" "a \<in> carrier R - { \<zero> }"
  shows "poly_mult [ a ] p = map (\<lambda>b. a \<otimes> b) p" and "poly_mult p [ a ] = map (\<lambda>b. a \<otimes> b) p"
proof -
  show "poly_mult [ a ] p = map (\<lambda>b. a \<otimes> b) p"
  proof -
    have "poly_mult [ a ] p = poly_add (map (\<lambda>b. a \<otimes> b) p) []"
      by (simp add: degree_def)
    moreover have "polynomial R (map (\<lambda>b. a \<otimes> b) p)"
    proof (cases p)
      case Nil thus ?thesis by (simp add: polynomial_def)
    next
      case (Cons b ps)
      hence "a \<otimes> lead_coeff p \<noteq> \<zero>"
        using assms integral[of a "lead_coeff p"] unfolding polynomial_def by auto 
      thus ?thesis
        using Cons polynomial_in_carrier[OF assms(1)] assms(2) unfolding polynomial_def by auto 
    qed
    ultimately show ?thesis
      using poly_add_zero(1)[of "map (\<lambda>b. a \<otimes> b) p"] by simp
  qed
  thus "poly_mult p [ a ] = map (\<lambda>b. a \<otimes> b) p"
    using poly_mult_comm[of "[ a ]" p] polynomial_in_carrier[OF assms(1)] assms(2) by auto
qed

lemma poly_mult_monon:
  assumes "polynomial R p" "a \<in> carrier R - { \<zero> }"
  shows "poly_mult (monon a n) p =
           (if p = [] then [] else (map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>))"
proof (cases p)
  case Nil thus ?thesis
    using poly_mult_zero(2)[OF monon_is_polynomial[OF assms(2)]] by simp
next
  case (Cons b ps)
  hence "lead_coeff ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)) = a \<otimes> b"
    by simp
  hence "lead_coeff ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)) \<noteq> \<zero>"
    using Cons assms integral[of a b] unfolding polynomial_def by auto
  moreover have "set ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)) \<subseteq> carrier R"
    using polynomial_in_carrier[OF assms(1)] assms(2) DiffD1 by auto 
  ultimately have is_polynomial: "polynomial R ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>))"
    using Cons unfolding polynomial_def by auto

  have "poly_mult (a # replicate n \<zero>) p =
        poly_add ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)) (poly_mult (replicate n \<zero>) p)"
    by (simp add: degree_def)
  also have " ... = poly_add ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)) []"
    using poly_mult_replicate_zero(1)[OF polynomial_in_carrier[OF assms(1)]] by simp
  also have " ... = (map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)"
    using poly_add_zero(1)[OF is_polynomial] .
  also have " ... = (if p = [] then [] else (map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>))"
    using Cons by auto
  finally show ?thesis unfolding monon_def .
qed

lemma poly_mult_one:
  assumes "polynomial R p"
  shows "poly_mult [ \<one> ] p = p" and "poly_mult p [ \<one> ] = p"
proof -
  have "map (\<lambda>a. \<one> \<otimes> a) p = p"
    using polynomial_in_carrier[OF assms] by (meson assms l_one map_idI  subsetCE) 
  thus "poly_mult [ \<one> ] p = p" and "poly_mult p [ \<one> ] = p"
    using poly_mult_const[OF assms, of \<one>] by auto
qed

lemma poly_mult_lead_coeff_aux:
  assumes "polynomial R p1" "polynomial R p2" and "p1 \<noteq> []" and "p2 \<noteq> []"
  shows "(coeff (poly_mult p1 p2)) (degree p1 + degree p2) = (lead_coeff p1) \<otimes> (lead_coeff p2)"
proof -
  have p1: "lead_coeff p1 \<in> carrier R - { \<zero> }" and p2: "lead_coeff p2 \<in> carrier R - { \<zero> }"
    using assms unfolding polynomial_def by auto

  have "(coeff (poly_mult p1 p2)) (degree p1 + degree p2) = 
        (\<Oplus> k \<in> {..((degree p1) + (degree p2))}.
          (coeff p1) k \<otimes> (coeff p2) ((degree p1) + (degree p2) - k))"
    using poly_mult_coeff assms(1-2) polynomial_in_carrier by auto
  also have " ... = (lead_coeff p1) \<otimes> (lead_coeff p2)"
  proof -
    let ?f = "\<lambda>i. (coeff p1) i \<otimes> (coeff p2) ((degree p1) + (degree p2) - i)"
    have in_carrier: "\<And>i. (coeff p1) i \<in> carrier R" "\<And>i. (coeff p2) i \<in> carrier R"
      using coeff_in_carrier assms by auto
    have "\<And>i. i < degree p1 \<Longrightarrow> ?f i = \<zero>"
      using coeff_degree[of p2] in_carrier by auto
    moreover have "\<And>i. i > degree p1 \<Longrightarrow> ?f i = \<zero>"
      using coeff_degree[of p1] in_carrier by auto
    moreover have "?f (degree p1) = (lead_coeff p1) \<otimes> (lead_coeff p2)"
      using assms(3-4) by simp
    ultimately have "?f = (\<lambda>i. if degree p1 = i then (lead_coeff p1) \<otimes> (lead_coeff p2) else \<zero>)"
      using nat_neq_iff by auto
    thus ?thesis
      using add.finprod_singleton[of "degree p1" "{..((degree p1) + (degree p2))}"
                                     "\<lambda>i. (lead_coeff p1) \<otimes> (lead_coeff p2)"] p1 p2 by auto
  qed
  finally show ?thesis .
qed

lemma poly_mult_degree_eq:
  assumes "polynomial R p1" "polynomial R p2"
  shows "degree (poly_mult p1 p2) = (if p1 = [] \<or> p2 = [] then 0 else (degree p1) + (degree p2))"
proof (cases p1)
  case Nil thus ?thesis by (simp add: degree_def)
next
  case (Cons a p1') note p1 = Cons
  show ?thesis
  proof (cases p2)
    case Nil thus ?thesis
      using poly_mult_zero(2)[OF assms(1)] by (simp add: degree_def)
  next
    case (Cons b p2') note p2 = Cons
    have a: "a \<in> carrier R" and b: "b \<in> carrier R"
      using p1 p2 polynomial_in_carrier[OF assms(1)] polynomial_in_carrier[OF assms(2)] by auto
    have "(coeff (poly_mult p1 p2)) ((degree p1) + (degree p2)) = a \<otimes> b"
      using poly_mult_lead_coeff_aux[OF assms] p1 p2 by simp
    hence "(coeff (poly_mult p1 p2)) ((degree p1) + (degree p2)) \<noteq> \<zero>"
      using assms p1 p2 integral[of a b] unfolding polynomial_def by auto
    moreover have "\<And>i. i > (degree p1) + (degree p2) \<Longrightarrow> (coeff (poly_mult p1 p2)) i = \<zero>"
    proof -
      have aux_lemma: "degree (poly_mult p1 p2) \<le> (degree p1) + (degree p2)"
      proof (induct p1)
        case Nil
        then show ?case by simp
      next
        case (Cons a p1)
        let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (degree (a # p1)) \<zero>)"
        have "poly_mult (a # p1) p2 = poly_add ?a_p2 (poly_mult p1 p2)" by simp
        hence "degree (poly_mult (a # p1) p2) \<le> max (degree ?a_p2) (degree (poly_mult p1 p2))"
          using poly_add_degree[of ?a_p2 "poly_mult p1 p2"] by simp
        also have " ... \<le> max ((degree (a # p1)) + (degree p2)) (degree (poly_mult p1 p2))"
          unfolding degree_def by auto
        also have " ... \<le> max ((degree (a # p1)) + (degree p2)) ((degree p1) + (degree p2))"
          using Cons by simp
        also have " ... \<le> (degree (a # p1)) + (degree p2)"
          unfolding degree_def by auto
        finally show ?case .
      qed
      fix i show "i > (degree p1) + (degree p2) \<Longrightarrow> (coeff (poly_mult p1 p2)) i = \<zero>"
        using coeff_degree aux_lemma by simp
    qed
    ultimately have "degree (poly_mult p1 p2) = degree p1 + degree p2"
      using degree_def'[OF poly_mult_closed[OF assms]]
      by (smt coeff_degree linorder_cases not_less_Least)
    thus ?thesis
      using p1 p2 by auto
  qed
qed

lemma poly_mult_integral:
  assumes "polynomial R p1" "polynomial R p2"
  shows "poly_mult p1 p2 = [] \<Longrightarrow> p1 = [] \<or> p2 = []"
proof (rule ccontr)
  assume A: "poly_mult p1 p2 = []" "\<not> (p1 = [] \<or> p2 = [])"
  hence "degree (poly_mult p1 p2) = degree p1 + degree p2"
    using poly_mult_degree_eq[OF assms] by simp
  hence "length p1 = 1 \<and> length p2 = 1"
    unfolding degree_def using A Suc_diff_Suc by fastforce
  then obtain a b where p1: "p1 = [ a ]" and p2: "p2 = [ b ]"
    by (metis One_nat_def length_0_conv length_Suc_conv)
  hence "a \<in> carrier R - { \<zero> }" and "b \<in> carrier R - { \<zero> }"
    using assms unfolding polynomial_def by auto
  hence "poly_mult [ a ] [ b ] = [ a \<otimes> b ]"
    using A assms(2) poly_mult_const(1) p1 by fastforce
  thus False using A(1) p1 p2 by simp
qed

lemma poly_mult_lead_coeff:
  assumes "polynomial R p1" "polynomial R p2" and "p1 \<noteq> []" and "p2 \<noteq> []"
  shows "lead_coeff (poly_mult p1 p2) = (lead_coeff p1) \<otimes> (lead_coeff p2)"
proof -
  have "poly_mult p1 p2 \<noteq> []"
    using poly_mult_integral[OF assms(1-2)] assms(3-4) by auto
  hence "lead_coeff (poly_mult p1 p2) = (coeff (poly_mult p1 p2)) (degree p1 + degree p2)"
    using poly_mult_degree_eq[OF assms(1-2)] assms(3-4) by (metis coeff.simps(2) list.collapse)
  thus ?thesis
    using poly_mult_lead_coeff_aux[OF assms] by simp
qed

end


subsection \<open>Algebraic Structure of Polynomials\<close>

definition univ_poly :: "('a, 'b) ring_scheme \<Rightarrow> ('a list) ring"
  where "univ_poly R =
           \<lparr> carrier = { p. polynomial R p },
         monoid.mult = ring.poly_mult R,
                 one = [ \<one>\<^bsub>R\<^esub> ],
                zero = [],
                 add = ring.poly_add R \<rparr>"

context domain
begin

lemma poly_mult_assoc_aux:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "a \<in> carrier R"
    shows "poly_mult ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)) q =
           poly_mult (monon a n) (poly_mult p q)"
proof -
  let ?len = "n"
  let ?a_p = "(map (\<lambda>b. a \<otimes> b) p) @ (replicate ?len \<zero>)"
  let ?c2 = "coeff p" and ?c3 = "coeff q"
  have coeff_a_p:
    "coeff ?a_p = (\<lambda>i. if i < ?len then \<zero> else a \<otimes> ?c2 (i - ?len))" (is
    "coeff ?a_p = (\<lambda>i. ?f i)")
    using append_coeff[of "map ((\<otimes>) a) p" "replicate ?len \<zero>"]
          replicate_zero_coeff[of ?len] scalar_coeff[OF assms(3), of p] by auto
  have in_carrier:
    "set ?a_p \<subseteq> carrier R" "\<And>i. ?c2 i \<in> carrier R" "\<And>i. ?c3 i \<in> carrier R"
    "\<And>i. coeff (poly_mult p q) i \<in> carrier R"
    using assms poly_mult_in_carrier by auto
  have "coeff (poly_mult ?a_p q) = (\<lambda>n. (\<Oplus>i \<in> {..n}. (coeff ?a_p) i \<otimes> ?c3 (n - i)))"
    using poly_mult_coeff[OF in_carrier(1) assms(2)] .
  also have " ... = (\<lambda>n. (\<Oplus>i \<in> {..n}. (?f i) \<otimes> ?c3 (n - i)))"
    using coeff_a_p by simp
  also have " ... = (\<lambda>n. (\<Oplus>i \<in> {..n}. (if i = ?len then a else \<zero>) \<otimes> (coeff (poly_mult p q)) (n - i)))"
    (is "(\<lambda>n. (\<Oplus>i \<in> {..n}. ?side1 n i)) = (\<lambda>n. (\<Oplus>i \<in> {..n}. ?side2 n i))")
  proof
    fix n
    have in_carrier': "\<And>i. ?side1 n i \<in> carrier R" "\<And>i. ?side2 n i \<in> carrier R"
      using in_carrier assms coeff_in_carrier poly_mult_in_carrier by auto
    show "(\<Oplus>i \<in> {..n}. ?side1 n i) = (\<Oplus>i \<in> {..n}. ?side2 n i)"
    proof (cases "n < ?len")
      assume "n < ?len"
      hence "\<And>i. i \<le> n \<Longrightarrow> ?side1 n i = ?side2 n i"
        using in_carrier assms coeff_in_carrier poly_mult_in_carrier by simp
      thus ?thesis
        using add.finprod_cong'[of "{..n}" "{..n}" "?side1 n" "?side2 n"] in_carrier'
        by (metis (no_types, lifting) Pi_I' atMost_iff)
    next
      assume "\<not> n < ?len"
      hence n_ge: "n \<ge> ?len" by simp
      define h where "h = (\<lambda>i. if i < ?len then \<zero> else (a \<otimes> ?c2 (i - ?len)) \<otimes> ?c3 (n - i))"
      hence h_in_carrier: "\<And>i. h i \<in> carrier R"
        using assms(3) in_carrier by auto
      have "\<And>i. (?f i) \<otimes> ?c3 (n - i) = h i"
        using in_carrier(2-3) assms(3) h_def by auto
      hence "(\<Oplus>i \<in> {..n}. ?side1 n i) = (\<Oplus>i \<in> {..n}. h i)"
        by simp
      also have " ... = (\<Oplus>i \<in> {..<?len}. h i) \<oplus> (\<Oplus>i \<in> {?len..n}. h i)"
        using add.finprod_Un_disjoint[of "{..<?len}" "{?len..n}" h] h_in_carrier n_ge
        by (simp add: ivl_disj_int_one(4) ivl_disj_un_one(4))
      also have " ... = (\<Oplus>i \<in> {..<?len}. \<zero>) \<oplus> (\<Oplus>i \<in> {?len..n}. h i)"
        using add.finprod_cong'[of "{..<?len}" "{..<?len}" h "\<lambda>_. \<zero>"] h_in_carrier
        unfolding h_def by auto
      also have " ... = (\<Oplus>i \<in> {?len..n}. h i)"
        using add.finprod_one h_in_carrier by simp
      also have " ... = (\<Oplus>i \<in> (\<lambda>i. i + ?len) ` {..n - ?len}. h i)"
        using n_ge atLeast0AtMost image_add_atLeastAtMost'[of ?len 0 "n - ?len"] by auto
      also have " ... = (\<Oplus>i \<in> {..n - ?len}. h (i + ?len))"
        using add.finprod_reindex[of h "\<lambda>i. i + ?len" "{..n - ?len}"] h_in_carrier by simp
      also have " ... = (\<Oplus>i \<in> {..n - ?len}. (a \<otimes> ?c2 i) \<otimes> ?c3 (n - (i + ?len)))"
        unfolding h_def by simp
      also have " ... = (\<Oplus>i \<in> {..n - ?len}. a \<otimes> (?c2 i \<otimes> ?c3 (n - (i + ?len))))"
        using in_carrier assms(3) by (simp add: m_assoc) 
      also have " ... = a \<otimes> (\<Oplus>i \<in> {..n - ?len}. ?c2 i \<otimes> ?c3 (n - (i + ?len)))"
        using finsum_rdistr[of "{..n - ?len}" a "\<lambda>i. ?c2 i \<otimes> ?c3 (n - (i + ?len))"]
              in_carrier(2-3) assms(3) by simp
      also have " ... = a \<otimes> (coeff (poly_mult p q)) (n - ?len)"
        using poly_mult_coeff[OF assms(1-2)] n_ge by (simp add: add.commute)
      also have " ... =
        (\<Oplus>i \<in> {..n}. if ?len = i then a \<otimes> (coeff (poly_mult p q)) (n - i) else \<zero>)"
        using add.finprod_singleton[of ?len "{..n}" "\<lambda>i. a \<otimes> (coeff (poly_mult p q)) (n - i)"]
              n_ge in_carrier(2-4) assms by simp
      also have " ... = (\<Oplus>i \<in> {..n}. (if ?len = i then a else \<zero>) \<otimes> (coeff (poly_mult p q)) (n - i))"
        using in_carrier(2-4) assms(3) add.finprod_cong'[of "{..n}" "{..n}"] by simp
      also have " ... = (\<Oplus>i \<in> {..n}. ?side2 n i)"
      proof -
        have "(\<lambda>i. (if ?len = i then a else \<zero>) \<otimes> (coeff (poly_mult p q)) (n - i)) = ?side2 n" by auto
        thus ?thesis by simp
      qed
      finally show ?thesis .
    qed
  qed
  also have " ... = coeff (poly_mult (monon a n) (poly_mult p q))"
    using monon_coeff[of a "n"] poly_mult_coeff[of "monon a n" "poly_mult p q"]
          poly_mult_in_carrier[OF assms(1-2)] assms(3) unfolding monon_def by force
  finally
  have "coeff (poly_mult ?a_p q) = coeff (poly_mult (monon a n) (poly_mult p q))" .
  moreover have "polynomial R (poly_mult ?a_p q)"
    using poly_mult_is_polynomial[OF in_carrier(1) assms(2)] by simp
  moreover have "polynomial R (poly_mult (monon a n) (poly_mult p q))"
    using poly_mult_is_polynomial[of "monon a n" "poly_mult p q"]
          poly_mult_in_carrier[OF assms(1-2)] assms(3) unfolding monon_def
    using in_carrier(1) by auto
  ultimately show ?thesis
    using coeff_iff_polynomial_cond by simp
qed

lemma univ_poly_is_monoid: "monoid (univ_poly R)"
  unfolding univ_poly_def using poly_mult_one
proof (auto simp add: poly_add_closed poly_mult_closed one_is_polynomial monoid_def)
  fix p1 p2 p3
  let ?P = "poly_mult (poly_mult p1 p2) p3 = poly_mult p1 (poly_mult p2 p3)"

  assume A: "polynomial R p1" "polynomial R p2" "polynomial R p3"
  show ?P using polynomial_in_carrier[OF A(1)]
  proof (induction p1)
    case Nil thus ?case by simp
  next
    case (Cons a p1) thus ?case
    proof (cases "a = \<zero>")
      assume eq_zero: "a = \<zero>"
      have p1: "set p1 \<subseteq> carrier R"
        using Cons(2) by simp
      have "poly_mult (poly_mult (a # p1) p2) p3 = poly_mult (poly_mult p1 p2) p3"
        using poly_mult_append_replicate_zero[OF p1 polynomial_in_carrier[OF A(2)], of "Suc 0"]
              eq_zero by simp
      also have " ... = poly_mult p1 (poly_mult p2 p3)"
        using p1[THEN Cons(1)] by simp
      also have " ... = poly_mult (a # p1) (poly_mult p2 p3)"
        using poly_mult_append_replicate_zero[OF p1
              poly_mult_in_carrier[OF A(2-3)[THEN polynomial_in_carrier]], of "Suc 0"] eq_zero by simp
      finally show ?thesis .
    next
      assume "a \<noteq> \<zero>" hence in_carrier:
        "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "set p3 \<subseteq> carrier R" "a \<in> carrier R - { \<zero> }"
        using A(2-3) polynomial_in_carrier Cons by auto

      let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (length p1) \<zero>)"
      have a_p2_in_carrier: "set ?a_p2 \<subseteq> carrier R"
        using in_carrier by auto

      have "poly_mult (poly_mult (a # p1) p2) p3 = poly_mult (poly_add ?a_p2 (poly_mult p1 p2)) p3"
        by (simp add: degree_def)
      also have " ... = poly_add (poly_mult ?a_p2 p3) (poly_mult (poly_mult p1 p2) p3)"
        using poly_mult_l_distr'[OF a_p2_in_carrier poly_mult_in_carrier[OF in_carrier(1-2)] in_carrier(3)] .
      also have " ... = poly_add (poly_mult ?a_p2 p3) (poly_mult p1 (poly_mult p2 p3))"
        using Cons(1)[OF in_carrier(1)] by simp
      also have " ... = poly_add (poly_mult (a # (replicate (length p1) \<zero>)) (poly_mult p2 p3))
                                 (poly_mult p1 (poly_mult p2 p3))"
        using poly_mult_assoc_aux[of p2 p3 a "length p1"] in_carrier unfolding monon_def by simp
      also have " ... = poly_mult (poly_add (a # (replicate (length p1) \<zero>)) p1) (poly_mult p2 p3)"
        using poly_mult_l_distr'[of "a # (replicate (length p1) \<zero>)" p1 "poly_mult p2 p3"]
              poly_mult_in_carrier[OF in_carrier(2-3)] in_carrier by force
      also have " ... = poly_mult (a # p1) (poly_mult p2 p3)"
        using poly_add_monon[OF in_carrier(1) in_carrier(4)] unfolding monon_def by simp
      finally show ?thesis .
    qed
  qed
qed

declare poly_add.simps[simp del]

lemma univ_poly_is_abelian_monoid: "abelian_monoid (univ_poly R)"
  unfolding univ_poly_def
  using poly_add_closed poly_add_zero zero_is_polynomial
proof (auto simp add: abelian_monoid_def comm_monoid_def monoid_def comm_monoid_axioms_def)
  fix p1 p2 p3
  let ?c = "\<lambda>p. coeff p"
  assume A: "polynomial R p1" "polynomial R p2" "polynomial R p3"
  hence
    p1: "\<And>i. (?c p1) i \<in> carrier R" "set p1 \<subseteq> carrier R" and
    p2: "\<And>i. (?c p2) i \<in> carrier R" "set p2 \<subseteq> carrier R" and
    p3: "\<And>i. (?c p3) i \<in> carrier R" "set p3 \<subseteq> carrier R"
    using polynomial_in_carrier by auto
  have "?c (poly_add (poly_add p1 p2) p3) = (\<lambda>i. (?c p1 i \<oplus> ?c p2 i) \<oplus> (?c p3 i))"
    using poly_add_coeff[OF poly_add_in_carrier[OF p1(2) p2(2)] p3(2)]
          poly_add_coeff[OF p1(2) p2(2)] by simp
  also have " ... = (\<lambda>i. (?c p1 i) \<oplus> ((?c p2 i) \<oplus> (?c p3 i)))"
    using p1 p2 p3 add.m_assoc by simp
  also have " ... = ?c (poly_add p1 (poly_add p2 p3))"
    using poly_add_coeff[OF p1(2) poly_add_in_carrier[OF p2(2) p3(2)]]
          poly_add_coeff[OF p2(2) p3(2)] by simp
  finally have "?c (poly_add (poly_add p1 p2) p3) = ?c (poly_add p1 (poly_add p2 p3))" .
  thus "poly_add (poly_add p1 p2) p3 = poly_add p1 (poly_add p2 p3)"
    using coeff_iff_polynomial_cond poly_add_closed A by auto
  show "poly_add p1 p2 = poly_add p2 p1"
    using poly_add_comm[OF p1(2) p2(2)] .
qed

lemma univ_poly_is_abelian_group: "abelian_group (univ_poly R)"
proof -
  interpret abelian_monoid "univ_poly R"
    using univ_poly_is_abelian_monoid .
  show ?thesis
  proof (unfold_locales)
    show "carrier (add_monoid (univ_poly R)) \<subseteq> Units (add_monoid (univ_poly R))"
      unfolding univ_poly_def Units_def
    proof (auto)
      fix p assume p: "polynomial R p"
      have "polynomial R [ \<ominus> \<one> ]"
        unfolding polynomial_def using r_neg by fastforce 
      hence cond0: "polynomial R (poly_mult [ \<ominus> \<one> ] p)"
        using poly_mult_closed[of "[ \<ominus> \<one> ]" p] p by simp
      
      have "poly_add p (poly_mult [ \<ominus> \<one> ] p) = poly_add (poly_mult [ \<one> ] p) (poly_mult [ \<ominus> \<one> ] p)"
        using poly_mult_one[OF p] by simp
      also have " ... = poly_mult (poly_add [ \<one> ] [ \<ominus> \<one> ]) p"
        using poly_mult_l_distr' polynomial_in_carrier[OF p] by auto
      also have " ... = poly_mult [] p"
        using poly_add.simps[of "[ \<one> ]" "[ \<ominus> \<one> ]"]
        by (simp add: case_prod_unfold r_neg)
      also have " ... = []" by simp
      finally have cond1: "poly_add p (poly_mult [ \<ominus> \<one> ] p) = []" .

      have "poly_add (poly_mult [ \<ominus> \<one> ] p) p = poly_add (poly_mult [ \<ominus> \<one> ] p) (poly_mult [ \<one> ] p)"
        using poly_mult_one[OF p] by simp
      also have " ... = poly_mult (poly_add [ \<ominus>  \<one> ] [ \<one> ]) p"
        using poly_mult_l_distr' polynomial_in_carrier[OF p] by auto
      also have " ... = poly_mult [] p"
        using \<open>poly_mult (poly_add [\<one>] [\<ominus> \<one>]) p = poly_mult [] p\<close> poly_add_comm by auto
      also have " ... = []" by simp
      finally have cond2: "poly_add (poly_mult [ \<ominus> \<one> ] p) p = []" .

      from cond0 cond1 cond2 show "\<exists>q. polynomial R q \<and> poly_add q p = [] \<and> poly_add p q = []"
        by auto
    qed
  qed
qed

declare poly_add.simps[simp]

end

lemma univ_poly_is_ring:
  assumes "domain R"
  shows "ring (univ_poly R)"
proof -
  interpret abelian_group "univ_poly R" + monoid "univ_poly R"
    using domain.univ_poly_is_abelian_group[OF assms] domain.univ_poly_is_monoid[OF assms] .
  have R: "ring R"
    using assms unfolding domain_def cring_def by simp
  show ?thesis
    apply unfold_locales
    apply (auto simp add: univ_poly_def assms domain.poly_mult_r_distr ring.poly_mult_l_distr[OF R])
    done
qed

lemma univ_poly_is_cring:
  assumes "domain R"
  shows "cring (univ_poly R)"
proof -
  interpret ring "univ_poly R"
    using univ_poly_is_ring[OF assms] by simp
  have "\<And>p q. \<lbrakk> p \<in> carrier (univ_poly R); q \<in> carrier (univ_poly R) \<rbrakk> \<Longrightarrow>
                p \<otimes>\<^bsub>univ_poly R\<^esub> q = q \<otimes>\<^bsub>univ_poly R\<^esub> p"
    unfolding univ_poly_def polynomial_def using domain.poly_mult_comm[OF assms] by auto
  thus ?thesis
    by unfold_locales auto
qed

lemma univ_poly_is_domain:
  assumes "domain R"
  shows "domain (univ_poly R)"
proof -
  interpret cring "univ_poly R"
    using univ_poly_is_cring[OF assms] by simp
  show ?thesis
    by unfold_locales
      (auto simp add: univ_poly_def domain.poly_mult_integral[OF assms])
qed


subsection \<open>Long Division Theorem\<close>

lemma (in domain) long_division_theorem:
  assumes "polynomial R p" "polynomial R b" and "b \<noteq> []" and "lead_coeff b \<in> Units R"
  shows "\<exists>q r. polynomial R q \<and> polynomial R r \<and>
               p = poly_add (poly_mult b q) r \<and> (r = [] \<or> degree r < degree b)"
    (is "\<exists>q r. ?long_division p q r")
  using assms
proof (induct "length p" arbitrary: p rule: less_induct)
  case less thus ?case
  proof (cases p)
    case Nil
    hence "?long_division p [] []"
      using zero_is_polynomial poly_mult_zero[OF less(3)] by (simp add: degree_def)
    thus ?thesis by blast
  next
    case (Cons a p') thus ?thesis
    proof (cases "length b > length p")
      assume "length b > length p"
      hence "p = [] \<or> degree p < degree b" unfolding degree_def
        by (meson diff_less_mono length_0_conv less_one not_le) 
      hence "?long_division p [] p"
        using poly_add_zero[OF less(2)] less(2) zero_is_polynomial
              poly_mult_zero[OF less(3)] by simp
      thus ?thesis by blast
    next
      interpret UP: cring "univ_poly R"
        using univ_poly_is_cring[OF is_domain] .

      assume "\<not> length b > length p"
      hence len_ge: "length p \<ge> length b" by simp
      obtain c b' where b: "b = c # b'"
        using less(4) list.exhaust_sel by blast
      hence c: "c \<in> Units R" "c \<in> carrier R - { \<zero> }" and a: "a \<in> carrier R - { \<zero> }"
        using assms(4) less(2-3) Cons unfolding polynomial_def by auto
      hence "(\<ominus> a) \<in> carrier R - { \<zero> }"
        using r_neg by force
      hence in_carrier: "(\<ominus> a) \<otimes> inv c \<in> carrier R - { \<zero> }"
        using a c(2) Units_inv_closed[OF c(1)] Units_l_inv[OF c(1)]
             empty_iff insert_iff integral_iff m_closed
        by (metis Diff_iff zero_not_one)

      let ?len = "length"
      define s where "s = poly_mult (monon ((\<ominus> a) \<otimes> inv c) (?len p - ?len b)) b"
      hence s_coeff: "lead_coeff s = (\<ominus> a)"
        using poly_mult_lead_coeff[OF monon_is_polynomial[OF in_carrier] less(3)] a c
        unfolding monon_def s_def b using m_assoc by force
      
      have "degree s = degree (monon ((\<ominus> a) \<otimes> inv c) (?len p - ?len b)) + degree b"
        using poly_mult_degree_eq[OF monon_is_polynomial[OF in_carrier] less(3)]
        unfolding s_def b monon_def by auto
      hence "?len s - 1 = ?len p - 1"
        using len_ge unfolding b Cons by (simp add: monon_def degree_def)
      moreover have "s \<noteq> []"
        using poly_mult_integral[OF monon_is_polynomial[OF in_carrier] less(3)]
        unfolding s_def monon_def b by blast
      hence "?len s > 0" by simp
      ultimately have len_eq: "?len s  = ?len p"
        by (simp add: Nitpick.size_list_simp(2) local.Cons)

      obtain s' where s: "s = (\<ominus> a) # s'"
        using s_coeff len_eq by (metis \<open>s \<noteq> []\<close> hd_Cons_tl) 

      define p_diff where "p_diff = poly_add p s"
      hence "?len p_diff < ?len p"
        using len_eq s_coeff in_carrier a c unfolding s Cons apply simp
        by (metis le_imp_less_Suc length_map map_fst_zip normalize_length_le r_neg)
      moreover have "polynomial R p_diff" unfolding p_diff_def s_def
        using poly_mult_closed[OF monon_is_polynomial[OF in_carrier(1)] less(3)]
              poly_add_closed[OF less(2)] by simp
      ultimately
      obtain q' r' where l_div: "?long_division p_diff q' r'"
        using less(1)[of p_diff] less(3-5) by blast
      hence r': "polynomial R r'" and q': "polynomial R q'" by auto

      obtain m where m: "polynomial R m" "s = poly_mult m b"
        using s_def monon_is_polynomial[OF in_carrier(1)] by auto
      have in_univ_carrier:
         "p \<in> carrier (univ_poly R)"  "m \<in> carrier (univ_poly R)" "b \<in> carrier (univ_poly R)"
        "r' \<in> carrier (univ_poly R)" "q' \<in> carrier (univ_poly R)" 
        using r' q' less(2-3) m(1) unfolding univ_poly_def by auto

      hence "poly_add p (poly_mult m b) = poly_add (poly_mult b q') r'"
        using m l_div unfolding p_diff_def by simp
      hence "p \<oplus>\<^bsub>(univ_poly R)\<^esub> (m \<otimes>\<^bsub>(univ_poly R)\<^esub> b) = (b \<otimes>\<^bsub>(univ_poly R)\<^esub> q') \<oplus>\<^bsub>(univ_poly R)\<^esub> r'"
        unfolding univ_poly_def by auto
      hence
        "(p \<oplus>\<^bsub>(univ_poly R)\<^esub> (m \<otimes>\<^bsub>(univ_poly R)\<^esub> b)) \<ominus>\<^bsub>(univ_poly R)\<^esub> (m \<otimes>\<^bsub>(univ_poly R)\<^esub> b) =
        ((b \<otimes>\<^bsub>(univ_poly R)\<^esub>q') \<oplus>\<^bsub>(univ_poly R)\<^esub> r') \<ominus>\<^bsub>(univ_poly R)\<^esub> (m \<otimes>\<^bsub>(univ_poly R)\<^esub> b)"
        by simp
      hence "p = (b \<otimes>\<^bsub>(univ_poly R)\<^esub> (q' \<ominus>\<^bsub>(univ_poly R)\<^esub> m)) \<oplus>\<^bsub>(univ_poly R)\<^esub> r'" 
        using in_univ_carrier by algebra
      hence "p = poly_add (poly_mult b (q' \<ominus>\<^bsub>(univ_poly R)\<^esub> m)) r'"
        unfolding univ_poly_def by simp
      moreover have "q' \<ominus>\<^bsub>(univ_poly R)\<^esub> m \<in> carrier (univ_poly R)"
        using UP.ring_simprules in_univ_carrier by simp
      hence "polynomial R (q' \<ominus>\<^bsub>(univ_poly R)\<^esub> m)"
        unfolding univ_poly_def by simp
      ultimately have "?long_division p (q' \<ominus>\<^bsub>(univ_poly R)\<^esub> m) r'"
        using l_div r' by simp
      thus ?thesis by blast
    qed
  qed
qed

lemma (in field) field_long_division_theorem:
  assumes "polynomial R p" "polynomial R b" and "b \<noteq> []"
  shows "\<exists>q r. polynomial R q \<and> polynomial R r \<and>
               p = poly_add (poly_mult b q) r \<and> (r = [] \<or> degree r < degree b)"
  using long_division_theorem[OF assms] assms lead_coeff_not_zero[of "hd b" "tl b"]
  by (simp add: field_Units)

lemma univ_poly_is_euclidean_domain:
  assumes "field R"
  shows "euclidean_domain (univ_poly R) degree"
proof -
  interpret domain "univ_poly R"
    using univ_poly_is_domain assms field_def by blast
  show ?thesis
    apply (rule euclidean_domainI)
    unfolding univ_poly_def
    using field.field_long_division_theorem[OF assms] by auto
qed


subsection \<open>Consistency Rules\<close>

lemma (in ring) subring_is_ring: (* <- Move to Subrings.thy *)
  assumes "subring K R" shows "ring (R \<lparr> carrier := K \<rparr>)"
  using assms unfolding subring_iff[OF subringE(1)[OF assms]] .

lemma (in ring) eval_consistent [simp]:
  assumes "subring K R" shows "ring.eval (R \<lparr> carrier := K \<rparr>) = eval"
proof
  fix p show "ring.eval (R \<lparr> carrier := K \<rparr>) p = eval p"
    using nat_pow_consistent ring.eval.simps[OF subring_is_ring[OF assms]] by (induct p) (auto)
qed

lemma (in ring) coeff_consistent [simp]:
  assumes "subring K R" shows "ring.coeff (R \<lparr> carrier := K \<rparr>) = coeff"
proof
  fix p show "ring.coeff (R \<lparr> carrier := K \<rparr>) p = coeff p"
    using ring.coeff.simps[OF subring_is_ring[OF assms]] by (induct p) (auto)
qed

lemma (in ring) normalize_consistent [simp]:
  assumes "subring K R" shows "ring.normalize (R \<lparr> carrier := K \<rparr>) = normalize"
proof
  fix p show "ring.normalize (R \<lparr> carrier := K \<rparr>) p = normalize p"
    using ring.normalize.simps[OF subring_is_ring[OF assms]] by (induct p) (auto)
qed

lemma (in ring) poly_add_consistent [simp]:
  assumes "subring K R" shows "ring.poly_add (R \<lparr> carrier := K \<rparr>) = poly_add" 
proof -
  have "\<And>p q. ring.poly_add (R \<lparr> carrier := K \<rparr>) p q = poly_add p q"
  proof -
    fix p q show "ring.poly_add (R \<lparr> carrier := K \<rparr>) p q = poly_add p q"
    using ring.poly_add.simps[OF subring_is_ring[OF assms]] normalize_consistent[OF assms] by auto
  qed
  thus ?thesis by (auto simp del: poly_add.simps)
qed

lemma (in ring) poly_mult_consistent [simp]:
  assumes "subring K R" shows "ring.poly_mult (R \<lparr> carrier := K \<rparr>) = poly_mult"
proof -
  have "\<And>p q. ring.poly_mult (R \<lparr> carrier := K \<rparr>) p q = poly_mult p q"
  proof - 
    fix p q show "ring.poly_mult (R \<lparr> carrier := K \<rparr>) p q = poly_mult p q"
      using ring.poly_mult.simps[OF subring_is_ring[OF assms]] poly_add_consistent[OF assms]
      by (induct p) (auto)
  qed
  thus ?thesis by auto
qed

lemma (in ring) univ_poly_carrier_change_def':
  assumes "subring K R"
  shows "univ_poly (R \<lparr> carrier := K \<rparr>) = (univ_poly R) \<lparr> carrier := { p. polynomial R p \<and> set p \<subseteq> K } \<rparr>"
  unfolding univ_poly_def polynomial_def
  using poly_add_consistent[OF assms]
        poly_mult_consistent[OF assms]
        subringE(1)[OF assms]
  by auto


subsection \<open>The Evaluation Homomorphism\<close>

lemma (in ring) eval_replicate:
  assumes "set p \<subseteq> carrier R" "a \<in> carrier R"
  shows "eval ((replicate n \<zero>) @ p) a = eval p a"
  using assms eval_in_carrier by (induct n) (auto)

lemma (in ring) eval_normalize:
  assumes "set p \<subseteq> carrier R" "a \<in> carrier R"
  shows "eval (normalize p) a = eval p a"
  using eval_replicate[OF normalize_in_carrier] normalize_def'[of p] assms by metis

lemma (in ring) eval_poly_add_aux:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "length p = length q" and "a \<in> carrier R"
  shows "eval (poly_add p q) a = (eval p a) \<oplus> (eval q a)"
proof -
  have "eval (map2 (\<oplus>) p q) a = (eval p a) \<oplus> (eval q a)"
    using assms
  proof (induct p arbitrary: q)
    case Nil
    then show ?case by simp
  next
    case (Cons b1 p')
    then obtain b2 q' where q: "q = b2 # q'"
      by (metis length_Cons list.exhaust list.size(3) nat.simps(3))
    show ?case
      using eval_in_carrier[OF _ Cons(5), of q']
            eval_in_carrier[OF _ Cons(5), of p'] Cons unfolding q
      by (auto simp add: degree_def ring_simprules(7,13,22))
  qed
  moreover have "set (map2 (\<oplus>) p q) \<subseteq> carrier R"
    using assms(1-2)
    by (induct p arbitrary: q) (auto, metis add.m_closed in_set_zipE set_ConsD subsetCE)
  ultimately show ?thesis
    using assms(3) eval_normalize[OF _ assms(4), of "map2 (\<oplus>) p q"] by auto
qed

lemma (in ring) eval_poly_add:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "a \<in> carrier R"
  shows "eval (poly_add p q) a = (eval p a) \<oplus> (eval q a)"
proof -
  { fix p q assume A: "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" "length p \<ge> length q"
    hence "eval (poly_add p ((replicate (length p - length q) \<zero>) @ q)) a =
         (eval p a) \<oplus> (eval ((replicate (length p - length q) \<zero>) @ q) a)"
      using eval_poly_add_aux[OF A(1) _ _ assms(3), of "(replicate (length p - length q) \<zero>) @ q"] by force
    hence "eval (poly_add p q) a = (eval p a) \<oplus> (eval q a)"
      using eval_replicate[OF A(2) assms(3)] A(3) by auto }
  note aux_lemma = this

  have ?thesis if "length q \<ge> length p"
    using assms(1-2)[THEN eval_in_carrier[OF _ assms(3)]] poly_add_comm[OF assms(1-2)]
          aux_lemma[OF assms(2,1) that]
    by (auto simp del: poly_add.simps simp add: add.m_comm)
  moreover have ?thesis if "length p \<ge> length q"
    using aux_lemma[OF assms(1-2) that] .
  ultimately show ?thesis by auto
qed

lemma (in ring) eval_append_aux:
  assumes "set p \<subseteq> carrier R" and "b \<in> carrier R" and "a \<in> carrier R"
  shows "eval (p @ [ b ]) a = ((eval p a) \<otimes> a) \<oplus> b"
  using assms(1)
proof (induct p)
  case Nil thus ?case by (auto simp add: degree_def assms(2-3))
next
  case (Cons l q)
  have "a [^] length q \<in> carrier R" "eval q a \<in> carrier R"
    using eval_in_carrier Cons(2) assms(2-3) by auto
  thus ?case
    using Cons assms(2-3) by (auto simp add: degree_def, algebra)
qed

lemma (in ring) eval_append:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "a \<in> carrier R"
  shows "eval (p @ q) a = ((eval p a) \<otimes> (a [^] (length q))) \<oplus> (eval q a)"
  using assms(2)
proof (induct "length q" arbitrary: q)
  case 0 thus ?case
    using eval_in_carrier[OF assms(1,3)] by auto
next
  case (Suc n)
  then obtain b q' where q: "q = q' @ [ b ]"
    by (metis length_Suc_conv list.simps(3) rev_exhaust)
  hence in_carrier: "eval p a \<in> carrier R" "eval q' a \<in> carrier R"
                    "a [^] (length q') \<in> carrier R" "b \<in> carrier R"
    using assms(1,3) Suc(3) eval_in_carrier[OF _ assms(3)] by auto

  have "eval (p @ q) a = ((eval (p @ q') a) \<otimes> a) \<oplus> b"
    using eval_append_aux[OF _ _ assms(3), of "p @ q'" b] assms(1) Suc(3) unfolding q by auto
  also have " ... = ((((eval p a) \<otimes> (a [^] (length q'))) \<oplus> (eval q' a)) \<otimes> a) \<oplus> b"
    using Suc unfolding q by auto
  also have " ... = (((eval p a) \<otimes> ((a [^] (length q')) \<otimes> a))) \<oplus> (((eval q' a) \<otimes> a) \<oplus> b)"
    using assms(3) in_carrier by algebra
  also have " ... = (eval p a) \<otimes> (a [^] (length q)) \<oplus> (eval q a)"
    using eval_append_aux[OF _ in_carrier(4) assms(3), of q'] Suc(3) unfolding q by auto
  finally show ?case .
qed

lemma (in ring) eval_monon:
  assumes "b \<in> carrier R" and "a \<in> carrier R"
  shows "eval (monon b n) a = b \<otimes> (a [^] n)"
proof (induct n)
  case 0 thus ?case
    using assms unfolding monon_def by (auto simp add: degree_def)
next
  case (Suc n)
  have "monon b (Suc n) = (monon b n) @ [ \<zero> ]"
    unfolding monon_def by (simp add: replicate_append_same)
  hence "eval (monon b (Suc n)) a = ((eval (monon b n) a) \<otimes> a) \<oplus> \<zero>"
    using eval_append_aux[OF monon_in_carrier[OF assms(1)] zero_closed assms(2), of n] by simp
  also have " ... =  b \<otimes> (a [^] (Suc n))"
    using Suc assms m_assoc by auto
  finally show ?case .
qed

lemma (in cring) eval_poly_mult:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "a \<in> carrier R"
  shows "eval (poly_mult p q) a = (eval p a) \<otimes> (eval q a)"
  using assms(1)
proof (induct p)
  case Nil thus ?case
    using eval_in_carrier[OF assms(2-3)] by simp
next
  { fix n b assume b: "b \<in> carrier R"
    hence "set (map ((\<otimes>) b) q) \<subseteq> carrier R" and "set (replicate n \<zero>) \<subseteq> carrier R"
      using assms(2) by (induct q) (auto)
    hence "eval ((map ((\<otimes>) b) q) @ (replicate n \<zero>)) a = (eval ((map ((\<otimes>) b) q)) a) \<otimes> (a [^] n) \<oplus> \<zero>"
      using eval_append[OF _ _ assms(3), of "map ((\<otimes>) b) q" "replicate n \<zero>"] 
            eval_replicate[OF _ assms(3), of "[]"] by auto
    moreover have "eval (map ((\<otimes>) b) q) a = b \<otimes> eval q a"
      using assms(2-3) eval_in_carrier b by(induct q) (auto simp add: degree_def m_assoc r_distr)
    ultimately have "eval ((map ((\<otimes>) b) q) @ (replicate n \<zero>)) a = (b \<otimes> eval q a) \<otimes> (a [^] n) \<oplus> \<zero>"
      by simp
    also have " ... = (b \<otimes> (a [^] n)) \<otimes> (eval q a)"
      using eval_in_carrier[OF assms(2-3)] b assms(3) m_assoc m_comm by auto
    finally have "eval ((map ((\<otimes>) b) q) @ (replicate n \<zero>)) a = (eval (monon b n) a) \<otimes> (eval q a)"
      using eval_monon[OF b assms(3)] by simp }
  note aux_lemma = this

  case (Cons b p)
  hence in_carrier:
    "eval (monon b (length p)) a \<in> carrier R" "eval p a \<in> carrier R" "eval q a \<in> carrier R" "b \<in> carrier R"
    using eval_in_carrier monon_in_carrier assms by auto
  have set_map: "set ((map ((\<otimes>) b) q) @ (replicate (length p) \<zero>)) \<subseteq> carrier R"
    using in_carrier(4) assms(2) by (induct q) (auto)
  have set_poly: "set (poly_mult p q) \<subseteq> carrier R"
    using poly_mult_in_carrier[OF _ assms(2), of p] Cons(2) by auto
  have "eval (poly_mult (b # p) q) a =
      ((eval (monon b (length p)) a) \<otimes> (eval q a)) \<oplus> ((eval p a) \<otimes> (eval q a))"
    using eval_poly_add[OF set_map set_poly assms(3)] aux_lemma[OF in_carrier(4), of "length p"] Cons
    by (auto simp del: poly_add.simps simp add: degree_def)
  also have " ... = ((eval (monon b (length p)) a) \<oplus> (eval p a)) \<otimes> (eval q a)"
    using l_distr[OF in_carrier(1-3)] by simp
  also have " ... = (eval (b # p) a) \<otimes> (eval q a)"
    unfolding eval_monon[OF in_carrier(4) assms(3), of "length p"] by (auto simp add: degree_def)
  finally show ?case .
qed

proposition (in cring) eval_is_hom:
  assumes "subring K R" and "a \<in> carrier R"
  shows "(\<lambda>p. (eval p) a) \<in> ring_hom (univ_poly (R \<lparr> carrier := K \<rparr>)) R"
  unfolding univ_poly_carrier_change_def'[OF assms(1)]
  using polynomial_in_carrier eval_in_carrier eval_poly_add eval_poly_mult assms(2)
  by (auto intro!: ring_hom_memI
         simp add: univ_poly_def degree_def
         simp del: poly_add.simps poly_mult.simps)


end