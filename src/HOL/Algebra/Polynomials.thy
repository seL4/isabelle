(*  Title:      HOL/Algebra/Polynomials.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Polynomials
  imports Ring Ring_Divisibility Subrings

begin

section \<open>Polynomials\<close>

subsection \<open>Definitions\<close>

abbreviation lead_coeff :: "'a list \<Rightarrow> 'a"
  where "lead_coeff \<equiv> hd"

abbreviation degree :: "'a list \<Rightarrow> nat"
  where "degree p \<equiv> length p - 1"

definition polynomial :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" (\<open>polynomial\<index>\<close>)
  where "polynomial\<^bsub>R\<^esub> K p \<longleftrightarrow> p = [] \<or> (set p \<subseteq> K \<and> lead_coeff p \<noteq> \<zero>\<^bsub>R\<^esub>)"

definition (in ring) monom :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"
  where "monom a n = a # (replicate n \<zero>\<^bsub>R\<^esub>)"

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

fun (in ring) poly_of_dense :: "('a \<times> nat) list \<Rightarrow> 'a list"
  where "poly_of_dense dl = foldr (\<lambda>(a, n) l. poly_add (monom a n) l) dl []"

definition (in ring) poly_of_const :: "'a \<Rightarrow> 'a list"
  where "poly_of_const = (\<lambda>k. normalize [ k ])"


subsection \<open>Basic Properties\<close>

context ring
begin

lemma polynomialI [intro]: "\<lbrakk> set p \<subseteq> K; lead_coeff p \<noteq> \<zero> \<rbrakk> \<Longrightarrow> polynomial K p"
  unfolding polynomial_def by auto

lemma polynomial_incl: "polynomial K p \<Longrightarrow> set p \<subseteq> K"
  unfolding polynomial_def by auto

lemma monom_in_carrier [intro]: "a \<in> carrier R \<Longrightarrow> set (monom a n) \<subseteq> carrier R"
  unfolding monom_def by auto

lemma lead_coeff_not_zero: "polynomial K (a # p) \<Longrightarrow> a \<in> K - { \<zero> }"
  unfolding polynomial_def by simp

lemma zero_is_polynomial [intro]: "polynomial K []"
  unfolding polynomial_def by simp

lemma const_is_polynomial [intro]: "a \<in> K - { \<zero> } \<Longrightarrow> polynomial K [ a ]"
  unfolding polynomial_def by auto

lemma normalize_gives_polynomial: "set p \<subseteq> K \<Longrightarrow> polynomial K (normalize p)"
  by (induction p) (auto simp add: polynomial_def)

lemma normalize_in_carrier: "set p \<subseteq> carrier R \<Longrightarrow> set (normalize p) \<subseteq> carrier R"
  by (induction p) (auto)

lemma normalize_polynomial: "polynomial K p \<Longrightarrow> normalize p = p"
  unfolding polynomial_def by (cases p) (auto)

lemma normalize_idem: "normalize ((normalize p) @ q) = normalize (p @ q)"
  by (induct p) (auto)

lemma normalize_length_le: "length (normalize p) \<le> length p"
  by (induction p) (auto)

lemma eval_in_carrier: "\<lbrakk> set p \<subseteq> carrier R; x \<in> carrier R \<rbrakk> \<Longrightarrow> (eval p) x \<in> carrier R"
  by (induction p) (auto)

lemma coeff_in_carrier [simp]: "set p \<subseteq> carrier R \<Longrightarrow> (coeff p) i \<in> carrier R"
  by (induction p) (auto)

lemma lead_coeff_simp [simp]: "p \<noteq> [] \<Longrightarrow> (coeff p) (degree p) = lead_coeff p"
  by (metis coeff.simps(2) list.exhaust_sel)

lemma coeff_list: "map (coeff p) (rev [0..< length p]) = p"
proof (induction p)
  case Nil thus ?case by simp
next
  case (Cons a p)
  have "map (coeff (a # p)) (rev [0..<length (a # p)]) =
         a # (map (coeff p) (rev [0..<length p]))"
    by auto
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
  by (induction p) (auto)

lemma coeff_degree: "\<And>i. i > degree p \<Longrightarrow> (coeff p) i = \<zero>"
  using coeff_length by (simp)

lemma replicate_zero_coeff [simp]: "coeff (replicate n \<zero>) = (\<lambda>_. \<zero>)"
  by (induction n) (auto)

lemma scalar_coeff: "a \<in> carrier R \<Longrightarrow> coeff (map (\<lambda>b. a \<otimes> b) p) = (\<lambda>i. a \<otimes> (coeff p) i)"
  by (induction p) (auto)

lemma monom_coeff: "coeff (monom a n) = (\<lambda>i. if i = n then a else \<zero>)"
  unfolding monom_def by (induction n) (auto)

lemma coeff_img:
  "(coeff p) ` {..< length p} = set p"
  "(coeff p) ` { length p ..} = { \<zero> }"
  "(coeff p) ` UNIV = (set p) \<union> { \<zero> }"
  using coeff_img_restrict
proof (simp)
  show coeff_img_up: "(coeff p) ` { length p ..} = { \<zero> }"
    using coeff_length[of p] by force
  from coeff_img_up and coeff_img_restrict[of p]
  show "(coeff p) ` UNIV = (set p) \<union> { \<zero> }"
    by force
qed

lemma degree_def':
  assumes "polynomial K p"
  shows "degree p = (LEAST n. \<forall>i. i > n \<longrightarrow> (coeff p) i = \<zero>)"
proof (cases p)
  case Nil thus ?thesis by auto
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
  assumes "polynomial K p1" and "polynomial K p2"
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
      using deg_eq by (simp add: Nitpick.size_list_simp(2)) 
    thus ?thesis
      using coeff_iff_length_cond[of p1 p2] coeff_eq by simp
  next
    { fix p1 p2 assume A: "p1 = []" "coeff p1 = coeff p2" "polynomial K p2"
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

corollary normalize_trick:
  shows "p = (replicate (length p - length (normalize p)) \<zero>) @ (normalize p)"
  using normalize_def'(1)[of p] unfolding sym[OF normalize_def'(2)] .

lemma normalize_coeff: "coeff p = coeff (normalize p)"
proof (induction p)
  case Nil thus ?case by simp
next
  case (Cons a p)
  have "coeff (normalize p) (length p) = \<zero>"
    using normalize_length_le[of p] coeff_degree[of "normalize p"] coeff_length by blast
  then show ?case
    using Cons by (cases "a = \<zero>") (auto)
qed

lemma append_coeff:
  "coeff (p @ q) = (\<lambda>i. if i < length q then (coeff q) i else (coeff p) (i - length q))"
proof (induction p)
  case Nil thus ?case
    using coeff_length[of q] by auto
next
  case (Cons a p)
  have "coeff ((a # p) @ q) = (\<lambda>i. if i = length p + length q then a else (coeff (p @ q)) i)"
    by auto
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
    by auto
  finally show ?case .
qed

lemma prefix_replicate_zero_coeff: "coeff p = coeff ((replicate n \<zero>) @ p)"
  using append_coeff[of "replicate n \<zero>" p] replicate_zero_coeff[of n] coeff_length[of p] by auto

(* ========================================================================== *)
context
  fixes K :: "'a set" assumes K: "subring K R"
begin

lemma polynomial_in_carrier [intro]: "polynomial K p \<Longrightarrow> set p \<subseteq> carrier R"
  unfolding polynomial_def using subringE(1)[OF K] by auto

lemma carrier_polynomial [intro]: "polynomial K p \<Longrightarrow> polynomial (carrier R) p"
  unfolding polynomial_def using subringE(1)[OF K] by auto

lemma append_is_polynomial: "\<lbrakk> polynomial K p; p \<noteq> [] \<rbrakk> \<Longrightarrow> polynomial K (p @ (replicate n \<zero>))"
  unfolding polynomial_def using subringE(2)[OF K] by auto

lemma lead_coeff_in_carrier: "polynomial K (a # p) \<Longrightarrow> a \<in> carrier R - { \<zero> }"
  unfolding polynomial_def using subringE(1)[OF K] by auto

lemma monom_is_polynomial [intro]: "a \<in> K - { \<zero> } \<Longrightarrow> polynomial K (monom a n)"
  unfolding polynomial_def monom_def using subringE(2)[OF K] by auto

lemma eval_poly_in_carrier: "\<lbrakk> polynomial K p; x \<in> carrier R \<rbrakk> \<Longrightarrow> (eval p) x \<in> carrier R"
  using eval_in_carrier[OF polynomial_in_carrier] .

lemma poly_coeff_in_carrier [simp]: "polynomial K p \<Longrightarrow> coeff p i \<in> carrier R"
  using coeff_in_carrier[OF polynomial_in_carrier] .

end (* of fixed K context. *)
(* ========================================================================== *)


subsection \<open>Polynomial Addition\<close>

(* ========================================================================== *)
context
  fixes K :: "'a set" assumes K: "subring K R"
begin

lemma poly_add_is_polynomial:
  assumes "set p1 \<subseteq> K" and "set p2 \<subseteq> K"
  shows "polynomial K (poly_add p1 p2)"
proof -
  { fix p1 p2 assume A: "set p1 \<subseteq> K" "set p2 \<subseteq> K" "length p1 \<ge> length p2"
    hence "polynomial K (poly_add p1 p2)"
    proof -
      define p2' where "p2' = (replicate (length p1 - length p2) \<zero>) @ p2"
      hence "set p2' \<subseteq> K" and "length p1 = length p2'"
        using A(2-3) subringE(2)[OF K] by auto
      hence "set (map2 (\<oplus>) p1 p2') \<subseteq> K"
        using A(1) subringE(7)[OF K]
        by (induct p1) (auto, metis set_ConsD subsetD set_zip_leftD set_zip_rightD)
      thus ?thesis
        unfolding p2'_def using normalize_gives_polynomial A(3) by simp
    qed }
  thus ?thesis
    using assms by auto
qed

lemma poly_add_closed: "\<lbrakk> polynomial K p1; polynomial K p2 \<rbrakk> \<Longrightarrow> polynomial K (poly_add p1 p2)"
  using poly_add_is_polynomial polynomial_incl by simp

lemma poly_add_length_eq:
  assumes "polynomial K p1" "polynomial K p2" and "length p1 \<noteq> length p2"
  shows "length (poly_add p1 p2) = max (length p1) (length p2)"
proof -
  { fix p1 p2 assume A: "polynomial K p1" "polynomial K p2" "length p1 > length p2"
    hence "length (poly_add p1 p2) = max (length p1) (length p2)"
    proof -
      let ?p2 = "(replicate (length p1 - length p2) \<zero>) @ p2"
      have p1: "p1 \<noteq> []" and p2: "?p2 \<noteq> []"
        using A(3) by auto
      then have "zip p1 (replicate (length p1 - length p2) \<zero> @ p2) = zip (lead_coeff p1 # tl p1) (lead_coeff (replicate (length p1 - length p2) \<zero> @ p2) # tl (replicate (length p1 - length p2) \<zero> @ p2))"
        by auto
      hence "lead_coeff (map2 (\<oplus>) p1 ?p2) = lead_coeff p1 \<oplus> lead_coeff ?p2"
        by simp
      moreover have "lead_coeff p1 \<in> carrier R"
        using p1 A(1) lead_coeff_in_carrier[OF K, of "hd p1" "tl p1"] by auto
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

lemma poly_add_degree_eq:
  assumes "polynomial K p1" "polynomial K p2" and "degree p1 \<noteq> degree p2"
  shows "degree (poly_add p1 p2) = max (degree p1) (degree p2)"
  using poly_add_length_eq[OF assms(1-2)] assms(3) by simp

end (* of fixed K context. *)
(* ========================================================================== *)

lemma poly_add_in_carrier:
  "\<lbrakk> set p1 \<subseteq> carrier R; set p2 \<subseteq> carrier R \<rbrakk> \<Longrightarrow> set (poly_add p1 p2) \<subseteq> carrier R"
  using polynomial_incl[OF poly_add_is_polynomial[OF carrier_is_subring]] by simp

lemma poly_add_length_le: "length (poly_add p1 p2) \<le> max (length p1) (length p2)"
proof -
  { fix p1 p2 :: "'a list" assume A: "length p1 \<ge> length p2"
    let ?p2 = "(replicate (length p1 - length p2) \<zero>) @ p2"
    have "length (poly_add p1 p2) \<le> max (length p1) (length p2)"
      using normalize_length_le[of "map2 (\<oplus>) p1 ?p2"] A by auto }
  thus ?thesis
    by (metis le_cases max.commute poly_add.simps)
qed

lemma poly_add_degree: "degree (poly_add p1 p2) \<le> max (degree p1) (degree p2)"
  using poly_add_length_le by (meson diff_le_mono le_max_iff_disj)

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
    using coeff_iff_polynomial_cond[OF
          poly_add_is_polynomial[OF carrier_is_subring assms] 
          poly_add_is_polynomial[OF carrier_is_subring assms(2,1)]] by simp 
qed

lemma poly_add_monom:
  assumes "set p \<subseteq> carrier R" and "a \<in> carrier R - { \<zero> }"
  shows "poly_add (monom a (length p)) p = a # p"
  unfolding monom_def using assms by (induction p) (auto)

lemma poly_add_append_replicate:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R"
  shows "poly_add (p @ (replicate (length q) \<zero>)) q = normalize (p @ q)"
proof -
  have "map2 (\<oplus>) (p @ (replicate (length q) \<zero>)) ((replicate (length p) \<zero>) @ q) = p @ q"
    using assms by (induct p) (induct q, auto)
  thus ?thesis by simp
qed

lemma poly_add_append_zero:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R"
  shows "poly_add (p @ [ \<zero> ]) (q @ [ \<zero> ]) = normalize ((poly_add p q) @ [ \<zero> ])"
proof -
  have in_carrier: "set (p @ [ \<zero> ]) \<subseteq> carrier R" "set (q @ [ \<zero> ]) \<subseteq> carrier R"
    using assms by auto
  have "coeff (poly_add (p @ [ \<zero> ]) (q @ [ \<zero> ])) = coeff ((poly_add p q) @ [ \<zero> ])"
    using append_coeff[of p "[ \<zero> ]"] poly_add_coeff[OF in_carrier]
          append_coeff[of q "[ \<zero> ]"] append_coeff[of "poly_add p q" "[ \<zero> ]"]
          poly_add_coeff[OF assms] assms[THEN coeff_in_carrier] by auto
  hence "coeff (poly_add (p @ [ \<zero> ]) (q @ [ \<zero> ])) = coeff (normalize ((poly_add p q) @ [ \<zero> ]))"
    using normalize_coeff by simp
  moreover have "set ((poly_add p q) @ [ \<zero> ]) \<subseteq> carrier R"
    using poly_add_in_carrier[OF assms] by simp
  ultimately show ?thesis
    using coeff_iff_polynomial_cond[OF poly_add_is_polynomial[OF carrier_is_subring in_carrier]
          normalize_gives_polynomial] by simp
qed

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
    using aux_lemma[OF normalize_in_carrier[OF assms(1)] assms(2)] by simp
  finally show ?thesis .
qed

lemma poly_add_normalize:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_add p1 p2 = poly_add (normalize p1) p2"
    and "poly_add p1 p2 = poly_add p1 (normalize p2)"
    and "poly_add p1 p2 = poly_add (normalize p1) (normalize p2)"
proof -
  show "poly_add p1 p2 = poly_add p1 (normalize p2)"
    unfolding poly_add_comm[OF assms] poly_add_normalize_aux[OF assms(2) assms(1)]
              poly_add_comm[OF normalize_in_carrier[OF assms(2)] assms(1)] by simp 
next
  show "poly_add p1 p2 = poly_add (normalize p1) p2"
    using poly_add_normalize_aux[OF assms] .
  also have " ... = poly_add (normalize p2) (normalize p1)"
    unfolding  poly_add_comm[OF normalize_in_carrier[OF assms(1)] assms(2)]
               poly_add_normalize_aux[OF assms(2) normalize_in_carrier[OF assms(1)]] by simp
  finally show "poly_add p1 p2 = poly_add (normalize p1) (normalize p2)"
    unfolding  poly_add_comm[OF assms[THEN normalize_in_carrier]] .
qed

lemma poly_add_zero':
  assumes "set p \<subseteq> carrier R"
  shows "poly_add p [] = normalize p" and "poly_add [] p = normalize p"
proof -
  have "map2 (\<oplus>) p (replicate (length p) \<zero>) = p"
    using assms by (induct p) (auto)
  thus "poly_add p [] = normalize p" and "poly_add [] p = normalize p"
    using poly_add_comm[OF assms, of "[]"] by simp+
qed

lemma poly_add_zero:
  assumes "subring K R" "polynomial K p"
  shows "poly_add p [] = p" and "poly_add [] p = p"
  using poly_add_zero' normalize_polynomial polynomial_in_carrier assms by auto

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
  assumes "subring K R" "polynomial K p"
  shows "poly_add p (replicate n \<zero>) = p" and "poly_add (replicate n \<zero>) p = p"
  using poly_add_replicate_zero' normalize_polynomial polynomial_in_carrier assms by auto



subsection \<open>Dense Representation\<close>

lemma dense_repr_replicate_zero: "dense_repr ((replicate n \<zero>) @ p) = dense_repr p"
  by (induction n) (auto)

lemma dense_repr_normalize: "dense_repr (normalize p) = dense_repr p"
  by (induct p) (auto)

lemma polynomial_dense_repr:
  assumes "polynomial K p" and "p \<noteq> []"
  shows "dense_repr p = (lead_coeff p, degree p) # dense_repr (normalize (tl p))"
proof -
  let ?len = length and ?norm = normalize
  obtain a p' where p: "p = a # p'"
    using assms(2) list.exhaust_sel by blast 
  hence a: "a \<in> K - { \<zero> }" and p': "set p' \<subseteq> K"
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

lemma monom_decomp:
  assumes "subring K R" "polynomial K p"
  shows "p = poly_of_dense (dense_repr p)"
  using assms(2)
proof (induct "length p" arbitrary: p rule: less_induct)
  case less thus ?case
  proof (cases p)
    case Nil thus ?thesis by simp
  next
    case (Cons a l)
    hence a: "a \<in> carrier R - { \<zero> }" and l: "set l \<subseteq> carrier R"  "set l \<subseteq> K"
      using less(2) subringE(1)[OF assms(1)] by (auto simp add: polynomial_def)
    hence "a # l = poly_add (monom a (degree (a # l))) l"
      using poly_add_monom[of l a] by simp
    also have " ... = poly_add (monom a (degree (a # l))) (normalize l)"
      using poly_add_normalize(2)[of "monom a (degree (a # l))", OF _ l(1)] a
      unfolding monom_def by force
    also have " ... = poly_add (monom a (degree (a # l))) (poly_of_dense (dense_repr (normalize l)))"
      using less(1)[OF _ normalize_gives_polynomial[OF l(2)]] normalize_length_le[of l]
      unfolding Cons by simp
    also have " ... = poly_of_dense ((a, degree (a # l)) # dense_repr (normalize l))"
      by simp
    also have " ... = poly_of_dense (dense_repr (a # l))"
      using polynomial_dense_repr[OF less(2)] unfolding Cons by simp
    finally show ?thesis
      unfolding Cons by simp
  qed
qed


subsection \<open>Polynomial Multiplication\<close>

lemma poly_mult_is_polynomial:
  assumes "subring K R" "set p1 \<subseteq> K" and "set p2 \<subseteq> K"
  shows "polynomial K (poly_mult p1 p2)"
  using assms(2-3)
proof (induction p1)
  case Nil thus ?case
    by (simp add: polynomial_def)
next
  case (Cons a p1)
  let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (degree (a # p1)) \<zero>)"
  
  have "set (poly_mult p1 p2) \<subseteq> K"
    using Cons unfolding polynomial_def by auto
  moreover have "set ?a_p2 \<subseteq> K"
      using assms(3) Cons(2) subringE(1-2,6)[OF assms(1)] by(induct p2) (auto)
  ultimately have "polynomial K (poly_add ?a_p2 (poly_mult p1 p2))"
    using poly_add_is_polynomial[OF assms(1)] by blast
  thus ?case by simp
qed

lemma poly_mult_closed:
  assumes "subring K R"
  shows "\<lbrakk> polynomial K p1; polynomial K p2 \<rbrakk> \<Longrightarrow> polynomial K (poly_mult p1 p2)"
  using poly_mult_is_polynomial polynomial_incl assms by simp

lemma poly_mult_in_carrier:
  "\<lbrakk> set p1 \<subseteq> carrier R; set p2 \<subseteq> carrier R \<rbrakk> \<Longrightarrow> set (poly_mult p1 p2) \<subseteq> carrier R"
  using poly_mult_is_polynomial polynomial_in_carrier carrier_is_subring by simp

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
    using prefix_replicate_zero_coeff[of "[]" "length p1"] by auto
  hence "coeff ?a_p2 = (\<lambda>i. if i < length p1 then \<zero> else (coeff (map (\<lambda>b. a \<otimes> b) p2)) (i - length p1))"
    using append_coeff[of "map (\<lambda>b. a \<otimes> b) p2" "replicate (length p1) \<zero>"] by auto
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
    using poly_mult_in_carrier[OF _ assms(2)] Cons(2) by simp

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
      using in_carrier coeff_length[of p1] by auto
    thus "(\<Oplus> k \<in> {..i}. ?f i k) = (\<Oplus> k \<in> {..i}. ?g i k)" by simp
  qed
  finally show ?case .
qed

lemma poly_mult_zero:
  assumes "set p \<subseteq> carrier R"
  shows "poly_mult [] p = []" and "poly_mult p [] = []"
proof (simp)
  have "coeff (poly_mult p []) = (\<lambda>_. \<zero>)"
    using poly_mult_coeff[OF assms, of "[]"] coeff_in_carrier[OF assms] by auto
  thus "poly_mult p [] = []"
    using coeff_iff_polynomial_cond[OF
          poly_mult_is_polynomial[OF carrier_is_subring assms] zero_is_polynomial] by simp
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
  moreover have "polynomial (carrier R) (poly_mult (poly_add p1 p2) p3)"
            and "polynomial (carrier R) (poly_add (poly_mult p1 p3) (poly_mult p2 p3))"
    using assms poly_add_is_polynomial poly_mult_is_polynomial polynomial_in_carrier
          carrier_is_subring by auto
  ultimately show ?thesis
    using coeff_iff_polynomial_cond by auto 
qed

lemma poly_mult_l_distr:
  assumes "subring K R" "polynomial K p1" "polynomial K p2" "polynomial K p3"
  shows "poly_mult (poly_add p1 p2) p3 = poly_add (poly_mult p1 p3) (poly_mult p2 p3)"
  using poly_mult_l_distr' polynomial_in_carrier assms by auto

lemma poly_mult_prepend_replicate_zero:
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
        by simp
      also have " ... = poly_add (normalize (replicate (length p2 + length p1) \<zero>)) (poly_mult p1 p2)"
        using poly_add_normalize(1)[of "replicate (length p2 + length p1) \<zero>" "poly_mult p1 p2"]
              poly_mult_in_carrier[OF A] by force
      also have " ... = poly_mult p1 p2"
        using poly_add_zero(2)[OF _ poly_mult_is_polynomial[OF _ A]] carrier_is_subring
              normalize_replicate_zero[of "length p2 + length p1" "[]"] by simp
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
  thus ?thesis
    using poly_mult_prepend_replicate_zero normalize_in_carrier assms by auto
qed

lemma poly_mult_append_zero:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R"
  shows "poly_mult (p @ [ \<zero> ]) q = normalize ((poly_mult p q) @ [ \<zero> ])"
  using assms(1)
proof (induct p)
  case Nil thus ?case
    using poly_mult_normalize[OF _ assms(2), of "[] @ [ \<zero> ]"]
          poly_mult_zero(1) poly_mult_zero(1)[of "q @ [ \<zero> ]"] assms(2) by auto
next
  case (Cons a p)
  let ?q_a = "\<lambda>n. (map ((\<otimes>) a) q) @ (replicate n \<zero>)"
  have set_q_a: "\<And>n. set (?q_a n) \<subseteq> carrier R"
    using Cons(2) assms(2) by (induct q) (auto)
  have set_poly_mult: "set ((poly_mult p q) @ [ \<zero> ]) \<subseteq> carrier R"
    using poly_mult_in_carrier[OF _ assms(2)] Cons(2) by auto
  have "poly_mult ((a # p) @ [\<zero>]) q = poly_add (?q_a (Suc (length p))) (poly_mult (p @ [\<zero>]) q)"
    by auto
  also have " ... = poly_add (?q_a (Suc (length p))) (normalize ((poly_mult p q) @ [ \<zero> ]))"
    using Cons by simp
  also have " ... = poly_add ((?q_a (length p)) @ [ \<zero> ]) ((poly_mult p q) @ [ \<zero> ])"
    using poly_add_normalize(2)[OF set_q_a[of "Suc (length p)"] set_poly_mult]
    by (simp add: replicate_append_same)
  also have " ... = normalize ((poly_add (?q_a (length p)) (poly_mult p q)) @ [ \<zero> ])"
    using poly_add_append_zero[OF set_q_a[of "length p"] poly_mult_in_carrier[OF _ assms(2)]] Cons(2) by auto
  also have " ... = normalize ((poly_mult (a # p) q) @ [ \<zero> ])"
    by auto
  finally show ?case .
qed

end (* of ring context. *)


subsection \<open>Properties Within a Domain\<close>

context domain
begin

lemma one_is_polynomial [intro]: "subring K R \<Longrightarrow> polynomial K [ \<one> ]"
  unfolding polynomial_def using subringE(3) by auto

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
    using poly_mult_coeff[OF assms] poly_mult_coeff[OF assms(2,1)] by simp
  thus ?thesis
    using coeff_iff_polynomial_cond[OF poly_mult_is_polynomial[OF _ assms]
                                       poly_mult_is_polynomial[OF _ assms(2,1)]]
          carrier_is_subring by simp
qed

lemma poly_mult_r_distr':
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "set p3 \<subseteq> carrier R"
  shows "poly_mult p1 (poly_add p2 p3) = poly_add (poly_mult p1 p2) (poly_mult p1 p3)"
  unfolding poly_mult_comm[OF assms(1) poly_add_in_carrier[OF assms(2-3)]]
            poly_mult_l_distr'[OF assms(2-3,1)] assms(2-3)[THEN poly_mult_comm[OF _ assms(1)]] ..

lemma poly_mult_r_distr:
  assumes "subring K R" "polynomial K p1" "polynomial K p2" "polynomial K p3"
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
      using Suc by simp
    also have " ... = poly_add ((map (\<lambda>a. \<zero>) p) @ (replicate n \<zero>)) []"
    proof -
      have "map ((\<otimes>) \<zero>) p = map (\<lambda>a. \<zero>) p"
        using Suc.prems by auto
      then show ?thesis
        by presburger
    qed
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

lemma poly_mult_const':
  assumes "set p \<subseteq> carrier R" "a \<in> carrier R"
  shows "poly_mult [ a ] p = normalize (map (\<lambda>b. a \<otimes> b) p)"
    and "poly_mult p [ a ] = normalize (map (\<lambda>b. a \<otimes> b) p)"
proof -
  have "map2 (\<oplus>) (map ((\<otimes>) a) p) (replicate (length p) \<zero>) = map ((\<otimes>) a) p"
    using assms by (induction p) (auto)
  thus "poly_mult [ a ] p = normalize (map (\<lambda>b. a \<otimes> b) p)" by simp
  thus "poly_mult p [ a ] = normalize (map (\<lambda>b. a \<otimes> b) p)"
    using poly_mult_comm[OF assms(1), of "[ a ]"] assms(2) by auto
qed

lemma poly_mult_const:
  assumes "subring K R" "polynomial K p" "a \<in> K - { \<zero> }"
  shows "poly_mult [ a ] p = map (\<lambda>b. a \<otimes> b) p"
    and "poly_mult p [ a ] = map (\<lambda>b. a \<otimes> b) p"
proof -
  have in_carrier: "set p \<subseteq> carrier R" "a \<in> carrier R"
    using polynomial_in_carrier[OF assms(1-2)] assms(3) subringE(1)[OF assms(1)] by auto

  show "poly_mult [ a ] p = map (\<lambda>b. a \<otimes> b) p"
  proof (cases p)
    case Nil thus ?thesis
      using poly_mult_const'(1) in_carrier by auto
  next
    case (Cons b q)
    have "lead_coeff (map (\<lambda>b. a \<otimes> b) p) \<noteq> \<zero>"
      using assms subringE(1)[OF assms(1)] integral[of a b] Cons lead_coeff_in_carrier by auto
    hence "normalize (map (\<lambda>b. a \<otimes> b) p) = (map (\<lambda>b. a \<otimes> b) p)"
      unfolding Cons by simp
    thus ?thesis
      using poly_mult_const'(1) in_carrier by auto
  qed
  thus "poly_mult p [ a ] = map (\<lambda>b. a \<otimes> b) p"
    using poly_mult_comm[OF in_carrier(1)] in_carrier(2) by auto
qed

lemma poly_mult_semiassoc:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "a \<in> carrier R"
  shows "poly_mult (poly_mult [ a ] p) q = poly_mult [ a ] (poly_mult p q)"
proof -
  let ?cp = "coeff p" and ?cq = "coeff q"
  have "coeff (poly_mult [ a ] p) = (\<lambda>i. (a \<otimes> ?cp i))"
    using poly_mult_const'(1)[OF assms(1,3)] normalize_coeff scalar_coeff[OF assms(3)] by simp

  hence "coeff (poly_mult (poly_mult [ a ] p) q) = (\<lambda>i. (\<Oplus>j \<in> {..i}. (a \<otimes> ?cp j) \<otimes> ?cq (i - j)))"
    using poly_mult_coeff[OF poly_mult_in_carrier[OF _ assms(1)] assms(2), of "[ a ]"] assms(3) by auto
  also have " ... = (\<lambda>i. a \<otimes> (\<Oplus>j \<in> {..i}. ?cp j \<otimes> ?cq (i - j)))"
  proof
    fix i show "(\<Oplus>j \<in> {..i}. (a \<otimes> ?cp j) \<otimes> ?cq (i - j)) = a \<otimes> (\<Oplus>j \<in> {..i}. ?cp j \<otimes> ?cq (i - j))"
      using finsum_rdistr[OF _ assms(3), of _ "\<lambda>j. ?cp j \<otimes> ?cq (i - j)"]
            assms(1-2)[THEN coeff_in_carrier] by (simp add: assms(3) m_assoc)
  qed
  also have " ... = coeff (poly_mult [ a ] (poly_mult p q))"
    unfolding poly_mult_const'(1)[OF poly_mult_in_carrier[OF assms(1-2)] assms(3)]
    using scalar_coeff[OF assms(3), of "poly_mult p q"]
          poly_mult_coeff[OF assms(1-2)] normalize_coeff by simp
  finally have "coeff (poly_mult (poly_mult [ a ] p) q) = coeff (poly_mult [ a ] (poly_mult p q))" .
  moreover have "polynomial (carrier R) (poly_mult (poly_mult [ a ] p) q)"
            and "polynomial (carrier R) (poly_mult [ a ] (poly_mult p q))"
    using poly_mult_is_polynomial[OF _ poly_mult_in_carrier[OF _ assms(1)] assms(2)]
          poly_mult_is_polynomial[OF _ _ poly_mult_in_carrier[OF assms(1-2)]]
          carrier_is_subring assms(3) by (auto simp del: poly_mult.simps)
  ultimately show ?thesis
    using coeff_iff_polynomial_cond by simp
qed


text \<open>Note that "polynomial (carrier R) p" and "subring K p; polynomial K p" are "equivalent"
      assumptions for any lemma in ring which the result doesn't depend on K, because carrier
      is a subring and a polynomial for a subset of the carrier is a carrier polynomial. The
      decision between one of them should be based on how the lemma is going to be used and
      proved. These are some tips:
        (a) Lemmas about the algebraic structure of polynomials should use the latter option.
        (b) Also, if the lemma deals with lots of polynomials, then the latter option is preferred.
        (c) If the proof is going to be much easier with the first option, do not hesitate. \<close>

lemma poly_mult_monom':
  assumes "set p \<subseteq> carrier R" "a \<in> carrier R"
  shows "poly_mult (monom a n) p = normalize ((map ((\<otimes>) a) p) @ (replicate n \<zero>))"
proof -
  have set_map: "set ((map ((\<otimes>) a) p) @ (replicate n \<zero>)) \<subseteq> carrier R"
    using assms by (induct p) (auto)
  show ?thesis
  using poly_mult_replicate_zero(1)[OF assms(1), of n]
        poly_add_zero'(1)[OF set_map]
  unfolding monom_def by simp
qed

lemma poly_mult_monom:
  assumes "polynomial (carrier R) p" "a \<in> carrier R - { \<zero> }"
  shows "poly_mult (monom a n) p =
           (if p = [] then [] else (poly_mult [ a ] p) @ (replicate n \<zero>))"
proof (cases p)
  case Nil thus ?thesis
    using poly_mult_zero(2)[of "monom a n"] assms(2) monom_def by fastforce
next
  case (Cons b ps)
  hence "lead_coeff ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)) \<noteq> \<zero>"
    using Cons assms integral[of a b] unfolding polynomial_def by auto
  thus ?thesis
    using poly_mult_monom'[OF polynomial_incl[OF assms(1)], of a n] assms(2) Cons
    unfolding poly_mult_const(1)[OF carrier_is_subring assms] by simp
qed

lemma poly_mult_one':
  assumes "set p \<subseteq> carrier R"
  shows "poly_mult [ \<one> ] p = normalize p" and "poly_mult p [ \<one> ] = normalize p"
proof -
  have "map2 (\<oplus>) (map ((\<otimes>) \<one>) p) (replicate (length p) \<zero>) = p"
    using assms by (induct p) (auto)
  thus "poly_mult [ \<one> ] p = normalize p" and "poly_mult p [ \<one> ] = normalize p"
    using poly_mult_comm[OF assms, of "[ \<one> ]"] by auto
qed

lemma poly_mult_one:
  assumes "subring K R" "polynomial K p"
  shows "poly_mult [ \<one> ] p = p" and "poly_mult p [ \<one> ] = p"
  using poly_mult_one'[OF polynomial_in_carrier[OF assms]] normalize_polynomial[OF assms(2)] by auto

lemma poly_mult_lead_coeff_aux:
  assumes "subring K R" "polynomial K p1" "polynomial K p2" and "p1 \<noteq> []" and "p2 \<noteq> []"
  shows "(coeff (poly_mult p1 p2)) (degree p1 + degree p2) = (lead_coeff p1) \<otimes> (lead_coeff p2)"
proof -
  have p1: "lead_coeff p1 \<in> carrier R - { \<zero> }" and p2: "lead_coeff p2 \<in> carrier R - { \<zero> }"
    using assms(2-5) lead_coeff_in_carrier[OF assms(1)] by (metis list.collapse)+

  have "(coeff (poly_mult p1 p2)) (degree p1 + degree p2) = 
        (\<Oplus> k \<in> {..((degree p1) + (degree p2))}.
          (coeff p1) k \<otimes> (coeff p2) ((degree p1) + (degree p2) - k))"
    using poly_mult_coeff[OF assms(2-3)[THEN polynomial_in_carrier[OF assms(1)]]] by simp
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
      using assms(4-5) lead_coeff_simp by simp 
    ultimately have "?f = (\<lambda>i. if degree p1 = i then (lead_coeff p1) \<otimes> (lead_coeff p2) else \<zero>)"
      using nat_neq_iff by auto
    thus ?thesis
      using add.finprod_singleton[of "degree p1" "{..((degree p1) + (degree p2))}"
                                     "\<lambda>i. (lead_coeff p1) \<otimes> (lead_coeff p2)"] p1 p2 by auto
  qed
  finally show ?thesis .
qed

lemma poly_mult_degree_eq:
  assumes "subring K R" "polynomial K p1" "polynomial K p2"
  shows "degree (poly_mult p1 p2) = (if p1 = [] \<or> p2 = [] then 0 else (degree p1) + (degree p2))"
proof (cases p1)
  case Nil thus ?thesis by simp
next
  case (Cons a p1') note p1 = Cons
  show ?thesis
  proof (cases p2)
    case Nil thus ?thesis
      using poly_mult_zero(2)[OF polynomial_in_carrier[OF assms(1-2)]] by simp
  next
    case (Cons b p2') note p2 = Cons
    have a: "a \<in> carrier R" and b: "b \<in> carrier R"
      using p1 p2 polynomial_in_carrier[OF assms(1-2)] polynomial_in_carrier[OF assms(1,3)] by auto
    have "(coeff (poly_mult p1 p2)) ((degree p1) + (degree p2)) = a \<otimes> b"
      using poly_mult_lead_coeff_aux[OF assms] p1 p2 by simp
    hence neq0: "(coeff (poly_mult p1 p2)) ((degree p1) + (degree p2)) \<noteq> \<zero>"
      using assms(2-3) integral[of a b] lead_coeff_in_carrier[OF assms(1)] p1 p2 by auto  
    moreover have eq0: "\<And>i. i > (degree p1) + (degree p2) \<Longrightarrow> (coeff (poly_mult p1 p2)) i = \<zero>"
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
          by auto
        also have " ... \<le> max ((degree (a # p1)) + (degree p2)) ((degree p1) + (degree p2))"
          using Cons by simp
        also have " ... \<le> (degree (a # p1)) + (degree p2)"
          by auto
        finally show ?case .
      qed
      fix i show "i > (degree p1) + (degree p2) \<Longrightarrow> (coeff (poly_mult p1 p2)) i = \<zero>"
        using coeff_degree aux_lemma by simp
    qed
    moreover have "polynomial K (poly_mult p1 p2)"
        by (simp add: assms poly_mult_closed)
    ultimately have "degree (poly_mult p1 p2) = degree p1 + degree p2"
      by (metis (no_types) assms(1) coeff.simps(1) coeff_degree domain.poly_mult_one(1) domain_axioms eq0 lead_coeff_simp length_greater_0_conv neq0 normalize_length_lt not_less_iff_gr_or_eq poly_mult_one'(1) polynomial_in_carrier)
    thus ?thesis
      using p1 p2 by auto
  qed
qed

lemma poly_mult_integral:
  assumes "subring K R" "polynomial K p1" "polynomial K p2"
  shows "poly_mult p1 p2 = [] \<Longrightarrow> p1 = [] \<or> p2 = []"
proof (rule ccontr)
  assume A: "poly_mult p1 p2 = []" "\<not> (p1 = [] \<or> p2 = [])"
  hence "degree (poly_mult p1 p2) = degree p1 + degree p2"
    using poly_mult_degree_eq[OF assms] by simp
  hence "length p1 = 1 \<and> length p2 = 1"
    using A Suc_diff_Suc by fastforce
  then obtain a b where p1: "p1 = [ a ]" and p2: "p2 = [ b ]"
    by (metis One_nat_def length_0_conv length_Suc_conv)
  hence "a \<in> carrier R - { \<zero> }" and "b \<in> carrier R - { \<zero> }"
    using assms lead_coeff_in_carrier by auto
  hence "poly_mult [ a ] [ b ] = [ a \<otimes> b ]"
    using integral by auto
  thus False using A(1) p1 p2 by simp
qed

lemma poly_mult_lead_coeff:
  assumes "subring K R" "polynomial K p1" "polynomial K p2" and "p1 \<noteq> []" and "p2 \<noteq> []"
  shows "lead_coeff (poly_mult p1 p2) = (lead_coeff p1) \<otimes> (lead_coeff p2)"
proof -
  have "poly_mult p1 p2 \<noteq> []"
    using poly_mult_integral[OF assms(1-3)] assms(4-5) by auto
  hence "lead_coeff (poly_mult p1 p2) = (coeff (poly_mult p1 p2)) (degree p1 + degree p2)"
    using poly_mult_degree_eq[OF assms(1-3)] assms(4-5) by (metis coeff.simps(2) list.collapse)
  thus ?thesis
    using poly_mult_lead_coeff_aux[OF assms] by simp
qed

lemma poly_mult_append_zero_lcancel:
  assumes "subring K R" and "polynomial K p" "polynomial K q"
  shows "poly_mult (p @ [ \<zero> ]) q = r @ [ \<zero> ] \<Longrightarrow> poly_mult p q = r"
proof -
  note in_carrier = assms(2-3)[THEN polynomial_in_carrier[OF assms(1)]]

  assume pmult: "poly_mult (p @ [ \<zero> ]) q = r @ [ \<zero> ]"
  have "poly_mult (p @ [ \<zero> ]) q = []" if "q = []"
    using poly_mult_zero(2)[of "p @ [ \<zero> ]"] that in_carrier(1) by auto
  moreover have "poly_mult (p @ [ \<zero> ]) q = []" if "p = []"
    using poly_mult_normalize[OF _ in_carrier(2), of "p @ [ \<zero> ]"] poly_mult_zero[OF in_carrier(2)]
    unfolding that by auto
  ultimately have "p \<noteq> []" and "q \<noteq> []"
    using pmult by auto
  hence "poly_mult p q \<noteq> []"
    using poly_mult_integral[OF assms] by auto
  hence "normalize ((poly_mult p q) @ [ \<zero> ]) = (poly_mult p q) @ [ \<zero> ]"
    using normalize_polynomial[OF append_is_polynomial[OF assms(1) poly_mult_closed[OF assms], of "Suc 0"]] by auto
  thus "poly_mult p q = r"
    using poly_mult_append_zero[OF assms(2-3)[THEN polynomial_in_carrier[OF assms(1)]]] pmult by simp
qed

lemma poly_mult_append_zero_rcancel:
  assumes "subring K R" and "polynomial K p" "polynomial K q"
  shows "poly_mult p (q @ [ \<zero> ]) = r @ [ \<zero> ] \<Longrightarrow> poly_mult p q = r"
  using poly_mult_append_zero_lcancel[OF assms(1,3,2)]
        poly_mult_comm[of p "q @ [ \<zero> ]"] poly_mult_comm[of p q]
        assms(2-3)[THEN polynomial_in_carrier[OF assms(1)]]
  by auto

end (* of domain context. *)


subsection \<open>Algebraic Structure of Polynomials\<close>

definition univ_poly :: "('a, 'b) ring_scheme \<Rightarrow>'a set \<Rightarrow> ('a list) ring"
    (\<open>(\<open>open_block notation=\<open>postfix X\<close>\<close>_ [X]\<index>)\<close> 80)
  where "univ_poly R K =
           \<lparr> carrier = { p. polynomial\<^bsub>R\<^esub> K p },
                mult = ring.poly_mult R,
                 one = [ \<one>\<^bsub>R\<^esub> ],
                zero = [],
                 add = ring.poly_add R \<rparr>"


text \<open>These lemmas allow you to unfold one field of the record at a time. \<close>

lemma univ_poly_carrier: "polynomial\<^bsub>R\<^esub> K p \<longleftrightarrow> p \<in> carrier (K[X]\<^bsub>R\<^esub>)"
  unfolding univ_poly_def by simp

lemma univ_poly_mult: "mult (K[X]\<^bsub>R\<^esub>) = ring.poly_mult R"
  unfolding univ_poly_def by simp

lemma univ_poly_one: "one (K[X]\<^bsub>R\<^esub>) = [ \<one>\<^bsub>R\<^esub> ]"
  unfolding univ_poly_def by simp

lemma univ_poly_zero: "zero (K[X]\<^bsub>R\<^esub>) = []"
  unfolding univ_poly_def by simp

lemma univ_poly_add: "add (K[X]\<^bsub>R\<^esub>) = ring.poly_add R"
  unfolding univ_poly_def by simp


(* NEW  ========== *)
lemma univ_poly_zero_closed [intro]: "[] \<in> carrier (K[X]\<^bsub>R\<^esub>)"
  unfolding sym[OF univ_poly_carrier] polynomial_def by simp


context domain
begin

lemma poly_mult_monom_assoc:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "a \<in> carrier R"
    shows "poly_mult (poly_mult (monom a n) p) q =
           poly_mult (monom a n) (poly_mult p q)"
proof (induct n)
  case 0 thus ?case
    unfolding monom_def using poly_mult_semiassoc[OF assms] by (auto simp del: poly_mult.simps)
next
  case (Suc n)
  have "poly_mult (poly_mult (monom a (Suc n)) p) q =
        poly_mult (normalize ((poly_mult (monom a n) p) @ [ \<zero> ])) q"
    using poly_mult_append_zero[OF monom_in_carrier[OF assms(3), of n] assms(1)]
    unfolding monom_def by (auto simp del: poly_mult.simps simp add: replicate_append_same)
  also have " ... = normalize ((poly_mult (poly_mult (monom a n) p) q) @ [ \<zero> ])"
    using poly_mult_normalize[OF _ assms(2)] poly_mult_append_zero[OF _ assms(2)]
          poly_mult_in_carrier[OF monom_in_carrier[OF assms(3), of n] assms(1)] by auto
  also have " ... = normalize ((poly_mult (monom a n) (poly_mult p q)) @ [ \<zero> ])"
    using Suc by simp
  also have " ... = poly_mult (monom a (Suc n)) (poly_mult p q)"
    using poly_mult_append_zero[OF monom_in_carrier[OF assms(3), of n]
                                   poly_mult_in_carrier[OF assms(1-2)]]
    unfolding monom_def by (simp add: replicate_append_same)
  finally show ?case .
qed


context
  fixes K :: "'a set" assumes K: "subring K R"
begin

lemma univ_poly_is_monoid: "monoid (K[X])"
  unfolding univ_poly_def using poly_mult_one[OF K]
proof (auto simp add: K poly_add_closed poly_mult_closed one_is_polynomial monoid_def)
  fix p1 p2 p3
  let ?P = "poly_mult (poly_mult p1 p2) p3 = poly_mult p1 (poly_mult p2 p3)"

  assume A: "polynomial K p1" "polynomial K p2" "polynomial K p3"
  show ?P using polynomial_in_carrier[OF K A(1)]
  proof (induction p1)
    case Nil thus ?case by simp
  next
next
    case (Cons a p1) thus ?case
    proof (cases "a = \<zero>")
      assume eq_zero: "a = \<zero>"
      have p1: "set p1 \<subseteq> carrier R"
        using Cons(2) by simp
      have "poly_mult (poly_mult (a # p1) p2) p3 = poly_mult (poly_mult p1 p2) p3"
        using poly_mult_prepend_replicate_zero[OF p1 polynomial_in_carrier[OF K A(2)], of "Suc 0"]
              eq_zero by simp
      also have " ... = poly_mult p1 (poly_mult p2 p3)"
        using p1[THEN Cons(1)] by simp
      also have " ... = poly_mult (a # p1) (poly_mult p2 p3)"
        using poly_mult_prepend_replicate_zero[OF p1
              poly_mult_in_carrier[OF A(2-3)[THEN polynomial_in_carrier[OF K]]], of "Suc 0"] eq_zero
        by simp
      finally show ?thesis .
    next
      assume "a \<noteq> \<zero>" hence in_carrier:
        "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "set p3 \<subseteq> carrier R" "a \<in> carrier R - { \<zero> }"
        using A(2-3) polynomial_in_carrier[OF K] Cons by auto

      let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (length p1) \<zero>)"
      have a_p2_in_carrier: "set ?a_p2 \<subseteq> carrier R"
        using in_carrier by auto

      have "poly_mult (poly_mult (a # p1) p2) p3 = poly_mult (poly_add ?a_p2 (poly_mult p1 p2)) p3"
        by simp
      also have " ... = poly_add (poly_mult ?a_p2 p3) (poly_mult (poly_mult p1 p2) p3)"
        using poly_mult_l_distr'[OF a_p2_in_carrier poly_mult_in_carrier[OF in_carrier(1-2)] in_carrier(3)] .
      also have " ... = poly_add (poly_mult ?a_p2 p3) (poly_mult p1 (poly_mult p2 p3))"
        using Cons(1)[OF in_carrier(1)] by simp
      also have " ... = poly_add (poly_mult (normalize ?a_p2) p3) (poly_mult p1 (poly_mult p2 p3))"
        using poly_mult_normalize[OF a_p2_in_carrier in_carrier(3)] by simp
      also have " ... = poly_add (poly_mult (poly_mult (monom a (length p1)) p2) p3)
                                 (poly_mult p1 (poly_mult p2 p3))"
        using poly_mult_monom'[OF in_carrier(2), of a "length p1"] in_carrier(4) by simp
      also have " ... = poly_add (poly_mult (a # (replicate (length p1) \<zero>)) (poly_mult p2 p3))
                                 (poly_mult p1 (poly_mult p2 p3))"
        using poly_mult_monom_assoc[of p2 p3 a "length p1"] in_carrier unfolding monom_def by simp
      also have " ... = poly_mult (poly_add (a # (replicate (length p1) \<zero>)) p1) (poly_mult p2 p3)"
        using poly_mult_l_distr'[of "a # (replicate (length p1) \<zero>)" p1 "poly_mult p2 p3"]
              poly_mult_in_carrier[OF in_carrier(2-3)] in_carrier by force
      also have " ... = poly_mult (a # p1) (poly_mult p2 p3)"
        using poly_add_monom[OF in_carrier(1) in_carrier(4)] unfolding monom_def by simp
      finally show ?thesis .
    qed
  qed
qed

declare poly_add.simps[simp del]

lemma univ_poly_is_abelian_monoid: "abelian_monoid (K[X])"
  unfolding univ_poly_def
  using poly_add_closed poly_add_zero zero_is_polynomial K
proof (auto simp add: abelian_monoid_def comm_monoid_def monoid_def comm_monoid_axioms_def)
  fix p1 p2 p3
  let ?c = "\<lambda>p. coeff p"
  assume A: "polynomial K p1" "polynomial K p2" "polynomial K p3"
  hence
    p1: "\<And>i. (?c p1) i \<in> carrier R" "set p1 \<subseteq> carrier R" and
    p2: "\<And>i. (?c p2) i \<in> carrier R" "set p2 \<subseteq> carrier R" and
    p3: "\<And>i. (?c p3) i \<in> carrier R" "set p3 \<subseteq> carrier R"
    using A[THEN polynomial_in_carrier[OF K]] coeff_in_carrier by auto
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
    using coeff_iff_polynomial_cond poly_add_closed[OF K] A by meson
  show "poly_add p1 p2 = poly_add p2 p1"
    using poly_add_comm[OF p1(2) p2(2)] .
qed

lemma univ_poly_is_abelian_group: "abelian_group (K[X])"
proof -
  interpret abelian_monoid "K[X]"
    using univ_poly_is_abelian_monoid .
  show ?thesis
  proof (unfold_locales)
    show "carrier (add_monoid (K[X])) \<subseteq> Units (add_monoid (K[X]))"
      unfolding univ_poly_def Units_def
    proof (auto)
      fix p assume p: "polynomial K p"
      have "polynomial K [ \<ominus> \<one> ]"
        unfolding polynomial_def using r_neg subringE(3,5)[OF K] by force
      hence cond0: "polynomial K (poly_mult [ \<ominus> \<one> ] p)"
        using poly_mult_closed[OF K, of "[ \<ominus> \<one> ]" p] p by simp
      
      have "poly_add p (poly_mult [ \<ominus> \<one> ] p) = poly_add (poly_mult [ \<one> ] p) (poly_mult [ \<ominus> \<one> ] p)"
        using poly_mult_one[OF K p] by simp
      also have " ... = poly_mult (poly_add [ \<one> ] [ \<ominus> \<one> ]) p"
        using poly_mult_l_distr' polynomial_in_carrier[OF K p] by auto
      also have " ... = poly_mult [] p"
        using poly_add.simps[of "[ \<one> ]" "[ \<ominus> \<one> ]"]
        by (simp add: case_prod_unfold r_neg)
      also have " ... = []" by simp
      finally have cond1: "poly_add p (poly_mult [ \<ominus> \<one> ] p) = []" .

      have "poly_add (poly_mult [ \<ominus> \<one> ] p) p = poly_add (poly_mult [ \<ominus> \<one> ] p) (poly_mult [ \<one> ] p)"
        using poly_mult_one[OF K p] by simp
      also have " ... = poly_mult (poly_add [ \<ominus>  \<one> ] [ \<one> ]) p"
        using poly_mult_l_distr' polynomial_in_carrier[OF K p] by auto
      also have " ... = poly_mult [] p"
        using \<open>poly_mult (poly_add [\<one>] [\<ominus> \<one>]) p = poly_mult [] p\<close> poly_add_comm by auto
      also have " ... = []" by simp
      finally have cond2: "poly_add (poly_mult [ \<ominus> \<one> ] p) p = []" .

      from cond0 cond1 cond2 show "\<exists>q. polynomial K q \<and> poly_add q p = [] \<and> poly_add p q = []"
        by auto
    qed
  qed
qed

lemma univ_poly_is_ring: "ring (K[X])"
proof -
  interpret UP: abelian_group "K[X]" + monoid "K[X]"
    using univ_poly_is_abelian_group univ_poly_is_monoid .
  show ?thesis
    by (unfold_locales)
       (auto simp add: univ_poly_def poly_mult_r_distr[OF K] poly_mult_l_distr[OF K])
qed

lemma univ_poly_is_cring: "cring (K[X])"
proof -
  interpret UP: ring "K[X]"
    using univ_poly_is_ring .
  have "\<And>p q. \<lbrakk> p \<in> carrier (K[X]); q \<in> carrier (K[X]) \<rbrakk> \<Longrightarrow> p \<otimes>\<^bsub>K[X]\<^esub> q = q \<otimes>\<^bsub>K[X]\<^esub> p"
    unfolding univ_poly_def using poly_mult_comm polynomial_in_carrier[OF K] by auto
  thus ?thesis
    by unfold_locales auto
qed

lemma univ_poly_is_domain: "domain (K[X])"
proof -
  interpret UP: cring "K[X]"
    using univ_poly_is_cring .
  show ?thesis
    by (unfold_locales, auto simp add: univ_poly_def poly_mult_integral[OF K])
qed

declare poly_add.simps[simp]

lemma univ_poly_a_inv_def':
  assumes "p \<in> carrier (K[X])" shows "\<ominus>\<^bsub>K[X]\<^esub> p = map (\<lambda>a. \<ominus> a) p"
proof -
  have aux_lemma:
    "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> p \<oplus>\<^bsub>K[X]\<^esub> (map (\<lambda>a. \<ominus> a) p) = []"
    "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> (map (\<lambda>a. \<ominus> a) p) \<in> carrier (K[X])"
  proof -
    fix p assume p: "p \<in> carrier (K[X])"
    hence set_p: "set p \<subseteq> K"
      unfolding univ_poly_def using polynomial_incl by auto
    show "(map (\<lambda>a. \<ominus> a) p) \<in> carrier (K[X])"
    proof (cases "p = []")
      assume "p = []" thus ?thesis
        unfolding univ_poly_def polynomial_def by auto
    next
      assume not_nil: "p \<noteq> []"
      hence "lead_coeff p \<noteq> \<zero>"
        using p unfolding univ_poly_def polynomial_def by auto
      moreover have "lead_coeff (map (\<lambda>a. \<ominus> a) p) = \<ominus> (lead_coeff p)"
        using not_nil by (simp add: hd_map)
      ultimately have "lead_coeff (map (\<lambda>a. \<ominus> a) p) \<noteq> \<zero>"
        using hd_in_set local.minus_zero not_nil set_p subringE(1)[OF K] by force
      moreover have "set (map (\<lambda>a. \<ominus> a) p) \<subseteq> K"
        using set_p subringE(5)[OF K] by (induct p) (auto)
      ultimately show ?thesis
        unfolding univ_poly_def polynomial_def by simp
    qed

    have "map2 (\<oplus>) p (map (\<lambda>a. \<ominus> a) p) = replicate (length p) \<zero>"
      using set_p subringE(1)[OF K] by (induct p) (auto simp add: r_neg)
    thus "p \<oplus>\<^bsub>K[X]\<^esub> (map (\<lambda>a. \<ominus> a) p) = []"
      unfolding univ_poly_def using normalize_replicate_zero[of "length p" "[]"] by auto
  qed

  interpret UP: ring "K[X]"
    using univ_poly_is_ring .

  from aux_lemma
  have "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> \<ominus>\<^bsub>K[X]\<^esub> p = map (\<lambda>a. \<ominus> a) p"
    by (metis Nil_is_map_conv UP.add.inv_closed UP.l_zero UP.r_neg1 UP.r_zero UP.zero_closed)
  thus ?thesis
    using assms by simp
qed

(* NEW ========== *)
corollary univ_poly_a_inv_length:
  assumes "p \<in> carrier (K[X])" shows "length (\<ominus>\<^bsub>K[X]\<^esub> p) = length p"
  unfolding univ_poly_a_inv_def'[OF assms] by simp

(* NEW ========== *)
corollary univ_poly_a_inv_degree:
  assumes "p \<in> carrier (K[X])" shows "degree (\<ominus>\<^bsub>K[X]\<^esub> p) = degree p"
  using univ_poly_a_inv_length[OF assms] by simp


subsection \<open>Long Division Theorem\<close>

lemma long_division_theorem:
  assumes "polynomial K p" and "polynomial K b" "b \<noteq> []"
     and "lead_coeff b \<in> Units (R \<lparr> carrier := K \<rparr>)"
  shows "\<exists>q r. polynomial K q \<and> polynomial K r \<and>
               p = (b \<otimes>\<^bsub>K[X]\<^esub> q) \<oplus>\<^bsub>K[X]\<^esub> r \<and> (r = [] \<or> degree r < degree b)"
    (is "\<exists>q r. ?long_division p q r")
  using assms(1)
proof (induct "length p" arbitrary: p rule: less_induct)
  case less thus ?case
  proof (cases p)
    case Nil
    hence "?long_division p [] []"
      using zero_is_polynomial poly_mult_zero[OF polynomial_in_carrier[OF K assms(2)]]
      by (simp add: univ_poly_def)
    thus ?thesis by blast
  next
    case (Cons a p') thus ?thesis
    proof (cases "length b > length p")
      assume "length b > length p"
      hence "p = [] \<or> degree p < degree b"
        by (meson diff_less_mono length_0_conv less_one not_le) 
      hence "?long_division p [] p"
        using poly_mult_zero(2)[OF polynomial_in_carrier[OF K assms(2)]]
              poly_add_zero(2)[OF K less(2)] zero_is_polynomial less(2)
        by (simp add: univ_poly_def)
      thus ?thesis by blast
    next
      interpret UP: cring "K[X]"
        using univ_poly_is_cring .

      assume "\<not> length b > length p"
      hence len_ge: "length p \<ge> length b" by simp
      obtain c b' where b: "b = c # b'"
        using assms(3) list.exhaust_sel by blast
      then obtain c' where c': "c' \<in> carrier R" "c' \<in> K" "c' \<otimes> c = \<one>" "c \<otimes> c' = \<one>"
        using assms(4) subringE(1)[OF K] unfolding Units_def by auto
      have c: "c \<in> carrier R" "c \<in> K" "c \<noteq> \<zero>" and a: "a \<in> carrier R" "a \<in> K" "a \<noteq> \<zero>"
        using less(2) assms(2) lead_coeff_not_zero subringE(1)[OF K] b Cons by auto
      hence lc: "c' \<otimes> (\<ominus> a) \<in> K - { \<zero> }"
        using subringE(5-6)[OF K] c' add.inv_solve_right integral_iff by fastforce

      let ?len = "length"
      define s where "s = monom (c' \<otimes> (\<ominus> a)) (?len p - ?len b)"
      hence s: "polynomial K s" "s \<noteq> []" "degree s = ?len p - ?len b" "length s \<ge> 1"
        using monom_is_polynomial[OF K lc] unfolding monom_def by auto
      hence is_polynomial: "polynomial K (p \<oplus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s))"
        using poly_add_closed[OF K less(2) poly_mult_closed[OF K assms(2), of s]]
        by (simp add: univ_poly_def)

      have "lead_coeff (b \<otimes>\<^bsub>K[X]\<^esub> s) = \<ominus> a"
        using poly_mult_lead_coeff[OF K assms(2) s(1) assms(3) s(2)] c c' a
        unfolding b s_def monom_def univ_poly_def by (auto simp del: poly_mult.simps, algebra)
      then obtain s' where s': "b \<otimes>\<^bsub>K[X]\<^esub> s = (\<ominus> a) # s'"
        using poly_mult_integral[OF K assms(2) s(1)] assms(2-3) s(2)
        by (simp add: univ_poly_def, metis hd_Cons_tl)
      moreover have "degree p = degree (b \<otimes>\<^bsub>K[X]\<^esub> s)"
        using poly_mult_degree_eq[OF K assms(2) s(1)] assms(3) s(2-4) len_ge b Cons
        by (auto simp add: univ_poly_def)
      hence "?len p = ?len (b \<otimes>\<^bsub>K[X]\<^esub> s)"
        unfolding Cons s' by simp
      hence "?len (p \<oplus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s)) < ?len p"
        unfolding Cons s' using a normalize_length_le[of "map2 (\<oplus>) p' s'"]
        by (auto simp add: univ_poly_def r_neg)
      then obtain q' r' where l_div: "?long_division (p \<oplus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s)) q' r'"
        using less(1)[OF _ is_polynomial] by blast

      have in_carrier:
         "p \<in> carrier (K[X])"  "b \<in> carrier (K[X])" "s \<in> carrier (K[X])"
        "q' \<in> carrier (K[X])" "r' \<in> carrier (K[X])"
        using l_div assms less(2) s unfolding univ_poly_def by auto
      have "(p \<oplus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s)) \<ominus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s) =
          ((b \<otimes>\<^bsub>K[X]\<^esub> q') \<oplus>\<^bsub>K[X]\<^esub> r') \<ominus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s)"
        using l_div by simp
      hence "p = (b \<otimes>\<^bsub>K[X]\<^esub> (q' \<ominus>\<^bsub>K[X]\<^esub> s)) \<oplus>\<^bsub>K[X]\<^esub> r'"
        using in_carrier by algebra
      moreover have "q' \<ominus>\<^bsub>K[X]\<^esub> s \<in> carrier (K[X])"
        using in_carrier by algebra
      hence "polynomial K (q' \<ominus>\<^bsub>K[X]\<^esub> s)"
        unfolding univ_poly_def by simp
      ultimately have "?long_division p (q' \<ominus>\<^bsub>K[X]\<^esub> s) r'"
        using l_div by auto
      thus ?thesis by blast
    qed
  qed
qed

end (* of fixed K context. *)

end (* of domain context. *)

(* PROOF ========== *)
lemma (in domain) field_long_division_theorem:
  assumes "subfield K R" "polynomial K p" and "polynomial K b" "b \<noteq> []"
  shows "\<exists>q r. polynomial K q \<and> polynomial K r \<and>
               p = (b \<otimes>\<^bsub>K[X]\<^esub> q) \<oplus>\<^bsub>K[X]\<^esub> r \<and> (r = [] \<or> degree r < degree b)"
  using long_division_theorem[OF subfieldE(1)[OF assms(1)] assms(2-4)] assms(3-4)
        subfield.subfield_Units[OF assms(1)] lead_coeff_not_zero[of K "hd b" "tl b"]
  by simp

(* PROOF ========== *)
text \<open>The same theorem as above, but now, everything is in a shell. \<close>
lemma (in domain) field_long_division_theorem_shell:
  assumes "subfield K R" "p \<in> carrier (K[X])" and "b \<in> carrier (K[X])" "b \<noteq> \<zero>\<^bsub>K[X]\<^esub>"
  shows "\<exists>q r. q \<in> carrier (K[X]) \<and> r \<in> carrier (K[X]) \<and>
               p = (b \<otimes>\<^bsub>K[X]\<^esub> q) \<oplus>\<^bsub>K[X]\<^esub> r \<and> (r = \<zero>\<^bsub>K[X]\<^esub> \<or> degree r < degree b)"
  using field_long_division_theorem assms by (auto simp add: univ_poly_def)


subsection \<open>Consistency Rules\<close>

lemma polynomial_consistent [simp]:
  shows "polynomial\<^bsub>(R \<lparr> carrier := K \<rparr>)\<^esub> K p \<Longrightarrow> polynomial\<^bsub>R\<^esub> K p"
  unfolding polynomial_def by auto

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

lemma (in domain) univ_poly_a_inv_consistent:
  assumes "subring K R" "p \<in> carrier (K[X])"
  shows "\<ominus>\<^bsub>K[X]\<^esub> p = \<ominus>\<^bsub>(carrier R)[X]\<^esub> p"
proof -
  have in_carrier: "p \<in> carrier ((carrier R)[X])"
    using assms carrier_polynomial by (auto simp add: univ_poly_def)
  show ?thesis
    using univ_poly_a_inv_def'[OF assms]
          univ_poly_a_inv_def'[OF carrier_is_subring in_carrier] by simp
qed

lemma (in domain) univ_poly_a_minus_consistent:
  assumes "subring K R" "q \<in> carrier (K[X])"
  shows "p \<ominus>\<^bsub>K[X]\<^esub> q = p \<ominus>\<^bsub>(carrier R)[X]\<^esub> q"
  using univ_poly_a_inv_consistent[OF assms]
  unfolding a_minus_def univ_poly_def by auto

lemma (in ring) univ_poly_consistent:
  assumes "subring K R"
  shows "univ_poly (R \<lparr> carrier := K \<rparr>) = univ_poly R"
  unfolding univ_poly_def polynomial_def
  using poly_add_consistent[OF assms]
        poly_mult_consistent[OF assms]
        subringE(1)[OF assms]
  by auto


subsubsection \<open>Corollaries\<close>

(* PROOF ========== *)
corollary (in ring) subfield_long_division_theorem_shell:
  assumes "subfield K R" "p \<in> carrier (K[X])" and "b \<in> carrier (K[X])" "b \<noteq> \<zero>\<^bsub>K[X]\<^esub>"
  shows "\<exists>q r. q \<in> carrier (K[X]) \<and> r \<in> carrier (K[X]) \<and>
               p = (b \<otimes>\<^bsub>K[X]\<^esub> q) \<oplus>\<^bsub>K[X]\<^esub> r \<and> (r = \<zero>\<^bsub>K[X]\<^esub> \<or> degree r < degree b)"
  using domain.field_long_division_theorem_shell[OF subdomain_is_domain[OF subfield.axioms(1)]
        field.carrier_is_subfield[OF subfield_iff(2)[OF assms(1)]]] assms(1-4)
  unfolding univ_poly_consistent[OF subfieldE(1)[OF assms(1)]]
  by auto

corollary (in domain) univ_poly_is_euclidean:
  assumes "subfield K R" shows "euclidean_domain (K[X]) degree"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF assms]] field_def by blast
  show ?thesis
    using subfield_long_division_theorem_shell[OF assms]
    by (auto intro!: UP.euclidean_domainI)
qed

corollary (in domain) univ_poly_is_principal:
  assumes "subfield K R" shows "principal_domain (K[X])"
proof -
  interpret UP: euclidean_domain "K[X]" degree
    using univ_poly_is_euclidean[OF assms] .
  show ?thesis ..
qed


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
    case Nil thus ?case by simp
  next
    case (Cons b1 p')
    then obtain b2 q' where q: "q = b2 # q'"
      by (metis length_Cons list.exhaust list.size(3) nat.simps(3))
    show ?case
      using eval_in_carrier[OF _ Cons(5), of q']
            eval_in_carrier[OF _ Cons(5), of p'] Cons unfolding q
      by (auto simp add: ring_simprules(7,13,22))
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
  case Nil thus ?case by (auto simp add: assms(2-3))
next
  case (Cons l q)
  have "a [^] length q \<in> carrier R" "eval q a \<in> carrier R"
    using eval_in_carrier Cons(2) assms(2-3) by auto
  thus ?case
    using Cons assms(2-3) by (auto, algebra)
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

lemma (in ring) eval_monom:
  assumes "b \<in> carrier R" and "a \<in> carrier R"
  shows "eval (monom b n) a = b \<otimes> (a [^] n)"
proof (induct n)
  case 0 thus ?case
    using assms unfolding monom_def by auto
next
  case (Suc n)
  have "monom b (Suc n) = (monom b n) @ [ \<zero> ]"
    unfolding monom_def by (simp add: replicate_append_same)
  hence "eval (monom b (Suc n)) a = ((eval (monom b n) a) \<otimes> a) \<oplus> \<zero>"
    using eval_append_aux[OF monom_in_carrier[OF assms(1)] zero_closed assms(2), of n] by simp
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
      using assms(2-3) eval_in_carrier b by(induct q) (auto simp add: m_assoc r_distr)
    ultimately have "eval ((map ((\<otimes>) b) q) @ (replicate n \<zero>)) a = (b \<otimes> eval q a) \<otimes> (a [^] n) \<oplus> \<zero>"
      by simp
    also have " ... = (b \<otimes> (a [^] n)) \<otimes> (eval q a)"
      using eval_in_carrier[OF assms(2-3)] b assms(3) m_assoc m_comm by auto
    finally have "eval ((map ((\<otimes>) b) q) @ (replicate n \<zero>)) a = (eval (monom b n) a) \<otimes> (eval q a)"
      using eval_monom[OF b assms(3)] by simp }
  note aux_lemma = this

  case (Cons b p)
  hence in_carrier:
    "eval (monom b (length p)) a \<in> carrier R" "eval p a \<in> carrier R" "eval q a \<in> carrier R" "b \<in> carrier R"
    using eval_in_carrier monom_in_carrier assms by auto
  have set_map: "set ((map ((\<otimes>) b) q) @ (replicate (length p) \<zero>)) \<subseteq> carrier R"
    using in_carrier(4) assms(2) by (induct q) (auto)
  have set_poly: "set (poly_mult p q) \<subseteq> carrier R"
    using poly_mult_in_carrier[OF _ assms(2), of p] Cons(2) by auto
  have "eval (poly_mult (b # p) q) a =
      ((eval (monom b (length p)) a) \<otimes> (eval q a)) \<oplus> ((eval p a) \<otimes> (eval q a))"
    using eval_poly_add[OF set_map set_poly assms(3)] aux_lemma[OF in_carrier(4), of "length p"] Cons
    by (auto simp del: poly_add.simps)
  also have " ... = ((eval (monom b (length p)) a) \<oplus> (eval p a)) \<otimes> (eval q a)"
    using l_distr[OF in_carrier(1-3)] by simp
  also have " ... = (eval (b # p) a) \<otimes> (eval q a)"
    unfolding eval_monom[OF in_carrier(4) assms(3), of "length p"] by auto
  finally show ?case .
qed

proposition (in cring) eval_is_hom:
  assumes "subring K R" and "a \<in> carrier R"
  shows "(\<lambda>p. (eval p) a) \<in> ring_hom (K[X]) R"
  unfolding univ_poly_def
  using polynomial_in_carrier[OF assms(1)] eval_in_carrier
        eval_poly_add eval_poly_mult assms(2)
  by (auto intro!: ring_hom_memI
         simp add: univ_poly_carrier
         simp del: poly_add.simps poly_mult.simps)

theorem (in domain) eval_cring_hom:
  assumes "subring K R" and "a \<in> carrier R"
  shows "ring_hom_cring (K[X]) R (\<lambda>p. (eval p) a)"
  unfolding ring_hom_cring_def ring_hom_cring_axioms_def
  using domain.axioms(1)[OF univ_poly_is_domain[OF assms(1)]]
        eval_is_hom[OF assms] cring_axioms by auto

corollary (in domain) eval_ring_hom:
  assumes "subring K R" and "a \<in> carrier R"
  shows "ring_hom_ring (K[X]) R (\<lambda>p. (eval p) a)"
  using eval_cring_hom[OF assms] ring_hom_ringI2
  unfolding ring_hom_cring_def ring_hom_cring_axioms_def cring_def by auto


subsection \<open>Homomorphisms\<close>

lemma (in ring_hom_ring) eval_hom':
  assumes "a \<in> carrier R" and "set p \<subseteq> carrier R"
  shows "h (R.eval p a) = eval (map h p) (h a)"
  using assms by (induct p, auto simp add: R.eval_in_carrier hom_nat_pow)

lemma (in ring_hom_ring) eval_hom:
  assumes "subring K R" and "a \<in> carrier R" and "p \<in> carrier (K[X])"
  shows "h (R.eval p a) = eval (map h p) (h a)"
proof -
  have "set p \<subseteq> carrier R"
    using subringE(1)[OF assms(1)] R.polynomial_incl assms(3)
    unfolding sym[OF univ_poly_carrier[of R]] by auto
  thus ?thesis
    using eval_hom'[OF assms(2)] by simp
qed

lemma (in ring_hom_ring) coeff_hom':
  assumes "set p \<subseteq> carrier R" shows "h (R.coeff p i) = coeff (map h p) i"
  using assms by (induct p) (auto)

lemma (in ring_hom_ring) poly_add_hom':
  assumes "set p \<subseteq> carrier R" and "set q \<subseteq> carrier R"
  shows "normalize (map h (R.poly_add p q)) = poly_add (map h p) (map h q)"
proof -
  have set_map: "set (map h s) \<subseteq> carrier S" if "set s \<subseteq> carrier R" for s
    using that by auto
  have "coeff (normalize (map h (R.poly_add p q))) = coeff (map h (R.poly_add p q))"
    using S.normalize_coeff by auto
  also have " ... = (\<lambda>i. h ((R.coeff p i) \<oplus> (R.coeff q i)))"
    using coeff_hom'[OF R.poly_add_in_carrier[OF assms]] R.poly_add_coeff[OF assms] by simp
  also have " ... = (\<lambda>i. (coeff (map h p) i) \<oplus>\<^bsub>S\<^esub> (coeff (map h q) i))"
    using assms[THEN R.coeff_in_carrier] assms[THEN coeff_hom'] by simp
  also have " ... = (\<lambda>i. coeff (poly_add (map h p) (map h q)) i)"
    using S.poly_add_coeff[OF assms[THEN set_map]] by simp
  finally have "coeff (normalize (map h (R.poly_add p q))) = (\<lambda>i. coeff (poly_add (map h p) (map h q)) i)" .
  thus ?thesis
    unfolding coeff_iff_polynomial_cond[OF
              normalize_gives_polynomial[OF set_map[OF R.poly_add_in_carrier[OF assms]]]
              poly_add_is_polynomial[OF carrier_is_subring assms[THEN set_map]]] .
qed

lemma (in ring_hom_ring) poly_mult_hom':
  assumes "set p \<subseteq> carrier R" and "set q \<subseteq> carrier R"
  shows "normalize (map h (R.poly_mult p q)) = poly_mult (map h p) (map h q)"
  using assms(1)
proof (induct p, simp)
  case (Cons a p)
  have set_map: "set (map h s) \<subseteq> carrier S" if "set s \<subseteq> carrier R" for s
    using that by auto

  let ?q_a = "(map ((\<otimes>) a) q) @ (replicate (length p) \<zero>)"
  have set_q_a: "set ?q_a \<subseteq> carrier R"
    using assms(2) Cons(2) by (induct q) (auto)
  have q_a_simp: "map h ?q_a = (map ((\<otimes>\<^bsub>S\<^esub>) (h a)) (map h q)) @ (replicate (length (map h p)) \<zero>\<^bsub>S\<^esub>)"
    using assms(2) Cons(2) by (induct q) (auto)

  have "S.normalize (map h (R.poly_mult (a # p) q)) = 
        S.normalize (map h (R.poly_add ?q_a (R.poly_mult p q)))"
    by simp
  also have " ... = S.poly_add (map h ?q_a) (map h (R.poly_mult p q))"
    using poly_add_hom'[OF set_q_a R.poly_mult_in_carrier[OF _ assms(2)]] Cons by simp
  also have " ... = S.poly_add (map h ?q_a) (S.normalize (map h (R.poly_mult p q)))"
    using poly_add_normalize(2)[OF set_map[OF set_q_a] set_map[OF R.poly_mult_in_carrier[OF _ assms(2)]]] Cons by simp
  also have " ... = S.poly_add (map h ?q_a) (S.poly_mult (map h p) (map h q))"
    using Cons by simp
  also have " ... = S.poly_mult (map h (a # p)) (map h q)"
    unfolding q_a_simp by simp
  finally show ?case . 
qed


subsection \<open>The X Variable\<close>

definition var :: "_ \<Rightarrow> 'a list" (\<open>X\<index>\<close>)
  where "X\<^bsub>R\<^esub> = [ \<one>\<^bsub>R\<^esub>, \<zero>\<^bsub>R\<^esub> ]"

lemma (in ring) eval_var:
  assumes "x \<in> carrier R" shows "eval X x = x"
  using assms unfolding var_def by auto

lemma (in domain) var_closed:
  assumes "subring K R" shows "X \<in> carrier (K[X])" and "polynomial K X"
  using subringE(2-3)[OF assms]
  by (auto simp add: var_def univ_poly_def polynomial_def)

lemma (in domain) poly_mult_var':
  assumes "set p \<subseteq> carrier R"
  shows "poly_mult X p = normalize (p @ [ \<zero> ])"
    and "poly_mult p X = normalize (p @ [ \<zero> ])"
proof -
  from \<open>set p \<subseteq> carrier R\<close> have "poly_mult [ \<one> ] p = normalize p"
    using poly_mult_one' by simp
  thus "poly_mult X p = normalize (p @ [ \<zero> ])"
    using poly_mult_append_zero[OF _ assms, of "[ \<one> ]"] normalize_idem
    unfolding var_def by (auto simp del: poly_mult.simps)
  thus "poly_mult p X = normalize (p @ [ \<zero> ])"
    using poly_mult_comm[OF assms] unfolding var_def by simp
qed

lemma (in domain) poly_mult_var:
  assumes "subring K R" "p \<in> carrier (K[X])"
  shows "p \<otimes>\<^bsub>K[X]\<^esub> X = (if p = [] then [] else p @ [ \<zero> ])"
proof -
  have is_poly: "polynomial K p"
    using assms(2) unfolding univ_poly_def by simp
  hence "polynomial K (p @ [ \<zero> ])" if "p \<noteq> []"
    using that subringE(2)[OF assms(1)] unfolding polynomial_def by auto
  thus ?thesis
    using poly_mult_var'(2)[OF polynomial_in_carrier[OF assms(1) is_poly]]
          normalize_polynomial[of K "p @ [ \<zero> ]"]
    by (auto simp add: univ_poly_mult[of R K])
qed

lemma (in domain) var_pow_closed:
  assumes "subring K R" shows "X [^]\<^bsub>K[X]\<^esub> (n :: nat) \<in> carrier (K[X])"
  using monoid.nat_pow_closed[OF univ_poly_is_monoid[OF assms] var_closed(1)[OF assms]] . 

lemma (in domain) unitary_monom_eq_var_pow:
  assumes "subring K R" shows "monom \<one> n = X [^]\<^bsub>K[X]\<^esub> n"
  using poly_mult_var[OF assms var_pow_closed[OF assms]] unfolding nat_pow_def monom_def
  by (induct n) (auto simp add: univ_poly_one, metis append_Cons replicate_append_same)

lemma (in domain) monom_eq_var_pow:
  assumes "subring K R" "a \<in> carrier R - { \<zero> }"
  shows "monom a n = [ a ] \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> n)"
proof -
  have "monom a n = map ((\<otimes>) a) (monom \<one> n)"
    unfolding monom_def using assms(2) by (induct n) (auto)
  also have " ... = poly_mult [ a ] (monom \<one> n)"
    using poly_mult_const(1)[OF _ monom_is_polynomial assms(2)] carrier_is_subring by simp
  also have " ... = [ a ] \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> n)"
    unfolding unitary_monom_eq_var_pow[OF assms(1)] univ_poly_mult[of R K] by simp
  finally show ?thesis .
qed

lemma (in domain) eval_rewrite:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "p = (ring.eval (K[X])) (map poly_of_const p) X"
proof -
  let ?map_norm = "\<lambda>p. map poly_of_const p"

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .

  { fix l assume "set l \<subseteq> K"
    hence "poly_of_const a \<in> carrier (K[X])" if "a \<in> set l" for a
      using that normalize_gives_polynomial[of "[ a ]" K]
      unfolding univ_poly_carrier poly_of_const_def by auto
    hence "set (?map_norm l) \<subseteq> carrier (K[X])"
      by auto }
  note aux_lemma1 = this

  { fix q l assume set_l: "set l \<subseteq> K" and q: "q \<in> carrier (K[X])"
    from set_l have "UP.eval (?map_norm l) q = UP.eval (?map_norm ((replicate n \<zero>) @ l)) q" for n
    proof (induct n, simp)
      case (Suc n)
      from \<open>set l \<subseteq> K\<close> have set_replicate: "set ((replicate n \<zero>) @ l) \<subseteq> K"
        using subringE(2)[OF assms(1)] by (induct n) (auto)
      have step: "UP.eval (?map_norm l') q = UP.eval (?map_norm (\<zero> # l')) q" if "set l' \<subseteq> K" for l'
        using UP.eval_in_carrier[OF aux_lemma1[OF that]] q unfolding poly_of_const_def
        by (simp, simp add: sym[OF univ_poly_zero[of R K]])
      have "UP.eval (?map_norm l) q = UP.eval (?map_norm ((replicate n \<zero>) @ l)) q"
        using Suc by simp
      also have " ... = UP.eval (map poly_of_const ((replicate (Suc n) \<zero>) @ l)) q"
        using step[OF set_replicate] by simp
      finally show ?case .
    qed }
  note aux_lemma2 = this

  { fix q l assume "set l \<subseteq> K" and q: "q \<in> carrier (K[X])"
    from \<open>set l \<subseteq> K\<close> have set_norm: "set (normalize l) \<subseteq> K"
      by (induct l) (auto)
    have "UP.eval (?map_norm l) q = UP.eval (?map_norm (normalize l)) q"
      using aux_lemma2[OF set_norm q, of "length l - length (local.normalize l)"]
      unfolding sym[OF normalize_trick[of l]] .. }
  note aux_lemma3 = this

  from \<open>p \<in> carrier (K[X])\<close> show ?thesis
  proof (induct "length p" arbitrary: p rule: less_induct)
    case less thus ?case
    proof (cases p, simp add: univ_poly_zero)
      case (Cons a l)
      hence a: "a \<in> carrier R - { \<zero> }" and set_l: "set l \<subseteq> carrier R" "set l \<subseteq> K"
        using less(2) subringE(1)[OF assms(1)] unfolding sym[OF univ_poly_carrier] polynomial_def by auto

      have "a # l = poly_add (monom a (length l)) l"
        using poly_add_monom[OF set_l(1) a] ..
      also have " ... = poly_add (monom a (length l)) (normalize l)"
        using poly_add_normalize(2)[OF monom_in_carrier[of a] set_l(1)] a by simp
      also have " ... = poly_add (monom a (length l)) (UP.eval (?map_norm (normalize l)) X)"
        using less(1)[of "normalize l"] normalize_gives_polynomial[OF set_l(2)] normalize_length_le[of l]
        by (auto simp add: univ_poly_carrier Cons(1))
      also have " ... = poly_add ([ a ] \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> (length l))) (UP.eval (?map_norm l) X)"
        unfolding monom_eq_var_pow[OF assms(1) a] aux_lemma3[OF set_l(2) var_closed(1)[OF assms(1)]] ..
      also have " ... = UP.eval (?map_norm (a # l)) X"
        using a unfolding sym[OF univ_poly_add[of R K]] unfolding poly_of_const_def by auto
      finally show ?thesis
        unfolding Cons(1) .
    qed
  qed   
qed

lemma (in ring) dense_repr_set_fst:
  assumes "set p \<subseteq> K" shows "fst ` (set (dense_repr p)) \<subseteq> K - { \<zero> }"
  using assms by (induct p) (auto)

lemma (in ring) dense_repr_set_snd:
  shows "snd ` (set (dense_repr p)) \<subseteq> {..< length p}"
  by (induct p) (auto)

lemma (in domain) dense_repr_monom_closed:
  assumes "subring K R" "set p \<subseteq> K"
  shows "t \<in> set (dense_repr p) \<Longrightarrow> monom (fst t) (snd t) \<in> carrier (K[X])"
  using dense_repr_set_fst[OF assms(2)] monom_is_polynomial[OF assms(1)]
  by (auto simp add: univ_poly_carrier)

lemma (in domain) monom_finsum_decomp:
  assumes "subring K R" "p \<in> carrier (K[X])"
  shows "p = (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> set (dense_repr p). monom (fst t) (snd t))"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .

  from \<open>p \<in> carrier (K[X])\<close> show ?thesis
  proof (induct "length p" arbitrary: p rule: less_induct)
    case less thus ?case
    proof (cases p)
      case Nil thus ?thesis
        using UP.finsum_empty univ_poly_zero[of R K] by simp
    next
      case (Cons a l)
      hence in_carrier:
        "normalize l \<in> carrier (K[X])" "polynomial K (normalize l)" "polynomial K (a # l)"
        using normalize_gives_polynomial polynomial_incl[of K p] less(2)
        unfolding univ_poly_carrier by auto
      have len_lt: "length (local.normalize l) < length p"
        using normalize_length_le by (simp add: Cons le_imp_less_Suc) 

      have a: "a \<in> K - { \<zero> }"
        using less(2) subringE(1)[OF assms(1)] unfolding Cons univ_poly_def polynomial_def by auto 
      hence "p = (monom a (length l)) \<oplus>\<^bsub>K[X]\<^esub> (poly_of_dense (dense_repr (normalize l)))"
        using monom_decomp[OF assms(1), of p] less(2) dense_repr_normalize
        unfolding univ_poly_add univ_poly_carrier Cons by (auto simp del: poly_add.simps)
      also have " ... = (monom a (length l)) \<oplus>\<^bsub>K[X]\<^esub> (normalize l)"
        using monom_decomp[OF assms(1) in_carrier(2)] by simp
      finally have "p = monom a (length l) \<oplus>\<^bsub>K[X]\<^esub>
                       (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> set (dense_repr l). monom (fst t) (snd t))"
        using less(1)[OF len_lt in_carrier(1)] dense_repr_normalize by simp

      moreover have "(a, (length l)) \<notin> set (dense_repr l)"
        using dense_repr_set_snd[of l] by auto
      moreover have "monom a (length l) \<in> carrier (K[X])"
        using monom_is_polynomial[OF assms(1) a] unfolding univ_poly_carrier by simp
      moreover have "\<And>t. t \<in> set (dense_repr l) \<Longrightarrow> monom (fst t) (snd t) \<in> carrier (K[X])"
        using dense_repr_monom_closed[OF assms(1)] polynomial_incl[OF in_carrier(3)] by auto
      ultimately have "p = (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> set (dense_repr (a # l)). monom (fst t) (snd t))"
        using UP.add.finprod_insert a by auto
      thus ?thesis unfolding Cons . 
    qed
  qed
qed

lemma (in domain) var_pow_finsum_decomp:
  assumes "subring K R" "p \<in> carrier (K[X])"
  shows "p = (\<Oplus>\<^bsub>K[X]\<^esub> t \<in> set (dense_repr p). [ fst t ] \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> (snd t)))"
proof -
  let ?f = "\<lambda>t. monom (fst t) (snd t)"
  let ?g = "\<lambda>t. [ fst t ] \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> (snd t))"

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .

  have set_p: "set p \<subseteq> K"
    using polynomial_incl assms(2) by (simp add: univ_poly_carrier)
  hence f: "?f \<in> set (dense_repr p) \<rightarrow> carrier (K[X])"
    using dense_repr_monom_closed[OF assms(1)] by auto

  moreover
  have "\<And>t. t \<in> set (dense_repr p) \<Longrightarrow> fst t \<in> carrier R - { \<zero> }"
    using dense_repr_set_fst[OF set_p] subringE(1)[OF assms(1)] by auto
  hence "\<And>t. t \<in> set (dense_repr p) \<Longrightarrow> monom (fst t) (snd t) = [ fst t ] \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> (snd t))"
    using monom_eq_var_pow[OF assms(1)] by auto

  ultimately show ?thesis
    using UP.add.finprod_cong[of _ _ ?f ?g] monom_finsum_decomp[OF assms] by auto
qed

corollary (in domain) hom_var_pow_finsum:
  assumes "subring K R" and "p \<in> carrier (K[X])" "ring_hom_ring (K[X]) A h"
  shows "h p = (\<Oplus>\<^bsub>A\<^esub> t \<in> set (dense_repr p). h [ fst t ] \<otimes>\<^bsub>A\<^esub> (h X [^]\<^bsub>A\<^esub> (snd t)))"
proof -
  let ?f = "\<lambda>t. [ fst t ] \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> (snd t))"
  let ?g = "\<lambda>t. h [ fst t ] \<otimes>\<^bsub>A\<^esub> (h X [^]\<^bsub>A\<^esub> (snd t))"

  interpret UP: domain "K[X]" + A: ring A
    using univ_poly_is_domain[OF assms(1)] ring_hom_ring.axioms(2)[OF assms(3)] by simp+

  have const_in_carrier:
    "\<And>t. t \<in> set (dense_repr p) \<Longrightarrow> [ fst t ] \<in> carrier (K[X])"
    using dense_repr_set_fst[OF polynomial_incl, of K p] assms(2) const_is_polynomial[of _ K]
    by (auto simp add: univ_poly_carrier)
  hence f: "?f: set (dense_repr p) \<rightarrow> carrier (K[X])"
    using UP.m_closed[OF _ var_pow_closed[OF assms(1)]] by auto
  hence h: "h \<circ> ?f: set (dense_repr p) \<rightarrow> carrier A"
    using ring_hom_memE(1)[OF ring_hom_ring.homh[OF assms(3)]] by (auto simp add: Pi_def)

  have hp: "h p = (\<Oplus>\<^bsub>A\<^esub> t \<in> set (dense_repr p). (h \<circ> ?f) t)"
    using ring_hom_ring.hom_finsum[OF assms(3) f] var_pow_finsum_decomp[OF assms(1-2)]
    by (auto, meson o_apply)
  have eq: "\<And>t. t \<in> set (dense_repr p) \<Longrightarrow> h [ fst t ] \<otimes>\<^bsub>A\<^esub> (h X [^]\<^bsub>A\<^esub> (snd t)) = (h \<circ> ?f) t"
    using ring_hom_memE(2)[OF ring_hom_ring.homh[OF assms(3)]
          const_in_carrier var_pow_closed[OF assms(1)]]
          ring_hom_ring.hom_nat_pow[OF assms(3) var_closed(1)[OF assms(1)]] by auto
  show ?thesis
    using A.add.finprod_cong'[OF _ h eq] hp by simp
qed

corollary (in domain) determination_of_hom:
  assumes "subring K R"
    and "ring_hom_ring (K[X]) A h" "ring_hom_ring (K[X]) A g"
    and "\<And>k. k \<in> K \<Longrightarrow> h [ k ] = g [ k ]" and "h X = g X"
  shows "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> h p = g p"
proof -
  interpret A: ring A
    using ring_hom_ring.axioms(2)[OF assms(2)] by simp

  fix p assume p: "p \<in> carrier (K[X])"
  hence
    "\<And>t. t \<in> set (dense_repr p) \<Longrightarrow> [ fst t ] \<in> carrier (K[X])"
    using dense_repr_set_fst[OF polynomial_incl, of K p] const_is_polynomial[of _ K]
    by (auto simp add: univ_poly_carrier)
  hence f: "(\<lambda>t. h [ fst t ] \<otimes>\<^bsub>A\<^esub> (h X [^]\<^bsub>A\<^esub> (snd t))): set (dense_repr p) \<rightarrow> carrier A"
    using ring_hom_memE(1)[OF ring_hom_ring.homh[OF assms(2)]] var_closed(1)[OF assms(1)]
          A.m_closed[OF _ A.nat_pow_closed]
    by auto

  have eq: "\<And>t. t \<in> set (dense_repr p) \<Longrightarrow>
    g [ fst t ] \<otimes>\<^bsub>A\<^esub> (g X [^]\<^bsub>A\<^esub> (snd t)) = h [ fst t ] \<otimes>\<^bsub>A\<^esub> (h X [^]\<^bsub>A\<^esub> (snd t))"
    using dense_repr_set_fst[OF polynomial_incl, of K p] p assms(4-5)
    by (auto simp add: univ_poly_carrier)
  show "h p = g p"
    unfolding assms(2-3)[THEN hom_var_pow_finsum[OF assms(1) p]]
    using A.add.finprod_cong'[OF _ f eq] by simp
qed

corollary (in domain) eval_as_unique_hom:
  assumes "subring K R" "x \<in> carrier R"
    and "ring_hom_ring (K[X]) R h"
    and "\<And>k. k \<in> K \<Longrightarrow> h [ k ] = k" and "h X = x"
  shows "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> h p = eval p x"
  using determination_of_hom[OF assms(1,3) eval_ring_hom[OF assms(1-2)]]
        eval_var[OF assms(2)] assms(4-5) subringE(1)[OF assms(1)]
  by fastforce


subsection \<open>The Constant Term\<close>

definition (in ring) const_term :: "'a list \<Rightarrow> 'a"
  where "const_term p = eval p \<zero>"

lemma (in ring) const_term_eq_last:
  assumes "set p \<subseteq> carrier R" and "a \<in> carrier R"
  shows "const_term (p @ [ a ]) = a"
  using assms by (induct p) (auto simp add: const_term_def)

lemma (in ring) const_term_not_zero:
  assumes "const_term p \<noteq> \<zero>" shows "p \<noteq> []"
  using assms by (auto simp add: const_term_def)

lemma (in ring) const_term_explicit:
  assumes "set p \<subseteq> carrier R" "p \<noteq> []" and "const_term p = a"
  obtains p' where "set p' \<subseteq> carrier R" and "p = p' @ [ a ]"
proof -
  obtain a' p' where p: "p = p' @ [ a' ]"
    using assms(2) rev_exhaust by blast
  have p': "set p' \<subseteq> carrier R" and a: "a = a'"
    using assms const_term_eq_last[of p' a'] unfolding p by auto
  show thesis
    using p p' that unfolding a by blast
qed

lemma (in ring) const_term_zero:
  assumes "subring K R" "polynomial K p" "p \<noteq> []" and "const_term p = \<zero>"
  obtains p' where "polynomial K p'" "p' \<noteq> []" and "p = p' @ [ \<zero> ]"
proof -
  obtain p' where p': "p = p' @ [ \<zero> ]"
    using const_term_explicit[OF polynomial_in_carrier[OF assms(1-2)] assms(3-4)] by auto
  have "polynomial K p'" "p' \<noteq> []"
    using assms(2) unfolding p' polynomial_def by auto
  thus thesis using p' ..
qed

lemma (in cring) const_term_simprules:
  shows "\<And>p. set p \<subseteq> carrier R \<Longrightarrow> const_term p \<in> carrier R"
    and "\<And>p q. \<lbrakk> set p \<subseteq> carrier R; set q \<subseteq> carrier R \<rbrakk> \<Longrightarrow>
                 const_term (poly_mult p q) = const_term p \<otimes> const_term q"
    and "\<And>p q. \<lbrakk> set p \<subseteq> carrier R; set q \<subseteq> carrier R \<rbrakk> \<Longrightarrow>
                 const_term (poly_add  p q) = const_term p \<oplus> const_term q"
  using eval_poly_mult eval_poly_add eval_in_carrier zero_closed
  unfolding const_term_def by auto

lemma (in domain) const_term_simprules_shell:
  assumes "subring K R"
  shows "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> const_term p \<in> K"
    and "\<And>p q. \<lbrakk> p \<in> carrier (K[X]); q \<in> carrier (K[X]) \<rbrakk> \<Longrightarrow>
                 const_term (p \<otimes>\<^bsub>K[X]\<^esub> q) = const_term p \<otimes> const_term q"
    and "\<And>p q. \<lbrakk> p \<in> carrier (K[X]); q \<in> carrier (K[X]) \<rbrakk> \<Longrightarrow>
                 const_term (p \<oplus>\<^bsub>K[X]\<^esub> q) = const_term p \<oplus> const_term q"
    and "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> const_term (\<ominus>\<^bsub>K[X]\<^esub> p) = \<ominus> (const_term p)"
  using eval_is_hom[OF assms(1) zero_closed]
  unfolding ring_hom_def const_term_def
proof (auto)
  fix p assume p: "p \<in> carrier (K[X])"
  hence "set p \<subseteq> carrier R"
    using polynomial_in_carrier[OF assms(1)] by (auto simp add: univ_poly_def)
  thus "eval (\<ominus>\<^bsub>K [X]\<^esub> p) \<zero> = \<ominus> local.eval p \<zero>"
    unfolding univ_poly_a_inv_def'[OF assms(1) p]
    by (induct p) (auto simp add: eval_in_carrier l_minus local.minus_add)

  have "set p \<subseteq> K"
    using p by (auto simp add: univ_poly_def polynomial_def)
  thus "eval p \<zero> \<in> K"
    using subringE(1-2,6-7)[OF assms]
    by (induct p) (auto, metis assms nat_pow_0 nat_pow_zero subringE(3))
qed


subsection \<open>The Canonical Embedding of K in K[X]\<close>

lemma (in ring) poly_of_const_consistent:
  assumes "subring K R" shows "ring.poly_of_const (R \<lparr> carrier := K \<rparr>) = poly_of_const"
  unfolding ring.poly_of_const_def[OF subring_is_ring[OF assms]]
            normalize_consistent[OF assms] poly_of_const_def ..

lemma (in domain) canonical_embedding_is_hom:
  assumes "subring K R" shows "poly_of_const \<in> ring_hom (R \<lparr> carrier := K \<rparr>) (K[X])"
  using subringE(1)[OF assms] unfolding subset_iff poly_of_const_def
  by (auto intro!: ring_hom_memI simp add: univ_poly_def)

lemma (in domain) canonical_embedding_ring_hom:
  assumes "subring K R" shows "ring_hom_ring (R \<lparr> carrier := K \<rparr>) (K[X]) poly_of_const"
  using canonical_embedding_is_hom[OF assms] unfolding symmetric[OF ring_hom_ring_axioms_def]
  by (rule ring_hom_ring.intro[OF subring_is_ring[OF assms] univ_poly_is_ring[OF assms]])

lemma (in field) poly_of_const_over_carrier:
  shows "poly_of_const ` (carrier R) = { p \<in> carrier ((carrier R)[X]). degree p = 0 }"
proof -
  have "poly_of_const ` (carrier R) = insert [] { [ k ] | k. k \<in> carrier R - { \<zero> } }"
    unfolding poly_of_const_def by auto
  also have " ... = { p \<in> carrier ((carrier R)[X]). degree p = 0 }"
    unfolding univ_poly_def polynomial_def
    by (auto, metis le_Suc_eq le_zero_eq length_0_conv length_Suc_conv list.sel(1) list.set_sel(1) subsetCE)
  finally show ?thesis .
qed

lemma (in ring) poly_of_const_over_subfield:
  assumes "subfield K R" shows "poly_of_const ` K = { p \<in> carrier (K[X]). degree p = 0 }"
  using field.poly_of_const_over_carrier[OF subfield_iff(2)[OF assms]]
        poly_of_const_consistent[OF subfieldE(1)[OF assms]]
        univ_poly_consistent[OF subfieldE(1)[OF assms]] by simp
    
lemma (in field) univ_poly_carrier_subfield_of_consts:
  "subfield (poly_of_const ` (carrier R)) ((carrier R)[X])"
proof -
  have ring_hom: "ring_hom_ring R ((carrier R)[X]) poly_of_const"
    using canonical_embedding_ring_hom[OF carrier_is_subring] by simp
  thus ?thesis
    using ring_hom_ring.img_is_subfield(2)[OF ring_hom carrier_is_subfield]
    unfolding univ_poly_def by auto
qed

proposition (in ring) univ_poly_subfield_of_consts:
  assumes "subfield K R" shows "subfield (poly_of_const ` K) (K[X])"
  using field.univ_poly_carrier_subfield_of_consts[OF subfield_iff(2)[OF assms]]
  unfolding poly_of_const_consistent[OF subfieldE(1)[OF assms]]
            univ_poly_consistent[OF subfieldE(1)[OF assms]] by simp

end
