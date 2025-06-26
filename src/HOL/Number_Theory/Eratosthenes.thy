(*  Title:      HOL/Number_Theory/Eratosthenes.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>The sieve of Eratosthenes\<close>

theory Eratosthenes
  imports Main "HOL-Computational_Algebra.Primes"
begin


subsection \<open>Preliminary: strict divisibility\<close>

context dvd
begin

abbreviation dvd_strict :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl \<open>dvd'_strict\<close> 50)
where
  "b dvd_strict a \<equiv> b dvd a \<and> \<not> a dvd b"

end


subsection \<open>Main corpus\<close>

text \<open>The sieve is modelled as a list of booleans, where \<^const>\<open>False\<close> means \emph{marked out}.\<close>

type_synonym marks = "bool list"

definition numbers_of_marks :: "nat \<Rightarrow> marks \<Rightarrow> nat set"
where
  "numbers_of_marks n bs = fst ` {x \<in> set (enumerate n bs). snd x}"

lemma numbers_of_marks_simps [simp, code]:
  "numbers_of_marks n [] = {}"
  "numbers_of_marks n (True # bs) = insert n (numbers_of_marks (Suc n) bs)"
  "numbers_of_marks n (False # bs) = numbers_of_marks (Suc n) bs"
  by (auto simp add: numbers_of_marks_def intro!: image_eqI)

lemma numbers_of_marks_Suc:
  "numbers_of_marks (Suc n) bs = Suc ` numbers_of_marks n bs"
  by (auto simp add: numbers_of_marks_def enumerate_Suc_eq image_iff Bex_def)

lemma numbers_of_marks_replicate_False [simp]:
  "numbers_of_marks n (replicate m False) = {}"
  by (auto simp add: numbers_of_marks_def enumerate_replicate_eq)

lemma numbers_of_marks_replicate_True [simp]:
  "numbers_of_marks n (replicate m True) = {n..<n+m}"
  by (auto simp add: numbers_of_marks_def enumerate_replicate_eq image_def)

lemma in_numbers_of_marks_eq:
  "m \<in> numbers_of_marks n bs \<longleftrightarrow> m \<in> {n..<n + length bs} \<and> bs ! (m - n)"
  by (simp add: numbers_of_marks_def in_set_enumerate_eq image_iff add.commute)

lemma sorted_list_of_set_numbers_of_marks:
  "sorted_list_of_set (numbers_of_marks n bs) = map fst (filter snd (enumerate n bs))"
  by (auto simp add: numbers_of_marks_def distinct_map
    intro!: sorted_filter distinct_filter inj_onI sorted_distinct_set_unique)


text \<open>Marking out multiples in a sieve\<close>

definition mark_out :: "nat \<Rightarrow> marks \<Rightarrow> marks"
where
  "mark_out n bs = map (\<lambda>(q, b). b \<and> \<not> Suc n dvd Suc (Suc q)) (enumerate n bs)"

lemma mark_out_Nil [simp]: "mark_out n [] = []"
  by (simp add: mark_out_def)

lemma length_mark_out [simp]: "length (mark_out n bs) = length bs"
  by (simp add: mark_out_def)

lemma numbers_of_marks_mark_out:
    "numbers_of_marks n (mark_out m bs) = {q \<in> numbers_of_marks n bs. \<not> Suc m dvd Suc q - n}"
  by (auto simp add: numbers_of_marks_def mark_out_def in_set_enumerate_eq image_iff
    nth_enumerate_eq less_eq_dvd_minus)


text \<open>Auxiliary operation for efficient implementation\<close>

definition mark_out_aux :: "nat \<Rightarrow> nat \<Rightarrow> marks \<Rightarrow> marks"
where
  "mark_out_aux n m bs =
    map (\<lambda>(q, b). b \<and> (q < m + n \<or> \<not> Suc n dvd Suc (Suc q) + (n - m mod Suc n))) (enumerate n bs)"

lemma mark_out_code [code]: "mark_out n bs = mark_out_aux n n bs"
proof -
  have aux: False
    if A: "Suc n dvd Suc (Suc a)"
    and B: "a < n + n"
    and C: "n \<le> a"
    for a
  proof (cases "n = 0")
    case True
    with A B C show ?thesis by simp
  next
    case False
    define m where "m = Suc n"
    then have "m > 0" by simp
    from False have "n > 0" by simp
    from A obtain q where q: "Suc (Suc a) = Suc n * q" by (rule dvdE)
    have "q > 0"
    proof (rule ccontr)
      assume "\<not> q > 0"
      with q show False by simp
    qed
    with \<open>n > 0\<close> have "Suc n * q \<ge> 2" by (auto simp add: gr0_conv_Suc)
    with q have a: "a = Suc n * q - 2" by simp
    with B have "q + n * q < n + n + 2" by auto
    then have "m * q < m * 2" by (simp add: m_def)
    with \<open>m > 0\<close> \<open>q > 0\<close> have "q = 1" by simp
    with a have "a = n - 1" by simp
    with \<open>n > 0\<close> C show False by simp
  qed
  show ?thesis
    by (auto simp add: mark_out_def mark_out_aux_def in_set_enumerate_eq intro: aux)
qed

lemma mark_out_aux_simps [simp, code]:
  "mark_out_aux n m [] = []"
  "mark_out_aux n 0 (b # bs) = False # mark_out_aux n n bs"
  "mark_out_aux n (Suc m) (b # bs) = b # mark_out_aux n m bs"
proof goal_cases
  case 1
  show ?case
    by (simp add: mark_out_aux_def)
next
  case 2
  show ?case
    by (auto simp add: mark_out_code [symmetric] mark_out_aux_def mark_out_def
      enumerate_Suc_eq in_set_enumerate_eq less_eq_dvd_minus)
next
  case 3
  { define v where "v = Suc m"
    define w where "w = Suc n"
    fix q
    assume "m + n \<le> q"
    then obtain r where q: "q = m + n + r" by (auto simp add: le_iff_add)
    { fix u
      from w_def have "u mod w < w" by simp
      then have "u + (w - u mod w) = w + (u - u mod w)"
        by simp
      then have "u + (w - u mod w) = w + u div w * w"
        by (simp add: minus_mod_eq_div_mult)
    }
    then have "w dvd v + w + r + (w - v mod w) \<longleftrightarrow> w dvd m + w + r + (w - m mod w)"
      by (simp add: add.assoc add.left_commute [of m] add.left_commute [of v]
        dvd_add_left_iff dvd_add_right_iff)
    moreover from q have "Suc q = m + w + r" by (simp add: w_def)
    moreover from q have "Suc (Suc q) = v + w + r" by (simp add: v_def w_def)
    ultimately have "w dvd Suc (Suc (q + (w - v mod w))) \<longleftrightarrow> w dvd Suc (q + (w - m mod w))"
      by (simp only: add_Suc [symmetric])
    then have "Suc n dvd Suc (Suc (Suc (q + n) - Suc m mod Suc n)) \<longleftrightarrow>
      Suc n dvd Suc (Suc (q + n - m mod Suc n))"
      by (simp add: v_def w_def Suc_diff_le trans_le_add2)
  }
  then show ?case
    by (auto simp add: mark_out_aux_def
      enumerate_Suc_eq in_set_enumerate_eq not_less)
qed


text \<open>Main entry point to sieve\<close>

fun sieve :: "nat \<Rightarrow> marks \<Rightarrow> marks"
where
  "sieve n [] = []"
| "sieve n (False # bs) = False # sieve (Suc n) bs"
| "sieve n (True # bs) = True # sieve (Suc n) (mark_out n bs)"

text \<open>
  There are the following possible optimisations here:

  \begin{itemize}

    \item \<^const>\<open>sieve\<close> can abort as soon as \<^term>\<open>n\<close> is too big to let
      \<^const>\<open>mark_out\<close> have any effect.

    \item Search for further primes can be given up as soon as the search
      position exceeds the square root of the maximum candidate.

  \end{itemize}

  This is left as an constructive exercise to the reader.
\<close>

lemma numbers_of_marks_sieve:
  "numbers_of_marks (Suc n) (sieve n bs) =
    {q \<in> numbers_of_marks (Suc n) bs. \<forall>m \<in> numbers_of_marks (Suc n) bs. \<not> m dvd_strict q}"
proof (induct n bs rule: sieve.induct)
  case 1
  show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 n bs)
  have aux: "n \<in> Suc ` M \<longleftrightarrow> n > 0 \<and> n - 1 \<in> M" (is "?lhs \<longleftrightarrow> ?rhs") for M n
  proof
    show ?rhs if ?lhs using that by auto
    show ?lhs if ?rhs
    proof -
      from that have "n > 0" and "n - 1 \<in> M" by auto
      then have "Suc (n - 1) \<in> Suc ` M" by blast
      with \<open>n > 0\<close> show "n \<in> Suc ` M" by simp
    qed
  qed
  have aux1: False if "Suc (Suc n) \<le> m" and "m dvd Suc n" for m :: nat
  proof -
    from \<open>m dvd Suc n\<close> obtain q where "Suc n = m * q" ..
    with \<open>Suc (Suc n) \<le> m\<close> have "Suc (m * q) \<le> m" by simp
    then have "m * q < m" by arith
    with \<open>Suc n = m * q\<close> show ?thesis by simp
  qed
  have aux2: "m dvd q"
    if 1: "\<forall>q>0. 1 < q \<longrightarrow> Suc n < q \<longrightarrow> q \<le> Suc (n + length bs) \<longrightarrow>
      bs ! (q - Suc (Suc n)) \<longrightarrow> \<not> Suc n dvd q \<longrightarrow> q dvd m \<longrightarrow> m dvd q"
    and 2: "\<not> Suc n dvd m" "q dvd m"
    and 3: "Suc n < q" "q \<le> Suc (n + length bs)" "bs ! (q - Suc (Suc n))"
    for m q :: nat
  proof -
    from 1 have *: "\<And>q. Suc n < q \<Longrightarrow> q \<le> Suc (n + length bs) \<Longrightarrow>
      bs ! (q - Suc (Suc n)) \<Longrightarrow> \<not> Suc n dvd q \<Longrightarrow> q dvd m \<Longrightarrow> m dvd q"
      by auto
    from 2 have "\<not> Suc n dvd q" by auto
    moreover note 3
    moreover note \<open>q dvd m\<close>
    ultimately show ?thesis by (auto intro: *)
  qed
  from 3 show ?case
    apply (simp_all add: numbers_of_marks_mark_out numbers_of_marks_Suc Compr_image_eq
      inj_image_eq_iff in_numbers_of_marks_eq Ball_def imp_conjL aux)
    apply safe
    apply (simp_all add: less_diff_conv2 le_diff_conv2 dvd_minus_self not_less)
    apply (clarsimp dest!: aux1)
    apply (simp add: Suc_le_eq less_Suc_eq_le)
    apply (rule aux2)
    apply (clarsimp dest!: aux1)+
    done
qed


text \<open>Relation of the sieve algorithm to actual primes\<close>

definition primes_upto :: "nat \<Rightarrow> nat list"
where
  "primes_upto n = sorted_list_of_set {m. m \<le> n \<and> prime m}"

lemma set_primes_upto: "set (primes_upto n) = {m. m \<le> n \<and> prime m}"
  by (simp add: primes_upto_def)

lemma sorted_primes_upto [iff]: "sorted (primes_upto n)"
  by (simp add: primes_upto_def)

lemma distinct_primes_upto [iff]: "distinct (primes_upto n)"
  by (simp add: primes_upto_def)

lemma set_primes_upto_sieve:
  "set (primes_upto n) = numbers_of_marks 2 (sieve 1 (replicate (n - 1) True))"
proof -
  consider "n = 0 \<or> n = 1" | "n > 1" by arith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (auto simp add: numbers_of_marks_sieve numeral_2_eq_2 set_primes_upto
        dest: prime_gt_Suc_0_nat)
  next
    case 2
    {
      fix m q
      assume "Suc (Suc 0) \<le> q"
        and "q < Suc n"
        and "m dvd q"
      then have "m < Suc n" by (auto dest: dvd_imp_le)
      assume *: "\<forall>m\<in>{Suc (Suc 0)..<Suc n}. m dvd q \<longrightarrow> q dvd m"
        and "m dvd q" and "m \<noteq> 1"
      have "m = q"
      proof (cases "m = 0")
        case True with \<open>m dvd q\<close> show ?thesis by simp
      next
        case False with \<open>m \<noteq> 1\<close> have "Suc (Suc 0) \<le> m" by arith
        with \<open>m < Suc n\<close> * \<open>m dvd q\<close> have "q dvd m" by simp
        with \<open>m dvd q\<close> show ?thesis by (simp add: dvd_antisym)
      qed
    }
    then have aux: "\<And>m q. Suc (Suc 0) \<le> q \<Longrightarrow>
      q < Suc n \<Longrightarrow>
      m dvd q \<Longrightarrow>
      \<forall>m\<in>{Suc (Suc 0)..<Suc n}. m dvd q \<longrightarrow> q dvd m \<Longrightarrow>
      m dvd q \<Longrightarrow> m \<noteq> q \<Longrightarrow> m = 1" by auto
    from 2 show ?thesis
      apply (auto simp add: numbers_of_marks_sieve numeral_2_eq_2 set_primes_upto
        dest: prime_gt_Suc_0_nat)
      apply (metis One_nat_def Suc_le_eq less_not_refl prime_nat_iff)
      apply (metis One_nat_def Suc_le_eq aux prime_nat_iff)
      done
  qed
qed

lemma primes_upto_sieve [code]:
  "primes_upto n = map fst (filter snd (enumerate 2 (sieve 1 (replicate (n - 1) True))))"
  using primes_upto_def set_primes_upto set_primes_upto_sieve sorted_list_of_set_numbers_of_marks by presburger

lemma prime_in_primes_upto: "prime n \<longleftrightarrow> n \<in> set (primes_upto n)"
  by (simp add: set_primes_upto)


subsection \<open>Application: smallest prime beyond a certain number\<close>

definition smallest_prime_beyond :: "nat \<Rightarrow> nat"
where
  "smallest_prime_beyond n = (LEAST p. prime p \<and> p \<ge> n)"

lemma prime_smallest_prime_beyond [iff]: "prime (smallest_prime_beyond n)" (is ?P)
  and smallest_prime_beyond_le [iff]: "smallest_prime_beyond n \<ge> n" (is ?Q)
proof -
  let ?least = "LEAST p. prime p \<and> p \<ge> n"
  from primes_infinite obtain q where "prime q \<and> q \<ge> n"
    by (metis finite_nat_set_iff_bounded_le mem_Collect_eq nat_le_linear)
  then have "prime ?least \<and> ?least \<ge> n"
    by (rule LeastI)
  then show ?P and ?Q
    by (simp_all add: smallest_prime_beyond_def)
qed

lemma smallest_prime_beyond_smallest: "prime p \<Longrightarrow> p \<ge> n \<Longrightarrow> smallest_prime_beyond n \<le> p"
  by (simp only: smallest_prime_beyond_def) (auto intro: Least_le)

lemma smallest_prime_beyond_eq:
  "prime p \<Longrightarrow> p \<ge> n \<Longrightarrow> (\<And>q. prime q \<Longrightarrow> q \<ge> n \<Longrightarrow> q \<ge> p) \<Longrightarrow> smallest_prime_beyond n = p"
  by (simp only: smallest_prime_beyond_def) (auto intro: Least_equality)

definition smallest_prime_between :: "nat \<Rightarrow> nat \<Rightarrow> nat option"
where
  "smallest_prime_between m n =
    (if (\<exists>p. prime p \<and> m \<le> p \<and> p \<le> n) then Some (smallest_prime_beyond m) else None)"

lemma smallest_prime_between_None:
  "smallest_prime_between m n = None \<longleftrightarrow> (\<forall>q. m \<le> q \<and> q \<le> n \<longrightarrow> \<not> prime q)"
  by (auto simp add: smallest_prime_between_def)

lemma smallest_prime_betwen_Some:
  "smallest_prime_between m n = Some p \<longleftrightarrow> smallest_prime_beyond m = p \<and> p \<le> n"
  by (auto simp add: smallest_prime_between_def dest: smallest_prime_beyond_smallest [of _ m])

lemma [code]: "smallest_prime_between m n = List.find (\<lambda>p. p \<ge> m) (primes_upto n)"
proof -
  have "List.find (\<lambda>p. p \<ge> m) (primes_upto n) = Some (smallest_prime_beyond m)"
    if assms: "m \<le> p" "prime p" "p \<le> n" for p
  proof -
    define A where "A = {p. p \<le> n \<and> prime p \<and> m \<le> p}"
    from assms have "smallest_prime_beyond m \<le> p"
      by (auto intro: smallest_prime_beyond_smallest)
    from this \<open>p \<le> n\<close> have *: "smallest_prime_beyond m \<le> n"
      by (rule order_trans)
    from assms have ex: "\<exists>p\<le>n. prime p \<and> m \<le> p"
      by auto
    then have "finite A"
      by (auto simp add: A_def)
    with * have "Min A = smallest_prime_beyond m"
      by (auto simp add: A_def intro: Min_eqI smallest_prime_beyond_smallest)
    with ex sorted_primes_upto show ?thesis
      by (auto simp add: set_primes_upto sorted_find_Min A_def)
  qed
  then show ?thesis
    by (auto simp add: smallest_prime_between_def find_None_iff set_primes_upto
      intro!: sym [of _ None])
qed

definition smallest_prime_beyond_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "smallest_prime_beyond_aux k n = smallest_prime_beyond n"

lemma [code]:
  "smallest_prime_beyond_aux k n =
    (case smallest_prime_between n (k * n) of
      Some p \<Rightarrow> p
    | None \<Rightarrow> smallest_prime_beyond_aux (Suc k) n)"
  by (simp add: smallest_prime_beyond_aux_def smallest_prime_betwen_Some split: option.split)

lemma [code]: "smallest_prime_beyond n = smallest_prime_beyond_aux 2 n"
  by (simp add: smallest_prime_beyond_aux_def)

end
