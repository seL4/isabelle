(*  Title:      HOL/Library/Nat_Bijection.thy
    Author:     Brian Huffman
    Author:     Florian Haftmann
    Author:     Stefan Richter
    Author:     Tobias Nipkow
    Author:     Alexander Krauss
*)

section \<open>Bijections between natural numbers and other types\<close>

theory Nat_Bijection
  imports Main
begin

subsection \<open>Type \<^typ>\<open>nat \<times> nat\<close>\<close>

text \<open>Triangle numbers: 0, 1, 3, 6, 10, 15, ...\<close>

definition triangle :: "nat \<Rightarrow> nat"
  where "triangle n = (n * Suc n) div 2"

lemma triangle_0 [simp]: "triangle 0 = 0"
  by (simp add: triangle_def)

lemma triangle_Suc [simp]: "triangle (Suc n) = triangle n + Suc n"
  by (simp add: triangle_def)

definition prod_encode :: "nat \<times> nat \<Rightarrow> nat"
  where "prod_encode = (\<lambda>(m, n). triangle (m + n) + m)"

text \<open>In this auxiliary function, \<^term>\<open>triangle k + m\<close> is an invariant.\<close>

fun prod_decode_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  where "prod_decode_aux k m =
    (if m \<le> k then (m, k - m) else prod_decode_aux (Suc k) (m - Suc k))"

declare prod_decode_aux.simps [simp del]

definition prod_decode :: "nat \<Rightarrow> nat \<times> nat"
  where "prod_decode = prod_decode_aux 0"

lemma prod_encode_prod_decode_aux: "prod_encode (prod_decode_aux k m) = triangle k + m"
proof (induction k m rule: prod_decode_aux.induct)
  case (1 k m)
  then show ?case
    by (simp add: prod_encode_def prod_decode_aux.simps)
qed

lemma prod_decode_inverse [simp]: "prod_encode (prod_decode n) = n"
  by (simp add: prod_decode_def prod_encode_prod_decode_aux)

lemma prod_decode_triangle_add: "prod_decode (triangle k + m) = prod_decode_aux k m"
proof (induct k arbitrary: m)
  case 0
  then show ?case 
    by (simp add: prod_decode_def)
next
  case (Suc k)
  then show ?case
    by (metis ab_semigroup_add_class.add_ac(1) add_diff_cancel_left' le_add1 not_less_eq_eq prod_decode_aux.simps triangle_Suc)
qed


lemma prod_encode_inverse [simp]: "prod_decode (prod_encode x) = x"
  unfolding prod_encode_def
proof (induct x)
  case (Pair a b)
  then show ?case
    by (simp add: prod_decode_triangle_add prod_decode_aux.simps)
qed

lemma inj_prod_encode: "inj_on prod_encode A"
  by (rule inj_on_inverseI) (rule prod_encode_inverse)

lemma inj_prod_decode: "inj_on prod_decode A"
  by (rule inj_on_inverseI) (rule prod_decode_inverse)

lemma surj_prod_encode: "surj prod_encode"
  by (rule surjI) (rule prod_decode_inverse)

lemma surj_prod_decode: "surj prod_decode"
  by (rule surjI) (rule prod_encode_inverse)

lemma bij_prod_encode: "bij prod_encode"
  by (rule bijI [OF inj_prod_encode surj_prod_encode])

lemma bij_prod_decode: "bij prod_decode"
  by (rule bijI [OF inj_prod_decode surj_prod_decode])

lemma prod_encode_eq: "prod_encode x = prod_encode y \<longleftrightarrow> x = y"
  by (rule inj_prod_encode [THEN inj_eq])

lemma prod_decode_eq: "prod_decode x = prod_decode y \<longleftrightarrow> x = y"
  by (rule inj_prod_decode [THEN inj_eq])


text \<open>Ordering properties\<close>

lemma le_prod_encode_1: "a \<le> prod_encode (a, b)"
  by (simp add: prod_encode_def)

lemma le_prod_encode_2: "b \<le> prod_encode (a, b)"
  by (induct b) (simp_all add: prod_encode_def)


subsection \<open>Type \<^typ>\<open>nat + nat\<close>\<close>

definition sum_encode :: "nat + nat \<Rightarrow> nat"
  where "sum_encode x = (case x of Inl a \<Rightarrow> 2 * a | Inr b \<Rightarrow> Suc (2 * b))"

definition sum_decode :: "nat \<Rightarrow> nat + nat"
  where "sum_decode n = (if even n then Inl (n div 2) else Inr (n div 2))"

lemma sum_encode_inverse [simp]: "sum_decode (sum_encode x) = x"
  by (induct x) (simp_all add: sum_decode_def sum_encode_def)

lemma sum_decode_inverse [simp]: "sum_encode (sum_decode n) = n"
  by (simp add: even_two_times_div_two sum_decode_def sum_encode_def)

lemma inj_sum_encode: "inj_on sum_encode A"
  by (rule inj_on_inverseI) (rule sum_encode_inverse)

lemma inj_sum_decode: "inj_on sum_decode A"
  by (rule inj_on_inverseI) (rule sum_decode_inverse)

lemma surj_sum_encode: "surj sum_encode"
  by (rule surjI) (rule sum_decode_inverse)

lemma surj_sum_decode: "surj sum_decode"
  by (rule surjI) (rule sum_encode_inverse)

lemma bij_sum_encode: "bij sum_encode"
  by (rule bijI [OF inj_sum_encode surj_sum_encode])

lemma bij_sum_decode: "bij sum_decode"
  by (rule bijI [OF inj_sum_decode surj_sum_decode])

lemma sum_encode_eq: "sum_encode x = sum_encode y \<longleftrightarrow> x = y"
  by (rule inj_sum_encode [THEN inj_eq])

lemma sum_decode_eq: "sum_decode x = sum_decode y \<longleftrightarrow> x = y"
  by (rule inj_sum_decode [THEN inj_eq])


subsection \<open>Type \<^typ>\<open>int\<close>\<close>

definition int_encode :: "int \<Rightarrow> nat"
  where "int_encode i = sum_encode (if 0 \<le> i then Inl (nat i) else Inr (nat (- i - 1)))"

definition int_decode :: "nat \<Rightarrow> int"
  where "int_decode n = (case sum_decode n of Inl a \<Rightarrow> int a | Inr b \<Rightarrow> - int b - 1)"

lemma int_encode_inverse [simp]: "int_decode (int_encode x) = x"
  by (simp add: int_decode_def int_encode_def)

lemma int_decode_inverse [simp]: "int_encode (int_decode n) = n"
  unfolding int_decode_def int_encode_def
  using sum_decode_inverse [of n] by (cases "sum_decode n") simp_all

lemma inj_int_encode: "inj_on int_encode A"
  by (rule inj_on_inverseI) (rule int_encode_inverse)

lemma inj_int_decode: "inj_on int_decode A"
  by (rule inj_on_inverseI) (rule int_decode_inverse)

lemma surj_int_encode: "surj int_encode"
  by (rule surjI) (rule int_decode_inverse)

lemma surj_int_decode: "surj int_decode"
  by (rule surjI) (rule int_encode_inverse)

lemma bij_int_encode: "bij int_encode"
  by (rule bijI [OF inj_int_encode surj_int_encode])

lemma bij_int_decode: "bij int_decode"
  by (rule bijI [OF inj_int_decode surj_int_decode])

lemma int_encode_eq: "int_encode x = int_encode y \<longleftrightarrow> x = y"
  by (rule inj_int_encode [THEN inj_eq])

lemma int_decode_eq: "int_decode x = int_decode y \<longleftrightarrow> x = y"
  by (rule inj_int_decode [THEN inj_eq])


subsection \<open>Type \<^typ>\<open>nat list\<close>\<close>

fun list_encode :: "nat list \<Rightarrow> nat"
  where
    "list_encode [] = 0"
  | "list_encode (x # xs) = Suc (prod_encode (x, list_encode xs))"

function list_decode :: "nat \<Rightarrow> nat list"
  where
    "list_decode 0 = []"
  | "list_decode (Suc n) = (case prod_decode n of (x, y) \<Rightarrow> x # list_decode y)"
  by pat_completeness auto

termination list_decode
proof -
  have "\<And>n x y. (x, y) = prod_decode n \<Longrightarrow> y < Suc n"
    by (metis le_imp_less_Suc le_prod_encode_2 prod_decode_inverse)
  then show ?thesis
    using "termination" by blast
qed

lemma list_encode_inverse [simp]: "list_decode (list_encode x) = x"
  by (induct x rule: list_encode.induct) simp_all

lemma list_decode_inverse [simp]: "list_encode (list_decode n) = n"
proof (induct n rule: list_decode.induct)
  case (2 n)
  then show ?case
    by (metis list_encode.simps(2) list_encode_inverse prod_decode_inverse surj_pair)
qed auto

lemma inj_list_encode: "inj_on list_encode A"
  by (rule inj_on_inverseI) (rule list_encode_inverse)

lemma inj_list_decode: "inj_on list_decode A"
  by (rule inj_on_inverseI) (rule list_decode_inverse)

lemma surj_list_encode: "surj list_encode"
  by (rule surjI) (rule list_decode_inverse)

lemma surj_list_decode: "surj list_decode"
  by (rule surjI) (rule list_encode_inverse)

lemma bij_list_encode: "bij list_encode"
  by (rule bijI [OF inj_list_encode surj_list_encode])

lemma bij_list_decode: "bij list_decode"
  by (rule bijI [OF inj_list_decode surj_list_decode])

lemma list_encode_eq: "list_encode x = list_encode y \<longleftrightarrow> x = y"
  by (rule inj_list_encode [THEN inj_eq])

lemma list_decode_eq: "list_decode x = list_decode y \<longleftrightarrow> x = y"
  by (rule inj_list_decode [THEN inj_eq])


subsection \<open>Finite sets of naturals\<close>

subsubsection \<open>Preliminaries\<close>

lemma finite_vimage_Suc_iff: "finite (Suc -` F) \<longleftrightarrow> finite F"
proof 
  have "F \<subseteq> insert 0 (Suc ` Suc -` F)"
    using nat.nchotomy by force
  moreover
  assume "finite (Suc -` F)"
  then have "finite (insert 0 (Suc ` Suc -` F))"
    by blast
  ultimately show "finite F"
    using finite_subset by blast
qed (force intro: finite_vimageI inj_Suc)

lemma vimage_Suc_insert_0: "Suc -` insert 0 A = Suc -` A"
  by auto

lemma vimage_Suc_insert_Suc: "Suc -` insert (Suc n) A = insert n (Suc -` A)"
  by auto

lemma div2_even_ext_nat:
  fixes x y :: nat
  assumes "x div 2 = y div 2"
    and "even x \<longleftrightarrow> even y"
  shows "x = y"
proof -
  from \<open>even x \<longleftrightarrow> even y\<close> have "x mod 2 = y mod 2"
    by (simp only: even_iff_mod_2_eq_zero) auto
  with assms have "x div 2 * 2 + x mod 2 = y div 2 * 2 + y mod 2"
    by simp
  then show ?thesis
    by simp
qed


subsubsection \<open>From sets to naturals\<close>

definition set_encode :: "nat set \<Rightarrow> nat"
  where "set_encode = sum ((^) 2)"

lemma set_encode_empty [simp]: "set_encode {} = 0"
  by (simp add: set_encode_def)

lemma set_encode_inf: "\<not> finite A \<Longrightarrow> set_encode A = 0"
  by (simp add: set_encode_def)

lemma set_encode_insert [simp]: "finite A \<Longrightarrow> n \<notin> A \<Longrightarrow> set_encode (insert n A) = 2^n + set_encode A"
  by (simp add: set_encode_def)

lemma even_set_encode_iff: "finite A \<Longrightarrow> even (set_encode A) \<longleftrightarrow> 0 \<notin> A"
  by (induct set: finite) (auto simp: set_encode_def)

lemma set_encode_vimage_Suc: "set_encode (Suc -` A) = set_encode A div 2"
proof (induction A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case
    by (simp add: finite_vimage_Suc_iff set_encode_inf)
next
  case (insert x A)
  show ?case
  proof (cases x)
    case 0
    with insert show ?thesis
      by (simp add: even_set_encode_iff vimage_Suc_insert_0)
  next
    case (Suc y)
    with insert show ?thesis
      by (simp add: finite_vimageI add.commute vimage_Suc_insert_Suc)
  qed   
qed auto

lemmas set_encode_div_2 = set_encode_vimage_Suc [symmetric]


subsubsection \<open>From naturals to sets\<close>

definition set_decode :: "nat \<Rightarrow> nat set"
  where "set_decode x = {n. odd (x div 2 ^ n)}"

lemma set_decode_0 [simp]: "0 \<in> set_decode x \<longleftrightarrow> odd x"
  by (simp add: set_decode_def)

lemma set_decode_Suc [simp]: "Suc n \<in> set_decode x \<longleftrightarrow> n \<in> set_decode (x div 2)"
  by (simp add: set_decode_def div_mult2_eq)

lemma set_decode_zero [simp]: "set_decode 0 = {}"
  by (simp add: set_decode_def)

lemma set_decode_div_2: "set_decode (x div 2) = Suc -` set_decode x"
  by auto

lemma set_decode_plus_power_2:
  "n \<notin> set_decode z \<Longrightarrow> set_decode (2 ^ n + z) = insert n (set_decode z)"
proof (induct n arbitrary: z)
  case 0
  show ?case
  proof (rule set_eqI)
    show "q \<in> set_decode (2 ^ 0 + z) \<longleftrightarrow> q \<in> insert 0 (set_decode z)" for q
      by (induct q) (use 0 in simp_all)
  qed
next
  case (Suc n)
  show ?case
  proof (rule set_eqI)
    show "q \<in> set_decode (2 ^ Suc n + z) \<longleftrightarrow> q \<in> insert (Suc n) (set_decode z)" for q
      by (induct q) (use Suc in simp_all)
  qed
qed

lemma finite_set_decode [simp]: "finite (set_decode n)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 0")
    case False
    then show ?thesis
      using less.IH [of "n div 2"] finite_vimage_Suc_iff set_decode_div_2 by auto
  qed auto
qed


subsubsection \<open>Proof of isomorphism\<close>

lemma set_decode_inverse [simp]: "set_encode (set_decode n) = n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 0")
    case False
    then have "set_encode (set_decode (n div 2)) = n div 2"
      using less.IH by auto
    then show ?thesis
      by (metis div2_even_ext_nat even_set_encode_iff finite_set_decode set_decode_0 set_decode_div_2 set_encode_div_2)
  qed auto
qed

lemma set_encode_inverse [simp]: "finite A \<Longrightarrow> set_decode (set_encode A) = A"
proof (induction rule: finite_induct)
  case (insert x A)
  then show ?case
    by (simp add: set_decode_plus_power_2)
qed auto

lemma inj_on_set_encode: "inj_on set_encode (Collect finite)"
  by (rule inj_on_inverseI [where g = "set_decode"]) simp

lemma set_encode_eq: "finite A \<Longrightarrow> finite B \<Longrightarrow> set_encode A = set_encode B \<longleftrightarrow> A = B"
  by (rule iffI) (simp_all add: inj_onD [OF inj_on_set_encode])

lemma subset_decode_imp_le:
  assumes "set_decode m \<subseteq> set_decode n"
  shows "m \<le> n"
proof -
  have "n = m + set_encode (set_decode n - set_decode m)"
  proof -
    obtain A B where
      "m = set_encode A" "finite A"
      "n = set_encode B" "finite B"
      by (metis finite_set_decode set_decode_inverse)
  with assms show ?thesis
    by auto (simp add: set_encode_def add.commute sum.subset_diff)
  qed
  then show ?thesis
    by (metis le_add1)
qed

end
