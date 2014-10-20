(*  Title:      HOL/Library/Nat_Bijection.thy
    Author:     Brian Huffman
    Author:     Florian Haftmann
    Author:     Stefan Richter
    Author:     Tobias Nipkow
    Author:     Alexander Krauss
*)

header {* Bijections between natural numbers and other types *}

theory Nat_Bijection
imports Main Parity
begin

subsection {* Type @{typ "nat \<times> nat"} *}

text "Triangle numbers: 0, 1, 3, 6, 10, 15, ..."

definition
  triangle :: "nat \<Rightarrow> nat"
where
  "triangle n = n * Suc n div 2"

lemma triangle_0 [simp]: "triangle 0 = 0"
unfolding triangle_def by simp

lemma triangle_Suc [simp]: "triangle (Suc n) = triangle n + Suc n"
unfolding triangle_def by simp

definition
  prod_encode :: "nat \<times> nat \<Rightarrow> nat"
where
  "prod_encode = (\<lambda>(m, n). triangle (m + n) + m)"

text {* In this auxiliary function, @{term "triangle k + m"} is an invariant. *}

fun
  prod_decode_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
where
  "prod_decode_aux k m =
    (if m \<le> k then (m, k - m) else prod_decode_aux (Suc k) (m - Suc k))"

declare prod_decode_aux.simps [simp del]

definition
  prod_decode :: "nat \<Rightarrow> nat \<times> nat"
where
  "prod_decode = prod_decode_aux 0"

lemma prod_encode_prod_decode_aux:
  "prod_encode (prod_decode_aux k m) = triangle k + m"
apply (induct k m rule: prod_decode_aux.induct)
apply (subst prod_decode_aux.simps)
apply (simp add: prod_encode_def)
done

lemma prod_decode_inverse [simp]: "prod_encode (prod_decode n) = n"
unfolding prod_decode_def by (simp add: prod_encode_prod_decode_aux)

lemma prod_decode_triangle_add:
  "prod_decode (triangle k + m) = prod_decode_aux k m"
apply (induct k arbitrary: m)
apply (simp add: prod_decode_def)
apply (simp only: triangle_Suc add.assoc)
apply (subst prod_decode_aux.simps, simp)
done

lemma prod_encode_inverse [simp]: "prod_decode (prod_encode x) = x"
unfolding prod_encode_def
apply (induct x)
apply (simp add: prod_decode_triangle_add)
apply (subst prod_decode_aux.simps, simp)
done

lemma inj_prod_encode: "inj_on prod_encode A"
by (rule inj_on_inverseI, rule prod_encode_inverse)

lemma inj_prod_decode: "inj_on prod_decode A"
by (rule inj_on_inverseI, rule prod_decode_inverse)

lemma surj_prod_encode: "surj prod_encode"
by (rule surjI, rule prod_decode_inverse)

lemma surj_prod_decode: "surj prod_decode"
by (rule surjI, rule prod_encode_inverse)

lemma bij_prod_encode: "bij prod_encode"
by (rule bijI [OF inj_prod_encode surj_prod_encode])

lemma bij_prod_decode: "bij prod_decode"
by (rule bijI [OF inj_prod_decode surj_prod_decode])

lemma prod_encode_eq: "prod_encode x = prod_encode y \<longleftrightarrow> x = y"
by (rule inj_prod_encode [THEN inj_eq])

lemma prod_decode_eq: "prod_decode x = prod_decode y \<longleftrightarrow> x = y"
by (rule inj_prod_decode [THEN inj_eq])

text {* Ordering properties *}

lemma le_prod_encode_1: "a \<le> prod_encode (a, b)"
unfolding prod_encode_def by simp

lemma le_prod_encode_2: "b \<le> prod_encode (a, b)"
unfolding prod_encode_def by (induct b, simp_all)


subsection {* Type @{typ "nat + nat"} *}

definition
  sum_encode  :: "nat + nat \<Rightarrow> nat"
where
  "sum_encode x = (case x of Inl a \<Rightarrow> 2 * a | Inr b \<Rightarrow> Suc (2 * b))"

definition
  sum_decode  :: "nat \<Rightarrow> nat + nat"
where
  "sum_decode n = (if even n then Inl (n div 2) else Inr (n div 2))"

lemma sum_encode_inverse [simp]: "sum_decode (sum_encode x) = x"
unfolding sum_decode_def sum_encode_def
by (induct x) simp_all

lemma sum_decode_inverse [simp]: "sum_encode (sum_decode n) = n"
  by (simp add: even_two_times_div_two odd_two_times_div_two_Suc sum_decode_def sum_encode_def)

lemma inj_sum_encode: "inj_on sum_encode A"
by (rule inj_on_inverseI, rule sum_encode_inverse)

lemma inj_sum_decode: "inj_on sum_decode A"
by (rule inj_on_inverseI, rule sum_decode_inverse)

lemma surj_sum_encode: "surj sum_encode"
by (rule surjI, rule sum_decode_inverse)

lemma surj_sum_decode: "surj sum_decode"
by (rule surjI, rule sum_encode_inverse)

lemma bij_sum_encode: "bij sum_encode"
by (rule bijI [OF inj_sum_encode surj_sum_encode])

lemma bij_sum_decode: "bij sum_decode"
by (rule bijI [OF inj_sum_decode surj_sum_decode])

lemma sum_encode_eq: "sum_encode x = sum_encode y \<longleftrightarrow> x = y"
by (rule inj_sum_encode [THEN inj_eq])

lemma sum_decode_eq: "sum_decode x = sum_decode y \<longleftrightarrow> x = y"
by (rule inj_sum_decode [THEN inj_eq])


subsection {* Type @{typ "int"} *}

definition
  int_encode :: "int \<Rightarrow> nat"
where
  "int_encode i = sum_encode (if 0 \<le> i then Inl (nat i) else Inr (nat (- i - 1)))"

definition
  int_decode :: "nat \<Rightarrow> int"
where
  "int_decode n = (case sum_decode n of Inl a \<Rightarrow> int a | Inr b \<Rightarrow> - int b - 1)"

lemma int_encode_inverse [simp]: "int_decode (int_encode x) = x"
unfolding int_decode_def int_encode_def by simp

lemma int_decode_inverse [simp]: "int_encode (int_decode n) = n"
unfolding int_decode_def int_encode_def using sum_decode_inverse [of n]
by (cases "sum_decode n", simp_all)

lemma inj_int_encode: "inj_on int_encode A"
by (rule inj_on_inverseI, rule int_encode_inverse)

lemma inj_int_decode: "inj_on int_decode A"
by (rule inj_on_inverseI, rule int_decode_inverse)

lemma surj_int_encode: "surj int_encode"
by (rule surjI, rule int_decode_inverse)

lemma surj_int_decode: "surj int_decode"
by (rule surjI, rule int_encode_inverse)

lemma bij_int_encode: "bij int_encode"
by (rule bijI [OF inj_int_encode surj_int_encode])

lemma bij_int_decode: "bij int_decode"
by (rule bijI [OF inj_int_decode surj_int_decode])

lemma int_encode_eq: "int_encode x = int_encode y \<longleftrightarrow> x = y"
by (rule inj_int_encode [THEN inj_eq])

lemma int_decode_eq: "int_decode x = int_decode y \<longleftrightarrow> x = y"
by (rule inj_int_decode [THEN inj_eq])


subsection {* Type @{typ "nat list"} *}

fun
  list_encode :: "nat list \<Rightarrow> nat"
where
  "list_encode [] = 0"
| "list_encode (x # xs) = Suc (prod_encode (x, list_encode xs))"

function
  list_decode :: "nat \<Rightarrow> nat list"
where
  "list_decode 0 = []"
| "list_decode (Suc n) = (case prod_decode n of (x, y) \<Rightarrow> x # list_decode y)"
by pat_completeness auto

termination list_decode
apply (relation "measure id", simp_all)
apply (drule arg_cong [where f="prod_encode"])
apply (drule sym)
apply (simp add: le_imp_less_Suc le_prod_encode_2)
done

lemma list_encode_inverse [simp]: "list_decode (list_encode x) = x"
by (induct x rule: list_encode.induct) simp_all

lemma list_decode_inverse [simp]: "list_encode (list_decode n) = n"
apply (induct n rule: list_decode.induct, simp)
apply (simp split: prod.split)
apply (simp add: prod_decode_eq [symmetric])
done

lemma inj_list_encode: "inj_on list_encode A"
by (rule inj_on_inverseI, rule list_encode_inverse)

lemma inj_list_decode: "inj_on list_decode A"
by (rule inj_on_inverseI, rule list_decode_inverse)

lemma surj_list_encode: "surj list_encode"
by (rule surjI, rule list_decode_inverse)

lemma surj_list_decode: "surj list_decode"
by (rule surjI, rule list_encode_inverse)

lemma bij_list_encode: "bij list_encode"
by (rule bijI [OF inj_list_encode surj_list_encode])

lemma bij_list_decode: "bij list_decode"
by (rule bijI [OF inj_list_decode surj_list_decode])

lemma list_encode_eq: "list_encode x = list_encode y \<longleftrightarrow> x = y"
by (rule inj_list_encode [THEN inj_eq])

lemma list_decode_eq: "list_decode x = list_decode y \<longleftrightarrow> x = y"
by (rule inj_list_decode [THEN inj_eq])


subsection {* Finite sets of naturals *}

subsubsection {* Preliminaries *}

lemma finite_vimage_Suc_iff: "finite (Suc -` F) \<longleftrightarrow> finite F"
apply (safe intro!: finite_vimageI inj_Suc)
apply (rule finite_subset [where B="insert 0 (Suc ` Suc -` F)"])
apply (rule subsetI, case_tac x, simp, simp)
apply (rule finite_insert [THEN iffD2])
apply (erule finite_imageI)
done

lemma vimage_Suc_insert_0: "Suc -` insert 0 A = Suc -` A"
by auto

lemma vimage_Suc_insert_Suc:
  "Suc -` insert (Suc n) A = insert n (Suc -` A)"
by auto

lemma div2_even_ext_nat:
  "x div 2 = y div 2 \<Longrightarrow> even x \<longleftrightarrow> even y \<Longrightarrow> (x::nat) = y"
apply (rule mod_div_equality [of x 2, THEN subst])
apply (rule mod_div_equality [of y 2, THEN subst])
apply (cases "even x")
apply (simp_all add: even_iff_mod_2_eq_zero)
done


subsubsection {* From sets to naturals *}

definition
  set_encode :: "nat set \<Rightarrow> nat"
where
  "set_encode = setsum (op ^ 2)"

lemma set_encode_empty [simp]: "set_encode {} = 0"
by (simp add: set_encode_def)

lemma set_encode_insert [simp]:
  "\<lbrakk>finite A; n \<notin> A\<rbrakk> \<Longrightarrow> set_encode (insert n A) = 2^n + set_encode A"
by (simp add: set_encode_def)

lemma even_set_encode_iff: "finite A \<Longrightarrow> even (set_encode A) \<longleftrightarrow> 0 \<notin> A"
unfolding set_encode_def by (induct set: finite, auto)

lemma set_encode_vimage_Suc: "set_encode (Suc -` A) = set_encode A div 2"
apply (cases "finite A")
apply (erule finite_induct, simp)
apply (case_tac x)
apply (simp add: even_set_encode_iff vimage_Suc_insert_0)
apply (simp add: finite_vimageI add.commute vimage_Suc_insert_Suc)
apply (simp add: set_encode_def finite_vimage_Suc_iff)
done

lemmas set_encode_div_2 = set_encode_vimage_Suc [symmetric]

subsubsection {* From naturals to sets *}

definition
  set_decode :: "nat \<Rightarrow> nat set"
where
  "set_decode x = {n. odd (x div 2 ^ n)}"

lemma set_decode_0 [simp]: "0 \<in> set_decode x \<longleftrightarrow> odd x"
by (simp add: set_decode_def)

lemma set_decode_Suc [simp]:
  "Suc n \<in> set_decode x \<longleftrightarrow> n \<in> set_decode (x div 2)"
by (simp add: set_decode_def div_mult2_eq)

lemma set_decode_zero [simp]: "set_decode 0 = {}"
by (simp add: set_decode_def)

lemma set_decode_div_2: "set_decode (x div 2) = Suc -` set_decode x"
by auto

lemma set_decode_plus_power_2:
  "n \<notin> set_decode z \<Longrightarrow> set_decode (2 ^ n + z) = insert n (set_decode z)"
 apply (induct n arbitrary: z, simp_all)
  apply (rule set_eqI, induct_tac x, simp, simp)
 apply (rule set_eqI, induct_tac x, simp, simp add: add.commute)
done

lemma finite_set_decode [simp]: "finite (set_decode n)"
apply (induct n rule: nat_less_induct)
apply (case_tac "n = 0", simp)
apply (drule_tac x="n div 2" in spec, simp)
apply (simp add: set_decode_div_2)
apply (simp add: finite_vimage_Suc_iff)
done

subsubsection {* Proof of isomorphism *}

lemma set_decode_inverse [simp]: "set_encode (set_decode n) = n"
apply (induct n rule: nat_less_induct)
apply (case_tac "n = 0", simp)
apply (drule_tac x="n div 2" in spec, simp)
apply (simp add: set_decode_div_2 set_encode_vimage_Suc)
apply (erule div2_even_ext_nat)
apply (simp add: even_set_encode_iff)
done

lemma set_encode_inverse [simp]: "finite A \<Longrightarrow> set_decode (set_encode A) = A"
apply (erule finite_induct, simp_all)
apply (simp add: set_decode_plus_power_2)
done

lemma inj_on_set_encode: "inj_on set_encode (Collect finite)"
by (rule inj_on_inverseI [where g="set_decode"], simp)

lemma set_encode_eq:
  "\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> set_encode A = set_encode B \<longleftrightarrow> A = B"
by (rule iffI, simp add: inj_onD [OF inj_on_set_encode], simp)

lemma subset_decode_imp_le: assumes "set_decode m \<subseteq> set_decode n" shows "m \<le> n"
proof -
  have "n = m + set_encode (set_decode n - set_decode m)"
  proof -
    obtain A B where "m = set_encode A" "finite A" 
                     "n = set_encode B" "finite B"
      by (metis finite_set_decode set_decode_inverse)
  thus ?thesis using assms
    apply auto
    apply (simp add: set_encode_def add.commute setsum.subset_diff)
    done
  qed
  thus ?thesis
    by (metis le_add1)
qed

end

