(* Author: Florian Haftmann, TU Muenchen *)

header {* Type of indices *}

theory Code_Index
imports Main
begin

text {*
  Indices are isomorphic to HOL @{typ nat} but
  mapped to target-language builtin integers.
*}

subsection {* Datatype of indices *}

typedef (open) index = "UNIV \<Colon> nat set"
  morphisms nat_of of_nat by rule

lemma of_nat_nat_of [simp]:
  "of_nat (nat_of k) = k"
  by (rule nat_of_inverse)

lemma nat_of_of_nat [simp]:
  "nat_of (of_nat n) = n"
  by (rule of_nat_inverse) (rule UNIV_I)

lemma [measure_function]:
  "is_measure nat_of" by (rule is_measure_trivial)

lemma index:
  "(\<And>n\<Colon>index. PROP P n) \<equiv> (\<And>n\<Colon>nat. PROP P (of_nat n))"
proof
  fix n :: nat
  assume "\<And>n\<Colon>index. PROP P n"
  then show "PROP P (of_nat n)" .
next
  fix n :: index
  assume "\<And>n\<Colon>nat. PROP P (of_nat n)"
  then have "PROP P (of_nat (nat_of n))" .
  then show "PROP P n" by simp
qed

lemma index_case:
  assumes "\<And>n. k = of_nat n \<Longrightarrow> P"
  shows P
  by (rule assms [of "nat_of k"]) simp

lemma index_induct_raw:
  assumes "\<And>n. P (of_nat n)"
  shows "P k"
proof -
  from assms have "P (of_nat (nat_of k))" .
  then show ?thesis by simp
qed

lemma nat_of_inject [simp]:
  "nat_of k = nat_of l \<longleftrightarrow> k = l"
  by (rule nat_of_inject)

lemma of_nat_inject [simp]:
  "of_nat n = of_nat m \<longleftrightarrow> n = m"
  by (rule of_nat_inject) (rule UNIV_I)+

instantiation index :: zero
begin

definition [simp, code del]:
  "0 = of_nat 0"

instance ..

end

definition [simp]:
  "Suc_index k = of_nat (Suc (nat_of k))"

rep_datatype "0 \<Colon> index" Suc_index
proof -
  fix P :: "index \<Rightarrow> bool"
  fix k :: index
  assume "P 0" then have init: "P (of_nat 0)" by simp
  assume "\<And>k. P k \<Longrightarrow> P (Suc_index k)"
    then have "\<And>n. P (of_nat n) \<Longrightarrow> P (Suc_index (of_nat n))" .
    then have step: "\<And>n. P (of_nat n) \<Longrightarrow> P (of_nat (Suc n))" by simp
  from init step have "P (of_nat (nat_of k))"
    by (induct "nat_of k") simp_all
  then show "P k" by simp
qed simp_all

declare index_case [case_names nat, cases type: index]
declare index.induct [case_names nat, induct type: index]

lemma index_decr [termination_simp]:
  "k \<noteq> Code_Index.of_nat 0 \<Longrightarrow> Code_Index.nat_of k - Suc 0 < Code_Index.nat_of k"
  by (cases k) simp

lemma [simp, code]:
  "index_size = nat_of"
proof (rule ext)
  fix k
  have "index_size k = nat_size (nat_of k)"
    by (induct k rule: index.induct) (simp_all del: zero_index_def Suc_index_def, simp_all)
  also have "nat_size (nat_of k) = nat_of k" by (induct "nat_of k") simp_all
  finally show "index_size k = nat_of k" .
qed

lemma [simp, code]:
  "size = nat_of"
proof (rule ext)
  fix k
  show "size k = nat_of k"
  by (induct k) (simp_all del: zero_index_def Suc_index_def, simp_all)
qed

lemmas [code del] = index.recs index.cases

lemma [code]:
  "eq_class.eq k l \<longleftrightarrow> eq_class.eq (nat_of k) (nat_of l)"
  by (cases k, cases l) (simp add: eq)

lemma [code nbe]:
  "eq_class.eq (k::index) k \<longleftrightarrow> True"
  by (rule HOL.eq_refl)


subsection {* Indices as datatype of ints *}

instantiation index :: number
begin

definition
  "number_of = of_nat o nat"

instance ..

end

lemma nat_of_number [simp]:
  "nat_of (number_of k) = number_of k"
  by (simp add: number_of_index_def nat_number_of_def number_of_is_id)

code_datatype "number_of \<Colon> int \<Rightarrow> index"


subsection {* Basic arithmetic *}

instantiation index :: "{minus, ordered_semidom, semiring_div, linorder}"
begin

definition [simp, code del]:
  "(1\<Colon>index) = of_nat 1"

definition [simp, code del]:
  "n + m = of_nat (nat_of n + nat_of m)"

definition [simp, code del]:
  "n - m = of_nat (nat_of n - nat_of m)"

definition [simp, code del]:
  "n * m = of_nat (nat_of n * nat_of m)"

definition [simp, code del]:
  "n div m = of_nat (nat_of n div nat_of m)"

definition [simp, code del]:
  "n mod m = of_nat (nat_of n mod nat_of m)"

definition [simp, code del]:
  "n \<le> m \<longleftrightarrow> nat_of n \<le> nat_of m"

definition [simp, code del]:
  "n < m \<longleftrightarrow> nat_of n < nat_of m"

instance proof
qed (auto simp add: index left_distrib div_mult_self1)

end

lemma zero_index_code [code inline, code]:
  "(0\<Colon>index) = Numeral0"
  by (simp add: number_of_index_def Pls_def)
lemma [code post]: "Numeral0 = (0\<Colon>index)"
  using zero_index_code ..

lemma one_index_code [code inline, code]:
  "(1\<Colon>index) = Numeral1"
  by (simp add: number_of_index_def Pls_def Bit1_def)
lemma [code post]: "Numeral1 = (1\<Colon>index)"
  using one_index_code ..

lemma plus_index_code [code nbe]:
  "of_nat n + of_nat m = of_nat (n + m)"
  by simp

definition subtract_index :: "index \<Rightarrow> index \<Rightarrow> index" where
  [simp, code del]: "subtract_index = op -"

lemma subtract_index_code [code nbe]:
  "subtract_index (of_nat n) (of_nat m) = of_nat (n - m)"
  by simp

lemma minus_index_code [code]:
  "n - m = subtract_index n m"
  by simp

lemma times_index_code [code nbe]:
  "of_nat n * of_nat m = of_nat (n * m)"
  by simp

lemma less_eq_index_code [code nbe]:
  "of_nat n \<le> of_nat m \<longleftrightarrow> n \<le> m"
  by simp

lemma less_index_code [code nbe]:
  "of_nat n < of_nat m \<longleftrightarrow> n < m"
  by simp

lemma Suc_index_minus_one: "Suc_index n - 1 = n" by simp

lemma of_nat_code [code]:
  "of_nat = Nat.of_nat"
proof
  fix n :: nat
  have "Nat.of_nat n = of_nat n"
    by (induct n) simp_all
  then show "of_nat n = Nat.of_nat n"
    by (rule sym)
qed

lemma index_not_eq_zero: "i \<noteq> of_nat 0 \<longleftrightarrow> i \<ge> 1"
  by (cases i) auto

definition nat_of_aux :: "index \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_of_aux i n = nat_of i + n"

lemma nat_of_aux_code [code]:
  "nat_of_aux i n = (if i = 0 then n else nat_of_aux (i - 1) (Suc n))"
  by (auto simp add: nat_of_aux_def index_not_eq_zero)

lemma nat_of_code [code]:
  "nat_of i = nat_of_aux i 0"
  by (simp add: nat_of_aux_def)

definition div_mod_index ::  "index \<Rightarrow> index \<Rightarrow> index \<times> index" where
  [code del]: "div_mod_index n m = (n div m, n mod m)"

lemma [code]:
  "div_mod_index n m = (if m = 0 then (0, n) else (n div m, n mod m))"
  unfolding div_mod_index_def by auto

lemma [code]:
  "n div m = fst (div_mod_index n m)"
  unfolding div_mod_index_def by simp

lemma [code]:
  "n mod m = snd (div_mod_index n m)"
  unfolding div_mod_index_def by simp

hide (open) const of_nat nat_of

subsection {* ML interface *}

ML {*
structure Index =
struct

fun mk k = HOLogic.mk_number @{typ index} k;

end;
*}


subsection {* Code generator setup *}

text {* Implementation of indices by bounded integers *}

code_type index
  (SML "int")
  (OCaml "int")
  (Haskell "Int")

code_instance index :: eq
  (Haskell -)

setup {*
  fold (Numeral.add_code @{const_name number_index_inst.number_of_index}
    false false) ["SML", "OCaml", "Haskell"]
*}

code_reserved SML Int int
code_reserved OCaml Pervasives int

code_const "op + \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.+/ ((_),/ (_))")
  (OCaml "Pervasives.( + )")
  (Haskell infixl 6 "+")

code_const "subtract_index \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.max/ (_/ -/ _,/ 0 : int)")
  (OCaml "Pervasives.max/ (_/ -/ _)/ (0 : int) ")
  (Haskell "max/ (_/ -/ _)/ (0 :: Int)")

code_const "op * \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.*/ ((_),/ (_))")
  (OCaml "Pervasives.( * )")
  (Haskell infixl 7 "*")

code_const div_mod_index
  (SML "(fn n => fn m =>/ if m = 0/ then (0, n) else/ (n div m, n mod m))")
  (OCaml "(fun n -> fun m ->/ if m = 0/ then (0, n) else/ (n '/ m, n mod m))")
  (Haskell "divMod")

code_const "eq_class.eq \<Colon> index \<Rightarrow> index \<Rightarrow> bool"
  (SML "!((_ : Int.int) = _)")
  (OCaml "!((_ : int) = _)")
  (Haskell infixl 4 "==")

code_const "op \<le> \<Colon> index \<Rightarrow> index \<Rightarrow> bool"
  (SML "Int.<=/ ((_),/ (_))")
  (OCaml "!((_ : int) <= _)")
  (Haskell infix 4 "<=")

code_const "op < \<Colon> index \<Rightarrow> index \<Rightarrow> bool"
  (SML "Int.</ ((_),/ (_))")
  (OCaml "!((_ : int) < _)")
  (Haskell infix 4 "<")

text {* Evaluation *}

lemma [code, code del]:
  "(Code_Eval.term_of \<Colon> index \<Rightarrow> term) = Code_Eval.term_of" ..

code_const "Code_Eval.term_of \<Colon> index \<Rightarrow> term"
  (SML "HOLogic.mk'_number/ HOLogic.indexT/ (IntInf.fromInt/ _)")

end
