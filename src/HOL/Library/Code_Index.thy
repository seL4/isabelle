(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Type of indices *}

theory Code_Index
imports Plain "~~/src/HOL/Code_Eval" "~~/src/HOL/Presburger"
begin

text {*
  Indices are isomorphic to HOL @{typ nat} but
  mapped to target-language builtin integers.
*}

subsection {* Datatype of indices *}

typedef index = "UNIV \<Colon> nat set"
  morphisms nat_of_index index_of_nat by rule

lemma index_of_nat_nat_of_index [simp]:
  "index_of_nat (nat_of_index k) = k"
  by (rule nat_of_index_inverse)

lemma nat_of_index_index_of_nat [simp]:
  "nat_of_index (index_of_nat n) = n"
  by (rule index_of_nat_inverse) 
    (unfold index_def, rule UNIV_I)

lemma index:
  "(\<And>n\<Colon>index. PROP P n) \<equiv> (\<And>n\<Colon>nat. PROP P (index_of_nat n))"
proof
  fix n :: nat
  assume "\<And>n\<Colon>index. PROP P n"
  then show "PROP P (index_of_nat n)" .
next
  fix n :: index
  assume "\<And>n\<Colon>nat. PROP P (index_of_nat n)"
  then have "PROP P (index_of_nat (nat_of_index n))" .
  then show "PROP P n" by simp
qed

lemma index_case:
  assumes "\<And>n. k = index_of_nat n \<Longrightarrow> P"
  shows P
  by (rule assms [of "nat_of_index k"]) simp

lemma index_induct_raw:
  assumes "\<And>n. P (index_of_nat n)"
  shows "P k"
proof -
  from assms have "P (index_of_nat (nat_of_index k))" .
  then show ?thesis by simp
qed

lemma nat_of_index_inject [simp]:
  "nat_of_index k = nat_of_index l \<longleftrightarrow> k = l"
  by (rule nat_of_index_inject)

lemma index_of_nat_inject [simp]:
  "index_of_nat n = index_of_nat m \<longleftrightarrow> n = m"
  by (auto intro!: index_of_nat_inject simp add: index_def)

instantiation index :: zero
begin

definition [simp, code func del]:
  "0 = index_of_nat 0"

instance ..

end

definition [simp]:
  "Suc_index k = index_of_nat (Suc (nat_of_index k))"

rep_datatype "0 \<Colon> index" Suc_index
proof -
  fix P :: "index \<Rightarrow> bool"
  fix k :: index
  assume "P 0" then have init: "P (index_of_nat 0)" by simp
  assume "\<And>k. P k \<Longrightarrow> P (Suc_index k)"
    then have "\<And>n. P (index_of_nat n) \<Longrightarrow> P (Suc_index (index_of_nat n))" .
    then have step: "\<And>n. P (index_of_nat n) \<Longrightarrow> P (index_of_nat (Suc n))" by simp
  from init step have "P (index_of_nat (nat_of_index k))"
    by (induct "nat_of_index k") simp_all
  then show "P k" by simp
qed simp_all

lemmas [code func del] = index.recs index.cases

declare index_case [case_names nat, cases type: index]
declare index.induct [case_names nat, induct type: index]

lemma [code func]:
  "index_size = nat_of_index"
proof (rule ext)
  fix k
  have "index_size k = nat_size (nat_of_index k)"
    by (induct k rule: index.induct) (simp_all del: zero_index_def Suc_index_def, simp_all)
  also have "nat_size (nat_of_index k) = nat_of_index k" by (induct "nat_of_index k") simp_all
  finally show "index_size k = nat_of_index k" .
qed

lemma [code func]:
  "size = nat_of_index"
proof (rule ext)
  fix k
  show "size k = nat_of_index k"
  by (induct k) (simp_all del: zero_index_def Suc_index_def, simp_all)
qed

lemma [code func]:
  "k = l \<longleftrightarrow> nat_of_index k = nat_of_index l"
  by (cases k, cases l) simp


subsection {* Indices as datatype of ints *}

instantiation index :: number
begin

definition
  "number_of = index_of_nat o nat"

instance ..

end

lemma nat_of_index_number [simp]:
  "nat_of_index (number_of k) = number_of k"
  by (simp add: number_of_index_def nat_number_of_def number_of_is_id)

code_datatype "number_of \<Colon> int \<Rightarrow> index"


subsection {* Basic arithmetic *}

instantiation index :: "{minus, ordered_semidom, Divides.div, linorder}"
begin

lemma zero_index_code [code inline, code func]:
  "(0\<Colon>index) = Numeral0"
  by (simp add: number_of_index_def Pls_def)
lemma [code post]: "Numeral0 = (0\<Colon>index)"
  using zero_index_code ..

definition [simp, code func del]:
  "(1\<Colon>index) = index_of_nat 1"

lemma one_index_code [code inline, code func]:
  "(1\<Colon>index) = Numeral1"
  by (simp add: number_of_index_def Pls_def Bit1_def)
lemma [code post]: "Numeral1 = (1\<Colon>index)"
  using one_index_code ..

definition [simp, code func del]:
  "n + m = index_of_nat (nat_of_index n + nat_of_index m)"

lemma plus_index_code [code func]:
  "index_of_nat n + index_of_nat m = index_of_nat (n + m)"
  by simp

definition [simp, code func del]:
  "n - m = index_of_nat (nat_of_index n - nat_of_index m)"

definition [simp, code func del]:
  "n * m = index_of_nat (nat_of_index n * nat_of_index m)"

lemma times_index_code [code func]:
  "index_of_nat n * index_of_nat m = index_of_nat (n * m)"
  by simp

definition [simp, code func del]:
  "n div m = index_of_nat (nat_of_index n div nat_of_index m)"

definition [simp, code func del]:
  "n mod m = index_of_nat (nat_of_index n mod nat_of_index m)"

lemma div_index_code [code func]:
  "index_of_nat n div index_of_nat m = index_of_nat (n div m)"
  by simp

lemma mod_index_code [code func]:
  "index_of_nat n mod index_of_nat m = index_of_nat (n mod m)"
  by simp

definition [simp, code func del]:
  "n \<le> m \<longleftrightarrow> nat_of_index n \<le> nat_of_index m"

definition [simp, code func del]:
  "n < m \<longleftrightarrow> nat_of_index n < nat_of_index m"

lemma less_eq_index_code [code func]:
  "index_of_nat n \<le> index_of_nat m \<longleftrightarrow> n \<le> m"
  by simp

lemma less_index_code [code func]:
  "index_of_nat n < index_of_nat m \<longleftrightarrow> n < m"
  by simp

instance by default (auto simp add: left_distrib index)

end

lemma Suc_index_minus_one: "Suc_index n - 1 = n" by simp

lemma index_of_nat_code [code]:
  "index_of_nat = of_nat"
proof
  fix n :: nat
  have "of_nat n = index_of_nat n"
    by (induct n) simp_all
  then show "index_of_nat n = of_nat n"
    by (rule sym)
qed

lemma index_not_eq_zero: "i \<noteq> index_of_nat 0 \<longleftrightarrow> i \<ge> 1"
  by (cases i) auto

definition
  nat_of_index_aux :: "index \<Rightarrow> nat \<Rightarrow> nat"
where
  "nat_of_index_aux i n = nat_of_index i + n"

lemma nat_of_index_aux_code [code]:
  "nat_of_index_aux i n = (if i = 0 then n else nat_of_index_aux (i - 1) (Suc n))"
  by (auto simp add: nat_of_index_aux_def index_not_eq_zero)

lemma nat_of_index_code [code]:
  "nat_of_index i = nat_of_index_aux i 0"
  by (simp add: nat_of_index_aux_def)


text {* Measure function (for termination proofs) *}

lemma [measure_function]:
  "is_measure nat_of_index" by (rule is_measure_trivial)

subsection {* ML interface *}

ML {*
structure Index =
struct

fun mk k = HOLogic.mk_number @{typ index} k;

end;
*}


subsection {* Specialized @{term "op - \<Colon> index \<Rightarrow> index \<Rightarrow> index"},
  @{term "op div \<Colon> index \<Rightarrow> index \<Rightarrow> index"} and @{term "op mod \<Colon> index \<Rightarrow> index \<Rightarrow> index"}
  operations *}

definition
  minus_index_aux :: "index \<Rightarrow> index \<Rightarrow> index"
where
  [code func del]: "minus_index_aux = op -"

lemma [code func]: "op - = minus_index_aux"
  using minus_index_aux_def ..

definition
  div_mod_index ::  "index \<Rightarrow> index \<Rightarrow> index \<times> index"
where
  [code func del]: "div_mod_index n m = (n div m, n mod m)"

lemma [code func]:
  "div_mod_index n m = (if m = 0 then (0, n) else (n div m, n mod m))"
  unfolding div_mod_index_def by auto

lemma [code func]:
  "n div m = fst (div_mod_index n m)"
  unfolding div_mod_index_def by simp

lemma [code func]:
  "n mod m = snd (div_mod_index n m)"
  unfolding div_mod_index_def by simp


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

code_const "minus_index_aux \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.max/ (_/ -/ _,/ 0 : int)")
  (OCaml "Pervasives.max/ (_/ -/ _)/ (0 : int) ")
  (Haskell "max/ (_/ -/ _)/ (0 :: Int)")

code_const "op * \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.*/ ((_),/ (_))")
  (OCaml "Pervasives.( * )")
  (Haskell infixl 7 "*")

code_const div_mod_index
  (SML "(fn n => fn m =>/ (n div m, n mod m))")
  (OCaml "(fun n -> fun m ->/ (n '/ m, n mod m))")
  (Haskell "divMod")

code_const "op = \<Colon> index \<Rightarrow> index \<Rightarrow> bool"
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

lemma [code func, code func del]:
  "(Code_Eval.term_of \<Colon> index \<Rightarrow> term) = Code_Eval.term_of" ..

code_const "Code_Eval.term_of \<Colon> index \<Rightarrow> term"
  (SML "HOLogic.mk'_number/ HOLogic.indexT/ (IntInf.fromInt/ _)")

end
