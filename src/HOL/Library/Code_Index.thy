(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Type of indices *}

theory Code_Index
imports PreList
begin

text {*
  Indices are isomorphic to HOL @{typ int} but
  mapped to target-language builtin integers
*}

subsection {* Datatype of indices *}

datatype index = index_of_int int

lemmas [code func del] = index.recs index.cases

fun
  int_of_index :: "index \<Rightarrow> int"
where
  "int_of_index (index_of_int k) = k"
lemmas [code func del] = int_of_index.simps

lemma index_id [simp]:
  "index_of_int (int_of_index k) = k"
  by (cases k) simp_all

lemma index:
  "(\<And>k\<Colon>index. PROP P k) \<equiv> (\<And>k\<Colon>int. PROP P (index_of_int k))"
proof
  fix k :: int
  assume "\<And>k\<Colon>index. PROP P k"
  then show "PROP P (index_of_int k)" .
next
  fix k :: index
  assume "\<And>k\<Colon>int. PROP P (index_of_int k)"
  then have "PROP P (index_of_int (int_of_index k))" .
  then show "PROP P k" by simp
qed

lemma [code func]: "size (k\<Colon>index) = 0"
  by (cases k) simp_all


subsection {* Built-in integers as datatype on numerals *}

instance index :: number
  "number_of \<equiv> index_of_int" ..

code_datatype "number_of \<Colon> int \<Rightarrow> index"

lemma number_of_index_id [simp]:
  "number_of (int_of_index k) = k"
  unfolding number_of_index_def by simp

lemma number_of_index_shift:
  "number_of k = index_of_int (number_of k)"
  by (simp add: number_of_is_id number_of_index_def)


subsection {* Basic arithmetic *}

instance index :: zero
  [simp]: "0 \<equiv> index_of_int 0" ..
lemmas [code func del] = zero_index_def

instance index :: one
  [simp]: "1 \<equiv> index_of_int 1" ..
lemmas [code func del] = one_index_def

instance index :: plus
  [simp]: "k + l \<equiv> index_of_int (int_of_index k + int_of_index l)" ..
lemmas [code func del] = plus_index_def
lemma plus_index_code [code func]:
  "index_of_int k + index_of_int l = index_of_int (k + l)"
  unfolding plus_index_def by simp

instance index :: minus
  [simp]: "- k \<equiv> index_of_int (- int_of_index k)"
  [simp]: "k - l \<equiv> index_of_int (int_of_index k - int_of_index l)" ..
lemmas [code func del] = uminus_index_def minus_index_def
lemma uminus_index_code [code func]:
  "- index_of_int k \<equiv> index_of_int (- k)"
  unfolding uminus_index_def by simp
lemma minus_index_code [code func]:
  "index_of_int k - index_of_int l = index_of_int (k - l)"
  unfolding minus_index_def by simp

instance index :: times
  [simp]: "k * l \<equiv> index_of_int (int_of_index k * int_of_index l)" ..
lemmas [code func del] = times_index_def
lemma times_index_code [code func]:
  "index_of_int k * index_of_int l = index_of_int (k * l)"
  unfolding times_index_def by simp

instance index :: ord
  [simp]: "k \<le> l \<equiv> int_of_index k \<le> int_of_index l"
  [simp]: "k < l \<equiv> int_of_index k < int_of_index l" ..
lemmas [code func del] = less_eq_index_def less_index_def
lemma less_eq_index_code [code func]:
  "index_of_int k \<le> index_of_int l \<longleftrightarrow> k \<le> l"
  unfolding less_eq_index_def by simp
lemma less_index_code [code func]:
  "index_of_int k < index_of_int l \<longleftrightarrow> k < l"
  unfolding less_index_def by simp

instance index :: ring_1
  by default (auto simp add: left_distrib right_distrib)

lemma of_nat_index: "of_nat n = index_of_int (of_nat n)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  then have "int_of_index (index_of_int (int n))
    = int_of_index (of_nat n)" by simp
  then have "int n = int_of_index (of_nat n)" by simp
  then show ?case by simp
qed

instance index :: number_ring
  by default
    (simp_all add: left_distrib number_of_index_def of_int_of_nat of_nat_index)

lemma zero_index_code [code inline, code func]:
  "(0\<Colon>index) = Numeral0"
  by simp

lemma one_index_code [code inline, code func]:
  "(1\<Colon>index) = Numeral1"
  by simp

instance index :: abs
  "\<bar>k\<bar> \<equiv> if k < 0 then -k else k" ..

lemma index_of_int [code func]:
  "index_of_int k = (if k = 0 then 0
    else if k = -1 then -1
    else let (l, m) = divAlg (k, 2) in 2 * index_of_int l +
      (if m = 0 then 0 else 1))"
  by (simp add: number_of_index_shift Let_def split_def divAlg_mod_div) arith


subsection {* Conversion to and from @{typ nat} *}

definition
  nat_of_index :: "index \<Rightarrow> nat"
where
  [code func del]: "nat_of_index = nat o int_of_index"

definition
  nat_of_index_aux :: "index \<Rightarrow> nat \<Rightarrow> nat" where
  [code func del]: "nat_of_index_aux i n = nat_of_index i + n"

lemma nat_of_index_aux_code [code]:
  "nat_of_index_aux i n = (if i \<le> 0 then n else nat_of_index_aux (i - 1) (Suc n))"
  by (auto simp add: nat_of_index_aux_def nat_of_index_def)

lemma nat_of_index_code [code]:
  "nat_of_index i = nat_of_index_aux i 0"
  by (simp add: nat_of_index_aux_def)

definition
  index_of_nat :: "nat \<Rightarrow> index"
where
  [code func del]: "index_of_nat = index_of_int o of_nat"

lemma index_of_nat [code func]:
  "index_of_nat 0 = 0"
  "index_of_nat (Suc n) = index_of_nat n + 1"
  unfolding index_of_nat_def by simp_all

lemma index_nat_id [simp]:
  "nat_of_index (index_of_nat n) = n"
  "index_of_nat (nat_of_index i) = (if i \<le> 0 then 0 else i)"
  unfolding index_of_nat_def nat_of_index_def by simp_all


subsection {* ML interface *}

ML {*
structure Index =
struct

fun mk k = @{term index_of_int} $ HOLogic.mk_number @{typ index} k;

end;
*}


subsection {* Code serialization *}

code_type index
  (SML "int")
  (OCaml "int")
  (Haskell "Integer")

code_instance index :: eq
  (Haskell -)

setup {*
  fold (fn target => CodeTarget.add_pretty_numeral target true
    @{const_name number_index_inst.number_of_index}
    @{const_name Numeral.B0} @{const_name Numeral.B1}
    @{const_name Numeral.Pls} @{const_name Numeral.Min}
    @{const_name Numeral.Bit}
  ) ["SML", "OCaml", "Haskell"]
*}

code_reserved SML int
code_reserved OCaml int

code_const "op + \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.+ ((_), (_))")
  (OCaml "Pervasives.+")
  (Haskell infixl 6 "+")

code_const "uminus \<Colon> index \<Rightarrow> index"
  (SML "Int.~")
  (OCaml "Pervasives.~-")
  (Haskell "negate")

code_const "op - \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.- ((_), (_))")
  (OCaml "Pervasives.-")
  (Haskell infixl 6 "-")

code_const "op * \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.* ((_), (_))")
  (OCaml "Pervasives.*")
  (Haskell infixl 7 "*")

code_const "op = \<Colon> index \<Rightarrow> index \<Rightarrow> bool"
  (SML "!((_ : Int.int) = _)")
  (OCaml "!((_ : Pervasives.int) = _)")
  (Haskell infixl 4 "==")

code_const "op \<le> \<Colon> index \<Rightarrow> index \<Rightarrow> bool"
  (SML "Int.<= ((_), (_))")
  (OCaml "!((_ : Pervasives.int) <= _)")
  (Haskell infix 4 "<=")

code_const "op < \<Colon> index \<Rightarrow> index \<Rightarrow> bool"
  (SML "Int.< ((_), (_))")
  (OCaml "!((_ : Pervasives.int) < _)")
  (Haskell infix 4 "<")

code_reserved SML Int
code_reserved OCaml Pervasives

end
