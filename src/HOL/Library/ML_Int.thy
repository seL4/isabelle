(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Built-in integers for code generation *}

theory ML_Int
imports PreList
begin

subsection {* Datatype of built-in integers *}

datatype ml_int = ml_int_of_int int

lemmas [code func del] = ml_int.recs ml_int.cases

fun
  int_of_ml_int :: "ml_int \<Rightarrow> int"
where
  "int_of_ml_int (ml_int_of_int k) = k"
lemmas [code func del] = int_of_ml_int.simps

lemma ml_int_id [simp]:
  "ml_int_of_int (int_of_ml_int k) = k"
  by (cases k) simp_all

lemma ml_int:
  "(\<And>k\<Colon>ml_int. PROP P k) \<equiv> (\<And>k\<Colon>int. PROP P (ml_int_of_int k))"
proof
  fix k :: int
  assume "\<And>k\<Colon>ml_int. PROP P k"
  then show "PROP P (ml_int_of_int k)" .
next
  fix k :: ml_int
  assume "\<And>k\<Colon>int. PROP P (ml_int_of_int k)"
  then have "PROP P (ml_int_of_int (int_of_ml_int k))" .
  then show "PROP P k" by simp
qed

lemma [code func]: "size (k\<Colon>ml_int) = 0"
  by (cases k) simp_all


subsection {* Built-in integers as datatype on numerals *}

instance ml_int :: number
  "number_of \<equiv> ml_int_of_int" ..

code_datatype "number_of \<Colon> int \<Rightarrow> ml_int"

lemma number_of_ml_int_id [simp]:
  "number_of (int_of_ml_int k) = k"
  unfolding number_of_ml_int_def by simp

lemma number_of_ml_int_shift:
  "number_of k = ml_int_of_int (number_of k)"
  by (simp add: number_of_is_id number_of_ml_int_def)


subsection {* Basic arithmetic *}

instance ml_int :: zero
  [simp]: "0 \<equiv> ml_int_of_int 0" ..
lemmas [code func del] = zero_ml_int_def

instance ml_int :: one
  [simp]: "1 \<equiv> ml_int_of_int 1" ..
lemmas [code func del] = one_ml_int_def

instance ml_int :: plus
  [simp]: "k + l \<equiv> ml_int_of_int (int_of_ml_int k + int_of_ml_int l)" ..
lemmas [code func del] = plus_ml_int_def
lemma plus_ml_int_code [code func]:
  "ml_int_of_int k + ml_int_of_int l = ml_int_of_int (k + l)"
  unfolding plus_ml_int_def by simp

instance ml_int :: minus
  [simp]: "- k \<equiv> ml_int_of_int (- int_of_ml_int k)"
  [simp]: "k - l \<equiv> ml_int_of_int (int_of_ml_int k - int_of_ml_int l)" ..
lemmas [code func del] = uminus_ml_int_def minus_ml_int_def
lemma uminus_ml_int_code [code func]:
  "- ml_int_of_int k \<equiv> ml_int_of_int (- k)"
  unfolding uminus_ml_int_def by simp
lemma minus_ml_int_code [code func]:
  "ml_int_of_int k - ml_int_of_int l = ml_int_of_int (k - l)"
  unfolding minus_ml_int_def by simp

instance ml_int :: times
  [simp]: "k * l \<equiv> ml_int_of_int (int_of_ml_int k * int_of_ml_int l)" ..
lemmas [code func del] = times_ml_int_def
lemma times_ml_int_code [code func]:
  "ml_int_of_int k * ml_int_of_int l = ml_int_of_int (k * l)"
  unfolding times_ml_int_def by simp

instance ml_int :: ord
  [simp]: "k \<le> l \<equiv> int_of_ml_int k \<le> int_of_ml_int l"
  [simp]: "k < l \<equiv> int_of_ml_int k < int_of_ml_int l" ..
lemmas [code func del] = less_eq_ml_int_def less_ml_int_def
lemma less_eq_ml_int_code [code func]:
  "ml_int_of_int k \<le> ml_int_of_int l \<longleftrightarrow> k \<le> l"
  unfolding less_eq_ml_int_def by simp
lemma less_ml_int_code [code func]:
  "ml_int_of_int k < ml_int_of_int l \<longleftrightarrow> k < l"
  unfolding less_ml_int_def by simp

instance ml_int :: ring_1
  by default (auto simp add: left_distrib right_distrib)

lemma of_nat_ml_int: "of_nat n = ml_int_of_int (of_nat n)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  then have "int_of_ml_int (ml_int_of_int (int n))
    = int_of_ml_int (of_nat n)" by simp
  then have "int n = int_of_ml_int (of_nat n)" by simp
  then show ?case by simp
qed

instance ml_int :: number_ring
  by default
    (simp_all add: left_distrib number_of_ml_int_def of_int_of_nat of_nat_ml_int)

lemma zero_ml_int_code [code inline, code func]:
  "(0\<Colon>ml_int) = Numeral0"
  by simp

lemma one_ml_int_code [code inline, code func]:
  "(1\<Colon>ml_int) = Numeral1"
  by simp

instance ml_int :: abs
  "\<bar>k\<bar> \<equiv> if k < 0 then -k else k" ..

lemma ml_int_of_int [code func]:
  "ml_int_of_int k = (if k = 0 then 0
    else if k = -1 then -1
    else let (l, m) = divAlg (k, 2) in 2 * ml_int_of_int l +
      (if m = 0 then 0 else 1))"
  by (simp add: number_of_ml_int_shift Let_def split_def divAlg_mod_div) arith


subsection {* Conversion to and from @{typ nat} *}

definition
  nat_of_ml_int :: "ml_int \<Rightarrow> nat"
where
  [code func del]: "nat_of_ml_int = nat o int_of_ml_int"

definition
  nat_of_ml_int_aux :: "ml_int \<Rightarrow> nat \<Rightarrow> nat" where
  [code func del]: "nat_of_ml_int_aux i n = nat_of_ml_int i + n"

lemma nat_of_ml_int_aux_code [code]:
  "nat_of_ml_int_aux i n = (if i \<le> 0 then n else nat_of_ml_int_aux (i - 1) (Suc n))"
  by (auto simp add: nat_of_ml_int_aux_def nat_of_ml_int_def)

lemma nat_of_ml_int_code [code]:
  "nat_of_ml_int i = nat_of_ml_int_aux i 0"
  by (simp add: nat_of_ml_int_aux_def)

definition
  ml_int_of_nat :: "nat \<Rightarrow> ml_int"
where
  [code func del]: "ml_int_of_nat = ml_int_of_int o of_nat"

lemma ml_int_of_nat [code func]:
  "ml_int_of_nat 0 = 0"
  "ml_int_of_nat (Suc n) = ml_int_of_nat n + 1"
  unfolding ml_int_of_nat_def by simp_all

lemma ml_int_nat_id [simp]:
  "nat_of_ml_int (ml_int_of_nat n) = n"
  "ml_int_of_nat (nat_of_ml_int i) = (if i \<le> 0 then 0 else i)"
  unfolding ml_int_of_nat_def nat_of_ml_int_def by simp_all


subsection {* ML interface *}

ML {*
structure ML_Int =
struct

fun mk k = @{term ml_int_of_int} $ HOLogic.mk_number @{typ ml_int} k;

end;
*}


subsection {* Code serialization *}

code_type ml_int
  (SML "int")
  (OCaml "int")
  (Haskell "Integer")

code_instance ml_int :: eq
  (Haskell -)

setup {*
  fold (fn target => CodeTarget.add_pretty_numeral target true
    @{const_name number_ml_int_inst.number_of_ml_int}
    @{const_name Numeral.B0} @{const_name Numeral.B1}
    @{const_name Numeral.Pls} @{const_name Numeral.Min}
    @{const_name Numeral.Bit}
  ) ["SML", "OCaml", "Haskell"]
*}

code_reserved SML int
code_reserved OCaml int

code_const "op + \<Colon> ml_int \<Rightarrow> ml_int \<Rightarrow> ml_int"
  (SML "Int.+ ((_), (_))")
  (OCaml "Pervasives.+")
  (Haskell infixl 6 "+")

code_const "uminus \<Colon> ml_int \<Rightarrow> ml_int"
  (SML "Int.~")
  (OCaml "Pervasives.~-")
  (Haskell "negate")

code_const "op - \<Colon> ml_int \<Rightarrow> ml_int \<Rightarrow> ml_int"
  (SML "Int.- ((_), (_))")
  (OCaml "Pervasives.-")
  (Haskell infixl 6 "-")

code_const "op * \<Colon> ml_int \<Rightarrow> ml_int \<Rightarrow> ml_int"
  (SML "Int.* ((_), (_))")
  (OCaml "Pervasives.*")
  (Haskell infixl 7 "*")

code_const "op = \<Colon> ml_int \<Rightarrow> ml_int \<Rightarrow> bool"
  (SML "!((_ : Int.int) = _)")
  (OCaml "!((_ : Pervasives.int) = _)")
  (Haskell infixl 4 "==")

code_const "op \<le> \<Colon> ml_int \<Rightarrow> ml_int \<Rightarrow> bool"
  (SML "Int.<= ((_), (_))")
  (OCaml "!((_ : Pervasives.int) <= _)")
  (Haskell infix 4 "<=")

code_const "op < \<Colon> ml_int \<Rightarrow> ml_int \<Rightarrow> bool"
  (SML "Int.< ((_), (_))")
  (OCaml "!((_ : Pervasives.int) < _)")
  (Haskell infix 4 "<")

code_reserved SML Int
code_reserved OCaml Pervasives

end
