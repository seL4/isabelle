(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Type of indices *}

theory Code_Index
imports ATP_Linkup
begin

text {*
  Indices are isomorphic to HOL @{typ nat} but
  mapped to target-language builtin integers
*}

subsection {* Datatype of indices *}

datatype index = index_of_nat nat

lemma [code func]:
  "index_size k = 0"
  by (cases k) simp

lemmas [code func del] = index.recs index.cases

primrec
  nat_of_index :: "index \<Rightarrow> nat"
where
  "nat_of_index (index_of_nat k) = k"
lemmas [code func del] = nat_of_index.simps

lemma index_id [simp]:
  "index_of_nat (nat_of_index n) = n"
  by (cases n) simp_all

lemma nat_of_index_inject [simp]:
  "nat_of_index n = nat_of_index m \<longleftrightarrow> n = m"
  by (cases n) auto

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

lemma [code func]: "size (n\<Colon>index) = 0"
  by (cases n) simp_all


subsection {* Indices as datatype of ints *}

instantiation index :: number
begin

definition
  "number_of = index_of_nat o nat"

instance ..

end

code_datatype "number_of \<Colon> int \<Rightarrow> index"


subsection {* Basic arithmetic *}

instantiation index :: "{minus, ordered_semidom, Divides.div, linorder}"
begin

definition [simp, code func del]:
  "(0\<Colon>index) = index_of_nat 0"

lemma zero_index_code [code inline, code func]:
  "(0\<Colon>index) = Numeral0"
  by (simp add: number_of_index_def Pls_def)
lemma [code post]: "Numeral0 = (0\<Colon>index)"
  using zero_index_code ..

definition [simp, code func del]:
  "(1\<Colon>index) = index_of_nat 1"

lemma one_index_code [code inline, code func]:
  "(1\<Colon>index) = Numeral1"
  by (simp add: number_of_index_def Pls_def Bit_def)
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


subsection {* ML interface *}

ML {*
structure Index =
struct

fun mk k = HOLogic.mk_number @{typ index} k;

end;
*}


subsection {* Code serialization *}

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

code_const "op - \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.max/ (_/ -/ _,/ 0 : int)")
  (OCaml "Pervasives.max/ (_/ -/ _)/ (0 : int) ")
  (Haskell "max/ (_/ -/ _)/ (0 :: Int)")

code_const "op * \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.*/ ((_),/ (_))")
  (OCaml "Pervasives.( * )")
  (Haskell infixl 7 "*")

code_const "op div \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.div/ ((_),/ (_))")
  (OCaml "Pervasives.( / )")
  (Haskell "div")

code_const "op mod \<Colon> index \<Rightarrow> index \<Rightarrow> index"
  (SML "Int.mod/ ((_),/ (_))")
  (OCaml "Pervasives.( mod )")
  (Haskell "mod")

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

end
