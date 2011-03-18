(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Counterexample generator preforming narrowing-based testing *}

theory Quickcheck_Narrowing
imports Main "~~/src/HOL/Library/Code_Char"
uses
  ("~~/src/HOL/Tools/Quickcheck/narrowing_generators.ML")
begin

subsection {* Counterexample generator *}

subsubsection {* Code generation setup *}

code_type typerep
  ("Haskell" "Typerep")

code_const Typerep.Typerep
  ("Haskell" "Typerep")

code_reserved Haskell Typerep

subsubsection {* Type @{text "code_int"} for Haskell's Int type *}

typedef (open) code_int = "UNIV \<Colon> int set"
  morphisms int_of of_int by rule

lemma of_int_int_of [simp]:
  "of_int (int_of k) = k"
  by (rule int_of_inverse)

lemma int_of_of_int [simp]:
  "int_of (of_int n) = n"
  by (rule of_int_inverse) (rule UNIV_I)

lemma code_int:
  "(\<And>n\<Colon>code_int. PROP P n) \<equiv> (\<And>n\<Colon>int. PROP P (of_int n))"
proof
  fix n :: int
  assume "\<And>n\<Colon>code_int. PROP P n"
  then show "PROP P (of_int n)" .
next
  fix n :: code_int
  assume "\<And>n\<Colon>int. PROP P (of_int n)"
  then have "PROP P (of_int (int_of n))" .
  then show "PROP P n" by simp
qed


lemma int_of_inject [simp]:
  "int_of k = int_of l \<longleftrightarrow> k = l"
  by (rule int_of_inject)

lemma of_int_inject [simp]:
  "of_int n = of_int m \<longleftrightarrow> n = m"
  by (rule of_int_inject) (rule UNIV_I)+

instantiation code_int :: equal
begin

definition
  "HOL.equal k l \<longleftrightarrow> HOL.equal (int_of k) (int_of l)"

instance proof
qed (auto simp add: equal_code_int_def equal_int_def eq_int_refl)

end

instantiation code_int :: number
begin

definition
  "number_of = of_int"

instance ..

end

lemma int_of_number [simp]:
  "int_of (number_of k) = number_of k"
  by (simp add: number_of_code_int_def number_of_is_id)


definition nat_of :: "code_int => nat"
where
  "nat_of i = nat (int_of i)"

instantiation code_int :: "{minus, linordered_semidom, semiring_div, linorder}"
begin

definition [simp, code del]:
  "0 = of_int 0"

definition [simp, code del]:
  "1 = of_int 1"

definition [simp, code del]:
  "n + m = of_int (int_of n + int_of m)"

definition [simp, code del]:
  "n - m = of_int (int_of n - int_of m)"

definition [simp, code del]:
  "n * m = of_int (int_of n * int_of m)"

definition [simp, code del]:
  "n div m = of_int (int_of n div int_of m)"

definition [simp, code del]:
  "n mod m = of_int (int_of n mod int_of m)"

definition [simp, code del]:
  "n \<le> m \<longleftrightarrow> int_of n \<le> int_of m"

definition [simp, code del]:
  "n < m \<longleftrightarrow> int_of n < int_of m"


instance proof
qed (auto simp add: code_int left_distrib zmult_zless_mono2)

end
(*
lemma zero_code_int_code [code, code_unfold]:
  "(0\<Colon>code_int) = Numeral0"
  by (simp add: number_of_code_numeral_def Pls_def)
lemma [code_post]: "Numeral0 = (0\<Colon>code_numeral)"
  using zero_code_numeral_code ..

lemma one_code_numeral_code [code, code_unfold]:
  "(1\<Colon>code_int) = Numeral1"
  by (simp add: number_of_code_numeral_def Pls_def Bit1_def)
lemma [code_post]: "Numeral1 = (1\<Colon>code_int)"
  using one_code_numeral_code ..
*)

definition div_mod_code_int :: "code_int \<Rightarrow> code_int \<Rightarrow> code_int \<times> code_int" where
  [code del]: "div_mod_code_int n m = (n div m, n mod m)"

lemma [code]:
  "div_mod_code_int n m = (if m = 0 then (0, n) else (n div m, n mod m))"
  unfolding div_mod_code_int_def by auto

lemma [code]:
  "n div m = fst (div_mod_code_int n m)"
  unfolding div_mod_code_int_def by simp

lemma [code]:
  "n mod m = snd (div_mod_code_int n m)"
  unfolding div_mod_code_int_def by simp

lemma int_of_code [code]:
  "int_of k = (if k = 0 then 0
    else (if k mod 2 = 0 then 2 * int_of (k div 2) else 2 * int_of (k div 2) + 1))"
proof -
  have 1: "(int_of k div 2) * 2 + int_of k mod 2 = int_of k" 
    by (rule mod_div_equality)
  have "int_of k mod 2 = 0 \<or> int_of k mod 2 = 1" by auto
  from this show ?thesis
    apply auto
    apply (insert 1) by (auto simp add: mult_ac)
qed


code_instance code_numeral :: equal
  (Haskell -)

setup {* fold (Numeral.add_code @{const_name number_code_int_inst.number_of_code_int}
  false Code_Printer.literal_numeral) ["Haskell"]  *}

code_const "0 \<Colon> code_int"
  (Haskell "0")

code_const "1 \<Colon> code_int"
  (Haskell "1")

code_const "minus \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> code_int"
  (Haskell "(_/ -/ _)")

code_const div_mod_code_int
  (Haskell "divMod")

code_const "HOL.equal \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> bool"
  (Haskell infix 4 "==")

code_const "op \<le> \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> bool"
  (Haskell infix 4 "<=")

code_const "op < \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> bool"
  (Haskell infix 4 "<")

code_type code_int
  (Haskell "Int")

code_abort of_int

subsubsection {* Narrowing's deep representation of types and terms *}

datatype type = SumOfProd "type list list"

datatype "term" = Var "code_int list" type | Ctr code_int "term list"

datatype 'a cons = C type "(term list => 'a) list"

subsubsection {* Auxilary functions for Narrowing *}

consts nth :: "'a list => code_int => 'a"

code_const nth ("Haskell" infixl 9  "!!")

consts error :: "char list => 'a"

code_const error ("Haskell" "error")

consts toEnum :: "code_int => char"

code_const toEnum ("Haskell" "toEnum")

consts map_index :: "(code_int * 'a => 'b) => 'a list => 'b list"  

consts split_At :: "code_int => 'a list => 'a list * 'a list"
 
subsubsection {* Narrowing's basic operations *}

type_synonym 'a narrowing = "code_int => 'a cons"

definition empty :: "'a narrowing"
where
  "empty d = C (SumOfProd []) []"
  
definition cons :: "'a => 'a narrowing"
where
  "cons a d = (C (SumOfProd [[]]) [(%_. a)])"

fun conv :: "(term list => 'a) list => term => 'a"
where
  "conv cs (Var p _) = error (Char Nibble0 Nibble0 # map toEnum p)"
| "conv cs (Ctr i xs) = (nth cs i) xs"

fun nonEmpty :: "type => bool"
where
  "nonEmpty (SumOfProd ps) = (\<not> (List.null ps))"

definition "apply" :: "('a => 'b) narrowing => 'a narrowing => 'b narrowing"
where
  "apply f a d =
     (case f d of C (SumOfProd ps) cfs =>
       case a (d - 1) of C ta cas =>
       let
         shallow = (d > 0 \<and> nonEmpty ta);
         cs = [(%xs'. (case xs' of [] => undefined | x # xs => cf xs (conv cas x))). shallow, cf <- cfs]
       in C (SumOfProd [ta # p. shallow, p <- ps]) cs)"

definition sum :: "'a narrowing => 'a narrowing => 'a narrowing"
where
  "sum a b d =
    (case a d of C (SumOfProd ssa) ca => 
      case b d of C (SumOfProd ssb) cb =>
      C (SumOfProd (ssa @ ssb)) (ca @ cb))"

lemma [fundef_cong]:
  assumes "a d = a' d" "b d = b' d" "d = d'"
  shows "sum a b d = sum a' b' d'"
using assms unfolding sum_def by (auto split: cons.split type.split)

lemma [fundef_cong]:
  assumes "f d = f' d" "(\<And>d'. 0 <= d' & d' < d ==> a d' = a' d')"
  assumes "d = d'"
  shows "apply f a d = apply f' a' d'"
proof -
  note assms moreover
  have "int_of (of_int 0) < int_of d' ==> int_of (of_int 0) <= int_of (of_int (int_of d' - int_of (of_int 1)))"
    by (simp add: of_int_inverse)
  moreover
  have "int_of (of_int (int_of d' - int_of (of_int 1))) < int_of d'"
    by (simp add: of_int_inverse)
  ultimately show ?thesis
    unfolding apply_def by (auto split: cons.split type.split simp add: Let_def)
qed

type_synonym pos = "code_int list"
(*
subsubsection {* Term refinement *}

definition new :: "pos => type list list => term list"
where
  "new p ps = map_index (%(c, ts). Ctr c (map_index (%(i, t). Var (p @ [i]) t) ts)) ps"

fun refine :: "term => pos => term list" and refineList :: "term list => pos => (term list) list"
where
  "refine (Var p (SumOfProd ss)) [] = new p ss"
| "refine (Ctr c xs) p = map (Ctr c) (refineList xs p)"
| "refineList xs (i # is) = (let (ls, xrs) = split_At i xs in (case xrs of x#rs => [ls @ y # rs. y <- refine x is]))"

text {* Find total instantiations of a partial value *}

function total :: "term => term list"
where
  "total (Ctr c xs) = [Ctr c ys. ys <- map total xs]"
| "total (Var p (SumOfProd ss)) = [y. x <- new p ss, y <- total x]"
by pat_completeness auto

termination sorry
*)
subsubsection {* Narrowing generator type class *}

class narrowing =
  fixes narrowing :: "code_int => 'a cons"

definition cons1 :: "('a::narrowing => 'b) => 'b narrowing"
where
  "cons1 f = apply (cons f) narrowing"

definition cons2 :: "('a :: narrowing => 'b :: narrowing => 'c) => 'c narrowing"
where
  "cons2 f = apply (apply (cons f) narrowing) narrowing"

definition drawn_from :: "'a list => 'a cons"
where "drawn_from xs = C (SumOfProd (map (%_. []) xs)) (map (%x y. x) xs)"

instantiation int :: narrowing
begin

definition
  "narrowing_int d = (let i = Quickcheck_Narrowing.int_of d in drawn_from [-i .. i])"

instance ..

end

instantiation unit :: narrowing
begin

definition
  "narrowing = cons ()"

instance ..

end

instantiation bool :: narrowing
begin

definition
  "narrowing = sum (cons True) (cons False)" 

instance ..

end

instantiation option :: (narrowing) narrowing
begin

definition
  "narrowing = sum (cons None) (cons1 Some)"

instance ..

end

instantiation sum :: (narrowing, narrowing) narrowing
begin

definition
  "narrowing = sum (cons1 Inl) (cons1 Inr)"

instance ..

end

instantiation list :: (narrowing) narrowing
begin

function narrowing_list :: "'a list narrowing"
where
  "narrowing_list d = sum (cons []) (apply (apply (cons Cons) narrowing) narrowing_list) d"
by pat_completeness auto

termination proof (relation "measure nat_of")
qed (auto simp add: of_int_inverse nat_of_def)
    
instance ..

end

instantiation nat :: narrowing
begin

function narrowing_nat :: "nat narrowing"
where
  "narrowing_nat d = sum (cons 0) (apply (cons Suc) narrowing_nat) d"
by pat_completeness auto

termination proof (relation "measure nat_of")
qed (auto simp add: of_int_inverse nat_of_def)

instance ..

end

instantiation Enum.finite_1 :: narrowing
begin

definition narrowing_finite_1 :: "Enum.finite_1 narrowing"
where
  "narrowing_finite_1 = cons (Enum.finite_1.a\<^isub>1 :: Enum.finite_1)"

instance ..

end

instantiation Enum.finite_2 :: narrowing
begin

definition narrowing_finite_2 :: "Enum.finite_2 narrowing"
where
  "narrowing_finite_2 = sum (cons (Enum.finite_2.a\<^isub>1 :: Enum.finite_2)) (cons (Enum.finite_2.a\<^isub>2 :: Enum.finite_2))"

instance ..

end

instantiation Enum.finite_3 :: narrowing
begin

definition narrowing_finite_3 :: "Enum.finite_3 narrowing"
where
  "narrowing_finite_3 = sum (cons (Enum.finite_3.a\<^isub>1 :: Enum.finite_3)) (sum (cons (Enum.finite_3.a\<^isub>2 :: Enum.finite_3)) (cons (Enum.finite_3.a\<^isub>3 :: Enum.finite_3)))"

instance ..

end

instantiation Enum.finite_4 :: narrowing
begin

definition narrowing_finite_4 :: "Enum.finite_4 narrowing"
where
  "narrowing_finite_4 = sum (cons Enum.finite_4.a\<^isub>1) (sum (cons Enum.finite_4.a\<^isub>2) (sum (cons Enum.finite_4.a\<^isub>3) (cons Enum.finite_4.a\<^isub>4)))"

instance ..

end

subsubsection {* class @{text is_testable} *}

text {* The class @{text is_testable} ensures that all necessary type instances are generated. *}

class is_testable

instance bool :: is_testable ..

instance "fun" :: ("{term_of, narrowing}", is_testable) is_testable ..

definition ensure_testable :: "'a :: is_testable => 'a :: is_testable"
where
  "ensure_testable f = f"

declare simp_thms(17,19)[code del]

subsubsection {* Defining a simple datatype to represent functions in an incomplete and redundant way *}

datatype ('a, 'b) ffun = Constant 'b | Update 'a 'b "('a, 'b) ffun"

primrec eval_ffun :: "('a, 'b) ffun => 'a => 'b"
where
  "eval_ffun (Constant c) x = c"
| "eval_ffun (Update x' y f) x = (if x = x' then y else eval_ffun f x)"

hide_type (open) ffun
hide_const (open) Constant Update eval_ffun

datatype 'b cfun = Constant 'b

primrec eval_cfun :: "'b cfun => 'a => 'b"
where
  "eval_cfun (Constant c) y = c"

hide_type (open) cfun
hide_const (open) Constant eval_cfun

subsubsection {* Setting up the counterexample generator *}
  
use "~~/src/HOL/Tools/Quickcheck/narrowing_generators.ML"

setup {* Narrowing_Generators.setup *}

hide_type (open) code_int type "term" cons
hide_const (open) int_of of_int nth error toEnum map_index split_At empty
  cons conv nonEmpty "apply" sum cons1 cons2 ensure_testable

end