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

lemma int_of_inject [simp]:
  "int_of k = int_of l \<longleftrightarrow> k = l"
  by (rule int_of_inject)

definition nat_of :: "code_int => nat"
where
  "nat_of i = nat (int_of i)"

instantiation code_int :: "{zero, one, minus, linorder}"
begin

definition [simp, code del]:
  "0 = of_int 0"

definition [simp, code del]:
  "1 = of_int 1"

definition [simp, code del]:
  "n - m = of_int (int_of n - int_of m)"

definition [simp, code del]:
  "n \<le> m \<longleftrightarrow> int_of n \<le> int_of m"

definition [simp, code del]:
  "n < m \<longleftrightarrow> int_of n < int_of m"


instance proof qed (auto)

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

code_const "0 \<Colon> code_int"
  (Haskell "0")

code_const "1 \<Colon> code_int"
  (Haskell "1")

code_const "minus \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> code_int"
  (Haskell "(_/ -/ _)")

code_const "op \<le> \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> bool"
  (Haskell infix 4 "<=")

code_const "op < \<Colon> code_int \<Rightarrow> code_int \<Rightarrow> bool"
  (Haskell infix 4 "<")

code_type code_int
  (Haskell "Int")

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

subsubsection {* Setting up the counterexample generator *}
  
use "~~/src/HOL/Tools/Quickcheck/narrowing_generators.ML"

setup {* Narrowing_Generators.setup *}

hide_type (open) code_int type "term" cons
hide_const (open) int_of of_int nth error toEnum map_index split_At empty
  cons conv nonEmpty "apply" sum cons1 cons2 ensure_testable

end