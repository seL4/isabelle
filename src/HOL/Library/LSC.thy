(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Counterexample generator based on LazySmallCheck *}

theory LSC
imports Main "~~/src/HOL/Library/Code_Char"
uses ("~~/src/HOL/Tools/LSC/lazysmallcheck.ML")
begin

subsection {* Counterexample generator *}

subsubsection {* Code generation setup *}

code_type typerep
  ("Haskell" "Typerep")

code_const Typerep.Typerep
  ("Haskell" "Typerep")

code_reserved Haskell Typerep

subsubsection {* Type code_int for Haskell's Int type *}

typedef (open) code_int = "UNIV \<Colon> int set"
  morphisms int_of of_int by rule

lemma int_of_inject [simp]:
  "int_of k = int_of l \<longleftrightarrow> k = l"
  by (rule int_of_inject)


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

subsubsection {* LSC's deep representation of types of terms *}

datatype type = SumOfProd "type list list"

datatype "term" = Var "code_int list" type | Ctr code_int "term list"

datatype 'a cons = C type "(term list => 'a) list"

subsubsection {* auxilary functions for LSC *}

consts nth :: "'a list => code_int => 'a"

code_const nth ("Haskell" infixl 9  "!!")

consts error :: "char list => 'a"

code_const error ("Haskell" "error")

consts toEnum :: "code_int => char"

code_const toEnum ("Haskell" "toEnum")

consts map_index :: "(code_int * 'a => 'b) => 'a list => 'b list"  

consts split_At :: "code_int => 'a list => 'a list * 'a list"
 
subsubsection {* LSC's basic operations *}

type_synonym 'a series = "code_int => 'a cons"

definition empty :: "'a series"
where
  "empty d = C (SumOfProd []) []"
  
definition cons :: "'a => 'a series"
where
  "cons a d = (C (SumOfProd [[]]) [(%_. a)])"

fun conv :: "(term list => 'a) list => term => 'a"
where
  "conv cs (Var p _) = error (Char Nibble0 Nibble0 # map toEnum p)"
| "conv cs (Ctr i xs) = (nth cs i) xs"

fun nonEmpty :: "type => bool"
where
  "nonEmpty (SumOfProd ps) = (\<not> (List.null ps))"

definition "apply" :: "('a => 'b) series => 'a series => 'b series"
where
  "apply f a d =
     (case f d of C (SumOfProd ps) cfs =>
       case a (d - 1) of C ta cas =>
       let
         shallow = (d > 0 \<and> nonEmpty ta);
         cs = [(%xs'. (case xs' of [] => undefined | x # xs => cf xs (conv cas x))). shallow, cf <- cfs]
       in C (SumOfProd [ta # p. shallow, p <- ps]) cs)"

definition sum :: "'a series => 'a series => 'a series"
where
  "sum a b d =
    (case a d of C (SumOfProd ssa) ca => 
      case b d of C (SumOfProd ssb) cb =>
      C (SumOfProd (ssa @ ssb)) (ca @ cb))"

definition cons0 :: "'a => 'a series"
where
  "cons0 f = cons f"

type_synonym pos = "code_int list"

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

subsubsection {* LSC's type class for enumeration *}

class serial =
  fixes series :: "code_int => 'a cons"

definition cons1 :: "('a::serial => 'b) => 'b series"
where
  "cons1 f = apply (cons f) series"

definition cons2 :: "('a :: serial => 'b :: serial => 'c) => 'c series"
where
  "cons2 f = apply (apply (cons f) series) series"
  
instantiation unit :: serial
begin

definition
  "series = cons0 ()"

instance ..

end

instantiation bool :: serial
begin

definition
  "series = sum (cons0 True) (cons0 False)" 

instance ..

end

instantiation option :: (serial) serial
begin

definition
  "series = sum (cons0 None) (cons1 Some)"

instance ..

end

instantiation sum :: (serial, serial) serial
begin

definition
  "series = sum (cons1 Inl) (cons1 Inr)"

instance ..

end

instantiation list :: (serial) serial
begin

function series_list :: "'a list series"
where
  "series_list d = sum (cons []) (apply (apply (cons Cons) series) series_list) d"
by pat_completeness auto

termination sorry

instance ..

end

instantiation nat :: serial
begin

function series_nat :: "nat series"
where
  "series_nat d = sum (cons 0) (apply (cons Suc) series_nat) d"
by pat_completeness auto

termination sorry

instance ..

end

instantiation Enum.finite_1 :: serial
begin

definition series_finite_1 :: "Enum.finite_1 series"
where
  "series_finite_1 = cons (Enum.finite_1.a\<^isub>1 :: Enum.finite_1)"

instance ..

end

instantiation Enum.finite_2 :: serial
begin

definition series_finite_2 :: "Enum.finite_2 series"
where
  "series_finite_2 = sum (cons (Enum.finite_2.a\<^isub>1 :: Enum.finite_2)) (cons (Enum.finite_2.a\<^isub>2 :: Enum.finite_2))"

instance ..

end

instantiation Enum.finite_3 :: serial
begin

definition series_finite_3 :: "Enum.finite_3 series"
where
  "series_finite_3 = sum (cons (Enum.finite_3.a\<^isub>1 :: Enum.finite_3)) (sum (cons (Enum.finite_3.a\<^isub>2 :: Enum.finite_3)) (cons (Enum.finite_3.a\<^isub>3 :: Enum.finite_3)))"

instance ..

end

subsubsection {* class is_testable *}

text {* The class is_testable ensures that all necessary type instances are generated. *}

class is_testable

instance bool :: is_testable ..

instance "fun" :: ("{term_of, serial}", is_testable) is_testable ..

definition ensure_testable :: "'a :: is_testable => 'a :: is_testable"
where
  "ensure_testable f = f"

subsubsection {* Setting up the counterexample generator *}
  
use "~~/src/HOL/Tools/LSC/lazysmallcheck.ML"

setup {* Lazysmallcheck.setup *}

hide_const (open) empty

end