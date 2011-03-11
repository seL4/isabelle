(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Counterexample generator based on LazySmallCheck *}

theory LSC
imports Main "~~/src/HOL/Library/Code_Char"
uses ("~~/src/HOL/Tools/LSC/lazysmallcheck.ML")
begin

subsection {* Counterexample generator *}

subsubsection {* LSC's deep representation of types of terms *}

datatype type = SumOfProd "type list list"

datatype "term" = Var "code_numeral list" type | Ctr code_numeral "term list"

datatype 'a cons = C type "(term list => 'a) list"

subsubsection {* auxilary functions for LSC *}

definition nth :: "'a list => code_numeral => 'a"
where
  "nth xs i = List.nth xs (Code_Numeral.nat_of i)"

lemma [code]:
  "nth (x # xs) i = (if i = 0 then x else nth xs (i - 1))"
unfolding nth_def by (cases i) simp

definition error :: "char list => 'a"
where
  "error = undefined"

code_const error ("Haskell" "error")

definition toEnum' :: "code_numeral => char"
where
  "toEnum' = undefined"

code_const toEnum' ("Haskell" "(toEnum . fromInteger)")

subsubsection {* LSC's basic operations *}

type_synonym 'a series = "code_numeral => 'a cons"

definition empty :: "'a series"
where
  "empty d = C (SumOfProd []) []"
  
definition cons :: "'a => 'a series"
where
  "cons a d = (C (SumOfProd [[]]) [(%_. a)])"

fun conv :: "(term list => 'a) list => term => 'a"
where
  "conv cs (Var p _) = error (Char Nibble0 Nibble0 # map toEnum' p)"
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


subsubsection {* LSC's type class for enumeration *}

class serial =
  fixes series :: "code_numeral => 'a cons"

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
  
use "Tools/LSC/lazysmallcheck.ML"

setup {* Lazysmallcheck.setup *}

end