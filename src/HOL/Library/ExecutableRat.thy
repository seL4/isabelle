(*  Title:      HOL/Library/ExecutableRat.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Executable implementation of rational numbers in HOL *}

theory ExecutableRat
imports "~~/src/HOL/Real/Rational" "~~/src/HOL/NumberTheory/IntPrimes"
begin

text {*
  Actually \emph{nothing} is proved about the implementation.
*}

subsection {* Representation and operations of executable rationals *}

datatype erat = Rat bool nat nat

axiomatization
  div_zero :: erat

fun
  common :: "(nat * nat) \<Rightarrow> (nat * nat) \<Rightarrow> (nat * nat) * nat" where
  "common (p1, q1) (p2, q2) = (
     let
       q' = q1 * q2 div gcd (q1, q2)
     in ((p1 * (q' div q1), p2 * (q' div q2)), q'))"

definition
  minus_sign :: "nat \<Rightarrow> nat \<Rightarrow> bool * nat" where
  "minus_sign n m = (if n < m then (False, m - n) else (True, n - m))"

fun
  add_sign :: "bool * nat \<Rightarrow> bool * nat \<Rightarrow> bool * nat" where
  "add_sign (True, n) (True, m) = (True, n + m)"
  "add_sign (False, n) (False, m) = (False, n + m)"
  "add_sign (True, n) (False, m) = minus_sign n m"
  "add_sign (False, n) (True, m) = minus_sign m n"

definition
  erat_of_quotient :: "int \<Rightarrow> int \<Rightarrow> erat" where
  "erat_of_quotient k1 k2 = (
    let
      l1 = nat (abs k1);
      l2 = nat (abs k2);
      m = gcd (l1, l2)
    in Rat (k1 \<le> 0 \<longleftrightarrow> k2 \<le> 0) (l1 div m) (l2 div m))"

instance erat :: zero
  zero_rat_def: "0 \<equiv> Rat True 0 1" ..

instance erat :: one
  one_rat_def: "1 \<equiv> Rat True 1 1" ..

instance erat :: plus
  add_rat_def: "r + s \<equiv> case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        let
          ((r1, r2), den) = common (p1, q1) (p2, q2);
          (sign, num) = add_sign (a1, r1) (a2, r2)
        in Rat sign num den" ..

instance erat :: minus
  uminus_rat_def: "- r \<equiv> case r of Rat a p q \<Rightarrow>
        if p = 0 then Rat True 0 1
        else Rat (\<not> a) p q" ..
  
instance erat :: times
  times_rat_def: "r * s \<equiv> case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        let
          p = p1 * p2;
          q = q1 * q2;
          m = gcd (p, q)
        in Rat (a1 = a2) (p div m) (q div m)" ..

instance erat :: inverse
  inverse_rat_def: "inverse r \<equiv> case r of Rat a p q \<Rightarrow>
        if p = 0 then div_zero
        else Rat a q p" ..

instance erat :: ord
  le_rat_def: "r1 \<le> r2 \<equiv> case r1 of Rat a1 p1 q1 \<Rightarrow> case r2 of Rat a2 p2 q2 \<Rightarrow>
        (\<not> a1 \<and> a2) \<or>
        (\<not> (a1 \<and> \<not> a2) \<and>
          (let
            ((r1, r2), dummy) = common (p1, q1) (p2, q2)
          in if a1 then r1 \<le> r2 else r2 \<le> r1))" ..


subsection {* Code generator setup *}

subsubsection {* code lemmas *}

lemma number_of_rat [code unfold]:
  "(number_of k \<Colon> rat) \<equiv> Fract k 1"
  unfolding Fract_of_int_eq rat_number_of_def by simp

lemma rat_minus [code func]:
  "(a\<Colon>rat) - b = a + (- b)" unfolding ab_group_add_class.diff_minus ..

lemma rat_divide [code func]:
  "(a\<Colon>rat) / b = a * inverse b" unfolding divide_inverse ..

instance rat :: eq ..

subsubsection {* names *}

code_modulename SML
  ExecutableRat Rational

code_modulename OCaml
  ExecutableRat Rational


subsubsection {* rat as abstype *}

lemma [code func]: -- {* prevents eq constraint *}
  shows "All = All"
    and "contents = contents" by rule+

code_const div_zero
  (SML "raise/ Fail/ \"Division by zero\"")
  (OCaml "failwith \"Division by zero\"")
  (Haskell "error/ \"Division by zero\"")

code_abstype rat erat where
  Fract \<equiv> erat_of_quotient
  "0 \<Colon> rat" \<equiv> "0 \<Colon> erat"
  "1 \<Colon> rat" \<equiv> "1 \<Colon> erat"
  "op + \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat" \<equiv> "op + \<Colon> erat \<Rightarrow> erat \<Rightarrow> erat"
  "uminus \<Colon> rat \<Rightarrow> rat" \<equiv> "uminus \<Colon> erat \<Rightarrow> erat"
  "op * \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat" \<equiv> "op * \<Colon> erat \<Rightarrow> erat \<Rightarrow> erat"
  "inverse \<Colon> rat \<Rightarrow> rat" \<equiv> "inverse \<Colon> erat \<Rightarrow> erat"
  "op \<le> \<Colon> rat \<Rightarrow> rat \<Rightarrow> bool" \<equiv>  "op \<le> \<Colon> erat \<Rightarrow> erat \<Rightarrow> bool"
  "op = \<Colon> rat \<Rightarrow> rat \<Rightarrow> bool" \<equiv> "op = \<Colon> erat \<Rightarrow> erat \<Rightarrow> bool"

types_code
  rat ("{*erat*}")

consts_code
  div_zero ("(raise/ (Fail/ \"Division by zero\"))")
  Fract ("({*erat_of_quotient*} (_) (_))")
  HOL.zero :: rat ("({*Rat True 0 1*})")
  HOL.one :: rat ("({*Rat True 1 1*})")
  HOL.plus :: "rat \<Rightarrow> rat \<Rightarrow> rat" ("({*op + \<Colon> erat \<Rightarrow> erat \<Rightarrow> erat*} (_) (_))")
  HOL.uminus :: "rat \<Rightarrow> rat" ("({*uminus \<Colon> erat \<Rightarrow> erat*} (_))")
  HOL.times :: "rat \<Rightarrow> rat \<Rightarrow> rat" ("({*op * \<Colon> erat \<Rightarrow> erat \<Rightarrow> erat*} (_) (_))")
  HOL.inverse :: "rat \<Rightarrow> rat" ("({*inverse \<Colon> erat \<Rightarrow> erat*} (_))")
  Orderings.less_eq :: "rat \<Rightarrow> rat \<Rightarrow> bool" ("({*op \<le> \<Colon> erat \<Rightarrow> erat \<Rightarrow> bool*} (_) (_))")
  "op =" :: "rat \<Rightarrow> rat \<Rightarrow> bool" ("({*op = \<Colon> erat \<Rightarrow> erat \<Rightarrow> bool*} (_) (_))")

end
