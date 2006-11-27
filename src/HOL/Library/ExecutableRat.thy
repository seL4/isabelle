(*  Title:      HOL/Library/ExecutableRat.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Executable implementation of rational numbers in HOL *}

theory ExecutableRat
imports "~~/src/HOL/Real/Rational" "~~/src/HOL/NumberTheory/IntPrimes"
begin

text {*
  Actually nothing is proved about the implementation.
*}


section {* HOL definitions *}

datatype erat = Rat bool int int

instance erat :: zero ..
instance erat :: one ..
instance erat :: plus ..
instance erat :: minus ..
instance erat :: times ..
instance erat :: inverse ..
instance erat :: ord ..

definition
  norm :: "erat \<Rightarrow> erat" where
  "norm r = (case r of (Rat a p q) \<Rightarrow>
     if p = 0 then Rat True 0 1
     else
       let
         absp = abs p
       in let
         m = zgcd (absp, q)
       in Rat (a = (0 <= p)) (absp div m) (q div m))"

definition
  common :: "(int * int) * (int * int) \<Rightarrow> (int * int) * int" where
  "common r = (case r of ((p1, q1), (p2, q2)) \<Rightarrow>
       let q' = q1 * q2 div int (gcd (nat q1, nat q2))
       in ((p1 * (q' div q1), p2 * (q' div q2)), q'))"

definition
  of_quotient :: "int \<Rightarrow> int \<Rightarrow> erat" where
  "of_quotient a b = norm (Rat True a b)"

definition
  of_rat :: "rat \<Rightarrow> erat" where
  "of_rat r = split of_quotient (SOME s. s : Rep_Rat r)"

definition
  to_rat :: "erat \<Rightarrow> rat" where
  "to_rat r = (case r of (Rat a p q) \<Rightarrow>
       if a then Fract p q else Fract (uminus p) q)"

definition
  eq_erat :: "erat \<Rightarrow> erat \<Rightarrow> bool" where
  "eq_erat r s = (norm r = norm s)"

axiomatization
  div_zero :: erat

defs (overloaded)
  zero_rat_def: "0 == Rat True 0 1"
  one_rat_def: "1 == Rat True 1 1"
  add_rat_def: "r + s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        let
          ((r1, r2), den) = common ((p1, q1), (p2, q2))
        in let
          num = (if a1 then r1 else -r1) + (if a2 then r2 else -r2)
        in norm (Rat True num den)"
  uminus_rat_def: "- r == case r of Rat a p q \<Rightarrow>
        if p = 0 then Rat a p q
        else Rat (\<not> a) p q"
  times_rat_def: "r * s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        norm (Rat (a1 = a2) (p1 * p2) (q1 * q2))"
  inverse_rat_def: "inverse r == case r of Rat a p q \<Rightarrow>
        if p = 0 then div_zero
        else Rat a q p"
  le_rat_def: "r <= s == case r of Rat a1 p1 q1 \<Rightarrow> case s of Rat a2 p2 q2 \<Rightarrow>
        (\<not> a1 \<and> a2) \<or>
        (\<not> (a1 \<and> \<not> a2) \<and>
          (let
            ((r1, r2), dummy) = common ((p1, q1), (p2, q2))
          in if a1 then r1 <= r2 else r2 <= r1))"


section {* code lemmas *}

lemma number_of_rat [code unfold]:
  "(number_of k \<Colon> rat) \<equiv> Fract k 1"
  unfolding Fract_of_int_eq rat_number_of_def by simp

declare divide_inverse [where ?'a = rat, code func]

instance rat :: eq ..
instance erat :: eq ..


section {* code names *}

code_modulename SML
  ExecutableRat Rational


section {* rat as abstype *}

lemma [code func]: -- {* prevents eq constraint *}
  shows "All = All"
    and "contents = contents" by rule+

code_abstype rat erat where
  Fract \<equiv> of_quotient
  "0 \<Colon> rat" \<equiv> "0 \<Colon> erat"
  "1 \<Colon> rat" \<equiv> "1 \<Colon> erat"
  "op + \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat" \<equiv> "op + \<Colon> erat \<Rightarrow> erat \<Rightarrow> erat"
  "uminus \<Colon> rat \<Rightarrow> rat" \<equiv> "uminus \<Colon> erat \<Rightarrow> erat"
  "op * \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat" \<equiv> "op * \<Colon> erat \<Rightarrow> erat \<Rightarrow> erat"
  "inverse \<Colon> rat \<Rightarrow> rat" \<equiv> "inverse \<Colon> erat \<Rightarrow> erat"
  "op \<le> \<Colon> rat \<Rightarrow> rat \<Rightarrow> bool" \<equiv>  "op \<le> \<Colon> erat \<Rightarrow> erat \<Rightarrow> bool"
  "op = \<Colon> rat \<Rightarrow> rat \<Rightarrow> bool" \<equiv> eq_erat

code_const div_zero
  (SML "raise/ (Fail/ \"Division by zero\")")
  (Haskell "error/ \"Division by zero\"")

code_gen
  Fract
  "0 \<Colon> rat"
  "1 \<Colon> rat"
  "op + \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat"
  "uminus \<Colon> rat \<Rightarrow> rat"
  "op * \<Colon> rat \<Rightarrow> rat \<Rightarrow> rat"
  "inverse \<Colon> rat \<Rightarrow> rat"
  "op \<le> \<Colon> rat \<Rightarrow> rat \<Rightarrow> bool"
  "op = \<Colon> rat \<Rightarrow> rat \<Rightarrow> bool"
  (SML #)


section {* type serializations *}

types_code
  rat ("{*erat*}")


section {* const serializations *}

consts_code
  div_zero ("raise/ (Fail/ \"non-defined rational number\")")
  Fract ("{*of_quotient*}")
  HOL.zero :: rat ("{*0::erat*}")
  HOL.one :: rat ("{*1::erat*}")
  HOL.plus :: "rat \<Rightarrow> rat \<Rightarrow> rat" ("{*op + :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
  uminus :: "rat \<Rightarrow> rat" ("{*uminus :: erat \<Rightarrow> erat*}")
  HOL.times :: "rat \<Rightarrow> rat \<Rightarrow> rat" ("{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}")
  inverse :: "rat \<Rightarrow> rat" ("{*inverse :: erat \<Rightarrow> erat*}")
  divide :: "rat \<Rightarrow> rat \<Rightarrow> rat" ("{*op * :: erat \<Rightarrow> erat \<Rightarrow> erat*}/ _/ ({*inverse :: erat \<Rightarrow> erat*}/ _)")
  Orderings.less_eq :: "rat \<Rightarrow> rat \<Rightarrow> bool" ("{*op <= :: erat \<Rightarrow> erat \<Rightarrow> bool*}")
  "op =" :: "rat \<Rightarrow> rat \<Rightarrow> bool" ("{*eq_erat*}")

end
