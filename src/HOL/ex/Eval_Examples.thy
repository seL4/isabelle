(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Small examples for evaluation mechanisms *}

theory Eval_Examples
imports Eval "~~/src/HOL/Real/Rational"
begin

text {* SML evaluation oracle *}

lemma "True \<or> False" by evaluation
lemma "\<not> (Suc 0 = Suc 1)" by evaluation
lemma "[] = ([]\<Colon> int list)" by evaluation
lemma "[()] = [()]" by evaluation
lemma "fst ([]::nat list, Suc 0) = []" by evaluation

text {* evaluation oracle *}

lemma "True \<or> False" by eval
lemma "\<not> (Suc 0 = Suc 1)" by eval
lemma "[] = ([]\<Colon> int list)" by eval
lemma "[()] = [()]" by eval
lemma "fst ([]::nat list, Suc 0) = []" by eval

text {* term evaluation *}

value "(Suc 2 + 1) * 4"
value (code) "(Suc 2 + 1) * 4"
value (SML) "(Suc 2 + 1) * 4"
value ("normal_form") "(Suc 2 + 1) * 4"

value "(Suc 2 + Suc 0) * Suc 3"
value (code) "(Suc 2 + Suc 0) * Suc 3"
value (SML) "(Suc 2 + Suc 0) * Suc 3"
value ("normal_form") "(Suc 2 + Suc 0) * Suc 3"

value "nat 100"
value (code) "nat 100"
value (SML) "nat 100"
value ("normal_form") "nat 100"

value "(10\<Colon>int) \<le> 12"
value (code) "(10\<Colon>int) \<le> 12"
value (SML) "(10\<Colon>int) \<le> 12"
value ("normal_form") "(10\<Colon>int) \<le> 12"

value "max (2::int) 4"
value (code) "max (2::int) 4"
value (SML) "max (2::int) 4"
value ("normal_form") "max (2::int) 4"

value "of_int 2 / of_int 4 * (1::rat)"
(*value (code) "of_int 2 / of_int 4 * (1::rat)"*)
value (SML) "of_int 2 / of_int 4 * (1::rat)"
value ("normal_form") "of_int 2 / of_int 4 * (1::rat)"

value "[]::nat list"
value (code) "[]::nat list"
(*value (SML) "[]::nat list" FIXME*)
value ("normal_form") "[]::nat list"

value "[(nat 100, ())]"
value (code) "[(nat 100, ())]"
(*value (SML) "[(nat 100, ())]" FIXME*)
value ("normal_form") "[(nat 100, ())]"


text {* a fancy datatype *}

datatype ('a, 'b) bair =
    Bair "'a\<Colon>order" 'b
  | Shift "('a, 'b) cair"
  | Dummy unit
and ('a, 'b) cair =
    Cair 'a 'b

value "Shift (Cair (4::nat) [Suc 0])"
value (code) "Shift (Cair (4::nat) [Suc 0])"
value (SML) "Shift (Cair (4::nat) [Suc 0])"
value ("normal_form") "Shift (Cair (4::nat) [Suc 0])"

end
