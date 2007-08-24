(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Small examples for evaluation mechanisms *}

theory Eval_Examples
imports Eval
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

value (overloaded) "(Suc 2 + 1) * 4"
value (overloaded) "(Suc 2 + 1) * 4"
value (overloaded) "(Suc 2 + Suc 0) * Suc 3"
value (overloaded) "nat 100"
value (overloaded) "(10\<Colon>int) \<le> 12"
value (overloaded) "[]::nat list"
value (overloaded) "[(nat 100, ())]"

text {* a fancy datatype *}

datatype ('a, 'b) bair =
    Bair "'a\<Colon>order" 'b
  | Shift "('a, 'b) cair"
  | Dummy unit
and ('a, 'b) cair =
    Cair 'a 'b

value (overloaded) "Shift (Cair (4::nat) [Suc 0])"

end
