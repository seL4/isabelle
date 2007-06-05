(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Small examples for evaluation mechanisms *}

theory Eval_Examples
imports Eval
begin

text {* evaluation oracle *}

lemma "True \<or> False" by eval
lemma "\<not> (Suc 0 = Suc 1)" by eval

text {* term evaluation *}

value (overloaded) "(Suc 2 + 1) * 4"
value (overloaded) "(Suc 2 + 1) * 4"
value (overloaded) "(Suc 2 + Suc 0) * Suc 3"
value (overloaded) "[]::nat list"
value (overloaded) "fst ([]::nat list, Suc 0) = []"
value (overloaded) "nat 100"
value (overloaded) "[(nat 100, ())]"
value (overloaded) "int 10 \<le> 12"

text {* a fancy datatype *}

datatype ('a, 'b) bair =
    Bair "'a\<Colon>order" 'b
  | Shift "('a, 'b) cair"
  | Dummy unit
and ('a, 'b) cair =
    Cair 'a 'b

value (overloaded) "Shift (Cair (4::nat) [Suc 0])"

end
