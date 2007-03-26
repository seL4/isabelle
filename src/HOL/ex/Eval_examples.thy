(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Small examples for evaluation mechanisms *}

theory Eval_examples
imports Eval
begin

text {* evaluation oracle *}

lemma "True \<or> False" by eval
lemma "\<not> (Suc 0 = Suc 1)" by eval

text {* term evaluation *}

ML {* Eval.term "(Suc 2 + 1) * 4" *}
ML {* Eval.term "(Suc 2 + Suc 0) * Suc 3" *}
ML {* Eval.term "[]::nat list" *}
ML {* Eval.term "fst ([]::nat list, Suc 0) = []" *}

text {* a fancy datatype *}

datatype ('a, 'b) bair =
    Bair "'a\<Colon>order" 'b
  | Shift "('a, 'b) cair"
  | Dummy unit
and ('a, 'b) cair =
    Cair 'a 'b

ML {* Eval.term "Shift (Cair (4::nat) [Suc 0])" *}

end