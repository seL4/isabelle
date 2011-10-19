(* Author: Florian Haftmann, TU Muenchen *)

header {* Small examples for evaluation mechanisms *}

theory Eval_Examples
imports Complex_Main
begin

text {* evaluation oracle *}

lemma "True \<or> False" by eval
lemma "Suc 0 \<noteq> Suc 1" by eval
lemma "[] = ([] :: int list)" by eval
lemma "[()] = [()]" by eval
lemma "fst ([] :: nat list, Suc 0) = []" by eval

text {* normalization *}

lemma "True \<or> False" by normalization
lemma "Suc 0 \<noteq> Suc 1" by normalization
lemma "[] = ([] :: int list)" by normalization
lemma "[()] = [()]" by normalization
lemma "fst ([] :: nat list, Suc 0) = []" by normalization

text {* term evaluation *}

value "(Suc 2 + 1) * 4"
value [code] "(Suc 2 + 1) * 4"
value [nbe] "(Suc 2 + 1) * 4"

value "(Suc 2 + Suc 0) * Suc 3"
value [code] "(Suc 2 + Suc 0) * Suc 3"
value [nbe] "(Suc 2 + Suc 0) * Suc 3"

value "nat 100"
value [code] "nat 100"
value [nbe] "nat 100"

value "(10::int) \<le> 12"
value [code] "(10::int) \<le> 12"
value [nbe] "(10::int) \<le> 12"

value "max (2::int) 4"
value [code] "max (2::int) 4"
value [nbe] "max (2::int) 4"

value "of_int 2 / of_int 4 * (1::rat)"
value [code] "of_int 2 / of_int 4 * (1::rat)"
value [nbe] "of_int 2 / of_int 4 * (1::rat)"

value "[] :: nat list"
value [code] "[] :: nat list"
value [nbe] "[] :: nat list"

value "[(nat 100, ())]"
value [code] "[(nat 100, ())]"
value [nbe] "[(nat 100, ())]"

text {* a fancy datatype *}

datatype ('a, 'b) foo =
    Foo "'a\<Colon>order" 'b
  | Bla "('a, 'b) bar"
  | Dummy nat
and ('a, 'b) bar =
    Bar 'a 'b
  | Blubb "('a, 'b) foo"

value "Bla (Bar (4::nat) [Suc 0])"
value [code] "Bla (Bar (4::nat) [Suc 0])"
value [nbe] "Bla (Bar (4::nat) [Suc 0])"

end
