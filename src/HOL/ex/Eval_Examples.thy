(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Small examples for evaluation mechanisms\<close>

theory Eval_Examples
imports Complex_Main
begin

text \<open>evaluation oracle\<close>

lemma "True \<or> False" by eval
lemma "Suc 0 \<noteq> Suc 1" by eval
lemma "[] = ([] :: int list)" by eval
lemma "[()] = [()]" by eval
lemma "fst ([] :: nat list, Suc 0) = []" by eval

text \<open>normalization\<close>

lemma "True \<or> False" by normalization
lemma "Suc 0 \<noteq> Suc 1" by normalization
lemma "[] = ([] :: int list)" by normalization
lemma "[()] = [()]" by normalization
lemma "fst ([] :: nat list, Suc 0) = []" by normalization

text \<open>term evaluation\<close>

value "(Suc 2 + 1) * 4"

value "(Suc 2 + Suc 0) * Suc 3"

value "nat 100"

value "(10::int) \<le> 12"

value "max (2::int) 4"

value "of_int 2 / of_int 4 * (1::rat)"

value "[] :: nat list"

value "[(nat 100, ())]"

text \<open>a fancy datatype\<close>

datatype ('a, 'b) foo =
    Foo "'a::order" 'b
  | Bla "('a, 'b) bar"
  | Dummy nat
and ('a, 'b) bar =
    Bar 'a 'b
  | Blubb "('a, 'b) foo"

value "Bla (Bar (4::nat) [Suc 0])"

end
