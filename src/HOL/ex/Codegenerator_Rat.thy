(*  Title:      HOL/Library/ExecutableRat.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Simple example for executable rational numbers *}

theory Codegenerator_Rat
imports ExecutableRat EfficientNat
begin

definition
  foo :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "foo r s t = (t + s) / t"

definition
  bar :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> bool" where
  "bar r s t \<longleftrightarrow> (r - s) \<le> t \<or> (s - t) \<le> r"

definition
  "R1 = Fract 3 7"

definition
  "R2 = Fract (-7) 5"

definition
  "R3 = Fract 11 (-9)"

definition
  "foobar = (foo R1 1 R3, bar R2 0 R3, foo R1 R3 R2)"

code_gen foobar (SML #) (SML -)
ML {* ROOT.Codegenerator_Rat.foobar *}

code_module Foo
  contains foobar
ML {* Foo.foobar *}

end
