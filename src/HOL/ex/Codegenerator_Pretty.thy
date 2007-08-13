(*  Title:      HOL/ex/Codegenerator_Pretty.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Simple examples for pretty numerals and such *}

theory Codegenerator_Pretty
imports Executable_Rat Executable_Real Efficient_Nat
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

definition
  foo' :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "foo' r s t = (t + s) / t"

definition
  bar' :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "bar' r s t \<longleftrightarrow> (r - s) \<le> t \<or> (s - t) \<le> r"

definition
  "R1' = real_of_rat (Fract 3 7)"

definition
  "R2' = real_of_rat (Fract (-7) 5)"

definition
  "R3' = real_of_rat (Fract 11 (-9))"

definition
  "foobar' = (foo' R1' 1 R3', bar' R2' 0 R3', foo' R1' R3' R2')"

code_gen foobar foobar' in SML module_name Foo
  in OCaml file -
  in Haskell file -
ML {* (Foo.foobar, Foo.foobar') *}

end
