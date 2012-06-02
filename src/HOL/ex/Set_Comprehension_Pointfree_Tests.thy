(*  Title:      HOL/ex/Set_Comprehension_Pointfree_Tests.thy
    Author:     Lukas Bulwahn
    Copyright   2012 TU Muenchen
*)

header {* Tests for the set comprehension to pointfree simproc *}

theory Set_Comprehension_Pointfree_Tests
imports Main
uses "set_comprehension_pointfree.ML"
begin

simproc_setup finite_Collect ("finite (Collect P)") = {* Set_Comprehension_Pointfree.simproc *}

lemma
  "finite {f a b| a b. a : A \<and> b : B}"
apply simp (* works :) *)
oops

lemma
  "finite {f a b| a b. a : A \<and> a : A' \<and> b : B}"
(* apply simp -- does not terminate *)
oops

lemma
  "finite {f a b| a b. a : A \<and> b : B \<and> b : B'}"
(* apply simp -- does not terminate *)
oops

lemma
  "finite {f a b c| a b c. a : A \<and> b : B \<and> c : C}"
(* apply simp -- failed *) 
oops

lemma
  "finite {f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D}"
(* apply simp -- failed *)
oops

lemma
  "finite {f a b c d e | a b c d e. a : A \<and> b : B \<and> c : C \<and> d : D \<and> e : E}"
(* apply simp -- failed *)
oops

end
