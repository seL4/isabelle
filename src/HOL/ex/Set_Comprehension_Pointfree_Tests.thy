(*  Title:      HOL/ex/Set_Comprehension_Pointfree_Tests.thy
    Author:     Lukas Bulwahn, Rafal Kolanski
    Copyright   2012 TU Muenchen
*)

header {* Tests for the set comprehension to pointfree simproc *}

theory Set_Comprehension_Pointfree_Tests
imports Main
begin

lemma
  "finite {p. EX x. p = (x, x)}"
  apply simp
  oops

lemma
  "finite {f a b| a b. a : A \<and> b : B}"
  apply simp
  oops

lemma
  "finite {f a b| a b. a : A \<and> a : A' \<and> b : B}"
  apply simp
  oops

lemma
  "finite {f a b| a b. a : A \<and> b : B \<and> b : B'}"
  apply simp
  oops

lemma
  "finite {f a b c| a b c. a : A \<and> b : B \<and> c : C}"
  apply simp
  oops

lemma
  "finite {f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D}"
  apply simp
  oops

lemma
  "finite {f a b c d e | a b c d e. a : A \<and> b : B \<and> c : C \<and> d : D \<and> e : E}"
  apply simp
  oops

lemma (* check arbitrary ordering *)
  "finite {f a d c b e | e b c d a. b : B \<and> a : A \<and> e : E' \<and> c : C \<and> d : D \<and> e : E \<and> b : B'}"
  apply simp
  oops

lemma
  "\<lbrakk> finite A ; finite B ; finite C ; finite D \<rbrakk>
  \<Longrightarrow> finite ({f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D})"
  by simp

lemma
  "finite ((\<lambda>(a,b,c,d). f a b c d) ` (A \<times> B \<times> C \<times> D))
  \<Longrightarrow> finite ({f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D})"
  by simp

schematic_lemma (* check interaction with schematics *)
  "finite {x :: ?'A \<Rightarrow> ?'B \<Rightarrow> bool. \<exists>a b. x = Pair_Rep a b}
   = finite ((\<lambda>(a:: ?'A, b :: ?'B). Pair_Rep a b) ` (UNIV \<times> UNIV))"
  by simp

end
