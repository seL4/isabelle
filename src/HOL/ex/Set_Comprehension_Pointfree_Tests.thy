(*  Title:      HOL/ex/Set_Comprehension_Pointfree_Tests.thy
    Author:     Lukas Bulwahn, Rafal Kolanski
    Copyright   2012 TU Muenchen
*)

header {* Tests for the set comprehension to pointfree simproc *}

theory Set_Comprehension_Pointfree_Tests
imports Main
begin

lemma
  "finite (UNIV::'a set) ==> finite {p. EX x::'a. p = (x, x)}"
  by simp

lemma
  "finite A ==> finite B ==> finite {f a b| a b. a : A \<and> b : B}"
  by simp
  
lemma
  "finite B ==> finite A' ==> finite {f a b| a b. a : A \<and> a : A' \<and> b : B}"
  by simp

lemma
  "finite A ==> finite B ==> finite {f a b| a b. a : A \<and> b : B \<and> b : B'}"
  by simp

lemma
  "finite A ==> finite B ==> finite C ==> finite {f a b c| a b c. a : A \<and> b : B \<and> c : C}"
  by simp

lemma
  "finite A ==> finite B ==> finite C ==> finite D ==>
     finite {f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D}"
  by simp

lemma
  "finite A ==> finite B ==> finite C ==> finite D ==> finite E ==>
    finite {f a b c d e | a b c d e. a : A \<and> b : B \<and> c : C \<and> d : D \<and> e : E}"
  by simp

lemma (* check arbitrary ordering *)
  "finite A ==> finite B ==> finite C ==> finite D ==> finite E \<Longrightarrow>
    finite {f a d c b e | e b c d a. b : B \<and> a : A \<and> e : E' \<and> c : C \<and> d : D \<and> e : E \<and> b : B'}"
  by simp

lemma
  "\<lbrakk> finite A ; finite B ; finite C ; finite D \<rbrakk>
  \<Longrightarrow> finite ({f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D})"
  by simp

lemma
  "finite ((\<lambda>(a,b,c,d). f a b c d) ` (A \<times> B \<times> C \<times> D))
  \<Longrightarrow> finite ({f a b c d| a b c d. a : A \<and> b : B \<and> c : C \<and> d : D})"
  by simp

lemma
  "finite S ==> finite {s'. EX s:S. s' = f a e s}"
  by simp

lemma
  "finite A ==> finite B ==> finite {f a b| a b. a : A \<and> b : B \<and> a \<notin> Z}"
  by simp

lemma
  "finite A ==> finite B ==> finite R ==> finite {f a b x y| a b x y. a : A \<and> b : B \<and> (x,y) \<in> R}"
by simp

lemma
  "finite A ==> finite B ==> finite R ==> finite {f a b x y| a b x y. a : A \<and> (x,y) \<in> R \<and> b : B}"
by simp

lemma
  "finite A ==> finite B ==> finite R ==> finite {f a (x, b) y| y b x a. a : A \<and> (x,y) \<in> R \<and> b : B}"
by simp

lemma
  "finite A ==> finite AA ==> finite B ==> finite {f a b| a b. (a : A \<or> a : AA) \<and> b : B \<and> a \<notin> Z}"
by simp

lemma
  "finite A1 ==> finite A2 ==> finite A3 ==> finite A4 ==> finite A5 ==> finite B ==>
     finite {f a b c | a b c. ((a : A1 \<and> a : A2) \<or> (a : A3 \<and> (a : A4 \<or> a : A5))) \<and> b : B \<and> a \<notin> Z}"
apply simp
oops

schematic_lemma (* check interaction with schematics *)
  "finite {x :: ?'A \<Rightarrow> ?'B \<Rightarrow> bool. \<exists>a b. x = Pair_Rep a b}
   = finite ((\<lambda>(b :: ?'B, a:: ?'A). Pair_Rep a b) ` (UNIV \<times> UNIV))"
  by simp

lemma
  assumes "finite S" shows "finite {(a,b,c,d). ([a, b], [c, d]) : S}"
proof -
  have eq: "{(a,b,c,d). ([a, b], [c, d]) : S} = ((%(a, b, c, d). ([a, b], [c, d])) -` S)"
   unfolding vimage_def by (auto split: prod.split)  (* to be proved with the simproc *)
  from `finite S` show ?thesis
    unfolding eq by (auto intro!: finite_vimageI simp add: inj_on_def)
    (* to be automated with further rules and automation *)
qed

end
