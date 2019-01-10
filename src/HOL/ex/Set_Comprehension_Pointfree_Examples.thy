(*  Title:      HOL/ex/Set_Comprehension_Pointfree_Examples.thy
    Author:     Lukas Bulwahn, Rafal Kolanski
    Copyright   2012 TU Muenchen
*)

section \<open>Examples for the set comprehension to pointfree simproc\<close>

theory Set_Comprehension_Pointfree_Examples
imports Main
begin

declare [[simproc add: finite_Collect]]

lemma
  "finite (UNIV::'a set) \<Longrightarrow> finite {p. \<exists>x::'a. p = (x, x)}"
  by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite {f a b| a b. a \<in> A \<and> b \<in> B}"
  by simp
  
lemma
  "finite B \<Longrightarrow> finite A' \<Longrightarrow> finite {f a b| a b. a \<in> A \<and> a \<in> A' \<and> b \<in> B}"
  by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite {f a b| a b. a \<in> A \<and> b \<in> B \<and> b \<in> B'}"
  by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite C \<Longrightarrow> finite {f a b c| a b c. a \<in> A \<and> b \<in> B \<and> c \<in> C}"
  by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite C \<Longrightarrow> finite D \<Longrightarrow>
     finite {f a b c d| a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
  by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite C \<Longrightarrow> finite D \<Longrightarrow> finite E \<Longrightarrow>
    finite {f a b c d e | a b c d e. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D \<and> e \<in> E}"
  by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite C \<Longrightarrow> finite D \<Longrightarrow> finite E \<Longrightarrow>
    finite {f a d c b e | e b c d a. b \<in> B \<and> a \<in> A \<and> e \<in> E' \<and> c \<in> C \<and> d \<in> D \<and> e \<in> E \<and> b \<in> B'}"
  by simp

lemma
  "\<lbrakk> finite A ; finite B ; finite C ; finite D \<rbrakk>
  \<Longrightarrow> finite ({f a b c d| a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D})"
  by simp

lemma
  "finite ((\<lambda>(a,b,c,d). f a b c d) ` (A \<times> B \<times> C \<times> D))
  \<Longrightarrow> finite ({f a b c d| a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D})"
  by simp

lemma
  "finite S \<Longrightarrow> finite {s'. \<exists>s\<in>S. s' = f a e s}"
  by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite {f a b| a b. a \<in> A \<and> b \<in> B \<and> a \<notin> Z}"
  by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite R \<Longrightarrow> finite {f a b x y| a b x y. a \<in> A \<and> b \<in> B \<and> (x,y) \<in> R}"
by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite R \<Longrightarrow> finite {f a b x y| a b x y. a \<in> A \<and> (x,y) \<in> R \<and> b \<in> B}"
by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite R \<Longrightarrow> finite {f a (x, b) y| y b x a. a \<in> A \<and> (x,y) \<in> R \<and> b \<in> B}"
by simp

lemma
  "finite A \<Longrightarrow> finite AA \<Longrightarrow> finite B \<Longrightarrow> finite {f a b| a b. (a \<in> A \<or> a \<in> AA) \<and> b \<in> B \<and> a \<notin> Z}"
by simp

lemma
  "finite A1 \<Longrightarrow> finite A2 \<Longrightarrow> finite A3 \<Longrightarrow> finite A4 \<Longrightarrow> finite A5 \<Longrightarrow> finite B \<Longrightarrow>
     finite {f a b c | a b c. ((a \<in> A1 \<and> a \<in> A2) \<or> (a \<in> A3 \<and> (a \<in> A4 \<or> a \<in> A5))) \<and> b \<in> B \<and> a \<notin> Z}"
apply simp
oops

lemma "finite B \<Longrightarrow> finite {c. \<exists>x. x \<in> B \<and> c = a * x}"
by simp

lemma
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite {f a * g b |a b. a \<in> A \<and> b \<in> B}"
by simp

lemma
  "finite S \<Longrightarrow> inj (\<lambda>(x, y). g x y) \<Longrightarrow> finite {f x y| x y. g x y \<in> S}"
  by (auto intro: finite_vimageI)

lemma
  "finite A \<Longrightarrow> finite S \<Longrightarrow> inj (\<lambda>(x, y). g x y) \<Longrightarrow> finite {f x y z | x y z. g x y \<in> S & z \<in> A}"
  by (auto intro: finite_vimageI)

lemma
  "finite S \<Longrightarrow> finite A \<Longrightarrow> inj (\<lambda>(x, y). g x y) \<Longrightarrow> inj (\<lambda>(x, y). h x y)
    \<Longrightarrow> finite {f a b c d | a b c d. g a c \<in> S \<and> h b d \<in> A}"
  by (auto intro: finite_vimageI)

lemma
  assumes "finite S" shows "finite {(a,b,c,d). ([a, b], [c, d]) \<in> S}"
using assms by (auto intro!: finite_vimageI simp add: inj_on_def)
  (* injectivity to be automated with further rules and automation *)

schematic_goal (* check interaction with schematics *)
  "finite {x :: ?'A \<Rightarrow> ?'B \<Rightarrow> bool. \<exists>a b. x = Pair_Rep a b}
   = finite ((\<lambda>(b :: ?'B, a:: ?'A). Pair_Rep a b) ` (UNIV \<times> UNIV))"
  by simp

declare [[simproc del: finite_Collect]]


section \<open>Testing simproc in code generation\<close>

definition union :: "nat set => nat set => nat set"
where
  "union A B = {x. x \<in> A \<or> x \<in> B}"

definition common_subsets :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set set"
where
  "common_subsets S1 S2 = {S. S \<subseteq> S1 \<and> S \<subseteq> S2}"

definition products :: "nat set => nat set => nat set"
where
  "products A B = {c. \<exists>a b. a \<in> A \<and> b \<in> B \<and> c = a * b}"

export_code union common_subsets products checking SML

end
