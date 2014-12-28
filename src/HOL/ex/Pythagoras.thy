(*  Title:      HOL/ex/Pythagoras.thy
    Author:     Amine Chaieb
*)

header "The Pythagorean Theorem"

theory Pythagoras
imports Complex_Main
begin

text {* Expressed in real numbers: *}

lemma pythagoras_verbose:
  "((A1::real) - B1) * (C1 - B1) + (A2 - B2) * (C2 - B2) = 0 \<Longrightarrow> 
  (C1 - A1) * (C1 - A1) + (C2 - A2) * (C2 - A2) =
  ((B1 - A1) * (B1 - A1) + (B2 - A2) * (B2 - A2)) + (C1 - B1) * (C1 - B1) + (C2 - B2) * (C2 - B2)"
  by algebra


text {* Expressed in vectors: *}

type_synonym point = "real \<times> real"

lemma pythagoras: 
  defines ort:"orthogonal \<equiv> (\<lambda>(A::point) B. fst A * fst B + snd A * snd B = 0)"
       and vc:"vector \<equiv> (\<lambda>(A::point) B. (fst A  - fst B, snd A - snd B))"
      and vcn:"vecsqnorm \<equiv> (\<lambda>A::point. fst A ^ 2 + snd A ^2)"
 assumes o: "orthogonal (vector A B) (vector C B)"
 shows "vecsqnorm(vector C A) = vecsqnorm(vector B  A) + vecsqnorm(vector C B)"
   using o unfolding ort vc vcn by (algebra add: fst_conv snd_conv)
 
 end