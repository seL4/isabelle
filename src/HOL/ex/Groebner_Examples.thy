(*  Title:      HOL/ex/Groebner_Examples.thy
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Groebner Basis Examples *}

theory Groebner_Examples
imports Groebner_Basis
begin

subsection {* Basic examples *}

lemma
  fixes x :: int
  shows "x ^ 3 = x ^ 3" 
  apply (tactic {* ALLGOALS (CONVERSION
    (Conv.arg_conv (Conv.arg1_conv (Semiring_Normalizer.semiring_normalize_conv @{context})))) *})
  by (rule refl)

lemma
  fixes x :: int
  shows "(x - (-2))^5 = x ^ 5 + (10 * x ^ 4 + (40 * x ^ 3 + (80 * x\<twosuperior> + (80 * x + 32))))" 
  apply (tactic {* ALLGOALS (CONVERSION
    (Conv.arg_conv (Conv.arg1_conv (Semiring_Normalizer.semiring_normalize_conv @{context})))) *})
  by (rule refl)

schematic_lemma
  fixes x :: int
  shows "(x - (-2))^5  * (y - 78) ^ 8 = ?X" 
  apply (tactic {* ALLGOALS (CONVERSION
    (Conv.arg_conv (Conv.arg1_conv (Semiring_Normalizer.semiring_normalize_conv @{context})))) *})
  by (rule refl)

lemma "((-3) ^ (Suc (Suc (Suc 0)))) == (X::'a::{comm_ring_1})"
  apply (simp only: power_Suc power_0)
  apply (simp only: semiring_norm)
  oops

lemma "((x::int) + y)^3 - 1 = (x - z)^2 - 10 \<Longrightarrow> x = z + 3 \<Longrightarrow> x = - y"
  by algebra

lemma "(4::nat) + 4 = 3 + 5"
  by algebra

lemma "(4::int) + 0 = 4"
  apply algebra?
  by simp

lemma
  assumes "a * x^2 + b * x + c = (0::int)" and "d * x^2 + e * x + f = 0"
  shows "d^2*c^2 - 2*d*c*a*f + a^2*f^2 - e*d*b*c - e*b*a*f + a*e^2*c + f*d*b^2 = 0"
  using assms by algebra

lemma "(x::int)^3  - x^2  - 5*x - 3 = 0 \<longleftrightarrow> (x = 3 \<or> x = -1)"
  by algebra

theorem "x* (x\<twosuperior> - x  - 5) - 3 = (0::int) \<longleftrightarrow> (x = 3 \<or> x = -1)"
  by algebra

lemma
  fixes x::"'a::{idom}"
  shows "x^2*y = x^2 & x*y^2 = y^2 \<longleftrightarrow>  x=1 & y=1 | x=0 & y=0"
  by algebra

subsection {* Lemmas for Lagrange's theorem *}

definition
  sq :: "'a::times => 'a" where
  "sq x == x*x"

lemma
  fixes x1 :: "'a::{idom}"
  shows
  "(sq x1 + sq x2 + sq x3 + sq x4) * (sq y1 + sq y2 + sq y3 + sq y4) =
    sq (x1*y1 - x2*y2 - x3*y3 - x4*y4)  +
    sq (x1*y2 + x2*y1 + x3*y4 - x4*y3)  +
    sq (x1*y3 - x2*y4 + x3*y1 + x4*y2)  +
    sq (x1*y4 + x2*y3 - x3*y2 + x4*y1)"
  by (algebra add: sq_def)

lemma
  fixes p1 :: "'a::{idom}"
  shows
  "(sq p1 + sq q1 + sq r1 + sq s1 + sq t1 + sq u1 + sq v1 + sq w1) *
   (sq p2 + sq q2 + sq r2 + sq s2 + sq t2 + sq u2 + sq v2 + sq w2)
    = sq (p1*p2 - q1*q2 - r1*r2 - s1*s2 - t1*t2 - u1*u2 - v1*v2 - w1*w2) +
      sq (p1*q2 + q1*p2 + r1*s2 - s1*r2 + t1*u2 - u1*t2 - v1*w2 + w1*v2) +
      sq (p1*r2 - q1*s2 + r1*p2 + s1*q2 + t1*v2 + u1*w2 - v1*t2 - w1*u2) +
      sq (p1*s2 + q1*r2 - r1*q2 + s1*p2 + t1*w2 - u1*v2 + v1*u2 - w1*t2) +
      sq (p1*t2 - q1*u2 - r1*v2 - s1*w2 + t1*p2 + u1*q2 + v1*r2 + w1*s2) +
      sq (p1*u2 + q1*t2 - r1*w2 + s1*v2 - t1*q2 + u1*p2 - v1*s2 + w1*r2) +
      sq (p1*v2 + q1*w2 + r1*t2 - s1*u2 - t1*r2 + u1*s2 + v1*p2 - w1*q2) +
      sq (p1*w2 - q1*v2 + r1*u2 + s1*t2 - t1*s2 - u1*r2 + v1*q2 + w1*p2)"
  by (algebra add: sq_def)


subsection {* Colinearity is invariant by rotation *}

type_synonym point = "int \<times> int"

definition collinear ::"point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "collinear \<equiv> \<lambda>(Ax,Ay) (Bx,By) (Cx,Cy).
    ((Ax - Bx) * (By - Cy) = (Ay - By) * (Bx - Cx))"

lemma collinear_inv_rotation:
  assumes "collinear (Ax, Ay) (Bx, By) (Cx, Cy)" and "c\<twosuperior> + s\<twosuperior> = 1"
  shows "collinear (Ax * c - Ay * s, Ay * c + Ax * s)
    (Bx * c - By * s, By * c + Bx * s) (Cx * c - Cy * s, Cy * c + Cx * s)"
  using assms 
  by (algebra add: collinear_def split_def fst_conv snd_conv)

lemma "EX (d::int). a*y - a*x = n*d \<Longrightarrow> EX u v. a*u + n*v = 1 \<Longrightarrow> EX e. y - x = n*e"
  by algebra

end
