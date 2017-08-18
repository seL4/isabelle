(*  Title:      HOL/ex/ThreeDivides.thy
    Author:     Benjamin Porter, 2005
*)

section \<open>Three Divides Theorem\<close>

theory ThreeDivides
imports Main "HOL-Library.LaTeXsugar"
begin

subsection \<open>Abstract\<close>

text \<open>
The following document presents a proof of the Three Divides N theorem
formalised in the Isabelle/Isar theorem proving system.

{\em Theorem}: $3$ divides $n$ if and only if $3$ divides the sum of all
digits in $n$.

{\em Informal Proof}:
Take $n = \sum{n_j * 10^j}$ where $n_j$ is the $j$'th least
significant digit of the decimal denotation of the number n and the
sum ranges over all digits. Then $$ (n - \sum{n_j}) = \sum{n_j * (10^j
- 1)} $$ We know $\forall j\; 3|(10^j - 1) $ and hence $3|LHS$,
therefore $$\forall n\; 3|n \Longleftrightarrow 3|\sum{n_j}$$
\<open>\<box>\<close>
\<close>


subsection \<open>Formal proof\<close>

subsubsection \<open>Miscellaneous summation lemmas\<close>

text \<open>If $a$ divides \<open>A x\<close> for all x then $a$ divides any
sum over terms of the form \<open>(A x)*(P x)\<close> for arbitrary $P$.\<close>

lemma div_sum:
  fixes a::nat and n::nat
  shows "\<forall>x. a dvd A x \<Longrightarrow> a dvd (\<Sum>x<n. A x * D x)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  from Suc
  have "a dvd (A n * D n)" by (simp add: dvd_mult2)
  with Suc
  have "a dvd ((\<Sum>x<n. A x * D x) + (A n * D n))" by (simp add: dvd_add)
  thus ?case by simp
qed


subsubsection \<open>Generalised Three Divides\<close>

text \<open>This section solves a generalised form of the three divides
problem. Here we show that for any sequence of numbers the theorem
holds. In the next section we specialise this theorem to apply
directly to the decimal expansion of the natural numbers.\<close>

text \<open>Here we show that the first statement in the informal proof is
true for all natural numbers. Note we are using @{term "D i"} to
denote the $i$'th element in a sequence of numbers.\<close>

lemma digit_diff_split:
  fixes n::nat and nd::nat and x::nat
  shows "n = (\<Sum>x\<in>{..<nd}. (D x)*((10::nat)^x)) \<Longrightarrow>
             (n - (\<Sum>x<nd. (D x))) = (\<Sum>x<nd. (D x)*(10^x - 1))"
by (simp add: sum_diff_distrib diff_mult_distrib2)

text \<open>Now we prove that 3 always divides numbers of the form $10^x - 1$.\<close>
lemma three_divs_0:
  shows "(3::nat) dvd (10^x - 1)"
proof (induct x)
  case 0 show ?case by simp
next
  case (Suc n)
  let ?thr = "(3::nat)"
  have "?thr dvd 9" by simp
  moreover
  have "?thr dvd (10*(10^n - 1))" by (rule dvd_mult) (rule Suc)
  hence "?thr dvd (10^(n+1) - 10)" by (simp add: nat_distrib)
  ultimately
  have"?thr dvd ((10^(n+1) - 10) + 9)"
    by (simp only: ac_simps) (rule dvd_add)
  thus ?case by simp
qed

text \<open>Expanding on the previous lemma and lemma \<open>div_sum\<close>.\<close>
lemma three_divs_1:
  fixes D :: "nat \<Rightarrow> nat"
  shows "3 dvd (\<Sum>x<nd. D x * (10^x - 1))"
  by (subst mult.commute, rule div_sum) (simp add: three_divs_0 [simplified])

text \<open>Using lemmas \<open>digit_diff_split\<close> and 
\<open>three_divs_1\<close> we now prove the following lemma. 
\<close>
lemma three_divs_2:
  fixes nd::nat and D::"nat\<Rightarrow>nat"
  shows "3 dvd ((\<Sum>x<nd. (D x)*(10^x)) - (\<Sum>x<nd. (D x)))"
proof -
  from three_divs_1 have "3 dvd (\<Sum>x<nd. D x * (10 ^ x - 1))" .
  thus ?thesis by (simp only: digit_diff_split)
qed

text \<open>
We now present the final theorem of this section. For any
sequence of numbers (defined by a function @{term "D :: (nat\<Rightarrow>nat)"}),
we show that 3 divides the expansive sum $\sum{(D\;x)*10^x}$ over $x$
if and only if 3 divides the sum of the individual numbers
$\sum{D\;x}$. 
\<close>
lemma three_div_general:
  fixes D :: "nat \<Rightarrow> nat"
  shows "(3 dvd (\<Sum>x<nd. D x * 10^x)) = (3 dvd (\<Sum>x<nd. D x))"
proof
  have mono: "(\<Sum>x<nd. D x) \<le> (\<Sum>x<nd. D x * 10^x)"
    by (rule sum_mono) simp
  txt \<open>This lets us form the term
         @{term "(\<Sum>x<nd. D x * 10^x) - (\<Sum>x<nd. D x)"}\<close>

  {
    assume "3 dvd (\<Sum>x<nd. D x)"
    with three_divs_2 mono
    show "3 dvd (\<Sum>x<nd. D x * 10^x)" 
      by (blast intro: dvd_diffD)
  }
  {
    assume "3 dvd (\<Sum>x<nd. D x * 10^x)"
    with three_divs_2 mono
    show "3 dvd (\<Sum>x<nd. D x)"
      by (blast intro: dvd_diffD1)
  }
qed


subsubsection \<open>Three Divides Natural\<close>

text \<open>This section shows that for all natural numbers we can
generate a sequence of digits less than ten that represent the decimal
expansion of the number. We then use the lemma \<open>three_div_general\<close> to prove our final theorem.\<close>


text \<open>\medskip Definitions of length and digit sum.\<close>

text \<open>This section introduces some functions to calculate the
required properties of natural numbers. We then proceed to prove some
properties of these functions.

The function \<open>nlen\<close> returns the number of digits in a natural
number n.\<close>

fun nlen :: "nat \<Rightarrow> nat"
where
  "nlen 0 = 0"
| "nlen x = 1 + nlen (x div 10)"

text \<open>The function \<open>sumdig\<close> returns the sum of all digits in
some number n.\<close>

definition
  sumdig :: "nat \<Rightarrow> nat" where
  "sumdig n = (\<Sum>x < nlen n. n div 10^x mod 10)"

text \<open>Some properties of these functions follow.\<close>

lemma nlen_zero:
  "0 = nlen x \<Longrightarrow> x = 0"
  by (induct x rule: nlen.induct) auto

lemma nlen_suc:
  "Suc m = nlen n \<Longrightarrow> m = nlen (n div 10)"
  by (induct n rule: nlen.induct) simp_all


text \<open>The following lemma is the principle lemma required to prove
our theorem. It states that an expansion of some natural number $n$
into a sequence of its individual digits is always possible.\<close>

lemma exp_exists:
  "m = (\<Sum>x<nlen m. (m div (10::nat)^x mod 10) * 10^x)"
proof (induct "nlen m" arbitrary: m)
  case 0 thus ?case by (simp add: nlen_zero)
next
  case (Suc nd)
  obtain c where mexp: "m = 10*(m div 10) + c \<and> c < 10"
    and cdef: "c = m mod 10" by simp
  show "m = (\<Sum>x<nlen m. m div 10^x mod 10 * 10^x)"
  proof -
    from \<open>Suc nd = nlen m\<close>
    have "nd = nlen (m div 10)" by (rule nlen_suc)
    with Suc have
      "m div 10 = (\<Sum>x<nd. m div 10 div 10^x mod 10 * 10^x)" by simp
    with mexp have
      "m = 10*(\<Sum>x<nd. m div 10 div 10^x mod 10 * 10^x) + c" by simp
    also have
      "\<dots> = (\<Sum>x<nd. m div 10 div 10^x mod 10 * 10^(x+1)) + c"
      by (subst sum_distrib_left) (simp add: ac_simps)
    also have
      "\<dots> = (\<Sum>x<nd. m div 10^(Suc x) mod 10 * 10^(Suc x)) + c"
      by (simp add: div_mult2_eq[symmetric])
    also have
      "\<dots> = (\<Sum>x\<in>{Suc 0..<Suc nd}. m div 10^x  mod 10 * 10^x) + c"
      by (simp only: sum_shift_bounds_Suc_ivl)
         (simp add: atLeast0LessThan)
    also have
      "\<dots> = (\<Sum>x<Suc nd. m div 10^x mod 10 * 10^x)"
      by (simp add: atLeast0LessThan[symmetric] sum_head_upt_Suc cdef)
    also note \<open>Suc nd = nlen m\<close>
    finally
    show "m = (\<Sum>x<nlen m. m div 10^x mod 10 * 10^x)" .
  qed
qed


text \<open>\medskip Final theorem.\<close>

text \<open>We now combine the general theorem \<open>three_div_general\<close>
and existence result of \<open>exp_exists\<close> to prove our final
theorem.\<close>

theorem three_divides_nat:
  shows "(3 dvd n) = (3 dvd sumdig n)"
proof (unfold sumdig_def)
  have "n = (\<Sum>x<nlen n. (n div (10::nat)^x mod 10) * 10^x)"
    by (rule exp_exists)
  moreover
  have "3 dvd (\<Sum>x<nlen n. (n div (10::nat)^x mod 10) * 10^x) =
        (3 dvd (\<Sum>x<nlen n. n div 10^x mod 10))"
    by (rule three_div_general)
  ultimately 
  show "3 dvd n = (3 dvd (\<Sum>x<nlen n. n div 10^x mod 10))" by simp
qed

end
