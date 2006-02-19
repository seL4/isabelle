(*  Title:      HOL/Library/ASeries.thy
    ID:         $Id$
    Author:     Benjamin Porter, 2006
*)


header {* Arithmetic Series *}

theory ASeries
imports Main
begin

section {* Abstract *}

text {* The following document presents a proof of the Arithmetic
Series Sum formalised in Isabelle/Isar.

{\em Theorem:} The series $\sum_{i=1}^{n} a_i$ where $a_{i+1} = a_i +
d$ for some constant $d$ has the sum $\frac{n}{2} (a_1 + a_n)$
(i.e. $n$ multiplied by the arithmetic mean of the first and last
element).

{\em Informal Proof:} (from
"http://mathworld.wolfram.com/ArithmeticSeries.html")
  The proof is a simple forward proof. Let $S$ equal the sum above and
  $a$ the first element, then we have
\begin{tabular}{ll}
  $S$ &$= a + (a+d) + (a+2d) + ... a_n$ \\
    &$= n*a + d (0 + 1 + 2 + ... n-1)$ \\
    &$= n*a + d (\frac{1}{2} * (n-1) * n)$   ..using a simple sum identity \\
    &$= \frac{n}{2} (2a + d(n-1))$ \\
    & ..but $(a+a_n = a + (a + d(n-1)) = 2a + d(n-1))$ so \\
  $S$ &$= \frac{n}{2} (a + a_n)$
\end{tabular}
*}

section {* Formal Proof *}

text {* We present a proof for the abstract case of a commutative ring,
we then instantiate for three common types nats, ints and reals. The
function @{text "of_nat"} maps the natural numbers into any
commutative ring.
*}

lemmas comm_simp [simp] = left_distrib right_distrib add_assoc mult_ac

text {* Next we prove the following simple summation law $\sum_{i=1}^n
i = \frac {n * (n+1)}{2}$. *}

lemma sum_ident:
  "((1::'a::comm_semiring_1_cancel) + 1)*(\<Sum>i\<in>{1..n}. of_nat i) =
   of_nat n*((of_nat n)+1)"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

text {* The abstract theorem follows. Note that $2$ is displayed as
$1+1$ to keep the structure as abstract as possible. *}

theorem arith_series_general:
  "((1::'a::comm_semiring_1_cancel) + 1) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
  of_nat n * (a + (a + of_nat(n - 1)*d))"
proof cases
  assume ngt1: "n > 1"
  let ?I = "\<lambda>i. of_nat i" and ?n = "of_nat n"
  have
    "(\<Sum>i\<in>{..<n}. a+?I i*d) =
     ((\<Sum>i\<in>{..<n}. a) + (\<Sum>i\<in>{..<n}. ?I i*d))"
    by (rule setsum_addf)
  also from ngt1 have "\<dots> = ?n*a + (\<Sum>i\<in>{..<n}. ?I i*d)" by simp
  also from ngt1 have "\<dots> = (?n*a + d*(\<Sum>i\<in>{1..<n}. ?I i))"
    by (simp add: setsum_mult setsum_head_upt)
  also have "(1+1)*\<dots> = (1+1)*?n*a + d*(1+1)*(\<Sum>i\<in>{1..<n}. ?I i)"
    by simp
  also from ngt1 have "{1..<n} = {1..n - 1}"
    by (cases n) (auto simp: atLeastLessThanSuc_atLeastAtMost)    
  also from ngt1 
  have "(1+1)*?n*a + d*(1+1)*(\<Sum>i\<in>{1..n - 1}. ?I i) = ((1+1)*?n*a + d*?I (n - 1)*?I n)"
    by (simp only: mult_ac sum_ident [of "n - 1"]) (simp add: of_nat_Suc [symmetric])
  finally show ?thesis by simp
next
  assume "\<not>(n > 1)"
  hence "n = 1 \<or> n = 0" by auto
  thus ?thesis by auto
qed

subsection {* Instantiation *}

lemma arith_series_nat:
  "(2::nat) * (\<Sum>i\<in>{..<n}. a+i*d) = n * (a + (a+(n - 1)*d))"
proof -
  have
    "((1::nat) + 1) * (\<Sum>i\<in>{..<n::nat}. a + of_nat(i)*d) =
    of_nat(n) * (a + (a + of_nat(n - 1)*d))"
    by (rule arith_series_general)
  thus ?thesis by (auto simp add: of_nat_id)
qed

lemma arith_series_int:
  "(2::int) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
  of_nat n * (a + (a + of_nat(n - 1)*d))"
proof -
  have
    "((1::int) + 1) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
    of_nat(n) * (a + (a + of_nat(n - 1)*d))"
    by (rule arith_series_general)
  thus ?thesis by simp
qed

end
