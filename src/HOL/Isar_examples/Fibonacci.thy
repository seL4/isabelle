(*  Title:      HOL/Isar_examples/Fibonacci.thy
    ID:         $Id$
    Author:     Gertrud Bauer
    Copyright   1999 Technische Universitaet Muenchen

The Fibonacci function.  Demonstrates the use of recdef.  Original
tactic script by Lawrence C Paulson.

Fibonacci numbers: proofs of laws taken from

  R. L. Graham, D. E. Knuth, O. Patashnik.
  Concrete Mathematics.
  (Addison-Wesley, 1989)
*)

header {* Fib and Gcd commute *};

theory Fibonacci = Primes:;

text_raw {*
 \footnote{Isar version by Gertrud Bauer.  Original tactic script by
 Larry Paulson.  A few proofs of laws taken from
 \cite{Concrete-Math}.}
*};


subsection {* Fibonacci numbers *};

consts fib :: "nat => nat";
recdef fib less_than
 "fib 0 = 0"
 "fib 1 = 1"
 "fib (Suc (Suc x)) = (fib x + fib (Suc x))";

lemmas [simp] = fib.rules;

lemma [simp]: "0 < fib (Suc n)";
  by (induct n rule: fib.induct) (simp+);


text {* Alternative induction rule. *};

theorem fib_induct:
"[| P 0; P 1; !!n. [| P (n + 1); P n |] ==> P (n + 2) |] ==> P n";
  by (induct rule: fib.induct, simp+);



subsection {* Fib and gcd commute *};

text {* A few laws taken from \cite{Concrete-Math}. *};

lemma fib_add: 
  "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"
  (is "?P n");
proof (induct ?P n rule: fib_induct) -- {* see \cite[page 280]{Concrete-Math} *};
  show "?P 0"; by simp;
  show "?P 1"; by simp;
  fix n;
  have "fib (n + 2 + k + 1)
    = fib (n + k + 1) + fib (n + 1 + k + 1)"; by simp;
  also; assume "fib (n + k + 1)
    = fib (k + 1) * fib (n + 1) + fib k * fib n"
      (is " _ = ?R1");
  also; assume "fib (n + 1 + k + 1)
    = fib (k + 1) * fib (n + 1 + 1) + fib k * fib (n + 1)"
      (is " _ = ?R2");
  also; have "?R1 + ?R2
    = fib (k + 1) * fib (n + 2 + 1) + fib k * fib (n + 2)";
    by (simp add: add_mult_distrib2);
  finally; show "?P (n + 2)"; .;
qed;

lemma gcd_fib_Suc_eq_1: "gcd (fib n, fib (n + 1)) = 1" (is "?P n");
proof (induct ?P n rule: fib_induct); 
  show "?P 0"; by simp;
  show "?P 1"; by simp;
  fix n; 
  have "fib (n + 2 + 1) = fib (n + 1) + fib (n + 2)"; 
    by simp;
  also; have "gcd (fib (n + 2), ...) = gcd (fib (n + 2), fib (n + 1))"; 
    by (simp add: gcd_add2);
  also; have "... = gcd (fib (n + 1), fib (n + 1 + 1))";
    by (simp add: gcd_commute);
  also; assume "... = 1";
  finally; show "?P (n + 2)"; .;
qed;

lemma gcd_mult_add: "0 < n ==> gcd (n * k + m, n) = gcd (m, n)";
proof -;
  assume "0 < n";
  hence "gcd (n * k + m, n) = gcd (n, m mod n)"; 
    by (simp add: gcd_non_0 add_commute);
  also; have "... = gcd (m, n)"; by (simp! add: gcd_non_0);
  finally; show ?thesis; .;
qed;

lemma gcd_fib_add: "gcd (fib m, fib (n + m)) = gcd (fib m, fib n)"; 
proof (rule nat.exhaust [of m]);
  assume "m = 0";
  thus "gcd (fib m, fib (n + m)) = gcd (fib m, fib n)"; by simp;
next;
  fix k; assume "m = Suc k"; 
  hence "gcd (fib m, fib (n + m)) = gcd (fib (n + k + 1), fib (k + 1))";
    by (simp add: gcd_commute);
  also; have "fib (n + k + 1) 
    = fib (k + 1) * fib (n + 1) + fib k * fib n";
    by (rule fib_add);
  also; have "gcd (..., fib (k + 1)) = gcd (fib k * fib n, fib (k + 1))"; 
    by (simp add: gcd_mult_add);
  also; have "... = gcd (fib n, fib (k + 1))"; 
    by (simp only: gcd_fib_Suc_eq_1 gcd_mult_cancel);
  also; have "... = gcd (fib m, fib n)"; 
    by (simp! add: gcd_commute);
  finally; show ?thesis; .;
qed;

lemma gcd_fib_diff: 
  "m <= n ==> gcd (fib m, fib (n - m)) = gcd (fib m, fib n)";
proof -; 
  assume "m <= n";
  have "gcd (fib m, fib (n - m)) = gcd (fib m, fib (n - m + m))"; 
    by (simp add: gcd_fib_add);
  also; have "n - m + m = n"; by (simp!); 
  finally; show ?thesis; .;
qed;

lemma if_cases: 
  "[| Q ==> P x; ~ Q ==> P y |] ==> P (if Q then x else y)"; by simp;

lemma gcd_fib_mod: 
  "0 < m ==> gcd (fib m, fib (n mod m)) = gcd (fib m, fib n)";
proof (induct n rule: less_induct);
  fix n; 
  assume m: "0 < m"
  and hyp: "ALL ma. ma < n 
           --> gcd (fib m, fib (ma mod m)) = gcd (fib m, fib ma)";
  have "n mod m = (if n < m then n else (n - m) mod m)";
    by (rule mod_if);
  also; have "gcd (fib m, fib ...) = gcd (fib m, fib n)";
  proof (rule if_cases);
    assume "~ n < m"; hence m_le_n: "m <= n"; by simp;
    have "n - m < n"; by (simp! add: diff_less);
    with hyp; have "gcd (fib m, fib ((n - m) mod m))
       = gcd (fib m, fib (n - m))"; by simp;
    also; from m_le_n; have "... = gcd (fib m, fib n)"; 
      by (rule gcd_fib_diff);
    finally; show "gcd (fib m, fib ((n - m) mod m)) = gcd (fib m, fib n)"; .;
  qed simp;
  finally; show "gcd (fib m, fib (n mod m)) = gcd (fib m, fib n)"; .;
qed;


theorem fib_gcd: "fib (gcd (m, n)) = gcd (fib m, fib n)" (is "?P m n");
proof (induct ?P m n rule: gcd_induct);
  fix m; show "fib (gcd (m, 0)) = gcd (fib m, fib 0)"; by simp;
  fix n; assume n: "0 < n";
  hence "gcd (m, n) = gcd (n, m mod n)"; by (rule gcd_non_0);
  also; assume hyp: "fib ... = gcd (fib n, fib (m mod n))";
  also; from n; have "... = gcd (fib n, fib m)"; by (rule gcd_fib_mod);
  also; have "... = gcd (fib m, fib n)"; by (rule gcd_commute);
  finally; show "fib (gcd (m, n)) = gcd (fib m, fib n)"; .;
qed;

end;
