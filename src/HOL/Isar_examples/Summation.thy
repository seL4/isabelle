(*  Title:      HOL/Isar_examples/Summation.thy
    ID:         $Id$
    Author:     Markus Wenzel

Summing natural numbers, squares and cubes (see HOL/ex/NatSum for the
original scripts).  Demonstrates mathematical induction together with
calculational proof.
*)

header {* Summing natural numbers *};

theory Summation = Main:;


subsection {* A summation operator *};

consts
  sum   :: "[nat => nat, nat] => nat";

primrec
  "sum f 0 = 0"
  "sum f (Suc n) = f n + sum f n";

syntax
  "_SUM" :: "idt => nat => nat => nat"
    ("SUM _ < _. _" [0, 0, 10] 10);
translations
  "SUM i < k. b" == "sum (%i. b) k";


subsection {* Summation laws *};

text_raw {* \begin{comment} *};

(* FIXME binary arithmetic does not yet work here *)

syntax
  "3" :: nat  ("3")
  "4" :: nat  ("4")
  "6" :: nat  ("6");

translations
  "3" == "Suc 2"
  "4" == "Suc 3"
  "6" == "Suc (Suc 4)";

theorems [simp] = add_mult_distrib add_mult_distrib2 mult_ac;

text_raw {* \end{comment} *};


theorem sum_of_naturals:
  "2 * (SUM i < n + 1. i) = n * (n + 1)"
  (is "?P n" is "?S n = _");
proof (induct n);
  show "?P 0"; by simp;

  fix n;
  have "?S (n + 1) = ?S n + 2 * (n + 1)"; by simp;
  also; assume "?S n = n * (n + 1)";
  also; have "... + 2 * (n + 1) = (n + 1) * (n + 2)"; by simp;
  finally; show "?P (Suc n)"; by simp;
qed;

theorem sum_of_odds:
  "(SUM i < n. 2 * i + 1) = n^2"
  (is "?P n" is "?S n = _");
proof (induct n);
  show "?P 0"; by simp;

  fix n;
  have "?S (n + 1) = ?S n + 2 * n + 1"; by simp;
  also; assume "?S n = n^2";
  also; have "... + 2 * n + 1 = (n + 1)^2"; by simp;
  finally; show "?P (Suc n)"; by simp;
qed;

theorem sum_of_squares:
  "6 * (SUM i < n + 1. i^2) = n * (n + 1) * (2 * n + 1)"
  (is "?P n" is "?S n = _");
proof (induct n);
  show "?P 0"; by simp;

  fix n;
  have "?S (n + 1) = ?S n + 6 * (n + 1)^2"; by simp;
  also; assume "?S n = n * (n + 1) * (2 * n + 1)";
  also; have "... + 6 * (n + 1)^2 =
    (n + 1) * (n + 2) * (2 * (n + 1) + 1)"; by simp;
  finally; show "?P (Suc n)"; by simp;
qed;

theorem sum_of_cubes:
  "4 * (SUM i < n + 1. i^3) = (n * (n + 1))^2"
  (is "?P n" is "?S n = _");
proof (induct n);
  show "?P 0"; by simp;

  fix n;
  have "?S (n + 1) = ?S n + 4 * (n + 1)^3"; by simp;
  also; assume "?S n = (n * (n + 1))^2";
  also; have "... + 4 * (n + 1)^3 = ((n + 1) * ((n + 1) + 1))^2";
    by simp;
  finally; show "?P (Suc n)"; by simp;
qed;

end;
