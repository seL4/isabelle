
header {* An old chestnut *}

theory Puzzle = Main:

text_raw {*
 \footnote{A question from ``Bundeswettbewerb Mathematik''.
 Original pen-and-paper proof due to Herbert Ehler; Isabelle tactic
 script by Tobias Nipkow.}
*}


subsection {* Generalized mathematical induction *}

text {*
 The following derived rule admits induction over some expression
 $f(x)$ wrt.\ the ${<}$ relation on natural numbers.
*}

lemma gen_less_induct:
  "(!!x. ALL y. f y < f x --> P y (f y) ==> P x (f x))
    ==> P x (f x :: nat)"
  (is "(!!x. ?H x ==> ?C x) ==> _")
proof -
  assume asm: "!!x. ?H x ==> ?C x"
  {
    fix k
    have "ALL x. k = f x --> ?C x" (is "?Q k")
    proof (rule nat_less_induct)
      fix k assume hyp: "ALL m<k. ?Q m"
      show "?Q k"
      proof
	fix x show "k = f x --> ?C x"
	proof
	  assume "k = f x"
	  with hyp have "?H x" by blast
	  thus "?C x" by (rule asm)
	qed
      qed
    qed
  }
  thus "?C x" by simp
qed


subsection {* The problem *}

text {*
 Given some function $f\colon \Nat \to \Nat$ such that $f \ap (f \ap
 n) < f \ap (\idt{Suc} \ap n)$ for all $n$.  Demonstrate that $f$ is
 the identity.
*}

consts f :: "nat => nat"
axioms f_ax: "f (f n) < f (Suc n)"

theorem "f n = n"
proof (rule order_antisym)
  txt {*
    Note that the generalized form of $n \le f \ap n$ is required
    later for monotonicity as well.
  *}
  show ge: "!!n. n <= f n"
  proof -
    fix n
    show "?thesis n" (is "?P n (f n)")
    proof (rule gen_less_induct [of f ?P])
      fix n assume hyp: "ALL m. f m < f n --> ?P m (f m)"
      show "?P n (f n)"
      proof (rule nat.exhaust)
	assume "n = 0" thus ?thesis by simp
      next
	fix m assume n_Suc: "n = Suc m"
	from f_ax have "f (f m) < f (Suc m)" .
	with hyp n_Suc have "f m <= f (f m)" by blast
	also from f_ax have "... < f (Suc m)" .
	finally have lt: "f m < f (Suc m)" .
	with hyp n_Suc have "m <= f m" by blast
	also note lt
	finally have "m < f (Suc m)" .
	thus "n <= f n" by (simp only: n_Suc)
      qed
    qed
  qed

  txt {*
    In order to show the other direction, we first establish
    monotonicity of $f$.
  *}
  have mono: "!!m n. m <= n --> f m <= f n"
  proof -
    fix m n
    show "?thesis m n" (is "?P n")
    proof (induct n)
      show "?P 0" by simp
      fix n assume hyp: "?P n"
      show "?P (Suc n)"
      proof
	assume "m <= Suc n"
	thus "f m <= f (Suc n)"
	proof (rule le_SucE)
	  assume "m <= n"
	  with hyp have "f m <= f n" ..
	  also from ge f_ax have "... < f (Suc n)"
	    by (rule le_less_trans)
	  finally show ?thesis by simp
	next
	  assume "m = Suc n"
	  thus ?thesis by simp
	qed
      qed
    qed
  qed

  show "f n <= n"
  proof (rule leI)
    show "~ n < f n"
    proof
      assume "n < f n"
      hence "Suc n <= f n" by (rule Suc_leI)
      hence "f (Suc n) <= f (f n)" by (rule mono [rule_format])
      also have "... < f (Suc n)" by (rule f_ax)
      finally have "... < ..." . thus False ..
    qed
  qed
qed

end
