
header {* An old chestnut *}

theory Puzzle = Main:

text_raw {*
 \footnote{A question from ``Bundeswettbewerb Mathematik''.  Original
 pen-and-paper proof due to Herbert Ehler; Isabelle tactic script by
 Tobias Nipkow.}

 \medskip \textbf{Problem.}  Given some function $f\colon \Nat \to
 \Nat$ such that $f \ap (f \ap n) < f \ap (\idt{Suc} \ap n)$ for all
 $n$.  Demonstrate that $f$ is the identity.
*}

theorem "(!!n::nat. f (f n) < f (Suc n)) ==> f n = n"
proof (rule order_antisym)
  assume f_ax: "!!n. f (f n) < f (Suc n)"

  txt {*
    Note that the generalized form of $n \le f \ap n$ is required
    later for monotonicity as well.
  *}
  show ge: "!!n. n <= f n"
  proof -
    fix k show "!!n. k == f n ==> n <= k" (is "PROP ?P k")
    proof (induct k rule: less_induct)
      fix k assume hyp: "!!m. m < k ==> PROP ?P m"
      fix n assume k_def: "k == f n"
      show "n <= k"
      proof (cases n)
        assume "n = 0" thus ?thesis by simp
      next
        fix m assume Suc: "n = Suc m"
        from f_ax have "f (f m) < f (Suc m)" .
        with hyp k_def Suc have "f m <= f (f m)" by simp
        also from f_ax have "... < f (Suc m)" .
        finally have less: "f m < f (Suc m)" .
        with hyp k_def Suc have "m <= f m" by simp
        also note less
        finally have "m < f (Suc m)" .
        hence "n <= f n" by (simp only: Suc)
        thus ?thesis by (simp only: k_def)
      qed
    qed
  qed

  txt {*
    In order to show the other direction, we first establish
    monotonicity of $f$.
  *}
  {
    fix m n
    have "m <= n \<Longrightarrow> f m <= f n" (is "PROP ?P n")
    proof (induct n)
      assume "m <= 0" hence "m = 0" by simp
      thus "f m <= f 0" by simp
    next
      fix n assume hyp: "PROP ?P n"
      assume "m <= Suc n"
      thus "f m <= f (Suc n)"
      proof (rule le_SucE)
        assume "m <= n"
        with hyp have "f m <= f n" .
        also from ge f_ax have "... < f (Suc n)"
          by (rule le_less_trans)
        finally show ?thesis by simp
      next
        assume "m = Suc n"
        thus ?thesis by simp
      qed
    qed
  } note mono = this

  show "f n <= n"
  proof -
    have "~ n < f n"
    proof
      assume "n < f n"
      hence "Suc n <= f n" by simp
      hence "f (Suc n) <= f (f n)" by (rule mono)
      also have "... < f (Suc n)" by (rule f_ax)
      finally have "... < ..." . thus False ..
    qed
    thus ?thesis by simp
  qed
qed

end
