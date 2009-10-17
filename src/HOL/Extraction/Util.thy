(*  Title:      HOL/Extraction/Util.thy
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Auxiliary lemmas used in program extraction examples *}

theory Util
imports Main
begin

text {*
Decidability of equality on natural numbers.
*}

lemma nat_eq_dec: "\<And>n::nat. m = n \<or> m \<noteq> n"
  apply (induct m)
  apply (case_tac n)
  apply (case_tac [3] n)
  apply (simp only: nat.simps, iprover?)+
  done

text {*
Well-founded induction on natural numbers, derived using the standard
structural induction rule.
*}

lemma nat_wf_ind:
  assumes R: "\<And>x::nat. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P z"
proof (rule R)
  show "\<And>y. y < z \<Longrightarrow> P y"
  proof (induct z)
    case 0
    thus ?case by simp
  next
    case (Suc n y)
    from nat_eq_dec show ?case
    proof
      assume ny: "n = y"
      have "P n"
        by (rule R) (rule Suc)
      with ny show ?case by simp
    next
      assume "n \<noteq> y"
      with Suc have "y < n" by simp
      thus ?case by (rule Suc)
    qed
  qed
qed

text {*
Bounded search for a natural number satisfying a decidable predicate.
*}

lemma search:
  assumes dec: "\<And>x::nat. P x \<or> \<not> P x"
  shows "(\<exists>x<y. P x) \<or> \<not> (\<exists>x<y. P x)"
proof (induct y)
  case 0 show ?case by simp
next
  case (Suc z)
  thus ?case
  proof
    assume "\<exists>x<z. P x"
    then obtain x where le: "x < z" and P: "P x" by iprover
    from le have "x < Suc z" by simp
    with P show ?case by iprover
  next
    assume nex: "\<not> (\<exists>x<z. P x)"
    from dec show ?case
    proof
      assume P: "P z"
      have "z < Suc z" by simp
      with P show ?thesis by iprover
    next
      assume nP: "\<not> P z"
      have "\<not> (\<exists>x<Suc z. P x)"
      proof
        assume "\<exists>x<Suc z. P x"
        then obtain x where le: "x < Suc z" and P: "P x" by iprover
        have "x < z"
        proof (cases "x = z")
          case True
          with nP and P show ?thesis by simp
        next
          case False
          with le show ?thesis by simp
        qed
        with P have "\<exists>x<z. P x" by iprover
        with nex show False ..
      qed
      thus ?case by iprover
    qed
  qed
qed

end
