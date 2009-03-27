(*  Title:      HOL/Library/While_Combinator.thy
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen
*)

header {* A general ``while'' combinator *}

theory While_Combinator
imports Main
begin

text {* 
  We define the while combinator as the "mother of all tail recursive functions".
*}

function (tailrec) while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  while_unfold[simp del]: "while b c s = (if b s then while b c (c s) else s)"
by auto

declare while_unfold[code]

lemma def_while_unfold:
  assumes fdef: "f == while test do"
  shows "f x = (if test x then f(do x) else x)"
proof -
  have "f x = while test do x" using fdef by simp
  also have "\<dots> = (if test x then while test do (do x) else x)"
    by(rule while_unfold)
  also have "\<dots> = (if test x then f(do x) else x)" by(simp add:fdef[symmetric])
  finally show ?thesis .
qed


text {*
 The proof rule for @{term while}, where @{term P} is the invariant.
*}

theorem while_rule_lemma:
  assumes invariant: "!!s. P s ==> b s ==> P (c s)"
    and terminate: "!!s. P s ==> \<not> b s ==> Q s"
    and wf: "wf {(t, s). P s \<and> b s \<and> t = c s}"
  shows "P s \<Longrightarrow> Q (while b c s)"
  using wf
  apply (induct s)
  apply simp
  apply (subst while_unfold)
  apply (simp add: invariant terminate)
  done

theorem while_rule:
  "[| P s;
      !!s. [| P s; b s  |] ==> P (c s);
      !!s. [| P s; \<not> b s  |] ==> Q s;
      wf r;
      !!s. [| P s; b s  |] ==> (c s, s) \<in> r |] ==>
   Q (while b c s)"
  apply (rule while_rule_lemma)
     prefer 4 apply assumption
    apply blast
   apply blast
  apply (erule wf_subset)
  apply blast
  done

text {*
 \medskip An application: computation of the @{term lfp} on finite
 sets via iteration.
*}

theorem lfp_conv_while:
  "[| mono f; finite U; f U = U |] ==>
    lfp f = fst (while (\<lambda>(A, fA). A \<noteq> fA) (\<lambda>(A, fA). (fA, f fA)) ({}, f {}))"
apply (rule_tac P = "\<lambda>(A, B). (A \<subseteq> U \<and> B = f A \<and> A \<subseteq> B \<and> B \<subseteq> lfp f)" and
                r = "((Pow U \<times> UNIV) \<times> (Pow U \<times> UNIV)) \<inter>
                     inv_image finite_psubset (op - U o fst)" in while_rule)
   apply (subst lfp_unfold)
    apply assumption
   apply (simp add: monoD)
  apply (subst lfp_unfold)
   apply assumption
  apply clarsimp
  apply (blast dest: monoD)
 apply (fastsimp intro!: lfp_lowerbound)
 apply (blast intro: wf_finite_psubset Int_lower2 [THEN [2] wf_subset])
apply (clarsimp simp add: finite_psubset_def order_less_le)
apply (blast intro!: finite_Diff dest: monoD)
done


text {*
 An example of using the @{term while} combinator.
*}

text{* Cannot use @{thm[source]set_eq_subset} because it leads to
looping because the antisymmetry simproc turns the subset relationship
back into equality. *}

theorem "P (lfp (\<lambda>N::int set. {0} \<union> {(n + 2) mod 6 | n. n \<in> N})) =
  P {0, 4, 2}"
proof -
  have seteq: "!!A B. (A = B) = ((!a : A. a:B) & (!b:B. b:A))"
    by blast
  have aux: "!!f A B. {f n | n. A n \<or> B n} = {f n | n. A n} \<union> {f n | n. B n}"
    apply blast
    done
  show ?thesis
    apply (subst lfp_conv_while [where ?U = "{0, 1, 2, 3, 4, 5}"])
       apply (rule monoI)
      apply blast
     apply simp
    apply (simp add: aux set_eq_subset)
    txt {* The fixpoint computation is performed purely by rewriting: *}
    apply (simp add: while_unfold aux seteq del: subset_empty)
    done
qed

end
