(*  Title:      HOL/Library/While.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen
*)

header {*
 \title{A general ``while'' combinator}
 \author{Tobias Nipkow}
*}

theory While_Combinator = Main:

text {*
 We define a while-combinator @{term while} and prove: (a) an
 unrestricted unfolding law (even if while diverges!)  (I got this
 idea from Wolfgang Goerigk), and (b) the invariant rule for reasoning
 about @{term while}.
*}

consts while_aux :: "('a => bool) \<times> ('a => 'a) \<times> 'a => 'a"
recdef (permissive) while_aux
  "same_fst (\<lambda>b. True) (\<lambda>b. same_fst (\<lambda>c. True) (\<lambda>c.
      {(t, s).  b s \<and> c s = t \<and>
        \<not> (\<exists>f. f (0::nat) = s \<and> (\<forall>i. b (f i) \<and> c (f i) = f (i + 1)))}))"
  "while_aux (b, c, s) =
    (if (\<exists>f. f (0::nat) = s \<and> (\<forall>i. b (f i) \<and> c (f i) = f (i + 1)))
      then arbitrary
      else if b s then while_aux (b, c, c s)
      else s)"

recdef_tc while_aux_tc: while_aux
  apply (rule wf_same_fst)
  apply (rule wf_same_fst)
  apply (simp add: wf_iff_no_infinite_down_chain)
  apply blast
  done

constdefs
  while :: "('a => bool) => ('a => 'a) => 'a => 'a"
  "while b c s == while_aux (b, c, s)"

lemma while_aux_unfold:
  "while_aux (b, c, s) =
    (if \<exists>f. f (0::nat) = s \<and> (\<forall>i. b (f i) \<and> c (f i) = f (i + 1))
      then arbitrary
      else if b s then while_aux (b, c, c s)
      else s)"
  apply (rule while_aux_tc [THEN while_aux.simps [THEN trans]])
  apply (rule refl)
  done

text {*
 The recursion equation for @{term while}: directly executable!
*}

theorem while_unfold [code]:
    "while b c s = (if b s then while b c (c s) else s)"
  apply (unfold while_def)
  apply (rule while_aux_unfold [THEN trans])
  apply auto
  apply (subst while_aux_unfold)
  apply simp
  apply clarify
  apply (erule_tac x = "\<lambda>i. f (Suc i)" in allE)
  apply blast
  done

hide const while_aux

lemma def_while_unfold: assumes fdef: "f == while test do"
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

theorem while_rule_lemma[rule_format]:
  "[| !!s. P s ==> b s ==> P (c s);
      !!s. P s ==> \<not> b s ==> Q s;
      wf {(t, s). P s \<and> b s \<and> t = c s} |] ==>
    P s --> Q (while b c s)"
proof -
  case rule_context
  assume wf: "wf {(t, s). P s \<and> b s \<and> t = c s}"
  show ?thesis
    apply (induct s rule: wf [THEN wf_induct])
    apply simp
    apply clarify
    apply (subst while_unfold)
    apply (simp add: rule_context)
    done
qed

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
apply(erule wf_subset)
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
apply (clarsimp simp add: inv_image_def finite_psubset_def order_less_le)
apply (blast intro!: finite_Diff dest: monoD)
done


text {*
 An example of using the @{term while} combinator.\footnote{It is safe
 to keep the example here, since there is no effect on the current
 theory.}
*}

theorem "P (lfp (\<lambda>N::int set. {0} \<union> {(n + 2) mod 6 | n. n \<in> N})) = P {0, 4, 2}"
proof -
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
    apply (simp add: while_unfold aux set_eq_subset del: subset_empty)
    done
qed

end
