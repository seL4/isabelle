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
recdef while_aux
  "same_fst (\<lambda>b. True) (\<lambda>b. same_fst (\<lambda>c. True) (\<lambda>c.
      {(t, s).  b s \<and> c s = t \<and>
        \<not> (\<exists>f. f 0 = s \<and> (\<forall>i. b (f i) \<and> c (f i) = f (i + 1)))}))"
  "while_aux (b, c, s) =
    (if (\<exists>f. f 0 = s \<and> (\<forall>i. b (f i) \<and> c (f i) = f (i + 1)))
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
    (if \<exists>f. f 0 = s \<and> (\<forall>i. b (f i) \<and> c (f i) = f (i + 1))
      then arbitrary
      else if b s then while_aux (b, c, c s)
      else s)"
  apply (rule while_aux_tc [THEN while_aux.simps [THEN trans]])
   apply (simp add: same_fst_def)
  apply (rule refl)
  done

text {*
 The recursion equation for @{term while}: directly executable!
*}

theorem while_unfold:
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

text {*
 The proof rule for @{term while}, where @{term P} is the invariant.
*}

theorem while_rule_lemma[rule_format]:
  "(!!s. P s ==> b s ==> P (c s)) ==>
    (!!s. P s ==> \<not> b s ==> Q s) ==>
    wf {(t, s). P s \<and> b s \<and> t = c s} ==>
    P s --> Q (while b c s)"
proof -
  case antecedent
  assume wf: "wf {(t, s). P s \<and> b s \<and> t = c s}"
  show ?thesis
    apply (induct s rule: wf [THEN wf_induct])
    apply simp
    apply clarify
    apply (subst while_unfold)
    apply (simp add: antecedent)
    done
qed

theorem while_rule:
  "[| P s; !!s. [| P s; b s  |] ==> P (c s);
    !!s. [| P s; \<not> b s  |] ==> Q s;
    wf r;  !!s. [| P s; b s  |] ==> (c s, s) \<in> r |] ==>
    Q (while b c s)"
apply (rule while_rule_lemma)
prefer 4 apply assumption
apply blast
apply blast
apply(erule wf_subset)
apply blast
done

hide const while_aux

end
