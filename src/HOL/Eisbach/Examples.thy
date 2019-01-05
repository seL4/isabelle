(*  Title:      HOL/Eisbach/Examples.thy
    Author:     Daniel Matichuk, NICTA/UNSW
*)

section \<open>Basic Eisbach examples\<close>

theory Examples
imports Main Eisbach_Tools
begin


subsection \<open>Basic methods\<close>

method my_intros = (rule conjI | rule impI)

lemma "P \<and> Q \<longrightarrow> Z \<and> X"
  apply my_intros+
  oops

method my_intros' uses intros = (rule conjI | rule impI | rule intros)

lemma "P \<and> Q \<longrightarrow> Z \<or> X"
  apply (my_intros' intros: disjI1)+
  oops

method my_spec for x :: 'a = (drule spec[where x="x"])

lemma "\<forall>x. P x \<Longrightarrow> P x"
  apply (my_spec x)
  apply assumption
  done


subsection \<open>Focusing and matching\<close>

method match_test =
  (match premises in U: "P x \<and> Q x" for P Q x \<Rightarrow>
    \<open>print_term P,
     print_term Q,
     print_term x,
     print_fact U\<close>)

lemma "\<And>x. P x \<and> Q x \<Longrightarrow> A x \<and> B x \<Longrightarrow> R x y \<Longrightarrow> True"
  apply match_test  \<comment> \<open>Valid match, but not quite what we were expecting..\<close>
  back  \<comment> \<open>Can backtrack over matches, exploring all bindings\<close>
  back
  back
  back
  back
  back  \<comment> \<open>Found the other conjunction\<close>
  back
  back
  back
  oops

text \<open>Use matching to avoid "improper" methods\<close>

lemma focus_test:
  shows "\<And>x. \<forall>x. P x \<Longrightarrow> P x"
  apply (my_spec "x :: 'a", assumption)?  \<comment> \<open>Wrong x\<close>
  apply (match conclusion in "P x" for x \<Rightarrow> \<open>my_spec x, assumption\<close>)
  done


text \<open>Matches are exclusive. Backtracking will not occur past a match\<close>

method match_test' =
  (match conclusion in
    "P \<and> Q" for P Q \<Rightarrow>
      \<open>print_term P, print_term Q, rule conjI[where P="P" and Q="Q"]; assumption\<close>
    \<bar> "H" for H \<Rightarrow> \<open>print_term H\<close>)

text \<open>Solves goal\<close>
lemma "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q"
  apply match_test'
  done

text \<open>Fall-through case never taken\<close>
lemma "P \<and> Q"
  apply match_test'?
  oops

lemma "P"
  apply match_test'
  oops


method my_spec_guess =
  (match conclusion in "P (x :: 'a)" for P x \<Rightarrow>
    \<open>drule spec[where x=x],
     print_term P,
     print_term x\<close>)

lemma "\<forall>x. P (x :: nat) \<Longrightarrow> Q (x :: nat)"
  apply my_spec_guess
  oops

method my_spec_guess2 =
  (match premises in U[thin]:"\<forall>x. P x \<longrightarrow> Q x" and U':"P x" for P Q x \<Rightarrow>
    \<open>insert spec[where x=x, OF U],
     print_term P,
     print_term Q\<close>)

lemma "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> Q x \<Longrightarrow> Q x"
  apply my_spec_guess2?  \<comment> \<open>Fails. Note that both "P"s must match\<close>
  oops

lemma "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> P x \<Longrightarrow> Q x"
  apply my_spec_guess2
  apply (erule mp)
  apply assumption
  done


subsection \<open>Higher-order methods\<close>

method higher_order_example for x methods meth =
  (cases x, meth, meth)

lemma
  assumes A: "x = Some a"
  shows "the x = a"
  by (higher_order_example x \<open>simp add: A\<close>)


subsection \<open>Recursion\<close>

method recursion_example for x :: bool =
  (print_term x,
     match (x) in "A \<and> B" for A B \<Rightarrow>
    \<open>print_term A,
     print_term B,
     recursion_example A,
     recursion_example B | -\<close>)

lemma "P"
  apply (recursion_example "(A \<and> D) \<and> (B \<and> C)")
  oops


subsection \<open>Solves combinator\<close>

lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  apply (solves \<open>rule conjI\<close>)?  \<comment> \<open>Doesn't solve the goal!\<close>
  apply (solves \<open>rule conjI, assumption, assumption\<close>)
  done


subsection \<open>Demo\<close>

named_theorems intros and elims and subst

method prop_solver declares intros elims subst =
  (assumption |
    rule intros | erule elims |
    subst subst | subst (asm) subst |
    (erule notE; solves prop_solver))+

lemmas [intros] =
  conjI
  impI
  disjCI
  iffI
  notI
lemmas [elims] =
  impCE
  conjE
  disjE

lemma "((A \<or> B) \<and> (A \<longrightarrow> C) \<and> (B \<longrightarrow> C)) \<longrightarrow> C"
  apply prop_solver
  done

method guess_all =
  (match premises in U[thin]:"\<forall>x. P (x :: 'a)" for P \<Rightarrow>
    \<open>match premises in "?H (y :: 'a)" for y \<Rightarrow>
       \<open>rule allE[where P = P and x = y, OF U]\<close>
   | match conclusion in "?H (y :: 'a)" for y \<Rightarrow>
       \<open>rule allE[where P = P and x = y, OF U]\<close>\<close>)

lemma "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> P y \<Longrightarrow> Q y"
  apply guess_all
  apply prop_solver
  done

lemma "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> P z \<Longrightarrow> P y \<Longrightarrow> Q y"
  apply (solves \<open>guess_all, prop_solver\<close>)  \<comment> \<open>Try it without solve\<close>
  done

method guess_ex =
  (match conclusion in
    "\<exists>x. P (x :: 'a)" for P \<Rightarrow>
      \<open>match premises in "?H (x :: 'a)" for x \<Rightarrow>
              \<open>rule exI[where x=x]\<close>\<close>)

lemma "P x \<Longrightarrow> \<exists>x. P x"
  apply guess_ex
  apply prop_solver
  done

method fol_solver =
  ((guess_ex | guess_all | prop_solver); solves fol_solver)

declare
  allI [intros]
  exE [elims]
  ex_simps [subst]
  all_simps [subst]

lemma "(\<forall>x. P x) \<and> (\<forall>x. Q x) \<Longrightarrow> (\<forall>x. P x \<and> Q x)"
  and  "\<exists>x. P x \<longrightarrow> (\<forall>x. P x)"
  and "(\<exists>x. \<forall>y. R x y) \<longrightarrow> (\<forall>y. \<exists>x. R x y)"
  by fol_solver+


text \<open>
  Eisbach_Tools provides the catch method, which catches run-time method
  errors. In this example the OF attribute throws an error when it can't
  compose H with A, forcing H to be re-bound to different members of imps
  until it succeeds.
\<close>

lemma
  assumes imps:  "A \<Longrightarrow> B" "A \<Longrightarrow> C" "B \<Longrightarrow> D"
  assumes A: "A"
  shows "B \<and> C"
  apply (rule conjI)
  apply ((match imps in H:"_ \<Longrightarrow> _" \<Rightarrow> \<open>catch \<open>rule H[OF A], print_fact H\<close> \<open>print_fact H, fail\<close>\<close>)+)
  done

text \<open>
  Eisbach_Tools provides the curry and uncurry attributes. This is useful
  when the number of premises of a thm isn't known statically. The pattern
  \<^term>\<open>P \<Longrightarrow> Q\<close> matches P against the major premise of a thm, and Q is the
  rest of the premises with the conclusion. If we first uncurry, then \<^term>\<open>P \<Longrightarrow> Q\<close> will match P with the conjunction of all the premises, and Q with
  the final conclusion of the rule.
\<close>

lemma
  assumes imps: "A \<Longrightarrow> B \<Longrightarrow> C" "D \<Longrightarrow> C" "E \<Longrightarrow> D \<Longrightarrow> A"
  shows "(A \<longrightarrow> B \<longrightarrow> C) \<and> (D \<longrightarrow> C)"
    by (match imps[uncurry] in H[curry]:"_ \<Longrightarrow> C" (cut, multi) \<Rightarrow>
                    \<open>match H in "E \<Longrightarrow> _" \<Rightarrow> fail
                                      \<bar> _ \<Rightarrow> \<open>simp add: H\<close>\<close>)

end
