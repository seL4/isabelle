theory Isar0 = Main:

(*
proof ::= "proof" [method] statement* "qed"
        | "by" method
statement ::= "fix" variables
            | "assume" proposition*
            | ["then"] ("show" | "have") proposition proof
proposition ::= [label":"] string

Typical skelton:

proof
assume <assumptions>
have <formula1> -- intermediate result
:
have <formulan> -- intermediate result
show ?thesis -- the conclusion
end
*)

lemma "A \<longrightarrow> A"
proof (rule impI)
  assume A: "A"
  show "A" by(rule A)
qed

(* Operational reading: assume A - show A proves "A \<Longrightarrow> A", which rule impI
turns into the desired "A \<longrightarrow> A".  Too much (operational) text *)

(* 1st Principle: let "proof" select the rule automatically; based on the
goal and a predefined list of (introduction) rules. Here: impI is found
automatically: *)

lemma "A \<longrightarrow> A"
proof
  assume A: "A"
  show "A" by(rule A)
qed

(* Proof by assumption should be trivial. Method "." does just that (and a
bit more - see later). Thus naming of assumptions is often superfluous. *)

lemma "A \<longrightarrow> A"
proof
  assume "A"
  have "A" .
qed

(* To hide proofs by assumption, by(method) first applies method and then
tries to solve all remaining subgoals by assumption. *)

lemma "A \<longrightarrow> A & A"
proof
  assume A
  show "A & A" by(rule conjI)
qed

(* Proofs of the form by(rule <rule>) can be abbreviated to ".." if <rule> is
one of the predefined introduction rules (for user supplied rules see below).
Thus
*)

lemma "A \<longrightarrow> A & A"
proof
  assume A
  show "A & A" ..
qed

(* What happens: applies "conj" (first "."), then solves the two subgoals by
assumptions (second ".") *)

(* Now: elimination *)

lemma "A & B \<longrightarrow> B & A"
proof
  assume AB: "A & B"
  show "B & A"
  proof (rule conjE[OF AB])
    assume A and B
    show ?thesis .. --"thesis = statement in previous show"
  qed
qed

(* Again: too much text.

Elimination rules are used to conclude new stuff from old. In Isar they are
triggered by propositions being fed INTO a proof block. Syntax:
from <previously proved propositions> show \<dots>
applies an elimination rule whose first premise matches one of the <previously proved propositions>. Thus:
*)

lemma "A & B \<longrightarrow> B & A"
proof
  assume AB: "A & B"
  from AB show "B & A"
  proof
    assume A and B
    show ?thesis ..
  qed
qed

(* 
2nd principle: try to arrange sequence of propositions in a UNIX like
pipe, such that the proof of the next proposition uses the previous
one. The previous proposition can be referred to via "this".
This greatly reduces the need for explicit naming of propositions.
*)
lemma "A & B \<longrightarrow> B & A"
proof
  assume "A & B"
  from this show "B & A"
  proof
    assume A and B
    show ?thesis ..
  qed
qed

(* Final simplification: "from this" = "thus".

Alternative: pure forward reasoning: *)

lemma "A & B --> B & A"
proof
  assume ab: "A & B"
  from ab have a: A ..
  from ab have b: B ..
  from b a show "B & A" ..
qed

(* New: itermediate haves *)

(* The predefined introduction and elimination rules include all the usual
natural deduction rules for propositional logic. Here is a longer example: *)

lemma "~(A & B) \<longrightarrow> ~A | ~B"
proof
  assume n: "~(A & B)"
  show "~A | ~B"
  proof (rule ccontr)
    assume nn: "~(~ A | ~B)"
    from n show False
    proof
      show "A & B"
      proof
	show A
	proof (rule ccontr)
	  assume "~A"
	  have "\<not> A \<or> \<not> B" ..
	  from nn this show False ..
	qed
      next
	show B
	proof (rule ccontr)
	  assume "~B"
	  have "\<not> A \<or> \<not> B" ..
	  from nn this show False ..
	qed
      qed
    qed
  qed
qed;

(* New:

1. Multiple subgoals. When showing "A & B" we need to show both A and B.
Each subgoal is proved separately, in ANY order. The individual proofs are
separated by "next".

2.  "have" for proving an intermediate fact
*)

subsection{*Becoming more concise*}

(* Normally want to prove rules expressed with \<Longrightarrow>, not \<longrightarrow> *)

lemma "\<lbrakk> A \<Longrightarrow> False \<rbrakk> \<Longrightarrow> \<not> A"
proof
  assume "A \<Longrightarrow> False" A
  thus False .
qed

(* In this case the "proof" works on the "~A", thus selecting notI

Now: avoid repeating formulae (which may be large). *)

lemma "(large_formula \<Longrightarrow> False) \<Longrightarrow> ~ large_formula"
      (is "(?P \<Longrightarrow> _) \<Longrightarrow> _")
proof
  assume "?P \<Longrightarrow> False" ?P
  thus False .
qed

(* Even better: can state assumptions directly *)

lemma assumes A: "large_formula \<Longrightarrow> False"
      shows "~ large_formula" (is "~ ?P")
proof
  assume ?P
  from A show False .
qed;


(* Predicate calculus. Keyword fix introduces new local variables into a
proof. Corresponds to !! just like assume-show corresponds to \<Longrightarrow> *)

lemma assumes P: "!x. P x" shows "!x. P(f x)"
proof --"allI"
  fix x
  from P show "P(f x)" .. --"allE"
qed

lemma assumes Pf: "EX x. P (f x)" shows "EX y. P y"
proof -
  from Pf show ?thesis
  proof  --"exE"
    fix a
    assume "P(f a)"
    show ?thesis ..  --"exI"
  qed
qed

text {*
 Explicit $\exists$-elimination as seen above can become quite
 cumbersome in practice.  The derived Isar language element
 ``\isakeyword{obtain}'' provides a more handsome way to do
 generalized existence reasoning.
*}

lemma assumes Pf: "EX x. P (f x)" shows "EX y. P y"
proof -
  from Pf obtain a where "P (f a)" ..  --"exE"
  thus "EX y. P y" ..  --"exI"
qed

text {*
 Technically, \isakeyword{obtain} is similar to \isakeyword{fix} and
 \isakeyword{assume} together with a soundness proof of the
 elimination involved.  Thus it behaves similar to any other forward
 proof element.  Also note that due to the nature of general existence
 reasoning involved here, any result exported from the context of an
 \isakeyword{obtain} statement may \emph{not} refer to the parameters
 introduced there.
*}

lemma assumes ex: "EX x. ALL y. P x y" shows "ALL y. EX x. P x y"
proof  --"allI"
  fix y
  from ex obtain x where "ALL y. P x y" ..  --"exE"
  from this have "P x y" ..  --"allE"
  thus "EX x. P x y" ..  --"exI"
qed

(* some example with blast, if . and .. fail *)

theorem "EX S. S ~: range (f :: 'a => 'a set)"
proof
  let ?S = "{x. x ~: f x}"
  show "?S ~: range f"
  proof
    assume "?S : range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof (cases)
      assume "y : ?S"
      with fy show False by blast
    next
      assume "y ~: ?S"
      with fy show False by blast
    qed
  qed
qed

theorem "EX S. S ~: range (f :: 'a => 'a set)"
proof
  let ?S = "{x. x ~: f x}"
  show "?S ~: range f"
  proof
    assume "?S : range f"
    then obtain y where eq: "?S = f y" ..
    show False
    proof (cases)
      assume A: "y : ?S"
      hence isin: "y : f y"   by(simp add:eq)
      from A have "y ~: f y"  by simp
      with isin show False    by contradiction
    next
      assume A: "y ~: ?S"
      hence notin: "y ~: f y"  by(simp add:eq)
      from A have "y : f y"    by simp
      with notin show False    by contradiction
    qed
  qed
qed

text {*
  How much creativity is required?  As it happens, Isabelle can prove
  this theorem automatically using best-first search.  Depth-first
  search would diverge, but best-first search successfully navigates
  through the large search space.  The context of Isabelle's classical
  prover contains rules for the relevant constructs of HOL's set
  theory.
*}

theorem "EX S. S ~: range (f :: 'a => 'a set)"
  by best

end
