(*  Title:      HOL/Isar_examples/BasicLogic.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Basic propositional and quantifier reasoning.
*)

header {* Basic reasoning *};

theory BasicLogic = Main:;


subsection {* Pure backward reasoning *};

text {*
 In order to get a first idea of how Isabelle/Isar proof documents may
 look like, we consider the propositions $I$, $K$, and $S$.  The
 following (rather explicit) proofs should require little extra
 explanations.
*};

lemma I: "A --> A";
proof;
  assume A;
  show A; by assumption;
qed;

lemma K: "A --> B --> A";
proof;
  assume A;
  show "B --> A";
  proof;
    show A; by assumption;
  qed;
qed;

lemma S: "(A --> B --> C) --> (A --> B) --> A --> C";
proof;
  assume "A --> B --> C";
  show "(A --> B) --> A --> C";
  proof;
    assume "A --> B";
    show "A --> C";
    proof;
      assume A;
      show C;
      proof (rule mp);
	show "B --> C"; by (rule mp);
        show B; by (rule mp);
      qed;
    qed;
  qed;
qed;

text {*
 Isar provides several ways to fine-tune the reasoning, avoiding
 irrelevant detail.  Several abbreviated language elements are
 available, enabling the writer to express proofs in a more concise
 way, even without referring to any automated proof tools yet.

 First of all, proof by assumption may be abbreviated as a single dot.
*};

lemma "A --> A";
proof;
  assume A;
  show A; .;
qed;

text {*
 In fact, concluding any (sub-)proof already involves solving any
 remaining goals by assumption.  Thus we may skip the rather vacuous
 body of the above proof as well.
*};

lemma "A --> A";
proof;
qed;

text {*
 Note that the \isacommand{proof} command refers to the $\idt{rule}$
 method (without arguments) by default.  Thus it implicitly applies a
 single rule, as determined from the syntactic form of the statements
 involved.  The \isacommand{by} command abbreviates any proof with
 empty body, so the proof may be further pruned.
*};

lemma "A --> A";
  by rule;

text {*
 Proof by a single rule may be abbreviated as a double dot.
*};

lemma "A --> A"; ..;

text {*
 Thus we have arrived at an adequate representation of the proof of a
 tautology that holds by a single standard rule.\footnote{Here the
 rule is implication introduction.}
*};

text {*
 Let us also reconsider $K$.  It's statement is composed of iterated
 connectives.  Basic decomposition is by a single rule at a time,
 which is why our first version above was by nesting two proofs.

 The $\idt{intro}$ proof method repeatedly decomposes a goal's
 conclusion.\footnote{The dual method is $\idt{elim}$, acting on a
 goal's premises.}
*};

lemma "A --> B --> A";
proof intro;
  assume A;
  show A; .;
qed;

text {*
 Again, the body may be collapsed.
*};

lemma "A --> B --> A";
  by intro;

text {*
 Just like $\idt{rule}$, the $\idt{intro}$ and $\idt{elim}$ proof
 methods pick standard structural rules, in case no explicit arguments
 are given.  While implicit rules are usually just fine for single
 rule application, this may go too far in iteration.  Thus in
 practice, $\idt{intro}$ and $\idt{elim}$ would be typically
 restricted to certain structures by giving a few rules only, e.g.\
 $(\idt{intro}~\name{impI}~\name{allI})$ to strip implications and
 universal quantifiers.

 Such well-tuned iterated decomposition of certain structure is the
 prime application of $\idt{intro}$~/ $\idt{elim}$.  In general,
 terminal steps that solve a goal completely are typically performed
 by actual automated proof methods (e.g.\
 \isacommand{by}~$\idt{blast}$).
*};


subsection {* Variations of backward vs.\ forward reasoning *};

text {*
 Certainly, any proof may be performed in backward-style only.  On the
 other hand, small steps of reasoning are often more naturally
 expressed in forward-style.  Isar supports both backward and forward
 reasoning as a first-class concept.  In order to demonstrate the
 difference, we consider several proofs of $A \conj B \impl B \conj
 A$.

 The first version is purely backward.
*};

lemma "A & B --> B & A";
proof;
  assume "A & B";
  show "B & A";
  proof;
    show B; by (rule conjunct2);
    show A; by (rule conjunct1);
  qed;
qed;

text {*
 Above, the $\idt{conjunct}_{1/2}$ projection rules had to be named
 explicitly, since the goals did not provide any structural clue.
 This may be avoided using \isacommand{from} to focus on $\idt{prems}$
 (i.e.\ the $A \conj B$ assumption) as the current facts, enabling the
 use of double-dot proofs.  Note that \isacommand{from} already
 involves forward-chaining.
*};

lemma "A & B --> B & A";
proof;
  assume "A & B";
  show "B & A";
  proof;
    from prems; show B; ..;
    from prems; show A; ..;
  qed;
qed;

text {*
 In the next version, we move the forward step one level upwards.
 Forward-chaining from the most recent facts is indicated by the
 \isacommand{then} command.  Thus the proof of $B \conj A$ from $A
 \conj B$ actually becomes an elimination, rather than an
 introduction.  The resulting proof structure directly corresponds to
 that of the $\name{conjE}$ rule, including the repeated goal
 proposition that is abbreviated as $\var{thesis}$ below.
*};

lemma "A & B --> B & A";
proof;
  assume "A & B";
  then; show "B & A";
  proof                    -- {* rule \name{conjE} of $A \conj B$ *};
    assume A B;
    show ?thesis; ..       -- {* rule \name{conjI} of $B \conj A$ *};
  qed;
qed;

text {*
 Subsequently, only the outermost decomposition step is left backward,
 all the rest is forward.
*};

lemma "A & B --> B & A";
proof;
  assume ab: "A & B";
  from ab; have a: A; ..;
  from ab; have b: B; ..;
  from b a; show "B & A"; ..;
qed;

text {*
 We can still push forward reasoning a bit further, even at the danger
 of getting ridiculous.  Note that we force the initial proof step to
 do nothing, by referring to the ``-'' proof method.
*};

lemma "A & B --> B & A";
proof -;
  {{;
    assume ab: "A & B";
    from ab; have a: A; ..;
    from ab; have b: B; ..;
    from b a; have "B & A"; ..;
  }};
  thus ?thesis; ..         -- {* rule \name{impI} *};
qed;

text {*
 \medskip With these examples we have shifted through a whole range
 from purely backward to purely forward reasoning.  Apparently, in the
 extreme ends we get slightly ill-structured proofs, which also
 require much explicit naming of either rules (backward) or local
 facts (forward).

 The general lesson learned here is that good proof style would
 achieve just the \emph{right} balance of top-down backward
 decomposition, and bottom-up forward composition.  In practice, there
 is no single best way to arrange some pieces of formal reasoning, of
 course.  Depending on the actual applications, the intended audience
 etc., certain aspects such as rules~/ methods vs.\ facts have to be
 emphasised in an appropriate way.  This requires the proof writer to
 develop good taste, and some practice, of course.
*};

text {*
 For our example the most appropriate way of reasoning is probably the
 middle one, with conjunction introduction done after elimination.
 This reads even more concisely using \isacommand{thus}, which
 abbreviates \isacommand{then}~\isacommand{show}.\footnote{In the same
 vein, \isacommand{hence} abbreviates
 \isacommand{then}~\isacommand{have}.}
*};

lemma "A & B --> B & A";
proof;
  assume "A & B";
  thus "B & A";
  proof;
    assume A B;
    show ?thesis; ..;
  qed;
qed;



subsection {* A few examples from ``Introduction to Isabelle'' *};

text {*
 We rephrase some of the basic reasoning examples of
 \cite{isabelle-intro}.
*};

subsubsection {* Propositional proof *};

lemma "P | P --> P";
proof;
  assume "P | P";
  then; show P;
  proof;
    assume P;
    show P; .;
    show P; .;
  qed;
qed;

lemma "P | P --> P";
proof;
  assume "P | P";
  then; show P; ..;
qed;


subsubsection {* Quantifier proof *};

lemma "(EX x. P(f(x))) --> (EX x. P(x))";
proof;
  assume "EX x. P(f(x))";
  then; show "EX x. P(x)";
  proof (rule exE);
    fix a;
    assume "P(f(a))" (is "P(?witness)");
    show ?thesis; by (rule exI [of P ?witness]);
  qed;
qed;

lemma "(EX x. P(f(x))) --> (EX x. P(x))";
proof;
  assume "EX x. P(f(x))";
  then; show "EX x. P(x)";
  proof;
    fix a;
    assume "P(f(a))";
    show ?thesis; ..;
  qed;
qed;

lemma "(EX x. P(f(x))) --> (EX x. P(x))";
  by blast;


subsubsection {* Deriving rules in Isabelle *};

text {* We derive the conjunction elimination rule from the
 projections.  The proof below follows the basic reasoning of the
 script given in the Isabelle Intro Manual closely.  Although, the
 actual underlying operations on rules and proof states are quite
 different: Isabelle/Isar supports non-atomic goals and assumptions
 fully transparently, while the original Isabelle classic script
 depends on the primitive goal command to decompose the rule into
 premises and conclusion, with the result emerging by discharging the
 context again later. *};

theorem conjE: "A & B ==> (A ==> B ==> C) ==> C";
proof -;
  assume ab: "A & B";
  assume ab_c: "A ==> B ==> C";
  show C;
  proof (rule ab_c);
    from ab; show A; ..;
    from ab; show B; ..;
  qed;
qed;

end;
