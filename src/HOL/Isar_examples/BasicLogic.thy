(*  Title:      HOL/Isar_examples/BasicLogic.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Basic propositional and quantifier reasoning.
*)

header {* Basic logical reasoning *};

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
 excessive detail.  Several abbreviated language elements are
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
 remaining goals by assumption\footnote{This is not a completely
 trivial operation, as proof by assumption may involve full
 higher-order unification.}.  Thus we may skip the rather vacuous body
 of the above proof as well.
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
 Proof by a single rule may be abbreviated as double-dot.
*};

lemma "A --> A"; ..;

text {*
 Thus we have arrived at an adequate representation of the proof of a
 tautology that holds by a single standard rule.\footnote{Apparently,
 the rule here is implication introduction.}
*};

text {*
 Let us also reconsider $K$.  Its statement is composed of iterated
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
 rule application, this may go too far with iteration.  Thus in
 practice, $\idt{intro}$ and $\idt{elim}$ would be typically
 restricted to certain structures by giving a few rules only, e.g.\
 \isacommand{proof}~($\idt{intro}$~\name{impI}~\name{allI}) to strip
 implications and universal quantifiers.

 Such well-tuned iterated decomposition of certain structures is the
 prime application of $\idt{intro}$ and $\idt{elim}$.  In contrast,
 terminal steps that solve a goal completely are usually performed by
 actual automated proof methods (such as
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
 explicitly, since the goals $B$ and $A$ did not provide any
 structural clue.  This may be avoided using \isacommand{from} to
 focus on $\idt{prems}$ (i.e.\ the $A \conj B$ assumption) as the
 current facts, enabling the use of double-dot proofs.  Note that
 \isacommand{from} already does forward-chaining, involving the
 \name{conjE} rule here.
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
 In the subsequent version we flatten the structure of the main body
 by doing forward reasoning all the time.  Only the outermost
 decomposition step is left as backward.
*};

lemma "A & B --> B & A";
proof;
  assume ab: "A & B";
  from ab; have a: A; ..;
  from ab; have b: B; ..;
  from b a; show "B & A"; ..;
qed;

text {*
 We can still push forward reasoning a bit further, even at the risk
 of getting ridiculous.  Note that we force the initial proof step to
 do nothing here, by referring to the ``-'' proof method.
*};

lemma "A & B --> B & A";
proof -;
  {;
    assume ab: "A & B";
    from ab; have a: A; ..;
    from ab; have b: B; ..;
    from b a; have "B & A"; ..;
  };
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
 decomposition, and bottom-up forward composition.  In general, there
 is no single best way to arrange some pieces of formal reasoning, of
 course.  Depending on the actual applications, the intended audience
 etc., rules (and methods) on the one hand vs.\ facts on the other
 hand have to be emphasized in an appropriate way.  This requires the
 proof writer to develop good taste, and some practice, of course.
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
 \cite{isabelle-intro}, using HOL rather than FOL.
*};

subsubsection {* A propositional proof *};

text {*
 We consider the proposition $P \disj P \impl P$.  The proof below
 involves forward-chaining from $P \disj P$, followed by an explicit
 case-analysis on the two \emph{identical} cases.
*};

lemma "P | P --> P";
proof;
  assume "P | P";
  thus P;
  proof                    -- {*
    rule \name{disjE}: \smash{$\infer{C}{A \disj B & \infer*{C}{[A]} & \infer*{C}{[B]}}$}
  *};
    assume P; show P; .;
  next;
    assume P; show P; .;
  qed;
qed;

text {*
 Case splits are \emph{not} hardwired into the Isar language as a
 special feature.  The \isacommand{next} command used to separate the
 cases above is just a short form of managing block structure.

 \medskip In general, applying proof methods may split up a goal into
 separate ``cases'', i.e.\ new subgoals with individual local
 assumptions.  The corresponding proof text typically mimics this by
 establishing results in appropriate contexts, separated by blocks.

 In order to avoid too much explicit parentheses, the Isar system
 implicitly opens an additional block for any new goal, the
 \isacommand{next} statement then closes one block level, opening a
 new one.  The resulting behavior is what one would expect from
 separating cases, only that it is more flexible.  E.g.\ an induction
 base case (which does not introduce local assumptions) would
 \emph{not} require \isacommand{next} to separate the subsequent step
 case.

 \medskip In our example the situation is even simpler, since the two
 cases actually coincide.  Consequently the proof may be rephrased as
 follows.
*};

lemma "P | P --> P";
proof;
  assume "P | P";
  thus P;
  proof;
    assume P;
    show P; .;
    show P; .;
  qed;
qed;

text {*
 Again, the rather vacuous body of the proof may be collapsed.  Thus
 the case analysis degenerates into two assumption steps, which are
 implicitly performed when concluding the single rule step of the
 double-dot proof as follows.
*};

lemma "P | P --> P";
proof;
  assume "P | P";
  thus P; ..;
qed;


subsubsection {* A quantifier proof *};

text {*
 To illustrate quantifier reasoning, let us prove $(\ex x P \ap (f \ap
 x)) \impl (\ex x P \ap x)$.  Informally, this holds because any $a$
 with $P \ap (f \ap a)$ may be taken as a witness for the second
 existential statement.

 The first proof is rather verbose, exhibiting quite a lot of
 (redundant) detail.  It gives explicit rules, even with some
 instantiation.  Furthermore, we encounter two new language elements:
 the \isacommand{fix} command augments the context by some new
 ``arbitrary, but fixed'' element; the \isacommand{is} annotation
 binds term abbreviations by higher-order pattern matching.
*};

lemma "(EX x. P (f x)) --> (EX x. P x)";
proof;
  assume "EX x. P (f x)";
  thus "EX x. P x";
  proof (rule exE)             -- {*
    rule \name{exE}: \smash{$\infer{B}{\ex x A(x) & \infer*{B}{[A(x)]_x}}$}
  *};
    fix a;
    assume "P (f a)" (is "P ?witness");
    show ?thesis; by (rule exI [of P ?witness]);
  qed;
qed;

text {*
 While explicit rule instantiation may occasionally improve
 readability of certain aspects of reasoning, it is usually quite
 redundant.  Above, the basic proof outline gives already enough
 structural clues for the system to infer both the rules and their
 instances (by higher-order unification).  Thus we may as well prune
 the text as follows.
*};

lemma "(EX x. P (f x)) --> (EX x. P x)";
proof;
  assume "EX x. P (f x)";
  thus "EX x. P x";
  proof;
    fix a;
    assume "P (f a)";
    show ?thesis; ..;
  qed;
qed;

text {*
 Explicit $\exists$-elimination as seen above can become quite
 cumbersome in practice.  The derived Isar language element
 ``\isakeyword{obtain}'' provides a more handsome way to do
 generalized existence reasoning.
*};

lemma "(EX x. P (f x)) --> (EX x. P x)";
proof;
  assume "EX x. P (f x)";
  then; obtain a where "P (f a)"; by blast;
  thus "EX x. P x"; ..;
qed;

text {*
 Technically, \isakeyword{obtain} is similar to \isakeyword{fix} and
 \isakeyword{assume} together with a soundness proof of the
 elimination involved.  Thus it behaves similar to any other forward
 proof element.  Also note that due to the nature of general existence
 reasoning involved here, any result exported from the context of an
 \isakeyword{obtain} statement may \emph{not} refer to the parameters
 introduced there.
*};



subsubsection {* Deriving rules in Isabelle *};

text {*
 We derive the conjunction elimination rule from the corresponding
 projections.  The proof is quite straight-forward, since
 Isabelle/Isar supports non-atomic goals and assumptions fully
 transparently.
*};

theorem conjE: "A & B ==> (A ==> B ==> C) ==> C";
proof -;
  assume "A & B";
  assume r: "A ==> B ==> C";
  show C;
  proof (rule r);
    show A; by (rule conjunct1);
    show B; by (rule conjunct2);
  qed;
qed;

text {*
 Note that classic Isabelle handles higher rules in a slightly
 different way.  The tactic script as given in \cite{isabelle-intro}
 for the same example of \name{conjE} depends on the primitive
 \texttt{goal} command to decompose the rule into premises and
 conclusion.  The actual result would then emerge by discharging of
 the context at \texttt{qed} time.
*};

end;
