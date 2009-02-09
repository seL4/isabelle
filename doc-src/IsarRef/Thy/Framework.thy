theory Framework
imports Main
begin

chapter {* The Isabelle/Isar Framework \label{ch:isar-framework} *}

text {*
  Isabelle/Isar
  \cite{Wenzel:1999:TPHOL,Wenzel-PhD,Nipkow-TYPES02,Wenzel-Paulson:2006,Wenzel:2006:Festschrift}
  is intended as a generic framework for developing formal
  mathematical documents with full proof checking.  Definitions and
  proofs are organized as theories; an assembly of theory sources may
  be presented as a printed document; see also
  \chref{ch:document-prep}.

  The main objective of Isar is the design of a human-readable
  structured proof language, which is called the ``primary proof
  format'' in Isar terminology.  Such a primary proof language is
  somewhere in the middle between the extremes of primitive proof
  objects and actual natural language.  In this respect, Isar is a bit
  more formalistic than Mizar
  \cite{Trybulec:1993:MizarFeatures,Rudnicki:1992:MizarOverview,Wiedijk:1999:Mizar},
  using logical symbols for certain reasoning schemes where Mizar
  would prefer English words; see \cite{Wenzel-Wiedijk:2002} for
  further comparisons of these systems.

  So Isar challenges the traditional way of recording informal proofs
  in mathematical prose, as well as the common tendency to see fully
  formal proofs directly as objects of some logical calculus (e.g.\
  @{text "\<lambda>"}-terms in a version of type theory).  In fact, Isar is
  better understood as an interpreter of a simple block-structured
  language for describing data flow of local facts and goals,
  interspersed with occasional invocations of proof methods.
  Everything is reduced to logical inferences internally, but these
  steps are somewhat marginal compared to the overall bookkeeping of
  the interpretation process.  Thanks to careful design of the syntax
  and semantics of Isar language elements, a formal record of Isar
  instructions may later appear as an intelligible text to the
  attentive reader.

  The Isar proof language has emerged from careful analysis of some
  inherent virtues of the existing logical framework of Isabelle/Pure
  \cite{paulson-found,paulson700}, notably composition of higher-order
  natural deduction rules, which is a generalization of Gentzen's
  original calculus \cite{Gentzen:1935}.  The approach of generic
  inference systems in Pure is continued by Isar towards actual proof
  texts.

  Concrete applications require another intermediate layer: an
  object-logic.  Isabelle/HOL \cite{isa-tutorial} (simply-typed
  set-theory) is being used most of the time; Isabelle/ZF
  \cite{isabelle-ZF} is less extensively developed, although it would
  probably fit better for classical mathematics.

  \medskip In order to illustrate typical natural deduction reasoning
  in Isar, we shall refer to the background theory and library of
  Isabelle/HOL.  This includes common notions of predicate logic,
  naive set-theory etc.\ using fairly standard mathematical notation.
  From the perspective of generic natural deduction there is nothing
  special about the logical connectives of HOL (@{text "\<and>"}, @{text
  "\<or>"}, @{text "\<forall>"}, @{text "\<exists>"}, etc.), only the resulting reasoning
  principles are relevant to the user.  There are similar rules
  available for set-theory operators (@{text "\<inter>"}, @{text "\<union>"}, @{text
  "\<Inter>"}, @{text "\<Union>"}, etc.), or any other theory developed in the
  library (lattice theory, topology etc.).

  Subsequently we briefly review fragments of Isar proof texts
  corresponding directly to such general natural deduction schemes.
  The examples shall refer to set-theory, to minimize the danger of
  understanding connectives of predicate logic as something special.

  \medskip The following deduction performs @{text "\<inter>"}-introduction,
  working forwards from assumptions towards the conclusion.  We give
  both the Isar text, and depict the primitive rule involved, as
  determined by unification of the problem against rules from the
  context.
*}

text_raw {*\medskip\begin{minipage}{0.6\textwidth}*}

(*<*)
lemma True
proof
(*>*)
    assume "x \<in> A" and "x \<in> B"
    then have "x \<in> A \<inter> B" ..
(*<*)
qed
(*>*)

text_raw {*\end{minipage}\begin{minipage}{0.4\textwidth}*}

text {*
  \infer{@{prop "x \<in> A \<inter> B"}}{@{prop "x \<in> A"} & @{prop "x \<in> B"}}
*}

text_raw {*\end{minipage}*}

text {*
  \medskip\noindent Note that @{command "assume"} augments the
  context, @{command "then"} indicates that the current facts shall be
  used in the next step, and @{command "have"} states a local claim.
  The two dots ``@{command ".."}'' above refer to a complete proof of
  the claim, using the indicated facts and a canonical rule from the
  context.  We could have been more explicit here by spelling out the
  final proof step via the @{command "by"} command:
*}

(*<*)
lemma True
proof
(*>*)
    assume "x \<in> A" and "x \<in> B"
    then have "x \<in> A \<inter> B" by (rule IntI)
(*<*)
qed
(*>*)

text {*
  \noindent The format of the @{text "\<inter>"}-introduction rule represents
  the most basic inference, which proceeds from given premises to a
  conclusion, without any additional context involved.

  \medskip The next example performs backwards introduction on @{term
  "\<Inter>\<A>"}, the intersection of all sets within a given set.  This
  requires a nested proof of set membership within a local context of
  an arbitrary-but-fixed member of the collection:
*}

text_raw {*\medskip\begin{minipage}{0.6\textwidth}*}

(*<*)
lemma True
proof
(*>*)
    have "x \<in> \<Inter>\<A>"
    proof
      fix A
      assume "A \<in> \<A>"
      show "x \<in> A" sorry
    qed
(*<*)
qed
(*>*)

text_raw {*\end{minipage}\begin{minipage}{0.4\textwidth}*}

text {*
  \infer{@{prop "x \<in> \<Inter>\<A>"}}{\infer*{@{prop "x \<in> A"}}{@{text "[A][A \<in> \<A>]"}}}
*}

text_raw {*\end{minipage}*}

text {*
  \medskip\noindent This Isar reasoning pattern again refers to the
  primitive rule depicted above.  The system determines it in the
  ``@{command "proof"}'' step, which could have been spelt out more
  explicitly as ``@{command "proof"}~@{text "("}@{method rule}~@{fact
  InterI}@{text ")"}''.  Note that this rule involves both a local
  parameter @{term "A"} and an assumption @{prop "A \<in> \<A>"} in the
  nested reasoning.  This kind of compound rule typically demands a
  genuine sub-proof in Isar, working backwards rather than forwards as
  seen before.  In the proof body we encounter the @{command
  "fix"}-@{command "assume"}-@{command "show"} skeleton of nested
  sub-proofs that is typical for Isar.  The final @{command "show"} is
  like @{command "have"} followed by an additional refinement of the
  enclosing claim, using the rule derived from the proof body.  The
  @{command "sorry"} command stands for a hole in the proof -- it may
  be understood as an excuse for not providing a proper proof yet.

  \medskip The next example involves @{term "\<Union>\<A>"}, which can be
  characterized as the set of all @{term "x"} such that @{prop "\<exists>A. x
  \<in> A \<and> A \<in> \<A>"}.  The elimination rule for @{prop "x \<in> \<Union>\<A>"} does
  not mention @{text "\<exists>"} and @{text "\<and>"} at all, but admits to obtain
  directly a local @{term "A"} such that @{prop "x \<in> A"} and @{prop "A
  \<in> \<A>"} hold.  This corresponds to the following Isar proof and
  inference rule, respectively:
*}

text_raw {*\medskip\begin{minipage}{0.6\textwidth}*}

(*<*)
lemma True
proof
(*>*)
    assume "x \<in> \<Union>\<A>"
    then have C
    proof
      fix A
      assume "x \<in> A" and "A \<in> \<A>"
      show C sorry
    qed
(*<*)
qed
(*>*)

text_raw {*\end{minipage}\begin{minipage}{0.4\textwidth}*}

text {*
  \infer{@{prop "C"}}{@{prop "x \<in> \<Union>\<A>"} & \infer*{@{prop "C"}~}{@{text "[A][x \<in> A, A \<in> \<A>]"}}}
*}

text_raw {*\end{minipage}*}

text {*
  \medskip\noindent Although the Isar proof follows the natural
  deduction rule closely, the text reads not as natural as
  anticipated.  There is a double occurrence of an arbitrary
  conclusion @{prop "C"}, which represents the final result, but is
  irrelevant for now.  This issue arises for any elimination rule
  involving local parameters.  Isar provides the derived language
  element @{command "obtain"}, which is able to perform the same
  elimination proof more conveniently:
*}

(*<*)
lemma True
proof
(*>*)
    assume "x \<in> \<Union>\<A>"
    then obtain A where "x \<in> A" and "A \<in> \<A>" ..
(*<*)
qed
(*>*)

text {*
  \noindent Here we avoid to mention the final conclusion @{prop "C"}
  and return to plain forward reasoning.  The rule involved in the
  ``@{command ".."}'' proof is the same as before.
*}

end
