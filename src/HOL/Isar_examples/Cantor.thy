(*  Title:      HOL/Isar_examples/Cantor.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Cantor's theorem -- Isar'ized version of the final section of the HOL
chapter of "Isabelle's Object-Logics" (Larry Paulson).
*)

theory Cantor = Main:;


section "Example: Cantor's Theorem";

text {*
  Cantor's Theorem states that every set has more subsets than it has
  elements.  It has become a favourite example in higher-order logic
  since it is so easily expressed: @{display term[show_types] "ALL f
  :: 'a => 'a => bool. EX S :: 'a => bool. ALL x::'a. f x ~= S"}

  Viewing types as sets, @{type "'a => bool"} represents the powerset
  of @{type 'a}.  This version states that for every function from
  @{type 'a} to its powerset, some subset is outside its range.

  The Isabelle/Isar proofs below use HOL's set theory, with the type
  @{type "'a set"} and the operator @{term range}.
*};


text {*
  We first consider a rather verbose version of the proof, with the
  reasoning expressed quite naively.  We only make use of the pure
  core of the Isar proof language.
*};

theorem "EX S. S ~: range(f :: 'a => 'a set)";
proof;
  let ??S = "{x. x ~: f x}";
  show "??S ~: range f";
  proof;
    assume "??S : range f";
    then; show False;
    proof;
      fix y; 
      assume "??S = f y";
      then; show ??thesis;
      proof (rule equalityCE);
        assume y_in_S: "y : ??S";
        assume y_in_fy: "y : f y";
        from y_in_S; have y_notin_fy: "y ~: f y"; ..;
        from y_notin_fy y_in_fy; show ??thesis; by contradiction;
      next;
        assume y_notin_S: "y ~: ??S";
        assume y_notin_fy: "y ~: f y";
        from y_notin_S; have y_in_fy: "y : f y"; ..;
        from y_notin_fy y_in_fy; show ??thesis; by contradiction;
      qed;
    qed;
  qed;
qed;


text {*
  The following version essentially does the same reasoning, only that
  it is expressed more neatly, with some derived Isar language
  elements involved.
*};

theorem "EX S. S ~: range(f :: 'a => 'a set)";
proof;
  let ??S = "{x. x ~: f x}";
  show "??S ~: range f";
  proof;
    assume "??S : range f";
    thus False;
    proof;
      fix y; 
      assume "??S = f y";
      thus ??thesis;
      proof (rule equalityCE);
        assume "y : f y";
        assume "y : ??S"; hence "y ~: f y"; ..;
        thus ??thesis; by contradiction;
      next;
        assume "y ~: f y";
        assume "y ~: ??S"; hence "y : f y"; ..;
        thus ??thesis; by contradiction;
      qed;
    qed;
  qed;
qed;


text {*
  How much creativity is required?  As it happens, Isabelle can prove
  this theorem automatically.  The default classical set contains
  rules for most of the constructs of HOL's set theory.  We must
  augment it with @{thm equalityCE} to break up set equalities, and
  then apply best-first search.  Depth-first search would diverge, but
  best-first search successfully navigates through the large search
  space.
*};

theorem "EX S. S ~: range(f :: 'a => 'a set)";
  by (best elim: equalityCE);

text {*
  While this establishes the same theorem internally, we do not get
  any idea of how the proof actually works.  There is currently no way
  to transform internal system-level representations of Isabelle
  proofs back into Isar documents.  Writing Isabelle/Isar proof
  documents actually \emph{is} a creative process.
*};


end;
