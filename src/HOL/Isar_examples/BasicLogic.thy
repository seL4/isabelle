(*  Title:      HOL/Isar_examples/BasicLogic.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Basic propositional and quantifier reasoning.
*)

header {* Basic reasoning *};

theory BasicLogic = Main:;

subsection {* Some trivialities *};

text {* Just a few toy examples to get an idea of how Isabelle/Isar
  proof documents may look like. *};

lemma I: "A --> A";
proof;
  assume A;
  show A; .;
qed;

lemma K: "A --> B --> A";
proof;
  assume A;
  show "B --> A";
  proof;
    show A; .;
  qed;
qed;

lemma K': "A --> B --> A";
proof;
  assume A;
  thus "B --> A"; ..;
qed;

lemma K'': "A --> B --> A";
proof intro;
  assume A;
  show A; .;
qed;

lemma K''': "A --> B --> A";
  by intro;

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

text {* Variations of backward vs.\ forward reasoning \dots *};

lemma "A & B --> B & A";
proof;
  assume "A & B";
  show "B & A";
  proof;
    show B; by (rule conjunct2);
    show A; by (rule conjunct1);
  qed;
qed;

lemma "A & B --> B & A";
proof;
  assume "A & B";
  then; show "B & A";
  proof;
    assume A B;
    show ?thesis; ..;
  qed;
qed;

lemma "A & B --> B & A";
proof;
  assume "A & B";
  show "B & A";
  proof;
    from prems; show B; ..;
    from prems; show A; ..;
  qed;
qed;

lemma "A & B --> B & A";
proof;
  assume ab: "A & B";
  from ab; have a: A; ..;
  from ab; have b: B; ..;
  from b a; show "B & A"; ..;
qed;


subsection {* A few examples from ``Introduction to Isabelle'' *};

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
