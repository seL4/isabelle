(*  Title:      HOL/Isar_examples/BasicLogic.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Basic propositional and quantifier reasoning.
*)

theory BasicLogic = Main:;


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
proof single*;
  assume A;
  show A; .;
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
    show ??thesis; ..;
  qed;
qed;

lemma "A & B --> B & A";
proof;
  assume ab: "A & B";
  from ab; have a: A; ..;
  from ab; have b: B; ..;
  from b a; show "B & A"; ..;
qed;


text {* propositional proof (from 'Introduction to Isabelle') *};

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


text {* quantifier proof (from 'Introduction to Isabelle') *};

lemma "(EX x. P(f(x))) --> (EX x. P(x))";
proof;
  assume "EX x. P(f(x))";
  then; show "EX x. P(x)";
  proof (rule exE);
    fix a;
    assume "P(f(a))" (is "P(??witness)");
    show ??thesis; by (rule exI [of P ??witness]);
  qed;
qed;

lemma "(EX x. P(f(x))) --> (EX x. P(x))";
proof;
  assume "EX x. P(f(x))";
  then; show "EX x. P(x)";
  proof;
    fix a;
    assume "P(f(a))";
    show ??thesis; ..;
  qed;
qed;

lemma "(EX x. P(f(x))) --> (EX x. P(x))";
  by blast;


end;
