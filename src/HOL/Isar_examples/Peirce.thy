(*  Title:      HOL/Isar_examples/Peirce.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

theory Peirce = Main:;

text {* Peirce's law: examples of classical proof. *};

theorem "((A --> B) --> A) --> A";
proof;
  assume aba: "(A --> B) --> A";
  show A;
  proof (rule classical);
    assume not_a: "~ A";

    have ab: "A --> B";
    proof;
      assume a: A;
      from not_a a; show B; ..;
    qed;

    from aba ab; show A; ..;
  qed;
qed;


theorem "((A --> B) --> A) --> A";
proof;
  assume aba: "(A --> B) --> A";
  show A;
  proof (rule classical);
    presume ab: "A --> B";
    from aba ab; show A; ..;
  next;
    assume not_a: "~ A";
    show "A --> B";
    proof;
      assume a: A;
      from not_a a; show B; ..;
    qed;
  qed;
qed;


end;
