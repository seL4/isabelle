(*  Title:      HOL/Isar_examples/Peirce.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Examples of classical proof: Peirce's Law *};

theory Peirce = Main:;

theorem "((A --> B) --> A) --> A";
proof;
  assume aba: "(A --> B) --> A";
  show A;
  proof (rule classical);
    assume "~ A";
    have "A --> B";
    proof;
      assume A;
      thus B; by contradiction;
    qed;
    with aba; show A; ..;
  qed;
qed;

theorem "((A --> B) --> A) --> A";
proof;
  assume aba: "(A --> B) --> A";
  show A;
  proof (rule classical);
    presume "A --> B";
    with aba; show A; ..;
  next;
    assume not_a: "~ A";
    show "A --> B";
    proof;
      assume A;
      with not_a; show B; ..;
    qed;
  qed;
qed;

end;
