(*  Title:      HOL/Isar_examples/Peirce.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Peirce's law: examples of classical proof.
*)

theory Peirce = Main:;


theorem "((A --> B) --> A) --> A";
proof;
  assume ABA: "(A --> B) --> A";
  show A;
  proof (rule classical);
    assume notA: "~ A";

    have AB: "A --> B";
    proof;
      assume A: A;
      from notA A; show B; ..;
    qed;

    from ABA AB; show A; ..;
  qed;
qed;


theorem "((A --> B) --> A) --> A";
proof;
  assume ABA: "(A --> B) --> A";
  show A;
  proof (rule classical);

    assume AB: "A --> B";
    from ABA AB; show A; ..;

    next;
    assume notA: "~ A";
    show "A --> B";
    proof;
      assume A: A;
      from notA A; show B; ..;
    qed;
  qed;
qed;


end;
