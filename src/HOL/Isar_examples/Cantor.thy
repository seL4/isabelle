(*  Title:      HOL/Isar_examples/Cantor.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Cantor's theorem (see also 'Isabelle's Object-Logics').
*)

theory Cantor = Main:;


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
        from y_notin_fy y_in_fy; show ??thesis; ..;
      next;
        assume y_notin_S: "y ~: ??S";
        assume y_notin_fy: "y ~: f y";
        from y_notin_S; have y_in_fy: "y : f y"; ..;
        from y_notin_fy y_in_fy; show ??thesis; ..;
      qed;
    qed;
  qed;
qed;


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
        assume "y : ??S"; then; have y_notin_fy: "y ~: f y"; ..;
        assume "y : f y";
        from y_notin_fy it; show ??thesis; ..;
      next;
        assume "y ~: ??S"; then; have y_in_fy: "y : f y"; ..;
        assume "y ~: f y";
        from it y_in_fy; show ??thesis; ..;
      qed;
    qed;
  qed;
qed;


theorem "EX S. S ~: range(f :: 'a => 'a set)";
  by (best elim: equalityCE);


end;
