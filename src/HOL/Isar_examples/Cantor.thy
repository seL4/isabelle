(*  Title:      HOL/Isar_examples/Cantor.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Cantor's theorem (see also 'Isabelle's Object-Logics').
*)

theory Cantor = Main:;

theorem cantor: "EX S. S ~: range(f :: 'a => 'a set)";
by (best elim: equalityCE);

end;
