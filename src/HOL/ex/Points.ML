(*  Title:      HOL/ex/Points.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen

Basic use of extensible records in HOL, including the famous points
and coloured points.

Note: any of these goals may be solved at a stroke by Auto_tac or Force_tac
*)


(* some basic simplifications *)

Goal "x (| x = m, y = n, ... = p |) = m";
by (Simp_tac 1);
result();

Goal "(| x = m, y = n, ... = p |) (| x:= 0 |) = (| x = 0, y = n, ... = p |)";
by (Simp_tac 1);
result();


(* splitting quantifiers: the !!r is NECESSARY *)

Goal "!!r. r (| x := n |) (| y := m |) = r (| y := m |) (| x := n |)";
by (record_split_tac 1);
by (Simp_tac 1);
result();

Goal "!!r. r (| x := n |) (| x := m |) = r (| x := m |)";
by (record_split_tac 1);
by (Simp_tac 1);
result();


(* record equality *)

Goal "(| x = n, y = p |) = (| x = n', y = p' |) & n = 0 ==> n' = 0";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
result();

Goalw [getX_def, setX_def, incX_def] "!!r n. incX r = setX r (Suc (getX r))";
by (record_split_tac 1);
by (Simp_tac 1);
result();
