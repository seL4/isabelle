(*  Title:      FOLP/ex/prop.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

First-Order Logic: propositional examples (intuitionistic and classical)
Needs declarations of the theory "thy" and the tactic "tac"
*)

writeln"commutative laws of & and | ";
Goal "?p : P & Q  -->  Q & P";
by tac;
result();

Goal "?p : P | Q  -->  Q | P";
by tac;
result();


writeln"associative laws of & and | ";
Goal "?p : (P & Q) & R  -->  P & (Q & R)";
by tac;
result();

Goal "?p : (P | Q) | R  -->  P | (Q | R)";
by tac;
result();



writeln"distributive laws of & and | ";
Goal "?p : (P & Q) | R  --> (P | R) & (Q | R)";
by tac;
result();

Goal "?p : (P | R) & (Q | R)  --> (P & Q) | R";
by tac;
result();

Goal "?p : (P | Q) & R  --> (P & R) | (Q & R)";
by tac;
result();


Goal "?p : (P & R) | (Q & R)  --> (P | Q) & R";
by tac;
result();


writeln"Laws involving implication";

Goal "?p : (P-->R) & (Q-->R) <-> (P|Q --> R)";
by tac;
result();


Goal "?p : (P & Q --> R) <-> (P--> (Q-->R))";
by tac;
result();


Goal "?p : ((P-->R)-->R) --> ((Q-->R)-->R) --> (P&Q-->R) --> R";
by tac;
result();

Goal "?p : ~(P-->R) --> ~(Q-->R) --> ~(P&Q-->R)";
by tac;
result();

Goal "?p : (P --> Q & R) <-> (P-->Q)  &  (P-->R)";
by tac;
result();


writeln"Propositions-as-types";

(*The combinator K*)
Goal "?p : P --> (Q --> P)";
by tac;
result();

(*The combinator S*)
Goal "?p : (P-->Q-->R)  --> (P-->Q) --> (P-->R)";
by tac;
result();


(*Converse is classical*)
Goal "?p : (P-->Q) | (P-->R)  -->  (P --> Q | R)";
by tac;
result();

Goal "?p : (P-->Q)  -->  (~Q --> ~P)";
by tac;
result();


writeln"Schwichtenberg's examples (via T. Nipkow)";

(* stab-imp *)
Goal "?p : (((Q-->R)-->R)-->Q) --> (((P-->Q)-->R)-->R)-->P-->Q";
by tac;
result();

(* stab-to-peirce *)
Goal "?p : (((P --> R) --> R) --> P) --> (((Q --> R) --> R) --> Q) \
\             --> ((P --> Q) --> P) --> P";
by tac;
result();

(* peirce-imp1 *)
Goal "?p : (((Q --> R) --> Q) --> Q) \
\              --> (((P --> Q) --> R) --> P --> Q) --> P --> Q";
by tac;
result();
  
(* peirce-imp2 *)
Goal "?p : (((P --> R) --> P) --> P) --> ((P --> Q --> R) --> P) --> P";
by tac;
result();

(* mints  *)
Goal "?p : ((((P --> Q) --> P) --> P) --> Q) --> Q";
by tac;
result();

(* mints-solovev *)
Goal "?p : (P --> (Q --> R) --> Q) --> ((P --> Q) --> R) --> R";
by tac;
result();

(* tatsuta *)
Goal "?p : (((P7 --> P1) --> P10) --> P4 --> P5) \
\         --> (((P8 --> P2) --> P9) --> P3 --> P10) \
\         --> (P1 --> P8) --> P6 --> P7 \
\         --> (((P3 --> P2) --> P9) --> P4) \
\         --> (P1 --> P3) --> (((P6 --> P1) --> P2) --> P9) --> P5";
by tac;
result();

(* tatsuta1 *)
Goal "?p : (((P8 --> P2) --> P9) --> P3 --> P10) \
\    --> (((P3 --> P2) --> P9) --> P4) \
\    --> (((P6 --> P1) --> P2) --> P9) \
\    --> (((P7 --> P1) --> P10) --> P4 --> P5) \
\    --> (P1 --> P3) --> (P1 --> P8) --> P6 --> P7 --> P5";
by tac;
result();
