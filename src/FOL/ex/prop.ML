(*  Title: 	FOL/ex/prop
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

First-Order Logic: propositional examples (intuitionistic and classical)
Needs declarations of the theory "thy" and the tactic "tac"
*)

writeln"File FOL/ex/prop.";


writeln"commutative laws of & and | ";
goal thy "P & Q  -->  Q & P";
by tac;
result();

goal thy "P | Q  -->  Q | P";
by tac;
result();


writeln"associative laws of & and | ";
goal thy "(P & Q) & R  -->  P & (Q & R)";
by tac;
result();

goal thy "(P | Q) | R  -->  P | (Q | R)";
by tac;
result();



writeln"distributive laws of & and | ";
goal thy "(P & Q) | R  --> (P | R) & (Q | R)";
by tac;
result();

goal thy "(P | R) & (Q | R)  --> (P & Q) | R";
by tac;
result();

goal thy "(P | Q) & R  --> (P & R) | (Q & R)";
by tac;
result();


goal thy "(P & R) | (Q & R)  --> (P | Q) & R";
by tac;
result();


writeln"Laws involving implication";

goal thy "(P-->R) & (Q-->R) <-> (P|Q --> R)";
by tac;
result();


goal thy "(P & Q --> R) <-> (P--> (Q-->R))";
by tac;
result();


goal thy "((P-->R)-->R) --> ((Q-->R)-->R) --> (P&Q-->R) --> R";
by tac;
result();

goal thy "~(P-->R) --> ~(Q-->R) --> ~(P&Q-->R)";
by tac;
result();

goal thy "(P --> Q & R) <-> (P-->Q)  &  (P-->R)";
by tac;
result();


writeln"Propositions-as-types";

(*The combinator K*)
goal thy "P --> (Q --> P)";
by tac;
result();

(*The combinator S*)
goal thy "(P-->Q-->R)  --> (P-->Q) --> (P-->R)";
by tac;
result();


(*Converse is classical*)
goal thy "(P-->Q) | (P-->R)  -->  (P --> Q | R)";
by tac;
result();

goal thy "(P-->Q)  -->  (~Q --> ~P)";
by tac;
result();


writeln"Schwichtenberg's examples (via T. Nipkow)";

(* stab-imp *)
goal thy "(((Q-->R)-->R)-->Q) --> (((P-->Q)-->R)-->R)-->P-->Q";
by tac;
result();

(* stab-to-peirce *)
goal thy "(((P --> R) --> R) --> P) --> (((Q --> R) --> R) --> Q) \
\	      --> ((P --> Q) --> P) --> P";
by tac;
result();

(* peirce-imp1 *)
goal thy "(((Q --> R) --> Q) --> Q) \
\	       --> (((P --> Q) --> R) --> P --> Q) --> P --> Q";
by tac;
result();
  
(* peirce-imp2 *)
goal thy "(((P --> R) --> P) --> P) --> ((P --> Q --> R) --> P) --> P";
by tac;
result();

(* mints  *)
goal thy "((((P --> Q) --> P) --> P) --> Q) --> Q";
by tac;
result();

(* mints-solovev *)
goal thy "(P --> (Q --> R) --> Q) --> ((P --> Q) --> R) --> R";
by tac;
result();

(* tatsuta *)
goal thy "(((P7 --> P1) --> P10) --> P4 --> P5) \
\	  --> (((P8 --> P2) --> P9) --> P3 --> P10) \
\	  --> (P1 --> P8) --> P6 --> P7 \
\	  --> (((P3 --> P2) --> P9) --> P4) \
\	  --> (P1 --> P3) --> (((P6 --> P1) --> P2) --> P9) --> P5";
by tac;
result();

(* tatsuta1 *)
goal thy "(((P8 --> P2) --> P9) --> P3 --> P10) \
\    --> (((P3 --> P2) --> P9) --> P4) \
\    --> (((P6 --> P1) --> P2) --> P9) \
\    --> (((P7 --> P1) --> P10) --> P4 --> P5) \
\    --> (P1 --> P3) --> (P1 --> P8) --> P6 --> P7 --> P5";
by tac;
result();

writeln"Reached end of file.";
