(*  Title:      LK/ex/prop
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Classical sequent calculus: examples with propositional connectives
Can be read to test the LK system.
*)

writeln"absorptive laws of & and | ";

goal (theory "LK") "|- P & P <-> P";
by (fast_tac prop_pack 1);
result();

goal (theory "LK") "|- P | P <-> P";
by (fast_tac prop_pack 1);
result();

writeln"commutative laws of & and | ";

goal (theory "LK") "|- P & Q  <->  Q & P";
by (fast_tac prop_pack 1);
result();

goal (theory "LK") "|- P | Q  <->  Q | P";
by (fast_tac prop_pack 1);
result();


writeln"associative laws of & and | ";

goal (theory "LK") "|- (P & Q) & R  <->  P & (Q & R)";
by (fast_tac prop_pack 1);
result();

goal (theory "LK") "|- (P | Q) | R  <->  P | (Q | R)";
by (fast_tac prop_pack 1);
result();

writeln"distributive laws of & and | ";
goal (theory "LK") "|- (P & Q) | R  <-> (P | R) & (Q | R)";
by (fast_tac prop_pack 1);
result();

goal (theory "LK") "|- (P | Q) & R  <-> (P & R) | (Q & R)";
by (fast_tac prop_pack 1);
result();

writeln"Laws involving implication";

goal (theory "LK") "|- (P|Q --> R) <-> (P-->R) & (Q-->R)";
by (fast_tac prop_pack 1);
result(); 

goal (theory "LK") "|- (P & Q --> R) <-> (P--> (Q-->R))";
by (fast_tac prop_pack 1);
result(); 


goal (theory "LK") "|- (P --> Q & R) <-> (P-->Q)  &  (P-->R)";
by (fast_tac prop_pack 1);
result();


writeln"Classical theorems";

goal (theory "LK") "|- P|Q --> P| ~P&Q";
by (fast_tac prop_pack 1);
result();


goal (theory "LK") "|- (P-->Q)&(~P-->R)  -->  (P&Q | R)";
by (fast_tac prop_pack 1);
result();


goal (theory "LK") "|- P&Q | ~P&R  <->  (P-->Q)&(~P-->R)";
by (fast_tac prop_pack 1);
result();


goal (theory "LK") "|- (P-->Q) | (P-->R)  <->  (P --> Q | R)";
by (fast_tac prop_pack 1);
result();


(*If and only if*)

goal (theory "LK") "|- (P<->Q) <-> (Q<->P)";
by (fast_tac prop_pack 1);
result();

goal (theory "LK") "|- ~ (P <-> ~P)";
by (fast_tac prop_pack 1);
result();


(*Sample problems from 
  F. J. Pelletier, 
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.
*)

(*1*)
goal (theory "LK") "|- (P-->Q)  <->  (~Q --> ~P)";
by (fast_tac prop_pack 1);
result();

(*2*)
goal (theory "LK") "|- ~ ~ P  <->  P";
by (fast_tac prop_pack 1);
result();

(*3*)
goal (theory "LK") "|- ~(P-->Q) --> (Q-->P)";
by (fast_tac prop_pack 1);
result();

(*4*)
goal (theory "LK") "|- (~P-->Q)  <->  (~Q --> P)";
by (fast_tac prop_pack 1);
result();

(*5*)
goal (theory "LK") "|- ((P|Q)-->(P|R)) --> (P|(Q-->R))";
by (fast_tac prop_pack 1);
result();

(*6*)
goal (theory "LK") "|- P | ~ P";
by (fast_tac prop_pack 1);
result();

(*7*)
goal (theory "LK") "|- P | ~ ~ ~ P";
by (fast_tac prop_pack 1);
result();

(*8.  Peirce's law*)
goal (theory "LK") "|- ((P-->Q) --> P)  -->  P";
by (fast_tac prop_pack 1);
result();

(*9*)
goal (theory "LK") "|- ((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (fast_tac prop_pack 1);
result();

(*10*)
goal (theory "LK") "Q-->R, R-->P&Q, P-->(Q|R) |- P<->Q";
by (fast_tac prop_pack 1);
result();

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
goal (theory "LK") "|- P<->P";
by (fast_tac prop_pack 1);
result();

(*12.  "Dijkstra's law"*)
goal (theory "LK") "|- ((P <-> Q) <-> R)  <->  (P <-> (Q <-> R))";
by (fast_tac prop_pack 1);
result();

(*13.  Distributive law*)
goal (theory "LK") "|- P | (Q & R)  <-> (P | Q) & (P | R)";
by (fast_tac prop_pack 1);
result();

(*14*)
goal (theory "LK") "|- (P <-> Q) <-> ((Q | ~P) & (~Q|P))";
by (fast_tac prop_pack 1);
result();


(*15*)
goal (theory "LK") "|- (P --> Q) <-> (~P | Q)";
by (fast_tac prop_pack 1);
result();

(*16*)
goal (theory "LK") "|- (P-->Q) | (Q-->P)";
by (fast_tac prop_pack 1);
result();

(*17*)
goal (theory "LK") "|- ((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S))";
by (fast_tac prop_pack 1);
result();
