(*  Title:      LK/Propositional.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Classical sequent calculus: examples with propositional connectives *}

theory Propositional
imports LK
begin

text "absorptive laws of & and | "

lemma "|- P & P <-> P"
  by fast_prop

lemma "|- P | P <-> P"
  by fast_prop


text "commutative laws of & and | "

lemma "|- P & Q  <->  Q & P"
  by fast_prop

lemma "|- P | Q  <->  Q | P"
  by fast_prop


text "associative laws of & and | "

lemma "|- (P & Q) & R  <->  P & (Q & R)"
  by fast_prop

lemma "|- (P | Q) | R  <->  P | (Q | R)"
  by fast_prop


text "distributive laws of & and | "

lemma "|- (P & Q) | R  <-> (P | R) & (Q | R)"
  by fast_prop

lemma "|- (P | Q) & R  <-> (P & R) | (Q & R)"
  by fast_prop


text "Laws involving implication"

lemma "|- (P|Q --> R) <-> (P-->R) & (Q-->R)"
  by fast_prop

lemma "|- (P & Q --> R) <-> (P--> (Q-->R))"
  by fast_prop

lemma "|- (P --> Q & R) <-> (P-->Q)  &  (P-->R)"
  by fast_prop


text "Classical theorems"

lemma "|- P|Q --> P| ~P&Q"
  by fast_prop

lemma "|- (P-->Q)&(~P-->R)  -->  (P&Q | R)"
  by fast_prop

lemma "|- P&Q | ~P&R  <->  (P-->Q)&(~P-->R)"
  by fast_prop

lemma "|- (P-->Q) | (P-->R)  <->  (P --> Q | R)"
  by fast_prop


(*If and only if*)

lemma "|- (P<->Q) <-> (Q<->P)"
  by fast_prop

lemma "|- ~ (P <-> ~P)"
  by fast_prop


(*Sample problems from 
  F. J. Pelletier, 
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.
*)

(*1*)
lemma "|- (P-->Q)  <->  (~Q --> ~P)"
  by fast_prop

(*2*)
lemma "|- ~ ~ P  <->  P"
  by fast_prop

(*3*)
lemma "|- ~(P-->Q) --> (Q-->P)"
  by fast_prop

(*4*)
lemma "|- (~P-->Q)  <->  (~Q --> P)"
  by fast_prop

(*5*)
lemma "|- ((P|Q)-->(P|R)) --> (P|(Q-->R))"
  by fast_prop

(*6*)
lemma "|- P | ~ P"
  by fast_prop

(*7*)
lemma "|- P | ~ ~ ~ P"
  by fast_prop

(*8.  Peirce's law*)
lemma "|- ((P-->Q) --> P)  -->  P"
  by fast_prop

(*9*)
lemma "|- ((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
  by fast_prop

(*10*)
lemma "Q-->R, R-->P&Q, P-->(Q|R) |- P<->Q"
  by fast_prop

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
lemma "|- P<->P"
  by fast_prop

(*12.  "Dijkstra's law"*)
lemma "|- ((P <-> Q) <-> R)  <->  (P <-> (Q <-> R))"
  by fast_prop

(*13.  Distributive law*)
lemma "|- P | (Q & R)  <-> (P | Q) & (P | R)"
  by fast_prop

(*14*)
lemma "|- (P <-> Q) <-> ((Q | ~P) & (~Q|P))"
  by fast_prop

(*15*)
lemma "|- (P --> Q) <-> (~P | Q)"
  by fast_prop

(*16*)
lemma "|- (P-->Q) | (Q-->P)"
  by fast_prop

(*17*)
lemma "|- ((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S))"
  by fast_prop

end
