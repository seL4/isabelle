(*  Title:      Modal/S4.thy
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

theory S4
imports Modal0
begin

axioms
(* Definition of the star operation using a set of Horn clauses *)
(* For system S4:  gamma * == {[]P | []P : gamma}               *)
(*                 delta * == {<>P | <>P : delta}               *)

  lstar0:         "|L>"
  lstar1:         "$G |L> $H ==> []P, $G |L> []P, $H"
  lstar2:         "$G |L> $H ==>   P, $G |L>      $H"
  rstar0:         "|R>"
  rstar1:         "$G |R> $H ==> <>P, $G |R> <>P, $H"
  rstar2:         "$G |R> $H ==>   P, $G |R>      $H"

(* Rules for [] and <> *)

  boxR:
   "[| $E |L> $E';  $F |R> $F';  $G |R> $G';
           $E'         |- $F', P, $G'|] ==> $E          |- $F, []P, $G"
  boxL:     "$E,P,$F,[]P |-         $G    ==> $E, []P, $F |-          $G"

  diaR:     "$E          |- $F,P,$G,<>P   ==> $E          |- $F, <>P, $G"
  diaL:
   "[| $E |L> $E';  $F |L> $F';  $G |R> $G';
           $E', P, $F' |-         $G'|] ==> $E, <>P, $F |- $G"

ML {*
structure S4_Prover = Modal_ProverFun
(
  val rewrite_rls = thms "rewrite_rls"
  val safe_rls = thms "safe_rls"
  val unsafe_rls = thms "unsafe_rls" @ [thm "boxR", thm "diaL"]
  val bound_rls = thms "bound_rls" @ [thm "boxL", thm "diaR"]
  val aside_rls = [thm "lstar0", thm "lstar1", thm "lstar2", thm "rstar0",
    thm "rstar1", thm "rstar2"]
)
*}

method_setup S4_solve =
  {* Scan.succeed (K (SIMPLE_METHOD (S4_Prover.solve_tac 2))) *} "S4 solver"


(* Theorems of system T from Hughes and Cresswell and Hailpern, LNCS 129 *)

lemma "|- []P --> P" by S4_solve
lemma "|- [](P-->Q) --> ([]P-->[]Q)" by S4_solve   (* normality*)
lemma "|- (P--<Q) --> []P --> []Q" by S4_solve
lemma "|- P --> <>P" by S4_solve

lemma "|-  [](P & Q) <-> []P & []Q" by S4_solve
lemma "|-  <>(P | Q) <-> <>P | <>Q" by S4_solve
lemma "|-  [](P<->Q) <-> (P>-<Q)" by S4_solve
lemma "|-  <>(P-->Q) <-> ([]P--><>Q)" by S4_solve
lemma "|-        []P <-> ~<>(~P)" by S4_solve
lemma "|-     [](~P) <-> ~<>P" by S4_solve
lemma "|-       ~[]P <-> <>(~P)" by S4_solve
lemma "|-      [][]P <-> ~<><>(~P)" by S4_solve
lemma "|- ~<>(P | Q) <-> ~<>P & ~<>Q" by S4_solve

lemma "|- []P | []Q --> [](P | Q)" by S4_solve
lemma "|- <>(P & Q) --> <>P & <>Q" by S4_solve
lemma "|- [](P | Q) --> []P | <>Q" by S4_solve
lemma "|- <>P & []Q --> <>(P & Q)" by S4_solve
lemma "|- [](P | Q) --> <>P | []Q" by S4_solve
lemma "|- <>(P-->(Q & R)) --> ([]P --> <>Q) & ([]P--><>R)" by S4_solve
lemma "|- (P--<Q) & (Q--<R) --> (P--<R)" by S4_solve
lemma "|- []P --> <>Q --> <>(P & Q)" by S4_solve


(* Theorems of system S4 from Hughes and Cresswell, p.46 *)

lemma "|- []A --> A" by S4_solve             (* refexivity *)
lemma "|- []A --> [][]A" by S4_solve         (* transitivity *)
lemma "|- []A --> <>A" by S4_solve           (* seriality *)
lemma "|- <>[](<>A --> []<>A)" by S4_solve
lemma "|- <>[](<>[]A --> []A)" by S4_solve
lemma "|- []P <-> [][]P" by S4_solve
lemma "|- <>P <-> <><>P" by S4_solve
lemma "|- <>[]<>P --> <>P" by S4_solve
lemma "|- []<>P <-> []<>[]<>P" by S4_solve
lemma "|- <>[]P <-> <>[]<>[]P" by S4_solve

(* Theorems for system S4 from Hughes and Cresswell, p.60 *)

lemma "|- []P | []Q <-> []([]P | []Q)" by S4_solve
lemma "|- ((P>-<Q) --< R) --> ((P>-<Q) --< []R)" by S4_solve

(* These are from Hailpern, LNCS 129 *)

lemma "|- [](P & Q) <-> []P & []Q" by S4_solve
lemma "|- <>(P | Q) <-> <>P | <>Q" by S4_solve
lemma "|- <>(P --> Q) <-> ([]P --> <>Q)" by S4_solve

lemma "|- [](P --> Q) --> (<>P --> <>Q)" by S4_solve
lemma "|- []P --> []<>P" by S4_solve
lemma "|- <>[]P --> <>P" by S4_solve

lemma "|- []P | []Q --> [](P | Q)" by S4_solve
lemma "|- <>(P & Q) --> <>P & <>Q" by S4_solve
lemma "|- [](P | Q) --> []P | <>Q" by S4_solve
lemma "|- <>P & []Q --> <>(P & Q)" by S4_solve
lemma "|- [](P | Q) --> <>P | []Q" by S4_solve

end
