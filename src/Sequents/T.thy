(*  Title:      Sequents/T.thy
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

theory T
imports Modal0
begin

axiomatization where
(* Definition of the star operation using a set of Horn clauses *)
(* For system T:  gamma * == {P | []P : gamma}                  *)
(*                delta * == {P | <>P : delta}                  *)

  lstar0:         "|L>" and
  lstar1:         "$G |L> $H ==> []P, $G |L> P, $H" and
  lstar2:         "$G |L> $H ==>   P, $G |L>    $H" and
  rstar0:         "|R>" and
  rstar1:         "$G |R> $H ==> <>P, $G |R> P, $H" and
  rstar2:         "$G |R> $H ==>   P, $G |R>    $H" and

(* Rules for [] and <> *)

  boxR:
   "[| $E |L> $E';  $F |R> $F';  $G |R> $G';
               $E'        |- $F', P, $G'|] ==> $E          |- $F, []P, $G" and
  boxL:     "$E, P, $F  |-         $G    ==> $E, []P, $F |-          $G" and
  diaR:     "$E         |- $F, P,  $G    ==> $E          |- $F, <>P, $G" and
  diaL:
   "[| $E |L> $E';  $F |L> $F';  $G |R> $G';
               $E', P, $F'|-         $G'|] ==> $E, <>P, $F |-          $G"

ML {*
structure T_Prover = Modal_ProverFun
(
  val rewrite_rls = @{thms rewrite_rls}
  val safe_rls = @{thms safe_rls}
  val unsafe_rls = @{thms unsafe_rls} @ [@{thm boxR}, @{thm diaL}]
  val bound_rls = @{thms bound_rls} @ [@{thm boxL}, @{thm diaR}]
  val aside_rls = [@{thm lstar0}, @{thm lstar1}, @{thm lstar2}, @{thm rstar0},
    @{thm rstar1}, @{thm rstar2}]
)
*}

method_setup T_solve = {* Scan.succeed (fn ctxt => SIMPLE_METHOD (T_Prover.solve_tac ctxt 2)) *}


(* Theorems of system T from Hughes and Cresswell and Hailpern, LNCS 129 *)

lemma "|- []P --> P" by T_solve
lemma "|- [](P-->Q) --> ([]P-->[]Q)" by T_solve   (* normality*)
lemma "|- (P--<Q) --> []P --> []Q" by T_solve
lemma "|- P --> <>P" by T_solve

lemma "|-  [](P & Q) <-> []P & []Q" by T_solve
lemma "|-  <>(P | Q) <-> <>P | <>Q" by T_solve
lemma "|-  [](P<->Q) <-> (P>-<Q)" by T_solve
lemma "|-  <>(P-->Q) <-> ([]P--><>Q)" by T_solve
lemma "|-        []P <-> ~<>(~P)" by T_solve
lemma "|-     [](~P) <-> ~<>P" by T_solve
lemma "|-       ~[]P <-> <>(~P)" by T_solve
lemma "|-      [][]P <-> ~<><>(~P)" by T_solve
lemma "|- ~<>(P | Q) <-> ~<>P & ~<>Q" by T_solve

lemma "|- []P | []Q --> [](P | Q)" by T_solve
lemma "|- <>(P & Q) --> <>P & <>Q" by T_solve
lemma "|- [](P | Q) --> []P | <>Q" by T_solve
lemma "|- <>P & []Q --> <>(P & Q)" by T_solve
lemma "|- [](P | Q) --> <>P | []Q" by T_solve
lemma "|- <>(P-->(Q & R)) --> ([]P --> <>Q) & ([]P--><>R)" by T_solve
lemma "|- (P--<Q) & (Q--<R) --> (P--<R)" by T_solve
lemma "|- []P --> <>Q --> <>(P & Q)" by T_solve

end
