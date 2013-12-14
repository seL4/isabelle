(*  Title:      Sequents/S43.thy
    Author:     Martin Coen
    Copyright   1991  University of Cambridge

This implements Rajeev Gore's sequent calculus for S43.
*)

theory S43
imports Modal0
begin

consts
  S43pi :: "[seq'=>seq', seq'=>seq', seq'=>seq',
             seq'=>seq', seq'=>seq', seq'=>seq'] => prop"
syntax
  "_S43pi" :: "[seq, seq, seq, seq, seq, seq] => prop"
                         ("S43pi((_);(_);(_);(_);(_);(_))" [] 5)

parse_translation {*
  let
    val tr  = seq_tr;
    fun s43pi_tr [s1, s2, s3, s4, s5, s6] =
      Const (@{const_syntax S43pi}, dummyT) $ tr s1 $ tr s2 $ tr s3 $ tr s4 $ tr s5 $ tr s6;
  in [(@{syntax_const "_S43pi"}, K s43pi_tr)] end
*}

print_translation {*
let
  val tr' = seq_tr';
  fun s43pi_tr' [s1, s2, s3, s4, s5, s6] =
    Const(@{syntax_const "_S43pi"}, dummyT) $ tr' s1 $ tr' s2 $ tr' s3 $ tr' s4 $ tr' s5 $ tr' s6;
in [(@{const_syntax S43pi}, K s43pi_tr')] end
*}

axiomatization where
(* Definition of the star operation using a set of Horn clauses  *)
(* For system S43: gamma * == {[]P | []P : gamma}                *)
(*                 delta * == {<>P | <>P : delta}                *)

  lstar0:         "|L>" and
  lstar1:         "$G |L> $H ==> []P, $G |L> []P, $H" and
  lstar2:         "$G |L> $H ==>   P, $G |L>      $H" and
  rstar0:         "|R>" and
  rstar1:         "$G |R> $H ==> <>P, $G |R> <>P, $H" and
  rstar2:         "$G |R> $H ==>   P, $G |R>      $H" and

(* Set of Horn clauses to generate the antecedents for the S43 pi rule       *)
(* ie                                                                        *)
(*           S1...Sk,Sk+1...Sk+m                                             *)
(*     ----------------------------------                                    *)
(*     <>P1...<>Pk, $G |- $H, []Q1...[]Qm                                    *)
(*                                                                           *)
(*  where Si == <>P1...<>Pi-1,<>Pi+1,..<>Pk,Pi, $G * |- $H *, []Q1...[]Qm    *)
(*    and Sj == <>P1...<>Pk, $G * |- $H *, []Q1...[]Qj-1,[]Qj+1...[]Qm,Qj    *)
(*    and 1<=i<=k and k<j<=k+m                                               *)

  S43pi0:         "S43pi $L;; $R;; $Lbox; $Rdia" and
  S43pi1:
   "[| (S43pi <>P,$L';     $L;; $R; $Lbox;$Rdia);   $L',P,$L,$Lbox |- $R,$Rdia |] ==>
       S43pi     $L'; <>P,$L;; $R; $Lbox;$Rdia" and
  S43pi2:
   "[| (S43pi $L';; []P,$R';     $R; $Lbox;$Rdia);  $L',$Lbox |- $R',P,$R,$Rdia |] ==>
       S43pi $L';;     $R'; []P,$R; $Lbox;$Rdia" and

(* Rules for [] and <> for S43 *)

  boxL:           "$E, P, $F, []P |- $G ==> $E, []P, $F |- $G" and
  diaR:           "$E |- $F, P, $G, <>P ==> $E |- $F, <>P, $G" and
  pi1:
   "[| $L1,<>P,$L2 |L> $Lbox;  $L1,<>P,$L2 |R> $Ldia;  $R |L> $Rbox;  $R |R> $Rdia;
      S43pi ; $Ldia;; $Rbox; $Lbox; $Rdia |] ==>
   $L1, <>P, $L2 |- $R" and
  pi2:
   "[| $L |L> $Lbox;  $L |R> $Ldia;  $R1,[]P,$R2 |L> $Rbox;  $R1,[]P,$R2 |R> $Rdia;
      S43pi ; $Ldia;; $Rbox; $Lbox; $Rdia |] ==>
   $L |- $R1, []P, $R2"


ML {*
structure S43_Prover = Modal_ProverFun
(
  val rewrite_rls = @{thms rewrite_rls}
  val safe_rls = @{thms safe_rls}
  val unsafe_rls = @{thms unsafe_rls} @ [@{thm pi1}, @{thm pi2}]
  val bound_rls = @{thms bound_rls} @ [@{thm boxL}, @{thm diaR}]
  val aside_rls = [@{thm lstar0}, @{thm lstar1}, @{thm lstar2}, @{thm rstar0},
    @{thm rstar1}, @{thm rstar2}, @{thm S43pi0}, @{thm S43pi1}, @{thm S43pi2}]
)
*}


method_setup S43_solve = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD
    (S43_Prover.solve_tac ctxt 2 ORELSE S43_Prover.solve_tac ctxt 3))
*}


(* Theorems of system T from Hughes and Cresswell and Hailpern, LNCS 129 *)

lemma "|- []P --> P" by S43_solve
lemma "|- [](P-->Q) --> ([]P-->[]Q)" by S43_solve   (* normality*)
lemma "|- (P--<Q) --> []P --> []Q" by S43_solve
lemma "|- P --> <>P" by S43_solve

lemma "|-  [](P & Q) <-> []P & []Q" by S43_solve
lemma "|-  <>(P | Q) <-> <>P | <>Q" by S43_solve
lemma "|-  [](P<->Q) <-> (P>-<Q)" by S43_solve
lemma "|-  <>(P-->Q) <-> ([]P--><>Q)" by S43_solve
lemma "|-        []P <-> ~<>(~P)" by S43_solve
lemma "|-     [](~P) <-> ~<>P" by S43_solve
lemma "|-       ~[]P <-> <>(~P)" by S43_solve
lemma "|-      [][]P <-> ~<><>(~P)" by S43_solve
lemma "|- ~<>(P | Q) <-> ~<>P & ~<>Q" by S43_solve

lemma "|- []P | []Q --> [](P | Q)" by S43_solve
lemma "|- <>(P & Q) --> <>P & <>Q" by S43_solve
lemma "|- [](P | Q) --> []P | <>Q" by S43_solve
lemma "|- <>P & []Q --> <>(P & Q)" by S43_solve
lemma "|- [](P | Q) --> <>P | []Q" by S43_solve
lemma "|- <>(P-->(Q & R)) --> ([]P --> <>Q) & ([]P--><>R)" by S43_solve
lemma "|- (P--<Q) & (Q--<R) --> (P--<R)" by S43_solve
lemma "|- []P --> <>Q --> <>(P & Q)" by S43_solve


(* Theorems of system S4 from Hughes and Cresswell, p.46 *)

lemma "|- []A --> A" by S43_solve             (* refexivity *)
lemma "|- []A --> [][]A" by S43_solve         (* transitivity *)
lemma "|- []A --> <>A" by S43_solve           (* seriality *)
lemma "|- <>[](<>A --> []<>A)" by S43_solve
lemma "|- <>[](<>[]A --> []A)" by S43_solve
lemma "|- []P <-> [][]P" by S43_solve
lemma "|- <>P <-> <><>P" by S43_solve
lemma "|- <>[]<>P --> <>P" by S43_solve
lemma "|- []<>P <-> []<>[]<>P" by S43_solve
lemma "|- <>[]P <-> <>[]<>[]P" by S43_solve

(* Theorems for system S4 from Hughes and Cresswell, p.60 *)

lemma "|- []P | []Q <-> []([]P | []Q)" by S43_solve
lemma "|- ((P>-<Q) --< R) --> ((P>-<Q) --< []R)" by S43_solve

(* These are from Hailpern, LNCS 129 *)

lemma "|- [](P & Q) <-> []P & []Q" by S43_solve
lemma "|- <>(P | Q) <-> <>P | <>Q" by S43_solve
lemma "|- <>(P --> Q) <-> ([]P --> <>Q)" by S43_solve

lemma "|- [](P --> Q) --> (<>P --> <>Q)" by S43_solve
lemma "|- []P --> []<>P" by S43_solve
lemma "|- <>[]P --> <>P" by S43_solve

lemma "|- []P | []Q --> [](P | Q)" by S43_solve
lemma "|- <>(P & Q) --> <>P & <>Q" by S43_solve
lemma "|- [](P | Q) --> []P | <>Q" by S43_solve
lemma "|- <>P & []Q --> <>(P & Q)" by S43_solve
lemma "|- [](P | Q) --> <>P | []Q" by S43_solve


(* Theorems of system S43 *)

lemma "|- <>[]P --> []<>P" by S43_solve
lemma "|- <>[]P --> [][]<>P" by S43_solve
lemma "|- [](<>P | <>Q) --> []<>P | []<>Q" by S43_solve
lemma "|- <>[]P & <>[]Q --> <>([]P & []Q)" by S43_solve
lemma "|- []([]P --> []Q) | []([]Q --> []P)" by S43_solve
lemma "|- [](<>P --> <>Q) | [](<>Q --> <>P)" by S43_solve
lemma "|- []([]P --> Q) | []([]Q --> P)" by S43_solve
lemma "|- [](P --> <>Q) | [](Q --> <>P)" by S43_solve
lemma "|- [](P --> []Q-->R) | [](P | ([]R --> Q))" by S43_solve
lemma "|- [](P | (Q --> <>C)) | [](P --> C --> <>Q)" by S43_solve
lemma "|- []([]P | Q) & [](P | []Q) --> []P | []Q" by S43_solve
lemma "|- <>P & <>Q --> <>(<>P & Q) | <>(P & <>Q)" by S43_solve
lemma "|- [](P | Q) & []([]P | Q) & [](P | []Q) --> []P | []Q" by S43_solve
lemma "|- <>P & <>Q --> <>(P & Q) | <>(<>P & Q) | <>(P & <>Q)" by S43_solve
lemma "|- <>[]<>P <-> []<>P" by S43_solve
lemma "|- []<>[]P <-> <>[]P" by S43_solve

(* These are from Hailpern, LNCS 129 *)

lemma "|- [](P & Q) <-> []P & []Q" by S43_solve
lemma "|- <>(P | Q) <-> <>P | <>Q" by S43_solve
lemma "|- <>(P --> Q) <-> []P --> <>Q" by S43_solve

lemma "|- [](P --> Q) --> <>P --> <>Q" by S43_solve
lemma "|- []P --> []<>P" by S43_solve
lemma "|- <>[]P --> <>P" by S43_solve
lemma "|- []<>[]P --> []<>P" by S43_solve
lemma "|- <>[]P --> <>[]<>P" by S43_solve
lemma "|- <>[]P --> []<>P" by S43_solve
lemma "|- []<>[]P <-> <>[]P" by S43_solve
lemma "|- <>[]<>P <-> []<>P" by S43_solve

lemma "|- []P | []Q --> [](P | Q)" by S43_solve
lemma "|- <>(P & Q) --> <>P & <>Q" by S43_solve
lemma "|- [](P | Q) --> []P | <>Q" by S43_solve
lemma "|- <>P & []Q --> <>(P & Q)" by S43_solve
lemma "|- [](P | Q) --> <>P | []Q" by S43_solve
lemma "|- [](P | Q) --> []<>P | []<>Q" by S43_solve
lemma "|- <>[]P & <>[]Q --> <>(P & Q)" by S43_solve
lemma "|- <>[](P & Q) <-> <>[]P & <>[]Q" by S43_solve
lemma "|- []<>(P | Q) <-> []<>P | []<>Q" by S43_solve

end
