(*  Title:      Sequents/S43.thy
    Author:     Martin Coen
    Copyright   1991  University of Cambridge

This implements Rajeev Gore's sequent calculus for S43.
*)

theory S43
imports Modal0
begin

consts
  S43pi :: "[seq'\<Rightarrow>seq', seq'\<Rightarrow>seq', seq'\<Rightarrow>seq',
             seq'\<Rightarrow>seq', seq'\<Rightarrow>seq', seq'\<Rightarrow>seq'] \<Rightarrow> prop"
syntax
  "_S43pi" :: "[seq, seq, seq, seq, seq, seq] \<Rightarrow> prop"
                         ("S43pi((_);(_);(_);(_);(_);(_))" [] 5)

parse_translation \<open>
  let
    val tr  = seq_tr;
    fun s43pi_tr [s1, s2, s3, s4, s5, s6] =
      Syntax.const \<^const_syntax>\<open>S43pi\<close> $ tr s1 $ tr s2 $ tr s3 $ tr s4 $ tr s5 $ tr s6;
  in [(\<^syntax_const>\<open>_S43pi\<close>, K s43pi_tr)] end
\<close>

print_translation \<open>
let
  val tr' = seq_tr';
  fun s43pi_tr' [s1, s2, s3, s4, s5, s6] =
    Syntax.const \<^syntax_const>\<open>_S43pi\<close> $ tr' s1 $ tr' s2 $ tr' s3 $ tr' s4 $ tr' s5 $ tr' s6;
in [(\<^const_syntax>\<open>S43pi\<close>, K s43pi_tr')] end
\<close>

axiomatization where
(* Definition of the star operation using a set of Horn clauses  *)
(* For system S43: gamma * == {[]P | []P : gamma}                *)
(*                 delta * == {<>P | <>P : delta}                *)

  lstar0:         "|L>" and
  lstar1:         "$G |L> $H \<Longrightarrow> []P, $G |L> []P, $H" and
  lstar2:         "$G |L> $H \<Longrightarrow>   P, $G |L>      $H" and
  rstar0:         "|R>" and
  rstar1:         "$G |R> $H \<Longrightarrow> <>P, $G |R> <>P, $H" and
  rstar2:         "$G |R> $H \<Longrightarrow>   P, $G |R>      $H" and

(* Set of Horn clauses to generate the antecedents for the S43 pi rule       *)
(* ie                                                                        *)
(*           S1...Sk,Sk+1...Sk+m                                             *)
(*     ----------------------------------                                    *)
(*     <>P1...<>Pk, $G \<turnstile> $H, []Q1...[]Qm                                    *)
(*                                                                           *)
(*  where Si == <>P1...<>Pi-1,<>Pi+1,..<>Pk,Pi, $G * \<turnstile> $H *, []Q1...[]Qm    *)
(*    and Sj == <>P1...<>Pk, $G * \<turnstile> $H *, []Q1...[]Qj-1,[]Qj+1...[]Qm,Qj    *)
(*    and 1<=i<=k and k<j<=k+m                                               *)

  S43pi0:         "S43pi $L;; $R;; $Lbox; $Rdia" and
  S43pi1:
   "\<lbrakk>(S43pi <>P,$L';     $L;; $R; $Lbox;$Rdia);   $L',P,$L,$Lbox \<turnstile> $R,$Rdia\<rbrakk> \<Longrightarrow>
       S43pi     $L'; <>P,$L;; $R; $Lbox;$Rdia" and
  S43pi2:
   "\<lbrakk>(S43pi $L';; []P,$R';     $R; $Lbox;$Rdia);  $L',$Lbox \<turnstile> $R',P,$R,$Rdia\<rbrakk> \<Longrightarrow>
       S43pi $L';;     $R'; []P,$R; $Lbox;$Rdia" and

(* Rules for [] and <> for S43 *)

  boxL:           "$E, P, $F, []P \<turnstile> $G \<Longrightarrow> $E, []P, $F \<turnstile> $G" and
  diaR:           "$E \<turnstile> $F, P, $G, <>P \<Longrightarrow> $E \<turnstile> $F, <>P, $G" and
  pi1:
   "\<lbrakk>$L1,<>P,$L2 |L> $Lbox;  $L1,<>P,$L2 |R> $Ldia;  $R |L> $Rbox;  $R |R> $Rdia;
      S43pi ; $Ldia;; $Rbox; $Lbox; $Rdia\<rbrakk> \<Longrightarrow>
   $L1, <>P, $L2 \<turnstile> $R" and
  pi2:
   "\<lbrakk>$L |L> $Lbox;  $L |R> $Ldia;  $R1,[]P,$R2 |L> $Rbox;  $R1,[]P,$R2 |R> $Rdia;
      S43pi ; $Ldia;; $Rbox; $Lbox; $Rdia\<rbrakk> \<Longrightarrow>
   $L \<turnstile> $R1, []P, $R2"


ML \<open>
structure S43_Prover = Modal_ProverFun
(
  val rewrite_rls = @{thms rewrite_rls}
  val safe_rls = @{thms safe_rls}
  val unsafe_rls = @{thms unsafe_rls} @ [@{thm pi1}, @{thm pi2}]
  val bound_rls = @{thms bound_rls} @ [@{thm boxL}, @{thm diaR}]
  val aside_rls = [@{thm lstar0}, @{thm lstar1}, @{thm lstar2}, @{thm rstar0},
    @{thm rstar1}, @{thm rstar2}, @{thm S43pi0}, @{thm S43pi1}, @{thm S43pi2}]
)
\<close>


method_setup S43_solve = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD
    (S43_Prover.solve_tac ctxt 2 ORELSE S43_Prover.solve_tac ctxt 3))
\<close>


(* Theorems of system T from Hughes and Cresswell and Hailpern, LNCS 129 *)

lemma "\<turnstile> []P \<longrightarrow> P" by S43_solve
lemma "\<turnstile> [](P \<longrightarrow> Q) \<longrightarrow> ([]P \<longrightarrow> []Q)" by S43_solve   (* normality*)
lemma "\<turnstile> (P--<Q) \<longrightarrow> []P \<longrightarrow> []Q" by S43_solve
lemma "\<turnstile> P \<longrightarrow> <>P" by S43_solve

lemma "\<turnstile>  [](P \<and> Q) \<longleftrightarrow> []P \<and> []Q" by S43_solve
lemma "\<turnstile>  <>(P \<or> Q) \<longleftrightarrow> <>P \<or> <>Q" by S43_solve
lemma "\<turnstile>  [](P \<longleftrightarrow> Q) \<longleftrightarrow> (P>-<Q)" by S43_solve
lemma "\<turnstile>  <>(P \<longrightarrow> Q) \<longleftrightarrow> ([]P \<longrightarrow> <>Q)" by S43_solve
lemma "\<turnstile>        []P \<longleftrightarrow> \<not> <>(\<not> P)" by S43_solve
lemma "\<turnstile>     [](\<not>P) \<longleftrightarrow> \<not> <>P" by S43_solve
lemma "\<turnstile>       \<not> []P \<longleftrightarrow> <>(\<not> P)" by S43_solve
lemma "\<turnstile>      [][]P \<longleftrightarrow> \<not> <><>(\<not> P)" by S43_solve
lemma "\<turnstile> \<not> <>(P \<or> Q) \<longleftrightarrow> \<not> <>P \<and> \<not> <>Q" by S43_solve

lemma "\<turnstile> []P \<or> []Q \<longrightarrow> [](P \<or> Q)" by S43_solve
lemma "\<turnstile> <>(P \<and> Q) \<longrightarrow> <>P \<and> <>Q" by S43_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> []P \<or> <>Q" by S43_solve
lemma "\<turnstile> <>P \<and> []Q \<longrightarrow> <>(P \<and> Q)" by S43_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> <>P \<or> []Q" by S43_solve
lemma "\<turnstile> <>(P \<longrightarrow> (Q \<and> R)) \<longrightarrow> ([]P \<longrightarrow> <>Q) \<and> ([]P \<longrightarrow> <>R)" by S43_solve
lemma "\<turnstile> (P --< Q) \<and> (Q --<R ) \<longrightarrow> (P --< R)" by S43_solve
lemma "\<turnstile> []P \<longrightarrow> <>Q \<longrightarrow> <>(P \<and> Q)" by S43_solve


(* Theorems of system S4 from Hughes and Cresswell, p.46 *)

lemma "\<turnstile> []A \<longrightarrow> A" by S43_solve             (* refexivity *)
lemma "\<turnstile> []A \<longrightarrow> [][]A" by S43_solve         (* transitivity *)
lemma "\<turnstile> []A \<longrightarrow> <>A" by S43_solve           (* seriality *)
lemma "\<turnstile> <>[](<>A \<longrightarrow> []<>A)" by S43_solve
lemma "\<turnstile> <>[](<>[]A \<longrightarrow> []A)" by S43_solve
lemma "\<turnstile> []P \<longleftrightarrow> [][]P" by S43_solve
lemma "\<turnstile> <>P \<longleftrightarrow> <><>P" by S43_solve
lemma "\<turnstile> <>[]<>P \<longrightarrow> <>P" by S43_solve
lemma "\<turnstile> []<>P \<longleftrightarrow> []<>[]<>P" by S43_solve
lemma "\<turnstile> <>[]P \<longleftrightarrow> <>[]<>[]P" by S43_solve

(* Theorems for system S4 from Hughes and Cresswell, p.60 *)

lemma "\<turnstile> []P \<or> []Q \<longleftrightarrow> []([]P \<or> []Q)" by S43_solve
lemma "\<turnstile> ((P >-< Q) --< R) \<longrightarrow> ((P >-< Q) --< []R)" by S43_solve

(* These are from Hailpern, LNCS 129 *)

lemma "\<turnstile> [](P \<and> Q) \<longleftrightarrow> []P \<and> []Q" by S43_solve
lemma "\<turnstile> <>(P \<or> Q) \<longleftrightarrow> <>P \<or> <>Q" by S43_solve
lemma "\<turnstile> <>(P \<longrightarrow> Q) \<longleftrightarrow> ([]P \<longrightarrow> <>Q)" by S43_solve

lemma "\<turnstile> [](P \<longrightarrow> Q) \<longrightarrow> (<>P \<longrightarrow> <>Q)" by S43_solve
lemma "\<turnstile> []P \<longrightarrow> []<>P" by S43_solve
lemma "\<turnstile> <>[]P \<longrightarrow> <>P" by S43_solve

lemma "\<turnstile> []P \<or> []Q \<longrightarrow> [](P \<or> Q)" by S43_solve
lemma "\<turnstile> <>(P \<and> Q) \<longrightarrow> <>P \<and> <>Q" by S43_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> []P \<or> <>Q" by S43_solve
lemma "\<turnstile> <>P \<and> []Q \<longrightarrow> <>(P \<and> Q)" by S43_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> <>P \<or> []Q" by S43_solve


(* Theorems of system S43 *)

lemma "\<turnstile> <>[]P \<longrightarrow> []<>P" by S43_solve
lemma "\<turnstile> <>[]P \<longrightarrow> [][]<>P" by S43_solve
lemma "\<turnstile> [](<>P \<or> <>Q) \<longrightarrow> []<>P \<or> []<>Q" by S43_solve
lemma "\<turnstile> <>[]P \<and> <>[]Q \<longrightarrow> <>([]P \<and> []Q)" by S43_solve
lemma "\<turnstile> []([]P \<longrightarrow> []Q) \<or> []([]Q \<longrightarrow> []P)" by S43_solve
lemma "\<turnstile> [](<>P \<longrightarrow> <>Q) \<or> [](<>Q \<longrightarrow> <>P)" by S43_solve
lemma "\<turnstile> []([]P \<longrightarrow> Q) \<or> []([]Q \<longrightarrow> P)" by S43_solve
lemma "\<turnstile> [](P \<longrightarrow> <>Q) \<or> [](Q \<longrightarrow> <>P)" by S43_solve
lemma "\<turnstile> [](P \<longrightarrow> []Q \<longrightarrow> R) \<or> [](P \<or> ([]R \<longrightarrow> Q))" by S43_solve
lemma "\<turnstile> [](P \<or> (Q \<longrightarrow> <>C)) \<or> [](P \<longrightarrow> C \<longrightarrow> <>Q)" by S43_solve
lemma "\<turnstile> []([]P \<or> Q) \<and> [](P \<or> []Q) \<longrightarrow> []P \<or> []Q" by S43_solve
lemma "\<turnstile> <>P \<and> <>Q \<longrightarrow> <>(<>P \<and> Q) \<or> <>(P \<and> <>Q)" by S43_solve
lemma "\<turnstile> [](P \<or> Q) \<and> []([]P \<or> Q) \<and> [](P \<or> []Q) \<longrightarrow> []P \<or> []Q" by S43_solve
lemma "\<turnstile> <>P \<and> <>Q \<longrightarrow> <>(P \<and> Q) \<or> <>(<>P \<and> Q) \<or> <>(P \<and> <>Q)" by S43_solve
lemma "\<turnstile> <>[]<>P \<longleftrightarrow> []<>P" by S43_solve
lemma "\<turnstile> []<>[]P \<longleftrightarrow> <>[]P" by S43_solve

(* These are from Hailpern, LNCS 129 *)

lemma "\<turnstile> [](P \<and> Q) \<longleftrightarrow> []P \<and> []Q" by S43_solve
lemma "\<turnstile> <>(P \<or> Q) \<longleftrightarrow> <>P \<or> <>Q" by S43_solve
lemma "\<turnstile> <>(P \<longrightarrow> Q) \<longleftrightarrow> []P \<longrightarrow> <>Q" by S43_solve

lemma "\<turnstile> [](P \<longrightarrow> Q) \<longrightarrow> <>P \<longrightarrow> <>Q" by S43_solve
lemma "\<turnstile> []P \<longrightarrow> []<>P" by S43_solve
lemma "\<turnstile> <>[]P \<longrightarrow> <>P" by S43_solve
lemma "\<turnstile> []<>[]P \<longrightarrow> []<>P" by S43_solve
lemma "\<turnstile> <>[]P \<longrightarrow> <>[]<>P" by S43_solve
lemma "\<turnstile> <>[]P \<longrightarrow> []<>P" by S43_solve
lemma "\<turnstile> []<>[]P \<longleftrightarrow> <>[]P" by S43_solve
lemma "\<turnstile> <>[]<>P \<longleftrightarrow> []<>P" by S43_solve

lemma "\<turnstile> []P \<or> []Q \<longrightarrow> [](P \<or> Q)" by S43_solve
lemma "\<turnstile> <>(P \<and> Q) \<longrightarrow> <>P \<and> <>Q" by S43_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> []P \<or> <>Q" by S43_solve
lemma "\<turnstile> <>P \<and> []Q \<longrightarrow> <>(P \<and> Q)" by S43_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> <>P \<or> []Q" by S43_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> []<>P \<or> []<>Q" by S43_solve
lemma "\<turnstile> <>[]P \<and> <>[]Q \<longrightarrow> <>(P \<and> Q)" by S43_solve
lemma "\<turnstile> <>[](P \<and> Q) \<longleftrightarrow> <>[]P \<and> <>[]Q" by S43_solve
lemma "\<turnstile> []<>(P \<or> Q) \<longleftrightarrow> []<>P \<or> []<>Q" by S43_solve

end
