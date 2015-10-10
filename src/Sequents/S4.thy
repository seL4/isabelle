(*  Title:      Sequents/S4.thy
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

theory S4
imports Modal0
begin

axiomatization where
(* Definition of the star operation using a set of Horn clauses *)
(* For system S4:  gamma * == {[]P | []P : gamma}               *)
(*                 delta * == {<>P | <>P : delta}               *)

  lstar0:         "|L>" and
  lstar1:         "$G |L> $H \<Longrightarrow> []P, $G |L> []P, $H" and
  lstar2:         "$G |L> $H \<Longrightarrow>   P, $G |L>      $H" and
  rstar0:         "|R>" and
  rstar1:         "$G |R> $H \<Longrightarrow> <>P, $G |R> <>P, $H" and
  rstar2:         "$G |R> $H \<Longrightarrow>   P, $G |R>      $H" and

(* Rules for [] and <> *)

  boxR:
   "\<lbrakk>$E |L> $E';  $F |R> $F';  $G |R> $G';
           $E'         \<turnstile> $F', P, $G'\<rbrakk> \<Longrightarrow> $E          \<turnstile> $F, []P, $G" and
  boxL:     "$E,P,$F,[]P \<turnstile>         $G    \<Longrightarrow> $E, []P, $F \<turnstile>          $G" and

  diaR:     "$E          \<turnstile> $F,P,$G,<>P   \<Longrightarrow> $E          \<turnstile> $F, <>P, $G" and
  diaL:
   "\<lbrakk>$E |L> $E';  $F |L> $F';  $G |R> $G';
           $E', P, $F' \<turnstile>         $G'\<rbrakk> \<Longrightarrow> $E, <>P, $F \<turnstile> $G"

ML \<open>
structure S4_Prover = Modal_ProverFun
(
  val rewrite_rls = @{thms rewrite_rls}
  val safe_rls = @{thms safe_rls}
  val unsafe_rls = @{thms unsafe_rls} @ [@{thm boxR}, @{thm diaL}]
  val bound_rls = @{thms bound_rls} @ [@{thm boxL}, @{thm diaR}]
  val aside_rls = [@{thm lstar0}, @{thm lstar1}, @{thm lstar2}, @{thm rstar0},
    @{thm rstar1}, @{thm rstar2}]
)
\<close>

method_setup S4_solve =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (S4_Prover.solve_tac ctxt 2))\<close>


(* Theorems of system T from Hughes and Cresswell and Hailpern, LNCS 129 *)

lemma "\<turnstile> []P \<longrightarrow> P" by S4_solve
lemma "\<turnstile> [](P \<longrightarrow> Q) \<longrightarrow> ([]P \<longrightarrow> []Q)" by S4_solve   (* normality*)
lemma "\<turnstile> (P --< Q) \<longrightarrow> []P \<longrightarrow> []Q" by S4_solve
lemma "\<turnstile> P \<longrightarrow> <>P" by S4_solve

lemma "\<turnstile>  [](P \<and> Q) \<longleftrightarrow> []P \<and> []Q" by S4_solve
lemma "\<turnstile>  <>(P \<or> Q) \<longleftrightarrow> <>P \<or> <>Q" by S4_solve
lemma "\<turnstile>  [](P \<longleftrightarrow> Q) \<longleftrightarrow> (P >-< Q)" by S4_solve
lemma "\<turnstile>  <>(P \<longrightarrow> Q) \<longleftrightarrow> ([]P \<longrightarrow> <>Q)" by S4_solve
lemma "\<turnstile>        []P \<longleftrightarrow> \<not> <>(\<not> P)" by S4_solve
lemma "\<turnstile>     [](\<not> P) \<longleftrightarrow> \<not> <>P" by S4_solve
lemma "\<turnstile>       \<not> []P \<longleftrightarrow> <>(\<not> P)" by S4_solve
lemma "\<turnstile>      [][]P \<longleftrightarrow> \<not> <><>(\<not> P)" by S4_solve
lemma "\<turnstile> \<not> <>(P \<or> Q) \<longleftrightarrow> \<not> <>P \<and> \<not> <>Q" by S4_solve

lemma "\<turnstile> []P \<or> []Q \<longrightarrow> [](P \<or> Q)" by S4_solve
lemma "\<turnstile> <>(P \<and> Q) \<longrightarrow> <>P \<and> <>Q" by S4_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> []P \<or> <>Q" by S4_solve
lemma "\<turnstile> <>P \<and> []Q \<longrightarrow> <>(P \<and> Q)" by S4_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> <>P \<or> []Q" by S4_solve
lemma "\<turnstile> <>(P \<longrightarrow> (Q \<and> R)) \<longrightarrow> ([]P \<longrightarrow> <>Q) \<and> ([]P \<longrightarrow> <>R)" by S4_solve
lemma "\<turnstile> (P --< Q) \<and> (Q --< R) \<longrightarrow> (P --< R)" by S4_solve
lemma "\<turnstile> []P \<longrightarrow> <>Q \<longrightarrow> <>(P \<and> Q)" by S4_solve


(* Theorems of system S4 from Hughes and Cresswell, p.46 *)

lemma "\<turnstile> []A \<longrightarrow> A" by S4_solve             (* refexivity *)
lemma "\<turnstile> []A \<longrightarrow> [][]A" by S4_solve         (* transitivity *)
lemma "\<turnstile> []A \<longrightarrow> <>A" by S4_solve           (* seriality *)
lemma "\<turnstile> <>[](<>A \<longrightarrow> []<>A)" by S4_solve
lemma "\<turnstile> <>[](<>[]A \<longrightarrow> []A)" by S4_solve
lemma "\<turnstile> []P \<longleftrightarrow> [][]P" by S4_solve
lemma "\<turnstile> <>P \<longleftrightarrow> <><>P" by S4_solve
lemma "\<turnstile> <>[]<>P \<longrightarrow> <>P" by S4_solve
lemma "\<turnstile> []<>P \<longleftrightarrow> []<>[]<>P" by S4_solve
lemma "\<turnstile> <>[]P \<longleftrightarrow> <>[]<>[]P" by S4_solve

(* Theorems for system S4 from Hughes and Cresswell, p.60 *)

lemma "\<turnstile> []P \<or> []Q \<longleftrightarrow> []([]P \<or> []Q)" by S4_solve
lemma "\<turnstile> ((P >-< Q) --< R) \<longrightarrow> ((P >-< Q) --< []R)" by S4_solve

(* These are from Hailpern, LNCS 129 *)

lemma "\<turnstile> [](P \<and> Q) \<longleftrightarrow> []P \<and> []Q" by S4_solve
lemma "\<turnstile> <>(P \<or> Q) \<longleftrightarrow> <>P \<or> <>Q" by S4_solve
lemma "\<turnstile> <>(P \<longrightarrow> Q) \<longleftrightarrow> ([]P \<longrightarrow> <>Q)" by S4_solve

lemma "\<turnstile> [](P \<longrightarrow> Q) \<longrightarrow> (<>P \<longrightarrow> <>Q)" by S4_solve
lemma "\<turnstile> []P \<longrightarrow> []<>P" by S4_solve
lemma "\<turnstile> <>[]P \<longrightarrow> <>P" by S4_solve

lemma "\<turnstile> []P \<or> []Q \<longrightarrow> [](P \<or> Q)" by S4_solve
lemma "\<turnstile> <>(P \<and> Q) \<longrightarrow> <>P \<and> <>Q" by S4_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> []P \<or> <>Q" by S4_solve
lemma "\<turnstile> <>P \<and> []Q \<longrightarrow> <>(P \<and> Q)" by S4_solve
lemma "\<turnstile> [](P \<or> Q) \<longrightarrow> <>P \<or> []Q" by S4_solve

end
