(*  Title:      Modal/S43
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge

This implements Rajeev Gore's sequent calculus for S43.
*)

S43 = Modal0 +

consts
  S43pi :: "[seq'=>seq', seq'=>seq', seq'=>seq',
             seq'=>seq', seq'=>seq', seq'=>seq'] => prop"
syntax
  "@S43pi" :: "[seq, seq, seq, seq, seq, seq] => prop"
                         ("S43pi((_);(_);(_);(_);(_);(_))" [] 5)

rules
(* Definition of the star operation using a set of Horn clauses  *)
(* For system S43: gamma * == {[]P | []P : gamma}                *)
(*                 delta * == {<>P | <>P : delta}                *)

  lstar0         "|L>"
  lstar1         "$G |L> $H ==> []P, $G |L> []P, $H"
  lstar2         "$G |L> $H ==>   P, $G |L>      $H"
  rstar0         "|R>"
  rstar1         "$G |R> $H ==> <>P, $G |R> <>P, $H"
  rstar2         "$G |R> $H ==>   P, $G |R>      $H"

(* Set of Horn clauses to generate the antecedents for the S43 pi rule       *)
(* ie                                                                        *)
(*           S1...Sk,Sk+1...Sk+m                                             *)
(*     ----------------------------------                                    *)
(*     <>P1...<>Pk, $G |- $H, []Q1...[]Qm                                    *)
(*                                                                           *)
(*  where Si == <>P1...<>Pi-1,<>Pi+1,..<>Pk,Pi, $G * |- $H *, []Q1...[]Qm    *)
(*    and Sj == <>P1...<>Pk, $G * |- $H *, []Q1...[]Qj-1,[]Qj+1...[]Qm,Qj    *)
(*    and 1<=i<=k and k<j<=k+m                                               *)

  S43pi0         "S43pi $L;; $R;; $Lbox; $Rdia"
  S43pi1
   "[| (S43pi <>P,$L';     $L;; $R; $Lbox;$Rdia);   $L',P,$L,$Lbox |- $R,$Rdia |] ==> 
       S43pi     $L'; <>P,$L;; $R; $Lbox;$Rdia"
  S43pi2
   "[| (S43pi $L';; []P,$R';     $R; $Lbox;$Rdia);  $L',$Lbox |- $R',P,$R,$Rdia |] ==> 
       S43pi $L';;     $R'; []P,$R; $Lbox;$Rdia"

(* Rules for [] and <> for S43 *)

  boxL           "$E, P, $F, []P |- $G ==> $E, []P, $F |- $G"
  diaR           "$E |- $F, P, $G, <>P ==> $E |- $F, <>P, $G"
  pi1
   "[| $L1,<>P,$L2 |L> $Lbox;  $L1,<>P,$L2 |R> $Ldia;  $R |L> $Rbox;  $R |R> $Rdia;  
      S43pi ; $Ldia;; $Rbox; $Lbox; $Rdia |] ==> 
   $L1, <>P, $L2 |- $R"
  pi2
   "[| $L |L> $Lbox;  $L |R> $Ldia;  $R1,[]P,$R2 |L> $Rbox;  $R1,[]P,$R2 |R> $Rdia;  
      S43pi ; $Ldia;; $Rbox; $Lbox; $Rdia |] ==> 
   $L |- $R1, []P, $R2"
end

ML

local

  val S43pi  = "S43pi";
  val SS43pi = "@S43pi";

  val tr  = Sequents.seq_tr;
  val tr' = Sequents.seq_tr';

  fun s43pi_tr[s1,s2,s3,s4,s5,s6]=
        Const(S43pi,dummyT)$tr s1$tr s2$tr s3$tr s4$tr s5$tr s6;
  fun s43pi_tr'[s1,s2,s3,s4,s5,s6] =
        Const(SS43pi,dummyT)$tr' s1$tr' s2$tr' s3$tr' s4$tr' s5$tr' s6;
in
val parse_translation = [(SS43pi,s43pi_tr)];
val print_translation = [(S43pi,s43pi_tr')]
end
