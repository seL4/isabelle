(*  Title:      FOLP/ex/nat.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Examples for the manual "Introduction to Isabelle"

Proofs about the natural numbers

To generate similar output to manual, execute these commands:
    Pretty.setmargin 72; print_depth 0;
*)

open Nat;

goal Nat.thy "?p : ~ (Suc(k) = k)";
by (res_inst_tac [("n","k")] induct 1);
by (rtac notI 1);
by (etac Suc_neq_0 1);
by (rtac notI 1);
by (etac notE 1);
by (etac Suc_inject 1);
val Suc_n_not_n = result();


goal Nat.thy "?p : (k+m)+n = k+(m+n)";
prths ([induct] RL [topthm()]);  (*prints all 14 next states!*)
by (rtac induct 1);
back();
back();
back();
back();
back();
back();

goalw Nat.thy [add_def] "?p : 0+n = n";
by (rtac rec_0 1);
val add_0 = result();

goalw Nat.thy [add_def] "?p : Suc(m)+n = Suc(m+n)";
by (rtac rec_Suc 1);
val add_Suc = result();

(*
val nat_congs = mk_congs Nat.thy ["Suc", "op +"];
prths nat_congs;
*)
val prems = goal Nat.thy "p: x=y ==> ?p : Suc(x) = Suc(y)";
by (resolve_tac (prems RL [subst]) 1);
by (rtac refl 1);
val Suc_cong = result();

val prems = goal Nat.thy "[| p : a=x;  q: b=y |] ==> ?p : a+b=x+y";
by (resolve_tac (prems RL [subst]) 1 THEN resolve_tac (prems RL [subst]) 1 THEN 
    rtac refl 1);
val Plus_cong = result();

val nat_congs = [Suc_cong,Plus_cong];


val add_ss = FOLP_ss  addcongs nat_congs  
                     addrews  [add_0, add_Suc];

goal Nat.thy "?p : (k+m)+n = k+(m+n)";
by (res_inst_tac [("n","k")] induct 1);
by (SIMP_TAC add_ss 1);
by (ASM_SIMP_TAC add_ss 1);
val add_assoc = result();

goal Nat.thy "?p : m+0 = m";
by (res_inst_tac [("n","m")] induct 1);
by (SIMP_TAC add_ss 1);
by (ASM_SIMP_TAC add_ss 1);
val add_0_right = result();

goal Nat.thy "?p : m+Suc(n) = Suc(m+n)";
by (res_inst_tac [("n","m")] induct 1);
by (ALLGOALS (ASM_SIMP_TAC add_ss));
val add_Suc_right = result();

(*mk_typed_congs appears not to work with FOLP's version of subst*)

