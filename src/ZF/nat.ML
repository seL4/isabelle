(*  Title: 	ZF/nat.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For nat.thy.  Natural numbers in Zermelo-Fraenkel Set Theory 
*)

open Nat;

goal Nat.thy "bnd_mono(Inf, %X. {0} Un {succ(i). i:X})";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [subset_refl, RepFun_mono, Un_mono] 2)); 
by (cut_facts_tac [infinity] 1);
by (fast_tac ZF_cs 1);
val nat_bnd_mono = result();

(* nat = {0} Un {succ(x). x:nat} *)
val nat_unfold = nat_bnd_mono RS (nat_def RS def_lfp_Tarski);

(** Type checking of 0 and successor **)

goal Nat.thy "0 : nat";
by (rtac (nat_unfold RS ssubst) 1);
by (rtac (singletonI RS UnI1) 1);
val nat_0I = result();

val prems = goal Nat.thy "n : nat ==> succ(n) : nat";
by (rtac (nat_unfold RS ssubst) 1);
by (rtac (RepFunI RS UnI2) 1);
by (resolve_tac prems 1);
val nat_succI = result();

goalw Nat.thy [one_def] "1 : nat";
by (rtac (nat_0I RS nat_succI) 1);
val nat_1I = result();

goal Nat.thy "bool <= nat";
by (REPEAT (ares_tac [subsetI,nat_0I,nat_1I] 1 ORELSE etac boolE 1));
val bool_subset_nat = result();

val bool_into_nat = bool_subset_nat RS subsetD;


(** Injectivity properties and induction **)

(*Mathematical induction*)
val major::prems = goal Nat.thy
    "[| n: nat;  P(0);  !!x. [| x: nat;  P(x) |] ==> P(succ(x)) |] ==> P(n)";
by (rtac ([nat_def, nat_bnd_mono, major] MRS def_induct) 1);
by (fast_tac (ZF_cs addIs prems) 1);
val nat_induct = result();

(*Perform induction on n, then prove the n:nat subgoal using prems. *)
fun nat_ind_tac a prems i = 
    EVERY [res_inst_tac [("n",a)] nat_induct i,
	   rename_last_tac a ["1"] (i+2),
	   ares_tac prems i];

val major::prems = goal Nat.thy
    "[| n: nat;  n=0 ==> P;  !!x. [| x: nat; n=succ(x) |] ==> P |] ==> P";
br (major RS (nat_unfold RS equalityD1 RS subsetD) RS UnE) 1;
by (DEPTH_SOLVE (eresolve_tac [singletonE,RepFunE] 1
          ORELSE ares_tac prems 1));
val natE = result();

val prems = goal Nat.thy "n: nat ==> Ord(n)";
by (nat_ind_tac "n" prems 1);
by (REPEAT (ares_tac [Ord_0, Ord_succ] 1));
val naturals_are_ordinals = result();

goal Nat.thy "!!n. n: nat ==> n=0 | 0:n";
by (etac nat_induct 1);
by (fast_tac ZF_cs 1);
by (fast_tac (ZF_cs addIs [naturals_are_ordinals RS Ord_0_mem_succ]) 1);
val natE0 = result();

goal Nat.thy "Ord(nat)";
by (rtac OrdI 1);
by (etac (naturals_are_ordinals RS Ord_is_Transset) 2);
by (rewtac Transset_def);
by (rtac ballI 1);
by (etac nat_induct 1);
by (REPEAT (ares_tac [empty_subsetI,succ_subsetI] 1));
val Ord_nat = result();

(** Variations on mathematical induction **)

(*complete induction*)
val complete_induct = Ord_nat RSN (2, Ord_induct);

val prems = goal Nat.thy
    "[| m: nat;  n: nat;  \
\       !!x. [| x: nat;  m<=x;  P(x) |] ==> P(succ(x)) \
\    |] ==> m <= n --> P(m) --> P(n)";
by (nat_ind_tac "n" prems 1);
by (ALLGOALS
    (asm_simp_tac
     (ZF_ss addsimps (prems@distrib_rews@[subset_empty_iff, subset_succ_iff, 
					 Ord_nat RS Ord_in_Ord]))));
val nat_induct_from_lemma = result();

(*Induction starting from m rather than 0*)
val prems = goal Nat.thy
    "[| m <= n;  m: nat;  n: nat;  \
\       P(m);  \
\       !!x. [| x: nat;  m<=x;  P(x) |] ==> P(succ(x)) \
\    |] ==> P(n)";
by (rtac (nat_induct_from_lemma RS mp RS mp) 1);
by (REPEAT (ares_tac prems 1));
val nat_induct_from = result();

(*Induction suitable for subtraction and less-than*)
val prems = goal Nat.thy
    "[| m: nat;  n: nat;  \
\       !!x. [| x: nat |] ==> P(x,0);  \
\       !!y. [| y: nat |] ==> P(0,succ(y));  \
\       !!x y. [| x: nat;  y: nat;  P(x,y) |] ==> P(succ(x),succ(y))  \
\    |] ==> P(m,n)";
by (res_inst_tac [("x","m")] bspec 1);
by (resolve_tac prems 2);
by (nat_ind_tac "n" prems 1);
by (rtac ballI 2);
by (nat_ind_tac "x" [] 2);
by (REPEAT (ares_tac (prems@[ballI]) 1 ORELSE etac bspec 1));
val diff_induct = result();

(** nat_case **)

goalw Nat.thy [nat_case_def] "nat_case(a,b,0) = a";
by (fast_tac (ZF_cs addIs [the_equality]) 1);
val nat_case_0 = result();

goalw Nat.thy [nat_case_def] "nat_case(a,b,succ(m)) = b(m)";
by (fast_tac (ZF_cs addIs [the_equality]) 1);
val nat_case_succ = result();

val major::prems = goal Nat.thy
    "[| n: nat;  a: C(0);  !!m. m: nat ==> b(m): C(succ(m))  \
\    |] ==> nat_case(a,b,n) : C(n)";
by (rtac (major RS nat_induct) 1);
by (REPEAT (resolve_tac [nat_case_0 RS ssubst,
			 nat_case_succ RS ssubst] 1 
       THEN resolve_tac prems 1));
by (assume_tac 1);
val nat_case_type = result();


(** nat_rec -- used to define eclose and transrec, then obsolete **)

val nat_rec_trans = wf_Memrel RS (nat_rec_def RS def_wfrec RS trans);

goal Nat.thy "nat_rec(0,a,b) = a";
by (rtac nat_rec_trans 1);
by (rtac nat_case_0 1);
val nat_rec_0 = result();

val [prem] = goal Nat.thy 
    "m: nat ==> nat_rec(succ(m),a,b) = b(m, nat_rec(m,a,b))";
val nat_rec_ss = ZF_ss 
      addsimps [prem, nat_case_succ, nat_succI, Memrel_iff, 
		vimage_singleton_iff];
by (rtac nat_rec_trans 1);
by (simp_tac nat_rec_ss 1);
val nat_rec_succ = result();

(** The union of two natural numbers is a natural number -- their maximum **)

(*  [| ?i : nat; ?j : nat |] ==> ?i Un ?j : nat  *)
val Un_nat_type = standard (Ord_nat RSN (3,Ord_member_UnI));

(*  [| ?i : nat; ?j : nat |] ==> ?i Int ?j : nat  *)
val Int_nat_type = standard (Ord_nat RSN (3,Ord_member_IntI));

