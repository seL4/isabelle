(*  Title: 	HOLCF/holcfb.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for Holcfb.thy 
*)

open Holcfb;

(* ------------------------------------------------------------------------ *)
(* <::nat=>nat=>bool is a well-ordering                                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "well_ordering_nat"  Nat.thy 
	"!P. P(x::nat) --> (? y. P(y) & (! x. P(x) --> y <= x))"
 (fn prems =>
	[
	(res_inst_tac [("n","x")] less_induct 1),
	(strip_tac 1),
	(res_inst_tac [("Q","? k.k<n & P(k)")] (excluded_middle RS disjE) 1),
	(etac exE 2),
	(etac conjE 2),
	(rtac mp 2),
	(etac allE 2),
	(etac impE 2),
	(atac 2),
	(etac spec 2),
	(atac 2),
	(res_inst_tac [("x","n")] exI 1),
	(rtac conjI 1),
	(atac 1),
	(strip_tac 1),
	(rtac leI  1),
	(fast_tac HOL_cs 1)
	]);


(* ------------------------------------------------------------------------ *)
(* Lemmas for selecting the least element in a nonempty set                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "theleast"  Holcfb.thy [theleast_def] 
"P(x) ==> P(theleast(P)) & (!x.P(x)--> theleast(P) <= x)"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (well_ordering_nat RS spec RS mp RS exE) 1),
	(atac 1),
	(rtac selectI 1),
	(atac 1)
	]);

val theleast1= theleast RS conjunct1;
(* ?P1(?x1) ==> ?P1(theleast(?P1)) *)

qed_goal "theleast2"  Holcfb.thy  "P(x) ==> theleast(P) <= x"
 (fn prems =>
	[
	(rtac (theleast RS conjunct2 RS spec RS mp) 1),
	(resolve_tac prems 1),
	(resolve_tac prems 1)
	]);


(* ------------------------------------------------------------------------ *)
(* Some lemmas in HOL.thy                                                   *)
(* ------------------------------------------------------------------------ *)


qed_goal "de_morgan1" HOL.thy "(~a & ~b)=(~(a | b))"
(fn prems =>
	[
	(rtac iffI 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "de_morgan2" HOL.thy "(~a | ~b)=(~(a & b))"
(fn prems =>
	[
	(rtac iffI 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);


qed_goal "notall2ex" HOL.thy "(~ (!x.P(x))) = (? x.~P(x))"
(fn prems =>
	[
	(rtac iffI 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "notex2all" HOL.thy "(~ (? x.P(x))) = (!x.~P(x))"
(fn prems =>
	[
	(rtac iffI 1),
	(fast_tac HOL_cs 1),
	(fast_tac HOL_cs 1)
	]);


qed_goal "selectI3" HOL.thy "(? x. P(x)) ==> P(@ x.P(x))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exE 1),
	(etac selectI 1)
	]);

qed_goal "selectE" HOL.thy "P(@ x.P(x)) ==> (? x. P(x))"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac exI 1)
	]);

qed_goal "select_eq_Ex" HOL.thy "(P(@ x.P(x))) =  (? x. P(x))"
(fn prems =>
	[
	(rtac (iff RS mp  RS mp) 1),
	(strip_tac 1),
	(etac selectE 1),
	(strip_tac 1),
	(etac selectI3 1)
	]);


qed_goal "notnotI" HOL.thy "P ==> ~~P"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(fast_tac HOL_cs 1)
	]);


qed_goal "classical2" HOL.thy "[|Q ==> R; ~Q ==> R|]==>R"
 (fn prems =>
	[
	(rtac disjE 1),
	(rtac excluded_middle 1),
	(eresolve_tac prems 1),
	(eresolve_tac prems 1)
	]);



val classical3 = (notE RS notI);
(* [| ?P ==> ~ ?P1; ?P ==> ?P1 |] ==> ~ ?P *)


qed_goal "nat_less_cases" Nat.thy 
    "[| (m::nat) < n ==> P(n,m); m=n ==> P(n,m);n < m ==> P(n,m)|]==>P(n,m)"
( fn prems =>
	[
	(res_inst_tac [("m1","n"),("n1","m")] (less_linear RS disjE) 1),
	(etac disjE 2),
	(etac (hd (tl (tl prems))) 1),
	(etac (sym RS hd (tl prems)) 1),
	(etac (hd prems) 1)
	]);







