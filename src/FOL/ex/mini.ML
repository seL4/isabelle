(*  Title: 	FOL/ex/mini
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Classical First-Order Logic

Conversion to nnf/miniscope format: pushing quantifiers in

Demonstration of formula rewriting by proof
*)

val ccontr = FalseE RS classical;

(**** Negation Normal Form ****)

(*** de Morgan laws ***)

val not_conjD = prove_fun "~(P&Q) ==> ~P | ~Q";
val not_disjD = prove_fun "~(P|Q) ==> ~P & ~Q";
val not_notD = prove_fun "~~P ==> P";
val not_allD = prove_fun  "~(ALL x.P(x)) ==> EX x. ~P(x)";
val not_exD = prove_fun   "~(EX x.P(x)) ==> ALL x. ~P(x)";


(*** Removal of --> and <-> (positive and negative occurrences) ***)

val imp_to_disjD = prove_fun "P-->Q ==> ~P | Q";
val not_impD = prove_fun   "~(P-->Q) ==> P & ~Q";

val iff_to_disjD = prove_fun "P<->Q ==> (~P | Q) & (~Q | P)";

(*Much more efficient than (P & ~Q) | (Q & ~P) for computing CNF*)
val not_iffD = prove_fun "~(P<->Q) ==> (P | Q) & (~P | ~Q)";


(*** Pushing in the existential quantifiers ***)

val null_exD = prove_fun "EX x. P ==> P";

(** Conjunction **)

val conj_exD1 = prove_fun "EX x. P(x) & Q ==> (EX x.P(x)) & Q";
val conj_exD2 = prove_fun "EX x. P & Q(x) ==> P & (EX x.Q(x))";

(** Disjunction **)

val disj_exD = prove_fun "EX x. P(x) | Q(x) ==> (EX x.P(x)) | (EX x.Q(x))";
val disj_exD1 = prove_fun "EX x. P(x) | Q ==> (EX x.P(x)) | Q";
val disj_exD2 = prove_fun "EX x. P | Q(x) ==> P | (EX x.Q(x))";


(*** Pushing in the universal quantifiers ***)

val null_allD = prove_fun "ALL x. P ==> P";

(** Conjunction **)

val conj_allD = prove_fun "ALL x. P(x) & Q(x) ==> (ALL x.P(x)) & (ALL x.Q(x))";
val conj_allD1 = prove_fun "ALL x. P(x) & Q ==> (ALL x.P(x)) & Q";
val conj_allD2 = prove_fun "ALL x. P & Q(x) ==> P & (ALL x.Q(x))";

(** Disjunction **)

val disj_allD1 = prove_fun "ALL x. P(x) | Q ==> (ALL x.P(x)) | Q";
val disj_allD2 = prove_fun "ALL x. P | Q(x) ==> P | (ALL x.Q(x))";


(**** Lemmas for forward proof (like congruence rules) ****)

(*NOTE: could handle conjunctions (faster?) by
    nf(th RS conjunct2) RS (nf(th RS conjunct1) RS conjI) *)
val major::prems = goal FOL.thy
    "[| P'&Q';  P' ==> P;  Q' ==> Q |] ==> P&Q";
by (rtac (major RS conjE) 1);
by (rtac conjI 1);
by (ALLGOALS (eresolve_tac prems));
val conj_forward = result();

val major::prems = goal FOL.thy
    "[| P'|Q';  P' ==> P;  Q' ==> Q |] ==> P|Q";
by (rtac (major RS disjE) 1);
by (ALLGOALS (dresolve_tac prems));
by (ALLGOALS (eresolve_tac [disjI1,disjI2]));
val disj_forward = result();

val major::prems = goal FOL.thy
    "[| ALL x. P'(x);  !!x. P'(x) ==> P(x) |] ==> ALL x. P(x)";
by (rtac allI 1);
by (resolve_tac prems 1);
by (rtac (major RS spec) 1);
val all_forward = result();

val major::prems = goal FOL.thy
    "[| EX x. P'(x);  !!x. P'(x) ==> P(x) |] ==> EX x. P(x)";
by (rtac (major RS exE) 1);
by (rtac exI 1);
by (eresolve_tac prems 1);
val ex_forward = result();


val mini_rls =
    [imp_to_disjD, iff_to_disjD, not_conjD, not_disjD,
     not_impD, not_iffD, not_allD, not_exD, not_notD,
     null_exD, conj_exD1, conj_exD2, disj_exD, disj_exD1, disj_exD2,
     null_allD, conj_allD, conj_allD1, conj_allD2, disj_allD1, disj_allD2];

val forward_rls = [conj_forward, disj_forward, all_forward, ex_forward];

(*** The transformation is done by forward proof: resolution.
     A tactic approach using dresolve_tac seems to be MUCH slower.
     The simplifier could compute nnf but not miniscope.
***)

(*Permits forward proof from rules that discharge assumptions*)
fun forward_res nf state =
  Sequence.hd
	(tapply(ALLGOALS (METAHYPS (fn [prem] => rtac (nf prem) 1)), 
		state));

(**** Operators for forward proof ****)

(*raises exception if no rules apply -- unlike RL*)
fun tryres (th, rl::rls) = (th RS rl handle THM _ => tryres(th,rls))
  | tryres (th, []) = raise THM("tryres", 0, [th]);

(*insert one destruction rule into the net*)
fun insert_D_rl (th, net) =
    Net.insert_term ((hd (prems_of th), th), net, K false);

fun net_tryres rls =
    let val net = foldr insert_D_rl (rls, Net.empty)
        fun tfun th = tryres (th, Net.unify_term net (concl_of th))
    in  tfun  end;

val try_mini    = net_tryres mini_rls
and try_forward = net_tryres forward_rls;

fun make_mini th = sub_mini (try_mini th)
    	handle THM _ => th
and sub_mini th = sub_mini (try_mini th)
	handle THM _ => make_mini (forward_res sub_mini (try_forward th))
	handle THM _ => th;

fun mini_tac prems = cut_facts_tac (map sub_mini prems);

fun MINI tac = SELECT_GOAL
 (EVERY1 [rtac ccontr,
	  METAHYPS (fn negs =>
		    EVERY1 [mini_tac negs, tac])]);

