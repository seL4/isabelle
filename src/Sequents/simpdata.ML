(*  Title:      Sequents/simpdata.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Instantiation of the generic simplifier for LK

Borrows from the DC simplifier of Soren Heilmann.

MAJOR LIMITATION: left-side sequent formulae are not added to the simpset.
  However, congruence rules for --> and & are available.
  The rule backwards_impR can be used to convert assumptions into right-side
  implications.
*)

(*** Rewrite rules ***)

fun prove_fun s = 
 (writeln s;  
  prove_goal LK.thy s
   (fn prems => [ (cut_facts_tac prems 1), 
                  (fast_tac LK_pack 1) ]));

val conj_simps = map prove_fun
 ["|- P & True <-> P",      "|- True & P <-> P",
  "|- P & False <-> False", "|- False & P <-> False",
  "|- P & P <-> P", "        |- P & P & Q <-> P & Q",
  "|- P & ~P <-> False",    "|- ~P & P <-> False",
  "|- (P & Q) & R <-> P & (Q & R)"];

val disj_simps = map prove_fun
 ["|- P | True <-> True",  "|- True | P <-> True",
  "|- P | False <-> P",    "|- False | P <-> P",
  "|- P | P <-> P",        "|- P | P | Q <-> P | Q",
  "|- (P | Q) | R <-> P | (Q | R)"];

val not_simps = map prove_fun
 ["|- ~ False <-> True",   "|- ~ True <-> False"];

val imp_simps = map prove_fun
 ["|- (P --> False) <-> ~P",       "|- (P --> True) <-> True",
  "|- (False --> P) <-> True",     "|- (True --> P) <-> P", 
  "|- (P --> P) <-> True",         "|- (P --> ~P) <-> ~P"];

val iff_simps = map prove_fun
 ["|- (True <-> P) <-> P",         "|- (P <-> True) <-> P",
  "|- (P <-> P) <-> True",
  "|- (False <-> P) <-> ~P",       "|- (P <-> False) <-> ~P"];

(*These are NOT supplied by default!*)
val distrib_simps  = map prove_fun
 ["|- P & (Q | R) <-> P&Q | P&R", 
  "|- (Q | R) & P <-> Q&P | R&P",
  "|- (P | Q --> R) <-> (P --> R) & (Q --> R)"];

(** Conversion into rewrite rules **)

fun gen_all th = forall_elim_vars (#maxidx(rep_thm th)+1) th;


(*Make atomic rewrite rules*)
fun atomize r =
 case concl_of r of
   Const("Trueprop",_) $ Abs(_,_,a) $ Abs(_,_,c) =>
     (case (forms_of_seq a, forms_of_seq c) of
	([], [p]) =>
	  (case p of
	       Const("op -->",_)$_$_ => atomize(r RS mp_R)
	     | Const("op &",_)$_$_   => atomize(r RS conjunct1) @
		   atomize(r RS conjunct2)
	     | Const("All",_)$_      => atomize(r RS spec)
	     | Const("True",_)       => []    (*True is DELETED*)
	     | Const("False",_)      => []    (*should False do something?*)
	     | _                     => [r])
      | _ => [])  (*ignore theorem unless it has precisely one conclusion*)
 | _ => [r];


qed_goal "P_iff_F" LK.thy "|- ~P ==> |- (P <-> False)"
    (fn prems => [lemma_tac (hd prems) 1, fast_tac LK_pack 1]);
val iff_reflection_F = P_iff_F RS iff_reflection;

qed_goal "P_iff_T" LK.thy "|- P ==> |- (P <-> True)"
    (fn prems => [lemma_tac (hd prems) 1, fast_tac LK_pack 1]);
val iff_reflection_T = P_iff_T RS iff_reflection;

(*Make meta-equalities.*)
fun mk_meta_eq th = case concl_of th of
    Const("==",_)$_$_           => th
  | Const("Trueprop",_) $ Abs(_,_,a) $ Abs(_,_,c) =>
	(case (forms_of_seq a, forms_of_seq c) of
	     ([], [p]) => 
		 (case p of
		      (Const("op =",_)$_$_)   => th RS eq_reflection
		    | (Const("op <->",_)$_$_) => th RS iff_reflection
		    | (Const("Not",_)$_)      => th RS iff_reflection_F
		    | _                       => th RS iff_reflection_T)
	   | _ => error ("addsimps: unable to use theorem\n" ^
			 string_of_thm th));


(*** Named rewrite rules proved for PL ***)

fun prove nm thm  = qed_goal nm LK.thy thm
    (fn prems => [ (cut_facts_tac prems 1), 
                   (fast_tac LK_pack 1) ]);

prove "conj_commute" "|- P&Q <-> Q&P";
prove "conj_left_commute" "|- P&(Q&R) <-> Q&(P&R)";
val conj_comms = [conj_commute, conj_left_commute];

prove "disj_commute" "|- P|Q <-> Q|P";
prove "disj_left_commute" "|- P|(Q|R) <-> Q|(P|R)";
val disj_comms = [disj_commute, disj_left_commute];

prove "conj_disj_distribL" "|- P&(Q|R) <-> (P&Q | P&R)";
prove "conj_disj_distribR" "|- (P|Q)&R <-> (P&R | Q&R)";

prove "disj_conj_distribL" "|- P|(Q&R) <-> (P|Q) & (P|R)";
prove "disj_conj_distribR" "|- (P&Q)|R <-> (P|R) & (Q|R)";

prove "imp_conj_distrib" "|- (P --> (Q&R)) <-> (P-->Q) & (P-->R)";
prove "imp_conj"         "|- ((P&Q)-->R)   <-> (P --> (Q --> R))";
prove "imp_disj"         "|- (P|Q --> R)   <-> (P-->R) & (Q-->R)";

prove "imp_disj1" "|- (P-->Q) | R <-> (P-->Q | R)";
prove "imp_disj2" "|- Q | (P-->R) <-> (P-->Q | R)";

prove "de_Morgan_disj" "|- (~(P | Q)) <-> (~P & ~Q)";
prove "de_Morgan_conj" "|- (~(P & Q)) <-> (~P | ~Q)";

prove "not_iff" "|- ~(P <-> Q) <-> (P <-> ~Q)";

prove "iff_refl" "|- (P <-> P)";


val [p1,p2] = Goal 
    "[| |- P <-> P';  |- P' ==> |- Q <-> Q' |] ==> |- (P-->Q) <-> (P'-->Q')";
by (lemma_tac p1 1);
by (Safe_tac 1);
by (REPEAT (rtac cut 1 
	    THEN
	    DEPTH_SOLVE_1 (resolve_tac [thinL, thinR, p2 COMP monotonic] 1)
	    THEN
	    Safe_tac 1));
qed "imp_cong";

val [p1,p2] = Goal 
    "[| |- P <-> P';  |- P' ==> |- Q <-> Q' |] ==> |- (P&Q) <-> (P'&Q')";
by (lemma_tac p1 1);
by (Safe_tac 1);
by (REPEAT (rtac cut 1 
	    THEN
	    DEPTH_SOLVE_1 (resolve_tac [thinL, thinR, p2 COMP monotonic] 1)
	    THEN
	    Safe_tac 1));
qed "conj_cong";


open Simplifier;

(*** Standard simpsets ***)

(*Add congruence rules for = or <-> (instead of ==) *)
infix 4 addcongs delcongs;
fun ss addcongs congs =
        ss addeqcongs (map standard (congs RL [eq_reflection,iff_reflection]));
fun ss delcongs congs =
        ss deleqcongs (map standard (congs RL [eq_reflection,iff_reflection]));

fun Addcongs congs = (simpset_ref() := simpset() addcongs congs);
fun Delcongs congs = (simpset_ref() := simpset() delcongs congs);

val triv_rls = [FalseL, TrueR, basic, refl, iff_refl];

fun unsafe_solver prems = FIRST'[resolve_tac (triv_rls@prems),
				 assume_tac];
(*No premature instantiation of variables during simplification*)
fun   safe_solver prems = FIRST'[fn i => DETERM (match_tac (triv_rls@prems) i),
				 eq_assume_tac];

(*No simprules, but basic infrastructure for simplification*)
val LK_basic_ss = empty_ss setsubgoaler asm_simp_tac
			   setSSolver   safe_solver
			   setSolver    unsafe_solver
			   setmksimps   (map mk_meta_eq o atomize o gen_all);

val LK_simps =
   [refl RS P_iff_T] @ conj_simps @ disj_simps @ not_simps @ 
    imp_simps @ iff_simps @
    [de_Morgan_conj, de_Morgan_disj, imp_disj1, imp_disj2] @
    map prove_fun
     ["|- P | ~P",             "|- ~P | P",
      "|- ~ ~ P <-> P",        "|- (~P --> P) <-> P",
      "|- (~P <-> ~Q) <-> (P<->Q)"];

val LK_ss = LK_basic_ss addsimps LK_simps addcongs [imp_cong];

simpset_ref() := LK_ss;


(* Subst rule *)

qed_goal "subst" LK.thy "|- a=b ==> $H, A(a), $G |- $E, A(b), $F"
  (fn prems =>
   [cut_facts_tac prems 1,
    asm_simp_tac LK_basic_ss 1]);


