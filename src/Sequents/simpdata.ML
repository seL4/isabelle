(*  Title:      Sequents/simpdata.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Instantiation of the generic simplifier for LK

Borrows from the DC simplifier of Soren Heilmann.
*)

(*** Rewrite rules ***)

fun prove_fun s =
 (writeln s;
  prove_goal LK.thy s
   (fn prems => [ (cut_facts_tac prems 1),
                  (fast_tac (pack() add_safes [subst]) 1) ]));

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


val quant_simps = map prove_fun
 ["|- (ALL x. P) <-> P",
  "|- (ALL x. x=t --> P(x)) <-> P(t)",
  "|- (ALL x. t=x --> P(x)) <-> P(t)",
  "|- (EX x. P) <-> P",
  "|- (EX x. x=t & P(x)) <-> P(t)",
  "|- (EX x. t=x & P(x)) <-> P(t)"];

(*** Miniscoping: pushing quantifiers in
     We do NOT distribute of ALL over &, or dually that of EX over |
     Baaz and Leitsch, On Skolemization and Proof Complexity (1994)
     show that this step can increase proof length!
***)

(*existential miniscoping*)
val ex_simps = map prove_fun
                   ["|- (EX x. P(x) & Q) <-> (EX x. P(x)) & Q",
                    "|- (EX x. P & Q(x)) <-> P & (EX x. Q(x))",
                    "|- (EX x. P(x) | Q) <-> (EX x. P(x)) | Q",
                    "|- (EX x. P | Q(x)) <-> P | (EX x. Q(x))",
                    "|- (EX x. P(x) --> Q) <-> (ALL x. P(x)) --> Q",
                    "|- (EX x. P --> Q(x)) <-> P --> (EX x. Q(x))"];

(*universal miniscoping*)
val all_simps = map prove_fun
                    ["|- (ALL x. P(x) & Q) <-> (ALL x. P(x)) & Q",
                     "|- (ALL x. P & Q(x)) <-> P & (ALL x. Q(x))",
                     "|- (ALL x. P(x) --> Q) <-> (EX x. P(x)) --> Q",
                     "|- (ALL x. P --> Q(x)) <-> P --> (ALL x. Q(x))",
                     "|- (ALL x. P(x) | Q) <-> (ALL x. P(x)) | Q",
                     "|- (ALL x. P | Q(x)) <-> P | (ALL x. Q(x))"];

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


Goal "|- ~P ==> |- (P <-> False)";
by (etac (thinR RS cut) 1);
by (Fast_tac 1);
qed "P_iff_F";

val iff_reflection_F = P_iff_F RS iff_reflection;

Goal "|- P ==> |- (P <-> True)";
by (etac (thinR RS cut) 1);
by (Fast_tac 1);
qed "P_iff_T";

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


(*Replace premises x=y, X<->Y by X==Y*)
val mk_meta_prems =
    rule_by_tactic
      (REPEAT_FIRST (resolve_tac [meta_eq_to_obj_eq, def_imp_iff]));

(*Congruence rules for = or <-> (instead of ==)*)
fun mk_meta_cong rl =
  standard(mk_meta_eq (mk_meta_prems rl))
  handle THM _ =>
  error("Premises and conclusion of congruence rules must use =-equality or <->");


(*** Named rewrite rules ***)

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

Goal "|- (x=y) <-> (y=x)";
by (fast_tac (pack() add_safes [subst]) 1);
qed "eq_sym_conv";


(** if-then-else rules **)

Goalw [If_def] "|- (if True then x else y) = x";
by (Fast_tac 1);
qed "if_True";

Goalw [If_def] "|- (if False then x else y) = y";
by (Fast_tac 1);
qed "if_False";

Goalw [If_def] "|- P ==> |- (if P then x else y) = x";
by (etac (thinR RS cut) 1);
by (Fast_tac 1);
qed "if_P";

Goalw [If_def] "|- ~P ==> |- (if P then x else y) = y";
by (etac (thinR RS cut) 1);
by (Fast_tac 1);
qed "if_not_P";


open Simplifier;

(*** Standard simpsets ***)

val triv_rls = [FalseL, TrueR, basic, refl, iff_refl, reflexive_thm];

fun unsafe_solver prems = FIRST'[resolve_tac (triv_rls@prems),
                                 assume_tac];
(*No premature instantiation of variables during simplification*)
fun   safe_solver prems = FIRST'[fn i => DETERM (match_tac (triv_rls@prems) i),
                                 eq_assume_tac];

(*No simprules, but basic infrastructure for simplification*)
val LK_basic_ss =
  empty_ss setsubgoaler asm_simp_tac
    setSSolver (mk_solver "safe" safe_solver)
    setSolver (mk_solver "unsafe" unsafe_solver)
    setmksimps (map mk_meta_eq o atomize o gen_all)
    setmkcong mk_meta_cong;

val LK_simps =
   [triv_forall_equality, (* prunes params *)
    refl RS P_iff_T] @
    conj_simps @ disj_simps @ not_simps @
    imp_simps @ iff_simps @quant_simps @ all_simps @ ex_simps @
    [de_Morgan_conj, de_Morgan_disj, imp_disj1, imp_disj2] @
    map prove_fun
     ["|- P | ~P",             "|- ~P | P",
      "|- ~ ~ P <-> P",        "|- (~P --> P) <-> P",
      "|- (~P <-> ~Q) <-> (P<->Q)"];

val LK_ss =
  LK_basic_ss addsimps LK_simps
  addeqcongs [left_cong]
  addcongs [imp_cong];

simpset_ref() := LK_ss;


(* To create substition rules *)

qed_goal "eq_imp_subst" LK.thy "|- a=b ==> $H, A(a), $G |- $E, A(b), $F"
  (fn prems =>
   [cut_facts_tac prems 1,
    asm_simp_tac LK_basic_ss 1]);

Goal "|- P(if Q then x else y) <-> ((Q --> P(x)) & (~Q --> P(y)))";
by (res_inst_tac [ ("P","Q") ] cut 1);
by (simp_tac (simpset() addsimps [if_P]) 2);
by (res_inst_tac [ ("P","~Q") ] cut 1);
by (simp_tac (simpset() addsimps [if_not_P]) 2);
by (Fast_tac 1);
qed "split_if";

Goal "|- (if P then x else x) = x";
by (lemma_tac split_if 1);
by (Fast_tac 1);
qed "if_cancel";

Goal "|- (if x=y then y else x) = x";
by (lemma_tac split_if 1);
by (Safe_tac 1);
by (rtac symL 1);
by (rtac basic 1);
qed "if_eq_cancel";

(*Putting in automatic case splits seems to require a lot of work.*)
