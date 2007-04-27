(*  Title:      FOL/simpdata.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Simplification data for FOL.
*)

(*** Rewrite rules ***)

fun int_prove_fun s =
 (writeln s;
  prove_goal (theory "IFOL") s
   (fn prems => [ (cut_facts_tac prems 1),
                  (IntPr.fast_tac 1) ]));

bind_thms ("conj_simps", map int_prove_fun
 ["P & True <-> P",      "True & P <-> P",
  "P & False <-> False", "False & P <-> False",
  "P & P <-> P", "P & P & Q <-> P & Q",
  "P & ~P <-> False",    "~P & P <-> False",
  "(P & Q) & R <-> P & (Q & R)"]);

bind_thms ("disj_simps", map int_prove_fun
 ["P | True <-> True",  "True | P <-> True",
  "P | False <-> P",    "False | P <-> P",
  "P | P <-> P", "P | P | Q <-> P | Q",
  "(P | Q) | R <-> P | (Q | R)"]);

bind_thms ("not_simps", map int_prove_fun
 ["~(P|Q)  <-> ~P & ~Q",
  "~ False <-> True",   "~ True <-> False"]);

bind_thms ("imp_simps", map int_prove_fun
 ["(P --> False) <-> ~P",       "(P --> True) <-> True",
  "(False --> P) <-> True",     "(True --> P) <-> P",
  "(P --> P) <-> True",         "(P --> ~P) <-> ~P"]);

bind_thms ("iff_simps", map int_prove_fun
 ["(True <-> P) <-> P",         "(P <-> True) <-> P",
  "(P <-> P) <-> True",
  "(False <-> P) <-> ~P",       "(P <-> False) <-> ~P"]);

(*The x=t versions are needed for the simplification procedures*)
bind_thms ("quant_simps", map int_prove_fun
 ["(ALL x. P) <-> P",
  "(ALL x. x=t --> P(x)) <-> P(t)",
  "(ALL x. t=x --> P(x)) <-> P(t)",
  "(EX x. P) <-> P",
  "EX x. x=t", "EX x. t=x",
  "(EX x. x=t & P(x)) <-> P(t)",
  "(EX x. t=x & P(x)) <-> P(t)"]);

(*These are NOT supplied by default!*)
bind_thms ("distrib_simps", map int_prove_fun
 ["P & (Q | R) <-> P&Q | P&R",
  "(Q | R) & P <-> Q&P | R&P",
  "(P | Q --> R) <-> (P --> R) & (Q --> R)"]);

(** Conversion into rewrite rules **)

bind_thm ("P_iff_F", int_prove_fun "~P ==> (P <-> False)");
bind_thm ("iff_reflection_F", P_iff_F RS iff_reflection);

bind_thm ("P_iff_T", int_prove_fun "P ==> (P <-> True)");
bind_thm ("iff_reflection_T", P_iff_T RS iff_reflection);

(*Make meta-equalities.  The operator below is Trueprop*)

fun mk_meta_eq th = case concl_of th of
    _ $ (Const("op =",_)$_$_)   => th RS eq_reflection
  | _ $ (Const("op <->",_)$_$_) => th RS iff_reflection
  | _                           =>
  error("conclusion must be a =-equality or <->");;

fun mk_eq th = case concl_of th of
    Const("==",_)$_$_           => th
  | _ $ (Const("op =",_)$_$_)   => mk_meta_eq th
  | _ $ (Const("op <->",_)$_$_) => mk_meta_eq th
  | _ $ (Const("Not",_)$_)      => th RS iff_reflection_F
  | _                           => th RS iff_reflection_T;

(*Replace premises x=y, X<->Y by X==Y*)
val mk_meta_prems =
    rule_by_tactic
      (REPEAT_FIRST (resolve_tac [meta_eq_to_obj_eq, thm "def_imp_iff"]));

(*Congruence rules for = or <-> (instead of ==)*)
fun mk_meta_cong rl =
  standard(mk_meta_eq (mk_meta_prems rl))
  handle THM _ =>
  error("Premises and conclusion of congruence rules must use =-equality or <->");

val mksimps_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", [])];

(* ###FIXME: move to simplifier.ML
val mk_atomize:      (string * thm list) list -> thm -> thm list
*)
(* ###FIXME: move to simplifier.ML *)
fun mk_atomize pairs =
  let fun atoms th =
        (case concl_of th of
           Const("Trueprop",_) $ p =>
             (case head_of p of
                Const(a,_) =>
                  (case AList.lookup (op =) pairs a of
                     SOME(rls) => List.concat (map atoms ([th] RL rls))
                   | NONE => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

fun mksimps pairs = (map mk_eq o mk_atomize pairs o gen_all);

(*** Classical laws ***)

fun prove_fun s =
 (writeln s;
  prove_goal (the_context ()) s
   (fn prems => [ (cut_facts_tac prems 1),
                  (Cla.fast_tac FOL_cs 1) ]));

(*Avoids duplication of subgoals after expand_if, when the true and false
  cases boil down to the same thing.*)
bind_thm ("cases_simp", prove_fun "(P --> Q) & (~P --> Q) <-> Q");


(*** Miniscoping: pushing quantifiers in
     We do NOT distribute of ALL over &, or dually that of EX over |
     Baaz and Leitsch, On Skolemization and Proof Complexity (1994)
     show that this step can increase proof length!
***)

(*existential miniscoping*)
bind_thms ("int_ex_simps", map int_prove_fun
 ["(EX x. P(x) & Q) <-> (EX x. P(x)) & Q",
  "(EX x. P & Q(x)) <-> P & (EX x. Q(x))",
  "(EX x. P(x) | Q) <-> (EX x. P(x)) | Q",
  "(EX x. P | Q(x)) <-> P | (EX x. Q(x))"]);

(*classical rules*)
bind_thms ("cla_ex_simps", map prove_fun
 ["(EX x. P(x) --> Q) <-> (ALL x. P(x)) --> Q",
  "(EX x. P --> Q(x)) <-> P --> (EX x. Q(x))"]);

bind_thms ("ex_simps", int_ex_simps @ cla_ex_simps);

(*universal miniscoping*)
bind_thms ("int_all_simps", map int_prove_fun
 ["(ALL x. P(x) & Q) <-> (ALL x. P(x)) & Q",
  "(ALL x. P & Q(x)) <-> P & (ALL x. Q(x))",
  "(ALL x. P(x) --> Q) <-> (EX x. P(x)) --> Q",
  "(ALL x. P --> Q(x)) <-> P --> (ALL x. Q(x))"]);

(*classical rules*)
bind_thms ("cla_all_simps", map prove_fun
 ["(ALL x. P(x) | Q) <-> (ALL x. P(x)) | Q",
  "(ALL x. P | Q(x)) <-> P | (ALL x. Q(x))"]);

bind_thms ("all_simps", int_all_simps @ cla_all_simps);


(*** Named rewrite rules proved for IFOL ***)

fun int_prove nm thm  = qed_goal nm (theory "IFOL") thm
    (fn prems => [ (cut_facts_tac prems 1),
                   (IntPr.fast_tac 1) ]);

fun prove nm thm  = qed_goal nm (the_context ()) thm (fn _ => [Blast_tac 1]);

int_prove "conj_commute" "P&Q <-> Q&P";
int_prove "conj_left_commute" "P&(Q&R) <-> Q&(P&R)";
bind_thms ("conj_comms", [conj_commute, conj_left_commute]);

int_prove "disj_commute" "P|Q <-> Q|P";
int_prove "disj_left_commute" "P|(Q|R) <-> Q|(P|R)";
bind_thms ("disj_comms", [disj_commute, disj_left_commute]);

int_prove "conj_disj_distribL" "P&(Q|R) <-> (P&Q | P&R)";
int_prove "conj_disj_distribR" "(P|Q)&R <-> (P&R | Q&R)";

int_prove "disj_conj_distribL" "P|(Q&R) <-> (P|Q) & (P|R)";
int_prove "disj_conj_distribR" "(P&Q)|R <-> (P|R) & (Q|R)";

int_prove "imp_conj_distrib" "(P --> (Q&R)) <-> (P-->Q) & (P-->R)";
int_prove "imp_conj"         "((P&Q)-->R)   <-> (P --> (Q --> R))";
int_prove "imp_disj"         "(P|Q --> R)   <-> (P-->R) & (Q-->R)";

prove "imp_disj1" "(P-->Q) | R <-> (P-->Q | R)";
prove "imp_disj2" "Q | (P-->R) <-> (P-->Q | R)";

int_prove "de_Morgan_disj" "(~(P | Q)) <-> (~P & ~Q)";
prove     "de_Morgan_conj" "(~(P & Q)) <-> (~P | ~Q)";

prove     "not_imp" "~(P --> Q) <-> (P & ~Q)";
prove     "not_iff" "~(P <-> Q) <-> (P <-> ~Q)";

prove     "not_all" "(~ (ALL x. P(x))) <-> (EX x.~P(x))";
prove     "imp_all" "((ALL x. P(x)) --> Q) <-> (EX x. P(x) --> Q)";
int_prove "not_ex"  "(~ (EX x. P(x))) <-> (ALL x.~P(x))";
int_prove "imp_ex" "((EX x. P(x)) --> Q) <-> (ALL x. P(x) --> Q)";

int_prove "ex_disj_distrib"
    "(EX x. P(x) | Q(x)) <-> ((EX x. P(x)) | (EX x. Q(x)))";
int_prove "all_conj_distrib"
    "(ALL x. P(x) & Q(x)) <-> ((ALL x. P(x)) & (ALL x. Q(x)))";


(** make simplification procedures for quantifier elimination **)
structure Quantifier1 = Quantifier1Fun(
struct
  (*abstract syntax*)
  fun dest_eq((c as Const("op =",_)) $ s $ t) = SOME(c,s,t)
    | dest_eq _ = NONE;
  fun dest_conj((c as Const("op &",_)) $ s $ t) = SOME(c,s,t)
    | dest_conj _ = NONE;
  fun dest_imp((c as Const("op -->",_)) $ s $ t) = SOME(c,s,t)
    | dest_imp _ = NONE;
  val conj = FOLogic.conj
  val imp  = FOLogic.imp
  (*rules*)
  val iff_reflection = iff_reflection
  val iffI = iffI
  val iff_trans = iff_trans
  val conjI= conjI
  val conjE= conjE
  val impI = impI
  val mp   = mp
  val uncurry = thm "uncurry"
  val exI  = exI
  val exE  = exE
  val iff_allI = thm "iff_allI"
  val iff_exI = thm "iff_exI"
  val all_comm = thm "all_comm"
  val ex_comm = thm "ex_comm"
end);

val defEX_regroup =
  Simplifier.simproc (the_context ())
    "defined EX" ["EX x. P(x)"] Quantifier1.rearrange_ex;

val defALL_regroup =
  Simplifier.simproc (the_context ())
    "defined ALL" ["ALL x. P(x)"] Quantifier1.rearrange_all;


(*** Case splitting ***)

structure SplitterData =
  struct
  structure Simplifier = Simplifier
  val mk_eq          = mk_eq
  val meta_eq_to_iff = meta_eq_to_iff
  val iffD           = iffD2
  val disjE          = disjE
  val conjE          = conjE
  val exE            = exE
  val contrapos      = thm "contrapos"
  val contrapos2     = thm "contrapos2"
  val notnotD        = thm "notnotD"
  end;

structure Splitter = SplitterFun(SplitterData);

val split_tac        = Splitter.split_tac;
val split_inside_tac = Splitter.split_inside_tac;
val split_asm_tac    = Splitter.split_asm_tac;
val op addsplits     = Splitter.addsplits;
val op delsplits     = Splitter.delsplits;
val Addsplits        = Splitter.Addsplits;
val Delsplits        = Splitter.Delsplits;


(*** Standard simpsets ***)

bind_thms ("meta_simps",
 [triv_forall_equality,   (* prunes params *)
  thm "True_implies_equals"]);  (* prune asms `True' *)

bind_thms ("IFOL_simps",
 [refl RS P_iff_T] @ conj_simps @ disj_simps @ not_simps @
  imp_simps @ iff_simps @ quant_simps);

bind_thm ("notFalseI", int_prove_fun "~False");
bind_thms ("triv_rls",
  [TrueI, refl, reflexive_thm, iff_refl, thm "notFalseI"]);

fun unsafe_solver prems = FIRST'[resolve_tac (triv_rls@prems),
                                 atac, etac FalseE];
(*No premature instantiation of variables during simplification*)
fun   safe_solver prems = FIRST'[match_tac (triv_rls@prems),
                                 eq_assume_tac, ematch_tac [FalseE]];

(*No simprules, but basic infastructure for simplification*)
val FOL_basic_ss =
  Simplifier.theory_context (the_context ()) empty_ss
  setsubgoaler asm_simp_tac
  setSSolver (mk_solver "FOL safe" safe_solver)
  setSolver (mk_solver "FOL unsafe" unsafe_solver)
  setmksimps (mksimps mksimps_pairs)
  setmkcong mk_meta_cong;

fun unfold_tac ths =
  let val ss0 = Simplifier.clear_ss FOL_basic_ss addsimps ths
  in fn ss => ALLGOALS (full_simp_tac (Simplifier.inherit_context ss ss0)) end;


(*intuitionistic simprules only*)
val IFOL_ss =
  FOL_basic_ss
  addsimps (meta_simps @ IFOL_simps @ int_ex_simps @ int_all_simps)
  addsimprocs [defALL_regroup, defEX_regroup]    
  addcongs [thm "imp_cong"];

bind_thms ("cla_simps",
  [de_Morgan_conj, de_Morgan_disj, imp_disj1, imp_disj2,
   not_imp, not_all, not_ex, cases_simp] @
  map prove_fun
   ["~(P&Q) <-> ~P | ~Q",
    "P | ~P",             "~P | P",
    "~ ~ P <-> P",        "(~P --> P) <-> P",
    "(~P <-> ~Q) <-> (P<->Q)"]);

(*classical simprules too*)
val FOL_ss = IFOL_ss addsimps (cla_simps @ cla_ex_simps @ cla_all_simps);

val simpsetup = (fn thy => (change_simpset_of thy (fn _ => FOL_ss); thy));


(*** integration of simplifier with classical reasoner ***)

structure Clasimp = ClasimpFun
 (structure Simplifier = Simplifier and Splitter = Splitter
  and Classical  = Cla and Blast = Blast
  val iffD1 = iffD1 val iffD2 = iffD2 val notE = notE);
open Clasimp;

ML_Context.value_antiq "clasimpset"
  (Scan.succeed ("clasimpset", "Clasimp.local_clasimpset_of (ML_Context.the_local_context ())"));

val FOL_css = (FOL_cs, FOL_ss);
