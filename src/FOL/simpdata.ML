(*  Title:      FOL/simpdata.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Simplification data for FOL.
*)


(* Elimination of True from asumptions: *)

val True_implies_equals = prove_goal IFOL.thy
 "(True ==> PROP P) == PROP P"
(K [rtac equal_intr_rule 1, atac 2,
          METAHYPS (fn prems => resolve_tac prems 1) 1,
          rtac TrueI 1]);


(*** Rewrite rules ***)

fun int_prove_fun s = 
 (writeln s;  
  prove_goal IFOL.thy s
   (fn prems => [ (cut_facts_tac prems 1), 
                  (IntPr.fast_tac 1) ]));

val conj_simps = map int_prove_fun
 ["P & True <-> P",      "True & P <-> P",
  "P & False <-> False", "False & P <-> False",
  "P & P <-> P", "P & P & Q <-> P & Q",
  "P & ~P <-> False",    "~P & P <-> False",
  "(P & Q) & R <-> P & (Q & R)"];

val disj_simps = map int_prove_fun
 ["P | True <-> True",  "True | P <-> True",
  "P | False <-> P",    "False | P <-> P",
  "P | P <-> P", "P | P | Q <-> P | Q",
  "(P | Q) | R <-> P | (Q | R)"];

val not_simps = map int_prove_fun
 ["~(P|Q)  <-> ~P & ~Q",
  "~ False <-> True",   "~ True <-> False"];

val imp_simps = map int_prove_fun
 ["(P --> False) <-> ~P",       "(P --> True) <-> True",
  "(False --> P) <-> True",     "(True --> P) <-> P", 
  "(P --> P) <-> True",         "(P --> ~P) <-> ~P"];

val iff_simps = map int_prove_fun
 ["(True <-> P) <-> P",         "(P <-> True) <-> P",
  "(P <-> P) <-> True",
  "(False <-> P) <-> ~P",       "(P <-> False) <-> ~P"];

(*The x=t versions are needed for the simplification procedures*)
val quant_simps = map int_prove_fun
 ["(ALL x. P) <-> P",   
  "(ALL x. x=t --> P(x)) <-> P(t)",
  "(ALL x. t=x --> P(x)) <-> P(t)",
  "(EX x. P) <-> P",
  "(EX x. x=t & P(x)) <-> P(t)", 
  "(EX x. t=x & P(x)) <-> P(t)"];

(*These are NOT supplied by default!*)
val distrib_simps  = map int_prove_fun
 ["P & (Q | R) <-> P&Q | P&R", 
  "(Q | R) & P <-> Q&P | R&P",
  "(P | Q --> R) <-> (P --> R) & (Q --> R)"];

(** Conversion into rewrite rules **)

fun gen_all th = forall_elim_vars (#maxidx(rep_thm th)+1) th;

val P_iff_F = int_prove_fun "~P ==> (P <-> False)";
val iff_reflection_F = P_iff_F RS iff_reflection;

val P_iff_T = int_prove_fun "P ==> (P <-> True)";
val iff_reflection_T = P_iff_T RS iff_reflection;

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
      (REPEAT_FIRST (resolve_tac [meta_eq_to_obj_eq, def_imp_iff]));

(*Congruence rules for = or <-> (instead of ==)*)
fun mk_meta_cong rl =
  standard(mk_meta_eq (mk_meta_prems rl))
  handle THM _ =>
  error("Premises and conclusion of congruence rules must use =-equality or <->");

val mksimps_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", [])];

(* ###FIXME: move to Provers/simplifier.ML
val mk_atomize:      (string * thm list) list -> thm -> thm list
*)
(* ###FIXME: move to Provers/simplifier.ML *)
fun mk_atomize pairs =
  let fun atoms th =
        (case concl_of th of
           Const("Trueprop",_) $ p =>
             (case head_of p of
                Const(a,_) =>
                  (case assoc(pairs,a) of
                     Some(rls) => flat (map atoms ([th] RL rls))
                   | None => [th])
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
val cases_simp = prove_fun "(P --> Q) & (~P --> Q) <-> Q";


(*** Miniscoping: pushing quantifiers in
     We do NOT distribute of ALL over &, or dually that of EX over |
     Baaz and Leitsch, On Skolemization and Proof Complexity (1994) 
     show that this step can increase proof length!
***)

(*existential miniscoping*)
val int_ex_simps = map int_prove_fun 
                     ["(EX x. P(x) & Q) <-> (EX x. P(x)) & Q",
                      "(EX x. P & Q(x)) <-> P & (EX x. Q(x))",
                      "(EX x. P(x) | Q) <-> (EX x. P(x)) | Q",
                      "(EX x. P | Q(x)) <-> P | (EX x. Q(x))"];

(*classical rules*)
val cla_ex_simps = map prove_fun 
                     ["(EX x. P(x) --> Q) <-> (ALL x. P(x)) --> Q",
                      "(EX x. P --> Q(x)) <-> P --> (EX x. Q(x))"];

val ex_simps = int_ex_simps @ cla_ex_simps;

(*universal miniscoping*)
val int_all_simps = map int_prove_fun
                      ["(ALL x. P(x) & Q) <-> (ALL x. P(x)) & Q",
                       "(ALL x. P & Q(x)) <-> P & (ALL x. Q(x))",
                       "(ALL x. P(x) --> Q) <-> (EX x. P(x)) --> Q",
                       "(ALL x. P --> Q(x)) <-> P --> (ALL x. Q(x))"];

(*classical rules*)
val cla_all_simps = map prove_fun
                      ["(ALL x. P(x) | Q) <-> (ALL x. P(x)) | Q",
                       "(ALL x. P | Q(x)) <-> P | (ALL x. Q(x))"];

val all_simps = int_all_simps @ cla_all_simps;


(*** Named rewrite rules proved for IFOL ***)

fun int_prove nm thm  = qed_goal nm IFOL.thy thm
    (fn prems => [ (cut_facts_tac prems 1), 
                   (IntPr.fast_tac 1) ]);

fun prove nm thm  = qed_goal nm (the_context ()) thm (fn _ => [Blast_tac 1]);

int_prove "conj_commute" "P&Q <-> Q&P";
int_prove "conj_left_commute" "P&(Q&R) <-> Q&(P&R)";
val conj_comms = [conj_commute, conj_left_commute];

int_prove "disj_commute" "P|Q <-> Q|P";
int_prove "disj_left_commute" "P|(Q|R) <-> Q|(P|R)";
val disj_comms = [disj_commute, disj_left_commute];

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
  fun dest_eq((c as Const("op =",_)) $ s $ t) = Some(c,s,t)
    | dest_eq _ = None;
  fun dest_conj((c as Const("op &",_)) $ s $ t) = Some(c,s,t)
    | dest_conj _ = None;
  val conj = FOLogic.conj
  val imp  = FOLogic.imp
  (*rules*)
  val iff_reflection = iff_reflection
  val iffI = iffI
  val sym  = sym
  val conjI= conjI
  val conjE= conjE
  val impI = impI
  val impE = impE
  val mp   = mp
  val exI  = exI
  val exE  = exE
  val allI = allI
  val allE = allE
end);

local

val ex_pattern =
  read_cterm (Theory.sign_of (the_context ())) ("EX x. P(x) & Q(x)", FOLogic.oT)

val all_pattern =
  read_cterm (Theory.sign_of (the_context ())) ("ALL x. P(x) & P'(x) --> Q(x)", FOLogic.oT)

in
val defEX_regroup =
  mk_simproc "defined EX" [ex_pattern] Quantifier1.rearrange_ex;
val defALL_regroup =
  mk_simproc "defined ALL" [all_pattern] Quantifier1.rearrange_all;
end;


(*** Case splitting ***)

val meta_eq_to_iff = prove_goal IFOL.thy "x==y ==> x<->y"
  (fn [prem] => [rewtac prem, rtac iffI 1, atac 1, atac 1]);

structure SplitterData =
  struct
  structure Simplifier = Simplifier
  val mk_eq          = mk_eq
  val meta_eq_to_iff = meta_eq_to_iff
  val iffD           = iffD2
  val disjE          = disjE
  val conjE          = conjE
  val exE            = exE
  val contrapos      = contrapos
  val contrapos2     = contrapos2
  val notnotD        = notnotD
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

structure Induction = InductionFun(struct val spec=IFOL.spec end);

open Induction;


val meta_simps =
   [triv_forall_equality,  (* prunes params *)
    True_implies_equals];  (* prune asms `True' *)

val IFOL_simps =
    [refl RS P_iff_T] @ conj_simps @ disj_simps @ not_simps @ 
    imp_simps @ iff_simps @ quant_simps;

val notFalseI = int_prove_fun "~False";
val triv_rls = [TrueI,refl,reflexive_thm,iff_refl,notFalseI];

fun unsafe_solver prems = FIRST'[resolve_tac (triv_rls@prems),
                                 atac, etac FalseE];
(*No premature instantiation of variables during simplification*)
fun   safe_solver prems = FIRST'[match_tac (triv_rls@prems),
                                 eq_assume_tac, ematch_tac [FalseE]];

(*No simprules, but basic infastructure for simplification*)
val FOL_basic_ss =
  empty_ss setsubgoaler asm_simp_tac
    addsimprocs [defALL_regroup, defEX_regroup]
    setSSolver (mk_solver "FOL safe" safe_solver)
    setSolver (mk_solver "FOL unsafe" unsafe_solver)
    setmksimps (mksimps mksimps_pairs)
    setmkcong mk_meta_cong;


(*intuitionistic simprules only*)
val IFOL_ss =
    FOL_basic_ss addsimps (meta_simps @ IFOL_simps @
                           int_ex_simps @ int_all_simps)
                 addcongs [imp_cong];

val cla_simps =
    [de_Morgan_conj, de_Morgan_disj, imp_disj1, imp_disj2,
     not_all, not_ex, cases_simp] @
    map prove_fun
     ["~(P&Q)  <-> ~P | ~Q",
      "P | ~P",             "~P | P",
      "~ ~ P <-> P",        "(~P --> P) <-> P",
      "(~P <-> ~Q) <-> (P<->Q)"];

(*classical simprules too*)
val FOL_ss = IFOL_ss addsimps (cla_simps @ cla_ex_simps @ cla_all_simps);

val simpsetup = [fn thy => (simpset_ref_of thy := FOL_ss; thy)];


(*** integration of simplifier with classical reasoner ***)

structure Clasimp = ClasimpFun
 (structure Simplifier = Simplifier and Splitter = Splitter
  and Classical  = Cla and Blast = Blast
  val dest_Trueprop = FOLogic.dest_Trueprop
  val iff_const = FOLogic.iff val not_const = FOLogic.not
  val notE = notE val iffD1 = iffD1 val iffD2 = iffD2
  val cla_make_elim = cla_make_elim);
open Clasimp;

val FOL_css = (FOL_cs, FOL_ss);


(* rulify setup *)

local
  val ss = FOL_basic_ss addsimps (Drule.norm_hhf_eq :: map Thm.symmetric (thms "atomize"));
in

structure Rulify = RulifyFun
 (val make_meta = Simplifier.simplify ss
  val full_make_meta = Simplifier.full_simplify ss);

structure BasicRulify: BASIC_RULIFY = Rulify;
open BasicRulify;

end;
