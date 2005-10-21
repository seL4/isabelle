(*  Title:      Pure/simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics (see also
meta_simplifier.ML for the actual meta-level rewriting engine).
*)

signature BASIC_SIMPLIFIER =
sig
  include BASIC_META_SIMPLIFIER
  val print_simpset: theory -> unit
  val change_simpset_of: theory -> (simpset -> simpset) -> unit
  val change_simpset: (simpset -> simpset) -> unit
  val simpset_of: theory -> simpset
  val simpset: unit -> simpset
  val SIMPSET: (simpset -> tactic) -> tactic
  val SIMPSET': (simpset -> 'a -> tactic) -> 'a -> tactic
  val Addsimps: thm list -> unit
  val Delsimps: thm list -> unit
  val Addsimprocs: simproc list -> unit
  val Delsimprocs: simproc list -> unit
  val Addcongs: thm list -> unit
  val Delcongs: thm list -> unit
  val local_simpset_of: Proof.context -> simpset
  val generic_simp_tac: bool -> bool * bool * bool -> simpset -> int -> tactic
  val safe_asm_full_simp_tac: simpset -> int -> tactic
  val               simp_tac: simpset -> int -> tactic
  val           asm_simp_tac: simpset -> int -> tactic
  val          full_simp_tac: simpset -> int -> tactic
  val        asm_lr_simp_tac: simpset -> int -> tactic
  val      asm_full_simp_tac: simpset -> int -> tactic
  val               Simp_tac:            int -> tactic
  val           Asm_simp_tac:            int -> tactic
  val          Full_simp_tac:            int -> tactic
  val        Asm_lr_simp_tac:            int -> tactic
  val      Asm_full_simp_tac:            int -> tactic
  val          simplify: simpset -> thm -> thm
  val      asm_simplify: simpset -> thm -> thm
  val     full_simplify: simpset -> thm -> thm
  val   asm_lr_simplify: simpset -> thm -> thm
  val asm_full_simplify: simpset -> thm -> thm
end;

signature SIMPLIFIER =
sig
  include BASIC_SIMPLIFIER
  val clear_ss: simpset -> simpset
  val debug_bounds: bool ref
  val inherit_context: simpset -> simpset -> simpset
  val the_context: simpset -> Proof.context
  val context: Proof.context -> simpset -> simpset
  val theory_context: theory  -> simpset -> simpset
  val simproc_i: theory -> string -> term list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val simproc: theory -> string -> string list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val          rewrite: simpset -> cterm -> thm
  val      asm_rewrite: simpset -> cterm -> thm
  val     full_rewrite: simpset -> cterm -> thm
  val   asm_lr_rewrite: simpset -> cterm -> thm
  val asm_full_rewrite: simpset -> cterm -> thm
  val get_simpset: theory -> simpset
  val print_local_simpset: Proof.context -> unit
  val get_local_simpset: Proof.context -> simpset
  val put_local_simpset: simpset -> Proof.context -> Proof.context
  val change_global_ss: (simpset * thm list -> simpset) -> theory attribute
  val change_local_ss: (simpset * thm list -> simpset) -> Proof.context attribute
  val simp_add_global: theory attribute
  val simp_del_global: theory attribute
  val simp_add_local: Proof.context attribute
  val simp_del_local: Proof.context attribute
  val cong_add_global: theory attribute
  val cong_del_global: theory attribute
  val cong_add_local: Proof.context attribute
  val cong_del_local: Proof.context attribute
  val simp_modifiers: (Args.T list -> (Method.modifier * Args.T list)) list
  val method_setup: (Args.T list -> (Method.modifier * Args.T list)) list
    -> (theory -> theory) list
  val easy_setup: thm -> thm list -> (theory -> theory) list
end;

structure Simplifier: SIMPLIFIER =
struct

(** simpset data **)

(* global simpsets *)

structure GlobalSimpset = TheoryDataFun
(struct
  val name = "Pure/simpset";
  type T = simpset ref;

  val empty = ref empty_ss;
  fun copy (ref ss) = ref ss: T;            (*create new reference!*)
  fun extend (ref ss) = ref (MetaSimplifier.inherit_context empty_ss ss);
  fun merge _ (ref ss1, ref ss2) = ref (merge_ss (ss1, ss2));
  fun print _ (ref ss) = print_ss ss;
end);

val _ = Context.add_setup [GlobalSimpset.init];
val print_simpset = GlobalSimpset.print;
val get_simpset = ! o GlobalSimpset.get;

val change_simpset_of = change o GlobalSimpset.get;
fun change_simpset f = change_simpset_of (Context.the_context ()) f;

fun simpset_of thy = MetaSimplifier.context (ProofContext.init thy) (get_simpset thy);
val simpset = simpset_of o Context.the_context;


fun SIMPSET tacf st = tacf (simpset_of (Thm.theory_of_thm st)) st;
fun SIMPSET' tacf i st = tacf (simpset_of (Thm.theory_of_thm st)) i st;

fun Addsimps args = change_simpset (fn ss => ss addsimps args);
fun Delsimps args = change_simpset (fn ss => ss delsimps args);
fun Addsimprocs args = change_simpset (fn ss => ss addsimprocs args);
fun Delsimprocs args = change_simpset (fn ss => ss delsimprocs args);
fun Addcongs args = change_simpset (fn ss => ss addcongs args);
fun Delcongs args = change_simpset (fn ss => ss delcongs args);


(* local simpsets *)

structure LocalSimpset = ProofDataFun
(struct
  val name = "Pure/simpset";
  type T = simpset;
  val init = get_simpset;
  fun print _ ss = print_ss ss;
end);

val _ = Context.add_setup [LocalSimpset.init];
val print_local_simpset = LocalSimpset.print;
val get_local_simpset = LocalSimpset.get;
val put_local_simpset = LocalSimpset.put;

fun local_simpset_of ctxt = MetaSimplifier.context ctxt (get_local_simpset ctxt);


(* attributes *)

fun change_global_ss f (thy, th) = (change_simpset_of thy (fn ss => f (ss, [th])); (thy, th));
fun change_local_ss f (ctxt, th) = (LocalSimpset.map (fn ss => f (ss, [th])) ctxt, th);

val simp_add_global = change_global_ss (op addsimps);
val simp_del_global = change_global_ss (op delsimps);
val simp_add_local = change_local_ss (op addsimps);
val simp_del_local = change_local_ss (op delsimps);

val cong_add_global = change_global_ss (op addcongs);
val cong_del_global = change_global_ss (op delcongs);
val cong_add_local = change_local_ss (op addcongs);
val cong_del_local = change_local_ss (op delcongs);



(** simplification tactics and rules **)

fun solve_all_tac solvers ss =
  let
    val (_, {subgoal_tac, ...}) = MetaSimplifier.rep_ss ss;
    val solve_tac = subgoal_tac (MetaSimplifier.set_solvers solvers ss) THEN_ALL_NEW (K no_tac);
  in DEPTH_SOLVE (solve_tac 1) end;

(*NOTE: may instantiate unknowns that appear also in other subgoals*)
fun generic_simp_tac safe mode ss =
  let
    val (_, {loop_tacs, solvers = (unsafe_solvers, solvers), ...}) = MetaSimplifier.rep_ss ss;
    val loop_tac = FIRST' (map (fn (_, tac) => tac ss) loop_tacs);
    val solve_tac = FIRST' (map (MetaSimplifier.solver ss)
      (if safe then solvers else unsafe_solvers));

    fun simp_loop_tac i =
      asm_rewrite_goal_tac mode (solve_all_tac unsafe_solvers) ss i THEN
      (solve_tac i ORELSE TRY ((loop_tac THEN_ALL_NEW simp_loop_tac) i));
  in simp_loop_tac end;

local

fun simp rew mode ss thm =
  let
    val (_, {solvers = (unsafe_solvers, _), ...}) = MetaSimplifier.rep_ss ss;
    val tacf = solve_all_tac unsafe_solvers;
    fun prover s th = Option.map #1 (Seq.pull (tacf s th));
  in rew mode prover ss thm end;

in

val simp_thm = simp MetaSimplifier.rewrite_thm;
val simp_cterm = simp MetaSimplifier.rewrite_cterm;

end;


(* tactics *)

val simp_tac = generic_simp_tac false (false, false, false);
val asm_simp_tac = generic_simp_tac false (false, true, false);
val full_simp_tac = generic_simp_tac false (true, false, false);
val asm_lr_simp_tac = generic_simp_tac false (true, true, false);
val asm_full_simp_tac = generic_simp_tac false (true, true, true);
val safe_asm_full_simp_tac = generic_simp_tac true (true, true, true);

(*the abstraction over the proof state delays the dereferencing*)
fun          Simp_tac i st =          simp_tac (simpset ()) i st;
fun      Asm_simp_tac i st =      asm_simp_tac (simpset ()) i st;
fun     Full_simp_tac i st =     full_simp_tac (simpset ()) i st;
fun   Asm_lr_simp_tac i st =   asm_lr_simp_tac (simpset ()) i st;
fun Asm_full_simp_tac i st = asm_full_simp_tac (simpset ()) i st;


(* conversions *)

val          simplify = simp_thm (false, false, false);
val      asm_simplify = simp_thm (false, true, false);
val     full_simplify = simp_thm (true, false, false);
val   asm_lr_simplify = simp_thm (true, true, false);
val asm_full_simplify = simp_thm (true, true, true);

val          rewrite = simp_cterm (false, false, false);
val      asm_rewrite = simp_cterm (false, true, false);
val     full_rewrite = simp_cterm (true, false, false);
val   asm_lr_rewrite = simp_cterm (true, true, false);
val asm_full_rewrite = simp_cterm (true, true, true);



(** concrete syntax of attributes **)

(* add / del *)

val simpN = "simp";
val congN = "cong";
val addN = "add";
val delN = "del";
val onlyN = "only";
val no_asmN = "no_asm";
val no_asm_useN = "no_asm_use";
val no_asm_simpN = "no_asm_simp";
val asm_lrN = "asm_lr";

val simp_attr =
 (Attrib.add_del_args simp_add_global simp_del_global,
  Attrib.add_del_args simp_add_local simp_del_local);

val cong_attr =
 (Attrib.add_del_args cong_add_global cong_del_global,
  Attrib.add_del_args cong_add_local cong_del_local);


(* conversions *)

local

fun conv_mode x =
  ((Args.parens (Args.$$$ no_asmN) >> K simplify ||
    Args.parens (Args.$$$ no_asm_simpN) >> K asm_simplify ||
    Args.parens (Args.$$$ no_asm_useN) >> K full_simplify ||
    Scan.succeed asm_full_simplify) |> Scan.lift) x;

fun simplified_att get args =
  Attrib.syntax (conv_mode -- args >> (fn (f, ths) =>
    Drule.rule_attribute (fn x =>
      f ((if null ths then I else MetaSimplifier.clear_ss) (get x) addsimps ths))));

in

val simplified_attr =
 (simplified_att simpset_of Attrib.global_thmss,
  simplified_att local_simpset_of Attrib.local_thmss);

end;


(* setup attributes *)

val _ = Context.add_setup
 [Attrib.add_attributes
   [(simpN, simp_attr, "declaration of simplification rule"),
    (congN, cong_attr, "declaration of Simplifier congruence rule"),
    ("simplified", simplified_attr, "simplified rule")]];



(** proof methods **)

(* simplification *)

val simp_options =
 (Args.parens (Args.$$$ no_asmN) >> K simp_tac ||
  Args.parens (Args.$$$ no_asm_simpN) >> K asm_simp_tac ||
  Args.parens (Args.$$$ no_asm_useN) >> K full_simp_tac ||
  Args.parens (Args.$$$ asm_lrN) >> K asm_lr_simp_tac ||
  Scan.succeed asm_full_simp_tac);

fun simp_flags x = (Scan.repeat
  (Args.parens (Args.$$$ "depth_limit" -- Args.colon |-- Args.nat)
    >> setmp MetaSimplifier.simp_depth_limit)
  >> (curry (Library.foldl op o) I o rev)) x;

val cong_modifiers =
 [Args.$$$ congN -- Args.colon >> K ((I, cong_add_local): Method.modifier),
  Args.$$$ congN -- Args.add -- Args.colon >> K (I, cong_add_local),
  Args.$$$ congN -- Args.del -- Args.colon >> K (I, cong_del_local)];

val simp_modifiers =
 [Args.$$$ simpN -- Args.colon >> K (I, simp_add_local),
  Args.$$$ simpN -- Args.add -- Args.colon >> K (I, simp_add_local),
  Args.$$$ simpN -- Args.del -- Args.colon >> K (I, simp_del_local),
  Args.$$$ simpN -- Args.$$$ onlyN -- Args.colon
    >> K (LocalSimpset.map MetaSimplifier.clear_ss, simp_add_local)]
   @ cong_modifiers;

val simp_modifiers' =
 [Args.add -- Args.colon >> K (I, simp_add_local),
  Args.del -- Args.colon >> K (I, simp_del_local),
  Args.$$$ onlyN -- Args.colon >> K (LocalSimpset.map MetaSimplifier.clear_ss, simp_add_local)]
   @ cong_modifiers;

fun simp_args more_mods =
  Method.sectioned_args (Args.bang_facts -- Scan.lift simp_options -- Scan.lift simp_flags)
    (more_mods @ simp_modifiers');

fun simp_method ((prems, tac), FLAGS) ctxt = Method.METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN
    (FLAGS o CHANGED_PROP o ALLGOALS o tac) (local_simpset_of ctxt));

fun simp_method' ((prems, tac), FLAGS) ctxt = Method.METHOD (fn facts =>
  HEADGOAL (Method.insert_tac (prems @ facts) THEN'
      ((FLAGS o CHANGED_PROP) oo tac) (local_simpset_of ctxt)));


(* setup methods *)

fun setup_methods more_mods = Method.add_methods
 [(simpN, simp_args more_mods simp_method', "simplification"),
  ("simp_all", simp_args more_mods simp_method, "simplification (all goals)")];

fun method_setup mods = [setup_methods mods];


(** easy_setup **)

fun easy_setup reflect trivs =
  let
    val trivialities = Drule.reflexive_thm :: trivs;

    fun unsafe_solver_tac prems = FIRST' [resolve_tac (trivialities @ prems), assume_tac];
    val unsafe_solver = mk_solver "easy unsafe" unsafe_solver_tac;

    (*no premature instantiation of variables during simplification*)
    fun safe_solver_tac prems = FIRST' [match_tac (trivialities @ prems), eq_assume_tac];
    val safe_solver = mk_solver "easy safe" safe_solver_tac;

    fun mk_eq thm =
      if Logic.is_equals (Thm.concl_of thm) then [thm]
      else [thm RS reflect] handle THM _ => [];

    fun mksimps thm = mk_eq (Drule.forall_elim_vars (#maxidx (Thm.rep_thm thm) + 1) thm);

    fun init_ss thy =
      (GlobalSimpset.get thy :=
        empty_ss setsubgoaler asm_simp_tac
        setSSolver safe_solver
        setSolver unsafe_solver
        setmksimps mksimps; thy);
  in method_setup [] @ [init_ss] end;


open MetaSimplifier;

end;

structure BasicSimplifier: BASIC_SIMPLIFIER = Simplifier;
open BasicSimplifier;
