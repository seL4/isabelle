(*  Title:      Pure/simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics (see also
meta_simplifier.ML for the actual meta-level rewriting engine).
*)

signature BASIC_SIMPLIFIER =
sig
  include BASIC_META_SIMPLIFIER
  type context_solver
  val mk_context_solver: string -> (Proof.context -> thm list -> int -> tactic)
    -> context_solver
  type context_simproc
  val mk_context_simproc: string -> cterm list ->
    (Proof.context -> simpset -> term -> thm option) -> context_simproc
  val print_simpset: theory -> unit
  val simpset_ref_of_sg: theory -> simpset ref    (*obsolete*)
  val simpset_ref_of: theory -> simpset ref
  val simpset_of_sg: theory -> simpset            (*obsolete*)
  val simpset_of: theory -> simpset
  val SIMPSET: (simpset -> tactic) -> tactic
  val SIMPSET': (simpset -> 'a -> tactic) -> 'a -> tactic
  val simpset: unit -> simpset
  val simpset_ref: unit -> simpset ref
  val Addsimps: thm list -> unit
  val Delsimps: thm list -> unit
  val Addsimprocs: simproc list -> unit
  val Delsimprocs: simproc list -> unit
  val Addcongs: thm list -> unit
  val Delcongs: thm list -> unit
  val local_simpset_of: Proof.context -> simpset
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
  val simproc_i: theory -> string -> term list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val simproc: theory -> string -> string list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val context_simproc_i: theory -> string -> term list
    -> (Proof.context -> simpset -> term -> thm option) -> context_simproc
  val context_simproc: theory -> string -> string list
    -> (Proof.context -> simpset -> term -> thm option) -> context_simproc
  val          rewrite: simpset -> cterm -> thm
  val      asm_rewrite: simpset -> cterm -> thm
  val     full_rewrite: simpset -> cterm -> thm
  val   asm_lr_rewrite: simpset -> cterm -> thm
  val asm_full_rewrite: simpset -> cterm -> thm
  val add_context_simprocs: context_simproc list -> theory -> theory
  val del_context_simprocs: context_simproc list -> theory -> theory
  val set_context_subgoaler: (Proof.context -> simpset -> int -> tactic) -> theory -> theory
  val reset_context_subgoaler: theory -> theory
  val add_context_looper: string * (Proof.context -> int -> Tactical.tactic) ->
    theory -> theory
  val del_context_looper: string -> theory -> theory
  val add_context_unsafe_solver: context_solver -> theory -> theory
  val add_context_safe_solver: context_solver -> theory -> theory
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
  val change_simpset_of: (simpset * 'a -> simpset) -> 'a -> theory -> theory
  val simp_modifiers: (Args.T list -> (Method.modifier * Args.T list)) list
  val method_setup: (Args.T list -> (Method.modifier * Args.T list)) list
    -> (theory -> theory) list
  val easy_setup: thm -> thm list -> (theory -> theory) list
end;

structure Simplifier: SIMPLIFIER =
struct

open MetaSimplifier;


(** context dependent simpset components **)

(* datatype context_solver *)

datatype context_solver =
  ContextSolver of (string * (Proof.context -> thm list -> int -> tactic)) * stamp;

fun mk_context_solver name f = ContextSolver ((name, f), stamp ());
fun eq_context_solver (ContextSolver (_, id1), ContextSolver (_, id2)) = (id1 = id2);
val merge_context_solvers = gen_merge_lists eq_context_solver;


(* datatype context_simproc *)

datatype context_simproc = ContextSimproc of
  (string * cterm list * (Proof.context -> simpset -> term -> thm option)) * stamp;

fun mk_context_simproc name lhss f = ContextSimproc ((name, lhss, f), stamp ());
fun eq_context_simproc (ContextSimproc (_, id1), ContextSimproc (_, id2)) = (id1 = id2);
val merge_context_simprocs = gen_merge_lists eq_context_simproc;

fun context_simproc_i thy name =
  mk_context_simproc name o map (Thm.cterm_of thy o Logic.varify);

fun context_simproc thy name =
  context_simproc_i thy name o map (Sign.read_term thy);


(* datatype context_ss *)

datatype context_ss = ContextSS of
 {simprocs: context_simproc list,
  subgoal_tac: (Proof.context -> simpset -> int -> tactic) option,
  loop_tacs: (string * (Proof.context -> int -> tactic)) list,
  unsafe_solvers: context_solver list,
  solvers: context_solver list};

fun context_ss ctxt ss ctxt_ss =
  let
    val ContextSS {simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers} = ctxt_ss;
    fun prep_simproc (ContextSimproc ((name, lhss, f), _)) =
      mk_simproc name lhss (K (f ctxt));
    fun add_loop (name, f) simpset = simpset addloop (name, f ctxt);
    fun add_solver add (ContextSolver ((name, f), _)) simpset =
      add (simpset, mk_solver name (f ctxt));
  in
    ((case subgoal_tac of NONE => ss | SOME tac => ss setsubgoaler tac ctxt)
      addsimprocs map prep_simproc simprocs)
    |> fold_rev add_loop loop_tacs
    |> fold_rev (add_solver (op addSolver)) unsafe_solvers
    |> fold_rev (add_solver (op addSSolver)) solvers
  end;

fun make_context_ss (simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers) =
  ContextSS {simprocs = simprocs, subgoal_tac = subgoal_tac, loop_tacs = loop_tacs,
    unsafe_solvers = unsafe_solvers, solvers = solvers};

val empty_context_ss = make_context_ss ([], NONE, [], [], []);

fun merge_context_ss (ctxt_ss1, ctxt_ss2) =
  let
    val ContextSS {simprocs = simprocs1, subgoal_tac = subgoal_tac1, loop_tacs = loop_tacs1,
      unsafe_solvers = unsafe_solvers1, solvers = solvers1} = ctxt_ss1;
    val ContextSS {simprocs = simprocs2, subgoal_tac = subgoal_tac2, loop_tacs = loop_tacs2,
      unsafe_solvers = unsafe_solvers2, solvers = solvers2} = ctxt_ss2;

    val simprocs' = merge_context_simprocs simprocs1 simprocs2;
    val subgoal_tac' = (case subgoal_tac1 of NONE => subgoal_tac2 | some => some);
    val loop_tacs' = merge_alists loop_tacs1 loop_tacs2;
    val unsafe_solvers' = merge_context_solvers unsafe_solvers1 unsafe_solvers2;
    val solvers' = merge_context_solvers solvers1 solvers2;
  in make_context_ss (simprocs', subgoal_tac', loop_tacs', unsafe_solvers', solvers') end;



(** global and local simpset data **)

(* theory data kind 'Pure/simpset' *)

structure GlobalSimpset = TheoryDataFun
(struct
  val name = "Pure/simpset";
  type T = simpset ref * context_ss;

  val empty = (ref empty_ss, empty_context_ss);
  fun copy (ref ss, ctxt_ss) = (ref ss, ctxt_ss): T;            (*create new reference!*)
  val extend = copy;
  fun merge _ ((ref ss1, ctxt_ss1), (ref ss2, ctxt_ss2)) =
    (ref (merge_ss (ss1, ss2)), merge_context_ss (ctxt_ss1, ctxt_ss2));
  fun print _ (ref ss, _) = print_ss ss;
end);

val _ = Context.add_setup [GlobalSimpset.init];
val print_simpset = GlobalSimpset.print;

val simpset_ref_of = #1 o GlobalSimpset.get;
val simpset_ref_of_sg = simpset_ref_of;
val get_context_ss = #2 o GlobalSimpset.get o ProofContext.theory_of;

fun map_context_ss f = GlobalSimpset.map (apsnd
  (fn ContextSS {simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers} =>
    make_context_ss (f (simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers))));


(* access global simpset *)

val simpset_of = ! o simpset_ref_of;
val simpset_of_sg = simpset_of;

fun SIMPSET tacf state = tacf (simpset_of (Thm.theory_of_thm state)) state;
fun SIMPSET' tacf i state = tacf (simpset_of (Thm.theory_of_thm state)) i state;

val simpset = simpset_of o Context.the_context;
val simpset_ref = simpset_ref_of o Context.the_context;


(* change global simpset *)

fun change_simpset_of f x thy =
  let val r = simpset_ref_of thy
  in r := f (! r, x); thy end;

fun change_simpset f x = (change_simpset_of f x (Context.the_context ()); ());

val Addsimps = change_simpset (op addsimps);
val Delsimps = change_simpset (op delsimps);
val Addsimprocs = change_simpset (op addsimprocs);
val Delsimprocs = change_simpset (op delsimprocs);
val Addcongs = change_simpset (op addcongs);
val Delcongs = change_simpset (op delcongs);


(* change context dependent components *)

fun add_context_simprocs procs =
  map_context_ss (fn (simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers) =>
    (merge_context_simprocs procs simprocs, subgoal_tac, loop_tacs,
      unsafe_solvers, solvers));

fun del_context_simprocs procs =
  map_context_ss (fn (simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers) =>
    (gen_rems eq_context_simproc (simprocs, procs), subgoal_tac, loop_tacs,
      unsafe_solvers, solvers));

fun set_context_subgoaler tac =
  map_context_ss (fn (simprocs, _, loop_tacs, unsafe_solvers, solvers) =>
    (simprocs, SOME tac, loop_tacs, unsafe_solvers, solvers));

val reset_context_subgoaler =
  map_context_ss (fn (simprocs, _, loop_tacs, unsafe_solvers, solvers) =>
    (simprocs, NONE, loop_tacs, unsafe_solvers, solvers));

fun add_context_looper (name, tac) =
  map_context_ss (fn (simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers) =>
    (simprocs, subgoal_tac, merge_alists [(name, tac)] loop_tacs,
      unsafe_solvers, solvers));

fun del_context_looper name =
  map_context_ss (fn (simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers) =>
    (simprocs, subgoal_tac, filter_out (equal name o #1) loop_tacs,
      unsafe_solvers, solvers));

fun add_context_unsafe_solver solver =
  map_context_ss (fn (simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers) =>
    (simprocs, subgoal_tac, loop_tacs,
      merge_context_solvers [solver] unsafe_solvers, solvers));

fun add_context_safe_solver solver =
  map_context_ss (fn (simprocs, subgoal_tac, loop_tacs, unsafe_solvers, solvers) =>
    (simprocs, subgoal_tac, loop_tacs, unsafe_solvers,
      merge_context_solvers [solver] solvers));


(* proof data kind 'Pure/simpset' *)

structure LocalSimpset = ProofDataFun
(struct
  val name = "Pure/simpset";
  type T = simpset;
  val init = simpset_of;
  fun print ctxt ss = print_ss (context_ss ctxt ss (get_context_ss ctxt));
end);

val _ = Context.add_setup [LocalSimpset.init];
val print_local_simpset = LocalSimpset.print;

val get_local_simpset = LocalSimpset.get;
val put_local_simpset = LocalSimpset.put;
fun map_local_simpset f ctxt = put_local_simpset (f (get_local_simpset ctxt)) ctxt;

fun local_simpset_of ctxt =
  context_ss ctxt (get_local_simpset ctxt) (get_context_ss ctxt);


(* attributes *)

fun change_global_ss f (thy, th) =
  let val r = simpset_ref_of thy
  in r := f (! r, [th]); (thy, th) end;

fun change_local_ss f (ctxt, th) =
  let val ss = f (get_local_simpset ctxt, [th])
  in (put_local_simpset ss ctxt, th) end;

val simp_add_global = change_global_ss (op addsimps);
val simp_del_global = change_global_ss (op delsimps);
val simp_add_local = change_local_ss (op addsimps);
val simp_del_local = change_local_ss (op delsimps);

val cong_add_global = change_global_ss (op addcongs);
val cong_del_global = change_global_ss (op delcongs);
val cong_add_local = change_local_ss (op addcongs);
val cong_del_local = change_local_ss (op delcongs);


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
    Drule.rule_attribute (fn x => f ((if null ths then I else clear_ss) (get x) addsimps ths))));

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
 [Args.$$$ congN -- Args.colon >> K ((I, cong_add_local):Method.modifier),
  Args.$$$ congN -- Args.add -- Args.colon >> K (I, cong_add_local),
  Args.$$$ congN -- Args.del -- Args.colon >> K (I, cong_del_local)];

val simp_modifiers =
 [Args.$$$ simpN -- Args.colon >> K (I, simp_add_local),
  Args.$$$ simpN -- Args.add -- Args.colon >> K (I, simp_add_local),
  Args.$$$ simpN -- Args.del -- Args.colon >> K (I, simp_del_local),
  Args.$$$ simpN -- Args.$$$ onlyN -- Args.colon >> K (map_local_simpset clear_ss, simp_add_local)]
   @ cong_modifiers;

val simp_modifiers' =
 [Args.add -- Args.colon >> K (I, simp_add_local),
  Args.del -- Args.colon >> K (I, simp_del_local),
  Args.$$$ onlyN -- Args.colon >> K (map_local_simpset clear_ss, simp_add_local)]
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
      (simpset_ref_of thy :=
        empty_ss setsubgoaler asm_simp_tac
        setSSolver safe_solver
        setSolver unsafe_solver
        setmksimps mksimps; thy);
  in method_setup [] @ [init_ss] end;

end;

structure BasicSimplifier: BASIC_SIMPLIFIER = Simplifier;
open BasicSimplifier;
