(*  Title:      Provers/simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics.  See Pure/thm.ML for the
actual meta-level rewriting engine.
*)

infix 4
  setsubgoaler setloop addloop delloop setSSolver addSSolver setSolver
  addSolver addsimps delsimps addeqcongs deleqcongs addcongs delcongs
  setmksimps setmkeqTrue setmkcong setmksym settermless addsimprocs delsimprocs;

signature BASIC_SIMPLIFIER =
sig
  type simproc
  val mk_simproc: string -> cterm list
    -> (Sign.sg -> thm list -> term -> thm option) -> simproc
  type solver
  val mk_solver: string -> (thm list -> int -> tactic) -> solver
  type simpset
  val empty_ss: simpset
  val rep_ss: simpset ->
   {mss: meta_simpset,
    mk_cong: thm -> thm,
    subgoal_tac: simpset -> int -> tactic,
    loop_tacs: (string * (int -> tactic)) list,
    unsafe_solvers: solver list,
    solvers: solver list};
  val print_ss: simpset -> unit
  val print_simpset: theory -> unit
  val setsubgoaler: simpset *  (simpset -> int -> tactic) -> simpset
  val setloop:      simpset *             (int -> tactic) -> simpset
  val addloop:      simpset *  (string * (int -> tactic)) -> simpset
  val delloop:      simpset *   string                    -> simpset
  val setSSolver:   simpset * solver -> simpset
  val addSSolver:   simpset * solver -> simpset
  val setSolver:    simpset * solver -> simpset
  val addSolver:    simpset * solver -> simpset
  val setmksimps:   simpset * (thm -> thm list) -> simpset
  val setmkeqTrue:  simpset * (thm -> thm option) -> simpset
  val setmkcong:    simpset * (thm -> thm) -> simpset
  val setmksym:     simpset * (thm -> thm option) -> simpset
  val settermless:  simpset * (term * term -> bool) -> simpset
  val addsimps:     simpset * thm list -> simpset
  val delsimps:     simpset * thm list -> simpset
  val addeqcongs:   simpset * thm list -> simpset
  val deleqcongs:   simpset * thm list -> simpset
  val addcongs:     simpset * thm list -> simpset
  val delcongs:     simpset * thm list -> simpset
  val addsimprocs:  simpset * simproc list -> simpset
  val delsimprocs:  simpset * simproc list -> simpset
  val merge_ss:     simpset * simpset -> simpset
  val prems_of_ss:  simpset -> thm list
  val simpset_ref_of_sg: Sign.sg -> simpset ref
  val simpset_ref_of: theory -> simpset ref
  val simpset_of_sg: Sign.sg -> simpset
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
  val generic_simp_tac: bool -> bool * bool * bool -> simpset -> int -> tactic
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
  val asm_full_simplify: simpset -> thm -> thm
end;

signature SIMPLIFIER =
sig
  include BASIC_SIMPLIFIER
  val          rewrite: simpset -> cterm -> thm
  val      asm_rewrite: simpset -> cterm -> thm
  val     full_rewrite: simpset -> cterm -> thm
  val asm_full_rewrite: simpset -> cterm -> thm
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
  val setup: (theory -> theory) list
  val method_setup: (Args.T list -> (Method.modifier * Args.T list)) list
    -> (theory -> theory) list
  val easy_setup: thm -> thm list -> (theory -> theory) list
end;

structure Simplifier: SIMPLIFIER =
struct


(** simplification procedures **)

(* datatype simproc *)

datatype simproc =
  Simproc of string * cterm list * (Sign.sg -> thm list -> term -> thm option) * stamp;

fun mk_simproc name lhss proc =
  Simproc (name, map (Thm.cterm_fun Logic.varify) lhss, proc, stamp ());

fun rep_simproc (Simproc args) = args;



(** solvers **)

datatype solver = Solver of string * (thm list -> int -> tactic) * stamp;

fun mk_solver name solver = Solver(name, solver, stamp());

fun eq_solver (Solver(_,_,s1),Solver(_,_,s2)) = s1=s2;

val merge_solvers = generic_merge eq_solver I I;

fun app_sols [] _ _ = no_tac
  | app_sols (Solver(_,solver,_)::sols) thms i =
       solver thms i ORELSE app_sols sols thms i;



(** simplification sets **)

(* type simpset *)

datatype simpset =
  Simpset of {
    mss: meta_simpset,
    mk_cong: thm -> thm,
    subgoal_tac: simpset -> int -> tactic,
    loop_tacs: (string * (int -> tactic)) list,
    unsafe_solvers: solver list,
    solvers: solver list};

fun make_ss mss mk_cong subgoal_tac loop_tacs unsafe_solvers solvers =
  Simpset {mss = mss, mk_cong = mk_cong, subgoal_tac = subgoal_tac,
    loop_tacs = loop_tacs, unsafe_solvers = unsafe_solvers, solvers = solvers};

val empty_ss =
  let val mss = Thm.set_mk_sym (Thm.empty_mss, Some o symmetric_fun)
  in make_ss mss I (K (K no_tac)) [] [] [] end;

fun rep_ss (Simpset args) = args;
fun prems_of_ss (Simpset {mss, ...}) = Thm.prems_of_mss mss;


(* print simpsets *)

fun print_ss ss =
  let
    val Simpset {mss, ...} = ss;
    val {simps, procs, congs} = Thm.dest_mss mss;

    val pretty_thms = map Display.pretty_thm;
    fun pretty_proc (name, lhss) =
      Pretty.big_list (name ^ ":") (map Display.pretty_cterm lhss);
  in
    [Pretty.big_list "simplification rules:" (pretty_thms simps),
      Pretty.big_list "simplification procedures:" (map pretty_proc procs),
      Pretty.big_list "congruences:" (pretty_thms congs)]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* extend simpsets *)

fun (Simpset {mss, mk_cong, subgoal_tac = _, loop_tacs, unsafe_solvers, solvers})
    setsubgoaler subgoal_tac =
  make_ss mss mk_cong subgoal_tac loop_tacs unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs = _, unsafe_solvers, solvers})
    setloop tac =
  make_ss mss mk_cong subgoal_tac [("", tac)] unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    addloop tac = make_ss mss mk_cong subgoal_tac
      (case assoc_string (loop_tacs, (#1 tac)) of None => () | Some x =>
        warning ("overwriting looper " ^ quote (#1 tac)); overwrite (loop_tacs, tac))
      unsafe_solvers solvers;

fun (ss as Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
 delloop name =
  let val (del, rest) = partition (fn (n, _) => n = name) loop_tacs in
    if null del then (warning ("No such looper in simpset: " ^ name); ss)
    else make_ss mss mk_cong subgoal_tac rest unsafe_solvers solvers
  end;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, ...})
    setSSolver solver =
  make_ss mss mk_cong subgoal_tac loop_tacs unsafe_solvers [solver];

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    addSSolver sol =
  make_ss mss mk_cong subgoal_tac loop_tacs unsafe_solvers (merge_solvers solvers [sol]);

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers = _, solvers})
    setSolver unsafe_solver =
  make_ss mss mk_cong subgoal_tac loop_tacs [unsafe_solver] solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    addSolver sol =
  make_ss mss mk_cong subgoal_tac loop_tacs (merge_solvers unsafe_solvers [sol]) solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    setmksimps mk_simps =
  make_ss (Thm.set_mk_rews (mss, mk_simps)) mk_cong subgoal_tac loop_tacs unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    setmkeqTrue mk_eq_True =
  make_ss (Thm.set_mk_eq_True (mss, mk_eq_True)) mk_cong subgoal_tac loop_tacs
    unsafe_solvers solvers;

fun (Simpset {mss, mk_cong = _, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    setmkcong mk_cong =
  make_ss mss mk_cong subgoal_tac loop_tacs unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    setmksym mksym =
  make_ss (Thm.set_mk_sym (mss, mksym)) mk_cong subgoal_tac loop_tacs unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs,  unsafe_solvers, solvers})
    settermless termless =
  make_ss (Thm.set_termless (mss, termless)) mk_cong subgoal_tac loop_tacs
    unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    addsimps rews =
  make_ss (Thm.add_simps (mss, rews)) mk_cong subgoal_tac loop_tacs unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    delsimps rews =
  make_ss (Thm.del_simps (mss, rews)) mk_cong subgoal_tac loop_tacs unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    addeqcongs newcongs =
  make_ss (Thm.add_congs (mss, newcongs)) mk_cong subgoal_tac loop_tacs unsafe_solvers solvers;

fun (Simpset {mss, subgoal_tac, mk_cong, loop_tacs, unsafe_solvers, solvers})
    deleqcongs oldcongs =
  make_ss (Thm.del_congs (mss, oldcongs)) mk_cong subgoal_tac loop_tacs unsafe_solvers solvers;

fun (ss as Simpset {mk_cong, ...}) addcongs newcongs =
  ss addeqcongs map mk_cong newcongs;

fun (ss as Simpset {mk_cong, ...}) delcongs oldcongs =
  ss deleqcongs map mk_cong oldcongs;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    addsimprocs simprocs =
  make_ss (Thm.add_simprocs (mss, map rep_simproc simprocs)) mk_cong subgoal_tac loop_tacs
    unsafe_solvers solvers;

fun (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers})
    delsimprocs simprocs =
  make_ss (Thm.del_simprocs (mss, map rep_simproc simprocs)) mk_cong subgoal_tac
    loop_tacs unsafe_solvers solvers;

fun clear_ss (Simpset {mss, mk_cong, subgoal_tac, loop_tacs = _, unsafe_solvers, solvers}) =
  make_ss (Thm.clear_mss mss) mk_cong subgoal_tac [] unsafe_solvers solvers;


(* merge simpsets *)

(*ignores subgoal_tac of 2nd simpset!*)

fun merge_ss
   (Simpset {mss = mss1, mk_cong, loop_tacs = loop_tacs1, subgoal_tac,
             unsafe_solvers = unsafe_solvers1, solvers = solvers1},
    Simpset {mss = mss2, mk_cong = _, loop_tacs = loop_tacs2, subgoal_tac = _,
             unsafe_solvers = unsafe_solvers2, solvers = solvers2}) =
  make_ss (Thm.merge_mss (mss1, mss2)) mk_cong subgoal_tac
    (merge_alists loop_tacs1 loop_tacs2)
    (merge_solvers unsafe_solvers1 unsafe_solvers2)
    (merge_solvers solvers1 solvers2);



(** global and local simpset data **)

(* theory data kind 'Provers/simpset' *)

structure GlobalSimpsetArgs =
struct
  val name = "Provers/simpset";
  type T = simpset ref;

  val empty = ref empty_ss;
  fun copy (ref ss) = (ref ss): T;            (*create new reference!*)
  val prep_ext = copy;
  fun merge (ref ss1, ref ss2) = ref (merge_ss (ss1, ss2));
  fun print _ (ref ss) = print_ss ss;
end;

structure GlobalSimpset = TheoryDataFun(GlobalSimpsetArgs);
val print_simpset = GlobalSimpset.print;
val simpset_ref_of_sg = GlobalSimpset.get_sg;
val simpset_ref_of = GlobalSimpset.get;


(* access global simpset *)

val simpset_of_sg = ! o simpset_ref_of_sg;
val simpset_of = simpset_of_sg o Theory.sign_of;

fun SIMPSET tacf state = tacf (simpset_of_sg (Thm.sign_of_thm state)) state;
fun SIMPSET' tacf i state = tacf (simpset_of_sg (Thm.sign_of_thm state)) i state;

val simpset = simpset_of o Context.the_context;
val simpset_ref = simpset_ref_of_sg o Theory.sign_of o Context.the_context;


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


(* proof data kind 'Provers/simpset' *)

structure LocalSimpsetArgs =
struct
  val name = "Provers/simpset";
  type T = simpset;
  val init = simpset_of;
  fun print _ ss = print_ss ss;
end;

structure LocalSimpset = ProofDataFun(LocalSimpsetArgs);
val print_local_simpset = LocalSimpset.print;
val get_local_simpset = LocalSimpset.get;
val put_local_simpset = LocalSimpset.put;
fun map_local_simpset f ctxt = put_local_simpset (f (get_local_simpset ctxt)) ctxt;


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



(** simplification tactics **)

fun solve_all_tac (mk_cong, subgoal_tac, loop_tacs, unsafe_solvers) mss =
  let
    val ss =
      make_ss mss mk_cong subgoal_tac loop_tacs unsafe_solvers unsafe_solvers;
    val solve1_tac = (subgoal_tac ss THEN_ALL_NEW (K no_tac)) 1
  in DEPTH_SOLVE solve1_tac end;

fun loop_tac loop_tacs = FIRST'(map snd loop_tacs);

(*note: may instantiate unknowns that appear also in other subgoals*)
fun generic_simp_tac safe mode =
  fn (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, solvers, ...}) =>
    let
      val solvs = app_sols (if safe then solvers else unsafe_solvers);
      fun simp_loop_tac i =
        asm_rewrite_goal_tac mode
          (solve_all_tac (mk_cong, subgoal_tac, loop_tacs, unsafe_solvers))
          mss i
        THEN (solvs (prems_of_mss mss) i ORELSE
              TRY ((loop_tac loop_tacs THEN_ALL_NEW simp_loop_tac) i))
    in simp_loop_tac end;

val          simp_tac = generic_simp_tac false (false, false, false);
val      asm_simp_tac = generic_simp_tac false (false, true, false);
val     full_simp_tac = generic_simp_tac false (true,  false, false);
val   asm_lr_simp_tac = generic_simp_tac false (true,  true, false);
val asm_full_simp_tac = generic_simp_tac false (true,  true, true);


(*the abstraction over the proof state delays the dereferencing*)
fun          Simp_tac i st =          simp_tac (simpset ()) i st;
fun      Asm_simp_tac i st =      asm_simp_tac (simpset ()) i st;
fun     Full_simp_tac i st =     full_simp_tac (simpset ()) i st;
fun   Asm_lr_simp_tac i st =   asm_lr_simp_tac (simpset ()) i st;
fun Asm_full_simp_tac i st = asm_full_simp_tac (simpset ()) i st;



(** simplification rules and conversions **)

fun simp rew mode
     (Simpset {mss, mk_cong, subgoal_tac, loop_tacs, unsafe_solvers, ...}) thm =
  let
    val tacf = solve_all_tac (mk_cong, subgoal_tac, loop_tacs, unsafe_solvers);
    fun prover m th = apsome fst (Seq.pull (tacf m th));
  in rew mode prover mss thm end;

val simp_thm = simp Drule.rewrite_thm;
val simp_cterm = simp Drule.rewrite_cterm;

val          simplify = simp_thm (false, false, false);
val      asm_simplify = simp_thm (false, true, false);
val     full_simplify = simp_thm (true, false, false);
val asm_full_simplify = simp_thm (true, true, false);

val          rewrite = simp_cterm (false, false, false);
val      asm_rewrite = simp_cterm (false, true, false);
val     full_rewrite = simp_cterm (true, false, false);
val asm_full_rewrite = simp_cterm (true, true, false);



(** concrete syntax of attributes **)

(* add / del *)

val simpN = "simp";
val congN = "cong";
val addN = "add";
val delN = "del";
val onlyN = "only";

val simp_attr =
 (Attrib.add_del_args simp_add_global simp_del_global,
  Attrib.add_del_args simp_add_local simp_del_local);

val cong_attr =
 (Attrib.add_del_args cong_add_global cong_del_global,
  Attrib.add_del_args cong_add_local cong_del_local);


(* conversions *)

fun conv_attr f =
  (Attrib.no_args (Drule.rule_attribute (f o simpset_of)),
    Attrib.no_args (Drule.rule_attribute (f o get_local_simpset)));


(* setup_attrs *)

val setup_attrs = Attrib.add_attributes
 [(simpN,               simp_attr, "declare simplification rule"),
  (congN,               cong_attr, "declare Simplifier congruence rule"),
  ("simplify",          conv_attr simplify, "simplify rule"),
  ("asm_simplify",      conv_attr asm_simplify, "simplify rule, using assumptions"),
  ("full_simplify",     conv_attr full_simplify, "fully simplify rule"),
  ("asm_full_simplify", conv_attr asm_full_simplify, "fully simplify rule, using assumptions")];



(** proof methods **)

(* simplification *)

val simp_options =
 (Args.parens (Args.$$$ "no_asm") >> K simp_tac ||
  Args.parens (Args.$$$ "no_asm_simp") >> K asm_simp_tac ||
  Args.parens (Args.$$$ "no_asm_use") >> K full_simp_tac ||
  Scan.succeed asm_full_simp_tac);

val cong_modifiers =
 [Args.$$$ congN -- Args.colon >> K ((I, cong_add_local):Method.modifier),
  Args.$$$ congN -- Args.$$$ addN -- Args.colon >> K (I, cong_add_local),
  Args.$$$ congN -- Args.$$$ delN -- Args.colon >> K (I, cong_del_local)];

val simp_modifiers =
 [Args.$$$ simpN -- Args.colon >> K (I, simp_add_local),
  Args.$$$ simpN -- Args.$$$ addN -- Args.colon >> K (I, simp_add_local),
  Args.$$$ simpN -- Args.$$$ delN -- Args.colon >> K (I, simp_del_local),
  Args.$$$ simpN -- Args.$$$ onlyN -- Args.colon >> K (map_local_simpset clear_ss, simp_add_local)]
   @ cong_modifiers;

val simp_modifiers' =
 [Args.$$$ addN -- Args.colon >> K (I, simp_add_local),
  Args.$$$ delN -- Args.colon >> K (I, simp_del_local),
  Args.$$$ onlyN -- Args.colon >> K (map_local_simpset clear_ss, simp_add_local)]
   @ cong_modifiers;

fun simp_args more_mods =
  Method.sectioned_args (Args.bang_facts -- Scan.lift simp_options) (more_mods @ simp_modifiers');


fun simp_method (prems, tac) ctxt = Method.METHOD (fn facts =>
  ALLGOALS (Method.insert_tac (prems @ facts)) THEN
    (CHANGED o ALLGOALS o tac) (get_local_simpset ctxt));

fun simp_method' (prems, tac) ctxt = Method.METHOD (fn facts =>
  HEADGOAL (Method.insert_tac (prems @ facts) THEN' (CHANGED oo tac) (get_local_simpset ctxt)));


(* setup_methods *)

fun setup_methods more_mods = Method.add_methods
 [(simpN, simp_args more_mods simp_method', "simplification"),
  ("simp_all", simp_args more_mods simp_method, "simplification (all goals)")];



(** theory setup **)

val setup = [GlobalSimpset.init, LocalSimpset.init, setup_attrs];
fun method_setup mods = [setup_methods mods];

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
  in setup @ method_setup [] @ [init_ss] end;



(** outer syntax **)

val print_simpsetP =
  OuterSyntax.improper_command "print_simpset" "print context of Simplifier"
    OuterSyntax.Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o (Toplevel.keep
      (Toplevel.node_case print_simpset (print_local_simpset o Proof.context_of)))));

val _ = OuterSyntax.add_parsers [print_simpsetP];

end;


structure BasicSimplifier: BASIC_SIMPLIFIER = Simplifier;
open BasicSimplifier;
