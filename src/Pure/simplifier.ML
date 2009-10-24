(*  Title:      Pure/simplifier.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics (see also
meta_simplifier.ML for the actual meta-level rewriting engine).
*)

signature BASIC_SIMPLIFIER =
sig
  include BASIC_META_SIMPLIFIER
  val change_simpset: (simpset -> simpset) -> unit
  val global_simpset_of: theory -> simpset
  val Addsimprocs: simproc list -> unit
  val Delsimprocs: simproc list -> unit
  val simpset_of: Proof.context -> simpset
  val generic_simp_tac: bool -> bool * bool * bool -> simpset -> int -> tactic
  val safe_asm_full_simp_tac: simpset -> int -> tactic
  val               simp_tac: simpset -> int -> tactic
  val           asm_simp_tac: simpset -> int -> tactic
  val          full_simp_tac: simpset -> int -> tactic
  val        asm_lr_simp_tac: simpset -> int -> tactic
  val      asm_full_simp_tac: simpset -> int -> tactic
  val          simplify: simpset -> thm -> thm
  val      asm_simplify: simpset -> thm -> thm
  val     full_simplify: simpset -> thm -> thm
  val   asm_lr_simplify: simpset -> thm -> thm
  val asm_full_simplify: simpset -> thm -> thm
end;

signature SIMPLIFIER =
sig
  include BASIC_SIMPLIFIER
  val pretty_ss: Proof.context -> simpset -> Pretty.T
  val clear_ss: simpset -> simpset
  val debug_bounds: bool Unsynchronized.ref
  val inherit_context: simpset -> simpset -> simpset
  val the_context: simpset -> Proof.context
  val context: Proof.context -> simpset -> simpset
  val theory_context: theory  -> simpset -> simpset
  val simproc_i: theory -> string -> term list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val simproc: theory -> string -> string list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val          rewrite: simpset -> conv
  val      asm_rewrite: simpset -> conv
  val     full_rewrite: simpset -> conv
  val   asm_lr_rewrite: simpset -> conv
  val asm_full_rewrite: simpset -> conv
  val get_ss: Context.generic -> simpset
  val map_ss: (simpset -> simpset) -> Context.generic -> Context.generic
  val attrib: (simpset * thm list -> simpset) -> attribute
  val simp_add: attribute
  val simp_del: attribute
  val cong_add: attribute
  val cong_del: attribute
  val map_simpset: (simpset -> simpset) -> theory -> theory
  val get_simproc: Context.generic -> xstring -> simproc
  val def_simproc: {name: string, lhss: string list,
    proc: morphism -> simpset -> cterm -> thm option, identifier: thm list} ->
    local_theory -> local_theory
  val def_simproc_i: {name: string, lhss: term list,
    proc: morphism -> simpset -> cterm -> thm option, identifier: thm list} ->
    local_theory -> local_theory
  val cong_modifiers: Method.modifier parser list
  val simp_modifiers': Method.modifier parser list
  val simp_modifiers: Method.modifier parser list
  val method_setup: Method.modifier parser list -> theory -> theory
  val easy_setup: thm -> thm list -> theory -> theory
end;

structure Simplifier: SIMPLIFIER =
struct

open MetaSimplifier;


(** pretty printing **)

fun pretty_ss ctxt ss =
  let
    val pretty_cterm = Syntax.pretty_term ctxt o Thm.term_of;
    val pretty_thm = Display.pretty_thm ctxt;
    fun pretty_proc (name, lhss) = Pretty.big_list (name ^ ":") (map pretty_cterm lhss);
    fun pretty_cong (name, thm) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, pretty_thm thm];

    val {simps, procs, congs, loopers, unsafe_solvers, safe_solvers, ...} = dest_ss ss;
  in
    [Pretty.big_list "simplification rules:" (map (pretty_thm o #2) simps),
      Pretty.big_list "simplification procedures:" (map pretty_proc (sort_wrt #1 procs)),
      Pretty.big_list "congruences:" (map pretty_cong congs),
      Pretty.strs ("loopers:" :: map quote loopers),
      Pretty.strs ("unsafe solvers:" :: map quote unsafe_solvers),
      Pretty.strs ("safe solvers:" :: map quote safe_solvers)]
    |> Pretty.chunks
  end;



(** simpset data **)

structure SimpsetData = GenericDataFun
(
  type T = simpset;
  val empty = empty_ss;
  fun extend ss = MetaSimplifier.inherit_context empty_ss ss;
  fun merge _ = merge_ss;
);

val get_ss = SimpsetData.get;
val map_ss = SimpsetData.map;


(* attributes *)

fun attrib f = Thm.declaration_attribute (fn th => map_ss (fn ss => f (ss, [th])));

val simp_add = attrib (op addsimps);
val simp_del = attrib (op delsimps);
val cong_add = attrib (op addcongs);
val cong_del = attrib (op delcongs);


(* global simpset *)

fun map_simpset f = Context.theory_map (map_ss f);
fun change_simpset f = Context.>> (Context.map_theory (map_simpset f));
fun global_simpset_of thy =
  MetaSimplifier.context (ProofContext.init thy) (get_ss (Context.Theory thy));

fun Addsimprocs args = change_simpset (fn ss => ss addsimprocs args);
fun Delsimprocs args = change_simpset (fn ss => ss delsimprocs args);


(* local simpset *)

fun simpset_of ctxt = MetaSimplifier.context ctxt (get_ss (Context.Proof ctxt));

val _ = ML_Antiquote.value "simpset"
  (Scan.succeed "Simplifier.simpset_of (ML_Context.the_local_context ())");



(** named simprocs **)

(* data *)

structure Simprocs = GenericDataFun
(
  type T = simproc NameSpace.table;
  val empty = NameSpace.empty_table;
  val extend = I;
  fun merge _ simprocs = NameSpace.merge_tables simprocs;
);


(* get simprocs *)

fun get_simproc context xname =
  let
    val (space, tab) = Simprocs.get context;
    val name = NameSpace.intern space xname;
  in
    (case Symtab.lookup tab name of
      SOME proc => proc
    | NONE => error ("Undefined simplification procedure: " ^ quote name))
  end;

val _ = ML_Antiquote.value "simproc" (Scan.lift Args.name >> (fn name =>
  "Simplifier.get_simproc (ML_Context.the_generic_context ()) " ^ ML_Syntax.print_string name));


(* define simprocs *)

local

fun gen_simproc prep {name, lhss, proc, identifier} lthy =
  let
    val b = Binding.name name;
    val naming = LocalTheory.full_naming lthy;
    val simproc = make_simproc
      {name = LocalTheory.full_name lthy b,
       lhss =
        let
          val lhss' = prep lthy lhss;
          val ctxt' = lthy
            |> fold Variable.declare_term lhss'
            |> fold Variable.auto_fixes lhss';
        in Variable.export_terms ctxt' lthy lhss' end
        |> map (Thm.cterm_of (ProofContext.theory_of lthy)),
       proc = proc,
       identifier = identifier}
      |> morph_simproc (LocalTheory.target_morphism lthy);
  in
    lthy |> LocalTheory.declaration (fn phi =>
      let
        val b' = Morphism.binding phi b;
        val simproc' = morph_simproc phi simproc;
      in
        Simprocs.map (#2 o NameSpace.define true naming (b', simproc'))
        #> map_ss (fn ss => ss addsimprocs [simproc'])
      end)
  end;

in

val def_simproc = gen_simproc Syntax.read_terms;
val def_simproc_i = gen_simproc Syntax.check_terms;

end;



(** simplification tactics and rules **)

fun solve_all_tac solvers ss =
  let
    val (_, {subgoal_tac, ...}) = MetaSimplifier.internal_ss ss;
    val solve_tac = subgoal_tac (MetaSimplifier.set_solvers solvers ss) THEN_ALL_NEW (K no_tac);
  in DEPTH_SOLVE (solve_tac 1) end;

(*NOTE: may instantiate unknowns that appear also in other subgoals*)
fun generic_simp_tac safe mode ss =
  let
    val (_, {loop_tacs, solvers = (unsafe_solvers, solvers), ...}) = MetaSimplifier.internal_ss ss;
    val loop_tac = FIRST' (map (fn (_, tac) => tac ss) (rev loop_tacs));
    val solve_tac = FIRST' (map (MetaSimplifier.solver ss)
      (rev (if safe then solvers else unsafe_solvers)));

    fun simp_loop_tac i =
      asm_rewrite_goal_tac mode (solve_all_tac unsafe_solvers) ss i THEN
      (solve_tac i ORELSE TRY ((loop_tac THEN_ALL_NEW simp_loop_tac) i));
  in simp_loop_tac end;

local

fun simp rew mode ss thm =
  let
    val (_, {solvers = (unsafe_solvers, _), ...}) = MetaSimplifier.internal_ss ss;
    val tacf = solve_all_tac (rev unsafe_solvers);
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
val onlyN = "only";
val no_asmN = "no_asm";
val no_asm_useN = "no_asm_use";
val no_asm_simpN = "no_asm_simp";
val asm_lrN = "asm_lr";


(* simprocs *)

local

val add_del =
  (Args.del -- Args.colon >> K (op delsimprocs) ||
    Scan.option (Args.add -- Args.colon) >> K (op addsimprocs))
  >> (fn f => fn simproc => fn phi => Thm.declaration_attribute
      (K (map_ss (fn ss => f (ss, [morph_simproc phi simproc])))));

in

val simproc_att =
  Scan.peek (fn context =>
    add_del :|-- (fn decl =>
      Scan.repeat1 (Args.named_attribute (decl o get_simproc context))
      >> (Library.apply o map Morphism.form)));

end;


(* conversions *)

local

fun conv_mode x =
  ((Args.parens (Args.$$$ no_asmN) >> K simplify ||
    Args.parens (Args.$$$ no_asm_simpN) >> K asm_simplify ||
    Args.parens (Args.$$$ no_asm_useN) >> K full_simplify ||
    Scan.succeed asm_full_simplify) |> Scan.lift) x;

in

val simplified = conv_mode -- Attrib.thms >>
  (fn (f, ths) => Thm.rule_attribute (fn context =>
    f ((if null ths then I else MetaSimplifier.clear_ss)
        (simpset_of (Context.proof_of context)) addsimps ths)));

end;


(* setup attributes *)

val _ = Context.>> (Context.map_theory
 (Attrib.setup (Binding.name simpN) (Attrib.add_del simp_add simp_del)
    "declaration of Simplifier rewrite rule" #>
  Attrib.setup (Binding.name congN) (Attrib.add_del cong_add cong_del)
    "declaration of Simplifier congruence rule" #>
  Attrib.setup (Binding.name "simproc") simproc_att "declaration of simplification procedures" #>
  Attrib.setup (Binding.name "simplified") simplified "simplified rule"));



(** method syntax **)

val cong_modifiers =
 [Args.$$$ congN -- Args.colon >> K ((I, cong_add): Method.modifier),
  Args.$$$ congN -- Args.add -- Args.colon >> K (I, cong_add),
  Args.$$$ congN -- Args.del -- Args.colon >> K (I, cong_del)];

val simp_modifiers =
 [Args.$$$ simpN -- Args.colon >> K (I, simp_add),
  Args.$$$ simpN -- Args.add -- Args.colon >> K (I, simp_add),
  Args.$$$ simpN -- Args.del -- Args.colon >> K (I, simp_del),
  Args.$$$ simpN -- Args.$$$ onlyN -- Args.colon
    >> K (Context.proof_map (map_ss MetaSimplifier.clear_ss), simp_add)]
   @ cong_modifiers;

val simp_modifiers' =
 [Args.add -- Args.colon >> K (I, simp_add),
  Args.del -- Args.colon >> K (I, simp_del),
  Args.$$$ onlyN -- Args.colon
    >> K (Context.proof_map (map_ss MetaSimplifier.clear_ss), simp_add)]
   @ cong_modifiers;

val simp_options =
 (Args.parens (Args.$$$ no_asmN) >> K simp_tac ||
  Args.parens (Args.$$$ no_asm_simpN) >> K asm_simp_tac ||
  Args.parens (Args.$$$ no_asm_useN) >> K full_simp_tac ||
  Args.parens (Args.$$$ asm_lrN) >> K asm_lr_simp_tac ||
  Scan.succeed asm_full_simp_tac);

fun simp_method more_mods meth =
  Args.bang_facts -- Scan.lift simp_options --|
    Method.sections (more_mods @ simp_modifiers') >>
    (fn (prems, tac) => fn ctxt => METHOD (fn facts => meth ctxt tac (prems @ facts)));



(** setup **)

fun method_setup more_mods =
  Method.setup (Binding.name simpN)
    (simp_method more_mods (fn ctxt => fn tac => fn facts =>
      HEADGOAL (Method.insert_tac facts THEN'
        (CHANGED_PROP oo tac) (simpset_of ctxt))))
    "simplification" #>
  Method.setup (Binding.name "simp_all")
    (simp_method more_mods (fn ctxt => fn tac => fn facts =>
      ALLGOALS (Method.insert_tac facts) THEN
        (CHANGED_PROP o ALLGOALS o tac) (simpset_of ctxt)))
    "simplification (all goals)";

fun easy_setup reflect trivs = method_setup [] #> Context.theory_map (map_ss (fn _ =>
  let
    val trivialities = Drule.reflexive_thm :: trivs;

    fun unsafe_solver_tac prems = FIRST' [resolve_tac (trivialities @ prems), assume_tac];
    val unsafe_solver = mk_solver "easy unsafe" unsafe_solver_tac;

    (*no premature instantiation of variables during simplification*)
    fun safe_solver_tac prems = FIRST' [match_tac (trivialities @ prems), eq_assume_tac];
    val safe_solver = mk_solver "easy safe" safe_solver_tac;

    fun mk_eq thm =
      if can Logic.dest_equals (Thm.concl_of thm) then [thm]
      else [thm RS reflect] handle THM _ => [];

    fun mksimps thm = mk_eq (Thm.forall_elim_vars (#maxidx (Thm.rep_thm thm) + 1) thm);
  in
    empty_ss setsubgoaler asm_simp_tac
    setSSolver safe_solver
    setSolver unsafe_solver
    setmksimps mksimps
  end));

end;

structure Basic_Simplifier: BASIC_SIMPLIFIER = Simplifier;
open Basic_Simplifier;
