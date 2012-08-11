(*  Title:      Pure/simplifier.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics (see also
raw_simplifier.ML for the actual meta-level rewriting engine).
*)

signature BASIC_SIMPLIFIER =
sig
  include BASIC_RAW_SIMPLIFIER
  val map_simpset: (simpset -> simpset) -> Proof.context -> Proof.context
  val simpset_of: Proof.context -> simpset
  val global_simpset_of: theory -> simpset
  val Addsimprocs: simproc list -> unit
  val Delsimprocs: simproc list -> unit
  val generic_simp_tac: bool -> bool * bool * bool -> simpset -> int -> tactic
  val safe_asm_full_simp_tac: simpset -> int -> tactic
  val simp_tac: simpset -> int -> tactic
  val asm_simp_tac: simpset -> int -> tactic
  val full_simp_tac: simpset -> int -> tactic
  val asm_lr_simp_tac: simpset -> int -> tactic
  val asm_full_simp_tac: simpset -> int -> tactic
  val simplify: simpset -> thm -> thm
  val asm_simplify: simpset -> thm -> thm
  val full_simplify: simpset -> thm -> thm
  val asm_lr_simplify: simpset -> thm -> thm
  val asm_full_simplify: simpset -> thm -> thm
end;

signature SIMPLIFIER =
sig
  include BASIC_SIMPLIFIER
  val map_simpset_global: (simpset -> simpset) -> theory -> theory
  val pretty_ss: Proof.context -> simpset -> Pretty.T
  val clear_ss: simpset -> simpset
  val default_mk_sym: simpset -> thm -> thm option
  val debug_bounds: bool Unsynchronized.ref
  val prems_of: simpset -> thm list
  val add_simp: thm -> simpset -> simpset
  val del_simp: thm -> simpset -> simpset
  val add_eqcong: thm -> simpset -> simpset
  val del_eqcong: thm -> simpset -> simpset
  val add_cong: thm -> simpset -> simpset
  val del_cong: thm -> simpset -> simpset
  val add_prems: thm list -> simpset -> simpset
  val mksimps: simpset -> thm -> thm list
  val set_mksimps: (simpset -> thm -> thm list) -> simpset -> simpset
  val set_mkcong: (simpset -> thm -> thm) -> simpset -> simpset
  val set_mksym: (simpset -> thm -> thm option) -> simpset -> simpset
  val set_mkeqTrue: (simpset -> thm -> thm option) -> simpset -> simpset
  val set_termless: (term * term -> bool) -> simpset -> simpset
  val set_subgoaler: (simpset -> int -> tactic) -> simpset -> simpset
  val inherit_context: simpset -> simpset -> simpset
  val the_context: simpset -> Proof.context
  val context: Proof.context -> simpset -> simpset
  val global_context: theory -> simpset -> simpset
  val with_context: Proof.context -> (simpset -> simpset) -> simpset -> simpset
  val simproc_global_i: theory -> string -> term list ->
    (theory -> simpset -> term -> thm option) -> simproc
  val simproc_global: theory -> string -> string list ->
    (theory -> simpset -> term -> thm option) -> simproc
  val rewrite: simpset -> conv
  val asm_rewrite: simpset -> conv
  val full_rewrite: simpset -> conv
  val asm_lr_rewrite: simpset -> conv
  val asm_full_rewrite: simpset -> conv
  val get_ss: Context.generic -> simpset
  val map_ss: (simpset -> simpset) -> Context.generic -> Context.generic
  val attrib: (thm -> simpset -> simpset) -> attribute
  val simp_add: attribute
  val simp_del: attribute
  val cong_add: attribute
  val cong_del: attribute
  val check_simproc: Proof.context -> xstring * Position.T -> string
  val the_simproc: Proof.context -> string -> simproc
  val def_simproc: {name: binding, lhss: term list,
    proc: morphism -> simpset -> cterm -> thm option, identifier: thm list} ->
    local_theory -> local_theory
  val def_simproc_cmd: {name: binding, lhss: string list,
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

open Raw_Simplifier;


(** data **)

structure Data = Generic_Data
(
  type T = simpset * simproc Name_Space.table;
  val empty : T = (empty_ss, Name_Space.empty_table "simproc");
  fun extend (ss, tab) = (Raw_Simplifier.inherit_context empty_ss ss, tab);
  fun merge ((ss1, tab1), (ss2, tab2)) =
    (merge_ss (ss1, ss2), Name_Space.merge_tables (tab1, tab2));
);

val get_ss = fst o Data.get;

fun map_ss f context =
  Data.map (apfst ((Raw_Simplifier.with_context (Context.proof_of context) f))) context;

val get_simprocs = snd o Data.get o Context.Proof;



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

(* attributes *)

fun attrib f = Thm.declaration_attribute (map_ss o f);

val simp_add = attrib add_simp;
val simp_del = attrib del_simp;
val cong_add = attrib add_cong;
val cong_del = attrib del_cong;


(* local simpset *)

fun map_simpset f = Context.proof_map (map_ss f);
fun simpset_of ctxt = Raw_Simplifier.context ctxt (get_ss (Context.Proof ctxt));

val _ = Context.>> (Context.map_theory
  (ML_Antiquote.value (Binding.name "simpset")
    (Scan.succeed "Simplifier.simpset_of ML_context")));


(* global simpset *)

fun map_simpset_global f = Context.theory_map (map_ss f);
fun global_simpset_of thy =
  Raw_Simplifier.context (Proof_Context.init_global thy) (get_ss (Context.Theory thy));

fun Addsimprocs args = Context.>> (map_ss (fn ss => ss addsimprocs args));
fun Delsimprocs args = Context.>> (map_ss (fn ss => ss delsimprocs args));



(** named simprocs **)

(* get simprocs *)

fun check_simproc ctxt = Name_Space.check (Context.Proof ctxt) (get_simprocs ctxt) #> #1;
val the_simproc = Name_Space.get o get_simprocs;

val _ =
  Context.>> (Context.map_theory
   (ML_Antiquote.value (Binding.name "simproc")
      (Args.context -- Scan.lift (Parse.position Args.name)
        >> (fn (ctxt, name) =>
          "Simplifier.the_simproc ML_context " ^
            ML_Syntax.print_string (check_simproc ctxt name)))));


(* define simprocs *)

local

fun gen_simproc prep {name = b, lhss, proc, identifier} lthy =
  let
    val simproc = make_simproc
      {name = Local_Theory.full_name lthy b,
       lhss =
        let
          val lhss' = prep lthy lhss;
          val ctxt' = fold Variable.auto_fixes lhss' lthy;
        in Variable.export_terms ctxt' lthy lhss' end
        |> map (Thm.cterm_of (Proof_Context.theory_of lthy)),
       proc = proc,
       identifier = identifier};
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = true} (fn phi => fn context =>
      let
        val b' = Morphism.binding phi b;
        val simproc' = transform_simproc phi simproc;
      in
        context
        |> Data.map (fn (ss, tab) =>
          (ss addsimprocs [simproc'], #2 (Name_Space.define context true (b', simproc') tab)))
      end)
  end;

in

val def_simproc = gen_simproc Syntax.check_terms;
val def_simproc_cmd = gen_simproc Syntax.read_terms;

end;



(** simplification tactics and rules **)

fun solve_all_tac solvers ss =
  let
    val (_, {subgoal_tac, ...}) = Raw_Simplifier.internal_ss ss;
    val solve_tac = subgoal_tac (Raw_Simplifier.set_solvers solvers ss) THEN_ALL_NEW (K no_tac);
  in DEPTH_SOLVE (solve_tac 1) end;

(*NOTE: may instantiate unknowns that appear also in other subgoals*)
fun generic_simp_tac safe mode ss =
  let
    val (_, {loop_tacs, solvers = (unsafe_solvers, solvers), ...}) = Raw_Simplifier.internal_ss ss;
    val loop_tac = FIRST' (map (fn (_, tac) => tac ss) (rev loop_tacs));
    val solve_tac = FIRST' (map (Raw_Simplifier.solver ss)
      (rev (if safe then solvers else unsafe_solvers)));

    fun simp_loop_tac i =
      Raw_Simplifier.generic_rewrite_goal_tac mode (solve_all_tac unsafe_solvers) ss i THEN
      (solve_tac i ORELSE TRY ((loop_tac THEN_ALL_NEW simp_loop_tac) i));
  in SELECT_GOAL (simp_loop_tac 1) end;

local

fun simp rew mode ss thm =
  let
    val (_, {solvers = (unsafe_solvers, _), ...}) = Raw_Simplifier.internal_ss ss;
    val tacf = solve_all_tac (rev unsafe_solvers);
    fun prover s th = Option.map #1 (Seq.pull (tacf s th));
  in rew mode prover ss thm end;

in

val simp_thm = simp Raw_Simplifier.rewrite_thm;
val simp_cterm = simp Raw_Simplifier.rewrite_cterm;

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
      (K (map_ss (fn ss => f (ss, [transform_simproc phi simproc])))));

in

val simproc_att =
  (Args.context -- Scan.lift add_del) :|-- (fn (ctxt, decl) =>
    Scan.repeat1 (Scan.lift (Args.named_attribute (decl o the_simproc ctxt o check_simproc ctxt))))
  >> (fn atts => Thm.declaration_attribute (fn th =>
        fold (fn att => Thm.attribute_declaration (Morphism.form att) th) atts));

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
    f ((if null ths then I else Raw_Simplifier.clear_ss)
        (simpset_of (Context.proof_of context)) addsimps ths)));

end;


(* setup attributes *)

val _ = Context.>> (Context.map_theory
 (Attrib.setup (Binding.name simpN) (Attrib.add_del simp_add simp_del)
    "declaration of Simplifier rewrite rule" #>
  Attrib.setup (Binding.name congN) (Attrib.add_del cong_add cong_del)
    "declaration of Simplifier congruence rule" #>
  Attrib.setup (Binding.name "simproc") simproc_att
    "declaration of simplification procedures" #>
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
    >> K (Context.proof_map (map_ss Raw_Simplifier.clear_ss), simp_add)]
   @ cong_modifiers;

val simp_modifiers' =
 [Args.add -- Args.colon >> K (I, simp_add),
  Args.del -- Args.colon >> K (I, simp_del),
  Args.$$$ onlyN -- Args.colon
    >> K (Context.proof_map (map_ss Raw_Simplifier.clear_ss), simp_add)]
   @ cong_modifiers;

val simp_options =
 (Args.parens (Args.$$$ no_asmN) >> K simp_tac ||
  Args.parens (Args.$$$ no_asm_simpN) >> K asm_simp_tac ||
  Args.parens (Args.$$$ no_asm_useN) >> K full_simp_tac ||
  Args.parens (Args.$$$ asm_lrN) >> K asm_lr_simp_tac ||
  Scan.succeed asm_full_simp_tac);

fun simp_method more_mods meth =
  Scan.lift simp_options --|
    Method.sections (more_mods @ simp_modifiers') >>
    (fn tac => fn ctxt => METHOD (fn facts => meth ctxt tac facts));



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
        (CHANGED_PROP o PARALLEL_GOALS o ALLGOALS o tac) (simpset_of ctxt)))
    "simplification (all goals)";

fun easy_setup reflect trivs = method_setup [] #> Context.theory_map (map_ss (fn _ =>
  let
    val trivialities = Drule.reflexive_thm :: trivs;

    fun unsafe_solver_tac ss =
      FIRST' [resolve_tac (trivialities @ Raw_Simplifier.prems_of ss), assume_tac];
    val unsafe_solver = mk_solver "easy unsafe" unsafe_solver_tac;

    (*no premature instantiation of variables during simplification*)
    fun safe_solver_tac ss =
      FIRST' [match_tac (trivialities @ Raw_Simplifier.prems_of ss), eq_assume_tac];
    val safe_solver = mk_solver "easy safe" safe_solver_tac;

    fun mk_eq thm =
      if can Logic.dest_equals (Thm.concl_of thm) then [thm]
      else [thm RS reflect] handle THM _ => [];

    fun mksimps thm = mk_eq (Thm.forall_elim_vars (Thm.maxidx_of thm + 1) thm);
  in
    empty_ss
    setSSolver safe_solver
    setSolver unsafe_solver
    |> set_subgoaler asm_simp_tac
    |> set_mksimps (K mksimps)
  end));

end;

structure Basic_Simplifier: BASIC_SIMPLIFIER = Simplifier;
open Basic_Simplifier;
