(*  Title:      Pure/simplifier.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Generic simplifier, suitable for most logics (see also
raw_simplifier.ML for the actual meta-level rewriting engine).
*)

signature BASIC_SIMPLIFIER =
sig
  val simp_tac: Proof.context -> int -> tactic
  val asm_simp_tac: Proof.context -> int -> tactic
  val full_simp_tac: Proof.context -> int -> tactic
  val asm_lr_simp_tac: Proof.context -> int -> tactic
  val asm_full_simp_tac: Proof.context -> int -> tactic
  val safe_simp_tac: Proof.context -> int -> tactic
  val safe_asm_simp_tac: Proof.context -> int -> tactic
  val safe_full_simp_tac: Proof.context -> int -> tactic
  val safe_asm_lr_simp_tac: Proof.context -> int -> tactic
  val safe_asm_full_simp_tac: Proof.context -> int -> tactic
  val simplify: Proof.context -> thm -> thm
  val asm_simplify: Proof.context -> thm -> thm
  val full_simplify: Proof.context -> thm -> thm
  val asm_lr_simplify: Proof.context -> thm -> thm
  val asm_full_simplify: Proof.context -> thm -> thm
end;

signature SIMPLIFIER =
sig
  include BASIC_SIMPLIFIER
  include RAW_SIMPLIFIER
  val attrib: (thm -> Proof.context -> Proof.context) -> attribute
  val simp_add: attribute
  val simp_del: attribute
  val simp_flip: attribute
  val cong_add: attribute
  val cong_del: attribute
  val check_simproc: Proof.context -> xstring * Position.T -> string * simproc
  val the_simproc: Proof.context -> string -> simproc
  val make_simproc: Proof.context ->
    {name: string, kind: proc_kind, lhss: term list, proc: morphism -> proc, identifier: thm list} ->
    simproc
  type ('a, 'b, 'c) simproc_spec =
    {passive: bool, name: binding, kind: proc_kind, lhss: 'a list, proc: 'b, identifier: 'c}
  val read_simproc_spec: Proof.context ->
    (string, 'b, 'c) simproc_spec -> (term, 'b, 'c) simproc_spec
  val define_simproc: (term, morphism -> proc, thm list) simproc_spec -> local_theory ->
    simproc * local_theory
  val simproc_setup: (term, morphism -> proc, thm list) simproc_spec -> simproc
  val simproc_setup_cmd: (string, morphism -> proc, thm list) simproc_spec -> simproc
  val simproc_setup_command: (local_theory -> local_theory) parser
  val pretty_simpset: bool -> Proof.context -> Pretty.T
  val set_mksimps: (Proof.context -> thm -> thm list) -> Proof.context -> Proof.context
  val rewrite: Proof.context -> conv
  val asm_rewrite: Proof.context -> conv
  val full_rewrite: Proof.context -> conv
  val asm_lr_rewrite: Proof.context -> conv
  val asm_full_rewrite: Proof.context -> conv
  val cong_modifiers: Method.modifier parser list
  val simp_modifiers': Method.modifier parser list
  val simp_modifiers: Method.modifier parser list
  val method_setup: Method.modifier parser list -> theory -> theory
  val unsafe_solver_tac: Proof.context -> int -> tactic
  val unsafe_solver: solver
  val safe_solver_tac: Proof.context -> int -> tactic
  val safe_solver: solver
end;

structure Simplifier: SIMPLIFIER =
struct

open Raw_Simplifier;


(** declarations **)

fun set_mksimps mk = set_mksimps_context (fn thm => fn ctxt => (mk ctxt thm, ctxt));


(* attributes *)

fun attrib f = Thm.declaration_attribute (map_ss o f);

val simp_add = attrib add_simp;
val simp_del = attrib del_simp;
val simp_flip = attrib flip_simp;
val cong_add = attrib add_cong;
val cong_del = attrib del_cong;


(** named simprocs **)

structure Simprocs = Generic_Data
(
  type T = simproc Name_Space.table;
  val empty : T = Name_Space.empty_table "simproc";
  fun merge data : T = Name_Space.merge_tables data;
);


(* get simprocs *)

val get_simprocs = Simprocs.get o Context.Proof;

val the_simproc = Name_Space.get o get_simprocs;
fun check_simproc ctxt = Name_Space.check (Context.Proof ctxt) (get_simprocs ctxt);

val _ = Theory.setup
  (ML_Antiquotation.value_embedded \<^binding>\<open>simproc\<close>
    (Args.context -- Scan.lift Parse.embedded_position >> (fn (ctxt, name) =>
      "Simplifier.the_simproc ML_context " ^ ML_Syntax.print_string (#1 (check_simproc ctxt name)))));


(* define simprocs *)

fun make_simproc ctxt {name, lhss, kind, proc, identifier} =
  let
    val ctxt' = fold Proof_Context.augment lhss ctxt;
    val lhss' = Variable.export_terms ctxt' ctxt lhss;
  in
    cert_simproc (Proof_Context.theory_of ctxt)
      {name = name, kind = kind, lhss = lhss', proc = Morphism.entity proc, identifier = identifier}
  end;

type ('a, 'b, 'c) simproc_spec =
  {passive: bool, name: binding, kind: proc_kind, lhss: 'a list, proc: 'b, identifier: 'c};

fun read_simproc_spec ctxt {passive, name, kind, lhss, proc, identifier} =
  let
    val lhss' =
      Syntax.read_terms ctxt lhss handle ERROR msg =>
        error (msg ^ Position.here_list (map Syntax.read_input_pos lhss));
  in
    {passive = passive, name = name, kind = kind, lhss = lhss', proc = proc, identifier = identifier}
  end;

fun define_simproc {passive, name, kind, lhss, proc, identifier} lthy =
  let
    val simproc0 =
      make_simproc lthy
        {name = Local_Theory.full_name lthy name,
          kind = kind, lhss = lhss, proc = proc, identifier = identifier};
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = false, pos = Binding.pos_of name}
      (fn phi => fn context =>
        let
          val name' = Morphism.binding phi name;
          val simproc' = simproc0 |> transform_simproc phi |> trim_context_simproc;
        in
          context
          |> Simprocs.map (#2 o Name_Space.define context true (name', simproc'))
          |> not passive ? map_ss (add_proc simproc')
        end)
    |> pair simproc0
  end;


(* simproc_setup with concrete syntax *)

val simproc_setup =
  Named_Target.setup_result transform_simproc o define_simproc;

fun simproc_setup_cmd args =
  Named_Target.setup_result transform_simproc
    (fn lthy => lthy |> define_simproc (read_simproc_spec lthy args));

val parse_proc_kind =
  Parse.$$$ "congproc" >> K (Congproc false) ||
  Parse.$$$ "weak_congproc" >> K (Congproc true) ||
  Scan.succeed Simproc;

fun print_proc_kind kind =
  (case kind of
    Simproc => "Simplifier.Simproc"
  | Congproc weak => "Simplifier.Congproc " ^ Bool.toString weak);

val parse_simproc_spec =
  Scan.optional (Parse.$$$ "passive" >> K true) false -- parse_proc_kind --
  Parse.binding --
    (Parse.$$$ "(" |-- Parse.enum1 "|" Parse.term --| Parse.$$$ ")") --
    (Parse.$$$ "=" |-- Parse.ML_source) --
    Scan.option ((Parse.position (Parse.$$$ "identifier") >> #2) -- Parse.thms1)
  >> (fn (((((a, b), c), d), e), f) =>
      {passive = a, kind = b, name = c, lhss = d, proc = e, identifier = f});

val _ = Theory.setup
  (ML_Context.add_antiquotation_embedded \<^binding>\<open>simproc_setup\<close>
    (fn _ => fn input => fn ctxt =>
      let
        val ml = ML_Lex.tokenize_no_range;

        val {passive, name, kind, lhss, proc, identifier} = input
          |> Parse.read_embedded ctxt (Thy_Header.get_keywords' ctxt) parse_simproc_spec
          |> read_simproc_spec ctxt;

        val (decl1, ctxt1) = ML_Context.read_antiquotes proc ctxt;
        val (decl2, ctxt2) =
          (case identifier of
            NONE => (K ("", "[]"), ctxt1)
          | SOME (_, thms) => ML_Thms.thm_binding "thms" false (Attrib.eval_thms ctxt1 thms) ctxt1);

        fun decl' ctxt' =
          let
            val (ml_env1, ml_body1) = decl1 ctxt';
            val (ml_env2, ml_body2) = decl2 ctxt' |> apply2 ml;
            val ml_body' =
              ml "Simplifier.simproc_setup {passive = " @ ml (Bool.toString passive) @
              ml ", name = " @ ml (ML_Syntax.make_binding (Binding.name_of name, Binding.pos_of name)) @
              ml ", kind = " @ ml (print_proc_kind kind) @
              ml ", lhss = " @ ml (ML_Syntax.print_list ML_Syntax.print_term lhss) @
              ml ", proc = (" @ ml_body1 @ ml ")" @
              ml ", identifier = (" @ ml_body2 @ ml ")}";
          in (ml_env1 @ ml_env2, ml_body') end;
      in (decl', ctxt2) end));

val simproc_setup_command =
  parse_simproc_spec >> (fn {passive, name, kind, lhss, proc, identifier} =>
    (case identifier of
      NONE =>
        Context.proof_map
          (ML_Context.expression (Input.pos_of proc)
            (ML_Lex.read
              ("Simplifier.simproc_setup_cmd {passive = " ^ Bool.toString passive ^
               ", name = " ^ ML_Syntax.make_binding (Binding.name_of name, Binding.pos_of name) ^
               ", kind = " ^ print_proc_kind kind ^
               ", lhss = " ^ ML_Syntax.print_strings lhss ^
               ", proc = (") @ ML_Lex.read_source proc @ ML_Lex.read "), identifier = []}"))
    | SOME (pos, _) =>
        error ("Bad command " ^ Markup.markup Markup.keyword1 "simproc_setup" ^
          " with " ^ Markup.markup Markup.keyword2 "identifier" ^
          ": this is only supported in\nML antiquotation \<^simproc_setup>\<open>...\<close>" ^ Position.here pos)));



(** congruence rule to protect foundational terms of local definitions **)

local

fun add_foundation_cong (binding, (const, target_params)) gthy =
  if null target_params then gthy
  else
    let
      val thy = Context.theory_of gthy;
      val cong =
        list_comb (const, target_params)
        |> Logic.varify_global
        |> Thm.global_cterm_of thy
        |> Thm.reflexive
        |> Thm.close_derivation \<^here>;
      val cong_binding = Binding.qualify_name true binding "cong";
    in
      gthy
      |> Attrib.generic_notes Thm.theoremK [((cong_binding, []), [([cong], [])])]
      |> #2
    end;

val _ = Theory.setup (Generic_Target.add_foundation_interpretation add_foundation_cong);

in end;



(** pretty_simpset **)

fun pretty_simpset verbose ctxt =
  let
    val pretty_term = Syntax.pretty_term ctxt;
    val pretty_thm = Thm.pretty_thm ctxt;
    val pretty_thm_item = Thm.pretty_thm_item ctxt;

    fun pretty_simproc (name, lhss) =
      Pretty.block
        (Pretty.marks_str name :: Pretty.str ":" :: Pretty.fbrk ::
          Pretty.fbreaks (map (Pretty.item o single o pretty_term) lhss));

    fun pretty_congproc (name, {lhss, proc}) =
      let
        val prt_rule =
          (case try (Morphism.form_context' ctxt proc) @{cterm dummy} of
            SOME (SOME thm) => [Pretty.fbrk, Pretty.str "rule:", Pretty.fbrk, pretty_thm thm]
          | NONE => []);
      in
        Pretty.block
          (Pretty.marks_str name :: Pretty.str ":" :: Pretty.fbrk ::
            Pretty.fbreaks (map (Pretty.item o single o pretty_term) lhss) @ prt_rule)
      end;

    fun pretty_cong_name (const, name) =
      pretty_term ((if const then Const else Free) (name, dummyT));
    fun pretty_cong (name, thm) =
      Pretty.block [pretty_cong_name name, Pretty.str ":", Pretty.brk 1, pretty_thm thm];

    val ss = dest_ss (simpset_of ctxt);
    val simproc_space = Name_Space.space_of_table (get_simprocs ctxt);
    val simprocs = Name_Space.markups_entries verbose ctxt simproc_space (#simprocs ss);
    val congprocs = Name_Space.markups_entries verbose ctxt simproc_space (#congprocs ss);
  in
    [Pretty.big_list "simplification rules:" (map (pretty_thm_item o #2) (#simps ss)),
      Pretty.big_list "simplification procedures:" (map pretty_simproc simprocs),
      Pretty.big_list "congruence procedures:" (map pretty_congproc congprocs),
      Pretty.big_list "congruences:" (map pretty_cong (#congs ss)),
      Pretty.strs ("loopers:" :: map quote (#loopers ss)),
      Pretty.strs ("unsafe solvers:" :: map quote (#unsafe_solvers ss)),
      Pretty.strs ("safe solvers:" :: map quote (#safe_solvers ss))]
    |> Pretty.chunks
  end;



(** simplification tactics and rules **)

fun solve_all_tac solvers ctxt =
  let
    val subgoal_tac = subgoal_tac (set_solvers solvers ctxt);
    val solve_tac = subgoal_tac THEN_ALL_NEW (K no_tac);
  in DEPTH_SOLVE (solve_tac 1) end;

(*NOTE: may instantiate unknowns that appear also in other subgoals*)
fun generic_simp_tac safe mode ctxt =
  let
    val loop_tac = loop_tac ctxt;
    val (unsafe_solvers, solvers) = solvers ctxt;
    val solve_tac = FIRST' (map (solver ctxt)
      (rev (if safe then solvers else unsafe_solvers)));

    fun simp_loop_tac i =
      generic_rewrite_goal_tac mode (solve_all_tac unsafe_solvers) ctxt i THEN
      (solve_tac i ORELSE TRY ((loop_tac THEN_ALL_NEW simp_loop_tac) i));
  in PREFER_GOAL (simp_loop_tac 1) end;

local

fun simp rew mode ctxt thm =
  let
    val (unsafe_solvers, _) = solvers ctxt;
    val tacf = solve_all_tac (rev unsafe_solvers);
    fun prover s th = Option.map #1 (Seq.pull (tacf s th));
  in rew mode prover ctxt thm end;

in

val simp_thm = simp rewrite_thm;
val simp_cterm = simp rewrite_cterm;

end;


(* tactics *)

val simp_tac = generic_simp_tac false (false, false, false);
val asm_simp_tac = generic_simp_tac false (false, true, false);
val full_simp_tac = generic_simp_tac false (true, false, false);
val asm_lr_simp_tac = generic_simp_tac false (true, true, false);
val asm_full_simp_tac = generic_simp_tac false (true, true, true);

(*not totally safe: may instantiate unknowns that appear also in other subgoals*)
val safe_simp_tac = generic_simp_tac true (false, false, false);
val safe_asm_simp_tac = generic_simp_tac true (false, true, false);
val safe_full_simp_tac = generic_simp_tac true (true, false, false);
val safe_asm_lr_simp_tac = generic_simp_tac true (true, true, false);
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
val flipN = "flip"
val congN = "cong";
val onlyN = "only";
val no_asmN = "no_asm";
val no_asm_useN = "no_asm_use";
val no_asm_simpN = "no_asm_simp";
val asm_lrN = "asm_lr";


(* simprocs *)

local

val add_del =
  (Args.del -- Args.colon >> K del_proc ||
    Scan.option (Args.add -- Args.colon) >> K add_proc)
  >> (fn f => fn simproc => Morphism.entity (fn phi => Thm.declaration_attribute
      (K (map_ss (f (transform_simproc phi simproc))))));

in

val simproc_att =
  (Args.context -- Scan.lift add_del) :|-- (fn (ctxt, decl) =>
    Scan.repeat1 (Scan.lift (Args.named_attribute (decl o #2 o check_simproc ctxt))))
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
  (fn (f, ths) => Thm.rule_attribute ths (fn context =>
    f (Context.proof_of context |>
      (if null ths then I else clear_simpset #> add_simps ths))));

end;


(* setup attributes *)

val cong_format = Scan.succeed (Thm.rule_attribute [] (Context.proof_of #> mk_cong));

val _ = Theory.setup
 (Attrib.setup \<^binding>\<open>simp\<close> (Attrib.add_del simp_add simp_del)
    "declaration of Simplifier rewrite rule" #>
  Attrib.setup \<^binding>\<open>cong\<close> (Attrib.add_del cong_add cong_del)
    "declaration of Simplifier congruence rule" #>
  Attrib.setup \<^binding>\<open>simproc\<close> simproc_att
    "declaration of simplification procedures" #>
  Attrib.setup \<^binding>\<open>simplified\<close> simplified "simplified rule" #>
  Attrib.setup \<^binding>\<open>cong_format\<close> cong_format "internal format of Simplifier cong rule");



(** method syntax **)

val cong_modifiers =
 [Args.$$$ congN -- Args.colon >> K (Method.modifier cong_add \<^here>),
  Args.$$$ congN -- Args.add -- Args.colon >> K (Method.modifier cong_add \<^here>),
  Args.$$$ congN -- Args.del -- Args.colon >> K (Method.modifier cong_del \<^here>)];

val simp_modifiers =
 [Args.$$$ simpN -- Args.colon >> K (Method.modifier simp_add \<^here>),
  Args.$$$ simpN -- Args.add -- Args.colon >> K (Method.modifier simp_add \<^here>),
  Args.$$$ simpN -- Args.del -- Args.colon >> K (Method.modifier simp_del \<^here>),
  Args.$$$ simpN -- Args.$$$ flipN -- Args.colon >> K (Method.modifier simp_flip \<^here>),
  Args.$$$ simpN -- Args.$$$ onlyN -- Args.colon >>
    K {init = clear_simpset, attribute = simp_add, pos = \<^here>}]
   @ cong_modifiers;

val simp_modifiers' =
 [Args.add -- Args.colon >> K (Method.modifier simp_add \<^here>),
  Args.del -- Args.colon >> K (Method.modifier simp_del \<^here>),
  Args.$$$ flipN -- Args.colon >> K (Method.modifier simp_flip \<^here>),
  Args.$$$ onlyN -- Args.colon >>
    K {init = clear_simpset, attribute = simp_add, pos = \<^here>}]
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
  Method.setup \<^binding>\<open>simp\<close>
    (simp_method more_mods (fn ctxt => fn tac => fn facts =>
      HEADGOAL (Method.insert_tac ctxt facts THEN'
        (CHANGED_PROP oo tac) ctxt)))
    "simplification" #>
  Method.setup \<^binding>\<open>simp_all\<close>
    (simp_method more_mods (fn ctxt => fn tac => fn facts =>
      ALLGOALS (Method.insert_tac ctxt facts) THEN
        (CHANGED_PROP o PARALLEL_ALLGOALS o tac) ctxt))
    "simplification (all goals)";

fun unsafe_solver_tac ctxt =
  FIRST' [resolve_tac ctxt (Drule.reflexive_thm :: prems_of ctxt), assume_tac ctxt];
val unsafe_solver = mk_solver "Pure unsafe" unsafe_solver_tac;

(*no premature instantiation of variables during simplification*)
fun safe_solver_tac ctxt =
  FIRST' [match_tac ctxt (Drule.reflexive_thm :: prems_of ctxt), eq_assume_tac];
val safe_solver = mk_solver "Pure safe" safe_solver_tac;

val _ =
  Theory.setup
    (method_setup [] #> Context.theory_map (map_ss (
      empty_simpset
      #> set_safe_solver safe_solver
      #> set_unsafe_solver unsafe_solver
      #> set_subgoaler asm_simp_tac)));

end;

structure Basic_Simplifier: BASIC_SIMPLIFIER = Simplifier;
open Basic_Simplifier;
