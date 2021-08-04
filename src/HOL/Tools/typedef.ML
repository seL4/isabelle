(*  Title:      HOL/Tools/typedef.ML
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Gordon/HOL-style type definitions: create a new syntactic type
represented by a non-empty set.
*)

signature TYPEDEF =
sig
  type info =
   {rep_type: typ, abs_type: typ, Rep_name: string, Abs_name: string, axiom_name: string} *
   {inhabited: thm, type_definition: thm, Rep: thm, Rep_inverse: thm, Abs_inverse: thm,
    Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
    Rep_induct: thm, Abs_induct: thm}
  val transform_info: morphism -> info -> info
  val get_info: Proof.context -> string -> info list
  val get_info_global: theory -> string -> info list
  val interpretation: (string -> local_theory -> local_theory) -> theory -> theory
  type bindings = {Rep_name: binding, Abs_name: binding, type_definition_name: binding}
  val default_bindings: binding -> bindings
  val make_bindings: binding -> bindings option -> bindings
  val make_morphisms: binding -> (binding * binding) option -> bindings
  val overloaded: bool Config.T
  val add_typedef: {overloaded: bool} -> binding * (string * sort) list * mixfix ->
    term -> bindings option -> (Proof.context -> tactic) -> local_theory ->
    (string * info) * local_theory
  val add_typedef_global: {overloaded: bool} -> binding * (string * sort) list * mixfix ->
    term -> bindings option -> (Proof.context -> tactic) -> theory ->
    (string * info) * theory
  val typedef: {overloaded: bool} -> binding * (string * sort) list * mixfix ->
    term -> bindings option -> local_theory -> Proof.state
  val typedef_cmd: {overloaded: bool} -> binding * (string * string option) list * mixfix ->
    string -> bindings option -> local_theory -> Proof.state
end;

structure Typedef: TYPEDEF =
struct

(** type definitions **)

(* theory data *)

type info =
  (*global part*)
  {rep_type: typ, abs_type: typ, Rep_name: string, Abs_name: string, axiom_name: string} *
  (*local part*)
  {inhabited: thm, type_definition: thm, Rep: thm, Rep_inverse: thm, Abs_inverse: thm,
    Rep_inject: thm, Abs_inject: thm, Rep_cases: thm, Abs_cases: thm,
    Rep_induct: thm, Abs_induct: thm};

fun transform_info phi (info: info) =
  let
    val thm = Morphism.thm phi;
    val (global_info, {inhabited, type_definition, Rep, Rep_inverse, Abs_inverse,
      Rep_inject, Abs_inject, Rep_cases, Abs_cases, Rep_induct, Abs_induct}) = info;
  in
    (global_info,
     {inhabited = thm inhabited, type_definition = thm type_definition,
      Rep = thm Rep, Rep_inverse = thm Rep_inverse, Abs_inverse = thm Abs_inverse,
      Rep_inject = thm Rep_inject, Abs_inject = thm Abs_inject,
      Rep_cases = thm Rep_cases, Abs_cases = thm Abs_cases,
      Rep_induct = thm Rep_induct, Abs_induct = thm Abs_induct})
  end;

structure Data = Generic_Data
(
  type T = info list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge_list (K true) data;
);

fun get_info_generic context =
  Symtab.lookup_list (Data.get context) #>
  map (transform_info (Morphism.transfer_morphism'' context));

val get_info = get_info_generic o Context.Proof;
val get_info_global = get_info_generic o Context.Theory;

fun put_info name info =
  Data.map (Symtab.cons_list (name, transform_info Morphism.trim_context_morphism info));


(* global interpretation *)

structure Typedef_Plugin = Plugin(type T = string);

val typedef_plugin = Plugin_Name.declare_setup \<^binding>\<open>typedef\<close>;

fun interpretation f =
  Typedef_Plugin.interpretation typedef_plugin
    (fn name => fn lthy =>
      lthy
      |> Local_Theory.map_background_naming
          (Name_Space.root_path #> Name_Space.add_path (Long_Name.qualifier name))
      |> f name
      |> Local_Theory.restore_background_naming lthy);


(* primitive typedef axiomatization -- for fresh typedecl *)

val typedef_overloaded = Attrib.setup_config_bool \<^binding>\<open>typedef_overloaded\<close> (K false);

fun mk_inhabited A =
  let val T = HOLogic.dest_setT (Term.fastype_of A)
  in HOLogic.mk_Trueprop (HOLogic.exists_const T $ Abs ("x", T, HOLogic.mk_mem (Bound 0, A))) end;

fun mk_typedef newT oldT RepC AbsC A =
  let
    val typedefC =
      Const (\<^const_name>\<open>type_definition\<close>,
        (newT --> oldT) --> (oldT --> newT) --> HOLogic.mk_setT oldT --> HOLogic.boolT);
  in Logic.mk_implies (mk_inhabited A, HOLogic.mk_Trueprop (typedefC $ RepC $ AbsC $ A)) end;

fun primitive_typedef {overloaded} type_definition_name newT oldT Rep_name Abs_name A lthy =
  let
    (* errors *)

    fun show_names pairs = commas_quote (map fst pairs);

    val lhs_tfrees = Term.add_tfreesT newT [];
    val rhs_tfrees = Term.add_tfreesT oldT [];
    val _ =
      (case fold (remove (op =)) lhs_tfrees rhs_tfrees of
        [] => ()
      | extras => error ("Extra type variables in representing set: " ^ show_names extras));

    val _ =
      (case Term.add_frees A [] of [] =>
        []
      | xs => error ("Illegal variables in representing set: " ^ show_names xs));


    (* axiomatization *)

    val ((RepC, AbsC), consts_lthy) = lthy
      |> Local_Theory.background_theory_result
        (Sign.declare_const lthy ((Rep_name, newT --> oldT), NoSyn) ##>>
          Sign.declare_const lthy ((Abs_name, oldT --> newT), NoSyn));
    val const_dep = Theory.const_dep (Proof_Context.theory_of consts_lthy);
    val defs_context = Proof_Context.defs_context consts_lthy;

    val A_consts = fold_aterms (fn Const c => insert (op =) (const_dep c) | _ => I) A [];
    val A_types =
      (fold_types o fold_subtypes) (fn Type t => insert (op =) (Theory.type_dep t) | _ => I) A [];
    val typedef_deps = A_consts @ A_types;

    val newT_dep = Theory.type_dep (dest_Type newT);

    val ((axiom_name, axiom), axiom_lthy) = consts_lthy
      |> Local_Theory.background_theory_result
        (Thm.add_axiom consts_lthy (type_definition_name, mk_typedef newT oldT RepC AbsC A) ##>
          Theory.add_deps defs_context "" newT_dep typedef_deps ##>
          Theory.add_deps defs_context "" (const_dep (dest_Const RepC)) [newT_dep] ##>
          Theory.add_deps defs_context "" (const_dep (dest_Const AbsC)) [newT_dep]);

    val axiom_defs = Theory.defs_of (Proof_Context.theory_of axiom_lthy);
    val newT_deps = maps #2 (Defs.get_deps axiom_defs (#1 newT_dep));
    val _ =
      if null newT_deps orelse overloaded orelse Config.get lthy typedef_overloaded then ()
      else
        error (Pretty.string_of (Pretty.chunks
          [Pretty.paragraph
            (Pretty.text "Type definition with open dependencies, use" @
             [Pretty.brk 1, Pretty.str "\"", Pretty.keyword1 "typedef", Pretty.brk 1,
              Pretty.str "(", Pretty.keyword2 "overloaded", Pretty.str ")\"", Pretty.brk 1] @
             Pretty.text "or enable configuration option \"typedef_overloaded\" in the context."),
           Pretty.block [Pretty.str "  Type:", Pretty.brk 2, Syntax.pretty_typ axiom_lthy newT],
           Pretty.block (Pretty.str "  Deps:" :: Pretty.brk 2 ::
             Pretty.commas
              (map (Defs.pretty_entry (Proof_Context.defs_context axiom_lthy)) newT_deps))]))
  in ((RepC, AbsC, axiom_name, axiom), axiom_lthy) end;


(* derived bindings *)

type bindings = {Rep_name: binding, Abs_name: binding, type_definition_name: binding};

fun prefix_binding prfx name =
  Binding.reset_pos (Binding.qualify_name false name (prfx ^ Binding.name_of name));

fun qualify_binding name = Binding.qualify false (Binding.name_of name);

fun default_bindings name =
 {Rep_name = prefix_binding "Rep_" name,
  Abs_name = prefix_binding "Abs_" name,
  type_definition_name = prefix_binding "type_definition_" name};

fun make_bindings name NONE = default_bindings name
  | make_bindings _ (SOME bindings) = bindings;

fun make_morphisms name NONE = default_bindings name
  | make_morphisms name (SOME (Rep_name, Abs_name)) =
     {Rep_name = qualify_binding name Rep_name,
      Abs_name = qualify_binding name Abs_name,
      type_definition_name = #type_definition_name (default_bindings name)};


(* prepare_typedef *)

fun prepare_typedef prep_term overloaded (name, raw_args, mx) raw_set opt_bindings lthy =
  let
    (* rhs *)

    val tmp_ctxt = lthy |> fold (Variable.declare_typ o TFree) raw_args;
    val set = prep_term tmp_ctxt raw_set;
    val tmp_ctxt' = tmp_ctxt |> Variable.declare_term set;

    val setT = Term.fastype_of set;
    val oldT = HOLogic.dest_setT setT handle TYPE _ =>
      error ("Not a set type: " ^ quote (Syntax.string_of_typ lthy setT));

    val bname = Binding.name_of name;
    val goal = mk_inhabited set;
    val goal_pat = mk_inhabited (Var (the_default (bname, 0) (Lexicon.read_variable bname), setT));


    (* lhs *)

    val args = map (Proof_Context.check_tfree tmp_ctxt') raw_args;
    val (newT, typedecl_lthy) = lthy
      |> Typedecl.typedecl {final = false} (name, args, mx)
      ||> Variable.declare_term set;

    val Type (full_name, _) = newT;


    (* axiomatization *)

    val {Rep_name, Abs_name, type_definition_name} = make_bindings name opt_bindings;

    val ((RepC, AbsC, axiom_name, typedef), typedef_lthy) = typedecl_lthy
      |> primitive_typedef overloaded type_definition_name newT oldT Rep_name Abs_name set;

    val alias_lthy = typedef_lthy
      |> Local_Theory.const_alias Rep_name (#1 (Term.dest_Const RepC))
      |> Local_Theory.const_alias Abs_name (#1 (Term.dest_Const AbsC));


    (* result *)

    fun note ((b, atts), th) =
      Local_Theory.note ((b, atts), [th]) #>> (fn (_, [th']) => th');

    fun typedef_result inhabited lthy1 =
      let
        val ((_, [type_definition]), lthy2) = lthy1
          |> Local_Theory.note ((type_definition_name, []), [inhabited RS typedef]);
        fun make th = Goal.norm_result lthy2 (type_definition RS th);
        val (((((((((Rep, Rep_inverse), Abs_inverse), Rep_inject), Abs_inject), Rep_cases),
            Abs_cases), Rep_induct), Abs_induct), lthy3) = lthy2
          |> note ((Rep_name, []), make @{thm type_definition.Rep})
          ||>> note ((Binding.suffix_name "_inverse" Rep_name, []),
              make @{thm type_definition.Rep_inverse})
          ||>> note ((Binding.suffix_name "_inverse" Abs_name, []),
              make @{thm type_definition.Abs_inverse})
          ||>> note ((Binding.suffix_name "_inject" Rep_name, []),
              make @{thm type_definition.Rep_inject})
          ||>> note ((Binding.suffix_name "_inject" Abs_name, []),
              make @{thm type_definition.Abs_inject})
          ||>> note ((Binding.suffix_name "_cases" Rep_name,
                [Attrib.case_names [Binding.name_of Rep_name],
                 Attrib.internal (K (Induct.cases_pred full_name))]),
              make @{thm type_definition.Rep_cases})
          ||>> note ((Binding.suffix_name "_cases" Abs_name,
                [Attrib.case_names [Binding.name_of Abs_name],
                 Attrib.internal (K (Induct.cases_type full_name))]),
              make @{thm type_definition.Abs_cases})
          ||>> note ((Binding.suffix_name "_induct" Rep_name,
                [Attrib.case_names [Binding.name_of Rep_name],
                 Attrib.internal (K (Induct.induct_pred full_name))]),
              make @{thm type_definition.Rep_induct})
          ||>> note ((Binding.suffix_name "_induct" Abs_name,
                [Attrib.case_names [Binding.name_of Abs_name],
                 Attrib.internal (K (Induct.induct_type full_name))]),
              make @{thm type_definition.Abs_induct});

        val info =
          ({rep_type = oldT, abs_type = newT, Rep_name = #1 (Term.dest_Const RepC),
            Abs_name = #1 (Term.dest_Const AbsC), axiom_name = axiom_name},
           {inhabited = inhabited, type_definition = type_definition,
            Rep = Rep, Rep_inverse = Rep_inverse, Abs_inverse = Abs_inverse,
            Rep_inject = Rep_inject, Abs_inject = Abs_inject, Rep_cases = Rep_cases,
          Abs_cases = Abs_cases, Rep_induct = Rep_induct, Abs_induct = Abs_induct});
      in
        lthy3
        |> Local_Theory.declaration {syntax = false, pervasive = true}
          (fn phi => put_info full_name (transform_info phi info))
        |> Typedef_Plugin.data Plugin_Name.default_filter full_name
        |> pair (full_name, info)
      end;

  in ((goal, goal_pat, typedef_result), alias_lthy) end
  handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in typedef " ^ Binding.print name);


(* add_typedef: tactic interface *)

fun add_typedef overloaded typ set opt_bindings tac lthy =
  let
    val ((goal, _, typedef_result), lthy') =
      prepare_typedef Syntax.check_term overloaded typ set opt_bindings lthy;
    val inhabited = Goal.prove lthy' [] [] goal (tac o #context) |> Goal.norm_result lthy';
  in typedef_result inhabited lthy' end;

fun add_typedef_global overloaded typ set opt_bindings tac =
  Named_Target.theory_map_result (apsnd o transform_info)
    (add_typedef overloaded typ set opt_bindings tac)


(* typedef: proof interface *)

local

fun gen_typedef prep_term prep_constraint overloaded (b, raw_args, mx) set opt_bindings lthy =
  let
    val args = map (apsnd (prep_constraint lthy)) raw_args;
    val ((goal, goal_pat, typedef_result), lthy') =
      prepare_typedef prep_term overloaded (b, args, mx) set opt_bindings lthy;
    fun after_qed [[th]] = snd o typedef_result th;
  in Proof.theorem NONE after_qed [[(goal, [goal_pat])]] lthy' end;

in

val typedef = gen_typedef Syntax.check_term (K I);
val typedef_cmd = gen_typedef Syntax.read_term Typedecl.read_constraint;

end;



(** outer syntax **)

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>typedef\<close>
    "HOL type definition (requires non-emptiness proof)"
    (Parse_Spec.overloaded -- Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix --
      (\<^keyword>\<open>=\<close> |-- Parse.term) --
      Scan.option (\<^keyword>\<open>morphisms\<close> |-- Parse.!!! (Parse.binding -- Parse.binding))
    >> (fn (((((overloaded, vs), t), mx), A), opt_morphs) => fn lthy =>
        typedef_cmd {overloaded = overloaded} (t, vs, mx) A
          (SOME (make_morphisms t opt_morphs)) lthy));


val overloaded = typedef_overloaded;



(** theory export **)

val _ =
  (Theory.setup o Thy_Info.add_presentation) (fn context => fn thy =>
    if Export_Theory.export_enabled context then
      let
        val parent_spaces = map Sign.type_space (Theory.parents_of thy);
        val typedefs =
          Name_Space.dest_table (#types (Type.rep_tsig (Sign.tsig_of thy)))
          |> maps (fn (name, _) =>
              if exists (fn space => Name_Space.declared space name) parent_spaces then []
              else
                get_info_global thy name
                |> map (fn ({rep_type, abs_type, Rep_name, Abs_name, axiom_name}, _) =>
                  (name, (rep_type, (abs_type, (Rep_name, (Abs_name, axiom_name)))))));
        val encode =
          let open XML.Encode Term_XML.Encode
          in list (pair string (pair typ (pair typ (pair string (pair string string))))) end;
      in
        if null typedefs then ()
        else Export_Theory.export_body thy "typedefs" (encode typedefs)
      end
    else ());

end;
