(*  Title:      Pure/Isar/attrib.ML
    Author:     Markus Wenzel, TU Muenchen

Symbolic representation of attributes -- with name and syntax.
*)

signature ATTRIB =
sig
  type src = Args.src
  type binding = binding * src list
  val empty_binding: binding
  val is_empty_binding: binding -> bool
  val print_attributes: theory -> unit
  val intern: theory -> xstring -> string
  val intern_src: theory -> src -> src
  val pretty_attribs: Proof.context -> src list -> Pretty.T list
  val defined: theory -> string -> bool
  val attribute: theory -> src -> attribute
  val attribute_i: theory -> src -> attribute
  val map_specs: ('a list -> 'att list) ->
    (('c * 'a list) * 'b) list -> (('c * 'att list) * 'b) list
  val map_facts: ('a list -> 'att list) ->
    (('c * 'a list) * ('d * 'a list) list) list ->
    (('c * 'att list) * ('d * 'att list) list) list
  val map_facts_refs: ('a list -> 'att list) -> ('b -> 'fact) ->
    (('c * 'a list) * ('b * 'a list) list) list ->
    (('c * 'att list) * ('fact * 'att list) list) list
  val eval_thms: Proof.context -> (Facts.ref * src list) list -> thm list
  val setup: Binding.binding -> attribute context_parser -> string -> theory -> theory
  val attribute_setup: bstring * Position.T -> Symbol_Pos.text * Position.T -> string ->
    theory -> theory
  val add_del: attribute -> attribute -> attribute context_parser
  val thm_sel: Facts.interval list parser
  val thm: thm context_parser
  val thms: thm list context_parser
  val multi_thm: thm list context_parser
  val partial_evaluation: Proof.context ->
    (binding * (thm list * Args.src list) list) list ->
    (binding * (thm list * Args.src list) list) list
  val internal: (morphism -> attribute) -> src
  val print_configs: Proof.context -> unit
  val config_bool: Binding.binding ->
    (Context.generic -> bool) -> bool Config.T * (theory -> theory)
  val config_int: Binding.binding ->
    (Context.generic -> int) -> int Config.T * (theory -> theory)
  val config_real: Binding.binding ->
    (Context.generic -> real) -> real Config.T * (theory -> theory)
  val config_string: Binding.binding ->
    (Context.generic -> string) -> string Config.T * (theory -> theory)
  val setup_config_bool: Binding.binding -> (Context.generic -> bool) -> bool Config.T
  val setup_config_int: Binding.binding -> (Context.generic -> int) -> int Config.T
  val setup_config_string: Binding.binding -> (Context.generic -> string) -> string Config.T
  val setup_config_real: Binding.binding -> (Context.generic -> real) -> real Config.T
end;

structure Attrib: ATTRIB =
struct

(* source and bindings *)

type src = Args.src;

type binding = binding * src list;

val empty_binding: binding = (Binding.empty, []);
fun is_empty_binding ((b, srcs): binding) = Binding.is_empty b andalso null srcs;



(** named attributes **)

(* theory data *)

structure Attributes = Theory_Data
(
  type T = ((src -> attribute) * string) Name_Space.table;
  val empty : T = Name_Space.empty_table "attribute";
  val extend = I;
  fun merge data : T = Name_Space.merge_tables data;
);

fun print_attributes thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val attribs = Attributes.get thy;
    fun prt_attr (name, (_, "")) = Pretty.str name
      | prt_attr (name, (_, comment)) =
          Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
  in
    [Pretty.big_list "attributes:" (map prt_attr (Name_Space.extern_table ctxt attribs))]
    |> Pretty.chunks |> Pretty.writeln
  end;

fun add_attribute name att comment thy = thy
  |> Attributes.map (Name_Space.define (Context.Theory thy) true (name, (att, comment)) #> snd);


(* name space *)

val intern = Name_Space.intern o #1 o Attributes.get;
val intern_src = Args.map_name o intern;

fun extern ctxt = Name_Space.extern ctxt (#1 (Attributes.get (Proof_Context.theory_of ctxt)));


(* pretty printing *)

fun pretty_attribs _ [] = []
  | pretty_attribs ctxt srcs =
      [Pretty.enum "," "[" "]" (map (Args.pretty_src ctxt o Args.map_name (extern ctxt)) srcs)];


(* get attributes *)

val defined = Symtab.defined o #2 o Attributes.get;

fun attribute_i thy =
  let
    val (space, tab) = Attributes.get thy;
    fun attr src =
      let val ((name, _), pos) = Args.dest_src src in
        (case Symtab.lookup tab name of
          NONE => error ("Unknown attribute: " ^ quote name ^ Position.str_of pos)
        | SOME (att, _) => (Position.report pos (Name_Space.markup space name); att src))
      end;
  in attr end;

fun attribute thy = attribute_i thy o intern_src thy;


(* attributed declarations *)

fun map_specs f = map (apfst (apsnd f));

fun map_facts f = map (apfst (apsnd f) o apsnd (map (apsnd f)));
fun map_facts_refs f g = map_facts f #> map (apsnd (map (apfst g)));


(* fact expressions *)

fun eval_thms ctxt srcs = ctxt
  |> Proof_Context.note_thmss ""
    (map_facts_refs (map (attribute (Proof_Context.theory_of ctxt))) (Proof_Context.get_fact ctxt)
      [((Binding.empty, []), srcs)])
  |> fst |> maps snd;


(* attribute setup *)

fun syntax scan = Args.syntax "attribute" scan;

fun setup name scan =
  add_attribute name
    (fn src => fn (ctxt, th) => let val (a, ctxt') = syntax scan src ctxt in a (ctxt', th) end);

fun attribute_setup name (txt, pos) cmt =
  Context.theory_map (ML_Context.expression pos
    "val (name, scan, comment): binding * attribute context_parser * string"
    "Context.map_theory (Attrib.setup name scan comment)"
    (ML_Lex.read Position.none ("(" ^ ML_Syntax.make_binding name ^ ", ") @
      ML_Lex.read pos txt @
      ML_Lex.read Position.none (", " ^ ML_Syntax.print_string cmt ^ ")")));


(* add/del syntax *)

fun add_del add del = Scan.lift (Args.add >> K add || Args.del >> K del || Scan.succeed add);



(** parsing attributed theorems **)

val thm_sel = Parse.$$$ "(" |-- Parse.list1
 (Parse.nat --| Parse.minus -- Parse.nat >> Facts.FromTo ||
  Parse.nat --| Parse.minus >> Facts.From ||
  Parse.nat >> Facts.Single) --| Parse.$$$ ")";

local

val fact_name = Args.internal_fact >> K "<fact>" || Args.name;

fun gen_thm pick = Scan.depend (fn context =>
  let
    val thy = Context.theory_of context;
    val get = Context.cases (Global_Theory.get_fact context) Proof_Context.get_fact context;
    val get_fact = get o Facts.Fact;
    fun get_named pos name = get (Facts.Named ((name, pos), NONE));
  in
    Parse.$$$ "[" |-- Args.attribs (intern thy) --| Parse.$$$ "]" >> (fn srcs =>
      let
        val atts = map (attribute_i thy) srcs;
        val (th', context') = fold (uncurry o Thm.apply_attribute) atts (Drule.dummy_thm, context);
      in (context', pick "" [th']) end)
    ||
    (Scan.ahead Args.alt_name -- Args.named_fact get_fact
      >> (fn (s, fact) => ("", Facts.Fact s, fact)) ||
     Scan.ahead (Parse.position fact_name) :|-- (fn (name, pos) =>
      Args.named_fact (get_named pos) -- Scan.option thm_sel
        >> (fn (fact, sel) => (name, Facts.Named ((name, pos), sel), fact))))
    -- Args.opt_attribs (intern thy) >> (fn ((name, thmref, fact), srcs) =>
      let
        val ths = Facts.select thmref fact;
        val atts = map (attribute_i thy) srcs;
        val (ths', context') =
          fold_map (curry (fold (uncurry o Thm.apply_attribute) atts)) ths context;
      in (context', pick name ths') end)
  end);

in

val thm = gen_thm Facts.the_single;
val multi_thm = gen_thm (K I);
val thms = Scan.repeat multi_thm >> flat;

end;



(** partial evaluation -- observing rule/declaration/mixed attributes **)

local

val strict_eq_thm = op = o pairself Thm.rep_thm;

fun apply_att src (context, th) =
  let
    val src1 = Args.assignable src;
    val result = attribute_i (Context.theory_of context) src1 (context, th);
    val src2 = Args.closure src1;
  in (src2, result) end;

fun err msg src =
  let val ((name, _), pos) = Args.dest_src src
  in error (msg ^ " " ^ quote name ^ Position.str_of pos) end;

fun eval src ((th, dyn), (decls, context)) =
  (case (apply_att src (context, th), dyn) of
    ((_, (NONE, SOME th')), NONE) => ((th', NONE), (decls, context))
  | ((_, (NONE, SOME _)), SOME _) => err "Mixed dynamic attribute followed by static rule" src
  | ((src', (SOME context', NONE)), NONE) =>
      let
        val decls' =
          (case decls of
            [] => [(th, [src'])]
          | (th2, srcs2) :: rest =>
              if strict_eq_thm (th, th2)
              then ((th2, src' :: srcs2) :: rest)
              else (th, [src']) :: (th2, srcs2) :: rest);
      in ((th, NONE), (decls', context')) end
  | ((src', (opt_context', opt_th')), _) =>
      let
        val context' = the_default context opt_context';
        val th' = the_default th opt_th';
        val dyn' =
          (case dyn of
            NONE => SOME (th, [src'])
          | SOME (dyn_th, srcs) => SOME (dyn_th, src' :: srcs));
      in ((th', dyn'), (decls, context')) end);

in

fun partial_evaluation ctxt facts =
  (facts, Context.Proof (Context_Position.set_visible false ctxt)) |->
    fold_map (fn ((b, more_atts), fact) => fn context =>
      let
        val (fact', (decls, context')) =
          (fact, ([], context)) |-> fold_map (fn (ths, atts) => fn res1 =>
            (ths, res1) |-> fold_map (fn th => fn res2 =>
              let
                val ((th', dyn'), res3) = fold eval (atts @ more_atts) ((th, NONE), res2);
                val th_atts' =
                  (case dyn' of
                    NONE => (th', [])
                  | SOME (dyn_th', atts') => (dyn_th', rev atts'));
              in (th_atts', res3) end))
          |>> flat;
        val decls' = rev (map (apsnd rev) decls);
        val facts' =
          if eq_list (eq_fst strict_eq_thm) (decls', fact') then
            [((b, []), map2 (fn (th, atts1) => fn (_, atts2) => (th, atts1 @ atts2)) decls' fact')]
          else if null decls' then [((b, []), fact')]
          else [(empty_binding, decls'), ((b, []), fact')];
      in (facts', context') end)
  |> fst |> flat |> map (apsnd (map (apfst single)))
  |> filter_out (fn (b, fact) => is_empty_binding b andalso forall (null o #2) fact);

end;



(** basic attributes **)

(* internal *)

fun internal att = Args.src (("Pure.attribute", [Token.mk_attribute att]), Position.none);


(* rule composition *)

val COMP_att =
  Scan.lift (Scan.optional (Args.bracks Parse.nat) 1) -- thm
    >> (fn (i, B) => Thm.rule_attribute (fn _ => fn A => Drule.compose_single (A, i, B)));

val THEN_att =
  Scan.lift (Scan.optional (Args.bracks Parse.nat) 1) -- thm
    >> (fn (i, B) => Thm.rule_attribute (fn _ => fn A => A RSN (i, B)));

val OF_att =
  thms >> (fn Bs => Thm.rule_attribute (fn _ => fn A => Bs MRS A));


(* rename_abs *)

val rename_abs =
  Scan.repeat (Args.maybe Args.name)
  >> (fn args => Thm.rule_attribute (K (Drule.rename_bvars' args)));


(* unfold / fold definitions *)

fun unfolded_syntax rule =
  thms >> (fn ths => Thm.rule_attribute (fn context => rule (Context.proof_of context) ths));

val unfolded = unfolded_syntax Local_Defs.unfold;
val folded = unfolded_syntax Local_Defs.fold;


(* rule format *)

val rule_format = Args.mode "no_asm"
  >> (fn true => Object_Logic.rule_format_no_asm | false => Object_Logic.rule_format);

val elim_format = Thm.rule_attribute (K Tactic.make_elim);


(* case names *)

val case_names =
  Scan.repeat1 (Args.name --
    Scan.optional (Parse.$$$ "[" |-- Scan.repeat1 (Args.maybe Args.name) --| Parse.$$$ "]") []) >>
  (fn cs =>
    Rule_Cases.cases_hyp_names (map fst cs)
      (map (map (the_default Rule_Cases.case_hypsN) o snd) cs));


(* misc rules *)

val no_vars = Thm.rule_attribute (fn context => fn th =>
  let
    val ctxt = Variable.set_body false (Context.proof_of context);
    val ((_, [th']), _) = Variable.import true [th] ctxt;
  in th' end);

val eta_long =
  Thm.rule_attribute (K (Conv.fconv_rule Drule.eta_long_conversion));

val rotated = Scan.optional Parse.int 1 >> (fn n => Thm.rule_attribute (K (rotate_prems n)));


(* theory setup *)

val _ = Context.>> (Context.map_theory
 (setup (Binding.name "attribute") (Scan.lift Args.internal_attribute >> Morphism.form)
    "internal attribute" #>
  setup (Binding.name "tagged") (Scan.lift (Args.name -- Args.name) >> Thm.tag) "tagged theorem" #>
  setup (Binding.name "untagged") (Scan.lift Args.name >> Thm.untag) "untagged theorem" #>
  setup (Binding.name "kind") (Scan.lift Args.name >> Thm.kind) "theorem kind" #>
  setup (Binding.name "COMP") COMP_att "direct composition with rules (no lifting)" #>
  setup (Binding.name "THEN") THEN_att "resolution with rule" #>
  setup (Binding.name "OF") OF_att "rule applied to facts" #>
  setup (Binding.name "rename_abs") (Scan.lift rename_abs)
    "rename bound variables in abstractions" #>
  setup (Binding.name "unfolded") unfolded "unfolded definitions" #>
  setup (Binding.name "folded") folded "folded definitions" #>
  setup (Binding.name "consumes") (Scan.lift (Scan.optional Parse.nat 1) >> Rule_Cases.consumes)
    "number of consumed facts" #>
  setup (Binding.name "constraints") (Scan.lift Parse.nat >> Rule_Cases.constraints)
    "number of equality constraints" #>
  setup (Binding.name "case_names") (Scan.lift case_names) "named rule cases" #>
  setup (Binding.name "case_conclusion")
    (Scan.lift (Args.name -- Scan.repeat Args.name) >> Rule_Cases.case_conclusion)
    "named conclusion of rule cases" #>
  setup (Binding.name "params")
    (Scan.lift (Parse.and_list1 (Scan.repeat Args.name)) >> Rule_Cases.params)
    "named rule parameters" #>
  setup (Binding.name "standard") (Scan.succeed (Thm.rule_attribute (K Drule.export_without_context)))
    "result put into standard form (legacy)" #>
  setup (Binding.name "rule_format") rule_format "result put into canonical rule format" #>
  setup (Binding.name "elim_format") (Scan.succeed elim_format)
    "destruct rule turned into elimination rule format" #>
  setup (Binding.name "no_vars") (Scan.succeed no_vars) "frozen schematic vars" #>
  setup (Binding.name "eta_long") (Scan.succeed eta_long)
    "put theorem into eta long beta normal form" #>
  setup (Binding.name "atomize") (Scan.succeed Object_Logic.declare_atomize)
    "declaration of atomize rule" #>
  setup (Binding.name "rulify") (Scan.succeed Object_Logic.declare_rulify)
    "declaration of rulify rule" #>
  setup (Binding.name "rotated") (Scan.lift rotated) "rotated theorem premises" #>
  setup (Binding.name "defn") (add_del Local_Defs.defn_add Local_Defs.defn_del)
    "declaration of definitional transformations" #>
  setup (Binding.name "abs_def")
    (Scan.succeed (Thm.rule_attribute (fn context =>
      Local_Defs.meta_rewrite_rule (Context.proof_of context) #> Drule.abs_def)))
    "abstract over free variables of definitionial theorem"));



(** configuration options **)

(* naming *)

structure Configs = Theory_Data
(
  type T = Config.raw Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

fun print_configs ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun prt (name, config) =
      let val value = Config.get ctxt config in
        Pretty.block [Pretty.str (name ^ ": " ^ Config.print_type value ^ " ="), Pretty.brk 1,
          Pretty.str (Config.print_value value)]
      end;
    val configs = Name_Space.extern_table ctxt (#1 (Attributes.get thy), Configs.get thy);
  in Pretty.writeln (Pretty.big_list "configuration options" (map prt configs)) end;


(* concrete syntax *)

local

val equals = Parse.$$$ "=";

fun scan_value (Config.Bool _) =
      equals -- Args.$$$ "false" >> K (Config.Bool false) ||
      equals -- Args.$$$ "true" >> K (Config.Bool true) ||
      Scan.succeed (Config.Bool true)
  | scan_value (Config.Int _) = equals |-- Parse.int >> Config.Int
  | scan_value (Config.Real _) = equals |-- Parse.real >> Config.Real
  | scan_value (Config.String _) = equals |-- Args.name >> Config.String;

fun scan_config thy config =
  let val config_type = Config.get_global thy config
  in scan_value config_type >> (K o Thm.declaration_attribute o K o Config.put_generic config) end;

fun register binding config thy =
  let val name = Sign.full_name thy binding in
    thy
    |> setup binding (Scan.lift (scan_config thy config) >> Morphism.form) "configuration option"
    |> Configs.map (Symtab.update (name, config))
  end;

fun declare make coerce binding default =
  let
    val name = Binding.name_of binding;
    val config_value = Config.declare_generic {global = false} name (make o default);
    val config = coerce config_value;
  in (config, register binding config_value) end;

in

val config_bool = declare Config.Bool Config.bool;
val config_int = declare Config.Int Config.int;
val config_real = declare Config.Real Config.real;
val config_string = declare Config.String Config.string;

fun register_config config = register (Binding.name (Config.name_of config)) config;

end;


(* implicit setup *)

local

fun setup_config declare_config binding default =
  let
    val (config, setup) = declare_config binding default;
    val _ = Context.>> (Context.map_theory setup);
  in config end;

in

val setup_config_bool = setup_config config_bool;
val setup_config_int = setup_config config_int;
val setup_config_string = setup_config config_string;
val setup_config_real = setup_config config_real;

end;


(* theory setup *)

val _ = Context.>> (Context.map_theory
 (register_config Ast.trace_raw #>
  register_config Ast.stats_raw #>
  register_config Printer.show_brackets_raw #>
  register_config Printer.show_sorts_raw #>
  register_config Printer.show_types_raw #>
  register_config Printer.show_structs_raw #>
  register_config Printer.show_question_marks_raw #>
  register_config Syntax.ambiguity_warning_raw #>
  register_config Syntax.ambiguity_limit_raw #>
  register_config Syntax_Trans.eta_contract_raw #>
  register_config Name_Space.names_long_raw #>
  register_config Name_Space.names_short_raw #>
  register_config Name_Space.names_unique_raw #>
  register_config ML_Context.trace_raw #>
  register_config Proof_Context.show_abbrevs_raw #>
  register_config Goal_Display.goals_limit_raw #>
  register_config Goal_Display.show_main_goal_raw #>
  register_config Goal_Display.show_consts_raw #>
  register_config Display.show_hyps_raw #>
  register_config Display.show_tags_raw #>
  register_config Unify.trace_bound_raw #>
  register_config Unify.search_bound_raw #>
  register_config Unify.trace_simp_raw #>
  register_config Unify.trace_types_raw #>
  register_config Raw_Simplifier.simp_depth_limit_raw #>
  register_config Raw_Simplifier.simp_trace_depth_limit_raw #>
  register_config Raw_Simplifier.simp_debug_raw #>
  register_config Raw_Simplifier.simp_trace_raw));

end;
