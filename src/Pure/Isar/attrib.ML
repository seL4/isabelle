(*  Title:      Pure/Isar/attrib.ML
    Author:     Markus Wenzel, TU Muenchen

Symbolic representation of attributes -- with name and syntax.
*)

signature ATTRIB =
sig
  type src = Args.src
  type binding = binding * src list
  val empty_binding: binding
  val print_attributes: theory -> unit
  val intern: theory -> xstring -> string
  val intern_src: theory -> src -> src
  val pretty_attribs: Proof.context -> src list -> Pretty.T list
  val defined: theory -> string -> bool
  val attribute: theory -> src -> attribute
  val attribute_i: theory -> src -> attribute
  val eval_thms: Proof.context -> (Facts.ref * src list) list -> thm list
  val map_specs: ('a -> 'att) ->
    (('c * 'a list) * 'b) list -> (('c * 'att list) * 'b) list
  val map_facts: ('a -> 'att) ->
    (('c * 'a list) * ('d * 'a list) list) list ->
    (('c * 'att list) * ('d * 'att list) list) list
  val map_facts_refs: ('a -> 'att) -> ('b -> 'fact) ->
    (('c * 'a list) * ('b * 'a list) list) list ->
    (('c * 'att list) * ('fact * 'att list) list) list
  val crude_closure: Proof.context -> src -> src
  val setup: Binding.binding -> attribute context_parser -> string -> theory -> theory
  val attribute_setup: bstring * Position.T -> Symbol_Pos.text * Position.T -> string ->
    theory -> theory
  val add_del: attribute -> attribute -> attribute context_parser
  val thm_sel: Facts.interval list parser
  val thm: thm context_parser
  val thms: thm list context_parser
  val multi_thm: thm list context_parser
  val print_configs: Proof.context -> unit
  val internal: (morphism -> attribute) -> src
  val register_config: Config.value Config.T -> theory -> theory
  val config_bool: bstring -> bool -> bool Config.T * (theory -> theory)
  val config_int: bstring -> int -> int Config.T * (theory -> theory)
  val config_string: bstring -> string -> string Config.T * (theory -> theory)
  val config_bool_global: bstring -> bool -> bool Config.T * (theory -> theory)
  val config_int_global: bstring -> int -> int Config.T * (theory -> theory)
  val config_string_global: bstring -> string -> string Config.T * (theory -> theory)
end;

structure Attrib: ATTRIB =
struct

structure T = OuterLex;
structure P = OuterParse;


(* source and bindings *)

type src = Args.src;

type binding = binding * src list;
val empty_binding: binding = (Binding.empty, []);



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
    val attribs = Attributes.get thy;
    fun prt_attr (name, (_, comment)) = Pretty.block
      [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
  in
    [Pretty.big_list "attributes:" (map prt_attr (Name_Space.extern_table attribs))]
    |> Pretty.chunks |> Pretty.writeln
  end;

fun add_attribute name att comment thy = thy
  |> Attributes.map (#2 o Name_Space.define true (Sign.naming_of thy) (name, (att, comment)));


(* name space *)

val intern = Name_Space.intern o #1 o Attributes.get;
val intern_src = Args.map_name o intern;

val extern = Name_Space.extern o #1 o Attributes.get o ProofContext.theory_of;


(* pretty printing *)

fun pretty_attribs _ [] = []
  | pretty_attribs ctxt srcs =
      [Pretty.enclose "[" "]"
        (Pretty.commas (map (Args.pretty_src ctxt o Args.map_name (extern ctxt)) srcs))];


(* get attributes *)

val defined = Symtab.defined o #2 o Attributes.get;

fun attribute_i thy =
  let
    val attrs = #2 (Attributes.get thy);
    fun attr src =
      let val ((name, _), pos) = Args.dest_src src in
        (case Symtab.lookup attrs name of
          NONE => error ("Unknown attribute: " ^ quote name ^ Position.str_of pos)
        | SOME (att, _) => (Position.report (Markup.attribute name) pos; att src))
      end;
  in attr end;

fun attribute thy = attribute_i thy o intern_src thy;

fun eval_thms ctxt args = ProofContext.note_thmss ""
    [(Thm.empty_binding, args |> map (fn (a, atts) =>
        (ProofContext.get_fact ctxt a, map (attribute (ProofContext.theory_of ctxt)) atts)))] ctxt
  |> fst |> maps snd;


(* attributed declarations *)

fun map_specs f = map (apfst (apsnd (map f)));

fun map_facts f = map (apfst (apsnd (map f)) o apsnd (map (apsnd (map f))));
fun map_facts_refs f g = map_facts f #> map (apsnd (map (apfst g)));


(* crude_closure *)

(*Produce closure without knowing facts in advance! The following
  works reasonably well for attribute parsers that do not peek at the
  thm structure.*)

fun crude_closure ctxt src =
 (try (fn () => attribute_i (ProofContext.theory_of ctxt) src
    (Context.Proof ctxt, Drule.asm_rl)) ();
  Args.closure src);


(* attribute setup *)

fun syntax scan = Args.syntax "attribute" scan;

fun setup name scan =
  add_attribute name
    (fn src => fn (ctxt, th) => let val (a, ctxt') = syntax scan src ctxt in a (ctxt', th) end);

fun attribute_setup name (txt, pos) cmt =
  Context.theory_map (ML_Context.expression pos
    "val (name, scan, comment): binding * attribute context_parser * string"
    "Context.map_theory (Attrib.setup name scan comment)"
    ("(" ^ ML_Syntax.make_binding name ^ ", " ^ txt ^ ", " ^ ML_Syntax.print_string cmt ^ ")"));


(* add/del syntax *)

fun add_del add del = Scan.lift (Args.add >> K add || Args.del >> K del || Scan.succeed add);



(** parsing attributed theorems **)

val thm_sel = P.$$$ "(" |-- P.list1
 (P.nat --| P.minus -- P.nat >> Facts.FromTo ||
  P.nat --| P.minus >> Facts.From ||
  P.nat >> Facts.Single) --| P.$$$ ")";

local

val fact_name = Args.internal_fact >> K "<fact>" || Args.name;

fun gen_thm pick = Scan.depend (fn context =>
  let
    val thy = Context.theory_of context;
    val get = Context.cases (PureThy.get_fact context) ProofContext.get_fact context;
    val get_fact = get o Facts.Fact;
    fun get_named pos name = get (Facts.Named ((name, pos), NONE));
  in
    P.$$$ "[" |-- Args.attribs (intern thy) --| P.$$$ "]" >> (fn srcs =>
      let
        val atts = map (attribute_i thy) srcs;
        val (context', th') = Library.apply atts (context, Drule.dummy_thm);
      in (context', pick "" [th']) end)
    ||
    (Scan.ahead Args.alt_name -- Args.named_fact get_fact
      >> (fn (s, fact) => ("", Facts.Fact s, fact)) ||
     Scan.ahead (P.position fact_name) :|-- (fn (name, pos) =>
      Args.named_fact (get_named pos) -- Scan.option thm_sel
        >> (fn (fact, sel) => (name, Facts.Named ((name, pos), sel), fact))))
    -- Args.opt_attribs (intern thy) >> (fn ((name, thmref, fact), srcs) =>
      let
        val ths = Facts.select thmref fact;
        val atts = map (attribute_i thy) srcs;
        val (context', ths') = Library.foldl_map (Library.apply atts) (context, ths);
      in (context', pick name ths') end)
  end);

in

val thm = gen_thm Facts.the_single;
val multi_thm = gen_thm (K I);
val thms = Scan.repeat multi_thm >> flat;

end;



(** basic attributes **)

(* internal *)

fun internal att = Args.src (("Pure.attribute", [T.mk_attribute att]), Position.none);


(* rule composition *)

val COMP_att =
  Scan.lift (Scan.optional (Args.bracks P.nat) 1) -- thm
    >> (fn (i, B) => Thm.rule_attribute (fn _ => fn A => Drule.compose_single (A, i, B)));

val THEN_att =
  Scan.lift (Scan.optional (Args.bracks P.nat) 1) -- thm
    >> (fn (i, B) => Thm.rule_attribute (fn _ => fn A => A RSN (i, B)));

val OF_att =
  thms >> (fn Bs => Thm.rule_attribute (fn _ => fn A => Bs MRS A));


(* rename_abs *)

fun rename_abs x = (Scan.repeat (Args.maybe Args.name) >> (apsnd o Drule.rename_bvars')) x;


(* unfold / fold definitions *)

fun unfolded_syntax rule =
  thms >> (fn ths => Thm.rule_attribute (fn context => rule (Context.proof_of context) ths));

val unfolded = unfolded_syntax LocalDefs.unfold;
val folded = unfolded_syntax LocalDefs.fold;


(* rule format *)

val rule_format = Args.mode "no_asm"
  >> (fn true => ObjectLogic.rule_format_no_asm | false => ObjectLogic.rule_format);

val elim_format = Thm.rule_attribute (K Tactic.make_elim);


(* misc rules *)

val no_vars = Thm.rule_attribute (fn context => fn th =>
  let
    val ctxt = Variable.set_body false (Context.proof_of context);
    val ((_, [th']), _) = Variable.import true [th] ctxt;
  in th' end);

val eta_long =
  Thm.rule_attribute (K (Conv.fconv_rule Drule.eta_long_conversion));

val rotated = Scan.optional P.int 1 >> (fn n => Thm.rule_attribute (K (rotate_prems n)));


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
  setup (Binding.name "consumes") (Scan.lift (Scan.optional P.nat 1) >> Rule_Cases.consumes)
    "number of consumed facts" #>
  setup (Binding.name "constraints") (Scan.lift P.nat >> Rule_Cases.constraints)
    "number of equality constraints" #>
  setup (Binding.name "case_names") (Scan.lift (Scan.repeat1 Args.name) >> Rule_Cases.case_names)
    "named rule cases" #>
  setup (Binding.name "case_conclusion")
    (Scan.lift (Args.name -- Scan.repeat Args.name) >> Rule_Cases.case_conclusion)
    "named conclusion of rule cases" #>
  setup (Binding.name "params")
    (Scan.lift (P.and_list1 (Scan.repeat Args.name)) >> Rule_Cases.params)
    "named rule parameters" #>
  setup (Binding.name "standard") (Scan.succeed (Thm.rule_attribute (K Drule.standard)))
    "result put into standard form (legacy)" #>
  setup (Binding.name "rule_format") rule_format "result put into canonical rule format" #>
  setup (Binding.name "elim_format") (Scan.succeed elim_format)
    "destruct rule turned into elimination rule format" #>
  setup (Binding.name "no_vars") (Scan.succeed no_vars) "frozen schematic vars" #>
  setup (Binding.name "eta_long") (Scan.succeed eta_long)
    "put theorem into eta long beta normal form" #>
  setup (Binding.name "atomize") (Scan.succeed ObjectLogic.declare_atomize)
    "declaration of atomize rule" #>
  setup (Binding.name "rulify") (Scan.succeed ObjectLogic.declare_rulify)
    "declaration of rulify rule" #>
  setup (Binding.name "rotated") (Scan.lift rotated) "rotated theorem premises" #>
  setup (Binding.name "defn") (add_del LocalDefs.defn_add LocalDefs.defn_del)
    "declaration of definitional transformations" #>
  setup (Binding.name "abs_def") (Scan.succeed (Thm.rule_attribute (K Drule.abs_def)))
    "abstract over free variables of a definition"));



(** configuration options **)

(* naming *)

structure Configs = Theory_Data
(
  type T = Config.value Config.T Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

fun print_configs ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    fun prt (name, config) =
      let val value = Config.get ctxt config in
        Pretty.block [Pretty.str (name ^ ": " ^ Config.print_type value ^ " ="), Pretty.brk 1,
          Pretty.str (Config.print_value value)]
      end;
    val configs = Name_Space.extern_table (#1 (Attributes.get thy), Configs.get thy);
  in Pretty.writeln (Pretty.big_list "configuration options" (map prt configs)) end;


(* concrete syntax *)

local

val equals = P.$$$ "=";

fun scan_value (Config.Bool _) =
      equals -- Args.$$$ "false" >> K (Config.Bool false) ||
      equals -- Args.$$$ "true" >> K (Config.Bool true) ||
      Scan.succeed (Config.Bool true)
  | scan_value (Config.Int _) = equals |-- P.int >> Config.Int
  | scan_value (Config.String _) = equals |-- Args.name >> Config.String;

fun scan_config thy config =
  let val config_type = Config.get_thy thy config
  in scan_value config_type >> (K o Thm.declaration_attribute o K o Config.put_generic config) end;

in

fun register_config config thy =
  let
    val bname = Config.name_of config;
    val name = Sign.full_bname thy bname;
  in
    thy
    |> setup (Binding.name bname) (Scan.lift (scan_config thy config) >> Morphism.form)
      "configuration option"
    |> Configs.map (Symtab.update (name, config))
  end;

fun declare_config make coerce global name default =
  let
    val config_value = Config.declare global name (make default);
    val config = coerce config_value;
  in (config, register_config config_value) end;

val config_bool   = declare_config Config.Bool Config.bool false;
val config_int    = declare_config Config.Int Config.int false;
val config_string = declare_config Config.String Config.string false;

val config_bool_global   = declare_config Config.Bool Config.bool true;
val config_int_global    = declare_config Config.Int Config.int true;
val config_string_global = declare_config Config.String Config.string true;

end;


(* theory setup *)

val _ = Context.>> (Context.map_theory
 (register_config Unify.trace_bound_value #>
  register_config Unify.search_bound_value #>
  register_config Unify.trace_simp_value #>
  register_config Unify.trace_types_value #>
  register_config MetaSimplifier.simp_depth_limit_value));

end;
