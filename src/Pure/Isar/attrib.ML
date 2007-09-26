(*  Title:      Pure/Isar/attrib.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Symbolic representation of attributes -- with name and syntax.
*)

signature BASIC_ATTRIB =
sig
  val print_attributes: theory -> unit
end;

signature ATTRIB =
sig
  include BASIC_ATTRIB
  type src
  val intern: theory -> xstring -> string
  val intern_src: theory -> src -> src
  val pretty_attribs: Proof.context -> src list -> Pretty.T list
  val attribute: theory -> src -> attribute
  val attribute_i: theory -> src -> attribute
  val eval_thms: Proof.context -> (thmref * src list) list -> thm list
  val map_specs: ('a -> 'att) ->
    (('c * 'a list) * 'd) list -> (('c * 'att list) * 'd) list
  val map_facts: ('a -> 'att) ->
    (('c * 'a list) * ('d * 'a list) list) list ->
    (('c * 'att list) * ('d * 'att list) list) list
  val crude_closure: Proof.context -> src -> src
  val add_attributes: (bstring * (src -> attribute) * string) list -> theory -> theory
  val print_configs: Proof.context -> unit
  val register_config: Config.value Config.T -> theory -> theory
  val config_bool: bstring -> bool -> bool Config.T * (theory -> theory)
  val config_int: bstring -> int -> int Config.T * (theory -> theory)
  val config_string: bstring -> string -> string Config.T * (theory -> theory)
  val config_bool_global: bstring -> bool -> bool Config.T * (theory -> theory)
  val config_int_global: bstring -> int -> int Config.T * (theory -> theory)
  val config_string_global: bstring -> string -> string Config.T * (theory -> theory)
  val thm: Context.generic * Args.T list -> thm * (Context.generic * Args.T list)
  val thms: Context.generic * Args.T list -> thm list * (Context.generic * Args.T list)
  val multi_thm: Context.generic * Args.T list -> thm list * (Context.generic * Args.T list)
  val syntax: (Context.generic * Args.T list ->
    attribute * (Context.generic * Args.T list)) -> src -> attribute
  val no_args: attribute -> src -> attribute
  val add_del_args: attribute -> attribute -> src -> attribute
  val internal: (morphism -> attribute) -> src
end;

structure Attrib: ATTRIB =
struct

type src = Args.src;


(** named attributes **)

(* theory data *)

structure Attributes = TheoryDataFun
(
  type T = (((src -> attribute) * string) * stamp) NameSpace.table;
  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;
  fun merge _ tables : T = NameSpace.merge_tables (eq_snd (op =)) tables handle Symtab.DUP dup =>
    error ("Attempt to merge different versions of attribute " ^ quote dup);
);

fun print_attributes thy =
  let
    val attribs = Attributes.get thy;
    fun prt_attr (name, ((_, comment), _)) = Pretty.block
      [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
  in
    [Pretty.big_list "attributes:" (map prt_attr (NameSpace.extern_table attribs))]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* name space *)

val intern = NameSpace.intern o #1 o Attributes.get;
val intern_src = Args.map_name o intern;

val extern = NameSpace.extern o #1 o Attributes.get o ProofContext.theory_of;


(* pretty printing *)

fun pretty_attribs _ [] = []
  | pretty_attribs ctxt srcs =
      [Pretty.enclose "[" "]"
        (Pretty.commas (map (Args.pretty_src ctxt o Args.map_name (extern ctxt)) srcs))];


(* get attributes *)

fun attribute_i thy =
  let
    val attrs = #2 (Attributes.get thy);
    fun attr src =
      let val ((name, _), pos) = Args.dest_src src in
        (case Symtab.lookup attrs name of
          NONE => error ("Unknown attribute: " ^ quote name ^ Position.str_of pos)
        | SOME ((att, _), _) => att src)
      end;
  in attr end;

fun attribute thy = attribute_i thy o intern_src thy;

fun eval_thms ctxt args = ProofContext.note_thmss Thm.theoremK
  [(("", []), map (apsnd (map (attribute (ProofContext.theory_of ctxt)))) args)] ctxt
  |> (flat o map snd o fst);


(* attributed declarations *)

fun map_specs f = map (apfst (apsnd (map f)));
fun map_facts f = map (apfst (apsnd (map f)) o apsnd (map (apsnd (map f))));


(* crude_closure *)

(*Produce closure without knowing facts in advance! The following
  works reasonably well for attribute parsers that do not peek at the
  thm structure.*)

fun crude_closure ctxt src =
 (try (fn () => attribute_i (ProofContext.theory_of ctxt) src
    (Context.Proof ctxt, Drule.asm_rl)) ();
  Args.closure src);


(* add_attributes *)

fun add_attributes raw_attrs thy =
  let
    val new_attrs =
      raw_attrs |> map (fn (name, att, comment) => (name, ((att, comment), stamp ())));
    fun add attrs = NameSpace.extend_table (Sign.naming_of thy) new_attrs attrs
      handle Symtab.DUP dup => error ("Duplicate declaration of attributes " ^ quote dup);
  in Attributes.map add thy end;



(** attribute parsers **)

(* tags *)

fun tag x = Scan.lift (Args.name -- Args.name) x;


(* theorems *)

local

val get_thms = Context.cases PureThy.get_thms ProofContext.get_thms;

val fact_name = Args.internal_fact >> K "<fact>" || Args.name;

fun gen_thm pick = Scan.depend (fn st =>
  Args.$$$ "[" |-- Args.attribs (intern (Context.theory_of st)) --| Args.$$$ "]"
    >> (fn srcs =>
      let
        val atts = map (attribute_i (Context.theory_of st)) srcs;
        val (st', th') = Library.apply atts (st, Drule.dummy_thm);
      in (st', pick "" [th']) end) ||
  (Scan.ahead Args.alt_name -- Args.named_fact (get_thms st o Fact)
    >> (fn (s, fact) => ("", Fact s, fact)) ||
  Scan.ahead fact_name -- Args.named_fact (get_thms st o Name) -- Args.thm_sel
    >> (fn ((name, fact), sel) => (name, NameSelection (name, sel), fact)) ||
  Scan.ahead fact_name -- Args.named_fact (get_thms st o Name)
    >> (fn (name, fact) => (name, Name name, fact)))
  -- Args.opt_attribs (intern (Context.theory_of st))
  >> (fn ((name, thmref, fact), srcs) =>
    let
      val ths = PureThy.select_thm thmref fact;
      val atts = map (attribute_i (Context.theory_of st)) srcs;
      val (st', ths') = foldl_map (Library.apply atts) (st, ths);
    in (st', pick name ths') end));

in

val thm = gen_thm PureThy.single_thm;
val multi_thm = gen_thm (K I);
val thms = Scan.repeat multi_thm >> flat;

end;



(** attribute syntax **)

fun syntax scan src (st, th) =
  let val (f, st') = Args.syntax "attribute" scan src st
  in f (st', th) end;

fun no_args x = syntax (Scan.succeed x);

fun add_del_args add del x = syntax
  (Scan.lift (Args.add >> K add || Args.del >> K del || Scan.succeed add)) x;



(** configuration options **)

(* naming *)

structure Configs = TheoryDataFun
(
  type T = Config.value Config.T Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge (K true);
);

fun print_configs ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    fun prt (name, config) =
      let val value = Config.get ctxt config in
        Pretty.block [Pretty.str (name ^ ": " ^ Config.print_type value ^ " ="), Pretty.brk 1,
          Pretty.str (Config.print_value value)]
      end;
    val configs = NameSpace.extern_table (#1 (Attributes.get thy), Configs.get thy);
  in Pretty.writeln (Pretty.big_list "configuration options" (map prt configs)) end;


(* concrete syntax *)

local

val equals = Args.$$$ "=";

fun scan_value (Config.Bool _) =
      equals -- Args.$$$ "false" >> K (Config.Bool false) ||
      equals -- Args.$$$ "true" >> K (Config.Bool true) ||
      Scan.succeed (Config.Bool true)
  | scan_value (Config.Int _) = equals |-- Args.int >> Config.Int
  | scan_value (Config.String _) = equals |-- Args.name >> Config.String;

fun scan_config thy config =
  let val config_type = Config.get_thy thy config
  in scan_value config_type >> (K o Thm.declaration_attribute o K o Config.put_generic config) end;

in

fun register_config config thy =
  let
    val bname = Config.name_of config;
    val name = Sign.full_name thy bname;
  in
    thy
    |> add_attributes [(bname, syntax (Scan.lift (scan_config thy config) >> Morphism.form),
      "configuration option")]
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



(** basic attributes **)

(* tags *)

fun tagged x = syntax (tag >> PureThy.tag) x;
fun untagged x = syntax (Scan.lift Args.name >> PureThy.untag) x;

fun kind x = syntax (Scan.lift Args.name >> PureThy.kind) x;


(* rule composition *)

val COMP_att =
  syntax (Scan.lift (Scan.optional (Args.bracks Args.nat) 1) -- thm
    >> (fn (i, B) => Thm.rule_attribute (fn _ => fn A => Drule.compose_single (A, i, B))));

val THEN_att =
  syntax (Scan.lift (Scan.optional (Args.bracks Args.nat) 1) -- thm
    >> (fn (i, B) => Thm.rule_attribute (fn _ => fn A => A RSN (i, B))));

val OF_att =
  syntax (thms >> (fn Bs => Thm.rule_attribute (fn _ => fn A => Bs MRS A)));


(* rename_abs *)

fun rename_abs src = syntax
  (Scan.lift (Scan.repeat (Args.maybe Args.name) >> (apsnd o Drule.rename_bvars'))) src;


(* unfold / fold definitions *)

fun unfolded_syntax rule =
  syntax (thms >>
    (fn ths => Thm.rule_attribute (fn context => rule (Context.proof_of context) ths)));

val unfolded = unfolded_syntax LocalDefs.unfold;
val folded = unfolded_syntax LocalDefs.fold;


(* rule cases *)

fun consumes x = syntax (Scan.lift (Scan.optional Args.nat 1) >> RuleCases.consumes) x;
fun case_names x = syntax (Scan.lift (Scan.repeat1 Args.name) >> RuleCases.case_names) x;
fun case_conclusion x =
  syntax (Scan.lift (Args.name -- Scan.repeat Args.name) >> RuleCases.case_conclusion) x;
fun params x = syntax (Args.and_list1 (Scan.lift (Scan.repeat Args.name)) >> RuleCases.params) x;


(* rule format *)

fun rule_format_att x = syntax (Args.mode "no_asm"
  >> (fn true => ObjectLogic.rule_format_no_asm | false => ObjectLogic.rule_format)) x;

fun elim_format x = no_args (Thm.rule_attribute (K Tactic.make_elim)) x;


(* misc rules *)

fun standard x = no_args (Thm.rule_attribute (K Drule.standard)) x;

fun no_vars x = no_args (Thm.rule_attribute (fn ctxt => fn th =>
  let val ((_, [th']), _) = Variable.import_thms true [th] (Context.proof_of ctxt)
  in th' end)) x;

fun eta_long x =
  no_args (Thm.rule_attribute (K (Conv.fconv_rule Drule.eta_long_conversion))) x;


(* internal attribute *)

fun internal att = Args.src (("Pure.attribute", [Args.mk_attribute att]), Position.none);

fun internal_att x =
  syntax (Scan.lift Args.internal_attribute >> Morphism.form) x;


(* attribute rotated *)

fun rotated_att x = 
  syntax (Scan.lift (Scan.optional Args.int 1) >> 
                    (fn n => Thm.rule_attribute (fn _ => rotate_prems n))) x


(* theory setup *)

val _ = Context.add_setup
 (register_config Unify.trace_bound_value #>
  register_config Unify.search_bound_value #>
  register_config Unify.trace_simp_value #>
  register_config Unify.trace_types_value #>
  register_config MetaSimplifier.simp_depth_limit_value #>
  add_attributes
   [("tagged", tagged, "tagged theorem"),
    ("untagged", untagged, "untagged theorem"),
    ("kind", kind, "theorem kind"),
    ("COMP", COMP_att, "direct composition with rules (no lifting)"),
    ("THEN", THEN_att, "resolution with rule"),
    ("OF", OF_att, "rule applied to facts"),
    ("rename_abs", rename_abs, "rename bound variables in abstractions"),
    ("unfolded", unfolded, "unfolded definitions"),
    ("folded", folded, "folded definitions"),
    ("standard", standard, "result put into standard form"),
    ("elim_format", elim_format, "destruct rule turned into elimination rule format"),
    ("no_vars", no_vars, "frozen schematic vars"),
    ("eta_long", eta_long, "put theorem into eta long beta normal form"),
    ("consumes", consumes, "number of consumed facts"),
    ("case_names", case_names, "named rule cases"),
    ("case_conclusion", case_conclusion, "named conclusion of rule cases"),
    ("params", params, "named rule parameters"),
    ("atomize", no_args ObjectLogic.declare_atomize, "declaration of atomize rule"),
    ("rulify", no_args ObjectLogic.declare_rulify, "declaration of rulify rule"),
    ("rule_format", rule_format_att, "result put into standard rule format"),
    ("rotated", rotated_att, "rotated theorem premises"),
    ("defn", add_del_args LocalDefs.defn_add LocalDefs.defn_del,
      "declaration of definitional transformations"),
    ("attribute", internal_att, "internal attribute")]);

end;

structure BasicAttrib: BASIC_ATTRIB = Attrib;
open BasicAttrib;
