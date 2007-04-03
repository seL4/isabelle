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
  exception ATTRIB_FAIL of (string * Position.T) * exn
  val intern: theory -> xstring -> string
  val intern_src: theory -> src -> src
  val pretty_attribs: Proof.context -> src list -> Pretty.T list
  val attribute: theory -> src -> attribute
  val attribute_i: theory -> src -> attribute
  val map_specs: ('a -> 'att) ->
    (('c * 'a list) * 'd) list -> (('c * 'att list) * 'd) list
  val map_facts: ('a -> 'att) ->
    (('c * 'a list) * ('d * 'a list) list) list ->
    (('c * 'att list) * ('d * 'att list) list) list
  val crude_closure: Proof.context -> src -> src
  val add_attributes: (bstring * (src -> attribute) * string) list -> theory -> theory
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

structure AttributesData = TheoryDataFun
(struct
  val name = "Isar/attributes";
  type T = (((src -> attribute) * string) * stamp) NameSpace.table;

  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;

  fun merge _ tables = NameSpace.merge_tables (eq_snd (op =)) tables handle Symtab.DUPS dups =>
    error ("Attempt to merge different versions of attribute(s) " ^ commas_quote dups);

  fun print _ attribs =
    let
      fun prt_attr (name, ((_, comment), _)) = Pretty.block
        [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    in
      [Pretty.big_list "attributes:" (map prt_attr (NameSpace.extern_table attribs))]
      |> Pretty.chunks |> Pretty.writeln
    end;
end);

val _ = Context.add_setup AttributesData.init;
val print_attributes = AttributesData.print;


(* name space *)

val intern = NameSpace.intern o #1 o AttributesData.get;
val intern_src = Args.map_name o intern;

val extern = NameSpace.extern o #1 o AttributesData.get o ProofContext.theory_of;


(* pretty printing *)

fun pretty_attribs _ [] = []
  | pretty_attribs ctxt srcs =
      [Pretty.enclose "[" "]"
        (Pretty.commas (map (Args.pretty_src ctxt o Args.map_name (extern ctxt)) srcs))];


(* get attributes *)

exception ATTRIB_FAIL of (string * Position.T) * exn;

fun attribute_i thy =
  let
    val attrs = #2 (AttributesData.get thy);
    fun attr src =
      let val ((name, _), pos) = Args.dest_src src in
        (case Symtab.lookup attrs name of
          NONE => error ("Unknown attribute: " ^ quote name ^ Position.str_of pos)
        | SOME ((att, _), _) => transform_failure (curry ATTRIB_FAIL (name, pos)) (att src))
      end;
  in attr end;

fun attribute thy = attribute_i thy o intern_src thy;


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
    fun add attrs = NameSpace.extend_table (Sign.naming_of thy) (attrs, new_attrs)
      handle Symtab.DUPS dups =>
        error ("Duplicate declaration of attributes(s) " ^ commas_quote dups);
  in AttributesData.map add thy end;



(** attribute parsers **)

(* tags *)

fun tag x = Scan.lift (Args.name -- Scan.repeat Args.name) x;


(* theorems *)

local

val get_thms = Context.cases PureThy.get_thms ProofContext.get_thms;

val fact_name = Args.internal_fact >> K "<fact>" || Args.name;

fun gen_thm pick = Scan.depend (fn st =>
 (Scan.ahead Args.alt_name -- Args.named_fact (get_thms st o Fact)
    >> (fn (s, fact) => ("", Fact s, fact)) ||
  Scan.ahead fact_name -- Args.named_fact (get_thms st o Name) -- Args.thm_sel
    >> (fn ((name, fact), sel) => (name, NameSelection (name, sel), fact)) ||
  Scan.ahead fact_name -- Args.named_fact (get_thms st o Name)
    >> (fn (name, fact) => (name, Name name, fact))) --
  Args.opt_attribs (intern (Context.theory_of st))
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

fun eta_long x = no_args (Thm.rule_attribute (K (Drule.fconv_rule Drule.eta_long_conversion))) x;


(* internal attribute *)

fun internal att = Args.src (("Pure.attribute", [Args.mk_attribute att]), Position.none);

fun internal_att x =
  syntax (Scan.lift Args.internal_attribute >> (fn att => att Morphism.identity)) x;


(* theory setup *)

val _ = Context.add_setup
 (add_attributes
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
    ("defn", add_del_args LocalDefs.defn_add LocalDefs.defn_del,
      "declaration of definitional transformations"),
    ("attribute", internal_att, "internal attribute")]);

end;

structure BasicAttrib: BASIC_ATTRIB = Attrib;
open BasicAttrib;
