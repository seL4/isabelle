(*  Title:      Pure/Isar/attrib.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Symbolic theorem attributes.
*)

signature BASIC_ATTRIB =
sig
  val print_attributes: theory -> unit
  val Attribute: bstring ->
    (Args.src -> theory attribute) * (Args.src -> ProofContext.context attribute) ->
    string -> unit
end;

signature ATTRIB =
sig
  include BASIC_ATTRIB
  val rule: ('a -> thm -> thm) -> 'a attribute
  val declaration: (thm -> 'a -> 'a) -> 'a attribute
  type src
  val theory: Context.generic attribute -> theory attribute
  val context: Context.generic attribute -> ProofContext.context attribute
  val generic: theory attribute * ProofContext.context attribute -> Context.generic attribute
  val common: (src -> Context.generic attribute) ->
    (src -> theory attribute) * (src -> ProofContext.context attribute)
  exception ATTRIB_FAIL of (string * Position.T) * exn
  val intern: theory -> xstring -> string
  val intern_src: theory -> src -> src
  val global_attribute_i: theory -> src -> theory attribute
  val global_attribute: theory -> src -> theory attribute
  val local_attribute_i: theory -> src -> ProofContext.context attribute
  val local_attribute: theory -> src -> ProofContext.context attribute
  val context_attribute_i: ProofContext.context -> Args.src -> ProofContext.context attribute
  val context_attribute: ProofContext.context -> Args.src -> ProofContext.context attribute
  val undef_global_attribute: theory attribute
  val undef_local_attribute: ProofContext.context attribute
  val generic_attribute_i: theory -> src -> Context.generic attribute
  val generic_attribute: theory -> src -> Context.generic attribute
  val map_specs: ('a -> 'b attribute) ->
    (('c * 'a list) * 'd) list -> (('c * 'b attribute list) * 'd) list
  val map_facts: ('a -> 'b attribute) ->
    (('c * 'a list) * ('d * 'a list) list) list ->
    (('c * 'b attribute list) * ('d * 'b attribute list) list) list
  val crude_closure: ProofContext.context -> src -> src
  val add_attributes: (bstring * ((src -> theory attribute) *
      (src -> ProofContext.context attribute)) * string) list -> theory -> theory
  val global_thm: theory * Args.T list -> thm * (theory * Args.T list)
  val global_thms: theory * Args.T list -> thm list * (theory * Args.T list)
  val global_thmss: theory * Args.T list -> thm list * (theory * Args.T list)
  val local_thm: ProofContext.context * Args.T list ->
    thm * (ProofContext.context * Args.T list)
  val local_thms: ProofContext.context * Args.T list ->
    thm list * (ProofContext.context * Args.T list)
  val local_thmss: ProofContext.context * Args.T list ->
    thm list * (ProofContext.context * Args.T list)
  val thm: Context.generic * Args.T list -> thm * (Context.generic * Args.T list)
  val thms: Context.generic * Args.T list -> thm list * (Context.generic * Args.T list)
  val thmss: Context.generic * Args.T list -> thm list * (Context.generic * Args.T list)
  val syntax: ('a * Args.T list -> 'a attribute * ('a * Args.T list)) -> src -> 'a attribute
  val no_args: 'a attribute -> src -> 'a attribute
  val add_del_args: 'a attribute -> 'a attribute -> src -> 'a attribute
  val attribute: Context.generic attribute -> src
end;

structure Attrib: ATTRIB =
struct

val rule = Drule.rule_attribute;
val declaration = Drule.declaration_attribute;

type src = Args.src;



(** generic attributes **)

fun generic (global_att, local_att) =
   fn (Context.Theory thy, th) => apfst Context.Theory (global_att (thy, th))
    | (Context.Proof ctxt, th) => apfst Context.Proof (local_att (ctxt, th));

fun theory att (thy, th) = apfst Context.the_theory (att (Context.Theory thy, th));
fun context att (ctxt, th) = apfst Context.the_proof (att (Context.Proof ctxt, th));

fun common att = (theory o att, context o att);



(** attributes theory data **)

(* datatype attributes *)

structure AttributesData = TheoryDataFun
(struct
  val name = "Isar/attributes";
  type T =
    ((((src -> theory attribute) * (src -> ProofContext.context attribute))
        * string) * stamp) NameSpace.table;

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

val _ = Context.add_setup [AttributesData.init];
val print_attributes = AttributesData.print;


(* interning *)

val intern = NameSpace.intern o #1 o AttributesData.get;
val intern_src = Args.map_name o intern;


(* get global / local attributes *)

exception ATTRIB_FAIL of (string * Position.T) * exn;

fun gen_attribute which thy =
  let
    val attrs = #2 (AttributesData.get thy);
    fun attr src =
      let val ((name, _), pos) = Args.dest_src src in
        (case Symtab.lookup attrs name of
          NONE => error ("Unknown attribute: " ^ quote name ^ Position.str_of pos)
        | SOME ((p, _), _) => transform_failure (curry ATTRIB_FAIL (name, pos)) (which p src))
      end;
  in attr end;

val global_attribute_i = gen_attribute fst;
fun global_attribute thy = global_attribute_i thy o intern_src thy;

val local_attribute_i = gen_attribute snd;
fun local_attribute thy = local_attribute_i thy o intern_src thy;

val context_attribute_i = local_attribute_i o ProofContext.theory_of;
val context_attribute = local_attribute o ProofContext.theory_of;

val undef_global_attribute: theory attribute =
  fn _ => error "attribute undefined in theory context";

val undef_local_attribute: ProofContext.context attribute =
  fn _ => error "attribute undefined in proof context";

fun generic_attribute thy src = generic (global_attribute thy src, local_attribute thy src);
fun generic_attribute_i thy src = generic (global_attribute_i thy src, local_attribute_i thy src);


(* attributed declarations *)

fun map_specs f = map (apfst (apsnd (map f)));
fun map_facts f = map (apfst (apsnd (map f)) o apsnd (map (apsnd (map f))));


(* crude_closure *)

(*Produce closure without knowing facts in advance! The following
  should work reasonably well for attribute parsers that do not peek
  at the thm structure.*)

fun crude_closure ctxt src =
 (try (fn () => context_attribute_i ctxt src (ctxt, Drule.asm_rl)) ();
  Args.closure src);


(* add_attributes *)

fun add_attributes raw_attrs thy =
  let
    val new_attrs = raw_attrs |> map (fn (name, (f, g), comment) =>
      (name, (((f, g), comment), stamp ())));
    fun add attrs = NameSpace.extend_table (Sign.naming_of thy) (attrs, new_attrs)
      handle Symtab.DUPS dups =>
        error ("Duplicate declaration of attributes(s) " ^ commas_quote dups);
  in AttributesData.map add thy end;

(*implicit version*)
fun Attribute name att cmt = Context.>> (add_attributes [(name, att, cmt)]);



(** attribute parsers **)

(* tags *)

fun tag x = Scan.lift (Args.name -- Scan.repeat Args.name) x;


(* theorems *)

local

fun gen_thm theory_of attrib get pick = Scan.depend (fn st =>
 (Scan.ahead Args.alt_name -- Args.named_fact (get st o Fact)
    >> (fn (s, fact) => ("", Fact s, fact)) ||
  Scan.ahead Args.name -- Args.named_fact (get st o Name) -- Args.thm_sel
    >> (fn ((name, fact), sel) => (name, NameSelection (name, sel), fact)) ||
  Scan.ahead Args.name -- Args.named_fact (get st o Name)
    >> (fn (name, fact) => (name, Name name, fact))) --
  Args.opt_attribs (intern (theory_of st))
  >> (fn ((name, thmref, fact), srcs) =>
    let
      val ths = PureThy.select_thm thmref fact;
      val atts = map (attrib (theory_of st)) srcs;
      val (st', ths') = Thm.applys_attributes atts (st, ths);
    in (st', pick name ths') end));

val get_thms = Context.cases PureThy.get_thms ProofContext.get_thms;

in

val global_thm = gen_thm I global_attribute_i PureThy.get_thms PureThy.single_thm;
val global_thms = gen_thm I global_attribute_i PureThy.get_thms (K I);
val global_thmss = Scan.repeat global_thms >> List.concat;

val local_thm =
  gen_thm ProofContext.theory_of local_attribute_i ProofContext.get_thms PureThy.single_thm;
val local_thms =
  gen_thm ProofContext.theory_of local_attribute_i ProofContext.get_thms (K I);
val local_thmss = Scan.repeat local_thms >> List.concat;

val thm = gen_thm Context.theory_of generic_attribute_i get_thms PureThy.single_thm;
val thms = gen_thm Context.theory_of generic_attribute_i get_thms (K I);
val thmss = Scan.repeat thms >> List.concat;

end;



(** attribute syntax **)

fun syntax scan src (st, th) =
  let val (st', f) = Args.syntax "attribute" scan src st
  in f (st', th) end;

fun no_args x = syntax (Scan.succeed x);

fun add_del_args add del x = syntax
  (Scan.lift (Args.add >> K add || Args.del >> K del || Scan.succeed add)) x;



(** basic attributes **)

(* tags *)

fun tagged x = syntax (tag >> Drule.tag) x;
fun untagged x = syntax (Scan.lift Args.name >> Drule.untag) x;


(* rule composition *)

val COMP_att =
  syntax (Scan.lift (Scan.optional (Args.bracks Args.nat) 1) -- thm
    >> (fn (i, B) => Drule.rule_attribute (fn _ => fn A => Drule.compose_single (A, i, B))));

val THEN_att =
  syntax (Scan.lift (Scan.optional (Args.bracks Args.nat) 1) -- thm
    >> (fn (i, B) => Drule.rule_attribute (fn _ => fn A => A RSN (i, B))));

val OF_att =
  syntax (thmss >> (fn Bs => Drule.rule_attribute (fn _ => fn A => Bs MRS A)));


(* read_instantiate: named instantiation of type and term variables *)

local

fun is_tvar (x, _) = (case Symbol.explode x of "'" :: _ => true | _ => false);

fun error_var msg xi = error (msg ^ Syntax.string_of_vname xi);

fun the_sort sorts xi = the (sorts xi)
  handle Option.Option => error_var "No such type variable in theorem: " xi;

fun the_type types xi = the (types xi)
  handle Option.Option => error_var "No such variable in theorem: " xi;

fun unify_types thy types ((unifier, maxidx), (xi, u)) =
  let
    val T = the_type types xi;
    val U = Term.fastype_of u;
    val maxidx' = Int.max (maxidx, Int.max (#2 xi, Term.maxidx_of_term u));
  in
    Sign.typ_unify thy (T, U) (unifier, maxidx')
      handle Type.TUNIFY => error_var "Incompatible type for instantiation of " xi
  end;

fun typ_subst env = apsnd (Term.typ_subst_TVars env);
fun subst env = apsnd (Term.subst_TVars env);

fun instantiate thy envT env thm =
  let
    val (_, sorts) = Drule.types_sorts thm;
    fun prepT (a, T) = (Thm.ctyp_of thy (TVar (a, the_sort sorts a)), Thm.ctyp_of thy T);
    fun prep (xi, t) = pairself (Thm.cterm_of thy) (Var (xi, Term.fastype_of t), t);
  in
    Drule.instantiate (map prepT (distinct envT),
      map prep (gen_distinct (fn ((xi, t), (yj, u)) => xi = yj andalso t aconv u) env)) thm
  end;

in

fun read_instantiate mixed_insts (generic, thm) =
  let
    val thy = Context.theory_of generic;
    val ctxt = Context.proof_of generic;

    val (type_insts, term_insts) = List.partition (is_tvar o fst) (map snd mixed_insts);
    val internal_insts = term_insts |> List.mapPartial
      (fn (xi, Args.Term t) => SOME (xi, t)
      | (_, Args.Name _) => NONE
      | (xi, _) => error_var "Term argument expected for " xi);
    val external_insts = term_insts |> List.mapPartial
      (fn (xi, Args.Name s) => SOME (xi, s) | _ => NONE);


    (* type instantiations *)

    val sorts = #2 (Drule.types_sorts thm);

    fun readT (xi, arg) =
      let
        val S = the_sort sorts xi;
        val T =
          (case arg of
            Args.Name s => ProofContext.read_typ ctxt s
          | Args.Typ T => T
          | _ => error_var "Type argument expected for " xi);
      in
        if Sign.of_sort thy (T, S) then (xi, T)
        else error_var "Incompatible sort for typ instantiation of " xi
      end;

    val type_insts' = map readT type_insts;
    val thm' = instantiate thy type_insts' [] thm;


    (* internal term instantiations *)

    val types' = #1 (Drule.types_sorts thm');
    val unifier = map (apsnd snd) (Vartab.dest (#1
      (Library.foldl (unify_types thy types') ((Vartab.empty, 0), internal_insts))));

    val type_insts'' = map (typ_subst unifier) type_insts';
    val internal_insts'' = map (subst unifier) internal_insts;
    val thm'' = instantiate thy unifier internal_insts'' thm';


    (* external term instantiations *)

    val types'' = #1 (Drule.types_sorts thm'');

    val (xs, ss) = split_list external_insts;
    val Ts = map (the_type types'') xs;
    val (ts, inferred) = ProofContext.read_termTs ctxt (K false)
        (K NONE) (K NONE) (Drule.add_used thm'' []) (ss ~~ Ts);

    val type_insts''' = map (typ_subst inferred) type_insts'';
    val internal_insts''' = map (subst inferred) internal_insts'';

    val external_insts''' = xs ~~ ts;
    val term_insts''' = internal_insts''' @ external_insts''';
    val thm''' = instantiate thy inferred external_insts''' thm'';


    (* assign internalized values *)

    val _ =
      mixed_insts |> List.app (fn (arg, (xi, _)) =>
        if is_tvar xi then
          Args.assign (SOME (Args.Typ (the (AList.lookup (op =) type_insts''' xi)))) arg
        else
          Args.assign (SOME (Args.Term (the (AList.lookup (op =) term_insts''' xi)))) arg);

  in (generic, thm''' |> RuleCases.save thm) end;

end;


(* where: named instantiation *)

local

val value =
  Args.internal_typ >> Args.Typ ||
  Args.internal_term >> Args.Term ||
  Args.name >> Args.Name;

val inst = Args.var -- (Args.$$$ "=" |-- Args.ahead -- value)
  >> (fn (xi, (a, v)) => (a, (xi, v)));

in

val where_att = syntax (Args.and_list (Scan.lift inst) >> read_instantiate);

end;


(* of: positional instantiation (term arguments only) *)

local

fun read_instantiate' (args, concl_args) (generic, thm) =
  let
    fun zip_vars _ [] = []
      | zip_vars (_ :: xs) ((_, NONE) :: rest) = zip_vars xs rest
      | zip_vars ((x, _) :: xs) ((a, SOME t) :: rest) = (a, (x, t)) :: zip_vars xs rest
      | zip_vars [] _ = error "More instantiations than variables in theorem";
    val insts =
      zip_vars (Drule.vars_of_terms [Thm.prop_of thm]) args @
      zip_vars (Drule.vars_of_terms [Thm.concl_of thm]) concl_args;
  in read_instantiate insts (generic, thm) end;

val value =
  Args.internal_term >> Args.Term ||
  Args.name >> Args.Name;

val inst = Args.ahead -- Args.maybe value;
val concl = Args.$$$ "concl" -- Args.colon;

val insts =
  Scan.repeat (Scan.unless concl inst) --
  Scan.optional (concl |-- Scan.repeat inst) [];

in

val of_att = syntax (Scan.lift insts >> read_instantiate');

end;


(* rename_abs *)

fun rename_abs src = syntax
  (Scan.lift (Scan.repeat (Args.maybe Args.name) >> (apsnd o Drule.rename_bvars'))) src;


(* unfold / fold definitions *)

val unfolded = syntax (thmss >> (fn defs => Drule.rule_attribute (K (Tactic.rewrite_rule defs))));
val folded = syntax (thmss >> (fn defs => Drule.rule_attribute (K (Tactic.fold_rule defs))));


(* rule cases *)

fun consumes x = syntax (Scan.lift (Scan.optional Args.nat 1) >> RuleCases.consumes) x;
fun case_names x = syntax (Scan.lift (Scan.repeat1 Args.name) >> RuleCases.case_names) x;
fun case_conclusion x =
  syntax (Scan.lift (Args.name -- Scan.repeat Args.name) >> RuleCases.case_conclusion) x;
fun params x = syntax (Args.and_list1 (Scan.lift (Scan.repeat Args.name)) >> RuleCases.params) x;


(* rule_format *)

fun rule_format_att x = syntax (Args.mode "no_asm"
  >> (fn true => ObjectLogic.rule_format_no_asm | false => ObjectLogic.rule_format)) x;


(* misc rules *)

fun standard x = no_args (Drule.rule_attribute (K Drule.standard)) x;
fun elim_format x = no_args (Drule.rule_attribute (K Tactic.make_elim)) x;
fun no_vars x = no_args (Drule.rule_attribute (K (#1 o Drule.freeze_thaw))) x;
fun eta_long x = no_args (Drule.rule_attribute (K (Drule.fconv_rule Drule.eta_long_conversion))) x;


(* internal attribute *)

fun attribute att = Args.src (("Pure.attribute", [Args.mk_attribute att]), Position.none);

fun internal_att x = syntax (Scan.lift Args.internal_attribute) x;


(* theory setup *)

val _ = Context.add_setup
 [add_attributes
   [("tagged", common tagged, "tagged theorem"),
    ("untagged", common untagged, "untagged theorem"),
    ("COMP", common COMP_att, "direct composition with rules (no lifting)"),
    ("THEN", common THEN_att, "resolution with rule"),
    ("OF", common OF_att, "rule applied to facts"),
    ("where", common where_att, "named instantiation of theorem"),
    ("of", common of_att, "rule applied to terms"),
    ("rename_abs", common rename_abs, "rename bound variables in abstractions"),
    ("unfolded", common unfolded, "unfolded definitions"),
    ("folded", common folded, "folded definitions"),
    ("standard", common standard, "result put into standard form"),
    ("elim_format", common elim_format, "destruct rule turned into elimination rule format"),
    ("no_vars", common no_vars, "frozen schematic vars"),
    ("eta_long", common eta_long, "put theorem into eta long beta normal form"),
    ("consumes", common consumes, "number of consumed facts"),
    ("case_names", common case_names, "named rule cases"),
    ("case_conclusion", common case_conclusion, "named conclusion of rule cases"),
    ("params", common params, "named rule parameters"),
    ("atomize", (no_args ObjectLogic.declare_atomize, no_args undef_local_attribute),
      "declaration of atomize rule"),
    ("rulify", (no_args ObjectLogic.declare_rulify, no_args undef_local_attribute),
      "declaration of rulify rule"),
    ("rule_format", common rule_format_att, "result put into standard rule format"),
    ("attribute", common internal_att, "internal attribute")]];

end;

structure BasicAttrib: BASIC_ATTRIB = Attrib;
open BasicAttrib;
