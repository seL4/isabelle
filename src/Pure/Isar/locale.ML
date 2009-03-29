(*  Title:      Pure/Isar/locale.ML
    Author:     Clemens Ballarin, TU Muenchen

Locales -- managed Isar proof contexts, based on Pure predicates.

Draws basic ideas from Florian Kammueller's original version of
locales, but uses the richer infrastructure of Isar instead of the raw
meta-logic.  Furthermore, structured import of contexts (with merge
and rename operations) are provided, as well as type-inference of the
signature parts, and predicate definitions of the specification text.

Interpretation enables the reuse of theorems of locales in other
contexts, namely those defined by theories, structured proofs and
locales themselves.

See also:

[1] Clemens Ballarin. Locales and Locale Expressions in Isabelle/Isar.
    In Stefano Berardi et al., Types for Proofs and Programs: International
    Workshop, TYPES 2003, Torino, Italy, LNCS 3085, pages 34-50, 2004.
[2] Clemens Ballarin. Interpretation of Locales in Isabelle: Managing
    Dependencies between Locales. Technical Report TUM-I0607, Technische
    Universitaet Muenchen, 2006.
[3] Clemens Ballarin. Interpretation of Locales in Isabelle: Theories and
    Proof Contexts. In J.M. Borwein and W.M. Farmer, MKM 2006, LNAI 4108,
    pages 31-43, 2006.
*)

signature LOCALE =
sig
  (* Locale specification *)
  val register_locale: binding ->
    (string * sort) list * ((string * typ) * mixfix) list ->
    term option * term list ->
    thm option * thm option -> thm list ->
    declaration list * declaration list ->
    (string * (Attrib.binding * (thm list * Attrib.src list) list) list) list ->
    (string * morphism) list -> theory -> theory
  val intern: theory -> xstring -> string
  val extern: theory -> string -> xstring
  val defined: theory -> string -> bool
  val params_of: theory -> string -> ((string * typ) * mixfix) list
  val intros_of: theory -> string -> thm option * thm option
  val axioms_of: theory -> string -> thm list
  val instance_of: theory -> string -> morphism -> term list
  val specification_of: theory -> string -> term option * term list
  val declarations_of: theory -> string -> declaration list * declaration list
  val dependencies_of: theory -> string -> (string * morphism) list

  (* Storing results *)
  val add_thmss: string -> string -> (Attrib.binding * (thm list * Attrib.src list) list) list ->
    Proof.context -> Proof.context
  val add_type_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_term_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_declaration: string -> declaration -> Proof.context -> Proof.context
  val add_dependency: string -> string * morphism -> theory -> theory

  (* Activation *)
  val activate_declarations: string * morphism -> Proof.context -> Proof.context
  val activate_facts: string * morphism -> Context.generic -> Context.generic
  val init: string -> theory -> Proof.context

  (* Reasoning about locales *)
  val get_witnesses: Proof.context -> thm list
  val get_intros: Proof.context -> thm list
  val get_unfolds: Proof.context -> thm list
  val witness_add: attribute
  val intro_add: attribute
  val unfold_add: attribute
  val intro_locales_tac: bool -> Proof.context -> thm list -> tactic

  (* Registrations *)
  val add_registration: string * (morphism * morphism) -> theory -> theory
  val amend_registration: morphism -> string * morphism -> theory -> theory
  val get_registrations: theory -> (string * morphism) list

  (* Diagnostic *)
  val print_locales: theory -> unit
  val print_locale: theory -> bool -> xstring -> unit
end;

structure Locale: LOCALE =
struct

datatype ctxt = datatype Element.ctxt;


(*** Theory data ***)

datatype locale = Loc of {
  (** static part **)
  parameters: (string * sort) list * ((string * typ) * mixfix) list,
    (* type and term parameters *)
  spec: term option * term list,
    (* assumptions (as a single predicate expression) and defines *)
  intros: thm option * thm option,
  axioms: thm list,
  (** dynamic part **)
  decls: (declaration * stamp) list * (declaration * stamp) list,
    (* type and term syntax declarations *)
  notes: ((string * (Attrib.binding * (thm list * Attrib.src list) list) list) * stamp) list,
    (* theorem declarations *)
  dependencies: ((string * morphism) * stamp) list
    (* locale dependencies (sublocale relation) *)
};

fun mk_locale ((parameters, spec, intros, axioms), ((decls, notes), dependencies)) =
  Loc {parameters = parameters, intros = intros, axioms = axioms, spec = spec,
    decls = decls, notes = notes, dependencies = dependencies};

fun map_locale f (Loc {parameters, spec, intros, axioms, decls, notes, dependencies}) =
  mk_locale (f ((parameters, spec, intros, axioms), ((decls, notes), dependencies)));

fun merge_locale (Loc {parameters, spec, intros, axioms, decls = (decls1, decls2),
  notes, dependencies}, Loc {decls = (decls1', decls2'), notes = notes',
    dependencies = dependencies', ...}) = mk_locale
      ((parameters, spec, intros, axioms),
        (((merge (eq_snd op =) (decls1, decls1'), merge (eq_snd op =) (decls2, decls2')),
          merge (eq_snd op =) (notes, notes')),
            merge (eq_snd op =) (dependencies, dependencies')));

structure Locales = TheoryDataFun
(
  type T = locale NameSpace.table;
  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;
  fun merge _ = NameSpace.join_tables (K merge_locale);
);

val intern = NameSpace.intern o #1 o Locales.get;
val extern = NameSpace.extern o #1 o Locales.get;

val get_locale = Symtab.lookup o #2 o Locales.get;
val defined = Symtab.defined o #2 o Locales.get;

fun the_locale thy name =
  (case get_locale thy name of
    SOME (Loc loc) => loc
  | NONE => error ("Unknown locale " ^ quote name));

fun register_locale binding parameters spec intros axioms decls notes dependencies thy =
  thy |> Locales.map (NameSpace.define (Sign.naming_of thy)
    (binding,
      mk_locale ((parameters, spec, intros, axioms),
        ((pairself (map (fn decl => (decl, stamp ()))) decls, map (fn n => (n, stamp ())) notes),
          map (fn d => (d, stamp ())) dependencies))) #> snd);

fun change_locale name =
  Locales.map o apsnd o Symtab.map_entry name o map_locale o apsnd;

fun print_locales thy =
  Pretty.strs ("locales:" :: map #1 (NameSpace.extern_table (Locales.get thy)))
  |> Pretty.writeln;


(*** Primitive operations ***)

fun params_of thy = snd o #parameters o the_locale thy;

fun intros_of thy = #intros o the_locale thy;

fun axioms_of thy = #axioms o the_locale thy;

fun instance_of thy name morph = params_of thy name |>
  map (Morphism.term morph o Free o #1);

fun specification_of thy = #spec o the_locale thy;

fun declarations_of thy name = the_locale thy name |>
  #decls |> pairself (map fst);

fun dependencies_of thy name = the_locale thy name |>
  #dependencies |> map fst;


(*** Activate context elements of locale ***)

(** Identifiers: activated locales in theory or proof context **)

fun ident_eq thy ((n: string, ts), (m, ss)) = (m = n) andalso Pattern.matchess thy (ss, ts);

local

datatype 'a delayed = Ready of 'a | ToDo of 'a delayed * 'a delayed;

structure Identifiers = GenericDataFun
(
  type T = (string * term list) list delayed;
  val empty = Ready [];
  val extend = I;
  fun merge _ = ToDo;
);

fun finish thy (ToDo (i1, i2)) = merge (ident_eq thy) (finish thy i1, finish thy i2)
  | finish _ (Ready ids) = ids;

val _ = Context.>> (Context.map_theory (Theory.at_begin (fn thy =>
  (case Identifiers.get (Context.Theory thy) of
    Ready _ => NONE
  | ids => SOME (Context.theory_map (Identifiers.put (Ready (finish thy ids))) thy)))));

in

val get_idents = (fn Ready ids => ids) o Identifiers.get;
val put_idents = Identifiers.put o Ready;

end;


(** Resolve locale dependencies in a depth-first fashion **)

local

val roundup_bound = 120;

fun add thy depth (name, morph) (deps, marked) =
  if depth > roundup_bound
  then error "Roundup bound exceeded (sublocale relation probably not terminating)."
  else
    let
      val dependencies = dependencies_of thy name;
      val instance = instance_of thy name morph;
    in
      if member (ident_eq thy) marked (name, instance)
      then (deps, marked)
      else
        let
          val dependencies' = map (fn (name, morph') => (name, morph' $> morph)) dependencies;
          val marked' = (name, instance) :: marked;
          val (deps', marked'') = fold_rev (add thy (depth + 1)) dependencies' ([], marked');
        in
          ((name, morph) :: deps' @ deps, marked'')
        end
    end;

in

fun roundup thy activate_dep (name, morph) (marked, input) =
  let
    (* Find all dependencies incuding new ones (which are dependencies enriching
      existing registrations). *)
    val (dependencies, marked') = add thy 0 (name, morph) ([], []);
    (* Filter out exisiting fragments. *)
    val dependencies' = filter_out (fn (name, morph) =>
      member (ident_eq thy) marked (name, instance_of thy name morph)) dependencies;
  in
    (merge (ident_eq thy) (marked, marked'), input |> fold_rev activate_dep dependencies')
  end;

end;


(* Declarations, facts and entire locale content *)

fun activate_decls (name, morph) context =
  let
    val thy = Context.theory_of context;
    val {decls = (typ_decls, term_decls), ...} = the_locale thy name;
  in
    context
    |> fold_rev (fn (decl, _) => decl morph) typ_decls
    |> fold_rev (fn (decl, _) => decl morph) term_decls
  end;

fun activate_notes activ_elem transfer thy (name, morph) input =
  let
    val {notes, ...} = the_locale thy name;
    fun activate ((kind, facts), _) input =
      let
        val facts' = facts |> Element.facts_map (Element.morph_ctxt (transfer input $> morph))
      in activ_elem (Notes (kind, facts')) input end;
  in
    fold_rev activate notes input
  end;

fun activate_all name thy activ_elem transfer (marked, input) =
  let
    val {parameters = (_, params), spec = (asm, defs), ...} = the_locale thy name;
    val input' = input |>
      (not (null params) ?
        activ_elem (Fixes (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) params))) |>
      (* FIXME type parameters *)
      (case asm of SOME A => activ_elem (Assumes [(Attrib.empty_binding, [(A, [])])]) | _ => I) |>
      (if not (null defs)
        then activ_elem (Defines (map (fn def => (Attrib.empty_binding, (def, []))) defs))
        else I);
    val activate = activate_notes activ_elem transfer thy;
  in
    roundup thy activate (name, Morphism.identity) (marked, input')
  end;


(** Public activation functions **)

local

fun init_elem (Fixes fixes) (Context.Proof ctxt) =
      Context.Proof (ProofContext.add_fixes fixes ctxt |> snd)
  | init_elem (Assumes assms) (Context.Proof ctxt) =
      let
        val assms' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) assms;
        val ctxt' = ctxt
          |> fold Variable.auto_fixes (maps (map fst o snd) assms')
          |> ProofContext.add_assms_i Assumption.assume_export assms' |> snd;
      in Context.Proof ctxt' end
  | init_elem (Defines defs) (Context.Proof ctxt) =
      let
        val defs' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) defs;
        val ctxt' = ctxt
          |> fold Variable.auto_fixes (map (fst o snd) defs')
          |> ProofContext.add_assms_i LocalDefs.def_export (map (fn (attn, t) => (attn, [t])) defs')
          |> snd;
      in Context.Proof ctxt' end
  | init_elem (Notes (kind, facts)) (Context.Proof ctxt) =
      let
        val facts' = Attrib.map_facts (Attrib.attribute_i (ProofContext.theory_of ctxt)) facts
      in Context.Proof (ProofContext.note_thmss kind facts' ctxt |> snd) end
  | init_elem (Notes (kind, facts)) (Context.Theory thy) =
      let
        val facts' = Attrib.map_facts (Attrib.attribute_i thy) facts
      in Context.Theory (PureThy.note_thmss kind facts' thy |> snd) end
  | init_elem _ (Context.Theory _) = raise Fail "Bad context element in global theory";

in

fun activate_declarations dep ctxt =
  let
    val context = Context.Proof ctxt;
    val thy = Context.theory_of context;
    val context' = roundup thy activate_decls dep (get_idents context, context) |-> put_idents;
  in Context.the_proof context' end;

fun activate_facts dep context =
  let
    val thy = Context.theory_of context;
    val activate = activate_notes init_elem (Element.transfer_morphism o Context.theory_of) thy;
  in roundup thy activate dep (get_idents context, context) |-> put_idents end;

fun init name thy =
  activate_all name thy init_elem (Element.transfer_morphism o Context.theory_of)
    ([], Context.Proof (ProofContext.init thy)) |-> put_idents |> Context.proof_of;

fun print_locale thy show_facts raw_name =
  let
    val name = intern thy raw_name;
    val ctxt = init name thy;
    fun cons_elem (elem as Notes _) = show_facts ? cons elem
      | cons_elem elem = cons elem;
    val elems =
      activate_all name thy cons_elem (K (Element.transfer_morphism thy)) ([], [])
      |> snd |> rev;
  in
    Pretty.big_list "locale elements:" (map (Pretty.chunks o Element.pretty_ctxt ctxt) elems)
    |> Pretty.writeln
  end;

end;


(*** Registrations: interpretations in theories ***)

structure Registrations = TheoryDataFun
(
  type T = ((string * (morphism * morphism)) * stamp) list;
    (* FIXME mixins need to be stamped *)
    (* registrations, in reverse order of declaration *)
  val empty = [];
  val extend = I;
  val copy = I;
  fun merge _ data : T = Library.merge (eq_snd op =) data;
    (* FIXME consolidate with dependencies, consider one data slot only *)
);

val get_registrations =
  Registrations.get #> map (#1 #> apsnd op $>);

fun add_registration (name, (base_morph, export)) thy =
  roundup thy (fn (name', morph') => Registrations.map (cons ((name', (morph', export)), stamp ())))
    (name, base_morph) (get_idents (Context.Theory thy), thy) |> snd;
    (* FIXME |-> put_global_idents ?*)

fun amend_registration morph (name, base_morph) thy =
  let
    val regs = map #1 (Registrations.get thy);
    val base = instance_of thy name base_morph;
    fun match (name', (morph', _)) =
      name = name' andalso eq_list (op aconv) (base, instance_of thy name' morph');
    val i = find_index match (rev regs);
    val _ =
      if i = ~1 then error ("No registration of locale " ^
        quote (extern thy name) ^ " and parameter instantiation " ^
        space_implode " " (map (quote o Syntax.string_of_term_global thy) base) ^ " available")
      else ();
  in
    Registrations.map (nth_map (length regs - 1 - i)
      (fn ((name, (base, export)), stamp) => ((name, (base $> morph, export)), stamp))) thy
  end;



(*** Storing results ***)

(* Theorems *)

fun add_thmss loc kind args ctxt =
  let
    val ([Notes args'], ctxt') = Element.activate_i [Notes (kind, args)] ctxt;
    val ctxt'' = ctxt' |> ProofContext.theory (
      (change_locale loc o apfst o apsnd) (cons (args', stamp ()))
        #>
      (* Registrations *)
      (fn thy => fold_rev (fn (name, morph) =>
            let
              val args'' = snd args' |> Element.facts_map (Element.morph_ctxt morph) |>
                Attrib.map_facts (Attrib.attribute_i thy)
            in PureThy.note_thmss kind args'' #> snd end)
        (get_registrations thy |> filter (fn (name, _) => name = loc)) thy))
  in ctxt'' end;


(* Declarations *)

local

fun decl_attrib decl phi = Thm.declaration_attribute (K (decl phi));

fun add_decls add loc decl =
  ProofContext.theory ((change_locale loc o apfst o apfst) (add (decl, stamp ()))) #>
  add_thmss loc Thm.internalK
    [((Binding.empty, [Attrib.internal (decl_attrib decl)]), [([Drule.dummy_thm], [])])];

in

val add_type_syntax = add_decls (apfst o cons);
val add_term_syntax = add_decls (apsnd o cons);
val add_declaration = add_decls (K I);

end;


(* Dependencies *)

fun add_dependency loc dep = (change_locale loc o apsnd) (cons (dep, stamp ()));


(*** Reasoning about locales ***)

(* Storage for witnesses, intro and unfold rules *)

structure Thms = GenericDataFun
(
  type T = thm list * thm list * thm list;
  val empty = ([], [], []);
  val extend = I;
  fun merge _ ((witnesses1, intros1, unfolds1), (witnesses2, intros2, unfolds2)) =
   (Thm.merge_thms (witnesses1, witnesses2),
    Thm.merge_thms (intros1, intros2),
    Thm.merge_thms (unfolds1, unfolds2));
);

val get_witnesses = #1 o Thms.get o Context.Proof;
val get_intros = #2 o Thms.get o Context.Proof;
val get_unfolds = #3 o Thms.get o Context.Proof;

val witness_add =
  Thm.declaration_attribute (fn th => Thms.map (fn (x, y, z) => (Thm.add_thm th x, y, z)));
val intro_add =
  Thm.declaration_attribute (fn th => Thms.map (fn (x, y, z) => (x, Thm.add_thm th y, z)));
val unfold_add =
  Thm.declaration_attribute (fn th => Thms.map (fn (x, y, z) => (x, y, Thm.add_thm th z)));


(* Tactic *)

fun intro_locales_tac eager ctxt =
  Method.intros_tac
    (get_witnesses ctxt @ get_intros ctxt @ (if eager then get_unfolds ctxt else []));

val _ = Context.>> (Context.map_theory
 (Method.setup (Binding.name "intro_locales") (Scan.succeed (METHOD o intro_locales_tac false))
    "back-chain introduction rules of locales without unfolding predicates" #>
  Method.setup (Binding.name "unfold_locales") (Scan.succeed (METHOD o intro_locales_tac true))
    "back-chain all introduction rules of locales"));

end;

