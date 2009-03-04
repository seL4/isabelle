(*  Title:      Pure/Isar/locale.ML
    Author:     Clemens Ballarin, TU Muenchen

Locales -- Isar proof contexts as meta-level predicates, with local
syntax and implicit structures.

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
  val register_locale: bstring ->
    (string * sort) list * (binding * typ option * mixfix) list ->
    term option * term list ->
    thm option * thm option -> thm list ->
    (declaration * stamp) list * (declaration * stamp) list ->
    ((string * (Attrib.binding * (thm list * Attrib.src list) list) list) * stamp) list ->
    ((string * morphism) * stamp) list -> theory -> theory
  val intern: theory -> xstring -> string
  val extern: theory -> string -> xstring
  val defined: theory -> string -> bool
  val params_of: theory -> string -> (binding * typ option * mixfix) list
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
  val activate_declarations: theory -> string * morphism ->
    Proof.context -> Proof.context
  val activate_global_facts: string * morphism -> theory -> theory
  val activate_local_facts: string * morphism -> Proof.context -> Proof.context
  val init: string -> theory -> Proof.context

  (* Reasoning about locales *)
  val witness_attrib: attribute
  val intro_attrib: attribute
  val unfold_attrib: attribute
  val intro_locales_tac: bool -> Proof.context -> thm list -> tactic

  (* Registrations *)
  val add_registration: string * (morphism * morphism) ->
    theory -> theory
  val amend_registration: morphism -> string * morphism ->
    theory -> theory
  val get_registrations: theory -> (string * morphism) list

  (* Diagnostic *)
  val print_locales: theory -> unit
  val print_locale: theory -> bool -> bstring -> unit
end;


(*** Theorem list extensible via attribute --- to control intro_locales_tac ***)

(* FIXME: consider moving named_thms.ML up in the build hierarchy and using that *)
functor ThmsFun() =
struct

structure Data = GenericDataFun
(
  type T = thm list;
  val empty = [];
  val extend = I;
  fun merge _ = Thm.merge_thms;
);

val get = Data.get o Context.Proof;
val add = Thm.declaration_attribute (Data.map o Thm.add_thm);

end;


structure Locale: LOCALE =
struct

datatype ctxt = datatype Element.ctxt;

fun global_note_qualified kind facts thy = (*FIXME*)
  thy
  |> Sign.qualified_names
  |> PureThy.note_thmss kind facts
  ||> Sign.restore_naming thy;

fun local_note_qualified kind facts ctxt = (*FIXME*)
  ctxt
  |> ProofContext.qualified_names
  |> ProofContext.note_thmss_i kind facts
  ||> ProofContext.restore_naming ctxt;



(*** Theory data ***)

datatype locale = Loc of {
  (** static part **)
  parameters: (string * sort) list * (binding * typ option * mixfix) list,
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

structure LocalesData = TheoryDataFun
(
  type T = locale NameSpace.table;
  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;
  fun merge _ = NameSpace.join_tables (K merge_locale);
);

val intern = NameSpace.intern o #1 o LocalesData.get;
val extern = NameSpace.extern o #1 o LocalesData.get;

fun get_locale thy = Symtab.lookup (#2 (LocalesData.get thy));

fun defined thy = is_some o get_locale thy;

fun the_locale thy name = case get_locale thy name
 of SOME (Loc loc) => loc
  | NONE => error ("Unknown locale " ^ quote name);

fun register_locale bname parameters spec intros axioms decls notes dependencies thy =
  thy |> LocalesData.map (NameSpace.bind (Sign.naming_of thy) (Binding.name bname,
    mk_locale ((parameters, spec, intros, axioms), ((decls, notes), dependencies))) #> snd);

fun change_locale name =
  LocalesData.map o apsnd o Symtab.map_entry name o map_locale o apsnd;

fun print_locales thy =
  Pretty.strs ("locales:" :: map #1 (NameSpace.extern_table (LocalesData.get thy)))
  |> Pretty.writeln;


(*** Primitive operations ***)

fun params_of thy = snd o #parameters o the_locale thy;

fun intros_of thy = #intros o the_locale thy;

fun axioms_of thy = #axioms o the_locale thy;

fun instance_of thy name morph = params_of thy name |>
  map ((fn (b, T, _) => Free (Binding.name_of b, the T)) #> Morphism.term morph);

fun specification_of thy = #spec o the_locale thy;

fun declarations_of thy name = the_locale thy name |>
  #decls |> apfst (map fst) |> apsnd (map fst);

fun dependencies_of thy name = the_locale thy name |>
  #dependencies |> map fst;


(*** Activate context elements of locale ***)

(** Identifiers: activated locales in theory or proof context **)

type identifiers = (string * term list) list;

val empty = ([] : identifiers);

fun ident_eq thy ((n: string, ts), (m, ss)) = (m = n) andalso Pattern.matchess thy (ss, ts);

local

datatype 'a delayed = Ready of 'a | ToDo of ('a delayed * 'a delayed);

structure IdentifiersData = GenericDataFun
(
  type T = identifiers delayed;
  val empty = Ready empty;
  val extend = I;
  fun merge _ = ToDo;
);

in

fun finish thy (ToDo (i1, i2)) = merge (ident_eq thy) (finish thy i1, finish thy i2)
  | finish _ (Ready ids) = ids;

val _ = Context.>> (Context.map_theory (Theory.at_begin (fn thy =>
  (case IdentifiersData.get (Context.Theory thy) of
    Ready _ => NONE |
    ids => SOME (Context.theory_map (IdentifiersData.put (Ready (finish thy ids))) thy))
  )));

fun get_global_idents thy =
  let val (Ready ids) = (IdentifiersData.get o Context.Theory) thy in ids end;
val put_global_idents = Context.theory_map o IdentifiersData.put o Ready;

fun get_local_idents ctxt =
  let val (Ready ids) = (IdentifiersData.get o Context.Proof) ctxt in ids end;
val put_local_idents = Context.proof_map o IdentifiersData.put o Ready;

end;


(** Resolve locale dependencies in a depth-first fashion **)

local

val roundup_bound = 120;

fun add thy depth (name, morph) (deps, marked) =
  if depth > roundup_bound
  then error "Roundup bound exceeded (sublocale relation probably not terminating)."
  else
    let
      val {parameters = (_, params), dependencies, ...} = the_locale thy name;
      val instance = instance_of thy name morph;
    in
      if member (ident_eq thy) marked (name, instance)
      then (deps, marked)
      else
        let
          val dependencies' =
            map (fn ((name, morph'), _) => (name, morph' $>  morph)) dependencies;
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
    val (dependencies, marked') = add thy 0 (name, morph) ([], empty);
    (* Filter out exisiting fragments. *)
    val dependencies' = filter_out (fn (name, morph) =>
      member (ident_eq thy) marked (name, instance_of thy name morph)) dependencies;
  in
    (merge (ident_eq thy) (marked, marked'), input |> fold_rev (activate_dep thy) dependencies')
  end;

end;


(* Declarations, facts and entire locale content *)

fun activate_decls thy (name, morph) ctxt =
  let
    val {decls = (typ_decls, term_decls), ...} = the_locale thy name;
  in
    ctxt |> fold_rev (fn (decl, _) => Context.proof_map (decl morph)) typ_decls |>
      fold_rev (fn (decl, _) => Context.proof_map (decl morph)) term_decls
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
    val {parameters = (_, params), spec = (asm, defs), ...} =
      the_locale thy name;
  in
    input |>
      (if not (null params) then activ_elem (Fixes params) else I) |>
      (* FIXME type parameters *)
      (if is_some asm then activ_elem (Assumes [(Attrib.empty_binding, [(the asm, [])])]) else I) |>
      (if not (null defs)
        then activ_elem (Defines (map (fn def => (Attrib.empty_binding, (def, []))) defs))
        else I) |>
      pair marked |> roundup thy (activate_notes activ_elem transfer) (name, Morphism.identity)
  end;


(** Public activation functions **)

local

fun init_global_elem (Notes (kind, facts)) thy =
  let
    val facts' = Attrib.map_facts (Attrib.attribute_i thy) facts
  in global_note_qualified kind facts' thy |> snd end

fun init_local_elem (Fixes fixes) ctxt = ctxt |>
      ProofContext.add_fixes_i fixes |> snd
  | init_local_elem (Assumes assms) ctxt =
      let
        val assms' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) assms
      in
        ctxt |> fold Variable.auto_fixes (maps (map fst o snd) assms') |>
          ProofContext.add_assms_i Assumption.assume_export assms' |> snd
     end
  | init_local_elem (Defines defs) ctxt =
      let
        val defs' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) defs
      in
        ctxt |> fold Variable.auto_fixes (map (fst o snd) defs') |>
          ProofContext.add_assms_i LocalDefs.def_export (map (fn (attn, t) => (attn, [t])) defs') |>
          snd
      end
  | init_local_elem (Notes (kind, facts)) ctxt =
      let
        val facts' = Attrib.map_facts (Attrib.attribute_i (ProofContext.theory_of ctxt)) facts
      in local_note_qualified kind facts' ctxt |> snd end

fun cons_elem false (Notes notes) elems = elems
  | cons_elem _ elem elems = elem :: elems

in

fun activate_declarations thy dep ctxt =
  roundup thy activate_decls dep (get_local_idents ctxt, ctxt) |-> put_local_idents;

fun activate_global_facts dep thy =
  roundup thy (activate_notes init_global_elem Element.transfer_morphism)
    dep (get_global_idents thy, thy) |-> put_global_idents;

fun activate_local_facts dep ctxt =
  roundup (ProofContext.theory_of ctxt)
  (activate_notes init_local_elem (Element.transfer_morphism o ProofContext.theory_of)) dep
    (get_local_idents ctxt, ctxt) |-> put_local_idents;

fun init name thy =
  activate_all name thy init_local_elem (Element.transfer_morphism o ProofContext.theory_of)
    (empty, ProofContext.init thy) |-> put_local_idents;

fun print_locale thy show_facts name =
  let
    val name' = intern thy name;
    val ctxt = init name' thy
  in
    Pretty.big_list "locale elements:"
      (activate_all name' thy (cons_elem show_facts) (K (Element.transfer_morphism thy))
        (empty, []) |> snd |> rev |>
        map (Element.pretty_ctxt ctxt) |> map Pretty.chunks) |> Pretty.writeln
  end

end;


(*** Registrations: interpretations in theories ***)

structure RegistrationsData = TheoryDataFun
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
  RegistrationsData.get #> map fst #> map (apsnd op $>);

fun add_registration (name, (base_morph, export)) thy =
  roundup thy (fn _ => fn (name', morph') =>
    (RegistrationsData.map o cons) ((name', (morph', export)), stamp ()))
    (name, base_morph) (get_global_idents thy, thy) |> snd
    (* FIXME |-> put_global_idents ?*);

fun amend_registration morph (name, base_morph) thy =
  let
    val regs = (RegistrationsData.get #> map fst) thy;
    val base = instance_of thy name base_morph;
    fun match (name', (morph', _)) =
      name = name' andalso eq_list (op aconv) (base, instance_of thy name' morph');
    val i = find_index match (rev regs);
    val _ = if i = ~1 then error ("No registration of locale " ^
        quote (extern thy name) ^ " and parameter instantiation " ^
        space_implode " " (map (quote o Syntax.string_of_term_global thy) base) ^ " available.")
      else ();
  in
    RegistrationsData.map (nth_map (length regs - 1 - i)
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
            in global_note_qualified kind args'' #> snd end)
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

(** Storage for witnesses, intro and unfold rules **)

structure Witnesses = ThmsFun();
structure Intros = ThmsFun();
structure Unfolds = ThmsFun();

val witness_attrib = Witnesses.add;
val intro_attrib = Intros.add;
val unfold_attrib = Unfolds.add;

(** Tactic **)

fun intro_locales_tac eager ctxt facts st =
  Method.intros_tac
    (Witnesses.get ctxt @ Intros.get ctxt @ (if eager then Unfolds.get ctxt else [])) facts st;

val _ = Context.>> (Context.map_theory
  (Method.add_methods
    [("intro_locales",
      Method.ctxt_args (fn ctxt => Method.METHOD (intro_locales_tac false ctxt)),
      "back-chain introduction rules of locales without unfolding predicates"),
     ("unfold_locales",
      Method.ctxt_args (fn ctxt => Method.METHOD (intro_locales_tac true ctxt)),
      "back-chain all introduction rules of locales")]));

end;

