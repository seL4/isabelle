(*  Title:      Pure/Isar/new_locale.ML
    Author:     Clemens Ballarin, TU Muenchen

New locale development --- experimental.
*)

signature NEW_LOCALE =
sig
  type locale

  val test_locale: theory -> string -> bool
  val register_locale: bstring ->
    (string * sort) list * (Binding.T * typ option * mixfix) list ->
    term option * term list ->
    (declaration * stamp) list * (declaration * stamp) list ->
    ((string * (Attrib.binding * (thm list * Attrib.src list) list) list) * stamp) list ->
    ((string * Morphism.morphism) * stamp) list -> theory -> theory

  (* Locale name space *)
  val intern: theory -> xstring -> string
  val extern: theory -> string -> xstring

  (* Specification *)
  val params_of: theory -> string -> (Binding.T * typ option * mixfix) list
  val instance_of: theory -> string -> Morphism.morphism -> term list
  val specification_of: theory -> string -> term option * term list
  val declarations_of: theory -> string -> declaration list * declaration list

  (* Storing results *)
  val add_thmss: string -> string -> (Attrib.binding * (thm list * Attrib.src list) list) list ->
    Proof.context -> Proof.context
  val add_type_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_term_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_declaration: string -> declaration -> Proof.context -> Proof.context
  val add_dependency: string -> (string * Morphism.morphism) -> theory -> theory

  (* Activation *)
  val activate_declarations: theory -> string * Morphism.morphism ->
    Proof.context -> Proof.context
  val activate_global_facts: string * Morphism.morphism -> theory -> theory
  val activate_local_facts: string * Morphism.morphism -> Proof.context -> Proof.context
  val init: string -> theory -> Proof.context

  (* Reasoning about locales *)
  val witness_attrib: attribute
  val intro_attrib: attribute
  val unfold_attrib: attribute
  val intro_locales_tac: bool -> Proof.context -> thm list -> tactic

  (* Registrations *)
  val add_global_registration: (string * (Morphism.morphism * Morphism.morphism)) ->
    theory -> theory
  val amend_global_registration: (string * Morphism.morphism) -> Morphism.morphism ->
    theory -> theory
  val get_global_registrations: theory -> (string * Morphism.morphism) list

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


structure NewLocale: NEW_LOCALE =
struct

datatype ctxt = datatype Element.ctxt;


(*** Basics ***)

datatype locale = Loc of {
  (* extensible lists are in reverse order: decls, notes, dependencies *)
  parameters: (string * sort) list * (Binding.T * typ option * mixfix) list,
    (* type and term parameters *)
  spec: term option * term list,
    (* assumptions (as a single predicate expression) and defines *)
  decls: (declaration * stamp) list * (declaration * stamp) list,
    (* type and term syntax declarations *)
  notes: ((string * (Attrib.binding * (thm list * Attrib.src list) list) list) * stamp) list,
    (* theorem declarations *)
  dependencies: ((string * Morphism.morphism) * stamp) list
    (* locale dependencies (sublocale relation) *)
}


(*** Theory data ***)

structure LocalesData = TheoryDataFun
(
  type T = NameSpace.T * locale Symtab.table;
    (* locale namespace and locales of the theory *)

  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;

  fun join_locales _
    (Loc {parameters, spec, decls = (decls1, decls2), notes, dependencies},
      Loc {decls = (decls1', decls2'), notes = notes',
        dependencies = dependencies', ...}) =
        let fun s_merge x = merge (eq_snd (op =)) x in
          Loc {parameters = parameters,
            spec = spec,
            decls = (s_merge (decls1, decls1'), s_merge (decls2, decls2')),
            notes = s_merge (notes, notes'),
            dependencies = s_merge (dependencies, dependencies')
          }          
        end;
  fun merge _ = NameSpace.join_tables join_locales;
);

val intern = NameSpace.intern o #1 o LocalesData.get;
val extern = NameSpace.extern o #1 o LocalesData.get;

fun get_locale thy name = Symtab.lookup (#2 (LocalesData.get thy)) name;

fun the_locale thy name = case get_locale thy name
 of SOME loc => loc
  | NONE => error ("Unknown locale " ^ quote name);

fun test_locale thy name = case get_locale thy name
 of SOME _ => true | NONE => false;

fun register_locale bname parameters spec decls notes dependencies thy =
  thy |> LocalesData.map (NameSpace.bind (Sign.naming_of thy) (Binding.name bname,
    Loc {parameters = parameters, spec = spec, decls = decls, notes = notes,
      dependencies = dependencies}) #> snd);

fun change_locale name f thy =
  let
    val Loc {parameters, spec, decls, notes, dependencies} =
        the_locale thy name;
    val (parameters', spec', decls', notes', dependencies') =
      f (parameters, spec, decls, notes, dependencies);
  in
    thy
    |> (LocalesData.map o apsnd) (Symtab.update (name, Loc {parameters = parameters',
      spec = spec', decls = decls', notes = notes', dependencies = dependencies'}))
  end;

fun print_locales thy =
  let val (space, locs) = LocalesData.get thy in
    Pretty.strs ("locales:" :: map #1 (NameSpace.extern_table (space, locs)))
    |> Pretty.writeln
  end;


(*** Primitive operations ***)

fun params_of thy name =
  let
    val Loc {parameters = (_, params), ...} = the_locale thy name
  in params end;

fun instance_of thy name morph =
  params_of thy name |>
    map ((fn (b, T, _) => Free (Binding.base_name b, the T)) #> Morphism.term morph);

fun specification_of thy name =
  let
    val Loc {spec, ...} = the_locale thy name
  in spec end;

fun declarations_of thy name =
  let
    val Loc {decls, ...} = the_locale thy name
  in
    decls |> apfst (map fst) |> apsnd (map fst)
  end;


(*** Activate context elements of locale ***)

(** Identifiers: activated locales in theory or proof context **)

type identifiers = (string * term list) list;

val empty = ([] : identifiers);

fun ident_eq thy ((n, ts), (m, ss)) = (m = n) andalso Pattern.matchess thy (ss, ts);

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
      val Loc {parameters = (_, params), dependencies, ...} = the_locale thy name;
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
    val Loc {decls = (typ_decls, term_decls), ...} = the_locale thy name;
  in
    ctxt |> fold_rev (fn (decl, _) => Context.proof_map (decl morph)) typ_decls |>
      fold_rev (fn (decl, _) => Context.proof_map (decl morph)) term_decls
  end;

fun activate_notes activ_elem thy (name, morph) input =
  let
    val Loc {notes, ...} = the_locale thy name;
    fun activate ((kind, facts), _) input =
      let
        val facts' = facts |> Element.facts_map (Element.morph_ctxt morph)
      in activ_elem (Notes (kind, facts')) input end;
  in
    fold_rev activate notes input
  end;

fun activate_all name thy activ_elem (marked, input) =
  let
    val Loc {parameters = (_, params), spec = (asm, defs), ...} =
      the_locale thy name;
  in
    input |>
      (if not (null params) then activ_elem (Fixes params) else I) |>
      (* FIXME type parameters *)
      (if is_some asm then activ_elem (Assumes [(Attrib.empty_binding, [(the asm, [])])]) else I) |>
      (if not (null defs)
        then activ_elem (Defines (map (fn def => (Attrib.empty_binding, (def, []))) defs))
        else I) |>
      pair marked |> roundup thy (activate_notes activ_elem) (name, Morphism.identity)
  end;


(** Public activation functions **)

local

fun init_global_elem (Notes (kind, facts)) thy =
      let
        val facts' = Attrib.map_facts (Attrib.attribute_i thy) facts
      in Locale.global_note_qualified kind facts' thy |> snd end

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
      in Locale.local_note_qualified kind facts' ctxt |> snd end

fun cons_elem false (Notes notes) elems = elems
  | cons_elem _ elem elems = elem :: elems

in

fun activate_declarations thy dep ctxt =
  roundup thy activate_decls dep (get_local_idents ctxt, ctxt) |> uncurry put_local_idents;

fun activate_global_facts dep thy =
  roundup thy (activate_notes init_global_elem) dep (get_global_idents thy, thy) |>
  uncurry put_global_idents;

fun activate_local_facts dep ctxt =
  roundup (ProofContext.theory_of ctxt) (activate_notes init_local_elem) dep
    (get_local_idents ctxt, ctxt) |>
  uncurry put_local_idents;

fun init name thy = activate_all name thy init_local_elem (empty, ProofContext.init thy) |>
  uncurry put_local_idents;

fun print_locale thy show_facts name =
  let
    val name' = intern thy name;
    val ctxt = init name' thy
  in
    Pretty.big_list "locale elements:"
      (activate_all name' thy (cons_elem show_facts) (empty, []) |> snd |> rev |> 
        map (Element.pretty_ctxt ctxt) |> map Pretty.chunks) |> Pretty.writeln
  end

end;


(*** Storing results ***)

(* Theorems *)

fun add_thmss loc kind args ctxt =
  let
    val (([Notes args'], _), ctxt') = Element.activate_i [Notes (kind, args)] ctxt;
    val ctxt'' = ctxt' |> ProofContext.theory
      (change_locale loc
        (fn (parameters, spec, decls, notes, dependencies) =>
          (parameters, spec, decls, (args', stamp ()) :: notes, dependencies)))
      (* FIXME registrations *)
  in ctxt'' end;


(* Declarations *)

local

fun decl_attrib decl phi = Thm.declaration_attribute (K (decl phi));

fun add_decls add loc decl =
  ProofContext.theory (change_locale loc
    (fn (parameters, spec, decls, notes, dependencies) =>
      (parameters, spec, add (decl, stamp ()) decls, notes, dependencies))) #>
  add_thmss loc Thm.internalK
    [((Binding.empty, [Attrib.internal (decl_attrib decl)]), [([Drule.dummy_thm], [])])];

in

val add_type_syntax = add_decls (apfst o cons);
val add_term_syntax = add_decls (apsnd o cons);
val add_declaration = add_decls (K I);

end;

(* Dependencies *)

fun add_dependency loc dep =
  change_locale loc
    (fn (parameters, spec, decls, notes, dependencies) =>
      (parameters, spec, decls, notes, (dep, stamp ()) :: dependencies));


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
      Method.ctxt_args (fn ctxt => Method.METHOD (intro_locales_tac false ctxt ORELSE'
        Locale.intro_locales_tac false ctxt)),
      "back-chain introduction rules of locales without unfolding predicates"),
     ("unfold_locales",
      Method.ctxt_args (fn ctxt => Method.METHOD (intro_locales_tac true ctxt ORELSE'
        Locale.intro_locales_tac true ctxt)),
      "back-chain all introduction rules of locales")]));


(*** Registrations: interpretations in theories ***)

(* FIXME only global variant needed *)
structure RegistrationsData = GenericDataFun
(
  type T = ((string * (Morphism.morphism * Morphism.morphism)) * stamp) list;
(* FIXME mixins need to be stamped *)
    (* registrations, in reverse order of declaration *)
  val empty = [];
  val extend = I;
  fun merge _ = Library.merge (eq_snd (op =));
    (* FIXME consolidate with dependencies, consider one data slot only *)
);

val get_global_registrations =
  Context.Theory #> RegistrationsData.get #> map fst #> map (apsnd op $>);
fun add_global_registration reg =
  (Context.theory_map o RegistrationsData.map) (cons (reg, stamp ()));

fun amend_global_registration (name, base_morph) morph thy =
  let
    val regs = (Context.Theory #> RegistrationsData.get #> map fst) thy;
    val base = instance_of thy name base_morph;
    fun match (name', (morph', _)) =
      name = name' andalso eq_list (op aconv) (base, instance_of thy name' morph');
    val i = find_index match (rev regs);
    val _ = if i = ~1 then error ("No interpretation of locale " ^
        quote (extern thy name) ^ " and parameter instantiation " ^
        space_implode " " (map (quote o Syntax.string_of_term_global thy) base) ^ " available.")
      else ();
  in
    (Context.theory_map o RegistrationsData.map) (nth_map (length regs - 1 - i)
      (fn ((name, (base, export)), stamp) => ((name, (base $> morph, export)), stamp))) thy
  end;

end;

