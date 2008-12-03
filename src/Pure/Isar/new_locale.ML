(*  Title:      Pure/Isar/new_locale.ML
    Author:     Clemens Ballarin, TU Muenchen

New locale development --- experimental.
*)

signature NEW_LOCALE =
sig
  type locale

  val clear_idents: Proof.context -> Proof.context
  val test_locale: theory -> string -> bool
  val register_locale: string ->
    (string * sort) list * (Name.binding * typ option * mixfix) list ->
    term option * term list ->
    (declaration * stamp) list * (declaration * stamp) list ->
    ((string * (Attrib.binding * (thm list * Attrib.src list) list) list) * stamp) list ->
    ((string * Morphism.morphism) * stamp) list -> theory -> theory

  (* Locale name space *)
  val intern: theory -> xstring -> string
  val extern: theory -> string -> xstring

  (* Specification *)
  val params_of: theory -> string -> (Name.binding * typ option * mixfix) list
  val specification_of: theory -> string -> term option * term list
  val declarations_of: theory -> string -> declaration list * declaration list

  (* Storing results *)
  val add_thmss: string -> string -> (Attrib.binding * (thm list * Attrib.src list) list) list ->
    Proof.context -> Proof.context
  val add_type_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_term_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_declaration: string -> declaration -> Proof.context -> Proof.context
  val add_dependency: string -> (string * Morphism.morphism) -> Proof.context -> Proof.context

  (* Activation *)
  val activate_declarations: theory -> string * Morphism.morphism ->
    Proof.context -> Proof.context
  val activate_facts: theory -> string * Morphism.morphism ->
    Proof.context -> Proof.context
(*  val activate: string -> theory -> (Element.context_i -> 'a -> 'a) -> 'a -> 'a *)
  val init: string -> theory -> Proof.context

  (* Reasoning about locales *)
  val witness_attrib: attribute
  val intro_attrib: attribute
  val unfold_attrib: attribute
  val intro_locales_tac: bool -> Proof.context -> thm list -> tactic

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
  parameters: (string * sort) list * (Name.binding * typ option * mixfix) list,
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

  val empty = (NameSpace.empty, Symtab.empty);
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
  fun merge _ ((space1, locs1), (space2, locs2)) =
    (NameSpace.merge (space1, space2), Symtab.join join_locales (locs1, locs2));
);

val intern = NameSpace.intern o #1 o LocalesData.get;
val extern = NameSpace.extern o #1 o LocalesData.get;

fun get_locale thy name = Symtab.lookup (#2 (LocalesData.get thy)) name;

fun the_locale thy name = case get_locale thy name
 of SOME loc => loc
  | NONE => error ("Unknown locale " ^ quote name);

fun test_locale thy name = case get_locale thy name
 of SOME _ => true | NONE => false;

fun register_locale name parameters spec decls notes dependencies thy =
  thy |> LocalesData.map (fn (space, locs) =>
    (Sign.declare_name thy name space, Symtab.update (name,
      Loc {parameters = parameters, spec = spec, decls = decls, notes = notes,
        dependencies = dependencies}) locs));

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

structure IdentifiersData = GenericDataFun
(
  type T = identifiers;
  val empty = empty;
  val extend = I;
  fun merge _ = Library.merge (op =);  (* FIXME cannot do this properly without theory context *)
);

in

val get_idents = IdentifiersData.get o Context.Proof;
val put_idents = Context.proof_map o IdentifiersData.put;
val clear_idents = put_idents empty;

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
      val instance = params |>
        map ((fn (b, T, _) => Free (Name.name_of b, the T)) #> Morphism.term morph);
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
    val (dependencies', marked') = add thy 0 (name, morph) ([], marked);
  in
    (marked', input |> fold_rev (activate_dep thy) dependencies')
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
    val Loc {parameters = (_, params), spec = (asm, defs), dependencies, ...} =
      the_locale thy name;
  in
    input |>
      (if not (null params) then activ_elem (Fixes params) else I) |>
      (* FIXME type parameters *)
      (if is_some asm then activ_elem (Assumes [(Attrib.no_binding, [(the asm, [])])]) else I) |>
      (if not (null defs)
        then activ_elem (Defines (map (fn def => (Attrib.no_binding, (def, []))) defs))
        else I) |>
      pair marked |> roundup thy (activate_notes activ_elem) (name, Morphism.identity)
  end;


(** Public activation functions **)

local

fun init_elem (Fixes fixes) ctxt = ctxt |>
      ProofContext.add_fixes_i fixes |> snd
  | init_elem (Assumes assms) ctxt =
      let
        val assms' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) assms
      in
        ctxt |> fold Variable.auto_fixes (maps (map fst o snd) assms') |>
          ProofContext.add_assms_i Assumption.assume_export assms' |> snd
     end 
  | init_elem (Defines defs) ctxt =
      let
        val defs' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) defs
      in
        ctxt |> fold Variable.auto_fixes (map (fst o snd) defs') |>
          ProofContext.add_assms_i LocalDefs.def_export (map (fn (attn, t) => (attn, [t])) defs') |>
          snd
      end
  | init_elem (Notes (kind, facts)) ctxt =
      let
        val facts' = Attrib.map_facts (Attrib.attribute_i (ProofContext.theory_of ctxt)) facts
      in Locale.local_note_qualified kind facts' ctxt |> snd end

fun cons_elem false (Notes notes) elems = elems
  | cons_elem _ elem elems = elem :: elems

in

fun activate_declarations thy dep ctxt =
  roundup thy activate_decls dep (get_idents ctxt, ctxt) |> uncurry put_idents;
  
fun activate_facts thy dep ctxt =
  roundup thy (activate_notes init_elem) dep (get_idents ctxt, ctxt) |> uncurry put_idents;

fun init name thy = activate_all name thy init_elem (empty, ProofContext.init thy) |>
  uncurry put_idents;

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
    [((Name.no_binding, [Attrib.internal (decl_attrib decl)]), [([Drule.dummy_thm], [])])];

in

val add_type_syntax = add_decls (apfst o cons);
val add_term_syntax = add_decls (apsnd o cons);
val add_declaration = add_decls (K I);

end;

(* Dependencies *)

fun add_dependency loc dep =
  ProofContext.theory (change_locale loc
    (fn (parameters, spec, decls, notes, dependencies) =>
      (parameters, spec, decls, notes, (dep, stamp ()) :: dependencies)));


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


end;

