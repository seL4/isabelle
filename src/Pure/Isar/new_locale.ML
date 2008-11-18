(*  Title:      Pure/Isar/expression.ML
    ID:         $Id$
    Author:     Clemens Ballarin, TU Muenchen

New locale development --- experimental.
*)

signature NEW_LOCALE =
sig
  type locale

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
  val declarations_of: theory -> string -> declaration list * declaration list;

  (* Storing results *)
  val add_thmss: string -> string -> (Attrib.binding * (thm list * Attrib.src list) list) list ->
    Proof.context -> Proof.context
  val add_type_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_term_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_declaration: string -> declaration -> Proof.context -> Proof.context

  (* Activate locales *)
  val activate_declarations: string -> theory -> Proof.context -> Proof.context
  val activate: string -> theory -> (Element.context_i -> 'a -> 'a) -> 'a -> 'a
  val init: string -> theory -> Proof.context

  (* Diagnostic *)
  val print_locales: theory -> unit
  val print_locale: theory -> bool -> bstring -> unit
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

fun declarations_of thy loc =
  let
    val Loc {decls, ...} = the_locale thy loc
  in
    decls |> apfst (map fst) |> apsnd (map fst)
  end;


(*** Activate context elements of locale ***)

(* Resolve locale dependencies in a depth-first fashion *)

local

structure Idtab = TableFun(type key = string * term list
  val ord = prod_ord string_ord (list_ord Term.fast_term_ord));

in

fun roundup thy deps =
  let
    fun add (name, morph) (deps, marked) =
      let
        val Loc {parameters = (_, params), dependencies, ...} = the_locale thy name;
        val instance = params |>
          map ((fn (b, T, _) => Free (Name.name_of b, the T)) #> Morphism.term morph);
      in
        if Idtab.defined marked (name, instance)
        then (deps, marked)
        else
          let
            val dependencies' =
              map (fn ((name, morph'), _) => (name, morph' $>  morph)) dependencies;
            val marked' = Idtab.insert (op =) ((name, instance), ()) marked;
            val (deps', marked'') = fold_rev add dependencies' ([], marked');
          in
            (cons (name, morph) deps' @ deps, marked'')
          end
      end
  in fold_rev add deps ([], Idtab.empty) |> fst end;

end;


fun activate_decls thy (name, morph) ctxt =
  let
    val Loc {decls = (typ_decls, term_decls), ...} = the_locale thy name;
  in
    ctxt |> fold_rev (fn (decl, _) => Context.proof_map (decl morph)) typ_decls |>
      fold_rev (fn (decl, _) => Context.proof_map (decl morph)) term_decls
  end;

fun activate_declarations name thy ctxt =
  let
    val name' = intern thy name;
    val Loc {parameters = (_, params), dependencies, ...} = the_locale thy name';
    val dependencies' =
      (name', Morphism.identity) :: roundup thy (map fst dependencies);
  in
    ctxt |>
      not (null params) ? (ProofContext.add_fixes_i params #> snd) |>
      (* FIXME type parameters *)
      fold_rev (activate_decls thy) dependencies'
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

fun activate name thy activ_elem input =
  let
    val name' = intern thy name;
    val Loc {parameters = (_, params), spec = (asm, defs), dependencies, ...} =
      the_locale thy name';
    val dependencies' =
      (name', Morphism.identity) :: roundup thy (map fst dependencies);
  in
    input |>
      not (null params) ? activ_elem (Fixes params) |>
      (* FIXME type parameters *)
      is_some asm ? activ_elem (Assumes [(Attrib.no_binding, [(the asm, [])])]) |>
      not (null defs) ?
        activ_elem (Defines (map (fn def => (Attrib.no_binding, (def, []))) defs)) |>
      fold_rev (activate_notes activ_elem thy) dependencies'
  end;

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
      in fold (fn args => Locale.local_note_prefix kind args #> snd) facts' ctxt end

fun cons_elem false (Notes notes) elems = elems
  | cons_elem _ elem elems = elem :: elems

in

fun init name thy = activate name thy init_elem (ProofContext.init thy);

fun print_locale thy show_facts name =
  let val ctxt = init name thy
  in
    Pretty.big_list "locale elements:"
      (activate name thy (cons_elem show_facts) [] |> rev |> 
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

end;

