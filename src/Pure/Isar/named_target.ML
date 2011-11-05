(*  Title:      Pure/Isar/named_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Targets for theory, locale and class.
*)

signature NAMED_TARGET =
sig
  val init: (local_theory -> local_theory) -> string -> theory -> local_theory
  val theory_init: theory -> local_theory
  val reinit: local_theory -> local_theory -> local_theory
  val context_cmd: xstring -> theory -> local_theory
  val peek: local_theory -> {target: string, is_locale: bool, is_class: bool} option
end;

structure Named_Target: NAMED_TARGET =
struct

(* context data *)

datatype target =
  Target of {target: string, is_locale: bool, is_class: bool,
    before_exit: local_theory -> local_theory};

fun make_target target is_locale is_class before_exit =
  Target {target = target, is_locale = is_locale, is_class = is_class,
    before_exit = before_exit};

fun named_target _ "" before_exit = make_target "" false false before_exit
  | named_target thy locale before_exit =
      if Locale.defined thy locale
      then make_target locale true (Class.is_class thy locale) before_exit
      else error ("No such locale: " ^ quote locale);

structure Data = Proof_Data
(
  type T = target option;
  fun init _ = NONE;
);

val peek =
  Data.get #> Option.map (fn Target {target, is_locale, is_class, ...} =>
    {target = target, is_locale = is_locale, is_class = is_class});


(* generic declarations *)

fun locale_declaration locale syntax decl lthy =
  let
    val add = if syntax then Locale.add_syntax_declaration else Locale.add_declaration;
    val locale_decl = Morphism.transform (Local_Theory.target_morphism lthy) decl;
  in
    lthy
    |> Local_Theory.target (add locale locale_decl)
  end;

fun target_declaration (Target {target, ...}) {syntax, pervasive} decl =
  if target = "" then Generic_Target.theory_declaration decl
  else
    locale_declaration target syntax decl
    #> pervasive ? Generic_Target.theory_declaration decl
    #> not pervasive ? Context.proof_map (Morphism.form decl);


(* consts in locales *)

fun locale_const (ta as Target {target, is_class, ...}) (prmode as (mode, _)) ((b, mx), rhs) =
  locale_declaration target true (fn phi =>
    let
      val b' = Morphism.binding phi b;
      val rhs' = Morphism.term phi rhs;
      val arg = (b', Term.close_schematic_term rhs');
      val same_shape = Term.aconv_untyped (rhs, rhs');

      (* FIXME workaround based on educated guess *)
      val prefix' = Binding.prefix_of b';
      val is_canonical_class = is_class andalso
        (Binding.eq_name (b, b')
          andalso not (null prefix')
          andalso List.last prefix' = (Class.class_prefix target, false)
        orelse same_shape);
    in
      not is_canonical_class ?
        (Context.mapping_result
          (Sign.add_abbrev Print_Mode.internal arg)
          (Proof_Context.add_abbrev Print_Mode.internal arg)
        #-> (fn (lhs' as Const (d, _), _) =>
            same_shape ?
              (Context.mapping
                (Sign.revert_abbrev mode d) (Proof_Context.revert_abbrev mode d) #>
               Morphism.form (Proof_Context.target_notation true prmode [(lhs', mx)]))))
    end);


(* define *)

fun locale_foundation ta (((b, U), mx), (b_def, rhs)) (type_params, term_params) =
  Generic_Target.theory_foundation (((b, U), NoSyn), (b_def, rhs)) (type_params, term_params)
  #-> (fn (lhs, def) => locale_const ta Syntax.mode_default ((b, mx), lhs)
    #> pair (lhs, def))

fun class_foundation (ta as Target {target, ...})
    (((b, U), mx), (b_def, rhs)) (type_params, term_params) =
  Generic_Target.theory_foundation (((b, U), NoSyn), (b_def, rhs)) (type_params, term_params)
  #-> (fn (lhs, def) => locale_const ta Syntax.mode_default ((b, NoSyn), lhs)
    #> Class.const target ((b, mx), (type_params, lhs))
    #> pair (lhs, def))

fun target_foundation (ta as Target {is_locale, is_class, ...}) =
  if is_class then class_foundation ta
  else if is_locale then locale_foundation ta
  else Generic_Target.theory_foundation;


(* notes *)

fun locale_notes locale kind global_facts local_facts lthy =
  let
    val global_facts' = Attrib.map_facts (K I) global_facts;
    val local_facts' = Element.facts_map
      (Element.transform_ctxt (Local_Theory.target_morphism lthy)) local_facts;
  in
    lthy
    |> Local_Theory.background_theory (Global_Theory.note_thmss kind global_facts' #> snd)
    |> Local_Theory.target (Locale.add_thmss locale kind local_facts')
  end

fun target_notes (Target {target, is_locale, ...}) =
  if is_locale then locale_notes target
  else fn kind => fn global_facts => fn _ => Generic_Target.theory_notes kind global_facts;


(* abbrev *)

fun locale_abbrev ta prmode ((b, mx), t) xs =
  Local_Theory.background_theory_result
    (Sign.add_abbrev Print_Mode.internal (b, t)) #->
      (fn (lhs, _) => locale_const ta prmode
        ((b, mx), Term.list_comb (Logic.unvarify_global lhs, xs)));

fun target_abbrev (ta as Target {target, is_locale, is_class, ...})
    prmode (b, mx) (global_rhs, t') xs lthy =
  if is_locale then
    lthy
    |> locale_abbrev ta prmode ((b, if is_class then NoSyn else mx), global_rhs) xs
    |> is_class ? Class.abbrev target prmode ((b, mx), t')
  else
    lthy
    |> Generic_Target.theory_abbrev prmode ((b, mx), global_rhs);


(* pretty *)

fun pretty (Target {target, is_locale, is_class, ...}) ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val target_name =
      [Pretty.command (if is_class then "class" else "locale"),
        Pretty.str (" " ^ Locale.extern thy target)];
    val fixes = map (fn (x, T) => (Binding.name x, SOME T, NoSyn))
      (#1 (Proof_Context.inferred_fixes ctxt));
    val assumes = map (fn A => (Attrib.empty_binding, [(Thm.term_of A, [])]))
      (Assumption.all_assms_of ctxt);
    val elems =
      (if null fixes then [] else [Element.Fixes fixes]) @
      (if null assumes then [] else [Element.Assumes assumes]);
    val body_elems =
      if not is_locale then []
      else if null elems then [Pretty.block target_name]
      else [Pretty.block (Pretty.fbreaks (Pretty.block (target_name @ [Pretty.str " ="]) ::
        map (Pretty.chunks o Element.pretty_ctxt ctxt) elems))];
  in
    Pretty.block [Pretty.command "theory", Pretty.brk 1,
      Pretty.str (Context.theory_name (Proof_Context.theory_of ctxt))] :: body_elems
  end;


(* init *)

fun init_context (Target {target, is_locale, is_class, ...}) =
  if not is_locale then Proof_Context.init_global
  else if not is_class then Locale.init target
  else Class.init target;

fun init before_exit target thy =
  let
    val ta = named_target thy target before_exit;
  in
    thy
    |> init_context ta
    |> Data.put (SOME ta)
    |> Local_Theory.init NONE (Long_Name.base_name target)
       {define = Generic_Target.define (target_foundation ta),
        notes = Generic_Target.notes (target_notes ta),
        abbrev = Generic_Target.abbrev (target_abbrev ta),
        declaration = target_declaration ta,
        pretty = pretty ta,
        exit = Local_Theory.target_of o before_exit}
  end;

val theory_init = init I "";

fun reinit lthy =
  (case Data.get lthy of
    SOME (Target {target, before_exit, ...}) =>
      init before_exit target o Local_Theory.exit_global
  | NONE => error "Not in a named target");

fun context_cmd "-" thy = init I "" thy
  | context_cmd target thy = init I (Locale.intern thy target) thy;

end;
