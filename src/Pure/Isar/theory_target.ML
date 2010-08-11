(*  Title:      Pure/Isar/theory_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Common theory/locale/class/instantiation/overloading targets.
*)

signature THEORY_TARGET =
sig
  val peek: local_theory -> {target: string, is_locale: bool, is_class: bool}
  val init: string option -> theory -> local_theory
  val context_cmd: xstring -> theory -> local_theory
end;

structure Theory_Target: THEORY_TARGET =
struct

(* context data *)

datatype target = Target of {target: string, is_locale: bool, is_class: bool};

fun make_target target is_locale is_class =
  Target {target = target, is_locale = is_locale, is_class = is_class};

val global_target = make_target "" false false;

structure Data = Proof_Data
(
  type T = target;
  fun init _ = global_target;
);

val peek = (fn Target args => args) o Data.get;


(* generic declarations *)

fun locale_declaration locale { syntax, pervasive } decl lthy =
  let
    val add = if syntax then Locale.add_syntax_declaration else Locale.add_declaration;
    val locale_decl = Morphism.transform (Local_Theory.target_morphism lthy) decl;
  in
    lthy
    |> pervasive ? Generic_Target.theory_declaration decl
    |> Local_Theory.target (add locale locale_decl)
  end;

fun target_declaration (Target {target, ...}) { syntax, pervasive } =
  if target = "" then Generic_Target.theory_declaration
  else locale_declaration target { syntax = syntax, pervasive = pervasive };


(* consts in locales *)

fun locale_const (Target {target, is_class, ...}) (prmode as (mode, _)) ((b, mx), rhs) phi =
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
        andalso List.last prefix' = (Class_Target.class_prefix target, false)
      orelse same_shape);
  in
    not is_canonical_class ?
      (Context.mapping_result
        (Sign.add_abbrev Print_Mode.internal arg)
        (ProofContext.add_abbrev Print_Mode.internal arg)
      #-> (fn (lhs' as Const (d, _), _) =>
          same_shape ?
            (Context.mapping
              (Sign.revert_abbrev mode d) (ProofContext.revert_abbrev mode d) #>
             Morphism.form (ProofContext.target_notation true prmode [(lhs', mx)]))))
  end;

fun locale_const_declaration (ta as Target {target, ...}) prmode arg =
  locale_declaration target { syntax = true, pervasive = false } (locale_const ta prmode arg);

fun class_target (Target {target, ...}) f =
  Local_Theory.raw_theory f #>
  Local_Theory.target (Class_Target.refresh_syntax target);


(* define *)

fun locale_foundation ta (((b, U), mx), (b_def, rhs)) (type_params, term_params) =
  Generic_Target.theory_foundation (((b, U), NoSyn), (b_def, rhs)) (type_params, term_params)
  #-> (fn (lhs, def) => locale_const_declaration ta Syntax.mode_default ((b, mx), lhs)
    #> pair (lhs, def))

fun class_foundation (ta as Target {target, ...})
    (((b, U), mx), (b_def, rhs)) (type_params, term_params) =
  Generic_Target.theory_foundation (((b, U), NoSyn), (b_def, rhs)) (type_params, term_params)
  #-> (fn (lhs, def) => locale_const_declaration ta Syntax.mode_default ((b, NoSyn), lhs)
    #> class_target ta (Class_Target.declare target ((b, mx), (type_params, lhs)))
    #> pair (lhs, def))

fun syntax_error c = error ("Illegal mixfix syntax for overloaded constant " ^ quote c);

fun fork_mixfix (Target {is_locale, is_class, ...}) mx =
  if not is_locale then (NoSyn, NoSyn, mx)
  else if not is_class then (NoSyn, mx, NoSyn)
  else (mx, NoSyn, NoSyn);

fun foundation (ta as Target {target, is_locale, is_class, ...})
    (((b, U), mx), (b_def, rhs)) (type_params, term_params) lthy =
  let
    val (mx1, mx2, mx3) = fork_mixfix ta mx;
    val (const, lthy2) = lthy |>
      (case Class_Target.instantiation_param lthy b of
        SOME c =>
          if mx3 <> NoSyn then syntax_error c
          else Local_Theory.theory_result (AxClass.declare_overloaded (c, U))
            ##> Class_Target.confirm_declaration b
      | NONE =>
          (case Overloading.operation lthy b of
            SOME (c, _) =>
              if mx3 <> NoSyn then syntax_error c
              else Local_Theory.theory_result (Overloading.declare (c, U))
                ##> Overloading.confirm b
          | NONE => Local_Theory.theory_result (Sign.declare_const ((b, U), mx3))));
    val Const (head, _) = const;
    val lhs = list_comb (const, type_params @ term_params);
  in
    lthy2
    |> pair lhs
    ||>> Local_Theory.theory_result
      (case Overloading.operation lthy b of
        SOME (_, checked) => Overloading.define checked b_def (head, rhs)
      | NONE =>
          if is_some (Class_Target.instantiation_param lthy b)
          then AxClass.define_overloaded b_def (head, rhs)
          else Thm.add_def false false (b_def, Logic.mk_equals (lhs, rhs)) #>> snd)
    ||> is_locale ? locale_const_declaration ta Syntax.mode_default ((b, mx2), lhs)
    ||> is_class ? class_target ta
          (Class_Target.declare target ((b, mx1), (type_params, lhs)))
  end;


(* notes *)

fun locale_notes locale kind global_facts local_facts lthy = 
  let
    val global_facts' = Attrib.map_facts (K I) global_facts;
    val local_facts' = Element.facts_map
      (Element.morph_ctxt (Local_Theory.target_morphism lthy)) local_facts;
  in
    lthy
    |> Local_Theory.theory (PureThy.note_thmss kind global_facts' #> snd)
    |> Local_Theory.target (Locale.add_thmss locale kind local_facts')
  end

fun target_notes (ta as Target {target, is_locale, ...}) =
  if is_locale then locale_notes target
    else fn kind => fn global_facts => fn _ => Generic_Target.theory_notes kind global_facts;


(* abbrev *)

fun locale_abbrev ta prmode ((b, mx), t) xs = Local_Theory.theory_result
  (Sign.add_abbrev Print_Mode.internal (b, t)) #->
    (fn (lhs, _) => locale_const_declaration ta prmode
      ((b, mx), Term.list_comb (Logic.unvarify_global lhs, xs)));

fun target_abbrev (ta as Target {target, is_locale, is_class, ...})
    prmode (b, mx) (global_rhs, t') xs lthy =
  if is_locale
    then lthy
      |> locale_abbrev ta prmode ((b, if is_class then NoSyn else mx), global_rhs) xs
      |> is_class ? class_target ta (Class_Target.abbrev target prmode ((b, mx), t'))
    else lthy
      |> Generic_Target.theory_abbrev prmode ((b, mx), global_rhs);


(* pretty *)

fun pretty_thy ctxt target is_class =
  let
    val thy = ProofContext.theory_of ctxt;
    val target_name =
      [Pretty.command (if is_class then "class" else "locale"),
        Pretty.str (" " ^ Locale.extern thy target)];
    val fixes = map (fn (x, T) => (Binding.name x, SOME T, NoSyn))
      (#1 (ProofContext.inferred_fixes ctxt));
    val assumes = map (fn A => (Attrib.empty_binding, [(Thm.term_of A, [])]))
      (Assumption.all_assms_of ctxt);
    val elems =
      (if null fixes then [] else [Element.Fixes fixes]) @
      (if null assumes then [] else [Element.Assumes assumes]);
  in
    if target = "" then []
    else if null elems then [Pretty.block target_name]
    else [Pretty.block (Pretty.fbreaks (Pretty.block (target_name @ [Pretty.str " ="]) ::
      map (Pretty.chunks o Element.pretty_ctxt ctxt) elems))]
  end;

fun pretty (Target {target, is_class, ...}) ctxt =
  Pretty.block [Pretty.command "theory", Pretty.brk 1,
      Pretty.str (Context.theory_name (ProofContext.theory_of ctxt))] ::
    pretty_thy ctxt target is_class;


(* init various targets *)

local

fun init_data (Target {target, is_locale, is_class}) =
  if not is_locale then ProofContext.init_global
  else if not is_class then Locale.init target
  else Class_Target.init target;

fun init_target (ta as Target {target, ...}) thy =
  thy
  |> init_data ta
  |> Data.put ta
  |> Local_Theory.init NONE (Long_Name.base_name target)
     {define = Generic_Target.define (foundation ta),
      notes = Generic_Target.notes (target_notes ta),
      abbrev = Generic_Target.abbrev (target_abbrev ta),
      declaration = fn pervasive => target_declaration ta
        { syntax = false, pervasive = pervasive },
      syntax_declaration = fn pervasive => target_declaration ta
        { syntax = true, pervasive = pervasive },
      pretty = pretty ta,
      reinit = init_target ta o ProofContext.theory_of,
      exit = Local_Theory.target_of};

fun named_target _ NONE = global_target
  | named_target thy (SOME target) =
      if Locale.defined thy target
      then make_target target true (Class_Target.is_class thy target)
      else error ("No such locale: " ^ quote target);

in

fun init target thy = init_target (named_target thy target) thy;

fun context_cmd "-" thy = init NONE thy
  | context_cmd target thy = init (SOME (Locale.intern thy target)) thy;

end;

end;
