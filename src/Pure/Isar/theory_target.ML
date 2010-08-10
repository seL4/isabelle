(*  Title:      Pure/Isar/theory_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Common theory/locale/class/instantiation/overloading targets.
*)

signature THEORY_TARGET =
sig
  val peek: local_theory ->
   {target: string,
    is_locale: bool,
    is_class: bool,
    instantiation: string list * (string * sort) list * sort,
    overloading: (string * (string * typ) * bool) list}
  val init: string option -> theory -> local_theory
  val context_cmd: xstring -> theory -> local_theory
  val instantiation: string list * (string * sort) list * sort -> theory -> local_theory
  val instantiation_cmd: xstring list * xstring list * xstring -> theory -> local_theory
  val overloading: (string * (string * typ) * bool) list -> theory -> local_theory
  val overloading_cmd: (string * string * bool) list -> theory -> local_theory
end;

structure Theory_Target: THEORY_TARGET =
struct

(* context data *)

datatype target = Target of {target: string, is_locale: bool,
  is_class: bool, instantiation: string list * (string * sort) list * sort,
  overloading: (string * (string * typ) * bool) list};

fun make_target target is_locale is_class instantiation overloading =
  Target {target = target, is_locale = is_locale,
    is_class = is_class, instantiation = instantiation, overloading = overloading};

val global_target = make_target "" false false ([], [], []) [];

structure Data = Proof_Data
(
  type T = target;
  fun init _ = global_target;
);

val peek = (fn Target args => args) o Data.get;


(* generic declarations *)

fun theory_declaration decl lthy =
  let
    val global_decl = Morphism.form
      (Morphism.transform (Local_Theory.global_morphism lthy) decl);
  in
    lthy
    |> Local_Theory.theory (Context.theory_map global_decl)
    |> Local_Theory.target (Context.proof_map global_decl)
  end;

fun locale_declaration locale { syntax, pervasive } decl lthy =
  let
    val add = if syntax then Locale.add_syntax_declaration else Locale.add_declaration;
    val locale_decl = Morphism.transform (Local_Theory.target_morphism lthy) decl;
  in
    lthy
    |> pervasive ? theory_declaration decl
    |> Local_Theory.target (add locale locale_decl)
  end;

fun target_declaration (Target {target, ...}) { syntax, pervasive } =
  if target = "" then theory_declaration
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


(* mixfix notation *)

fun fork_mixfix (Target {is_locale, is_class, ...}) mx =
  if not is_locale then (NoSyn, NoSyn, mx)
  else if not is_class then (NoSyn, mx, NoSyn)
  else (mx, NoSyn, NoSyn);


(* define *)

local

fun syntax_error c = error ("Illegal mixfix syntax for overloaded constant " ^ quote c);

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

in

fun define ta = Generic_Target.define (foundation ta);

end;


(* notes *)

fun theory_notes kind global_facts lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val global_facts' = Attrib.map_facts (Attrib.attribute_i thy) global_facts;
  in
    lthy
    |> Local_Theory.theory (PureThy.note_thmss kind global_facts' #> snd)
    |> Local_Theory.target (ProofContext.note_thmss kind global_facts' #> snd)
  end;

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

fun notes (Target {target, is_locale, ...}) =
  Generic_Target.notes (if is_locale then locale_notes target
    else fn kind => fn global_facts => fn _ => theory_notes kind global_facts);


(* abbrev *)

fun theory_abbrev prmode ((b, mx), t) = Local_Theory.theory
  (Sign.add_abbrev (#1 prmode) (b, t) #->
    (fn (lhs, _) => Sign.notation true prmode [(lhs, mx)]));

fun locale_abbrev ta prmode ((b, mx), t) xs = Local_Theory.theory_result
  (Sign.add_abbrev Print_Mode.internal (b, t)) #->
    (fn (lhs, _) => locale_const_declaration ta prmode
      ((b, mx), Term.list_comb (Logic.unvarify_global lhs, xs)));

fun target_abbrev (ta as Target {target, is_locale, is_class, ...})
    prmode (b, mx) (global_rhs, t') xs lthy =
  let
    val (mx1, mx2, mx3) = fork_mixfix ta mx;
  in if is_locale
    then lthy
      |> locale_abbrev ta prmode ((b, mx2), global_rhs) xs
      |> is_class ? class_target ta (Class_Target.abbrev target prmode ((b, mx1), t'))
    else lthy
      |> theory_abbrev prmode ((b, mx3), global_rhs)
  end;

fun abbrev ta = Generic_Target.abbrev (target_abbrev ta);


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

fun pretty (Target {target, is_class, instantiation, overloading, ...}) ctxt =
  Pretty.block [Pretty.command "theory", Pretty.brk 1,
      Pretty.str (Context.theory_name (ProofContext.theory_of ctxt))] ::
    (if not (null overloading) then [Overloading.pretty ctxt]
     else if not (null (#1 instantiation)) then [Class_Target.pretty_instantiation ctxt]
     else pretty_thy ctxt target is_class);


(* init various targets *)

local

fun init_data (Target {target, is_locale, is_class, instantiation, overloading}) =
  if not (null (#1 instantiation)) then Class_Target.init_instantiation instantiation
  else if not (null overloading) then Overloading.init overloading
  else if not is_locale then ProofContext.init_global
  else if not is_class then Locale.init target
  else Class_Target.init target;

fun init_target (ta as Target {target, instantiation, overloading, ...}) thy =
  thy
  |> init_data ta
  |> Data.put ta
  |> Local_Theory.init NONE (Long_Name.base_name target)
     {define = define ta,
      notes = notes ta,
      abbrev = abbrev ta,
      declaration = fn pervasive => target_declaration ta
        { syntax = false, pervasive = pervasive },
      syntax_declaration = fn pervasive => target_declaration ta
        { syntax = true, pervasive = pervasive },
      pretty = pretty ta,
      reinit = init_target ta o ProofContext.theory_of,
      exit = Local_Theory.target_of o
        (if not (null (#1 instantiation)) then Class_Target.conclude_instantiation
         else if not (null overloading) then Overloading.conclude
         else I)};

fun named_target _ NONE = global_target
  | named_target thy (SOME target) =
      if Locale.defined thy target
      then make_target target true (Class_Target.is_class thy target) ([], [], []) []
      else error ("No such locale: " ^ quote target);

fun gen_overloading prep_const raw_ops thy =
  let
    val ctxt = ProofContext.init_global thy;
    val ops = raw_ops |> map (fn (name, const, checked) =>
      (name, Term.dest_Const (prep_const ctxt const), checked));
  in thy |> init_target (make_target "" false false ([], [], []) ops) end;

in

fun init target thy = init_target (named_target thy target) thy;

fun context_cmd "-" thy = init NONE thy
  | context_cmd target thy = init (SOME (Locale.intern thy target)) thy;

fun instantiation arities = init_target (make_target "" false false arities []);
fun instantiation_cmd arities thy =
  instantiation (Class_Target.read_multi_arity thy arities) thy;

val overloading = gen_overloading (fn ctxt => Syntax.check_term ctxt o Const);
val overloading_cmd = gen_overloading Syntax.read_term;

end;

end;
