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


(* pretty *)

fun pretty_thy ctxt target is_class =
  let
    val thy = ProofContext.theory_of ctxt;
    val target_name =
      [Pretty.command (if is_class then "class" else "locale"),
        Pretty.str (" " ^ Locale.extern thy target)];
    val fixes =
      map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) (#1 (ProofContext.inferred_fixes ctxt));
    val assumes =
      map (fn A => (Attrib.empty_binding, [(Thm.term_of A, [])])) (Assumption.all_assms_of ctxt);
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


(* generic declarations *)

local

fun direct_decl decl =
  let val decl0 = Morphism.form decl in
    Local_Theory.theory (Context.theory_map decl0) #>
    Local_Theory.target (Context.proof_map decl0)
  end;

fun target_decl add (Target {target, ...}) pervasive decl lthy =
  let
    val global_decl = Morphism.transform (Local_Theory.global_morphism lthy) decl;
    val target_decl = Morphism.transform (Local_Theory.target_morphism lthy) decl;
  in
    if target = "" then
      lthy
      |> direct_decl global_decl
    else
      lthy
      |> pervasive ? direct_decl global_decl
      |> Local_Theory.target (add target target_decl)
  end;

in

val declaration = target_decl Locale.add_declaration;
val syntax_declaration = target_decl Locale.add_syntax_declaration;

end;

fun class_target (Target {target, ...}) f =
  Local_Theory.raw_theory f #>
  Local_Theory.target (Class_Target.refresh_syntax target);


(* notes *)

fun import_export_proof ctxt (name, raw_th) =
  let
    val thy = ProofContext.theory_of ctxt;
    val thy_ctxt = ProofContext.init_global thy;
    val certT = Thm.ctyp_of thy;
    val cert = Thm.cterm_of thy;

    (*export assumes/defines*)
    val th = Goal.norm_result raw_th;
    val (defs, th') = Local_Defs.export ctxt thy_ctxt th;
    val assms = map (MetaSimplifier.rewrite_rule defs o Thm.assume) (Assumption.all_assms_of ctxt);
    val nprems = Thm.nprems_of th' - Thm.nprems_of th;

    (*export fixes*)
    val tfrees = map TFree (Thm.fold_terms Term.add_tfrees th' []);
    val frees = map Free (Thm.fold_terms Term.add_frees th' []);
    val (th'' :: vs) = (th' :: map (Drule.mk_term o cert) (map Logic.mk_type tfrees @ frees))
      |> Variable.export ctxt thy_ctxt
      |> Drule.zero_var_indexes_list;

    (*thm definition*)
    val result = PureThy.name_thm true true name th'';

    (*import fixes*)
    val (tvars, vars) =
      chop (length tfrees) (map (Thm.term_of o Drule.dest_term) vs)
      |>> map Logic.dest_type;

    val instT = map_filter (fn (TVar v, T) => SOME (v, T) | _ => NONE) (tvars ~~ tfrees);
    val inst = filter (is_Var o fst) (vars ~~ frees);
    val cinstT = map (pairself certT o apfst TVar) instT;
    val cinst = map (pairself (cert o Term.map_types (Term_Subst.instantiateT instT))) inst;
    val result' = Thm.instantiate (cinstT, cinst) result;

    (*import assumes/defines*)
    val assm_tac = FIRST' (map (fn assm => Tactic.compose_tac (false, assm, 0)) assms);
    val result'' =
      (case SINGLE (Seq.INTERVAL assm_tac 1 nprems) result' of
        NONE => raise THM ("Failed to re-import result", 0, [result'])
      | SOME res => Local_Defs.contract ctxt defs (Thm.cprop_of th) res)
      |> Goal.norm_result
      |> PureThy.name_thm false false name;

  in (result'', result) end;

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
    val local_facts' = Element.facts_map (Element.morph_ctxt (Local_Theory.target_morphism lthy)) local_facts;
  in
    lthy
    |> Local_Theory.theory (PureThy.note_thmss kind global_facts' #> snd)
    |> Local_Theory.target (Locale.add_thmss locale kind local_facts')
  end

fun notes (Target {target, is_locale, ...}) kind facts lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val facts' = facts
      |> map (fn (a, bs) => (a, PureThy.burrow_fact (PureThy.name_multi
          (Local_Theory.full_name lthy (fst a))) bs))
      |> PureThy.map_facts (import_export_proof lthy);
    val local_facts = PureThy.map_facts #1 facts';
    val global_facts = PureThy.map_facts #2 facts';
  in
    lthy
    |> (if is_locale then locale_notes target kind global_facts local_facts
        else theory_notes kind global_facts)
    |> ProofContext.note_thmss kind (Attrib.map_facts (Attrib.attribute_i thy) local_facts)
  end;


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
            (Context.mapping (Sign.revert_abbrev mode d) (ProofContext.revert_abbrev mode d) #>
             Morphism.form (ProofContext.target_notation true prmode [(lhs', mx)]))))
  end;


(* mixfix notation *)

local

fun fork_mixfix (Target {is_locale, is_class, ...}) mx =
  if not is_locale then (NoSyn, NoSyn, mx)
  else if not is_class then (NoSyn, mx, NoSyn)
  else (mx, NoSyn, NoSyn);

in

fun prep_mixfix ctxt ta (b, extra_tfrees) mx =
  let
    val mx' =
      if null extra_tfrees then mx
      else
        (warning
          ("Additional type variable(s) in specification of " ^ Binding.str_of b ^ ": " ^
            commas (map (Syntax.string_of_typ ctxt o TFree) (sort_wrt #1 extra_tfrees)) ^
            (if mx = NoSyn then ""
             else "\nDropping mixfix syntax " ^ Pretty.string_of (Syntax.pretty_mixfix mx)));
          NoSyn);
  in fork_mixfix ta mx' end;

end;


(* abbrev *)

fun theory_abbrev prmode ((b, mx), t) = Local_Theory.theory
  (Sign.add_abbrev (#1 prmode) (b, t) #-> (fn (lhs, _) => Sign.notation true prmode [(lhs, mx)]));

fun locale_abbrev ta prmode ((b, mx), t) xs = Local_Theory.theory_result
  (Sign.add_abbrev Print_Mode.internal (b, t)) #-> (fn (lhs, _) =>
    syntax_declaration ta false (locale_const ta prmode ((b, mx), Term.list_comb (Logic.unvarify_global lhs, xs))));

fun abbrev (ta as Target {target, is_locale, is_class, ...}) prmode ((b, mx), t) lthy =
  let
    val thy_ctxt = ProofContext.init_global (ProofContext.theory_of lthy);
    val target_ctxt = Local_Theory.target_of lthy;

    val t' = Assumption.export_term lthy target_ctxt t;
    val xs = map Free (rev (Variable.add_fixed target_ctxt t' []));
    val u = fold_rev lambda xs t';

    val extra_tfrees =
      subtract (op =) (Term.add_tfreesT (Term.fastype_of u) []) (Term.add_tfrees u []);
    val (mx1, mx2, mx3) = prep_mixfix lthy ta (b, extra_tfrees) mx;

    val global_rhs =
      singleton (Variable.export_terms (Variable.declare_term u target_ctxt) thy_ctxt) u;
  in
    lthy |>
     (if is_locale then locale_abbrev ta prmode ((b, mx2), global_rhs) xs #>
        is_class ? class_target ta (Class_Target.abbrev target prmode ((b, mx1), t'))
      else theory_abbrev prmode ((b, mx3), global_rhs))
    |> ProofContext.add_abbrev Print_Mode.internal (b, t) |> snd
    |> Local_Defs.fixed_abbrev ((b, NoSyn), t)
  end;


(* define *)

local

fun syntax_error c = error ("Illegal mixfix syntax for overloaded constant " ^ quote c);

fun foundation (ta as Target {target, is_locale, is_class, ...})
    (((b, U), mx), rhs') name' params (extra_tfrees, type_params) lthy =
  let
    val (mx1, mx2, mx3) = prep_mixfix lthy ta (b, extra_tfrees) mx;
    val (const, lthy2) = lthy |>
      (case Class_Target.instantiation_param lthy b of
        SOME c' =>
          if mx3 <> NoSyn then syntax_error c'
          else Local_Theory.theory_result (AxClass.declare_overloaded (c', U))
            ##> Class_Target.confirm_declaration b
      | NONE =>
          (case Overloading.operation lthy b of
            SOME (c', _) =>
              if mx3 <> NoSyn then syntax_error c'
              else Local_Theory.theory_result (Overloading.declare (c', U))
                ##> Overloading.confirm b
          | NONE => Local_Theory.theory_result (Sign.declare_const ((b, U), mx3))));
    val Const (head, _) = const;
    val lhs' = list_comb (const, params);
  in
    lthy2
    |> pair lhs'
    ||>> Local_Theory.theory_result
      (case Overloading.operation lthy b of
        SOME (_, checked) => Overloading.define checked name' (head, rhs')
      | NONE =>
          if is_some (Class_Target.instantiation_param lthy b)
          then AxClass.define_overloaded name' (head, rhs')
          else Thm.add_def false false (name', Logic.mk_equals (lhs', rhs')) #>> snd)
    ||> is_locale ? syntax_declaration ta false (locale_const ta Syntax.mode_default ((b, mx2), lhs'))
    ||> is_class ? class_target ta (Class_Target.declare target ((b, mx1), (type_params, lhs')))
  end;

in

fun define ta ((b, mx), ((name, atts), rhs)) lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val thy_ctxt = ProofContext.init_global thy;

    val name' = Thm.def_binding_optional b name;

    (*term and type parameters*)
    val crhs = Thm.cterm_of thy rhs;
    val (defs, rhs') = Local_Defs.export_cterm lthy thy_ctxt crhs ||> Thm.term_of;
    val rhs_conv = MetaSimplifier.rewrite true defs crhs;

    val xs = Variable.add_fixed (Local_Theory.target_of lthy) rhs' [];
    val T = Term.fastype_of rhs;
    val tfreesT = Term.add_tfreesT T (fold (Term.add_tfreesT o #2) xs []);
    val extra_tfrees = rev (subtract (op =) tfreesT (Term.add_tfrees rhs []));

    val type_params = map (Logic.mk_type o TFree) extra_tfrees;
    val term_params =
      rev (Variable.fixes_of (Local_Theory.target_of lthy))
      |> map_filter (fn (_, x) =>
        (case AList.lookup (op =) xs x of
          SOME T => SOME (Free (x, T))
        | NONE => NONE));
    val params = type_params @ term_params;

    val U = map Term.fastype_of params ---> T;

    (*foundation*)
    val ((lhs', global_def), lthy3) = foundation ta
      (((b, U), mx), rhs') name' params (extra_tfrees, type_params) lthy;

    (*local definition*)
    val ((lhs, local_def), lthy4) = lthy3
      |> Local_Defs.add_def ((b, NoSyn), lhs');
    val def = Local_Defs.trans_terms lthy4
      [(*c == global.c xs*)     local_def,
       (*global.c xs == rhs'*)  global_def,
       (*rhs' == rhs*)          Thm.symmetric rhs_conv];

    (*note*)
    val ([(res_name, [res])], lthy5) = lthy4
      |> Local_Theory.notes_kind "" [((name', atts), [([def], [])])];
  in ((lhs, (res_name, res)), lthy5) end;

end;


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
     {pretty = pretty ta,
      abbrev = abbrev ta,
      define = define ta,
      notes = notes ta,
      declaration = declaration ta,
      syntax_declaration = syntax_declaration ta,
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
fun instantiation_cmd arities thy = instantiation (Class_Target.read_multi_arity thy arities) thy;

val overloading = gen_overloading (fn ctxt => Syntax.check_term ctxt o Const);
val overloading_cmd = gen_overloading Syntax.read_term;

end;

end;

