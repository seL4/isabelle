(*  Title:      Pure/Isar/theory_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Common theory/locale/class/instantiation/overloading targets.
*)

signature THEORY_TARGET =
sig
  val peek: local_theory -> {target: string, is_locale: bool,
    is_class: bool, instantiation: string list * (string * sort) list * sort,
    overloading: (string * (string * typ) * bool) list}
  val init: string option -> theory -> local_theory
  val begin: string -> Proof.context -> local_theory
  val context: xstring -> theory -> local_theory
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
    val target_name = (if is_class then "class " else "locale ") ^ Locale.extern thy target;
    val fixes =
      map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) (#1 (ProofContext.inferred_fixes ctxt));
    val assumes =
      map (fn A => (Attrib.empty_binding, [(Thm.term_of A, [])])) (Assumption.all_assms_of ctxt);
    val elems =
      (if null fixes then [] else [Element.Fixes fixes]) @
      (if null assumes then [] else [Element.Assumes assumes]);
  in
    if target = "" then []
    else if null elems then [Pretty.str target_name]
    else [Pretty.big_list (target_name ^ " =")
      (map (Pretty.chunks o Element.pretty_ctxt ctxt) elems)]
  end;

fun pretty (Target {target, is_class, instantiation, overloading, ...}) ctxt =
  Pretty.block [Pretty.str "theory", Pretty.brk 1,
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
      |> direct_decl target_decl
    else
      lthy
      |> pervasive ? direct_decl global_decl
      |> Local_Theory.target (add target target_decl)
  end;

in

val type_syntax = target_decl Locale.add_type_syntax;
val term_syntax = target_decl Locale.add_term_syntax;
val declaration = target_decl Locale.add_declaration;

end;

fun class_target (Target {target, ...}) f =
  Local_Theory.raw_theory f #>
  Local_Theory.target (Class_Target.refresh_syntax target);


(* notes *)

fun import_export_proof ctxt (name, raw_th) =
  let
    val thy = ProofContext.theory_of ctxt;
    val thy_ctxt = ProofContext.init thy;
    val certT = Thm.ctyp_of thy;
    val cert = Thm.cterm_of thy;

    (*export assumes/defines*)
    val th = Goal.norm_result raw_th;
    val (defs, th') = LocalDefs.export ctxt thy_ctxt th;
    val concl_conv = MetaSimplifier.rewrite true defs (Thm.cprop_of th);
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
      | SOME res => LocalDefs.trans_props ctxt [res, Thm.symmetric concl_conv])
      |> Goal.norm_result
      |> PureThy.name_thm false false name;

  in (result'', result) end;

fun notes (Target {target, is_locale, ...}) kind facts lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val facts' = facts
      |> map (fn (a, bs) => (a, PureThy.burrow_fact (PureThy.name_multi
          (Local_Theory.full_name lthy (fst a))) bs))
      |> PureThy.map_facts (import_export_proof lthy);
    val local_facts = PureThy.map_facts #1 facts'
      |> Attrib.map_facts (Attrib.attribute_i thy);
    val target_facts = PureThy.map_facts #1 facts'
      |> is_locale ? Element.facts_map (Element.morph_ctxt (Local_Theory.target_morphism lthy));
    val global_facts = PureThy.map_facts #2 facts'
      |> Attrib.map_facts (if is_locale then K I else Attrib.attribute_i thy);
  in
    lthy
    |> Local_Theory.theory (PureThy.note_thmss kind global_facts #> snd)
    |> not is_locale ? Local_Theory.target (ProofContext.note_thmss kind global_facts #> snd)
    |> is_locale ? Local_Theory.target (Locale.add_thmss target kind target_facts)
    |> ProofContext.note_thmss kind local_facts
  end;


(* declare_const *)

fun fork_mixfix (Target {is_locale, is_class, ...}) mx =
  if not is_locale then (NoSyn, NoSyn, mx)
  else if not is_class then (NoSyn, mx, NoSyn)
  else (mx, NoSyn, NoSyn);

fun locale_const (Target {target, is_class, ...}) (prmode as (mode, _)) ((b, mx), rhs) phi =
  let
    val b' = Morphism.binding phi b;
    val rhs' = Morphism.term phi rhs;
    val arg = (b', Term.close_schematic_term rhs');
    val same_shape = Term.aconv_untyped (rhs, rhs');
    (* FIXME workaround based on educated guess *)
    val prefix' = Binding.prefix_of b';
    val class_global =
      Binding.eq_name (b, b') andalso
      not (null prefix') andalso
      fst (snd (split_last prefix')) = Class_Target.class_prefix target;
  in
    not (is_class andalso (same_shape orelse class_global)) ?
      (Context.mapping_result
        (Sign.add_abbrev PrintMode.internal arg)
        (ProofContext.add_abbrev PrintMode.internal arg)
      #-> (fn (lhs' as Const (d, _), _) =>
          same_shape ?
            (Context.mapping (Sign.revert_abbrev mode d) (ProofContext.revert_abbrev mode d) #>
             Morphism.form (ProofContext.target_notation true prmode [(lhs', mx)]))))
  end;

fun syntax_error c = error ("Illegal mixfix syntax for overloaded constant " ^ quote c);

fun declare_const (ta as Target {target, is_locale, is_class, ...}) depends ((b, T), mx) lthy =
  let
    val xs = filter depends (#1 (ProofContext.inferred_fixes (Local_Theory.target_of lthy)));
    val U = map #2 xs ---> T;
    val (mx1, mx2, mx3) = fork_mixfix ta mx;
    val (const, lthy') = lthy |>
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
    val t = Term.list_comb (const, map Free xs);
  in
    lthy'
    |> is_locale ? term_syntax ta false (locale_const ta Syntax.mode_default ((b, mx2), t))
    |> is_class ? class_target ta (Class_Target.declare target ((b, mx1), t))
    |> LocalDefs.add_def ((b, NoSyn), t)
  end;


(* abbrev *)

fun abbrev (ta as Target {target, is_locale, is_class, ...}) prmode ((b, mx), t) lthy =
  let
    val thy_ctxt = ProofContext.init (ProofContext.theory_of lthy);
    val target_ctxt = Local_Theory.target_of lthy;

    val (mx1, mx2, mx3) = fork_mixfix ta mx;
    val t' = Assumption.export_term lthy target_ctxt t;
    val xs = map Free (rev (Variable.add_fixed target_ctxt t' []));
    val u = fold_rev lambda xs t';
    val global_rhs =
      singleton (Variable.export_terms (Variable.declare_term u target_ctxt) thy_ctxt) u;
  in
    lthy |>
     (if is_locale then
        Local_Theory.theory_result (Sign.add_abbrev PrintMode.internal (b, global_rhs))
        #-> (fn (lhs, _) =>
          let val lhs' = Term.list_comb (Logic.unvarify lhs, xs) in
            term_syntax ta false (locale_const ta prmode ((b, mx2), lhs')) #>
            is_class ? class_target ta (Class_Target.abbrev target prmode ((b, mx1), t'))
          end)
      else
        Local_Theory.theory
          (Sign.add_abbrev (#1 prmode) (b, global_rhs) #-> (fn (lhs, _) =>
           Sign.notation true prmode [(lhs, mx3)])))
    |> ProofContext.add_abbrev PrintMode.internal (b, t) |> snd
    |> LocalDefs.fixed_abbrev ((b, NoSyn), t)
  end;


(* define *)

fun define ta kind ((b, mx), ((name, atts), rhs)) lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val thy_ctxt = ProofContext.init thy;

    val name' = Thm.def_binding_optional b name;
    val (rhs', rhs_conv) =
      LocalDefs.export_cterm lthy thy_ctxt (Thm.cterm_of thy rhs) |>> Thm.term_of;
    val xs = Variable.add_fixed (Local_Theory.target_of lthy) rhs' [];
    val T = Term.fastype_of rhs;

    (*const*)
    val ((lhs, local_def), lthy2) = lthy |> declare_const ta (member (op =) xs) ((b, T), mx);
    val (_, lhs') = Logic.dest_equals (Thm.prop_of local_def);

    (*def*)
    val (global_def, lthy3) = lthy2
      |> Local_Theory.theory_result
        (case Overloading.operation lthy b of
          SOME (_, checked) => Overloading.define checked name' (fst (dest_Const lhs'), rhs')
        | NONE =>
            if is_none (Class_Target.instantiation_param lthy b)
            then Thm.add_def false false (name', Logic.mk_equals (lhs', rhs'))
            else AxClass.define_overloaded name' (fst (dest_Const lhs'), rhs'));
    val def = LocalDefs.trans_terms lthy3
      [(*c == global.c xs*)     local_def,
       (*global.c xs == rhs'*)  global_def,
       (*rhs' == rhs*)          Thm.symmetric rhs_conv];

    (*note*)
    val ([(res_name, [res])], lthy4) = lthy3
      |> notes ta kind [((name', atts), [([def], [])])];
  in ((lhs, (res_name, res)), lthy4) end;


(* init *)

local

fun init_target _ NONE = global_target
  | init_target thy (SOME target) =
      if Locale.defined thy (Locale.intern thy target)
      then make_target target true (Class_Target.is_class thy target) ([], [], []) []
      else error ("No such locale: " ^ quote target);

fun init_ctxt (Target {target, is_locale, is_class, instantiation, overloading}) =
  if not (null (#1 instantiation)) then Class_Target.init_instantiation instantiation
  else if not (null overloading) then Overloading.init overloading
  else if not is_locale then ProofContext.init
  else if not is_class then Locale.init target
  else Class_Target.init target;

fun init_lthy (ta as Target {target, instantiation, overloading, ...}) =
  Data.put ta #>
  Local_Theory.init (Long_Name.base_name target)
   {pretty = pretty ta,
    abbrev = abbrev ta,
    define = define ta,
    notes = notes ta,
    type_syntax = type_syntax ta,
    term_syntax = term_syntax ta,
    declaration = declaration ta,
    reinit = fn lthy => init_lthy_ctxt ta (ProofContext.theory_of lthy),
    exit = Local_Theory.target_of o
      (if not (null (#1 instantiation)) then Class_Target.conclude_instantiation
       else if not (null overloading) then Overloading.conclude
       else I)}
and init_lthy_ctxt ta = init_lthy ta o init_ctxt ta;

fun gen_overloading prep_const raw_ops thy =
  let
    val ctxt = ProofContext.init thy;
    val ops = raw_ops |> map (fn (name, const, checked) =>
      (name, Term.dest_Const (prep_const ctxt const), checked));
  in thy |> init_lthy_ctxt (make_target "" false false ([], [], []) ops) end;

in

fun init target thy = init_lthy_ctxt (init_target thy target) thy;
fun begin target ctxt = init_lthy (init_target (ProofContext.theory_of ctxt) (SOME target)) ctxt;

fun context "-" thy = init NONE thy
  | context target thy = init (SOME (Locale.intern thy target)) thy;


(* other targets *)

fun instantiation arities = init_lthy_ctxt (make_target "" false false arities []);
fun instantiation_cmd raw_arities thy =
  instantiation (Class_Target.read_multi_arity thy raw_arities) thy;

val overloading = gen_overloading (fn ctxt => Syntax.check_term ctxt o Const);
val overloading_cmd = gen_overloading Syntax.read_term;

end;

end;

