(*  Title:      Pure/Isar/generic_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Common target infrastructure.
*)

signature GENERIC_TARGET =
sig
  (*auxiliary*)
  val export_abbrev: Proof.context ->
      (term -> term) -> term -> term * ((string * sort) list * (term list * term list))
  val check_mixfix: Proof.context -> binding * (string * sort) list -> mixfix -> mixfix
  val check_mixfix_global: binding * bool -> mixfix -> mixfix

  (*background primitives*)
  val background_foundation: ((binding * typ) * mixfix) * (binding * term) ->
    term list * term list -> local_theory -> (term * thm) * local_theory
  val background_declaration: Morphism.declaration_entity -> local_theory -> local_theory
  val background_abbrev: binding * term -> term list -> local_theory -> (term * term) * local_theory
  val add_foundation_interpretation: (binding * (term * term list) -> Context.generic -> Context.generic) ->
    theory -> theory

  (*nested local theories primitives*)
  val standard_facts: local_theory -> Proof.context -> Attrib.fact list -> Attrib.fact list
  val standard_notes: (int * int -> bool) -> string -> Attrib.fact list ->
    local_theory -> local_theory
  val standard_declaration: (int * int -> bool) -> Morphism.declaration_entity ->
    local_theory -> local_theory
  val standard_const: (int * int -> bool) -> Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> local_theory
  val local_interpretation: Locale.registration ->
    local_theory -> local_theory

  (*lifting target primitives to local theory operations*)
  val define: (((binding * typ) * mixfix) * (binding * term) ->
      term list * term list -> local_theory -> (term * thm) * local_theory) ->
    bool -> (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory
  val notes:
    (string -> Attrib.fact list -> Attrib.fact list -> local_theory -> local_theory) ->
    string -> Attrib.fact list -> local_theory -> (string * thm list) list * local_theory
  val abbrev: (Syntax.mode -> binding * mixfix -> term ->
      term list * term list -> local_theory -> local_theory) ->
    Syntax.mode -> (binding * mixfix) * term -> local_theory -> (term * term) * local_theory

  (*theory target primitives*)
  val theory_target_foundation: ((binding * typ) * mixfix) * (binding * term) ->
     term list * term list -> local_theory -> (term * thm) * local_theory
  val theory_target_notes: string -> Attrib.fact list -> Attrib.fact list ->
    local_theory -> local_theory
  val theory_target_abbrev: Syntax.mode -> (binding * mixfix) -> term -> term list * term list ->
    local_theory -> local_theory

  (*theory target operations*)
  val theory_abbrev: Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> (term * term) * local_theory
  val theory_declaration: Morphism.declaration_entity -> local_theory -> local_theory
  val theory_registration: Locale.registration -> local_theory -> local_theory

  (*locale target primitives*)
  val locale_target_notes: string -> string -> Attrib.fact list -> Attrib.fact list ->
    local_theory -> local_theory
  val locale_target_abbrev: string -> Syntax.mode ->
    (binding * mixfix) -> term -> term list * term list -> local_theory -> local_theory
  val locale_target_declaration: string -> {syntax: bool, pos: Position.T} ->
    Morphism.declaration_entity -> local_theory -> local_theory
  val locale_target_const: string -> (morphism -> bool) -> Syntax.mode ->
    (binding * mixfix) * term -> local_theory -> local_theory

  (*locale operations*)
  val locale_abbrev: string -> Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> (term * term) * local_theory
  val locale_declaration: string -> {syntax: bool, pervasive: bool, pos: Position.T} ->
    Morphism.declaration_entity -> local_theory -> local_theory
  val locale_const: string -> Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> local_theory
  val locale_dependency: string -> Locale.registration ->
    local_theory -> local_theory
end

structure Generic_Target: GENERIC_TARGET =
struct

(** consts **)

fun export_abbrev lthy preprocess rhs =
  let
    val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);

    val rhs' = rhs
      |> Assumption.export_term lthy (Local_Theory.target_of lthy)
      |> preprocess;
    val term_params =
      map Free (sort (Variable.fixed_ord lthy o apply2 #1) (Variable.add_fixed lthy rhs' []));
    val u = fold_rev lambda term_params rhs';
    val global_rhs = singleton (Variable.polymorphic thy_ctxt) u;

    val type_tfrees = TFrees.build (TFrees.add_tfreesT (Term.fastype_of u));
    val extra_tfrees =
      TFrees.build (TFrees.add_tfrees_unless (TFrees.defined type_tfrees) u)
      |> TFrees.keys;
    val type_params = map (Logic.mk_type o TFree) extra_tfrees;
  in (global_rhs, (extra_tfrees, (type_params, term_params))) end;

fun check_mixfix ctxt (b, extra_tfrees) mx =
  if null extra_tfrees then mx
  else
   (if Context_Position.is_visible ctxt then
      warning
        ("Additional type variable(s) in specification of " ^ Binding.print b ^ ": " ^
          commas (map (Syntax.string_of_typ ctxt o TFree) extra_tfrees) ^
          (if Mixfix.is_empty mx then ""
           else "\nDropping mixfix syntax " ^ Pretty.string_of (Mixfix.pretty_mixfix mx)))
    else (); NoSyn);

fun check_mixfix_global (b, no_params) mx =
  if no_params orelse Mixfix.is_empty mx then mx
  else
    (warning ("Dropping global mixfix syntax: " ^ Binding.print b ^ " " ^
      Pretty.string_of (Mixfix.pretty_mixfix mx)); NoSyn);

fun same_const (Const (c, _), Const (c', _)) = c = c'
  | same_const (t $ _, t' $ _) = same_const (t, t')
  | same_const _ = false;

fun const_decl phi_pred prmode ((b, mx), rhs) = Morphism.entity (fn phi => fn context =>
  if phi_pred phi then
    let
      val b' = Morphism.binding phi b;
      val rhs' = Morphism.term phi rhs;
      val same_shape = Term.aconv_untyped (rhs, rhs');
      val same_stem = same_shape orelse same_const (rhs, rhs');
      val const_alias =
        if same_shape then
          (case rhs' of
            Const (c, T) =>
              let
                val thy = Context.theory_of context;
                val ctxt = Context.proof_of context;
              in
                (case Type_Infer_Context.const_type ctxt c of
                  SOME T' => if Sign.typ_equiv thy (T, T') then SOME c else NONE
                | NONE => NONE)
              end
          | _ => NONE)
        else NONE;
    in
      (case const_alias of
        SOME c =>
          context
          |> Context.mapping (Sign.const_alias b' c) (Proof_Context.const_alias b' c)
          |> Morphism.form_entity (Proof_Context.generic_notation true prmode [(rhs', mx)])
      | NONE =>
          context
          |> Proof_Context.generic_add_abbrev Print_Mode.internal
            (b', Term.close_schematic_term rhs')
          |-> (fn (const as Const (c, _), _) => same_stem ?
                (Proof_Context.generic_revert_abbrev (#1 prmode) c #>
                 same_shape ?
                  Morphism.form_entity (Proof_Context.generic_notation true prmode [(const, mx)]))))
    end
  else context);



(** background primitives **)

structure Foundation_Interpretations = Theory_Data
(
  type T = ((binding * (term * term list) -> Context.generic -> Context.generic) * stamp) list
  val empty = [];
  val merge = Library.merge (eq_snd (op =));
);

fun add_foundation_interpretation f =
  Foundation_Interpretations.map (cons (f, stamp ()));

fun foundation_interpretation binding_const_params lthy =
  let
    val interps = Foundation_Interpretations.get (Proof_Context.theory_of lthy);
    val interp = fold (fn (f, _) => f binding_const_params) interps;
  in
    lthy
    |> Local_Theory.background_theory (Context.theory_map interp)
    |> Local_Theory.map_contexts (K (Context.proof_map interp))
  end;

fun background_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params) lthy =
  let
    val params = type_params @ term_params;
    val target_params = type_params
      @ take_prefix is_Free (Variable.export_terms lthy (Local_Theory.target_of lthy) term_params);
    val mx' = check_mixfix_global (b, null params) mx;

    val (const, lthy2) = lthy
      |> Local_Theory.background_theory_result (Sign.declare_const lthy ((b, U), mx'));
    val lhs = Term.list_comb (const, params);

    val ((_, def), lthy3) = lthy2
      |> Local_Theory.background_theory_result
        (Thm.add_def (Proof_Context.defs_context lthy2) false false
          (Thm.def_binding_optional b b_def, Logic.mk_equals (lhs, rhs)))
      ||> foundation_interpretation (b, (const, target_params));
  in ((lhs, def), lthy3) end;

fun background_declaration decl lthy =
  let
    fun theory_decl context =
      Local_Theory.standard_form lthy
        (Proof_Context.init_global (Context.theory_of context)) decl context;
  in Local_Theory.background_theory (Context.theory_map theory_decl) lthy end;

fun background_abbrev (b, global_rhs) params =
  Local_Theory.background_theory_result (Sign.add_abbrev Print_Mode.internal (b, global_rhs))
  #>> apply2 (fn t => Term.list_comb (Logic.unvarify_global t, params))



(** nested local theories primitives **)

fun standard_facts lthy ctxt =
  Attrib.transform_facts (Local_Theory.standard_morphism lthy ctxt);

fun standard_notes pred kind facts lthy =
  Local_Theory.map_contexts (fn level => fn ctxt =>
    if pred (Local_Theory.level lthy, level)
    then Attrib.local_notes kind (standard_facts lthy ctxt facts) ctxt |> snd
    else ctxt) lthy;

fun standard_declaration pred decl lthy =
  Local_Theory.map_contexts (fn level => fn ctxt =>
    if pred (Local_Theory.level lthy, level)
    then Context.proof_map (Local_Theory.standard_form lthy ctxt decl) ctxt
    else ctxt) lthy;

fun standard_const pred prmode ((b, mx), rhs) =
  standard_declaration pred (const_decl (K true) prmode ((b, mx), rhs));

fun standard_registration pred registration lthy =
  Local_Theory.map_contexts (fn level =>
    if pred (Local_Theory.level lthy, level)
    then Context.proof_map (Locale.add_registration registration)
    else I) lthy;

val local_interpretation = standard_registration (fn (n, level) => level >= n - 1);



(** lifting target primitives to local theory operations **)

(* define *)

fun define foundation internal ((b, mx), ((b_def, atts), rhs)) lthy =
  let
    val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);

    (*term and type parameters*)
    val ((defs, _), rhs') = Thm.cterm_of lthy rhs
      |> Local_Defs.export_cterm lthy thy_ctxt ||> Thm.term_of;

    val xs = Variable.add_fixed lthy rhs' [];
    val T = Term.fastype_of rhs;
    val type_tfrees = TFrees.build (TFrees.add_tfreesT T #> fold (TFrees.add_tfreesT o #2) xs);
    val extra_tfrees =
      TFrees.build (rhs |> TFrees.add_tfrees_unless (TFrees.defined type_tfrees))
      |> TFrees.keys;
    val mx' = check_mixfix lthy (b, extra_tfrees) mx;

    val type_params = map (Logic.mk_type o TFree) extra_tfrees;
    val term_params = map Free (sort (Variable.fixed_ord lthy o apply2 #1) xs);
    val params = type_params @ term_params;

    val U = map Term.fastype_of params ---> T;

    (*foundation*)
    val ((lhs', global_def), lthy2) = lthy
      |> foundation (((b, U), mx'), (b_def, rhs')) (type_params, term_params);

    (*local definition*)
    val ([(lhs, (_, local_def))], lthy3) = lthy2
      |> Context_Position.set_visible false
      |> Local_Defs.define [((b, NoSyn), (Binding.empty_atts, lhs'))]
      ||> Context_Position.restore_visible lthy2;

    (*result*)
    val def =
      Thm.transitive local_def global_def
      |> Local_Defs.contract lthy3 defs (Thm.cterm_of lthy3 (Logic.mk_equals (lhs, rhs)));
    val ([(res_name, [res])], lthy4) = lthy3
      |> Local_Theory.notes [((if internal then Binding.empty else b_def, atts), [([def], [])])];
  in ((lhs, (res_name, res)), lthy4) end;


(* notes *)

local

val name_thm1 = Global_Theory.name_thm Global_Theory.official1;
val name_thm2 = Global_Theory.name_thm Global_Theory.unofficial2;

fun thm_def (name, pos) thm lthy =
  if #1 name <> "" andalso Proofterm.zproof_enabled (Proofterm.get_proofs_level ()) then
    Local_Theory.background_theory_result (Thm.store_zproof (name, pos) thm) lthy
  else (thm, lthy);

fun thm_definition (name_pos, thm) lthy =
  let
    val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);

    (*export assumes/defines*)
    val ((defs, asms), thm') = Local_Defs.export lthy thy_ctxt thm;
    val asms' = map (rewrite_rule lthy (Drule.norm_hhf_eqs @ defs)) asms;

    (*export fixes*)
    val tfrees =
      TFrees.build (Thm.fold_terms {hyps = true} TFrees.add_tfrees thm')
      |> TFrees.keys |> map TFree;
    val frees =
      Frees.build (Thm.fold_terms {hyps = true} Frees.add_frees thm')
      |> Frees.list_set_rev |> map Free;
    val (schematic_thm :: variables) =
      (thm' :: map (Drule.mk_term o Thm.cterm_of lthy) (map Logic.mk_type tfrees @ frees))
      |> Variable.export lthy thy_ctxt
      |> Drule.zero_var_indexes_list;

    (*thm definition*)
    val (global_thm, lthy') = thm_def name_pos (name_thm1 name_pos schematic_thm) lthy;

    (*import fixes*)
    val (tvars, vars) =
      chop (length tfrees) (map (Thm.term_of o Drule.dest_term) variables)
      |>> map Logic.dest_type;

    val instT =
      TVars.build (fold2 (fn a => fn b =>
        (case a of TVar v => TVars.add (v, b) | _ => I)) tvars tfrees);
    val cinstT = TVars.map (K (Thm.ctyp_of lthy')) instT;
    val cinst =
      Vars.build
        (fold2 (fn v => fn t =>
          (case v of
            Var (xi, T) =>
              Vars.add ((xi, Term_Subst.instantiateT instT T),
                Thm.cterm_of lthy' (Term.map_types (Term_Subst.instantiateT_same instT) t))
          | _ => I)) vars frees);
    val fixed_thm = Thm.instantiate (cinstT, cinst) global_thm;

    (*import assumes/defines*)
    val local_thm =
      (fold (curry op COMP) asms' fixed_thm
        handle THM _ => raise THM ("Failed to re-import result", 0, fixed_thm :: asms'))
      |> Local_Defs.contract lthy defs (Thm.cprop_of thm)
      |> Goal.norm_result lthy
      |> name_thm2 name_pos;

  in ((local_thm, global_thm), lthy') end;

in

fun notes target_notes kind facts0 lthy =
  let
    val facts = Attrib.map_thms (Goal.norm_result lthy) facts0;
    val (facts', lthy') =
      (facts, lthy) |-> fold_map (fn (a, thms) => fn lthy1 =>
        let
          val thms1 = Thm_Name.expr (Local_Theory.full_name_pos lthy1 (fst a)) thms;
          val (thms2, lthy2) =
            (thms1, lthy1) |-> fold_map (fn (args, atts) =>
              fold_map thm_definition args #>> rpair atts);
        in ((a, thms2), lthy2) end);
    val local_facts = Attrib.map_thms #1 facts';
    val global_facts = Attrib.map_thms #2 facts';
  in
    lthy'
    |> target_notes kind global_facts (Attrib.partial_evaluation lthy' local_facts)
    |> Attrib.local_notes kind local_facts
  end;

end;


(* abbrev *)

fun abbrev target_abbrev prmode ((b, mx), rhs) lthy =
  let
    val (global_rhs, (extra_tfrees, (type_params, term_params))) = export_abbrev lthy I rhs;
    val mx' = check_mixfix lthy (b, extra_tfrees) mx;
  in
    lthy
    |> target_abbrev prmode (b, mx') global_rhs (type_params, term_params)
    |> Context_Position.set_visible false
    |> Proof_Context.add_abbrev Print_Mode.internal (b, rhs) |> snd
    |> Local_Defs.fixed_abbrev ((b, NoSyn), rhs)
    ||> Context_Position.restore_visible lthy
  end;



(** theory target primitives **)

fun theory_target_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params) =
  background_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params)
  #-> (fn (lhs, def) => standard_const (op <>) Syntax.mode_default ((b, mx), lhs)
    #> pair (lhs, def));

fun theory_target_notes kind global_facts local_facts =
  Local_Theory.background_theory (Attrib.global_notes kind global_facts #> snd)
  #> standard_notes (op <>) kind local_facts;

fun theory_target_abbrev prmode (b, mx) global_rhs params =
  Local_Theory.background_theory_result
    (Sign.add_abbrev (#1 prmode) (b, global_rhs) #->
      (fn (lhs, _) =>  (* FIXME type_params!? *)
        Sign.notation_global true prmode
          [(lhs, check_mixfix_global (b, null (snd params)) mx)] #> pair lhs))
  #-> (fn lhs =>
        standard_const (op <>) prmode
          ((b, if null (snd params) then NoSyn else mx),
            Term.list_comb (Logic.unvarify_global lhs, snd params)));



(** theory operations **)

val theory_abbrev = abbrev theory_target_abbrev;

fun theory_declaration decl =
  background_declaration decl #> standard_declaration (K true) decl;

fun target_registration lthy {inst, mixin, export} =
  {inst = inst, mixin = mixin,
    export = export $> Proof_Context.export_morphism lthy (Local_Theory.target_of lthy)};

fun theory_registration registration lthy =
  lthy
  |> (Local_Theory.raw_theory o Context.theory_map)
    (Locale.add_registration (target_registration lthy registration))
  |> standard_registration (K true) registration;



(** locale target primitives **)

fun locale_target_notes locale kind global_facts local_facts =
  Local_Theory.background_theory
    (Attrib.global_notes kind (Attrib.map_facts (K []) global_facts) #> snd) #>
  (fn lthy => lthy |>
    Local_Theory.target (fn ctxt => ctxt |>
      Locale.add_facts locale kind (standard_facts lthy ctxt local_facts))) #>
  standard_notes (fn (this, other) => other <> 0 andalso this <> other) kind local_facts;

fun locale_target_declaration locale params decl lthy = lthy
  |> Local_Theory.target (fn ctxt => ctxt |>
    Locale.add_declaration locale params
      (Morphism.transform (Local_Theory.standard_morphism lthy ctxt) decl));

fun locale_target_const locale phi_pred prmode ((b, mx), rhs) =
  locale_target_declaration locale {syntax = true, pos = Binding.pos_of b}
    (const_decl phi_pred prmode ((b, mx), rhs));


(** locale operations **)

fun locale_declaration locale {syntax, pervasive, pos} decl =
  pervasive ? background_declaration decl
  #> locale_target_declaration locale {syntax = syntax, pos = pos} decl
  #> standard_declaration (fn (_, other) => other <> 0) decl;

fun locale_const locale prmode ((b, mx), rhs) =
  locale_target_const locale (K true) prmode ((b, mx), rhs)
  #> standard_const (fn (this, other) => other <> 0 andalso this <> other) prmode ((b, mx), rhs);

fun locale_dependency loc registration lthy =
  lthy
  |> Local_Theory.raw_theory (Locale.add_dependency loc registration)
  |> standard_registration (K true) registration;


(** locale abbreviations **)

fun locale_target_abbrev locale prmode (b, mx) global_rhs params =
  background_abbrev (b, global_rhs) (snd params)
  #-> (fn (lhs, _) => locale_const locale prmode ((b, mx), lhs));

fun locale_abbrev locale = abbrev (locale_target_abbrev locale);

end;
