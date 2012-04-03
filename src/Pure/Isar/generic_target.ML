(*  Title:      Pure/Isar/generic_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Common target infrastructure.
*)

signature GENERIC_TARGET =
sig
  val define: (((binding * typ) * mixfix) * (binding * term) ->
      term list * term list -> local_theory -> (term * thm) * local_theory) ->
    bool -> (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory
  val notes:
    (string -> (Attrib.binding * (thm list * Args.src list) list) list ->
      (Attrib.binding * (thm list * Args.src list) list) list -> local_theory -> local_theory) ->
    string -> (Attrib.binding * (thm list * Args.src list) list) list -> local_theory ->
    (string * thm list) list * local_theory
  val locale_notes: string -> string ->
    (Attrib.binding * (thm list * Args.src list) list) list ->
    (Attrib.binding * (thm list * Args.src list) list) list ->
    local_theory -> local_theory
  val abbrev: (string * bool -> binding * mixfix -> term * term ->
      term list -> local_theory -> local_theory) ->
    string * bool -> (binding * mixfix) * term -> local_theory -> (term * term) * local_theory
  val background_declaration: declaration -> local_theory -> local_theory
  val locale_declaration: string -> bool -> declaration -> local_theory -> local_theory
  val standard_declaration: (int -> bool) -> declaration -> local_theory -> local_theory
  val generic_const: bool -> Syntax.mode -> (binding * mixfix) * term ->
    Context.generic -> Context.generic
  val const_declaration: (int -> bool) -> Syntax.mode -> (binding * mixfix) * term ->
    local_theory -> local_theory
  val theory_foundation: ((binding * typ) * mixfix) * (binding * term) ->
    term list * term list -> local_theory -> (term * thm) * local_theory
  val theory_notes: string ->
    (Attrib.binding * (thm list * Args.src list) list) list ->
    (Attrib.binding * (thm list * Args.src list) list) list ->
    local_theory -> local_theory
  val theory_abbrev: Syntax.mode -> (binding * mixfix) * term -> local_theory -> local_theory
  val theory_declaration: declaration -> local_theory -> local_theory
end

structure Generic_Target: GENERIC_TARGET =
struct

(** lifting primitive to target operations **)

(* mixfix syntax *)

fun check_mixfix ctxt (b, extra_tfrees) mx =
  if null extra_tfrees then mx
  else
    (Context_Position.if_visible ctxt warning
      ("Additional type variable(s) in specification of " ^ Binding.print b ^ ": " ^
        commas (map (Syntax.string_of_typ ctxt o TFree) (sort_wrt #1 extra_tfrees)) ^
        (if mx = NoSyn then ""
         else "\nDropping mixfix syntax " ^ Pretty.string_of (Mixfix.pretty_mixfix mx)));
      NoSyn);


(* define *)

fun define foundation internal ((b, mx), ((b_def, atts), rhs)) lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val thy_ctxt = Proof_Context.init_global thy;

    (*term and type parameters*)
    val ((defs, _), rhs') = Thm.cterm_of thy rhs
      |> Local_Defs.export_cterm lthy thy_ctxt ||> Thm.term_of;

    val xs = Variable.add_fixed lthy rhs' [];
    val T = Term.fastype_of rhs;
    val tfreesT = Term.add_tfreesT T (fold (Term.add_tfreesT o #2) xs []);
    val extra_tfrees = rev (subtract (op =) tfreesT (Term.add_tfrees rhs []));
    val mx' = check_mixfix lthy (b, extra_tfrees) mx;

    val type_params = map (Logic.mk_type o TFree) extra_tfrees;
    val term_params = map Free (sort (Variable.fixed_ord lthy o pairself #1) xs);
    val params = type_params @ term_params;

    val U = map Term.fastype_of params ---> T;

    (*foundation*)
    val ((lhs', global_def), lthy2) = lthy
      |> foundation (((b, U), mx'), (b_def, rhs')) (type_params, term_params);

    (*local definition*)
    val ((lhs, local_def), lthy3) = lthy2
      |> Local_Defs.add_def ((b, NoSyn), lhs');

    (*result*)
    val def =
      Thm.transitive local_def global_def
      |> Local_Defs.contract defs
          (Thm.cterm_of (Proof_Context.theory_of lthy3) (Logic.mk_equals (lhs, rhs)));
    val ([(res_name, [res])], lthy4) = lthy3
      |> Local_Theory.notes [((if internal then Binding.empty else b_def, atts), [([def], [])])];
  in ((lhs, (res_name, res)), lthy4) end;


(* notes *)

local

fun import_export_proof ctxt (name, raw_th) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val thy_ctxt = Proof_Context.init_global thy;
    val certT = Thm.ctyp_of thy;
    val cert = Thm.cterm_of thy;

    (*export assumes/defines*)
    val th = Goal.norm_result raw_th;
    val ((defs, asms), th') = Local_Defs.export ctxt thy_ctxt th;
    val asms' = map (Raw_Simplifier.rewrite_rule defs) asms;

    (*export fixes*)
    val tfrees = map TFree (Thm.fold_terms Term.add_tfrees th' []);
    val frees = map Free (Thm.fold_terms Term.add_frees th' []);
    val (th'' :: vs) =
      (th' :: map (Drule.mk_term o cert) (map Logic.mk_type tfrees @ frees))
      |> Variable.export ctxt thy_ctxt
      |> Drule.zero_var_indexes_list;

    (*thm definition*)
    val result = Global_Theory.name_thm true true name th'';

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
    val result'' =
      (fold (curry op COMP) asms' result'
        handle THM _ => raise THM ("Failed to re-import result", 0, result' :: asms'))
      |> Local_Defs.contract defs (Thm.cprop_of th)
      |> Goal.norm_result
      |> Global_Theory.name_thm false false name;

  in (result'', result) end;

fun standard_facts lthy ctxt =
  Element.transform_facts (Local_Theory.standard_morphism lthy ctxt);

in

fun notes target_notes kind facts lthy =
  let
    val facts' = facts
      |> map (fn (a, bs) => (a, Global_Theory.burrow_fact (Global_Theory.name_multi
          (Local_Theory.full_name lthy (fst a))) bs))
      |> Global_Theory.map_facts (import_export_proof lthy);
    val local_facts = Global_Theory.map_facts #1 facts';
    val global_facts = Global_Theory.map_facts #2 facts';
  in
    lthy
    |> target_notes kind global_facts (Attrib.partial_evaluation lthy local_facts)
    |> Attrib.local_notes kind local_facts
  end;

fun locale_notes locale kind global_facts local_facts =
  Local_Theory.background_theory
    (Attrib.global_notes kind (Attrib.map_facts (K []) global_facts) #> snd) #>
  (fn lthy => lthy |>
    Local_Theory.target (fn ctxt => ctxt |>
      Locale.add_thmss locale kind (standard_facts lthy ctxt local_facts))) #>
  (fn lthy => lthy |>
    Local_Theory.map_contexts (fn level => fn ctxt =>
      if level = 0 orelse level = Local_Theory.level lthy then ctxt
      else ctxt |> Attrib.local_notes kind (standard_facts lthy ctxt local_facts) |> snd));

end;


(* abbrev *)

fun abbrev target_abbrev prmode ((b, mx), t) lthy =
  let
    val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);
    val target_ctxt = Local_Theory.target_of lthy;

    val t' = Assumption.export_term lthy target_ctxt t;
    val xs = map Free (rev (Variable.add_fixed lthy t' []));
    val u = fold_rev lambda xs t';

    val extra_tfrees =
      subtract (op =) (Term.add_tfreesT (Term.fastype_of u) []) (Term.add_tfrees u []);
    val mx' = check_mixfix lthy (b, extra_tfrees) mx;

    val global_rhs =
      singleton (Variable.export_terms (Variable.declare_term u target_ctxt) thy_ctxt) u;
  in
    lthy
    |> target_abbrev prmode (b, mx') (global_rhs, t') xs
    |> Proof_Context.add_abbrev Print_Mode.internal (b, t) |> snd
    |> Local_Defs.fixed_abbrev ((b, NoSyn), t)
  end;


(* declaration *)

fun background_declaration decl lthy =
  let
    val theory_decl =
      Local_Theory.standard_form lthy
        (Proof_Context.init_global (Proof_Context.theory_of lthy)) decl;
  in Local_Theory.background_theory (Context.theory_map theory_decl) lthy end;

fun locale_declaration locale syntax decl lthy = lthy
  |> Local_Theory.target (fn ctxt => ctxt |>
    Locale.add_declaration locale syntax
      (Morphism.transform (Local_Theory.standard_morphism lthy ctxt) decl));

fun standard_declaration pred decl lthy =
  Local_Theory.map_contexts (fn level => fn ctxt =>
    if pred level then Context.proof_map (Local_Theory.standard_form lthy ctxt decl) ctxt
    else ctxt) lthy;


(* const declaration *)

fun generic_const same_shape prmode ((b, mx), t) context =
  let
    val const_alias =
      if same_shape then
        (case t of
          Const (c, T) =>
            let
              val thy = Context.theory_of context;
              val ctxt = Context.proof_of context;
              val t' = Syntax.check_term ctxt (Const (c, dummyT))
                |> singleton (Variable.polymorphic ctxt);
            in
              (case t' of
                Const (c', T') =>
                  if c = c' andalso Sign.typ_equiv thy (T, T') then SOME c else NONE
              | _ => NONE)
            end
        | _ => NONE)
      else NONE;
  in
    (case const_alias of
      SOME c =>
        context
        |> Context.mapping (Sign.const_alias b c) (Proof_Context.const_alias b c)
        |> Morphism.form (Proof_Context.generic_notation true prmode [(t, mx)])
    | NONE =>
        context
        |> Proof_Context.generic_add_abbrev Print_Mode.internal (b, t)
        |-> (fn (const as Const (c, _), _) => same_shape ?
              (Proof_Context.generic_revert_abbrev (#1 prmode) c #>
               Morphism.form (Proof_Context.generic_notation true prmode [(const, mx)]))))
  end;

fun const_declaration pred prmode ((b, mx), rhs) =
  standard_declaration pred (fn phi =>
    let
      val b' = Morphism.binding phi b;
      val rhs' = Morphism.term phi rhs;
      val same_shape = Term.aconv_untyped (rhs, rhs');
    in generic_const same_shape prmode ((b', mx), Term.close_schematic_term rhs') end);



(** primitive theory operations **)

fun theory_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params) lthy =
  let
    val (const, lthy2) = lthy
      |> Local_Theory.background_theory_result (Sign.declare_const lthy ((b, U), mx));
    val lhs = list_comb (const, type_params @ term_params);
    val ((_, def), lthy3) = lthy2
      |> Local_Theory.background_theory_result
        (Thm.add_def lthy2 false false
          (Thm.def_binding_optional b b_def, Logic.mk_equals (lhs, rhs)));
  in ((lhs, def), lthy3) end;

fun theory_notes kind global_facts local_facts =
  Local_Theory.background_theory (Attrib.global_notes kind global_facts #> snd) #>
  (fn lthy => lthy |> Local_Theory.map_contexts (fn level => fn ctxt =>
    if level = Local_Theory.level lthy then ctxt
    else
      ctxt |> Attrib.local_notes kind
        (Element.transform_facts (Local_Theory.standard_morphism lthy ctxt) local_facts) |> snd));

fun theory_abbrev prmode ((b, mx), t) =
  Local_Theory.background_theory
    (Sign.add_abbrev (#1 prmode) (b, t) #->
      (fn (lhs, _) => Sign.notation true prmode [(lhs, mx)]));

fun theory_declaration decl =
  background_declaration decl #> standard_declaration (K true) decl;

end;
