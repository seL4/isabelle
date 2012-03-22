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
  val notes: (string -> (Attrib.binding * (thm list * Args.src list) list) list ->
      (Attrib.binding * (thm list * Args.src list) list) list -> local_theory -> local_theory) ->
    string -> (Attrib.binding * (thm list * Args.src list) list) list -> local_theory ->
    (string * thm list) list * local_theory
  val abbrev: (string * bool -> binding * mixfix -> term * term ->
      term list -> local_theory -> local_theory) ->
    string * bool -> (binding * mixfix) * term -> local_theory ->
    (term * term) * local_theory

  val background_declaration: declaration -> local_theory -> local_theory
  val standard_declaration: declaration -> local_theory -> local_theory

  val theory_foundation: ((binding * typ) * mixfix) * (binding * term) ->
    term list * term list -> local_theory -> (term * thm) * local_theory
  val theory_notes: string -> (Attrib.binding * (thm list * Args.src list) list) list ->
    local_theory -> local_theory
  val theory_abbrev: Syntax.mode -> (binding * mixfix) * term -> local_theory -> local_theory
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
    val crhs = Thm.cterm_of thy rhs;
    val ((defs, _), rhs') = Local_Defs.export_cterm lthy thy_ctxt crhs ||> Thm.term_of;
    val rhs_conv = Raw_Simplifier.rewrite true defs crhs;

    val xs = Variable.add_fixed (Local_Theory.target_of lthy) rhs' [];
    val T = Term.fastype_of rhs;
    val tfreesT = Term.add_tfreesT T (fold (Term.add_tfreesT o #2) xs []);
    val extra_tfrees = rev (subtract (op =) tfreesT (Term.add_tfrees rhs []));
    val mx' = check_mixfix lthy (b, extra_tfrees) mx;

    val type_params = map (Logic.mk_type o TFree) extra_tfrees;
    val target_ctxt = Local_Theory.target_of lthy;
    val term_params =
      filter (Variable.is_fixed target_ctxt o #1) xs
      |> sort (Variable.fixed_ord target_ctxt o pairself #1)
      |> map Free;
    val params = type_params @ term_params;

    val U = map Term.fastype_of params ---> T;

    (*foundation*)
    val ((lhs', global_def), lthy2) = lthy
      |> foundation (((b, U), mx'), (b_def, rhs')) (type_params, term_params);

    (*local definition*)
    val ((lhs, local_def), lthy3) = lthy2
      |> Local_Defs.add_def ((b, NoSyn), lhs');
    val def = Local_Defs.trans_terms lthy3
      [(*c == global.c xs*)     local_def,
       (*global.c xs == rhs'*)  global_def,
       (*rhs' == rhs*)          Thm.symmetric rhs_conv];

    (*note*)
    val ([(res_name, [res])], lthy4) = lthy3
      |> Local_Theory.notes [((if internal then Binding.empty else b_def, atts), [([def], [])])];
  in ((lhs, (res_name, res)), lthy4) end;


(* notes *)

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
      |> Local_Defs.contract ctxt defs (Thm.cprop_of th)
      |> Goal.norm_result
      |> Global_Theory.name_thm false false name;

  in (result'', result) end;

fun notes target_notes kind facts lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val facts' = facts
      |> map (fn (a, bs) => (a, Global_Theory.burrow_fact (Global_Theory.name_multi
          (Local_Theory.full_name lthy (fst a))) bs))
      |> Global_Theory.map_facts (import_export_proof lthy);
    val local_facts = Global_Theory.map_facts #1 facts';
    val global_facts = Global_Theory.map_facts #2 facts';
  in
    lthy
    |> target_notes kind global_facts local_facts
    |> Proof_Context.note_thmss kind (Attrib.map_facts (map (Attrib.attribute_i thy)) local_facts)
  end;


(* abbrev *)

fun abbrev target_abbrev prmode ((b, mx), t) lthy =
  let
    val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);
    val target_ctxt = Local_Theory.target_of lthy;

    val t' = Assumption.export_term lthy target_ctxt t;
    val xs = map Free (rev (Variable.add_fixed target_ctxt t' []));
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

fun standard_declaration decl =
  background_declaration decl #>
  (fn lthy => Local_Theory.map_contexts (fn ctxt =>
    Context.proof_map (Local_Theory.standard_form lthy ctxt decl) ctxt) lthy);



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

fun theory_notes kind global_facts lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val global_facts' = Attrib.map_facts (map (Attrib.attribute_i thy)) global_facts;
  in
    lthy
    |> Local_Theory.background_theory (Global_Theory.note_thmss kind global_facts' #> snd)
    |> Local_Theory.target (Proof_Context.note_thmss kind global_facts' #> snd)
  end;

fun theory_abbrev prmode ((b, mx), t) =
  Local_Theory.background_theory
    (Sign.add_abbrev (#1 prmode) (b, t) #->
      (fn (lhs, _) => Sign.notation true prmode [(lhs, mx)]));

end;
