(*  Title:      Pure/Isar/theory_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Common target infrastructure.
*)

signature GENERIC_TARGET =
sig
  val define: (((binding * typ) * mixfix) * (binding * term)
    -> term list * term list -> local_theory -> (term * thm) * local_theory)
    -> (binding * mixfix) * (Attrib.binding * term) -> local_theory
    -> (term * (string * thm)) * local_theory
  val notes: (string
    -> (Attrib.binding * (thm list * Args.src list) list) list
    -> (Attrib.binding * (thm list * Args.src list) list) list
    -> local_theory -> local_theory)
    -> string -> (Attrib.binding * (thm list * Args.src list) list) list
    -> local_theory -> (string * thm list) list * local_theory
  val abbrev: (string * bool -> binding * mixfix -> term * term
    -> term list -> local_theory -> local_theory)
    -> string * bool -> (binding * mixfix) * term -> local_theory
    -> (term * term) * local_theory

  val theory_declaration: declaration -> local_theory -> local_theory
  val theory_foundation: ((binding * typ) * mixfix) * (binding * term)
    -> term list * term list -> local_theory -> (term * thm) * local_theory
  val theory_notes: string -> (Attrib.binding * (thm list * Args.src list) list) list
    -> local_theory -> local_theory
  val theory_abbrev: Syntax.mode -> (binding * mixfix) * term
    -> local_theory -> local_theory
end;

structure Generic_Target: GENERIC_TARGET =
struct

(** lifting primitive to target operations **)

(* mixfix syntax *)

fun check_mixfix ctxt (b, extra_tfrees) mx =
  if null extra_tfrees then mx
  else
    (warning
      ("Additional type variable(s) in specification of " ^ Binding.str_of b ^ ": " ^
        commas (map (Syntax.string_of_typ ctxt o TFree) (sort_wrt #1 extra_tfrees)) ^
        (if mx = NoSyn then ""
         else "\nDropping mixfix syntax " ^ Pretty.string_of (Syntax.pretty_mixfix mx)));
      NoSyn);


(* define *)

fun define foundation ((b, mx), ((proto_b_def, atts), rhs)) lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val thy_ctxt = ProofContext.init_global thy;

    val b_def = Thm.def_binding_optional b proto_b_def;

    (*term and type parameters*)
    val crhs = Thm.cterm_of thy rhs;
    val (defs, rhs') = Local_Defs.export_cterm lthy thy_ctxt crhs ||> Thm.term_of;
    val rhs_conv = MetaSimplifier.rewrite true defs crhs;

    val xs = Variable.add_fixed (Local_Theory.target_of lthy) rhs' [];
    val T = Term.fastype_of rhs;
    val tfreesT = Term.add_tfreesT T (fold (Term.add_tfreesT o #2) xs []);
    val extra_tfrees = rev (subtract (op =) tfreesT (Term.add_tfrees rhs []));
    val mx' = check_mixfix lthy (b, extra_tfrees) mx;

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
    val ((lhs', global_def), lthy2) = foundation
      (((b, U), mx'), (b_def, rhs')) (type_params, term_params) lthy;

    (*local definition*)
    val ((lhs, local_def), lthy3) = lthy2
      |> Local_Defs.add_def ((b, NoSyn), lhs');
    val def = Local_Defs.trans_terms lthy3
      [(*c == global.c xs*)     local_def,
       (*global.c xs == rhs'*)  global_def,
       (*rhs' == rhs*)          Thm.symmetric rhs_conv];

    (*note*)
    val ([(res_name, [res])], lthy4) = lthy3
      |> Local_Theory.notes_kind "" [((b_def, atts), [([def], [])])];
  in ((lhs, (res_name, res)), lthy4) end;


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
    val assms = map (MetaSimplifier.rewrite_rule defs o Thm.assume)
      (Assumption.all_assms_of ctxt);
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

fun notes target_notes kind facts lthy =
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
    |> target_notes kind global_facts local_facts
    |> ProofContext.note_thmss kind (Attrib.map_facts (Attrib.attribute_i thy) local_facts)
  end;


(* abbrev *)

fun abbrev target_abbrev prmode ((b, mx), t) lthy =
  let
    val thy_ctxt = ProofContext.init_global (ProofContext.theory_of lthy);
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
    |> ProofContext.add_abbrev Print_Mode.internal (b, t) |> snd
    |> Local_Defs.fixed_abbrev ((b, NoSyn), t)
  end;


(** primitive theory operations **)

fun theory_declaration decl lthy =
  let
    val global_decl = Morphism.form
      (Morphism.transform (Local_Theory.global_morphism lthy) decl);
  in
    lthy
    |> Local_Theory.theory (Context.theory_map global_decl)
    |> Local_Theory.target (Context.proof_map global_decl)
  end;

fun theory_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params) lthy =
  let
    val (const, lthy2) = lthy |> Local_Theory.theory_result
      (Sign.declare_const ((b, U), mx));
    val lhs = list_comb (const, type_params @ term_params);
    val ((_, def), lthy3) = lthy2 |> Local_Theory.theory_result
      (Thm.add_def false false (b_def, Logic.mk_equals (lhs, rhs)));
  in ((lhs, def), lthy3) end;

fun theory_notes kind global_facts lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val global_facts' = Attrib.map_facts (Attrib.attribute_i thy) global_facts;
  in
    lthy
    |> Local_Theory.theory (PureThy.note_thmss kind global_facts' #> snd)
    |> Local_Theory.target (ProofContext.note_thmss kind global_facts' #> snd)
  end;

fun theory_abbrev prmode ((b, mx), t) = Local_Theory.theory
  (Sign.add_abbrev (#1 prmode) (b, t) #->
    (fn (lhs, _) => Sign.notation true prmode [(lhs, mx)]));

end;
