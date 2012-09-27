(*  Title:      HOL/Tools/Lifting/lifting_def.ML
    Author:     Ondrej Kuncar

Definitions for constants on quotient types.
*)

signature LIFTING_DEF =
sig
  val add_lift_def:
    (binding * mixfix) -> typ -> term -> thm -> local_theory -> local_theory

  val lift_def_cmd:
    (binding * string option * mixfix) * string -> local_theory -> Proof.state

  val can_generate_code_cert: thm -> bool
end;

structure Lifting_Def: LIFTING_DEF =
struct

open Lifting_Util

infix 0 MRSL

(* Generation of the code certificate from the rsp theorem *)

fun get_body_types (Type ("fun", [_, U]), Type ("fun", [_, V])) = get_body_types (U, V)
  | get_body_types (U, V)  = (U, V)

fun get_binder_types (Type ("fun", [T, U]), Type ("fun", [V, W])) = (T, V) :: get_binder_types (U, W)
  | get_binder_types _ = []

fun get_binder_types_by_rel (Const (@{const_name "fun_rel"}, _) $ _ $ S) (Type ("fun", [T, U]), Type ("fun", [V, W])) = 
    (T, V) :: get_binder_types_by_rel S (U, W)
  | get_binder_types_by_rel _ _ = []

fun get_body_type_by_rel (Const (@{const_name "fun_rel"}, _) $ _ $ S) (Type ("fun", [_, U]), Type ("fun", [_, V])) = 
    get_body_type_by_rel S (U, V)
  | get_body_type_by_rel _ (U, V)  = (U, V)

fun force_rty_type ctxt rty rhs = 
  let
    val thy = Proof_Context.theory_of ctxt
    val rhs_schematic = singleton (Variable.polymorphic ctxt) rhs
    val rty_schematic = fastype_of rhs_schematic
    val match = Sign.typ_match thy (rty_schematic, rty) Vartab.empty
  in
    Envir.subst_term_types match rhs_schematic
  end

fun unabs_def ctxt def = 
  let
    val (_, rhs) = Thm.dest_equals (cprop_of def)
    fun dest_abs (Abs (var_name, T, _)) = (var_name, T)
      | dest_abs tm = raise TERM("get_abs_var",[tm])
    val (var_name, T) = dest_abs (term_of rhs)
    val (new_var_names, ctxt') = Variable.variant_fixes [var_name] ctxt
    val thy = Proof_Context.theory_of ctxt'
    val refl_thm = Thm.reflexive (cterm_of thy (Free (hd new_var_names, T)))
  in
    Thm.combination def refl_thm |>
    singleton (Proof_Context.export ctxt' ctxt)
  end

fun unabs_all_def ctxt def = 
  let
    val (_, rhs) = Thm.dest_equals (cprop_of def)
    val xs = strip_abs_vars (term_of rhs)
  in  
    fold (K (unabs_def ctxt)) xs def
  end

val map_fun_unfolded = 
  @{thm map_fun_def[abs_def]} |>
  unabs_def @{context} |>
  unabs_def @{context} |>
  Local_Defs.unfold @{context} [@{thm comp_def}]

fun unfold_fun_maps ctm =
  let
    fun unfold_conv ctm =
      case (Thm.term_of ctm) of
        Const (@{const_name "map_fun"}, _) $ _ $ _ => 
          (Conv.arg_conv unfold_conv then_conv Conv.rewr_conv map_fun_unfolded) ctm
        | _ => Conv.all_conv ctm
  in
    (Conv.fun_conv unfold_conv) ctm
  end

fun unfold_fun_maps_beta ctm =
  let val try_beta_conv = Conv.try_conv (Thm.beta_conversion false)
  in 
    (unfold_fun_maps then_conv try_beta_conv) ctm 
  end

fun prove_rel ctxt rsp_thm (rty, qty) =
  let
    val ty_args = get_binder_types (rty, qty)
    fun disch_arg args_ty thm = 
      let
        val quot_thm = Lifting_Term.prove_quot_thm ctxt args_ty
      in
        [quot_thm, thm] MRSL @{thm apply_rsp''}
      end
  in
    fold disch_arg ty_args rsp_thm
  end

exception CODE_CERT_GEN of string

fun simplify_code_eq ctxt def_thm = 
  Local_Defs.unfold ctxt [@{thm o_apply}, @{thm map_fun_def}, @{thm id_apply}] def_thm

(*
  quot_thm - quotient theorem (Quotient R Abs Rep T).
  returns: whether the Lifting package is capable to generate code for the abstract type
    represented by quot_thm
*)

fun can_generate_code_cert quot_thm  =
  case quot_thm_rel quot_thm of
    Const (@{const_name HOL.eq}, _) => true
    | Const (@{const_name invariant}, _) $ _  => true
    | _ => false

fun generate_code_cert ctxt def_thm rsp_thm (rty, qty) =
  let
    val thy = Proof_Context.theory_of ctxt
    val quot_thm = Lifting_Term.prove_quot_thm ctxt (get_body_types (rty, qty))
    val fun_rel = prove_rel ctxt rsp_thm (rty, qty)
    val abs_rep_thm = [quot_thm, fun_rel] MRSL @{thm Quotient_rep_abs}
    val abs_rep_eq = 
      case (HOLogic.dest_Trueprop o prop_of) fun_rel of
        Const (@{const_name HOL.eq}, _) $ _ $ _ => abs_rep_thm
        | Const (@{const_name invariant}, _) $ _ $ _ $ _ => abs_rep_thm RS @{thm invariant_to_eq}
        | _ => raise CODE_CERT_GEN "relation is neither equality nor invariant"
    val unfolded_def = Conv.fconv_rule (Conv.arg_conv unfold_fun_maps_beta) def_thm
    val unabs_def = unabs_all_def ctxt unfolded_def
    val rep = (cterm_of thy o quot_thm_rep) quot_thm
    val rep_refl = Thm.reflexive rep RS @{thm meta_eq_to_obj_eq}
    val repped_eq = [rep_refl, unabs_def RS @{thm meta_eq_to_obj_eq}] MRSL @{thm cong}
    val code_cert = [repped_eq, abs_rep_eq] MRSL @{thm trans}
  in
    simplify_code_eq ctxt code_cert
  end

fun generate_trivial_rep_eq ctxt def_thm =
  let
    val unfolded_def = Conv.fconv_rule (Conv.arg_conv unfold_fun_maps_beta) def_thm
    val code_eq = unabs_all_def ctxt unfolded_def
    val simp_code_eq = simplify_code_eq ctxt code_eq
  in
    simp_code_eq
  end

fun generate_rep_eq ctxt def_thm rsp_thm (rty, qty) =
  if body_type rty = body_type qty then 
    SOME (generate_trivial_rep_eq ctxt def_thm)
  else 
    let
      val (rty_body, qty_body) = get_body_types (rty, qty)
      val quot_thm = Lifting_Term.prove_quot_thm ctxt (rty_body, qty_body)
    in
      if can_generate_code_cert quot_thm then
        SOME (generate_code_cert ctxt def_thm rsp_thm (rty, qty))
      else 
        NONE
    end

fun generate_abs_eq ctxt def_thm rsp_thm quot_thm =
  let
    fun refl_tac ctxt =
      let
        fun intro_reflp_tac (t, i) = 
        let
          val concl_pat = Drule.strip_imp_concl (cprop_of @{thm reflpD})
          val insts = Thm.first_order_match (concl_pat, t)
        in
          rtac (Drule.instantiate_normalize insts @{thm reflpD}) i
        end
        handle Pattern.MATCH => no_tac
        
        val fun_rel_meta_eq = mk_meta_eq @{thm fun_rel_eq}
        val conv = Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv fun_rel_meta_eq))) ctxt
        val rules = Lifting_Info.get_reflexivity_rules ctxt
      in
        EVERY' [CSUBGOAL intro_reflp_tac, 
                CONVERSION conv,
                REPEAT_ALL_NEW (resolve_tac rules)]
      end
    
    fun try_prove_prem ctxt prop =
      SOME (Goal.prove ctxt [] [] prop (fn {context, ...} => refl_tac context 1))
        handle ERROR _ => NONE

    val abs_eq_with_assms =
      let
        val (rty, qty) = quot_thm_rty_qty quot_thm
        val rel = quot_thm_rel quot_thm
        val ty_args = get_binder_types_by_rel rel (rty, qty)
        val body_type = get_body_type_by_rel rel (rty, qty)
        val quot_ret_thm = Lifting_Term.prove_quot_thm ctxt body_type
        
        val rep_abs_folded_unmapped_thm = 
          let
            val rep_id = [quot_thm, def_thm] MRSL @{thm Quotient_Rep_eq}
            val ctm = Thm.dest_equals_lhs (cprop_of rep_id)
            val unfolded_maps_eq = unfold_fun_maps ctm
            val t1 = [quot_thm, def_thm, rsp_thm] MRSL @{thm Quotient_rep_abs_fold_unmap}
            val prems_pat = (hd o Drule.cprems_of) t1
            val insts = Thm.first_order_match (prems_pat, cprop_of unfolded_maps_eq)
          in
            unfolded_maps_eq RS (Drule.instantiate_normalize insts t1)
          end
      in
        rep_abs_folded_unmapped_thm
        |> fold (fn _ => fn thm => thm RS @{thm fun_relD2}) ty_args
        |> (fn x => x RS (@{thm Quotient_rel_abs2} OF [quot_ret_thm]))
      end
    
    val prems = prems_of abs_eq_with_assms
    val indexed_prems = map_index (apfst (fn x => x + 1)) prems
    val indexed_assms = map (apsnd (try_prove_prem ctxt)) indexed_prems
    val proved_assms = map (apsnd the) (filter (is_some o snd) indexed_assms)
    val abs_eq = fold_rev (fn (i, assms) => fn thm => assms RSN (i, thm)) proved_assms abs_eq_with_assms
  in
    simplify_code_eq ctxt abs_eq
  end

fun define_code_using_abs_eq abs_eq_thm lthy =
  if null (Logic.strip_imp_prems(prop_of abs_eq_thm)) then
    (snd oo Local_Theory.note) ((Binding.empty, [Code.add_default_eqn_attrib]), [abs_eq_thm]) lthy
  else
    lthy
  
fun define_code_using_rep_eq maybe_rep_eq_thm lthy = 
  case maybe_rep_eq_thm of
    SOME rep_eq_thm =>   
      let
        val add_abs_eqn_attribute = 
          Thm.declaration_attribute (fn thm => Context.mapping (Code.add_abs_eqn thm) I)
        val add_abs_eqn_attrib = Attrib.internal (K add_abs_eqn_attribute);
      in
        (snd oo Local_Theory.note) ((Binding.empty, [add_abs_eqn_attrib]), [rep_eq_thm]) lthy
      end
    | NONE => lthy

fun has_constr ctxt quot_thm =
  let
    val thy = Proof_Context.theory_of ctxt
    val abs_fun = quot_thm_abs quot_thm
  in
    if is_Const abs_fun then
      Code.is_constr thy ((fst o dest_Const) abs_fun)
    else
      false
  end

fun has_abstr ctxt quot_thm =
  let
    val thy = Proof_Context.theory_of ctxt
    val abs_fun = quot_thm_abs quot_thm
  in
    if is_Const abs_fun then
      Code.is_abstr thy ((fst o dest_Const) abs_fun)
    else
      false
  end

fun define_code abs_eq_thm maybe_rep_eq_thm (rty, qty) lthy =
  let
    val (rty_body, qty_body) = get_body_types (rty, qty)
  in
    if rty_body = qty_body then
      if null (Logic.strip_imp_prems(prop_of abs_eq_thm)) then
        (snd oo Local_Theory.note) ((Binding.empty, [Code.add_default_eqn_attrib]), [abs_eq_thm]) lthy
      else
        (snd oo Local_Theory.note) ((Binding.empty, [Code.add_default_eqn_attrib]), [the maybe_rep_eq_thm]) lthy
    else
      let 
        val body_quot_thm = Lifting_Term.prove_quot_thm lthy (rty_body, qty_body)
      in
        if has_constr lthy body_quot_thm then
          define_code_using_abs_eq abs_eq_thm lthy
        else if has_abstr lthy body_quot_thm then
          define_code_using_rep_eq maybe_rep_eq_thm lthy
        else
          lthy
      end
  end

(*
  Defines an operation on an abstract type in terms of a corresponding operation 
    on a representation type.

  var - a binding and a mixfix of the new constant being defined
  qty - an abstract type of the new constant
  rhs - a term representing the new constant on the raw level
  rsp_thm - a respectfulness theorem in the internal tagged form (like '(R ===> R ===> R) f f'),
    i.e. "(Lifting_Term.equiv_relation (fastype_of rhs, qty)) $ rhs $ rhs"
*)

fun add_lift_def var qty rhs rsp_thm lthy =
  let
    val rty = fastype_of rhs
    val quot_thm = Lifting_Term.prove_quot_thm lthy (rty, qty)
    val absrep_trm =  quot_thm_abs quot_thm
    val rty_forced = (domain_type o fastype_of) absrep_trm
    val forced_rhs = force_rty_type lthy rty_forced rhs
    val lhs = Free (Binding.print (#1 var), qty)
    val prop = Logic.mk_equals (lhs, absrep_trm $ forced_rhs)
    val (_, prop') = Local_Defs.cert_def lthy prop
    val (_, newrhs) = Local_Defs.abs_def prop'

    val ((_, (_ , def_thm)), lthy') = 
      Local_Theory.define (var, ((Thm.def_binding (#1 var), []), newrhs)) lthy

    val transfer_thm = ([quot_thm, rsp_thm, def_thm] MRSL @{thm Quotient_to_transfer})
        |> Raw_Simplifier.rewrite_rule (Transfer.get_sym_relator_eq lthy')
     
    val abs_eq_thm = generate_abs_eq lthy' def_thm rsp_thm quot_thm
    val maybe_rep_eq_thm = generate_rep_eq lthy' def_thm rsp_thm (rty_forced, qty)

    fun qualify defname suffix = Binding.qualified true suffix defname

    val lhs_name = (#1 var)
    val rsp_thm_name = qualify lhs_name "rsp"
    val abs_eq_thm_name = qualify lhs_name "abs_eq"
    val rep_eq_thm_name = qualify lhs_name "rep_eq"
    val transfer_thm_name = qualify lhs_name "transfer"
    val transfer_attr = Attrib.internal (K Transfer.transfer_add)
  in
    lthy'
      |> (snd oo Local_Theory.note) ((rsp_thm_name, []), [rsp_thm])
      |> (snd oo Local_Theory.note) ((transfer_thm_name, [transfer_attr]), [transfer_thm])
      |> (snd oo Local_Theory.note) ((abs_eq_thm_name, []), [abs_eq_thm])
      |> (case maybe_rep_eq_thm of 
            SOME rep_eq_thm => (snd oo Local_Theory.note) ((rep_eq_thm_name, []), [rep_eq_thm])
            | NONE => I)
      |> define_code abs_eq_thm maybe_rep_eq_thm (rty_forced, qty)
  end

fun mk_readable_rsp_thm_eq tm lthy =
  let
    val ctm = cterm_of (Proof_Context.theory_of lthy) tm
    
    fun norm_fun_eq ctm = 
      let
        fun abs_conv2 cv = Conv.abs_conv (K (Conv.abs_conv (K cv) lthy)) lthy
        fun erase_quants ctm' =
          case (Thm.term_of ctm') of
            Const ("HOL.eq", _) $ _ $ _ => Conv.all_conv ctm'
            | _ => (Conv.binder_conv (K erase_quants) lthy then_conv 
              Conv.rewr_conv @{thm fun_eq_iff[symmetric, THEN eq_reflection]}) ctm'
      in
        (abs_conv2 erase_quants then_conv Thm.eta_conversion) ctm
      end

    fun simp_arrows_conv ctm =
      let
        val unfold_conv = Conv.rewrs_conv 
          [@{thm fun_rel_eq_invariant[THEN eq_reflection]}, @{thm fun_rel_eq_rel[THEN eq_reflection]}, 
            @{thm fun_rel_def[THEN eq_reflection]}]
        val left_conv = simp_arrows_conv then_conv Conv.try_conv norm_fun_eq
        fun binop_conv2 cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2
        val invariant_commute_conv = Conv.bottom_conv
          (K (Conv.try_conv (Conv.rewrs_conv (Lifting_Info.get_invariant_commute_rules lthy)))) lthy
      in
        case (Thm.term_of ctm) of
          Const (@{const_name "fun_rel"}, _) $ _ $ _ => 
            (binop_conv2  left_conv simp_arrows_conv then_conv unfold_conv) ctm
          | _ => invariant_commute_conv ctm
      end
    
    val unfold_ret_val_invs = Conv.bottom_conv 
      (K (Conv.try_conv (Conv.rewr_conv @{thm invariant_same_args}))) lthy 
    val simp_conv = Trueprop_conv (Conv.fun2_conv simp_arrows_conv)
    val univq_conv = Conv.rewr_conv @{thm HOL.all_simps(6)[symmetric, THEN eq_reflection]}
    val univq_prenex_conv = Conv.top_conv (K (Conv.try_conv univq_conv)) lthy
    val beta_conv = Thm.beta_conversion true
    val eq_thm = 
      (simp_conv then_conv univq_prenex_conv then_conv beta_conv then_conv unfold_ret_val_invs) ctm
  in
    Object_Logic.rulify(eq_thm RS Drule.equal_elim_rule2)
  end

fun rename_to_tnames ctxt term =
  let
    fun all_typs (Const ("all", _) $ Abs (_, T, t)) = T :: all_typs t
      | all_typs _ = []

    fun rename (Const ("all", T1) $ Abs (_, T2, t)) (new_name :: names) = 
        (Const ("all", T1) $ Abs (new_name, T2, rename t names)) 
      | rename t _ = t

    val (fixed_def_t, _) = yield_singleton (Variable.importT_terms) term ctxt
    val new_names = Datatype_Prop.make_tnames (all_typs fixed_def_t)
  in
    rename term new_names
  end

(*

  lifting_definition command. It opens a proof of a corresponding respectfulness 
  theorem in a user-friendly, readable form. Then add_lift_def is called internally.

*)

fun lift_def_cmd (raw_var, rhs_raw) lthy =
  let
    val ((binding, SOME qty, mx), lthy') = yield_singleton Proof_Context.read_vars raw_var lthy 
    val rhs = (Syntax.check_term lthy' o Syntax.parse_term lthy') rhs_raw
 
    fun try_to_prove_refl thm = 
      let
        val lhs_eq =
          thm
          |> prop_of
          |> Logic.dest_implies
          |> fst
          |> strip_all_body
          |> try HOLogic.dest_Trueprop
      in
        case lhs_eq of
          SOME (Const ("HOL.eq", _) $ _ $ _) => SOME (@{thm refl} RS thm)
          | _ => NONE
      end

    val rsp_rel = Lifting_Term.equiv_relation lthy' (fastype_of rhs, qty)
    val rty_forced = (domain_type o fastype_of) rsp_rel;
    val forced_rhs = force_rty_type lthy' rty_forced rhs;
    val internal_rsp_tm = HOLogic.mk_Trueprop (rsp_rel $ forced_rhs $ forced_rhs)
    val readable_rsp_thm_eq = mk_readable_rsp_thm_eq internal_rsp_tm lthy'
    val maybe_proven_rsp_thm = try_to_prove_refl readable_rsp_thm_eq
    val (readable_rsp_tm, _) = Logic.dest_implies (prop_of readable_rsp_thm_eq)
    val readable_rsp_tm_tnames = rename_to_tnames lthy' readable_rsp_tm

    fun after_qed thm_list lthy = 
      let
        val internal_rsp_thm =
          case thm_list of
            [] => the maybe_proven_rsp_thm
          | [[thm]] => Goal.prove lthy [] [] internal_rsp_tm 
            (fn _ => rtac readable_rsp_thm_eq 1 THEN Proof_Context.fact_tac [thm] 1)
      in
        add_lift_def (binding, mx) qty rhs internal_rsp_thm lthy
      end

  in
    case maybe_proven_rsp_thm of
      SOME _ => Proof.theorem NONE after_qed [] lthy'
      | NONE =>  Proof.theorem NONE after_qed [[(readable_rsp_tm_tnames,[])]] lthy'
  end

fun quot_thm_err ctxt (rty, qty) pretty_msg =
  let
    val error_msg = cat_lines
       ["Lifting failed for the following types:",
        Pretty.string_of (Pretty.block
         [Pretty.str "Raw type:", Pretty.brk 2, Syntax.pretty_typ ctxt rty]),
        Pretty.string_of (Pretty.block
         [Pretty.str "Abstract type:", Pretty.brk 2, Syntax.pretty_typ ctxt qty]),
        "",
        (Pretty.string_of (Pretty.block
         [Pretty.str "Reason:", Pretty.brk 2, pretty_msg]))]
  in
    error error_msg
  end

fun check_rty_err ctxt (rty_schematic, rty_forced) (raw_var, rhs_raw) =
  let
    val (_, ctxt') = yield_singleton Proof_Context.read_vars raw_var ctxt 
    val rhs = (Syntax.check_term ctxt' o Syntax.parse_term ctxt') rhs_raw
    val error_msg = cat_lines
       ["Lifting failed for the following term:",
        Pretty.string_of (Pretty.block
         [Pretty.str "Term:", Pretty.brk 2, Syntax.pretty_term ctxt rhs]),
        Pretty.string_of (Pretty.block
         [Pretty.str "Type:", Pretty.brk 2, Syntax.pretty_typ ctxt rty_schematic]),
        "",
        (Pretty.string_of (Pretty.block
         [Pretty.str "Reason:", 
          Pretty.brk 2, 
          Pretty.str "The type of the term cannot be instancied to",
          Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt rty_forced),
          Pretty.str "."]))]
    in
      error error_msg
    end

fun lift_def_cmd_with_err_handling (raw_var, rhs_raw) lthy =
  (lift_def_cmd (raw_var, rhs_raw) lthy
    handle Lifting_Term.QUOT_THM (rty, qty, msg) => quot_thm_err lthy (rty, qty) msg)
    handle Lifting_Term.CHECK_RTY (rty_schematic, rty_forced) => 
      check_rty_err lthy (rty_schematic, rty_forced) (raw_var, rhs_raw)

(* parser and command *)
val liftdef_parser =
  ((Parse.binding -- (@{keyword "::"} |-- (Parse.typ >> SOME) -- Parse.opt_mixfix')) >> Parse.triple2)
    --| @{keyword "is"} -- Parse.term

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "lift_definition"}
    "definition for constants over the quotient type"
      (liftdef_parser >> lift_def_cmd_with_err_handling)


end; (* structure *)
