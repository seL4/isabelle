(*  Title:      HOL/Tools/Quotient/quotient_def.ML
    Author:     Cezary Kaliszyk and Christian Urban

Definitions for constants on quotient types.
*)

signature QUOTIENT_DEF =
sig
  val add_quotient_def:
    ((binding * mixfix) * Attrib.binding) * (term * term) -> thm ->
    local_theory -> Quotient_Info.quotconsts * local_theory

  val quotient_def:
    (binding * typ option * mixfix) option * (Attrib.binding * (term * term)) ->
    local_theory -> Proof.state

  val quotient_def_cmd:
    (binding * string option * mixfix) option * (Attrib.binding * (string * string)) ->
    local_theory -> Proof.state

  val lift_raw_const: typ list -> (string * term * mixfix) -> local_theory ->
    Quotient_Info.quotconsts * local_theory
end;

structure Quotient_Def: QUOTIENT_DEF =
struct

(** Interface and Syntax Setup **)

(* Generation of the code certificate from the rsp theorem *)

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

fun get_body_types (Type ("fun", [_, U]), Type ("fun", [_, V])) = get_body_types (U, V)
  | get_body_types (U, V)  = (U, V)

fun get_binder_types (Type ("fun", [T, U]), Type ("fun", [V, W])) = (T, V) :: get_binder_types (U, W)
  | get_binder_types _ = []

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
    val try_beta_conv = Conv.try_conv (Thm.beta_conversion false)
  in
    (Conv.arg_conv (Conv.fun_conv unfold_conv then_conv try_beta_conv)) ctm
  end

fun prove_rel ctxt rsp_thm (rty, qty) =
  let
    val ty_args = get_binder_types (rty, qty)
    fun disch_arg args_ty thm = 
      let
        val quot_thm = Quotient_Term.prove_quot_theorem ctxt args_ty
      in
        [quot_thm, thm] MRSL @{thm apply_rsp''}
      end
  in
    fold disch_arg ty_args rsp_thm
  end

exception CODE_CERT_GEN of string

fun simplify_code_eq ctxt def_thm = 
  Local_Defs.unfold ctxt [@{thm o_def}, @{thm map_fun_def}, @{thm id_def}] def_thm

fun generate_code_cert ctxt def_thm rsp_thm (rty, qty) =
  let
    val quot_thm = Quotient_Term.prove_quot_theorem ctxt (get_body_types (rty, qty))
    val fun_rel = prove_rel ctxt rsp_thm (rty, qty)
    val abs_rep_thm = [quot_thm, fun_rel] MRSL @{thm Quotient_rep_abs}
    val abs_rep_eq = 
      case (HOLogic.dest_Trueprop o prop_of) fun_rel of
        Const (@{const_name HOL.eq}, _) $ _ $ _ => abs_rep_thm
        | Const (@{const_name invariant}, _) $ _ $ _ $ _ => abs_rep_thm RS @{thm invariant_to_eq}
        | _ => raise CODE_CERT_GEN "relation is neither equality nor invariant"
    val unfolded_def = Conv.fconv_rule unfold_fun_maps def_thm
    val unabs_def = unabs_all_def ctxt unfolded_def
    val rep = (snd o Thm.dest_comb o snd o Thm.dest_comb o cprop_of) quot_thm
    val rep_refl = Thm.reflexive rep RS @{thm meta_eq_to_obj_eq}
    val repped_eq = [rep_refl, unabs_def RS @{thm meta_eq_to_obj_eq}] MRSL @{thm cong}
    val code_cert = [repped_eq, abs_rep_eq] MRSL @{thm trans}
  in
    simplify_code_eq ctxt code_cert
  end

fun define_code_cert code_eqn_thm_name def_thm rsp_thm (rty, qty) lthy = 
  let
    val quot_thm = Quotient_Term.prove_quot_theorem lthy (get_body_types (rty, qty))
  in
    if Quotient_Type.can_generate_code_cert quot_thm then
      let
        val code_cert = generate_code_cert lthy def_thm rsp_thm (rty, qty)
        val add_abs_eqn_attribute = 
          Thm.declaration_attribute (fn thm => Context.mapping (Code.add_abs_eqn thm) I)
        val add_abs_eqn_attrib = Attrib.internal (K add_abs_eqn_attribute);
      in
        lthy
          |> (snd oo Local_Theory.note) ((code_eqn_thm_name, [add_abs_eqn_attrib]), [code_cert])
      end
    else
      lthy
  end

fun define_code_eq code_eqn_thm_name def_thm lthy =
  let
    val unfolded_def = Conv.fconv_rule unfold_fun_maps def_thm
    val code_eq = unabs_all_def lthy unfolded_def
    val simp_code_eq = simplify_code_eq lthy code_eq
  in
    lthy
      |> (snd oo Local_Theory.note) ((code_eqn_thm_name, [Code.add_default_eqn_attrib]), [simp_code_eq])
  end

fun define_code code_eqn_thm_name def_thm rsp_thm (rty, qty) lthy =
  if body_type rty = body_type qty then 
    define_code_eq code_eqn_thm_name def_thm lthy
  else 
    define_code_cert code_eqn_thm_name def_thm rsp_thm (rty, qty) lthy

(* The ML-interface for a quotient definition takes
   as argument:

    - an optional binding and mixfix annotation
    - attributes
    - the new constant as term
    - the rhs of the definition as term
    - respectfulness theorem for the rhs

   It stores the qconst_info in the quotconsts data slot.

   Restriction: At the moment the left- and right-hand
   side of the definition must be a constant.
*)
fun error_msg bind str =
  let
    val name = Binding.name_of bind
    val pos = Position.str_of (Binding.pos_of bind)
  in
    error ("Head of quotient_definition " ^
      quote str ^ " differs from declaration " ^ name ^ pos)
  end

fun add_quotient_def ((var, (name, atts)), (lhs, rhs)) rsp_thm lthy =
  let
    val rty = fastype_of rhs
    val qty = fastype_of lhs
    val absrep_trm = 
      Quotient_Term.absrep_fun lthy Quotient_Term.AbsF (rty, qty) $ rhs
    val prop = Syntax.check_term lthy (Logic.mk_equals (lhs, absrep_trm))
    val (_, prop') = Local_Defs.cert_def lthy prop
    val (_, newrhs) = Local_Defs.abs_def prop'

    val ((trm, (_ , def_thm)), lthy') =
      Local_Theory.define (var, ((Thm.def_binding_optional (#1 var) name, atts), newrhs)) lthy

    (* data storage *)
    val qconst_data = {qconst = trm, rconst = rhs, def = def_thm}
    val lhs_name = #1 var
    val rsp_thm_name = Binding.suffix_name "_rsp" lhs_name
    val code_eqn_thm_name = Binding.suffix_name "_code_eqn" lhs_name
    
    val lthy'' = lthy'
      |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi =>
          (case Quotient_Info.transform_quotconsts phi qconst_data of
            qcinfo as {qconst = Const (c, _), ...} =>
              Quotient_Info.update_quotconsts c qcinfo
          | _ => I))
      |> (snd oo Local_Theory.note) 
        ((rsp_thm_name, [Attrib.internal (K Quotient_Info.rsp_rules_add)]),
        [rsp_thm])
      |> define_code code_eqn_thm_name def_thm rsp_thm (rty, qty)

  in
    (qconst_data, lthy'')
  end

fun mk_readable_rsp_thm_eq tm lthy =
  let
    val ctm = cterm_of (Proof_Context.theory_of lthy) tm
    
    fun norm_fun_eq ctm = 
      let
        fun abs_conv2 cv = Conv.abs_conv (K (Conv.abs_conv (K cv) lthy)) lthy
        fun erase_quants ctm' =
          case (Thm.term_of ctm') of
            Const (@{const_name HOL.eq}, _) $ _ $ _ => Conv.all_conv ctm'
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
      in
        case (Thm.term_of ctm) of
          Const (@{const_name fun_rel}, _) $ _ $ _ => 
            (binop_conv2 left_conv simp_arrows_conv then_conv unfold_conv) ctm
          | _ => Conv.all_conv ctm
      end

    val unfold_ret_val_invs = Conv.bottom_conv 
      (K (Conv.try_conv (Conv.rewr_conv @{thm invariant_same_args}))) lthy 
    val simp_conv = Conv.arg_conv (Conv.fun2_conv simp_arrows_conv)
    val univq_conv = Conv.rewr_conv @{thm HOL.all_simps(6)[symmetric, THEN eq_reflection]}
    val univq_prenex_conv = Conv.top_conv (K (Conv.try_conv univq_conv)) lthy
    val beta_conv = Thm.beta_conversion true
    val eq_thm = 
      (simp_conv then_conv univq_prenex_conv then_conv beta_conv then_conv unfold_ret_val_invs) ctm
  in
    Object_Logic.rulify (eq_thm RS Drule.equal_elim_rule2)
  end



fun gen_quotient_def prep_vars prep_term (raw_var, (attr, (lhs_raw, rhs_raw))) lthy =
  let
    val (vars, ctxt) = prep_vars (the_list raw_var) lthy
    val T_opt = (case vars of [(_, SOME T, _)] => SOME T | _ => NONE)
    val lhs = prep_term T_opt ctxt lhs_raw
    val rhs = prep_term NONE ctxt rhs_raw

    val (lhs_str, lhs_ty) = dest_Free lhs handle TERM _ => error "Constant already defined."
    val _ = if null (strip_abs_vars rhs) then () else error "The definiens cannot be an abstraction"
    val _ = if is_Const rhs then () else warning "The definiens is not a constant"

    val var =
      (case vars of 
        [] => (Binding.name lhs_str, NoSyn)
      | [(binding, _, mx)] =>
          if Variable.check_name binding = lhs_str then (binding, mx)
          else error_msg binding lhs_str
      | _ => raise Match)
    
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
          SOME (Const (@{const_name HOL.eq}, _) $ _ $ _) => SOME (@{thm refl} RS thm)
          | SOME _ => (case body_type (fastype_of lhs) of
            Type (typ_name, _) => ( SOME
              (#equiv_thm (the (Quotient_Info.lookup_quotients lthy typ_name)) 
                RS @{thm Equiv_Relations.equivp_reflp} RS thm)
              handle _ => NONE)
            | _ => NONE
            )
          | _ => NONE
      end

    val rsp_rel = Quotient_Term.equiv_relation lthy (fastype_of rhs, lhs_ty)
    val internal_rsp_tm = HOLogic.mk_Trueprop (Syntax.check_term lthy (rsp_rel $ rhs $ rhs))
    val readable_rsp_thm_eq = mk_readable_rsp_thm_eq internal_rsp_tm lthy
    val maybe_proven_rsp_thm = try_to_prove_refl readable_rsp_thm_eq
    val (readable_rsp_tm, _) = Logic.dest_implies (prop_of readable_rsp_thm_eq)
  
    fun after_qed thm_list lthy = 
      let
        val internal_rsp_thm =
          case thm_list of
            [] => the maybe_proven_rsp_thm
          | [[thm]] => Goal.prove ctxt [] [] internal_rsp_tm 
            (fn _ => rtac readable_rsp_thm_eq 1 THEN Proof_Context.fact_tac [thm] 1)
      in
        snd (add_quotient_def ((var, attr), (lhs, rhs)) internal_rsp_thm lthy)
      end

  in
    case maybe_proven_rsp_thm of
      SOME _ => Proof.theorem NONE after_qed [] lthy
      | NONE =>  Proof.theorem NONE after_qed [[(readable_rsp_tm,[])]] lthy
  end

fun check_term' cnstr ctxt =
  Syntax.check_term ctxt o (case cnstr of SOME T => Type.constraint T | _ => I)

fun read_term' cnstr ctxt =
  check_term' cnstr ctxt o Syntax.parse_term ctxt

val quotient_def = gen_quotient_def Proof_Context.cert_vars check_term'
val quotient_def_cmd = gen_quotient_def Proof_Context.read_vars read_term'


(* a wrapper for automatically lifting a raw constant *)
fun lift_raw_const qtys (qconst_name, rconst, mx) ctxt =
  let
    val rty = fastype_of rconst
    val qty = Quotient_Term.derive_qtyp ctxt qtys rty
    val lhs = Free (qconst_name, qty)
  in
    (*quotient_def (SOME (Binding.name qconst_name, NONE, mx), (Attrib.empty_binding, (lhs, rconst))) ctxt*)
    ({qconst = lhs, rconst = lhs, def = @{thm refl}}, ctxt)
  end

(* parser and command *)
val quotdef_parser =
  Scan.option Parse_Spec.constdecl --
    Parse.!!! (Parse_Spec.opt_thm_name ":" -- (Parse.term --| @{keyword "is"} -- Parse.term))

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "quotient_definition"}
    "definition for constants over the quotient type"
      (quotdef_parser >> quotient_def_cmd)


end; (* structure *)
