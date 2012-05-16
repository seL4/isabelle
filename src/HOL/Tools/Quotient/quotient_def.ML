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

end;

structure Quotient_Def: QUOTIENT_DEF =
struct

(** Interface and Syntax Setup **)

(* Generation of the code certificate from the rsp theorem *)

open Lifting_Util

infix 0 MRSL

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
     
    fun qualify defname suffix = Binding.name suffix
      |> Binding.qualify true defname

    val lhs_name = Binding.name_of (#1 var)
    val rsp_thm_name = qualify lhs_name "rsp"
    
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


(* parser and command *)
val quotdef_parser =
  Scan.option Parse_Spec.constdecl --
    Parse.!!! (Parse_Spec.opt_thm_name ":" -- (Parse.term --| @{keyword "is"} -- Parse.term))

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "quotient_definition"}
    "definition for constants over the quotient type"
      (quotdef_parser >> quotient_def_cmd)


end; (* structure *)
