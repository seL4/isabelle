(*  Title:      HOL/Tools/Lifting/lifting_def.ML
    Author:     Ondrej Kuncar

Definitions for constants on quotient types.
*)

signature LIFTING_DEF =
sig
  val generate_parametric_transfer_rule:
    Proof.context -> thm -> thm -> thm

  val add_lift_def:
    (binding * mixfix) -> typ -> term -> thm -> thm list -> local_theory -> local_theory

  val lift_def_cmd:
    (binding * string option * mixfix) * string * (Facts.ref * Token.src list) list ->
    local_theory -> Proof.state

  val can_generate_code_cert: thm -> bool
end

structure Lifting_Def: LIFTING_DEF =
struct

open Lifting_Util

infix 0 MRSL

(* Reflexivity prover *)

fun mono_eq_prover ctxt prop =
  let
    val refl_rules = Lifting_Info.get_reflexivity_rules ctxt
    val transfer_rules = Transfer.get_transfer_raw ctxt
    
    fun main_tac i = (REPEAT_ALL_NEW (DETERM o resolve_tac refl_rules) THEN_ALL_NEW 
      (REPEAT_ALL_NEW (DETERM o resolve_tac transfer_rules))) i
  in
    SOME (Goal.prove ctxt [] [] prop (K (main_tac 1)))
      handle ERROR _ => NONE
  end

fun try_prove_refl_rel ctxt rel =
  let
    fun mk_ge_eq x =
      let
        val T = fastype_of x
      in
        Const (@{const_name "less_eq"}, T --> T --> HOLogic.boolT) $ 
          (Const (@{const_name HOL.eq}, T)) $ x
      end;
    val goal = HOLogic.mk_Trueprop (mk_ge_eq rel);
  in
     mono_eq_prover ctxt goal
  end;

fun try_prove_reflexivity ctxt prop =
  let
    val thy = Proof_Context.theory_of ctxt
    val cprop = cterm_of thy prop
    val rule = @{thm ge_eq_refl}
    val concl_pat = Drule.strip_imp_concl (cprop_of rule)
    val insts = Thm.first_order_match (concl_pat, cprop)
    val rule = Drule.instantiate_normalize insts rule
    val prop = hd (prems_of rule)
  in
    case mono_eq_prover ctxt prop of
      SOME thm => SOME (thm RS rule)
      | NONE => NONE
  end

(* 
  Generates a parametrized transfer rule.
  transfer_rule - of the form T t f
  parametric_transfer_rule - of the form par_R t' t
  
  Result: par_T t' f, after substituing op= for relations in par_R that relate
    a type constructor to the same type constructor, it is a merge of (par_R' OO T) t' f
    using Lifting_Term.merge_transfer_relations
*)

fun generate_parametric_transfer_rule ctxt transfer_rule parametric_transfer_rule =
  let
    fun preprocess ctxt thm =
      let
        val tm = (strip_args 2 o HOLogic.dest_Trueprop o concl_of) thm;
        val param_rel = (snd o dest_comb o fst o dest_comb) tm;
        val thy = Proof_Context.theory_of ctxt;
        val free_vars = Term.add_vars param_rel [];
        
        fun make_subst (var as (_, typ)) subst = 
          let
            val [rty, rty'] = binder_types typ
          in
            if (Term.is_TVar rty andalso is_Type rty') then
              (Var var, HOLogic.eq_const rty')::subst
            else
              subst
          end;
        
        val subst = fold make_subst free_vars [];
        val csubst = map (apply2 (cterm_of thy)) subst;
        val inst_thm = Drule.cterm_instantiate csubst thm;
      in
        Conv.fconv_rule 
          ((Conv.concl_conv (nprems_of inst_thm) o HOLogic.Trueprop_conv o Conv.fun2_conv o Conv.arg1_conv)
            (Raw_Simplifier.rewrite ctxt false (Transfer.get_sym_relator_eq ctxt))) inst_thm
      end

    fun inst_relcomppI thy ant1 ant2 =
      let
        val t1 = (HOLogic.dest_Trueprop o concl_of) ant1
        val t2 = (HOLogic.dest_Trueprop o prop_of) ant2
        val fun1 = cterm_of thy (strip_args 2 t1)
        val args1 = map (cterm_of thy) (get_args 2 t1)
        val fun2 = cterm_of thy (strip_args 2 t2)
        val args2 = map (cterm_of thy) (get_args 1 t2)
        val relcomppI = Drule.incr_indexes2 ant1 ant2 @{thm relcomppI}
        val vars = (rev (Term.add_vars (prop_of relcomppI) []))
        val subst = map (apfst ((cterm_of thy) o Var)) (vars ~~ ([fun1] @ args1 @ [fun2] @ args2))
      in
        Drule.cterm_instantiate subst relcomppI
      end

    fun zip_transfer_rules ctxt thm =
      let
        val thy = Proof_Context.theory_of ctxt
        fun mk_POS ty = Const (@{const_name POS}, ty --> ty --> HOLogic.boolT)
        val rel = (Thm.dest_fun2 o Thm.dest_arg o cprop_of) thm
        val typ = (typ_of o ctyp_of_term) rel
        val POS_const = cterm_of thy (mk_POS typ)
        val var = cterm_of thy (Var (("X", #maxidx (rep_cterm (rel)) + 1), typ))
        val goal = Thm.apply (cterm_of thy HOLogic.Trueprop) (Thm.apply (Thm.apply POS_const rel) var)
      in
        [Lifting_Term.merge_transfer_relations ctxt goal, thm] MRSL @{thm POS_apply}
      end
     
    val thm = (inst_relcomppI (Proof_Context.theory_of ctxt) parametric_transfer_rule transfer_rule) 
                OF [parametric_transfer_rule, transfer_rule]
    val preprocessed_thm = preprocess ctxt thm
    val orig_ctxt = ctxt
    val (fixed_thm, ctxt) = yield_singleton (apfst snd oo Variable.import true) preprocessed_thm ctxt
    val assms = cprems_of fixed_thm
    val add_transfer_rule = Thm.attribute_declaration Transfer.transfer_add
    val (prems, ctxt) = fold_map Thm.assume_hyps assms ctxt
    val ctxt = Context.proof_map (fold add_transfer_rule prems) ctxt
    val zipped_thm =
      fixed_thm
      |> undisch_all
      |> zip_transfer_rules ctxt
      |> implies_intr_list assms
      |> singleton (Variable.export ctxt orig_ctxt)
  in
    zipped_thm
  end

fun print_generate_transfer_info msg = 
  let
    val error_msg = cat_lines 
      ["Generation of a parametric transfer rule failed.",
      (Pretty.string_of (Pretty.block
         [Pretty.str "Reason:", Pretty.brk 2, msg]))]
  in
    error error_msg
  end

fun map_ter _ x [] = x
    | map_ter f _ xs = map f xs

fun generate_transfer_rules lthy quot_thm rsp_thm def_thm par_thms =
  let
    val transfer_rule =
      ([quot_thm, rsp_thm, def_thm] MRSL @{thm Quotient_to_transfer})
      |> Lifting_Term.parametrize_transfer_rule lthy
  in
    (map_ter (generate_parametric_transfer_rule lthy transfer_rule) [transfer_rule] par_thms
    handle Lifting_Term.MERGE_TRANSFER_REL msg => (print_generate_transfer_info msg; [transfer_rule]))
  end

(* Generation of the code certificate from the rsp theorem *)

fun get_body_types (Type ("fun", [_, U]), Type ("fun", [_, V])) = get_body_types (U, V)
  | get_body_types (U, V)  = (U, V)

fun get_binder_types (Type ("fun", [T, U]), Type ("fun", [V, W])) = (T, V) :: get_binder_types (U, W)
  | get_binder_types _ = []

fun get_binder_types_by_rel (Const (@{const_name "rel_fun"}, _) $ _ $ S) (Type ("fun", [T, U]), Type ("fun", [V, W])) = 
    (T, V) :: get_binder_types_by_rel S (U, W)
  | get_binder_types_by_rel _ _ = []

fun get_body_type_by_rel (Const (@{const_name "rel_fun"}, _) $ _ $ S) (Type ("fun", [_, U]), Type ("fun", [_, V])) = 
    get_body_type_by_rel S (U, V)
  | get_body_type_by_rel _ (U, V)  = (U, V)

fun get_binder_rels (Const (@{const_name "rel_fun"}, _) $ R $ S) = R :: get_binder_rels S
  | get_binder_rels _ = []

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
    | Const (@{const_name eq_onp}, _) $ _  => true
    | _ => false

fun generate_rep_eq ctxt def_thm rsp_thm (rty, qty) =
  let
    val unfolded_def = Conv.fconv_rule (Conv.arg_conv unfold_fun_maps_beta) def_thm
    val unabs_def = unabs_all_def ctxt unfolded_def
  in  
    if body_type rty = body_type qty then 
      SOME (simplify_code_eq ctxt (unabs_def RS @{thm meta_eq_to_obj_eq}))
    else 
      let
        val thy = Proof_Context.theory_of ctxt
        val quot_thm = Lifting_Term.prove_quot_thm ctxt (get_body_types (rty, qty))
        val rel_fun = prove_rel ctxt rsp_thm (rty, qty)
        val rep_abs_thm = [quot_thm, rel_fun] MRSL @{thm Quotient_rep_abs_eq}
      in
        case mono_eq_prover ctxt (hd(prems_of rep_abs_thm)) of
          SOME mono_eq_thm =>
            let
              val rep_abs_eq = mono_eq_thm RS rep_abs_thm
              val rep = (cterm_of thy o quot_thm_rep) quot_thm
              val rep_refl = Thm.reflexive rep RS @{thm meta_eq_to_obj_eq}
              val repped_eq = [rep_refl, unabs_def RS @{thm meta_eq_to_obj_eq}] MRSL @{thm cong}
              val code_cert = [repped_eq, rep_abs_eq] MRSL trans
            in
              SOME (simplify_code_eq ctxt code_cert)
            end
          | NONE => NONE
      end
  end

fun generate_abs_eq ctxt def_thm rsp_thm quot_thm =
  let
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
        |> fold (fn _ => fn thm => thm RS @{thm rel_funD2}) ty_args
        |> (fn x => x RS (@{thm Quotient_rel_abs2} OF [quot_ret_thm]))
      end
    
    val prem_rels = get_binder_rels (quot_thm_rel quot_thm);
    val proved_assms = prem_rels |> map (try_prove_refl_rel ctxt) 
      |> map_index (apfst (fn x => x + 1)) |> filter (is_some o snd) |> map (apsnd the) 
      |> map (apsnd (fn assm => assm RS @{thm ge_eq_refl}))
    val abs_eq = fold_rev (fn (i, assm) => fn thm => assm RSN (i, thm)) proved_assms abs_eq_with_assms
  in
    simplify_code_eq ctxt abs_eq
  end


fun register_code_eq_thy abs_eq_thm opt_rep_eq_thm (rty, qty) thy =
  let
    fun no_abstr (t $ u) = no_abstr t andalso no_abstr u
      | no_abstr (Abs (_, _, t)) = no_abstr t
      | no_abstr (Const (name, _)) = not (Code.is_abstr thy name)
      | no_abstr _ = true
    fun is_valid_eq eqn = can (Code.assert_eqn thy) (mk_meta_eq eqn, true) 
      andalso no_abstr (prop_of eqn)
    fun is_valid_abs_eq abs_eq = can (Code.assert_abs_eqn thy NONE) (mk_meta_eq abs_eq)

  in
    if is_valid_eq abs_eq_thm then
      Code.add_default_eqn abs_eq_thm thy
    else
      let
        val (rty_body, qty_body) = get_body_types (rty, qty)
      in
        if rty_body = qty_body then
         Code.add_default_eqn (the opt_rep_eq_thm) thy
        else
          if is_some opt_rep_eq_thm andalso is_valid_abs_eq (the opt_rep_eq_thm)
          then
            Code.add_abs_default_eqn (the opt_rep_eq_thm) thy
          else
            thy
      end
  end

local
  fun encode_code_eq thy abs_eq opt_rep_eq (rty, qty) = 
    let
      fun mk_type typ = typ |> Logic.mk_type |> cterm_of thy |> Drule.mk_term
    in
      Conjunction.intr_balanced [abs_eq, (the_default TrueI opt_rep_eq), mk_type rty, mk_type qty]
    end
  
  exception DECODE
    
  fun decode_code_eq thm =
    if nprems_of thm > 0 then raise DECODE 
    else
      let
        val [abs_eq, rep_eq, rty, qty] = Conjunction.elim_balanced 4 thm
        val opt_rep_eq = if Thm.eq_thm_prop (rep_eq, TrueI) then NONE else SOME rep_eq
        fun dest_type typ = typ |> Drule.dest_term |> term_of |> Logic.dest_type
      in
        (abs_eq, opt_rep_eq, (dest_type rty, dest_type qty)) 
      end
  
  fun register_encoded_code_eq thm thy =
    let
      val (abs_eq_thm, opt_rep_eq_thm, (rty, qty)) = decode_code_eq thm
    in
      register_code_eq_thy abs_eq_thm opt_rep_eq_thm (rty, qty) thy
    end
    handle DECODE => thy
  
  val register_code_eq_attribute = Thm.declaration_attribute
    (fn thm => Context.mapping (register_encoded_code_eq thm) I)
  val register_code_eq_attrib = Attrib.internal (K register_code_eq_attribute)

  fun no_no_code ctxt (rty, qty) =
    if same_type_constrs (rty, qty) then
      forall (no_no_code ctxt) (Targs rty ~~ Targs qty)
    else
      if is_Type qty then
        if Lifting_Info.is_no_code_type ctxt (Tname qty) then false
        else 
          let 
            val (rty', rtyq) = Lifting_Term.instantiate_rtys ctxt (rty, qty)
            val (rty's, rtyqs) = (Targs rty', Targs rtyq)
          in
            forall (no_no_code ctxt) (rty's ~~ rtyqs)
          end
      else
        true
in

fun register_code_eq abs_eq_thm opt_rep_eq_thm (rty, qty) lthy =
  let
    val thy = Proof_Context.theory_of lthy
    val encoded_code_eq = encode_code_eq thy abs_eq_thm opt_rep_eq_thm (rty, qty)
  in
    if no_no_code lthy (rty, qty) then 
      (snd oo Local_Theory.note) ((Binding.empty, [register_code_eq_attrib]), [encoded_code_eq]) lthy
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
  par_thms - a parametricity theorem for rhs
*)

fun add_lift_def var qty rhs rsp_thm par_thms lthy =
  let
    val rty = fastype_of rhs
    val quot_thm = Lifting_Term.prove_quot_thm lthy (rty, qty)
    val absrep_trm =  quot_thm_abs quot_thm
    val rty_forced = (domain_type o fastype_of) absrep_trm
    val forced_rhs = force_rty_type lthy rty_forced rhs
    val lhs = Free (Binding.name_of (#1 var), qty)
    val prop = Logic.mk_equals (lhs, absrep_trm $ forced_rhs)
    val (_, prop') = Local_Defs.cert_def lthy prop
    val (_, newrhs) = Local_Defs.abs_def prop'

    val ((_, (_ , def_thm)), lthy') = 
      Local_Theory.define (var, ((Thm.def_binding (#1 var), []), newrhs)) lthy

    val transfer_rules = generate_transfer_rules lthy' quot_thm rsp_thm def_thm par_thms

    val abs_eq_thm = generate_abs_eq lthy' def_thm rsp_thm quot_thm
    val opt_rep_eq_thm = generate_rep_eq lthy' def_thm rsp_thm (rty_forced, qty)

    fun qualify defname suffix = Binding.qualified true suffix defname

    val lhs_name = (#1 var)
    val rsp_thm_name = qualify lhs_name "rsp"
    val abs_eq_thm_name = qualify lhs_name "abs_eq"
    val rep_eq_thm_name = qualify lhs_name "rep_eq"
    val transfer_rule_name = qualify lhs_name "transfer"
    val transfer_attr = Attrib.internal (K Transfer.transfer_add)
  in
    lthy'
      |> (snd oo Local_Theory.note) ((rsp_thm_name, []), [rsp_thm])
      |> (snd oo Local_Theory.note) ((transfer_rule_name, [transfer_attr]), transfer_rules)
      |> (snd oo Local_Theory.note) ((abs_eq_thm_name, []), [abs_eq_thm])
      |> (case opt_rep_eq_thm of 
            SOME rep_eq_thm => (snd oo Local_Theory.note) ((rep_eq_thm_name, []), [rep_eq_thm])
            | NONE => I)
      |> register_code_eq abs_eq_thm opt_rep_eq_thm (rty_forced, qty)
  end

local
  val eq_onp_assms_tac_fixed_rules = map (Transfer.prep_transfer_domain_thm @{context})
    [@{thm pcr_Domainp_total}, @{thm pcr_Domainp_par_left_total}, @{thm pcr_Domainp_par}, 
      @{thm pcr_Domainp}]
in
fun mk_readable_rsp_thm_eq tm lthy =
  let
    val ctm = cterm_of (Proof_Context.theory_of lthy) tm
    
    fun assms_rewr_conv tactic rule ct =
      let
        fun prove_extra_assms thm =
          let
            val assms = cprems_of thm
            fun finish thm = if Thm.no_prems thm then SOME (Goal.conclude thm) else NONE
            fun prove ctm = Option.mapPartial finish (SINGLE tactic (Goal.init ctm))
          in
            map_interrupt prove assms
          end
    
        fun cconl_of thm = Drule.strip_imp_concl (cprop_of thm)
        fun lhs_of thm = fst (Thm.dest_equals (cconl_of thm))
        fun rhs_of thm = snd (Thm.dest_equals (cconl_of thm))
        val rule1 = Thm.incr_indexes (#maxidx (Thm.rep_cterm ct) + 1) rule;
        val lhs = lhs_of rule1;
        val rule2 = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule1;
        val rule3 =
          Thm.instantiate (Thm.match (lhs, ct)) rule2
            handle Pattern.MATCH => raise CTERM ("assms_rewr_conv", [lhs, ct]);
        val proved_assms = prove_extra_assms rule3
      in
        case proved_assms of
          SOME proved_assms =>
            let
              val rule3 = proved_assms MRSL rule3
              val rule4 =
                if lhs_of rule3 aconvc ct then rule3
                else
                  let val ceq = Thm.dest_fun2 (Thm.cprop_of rule3)
                  in rule3 COMP Thm.trivial (Thm.mk_binop ceq ct (rhs_of rule3)) end
            in Thm.transitive rule4 (Thm.beta_conversion true (rhs_of rule4)) end
          | NONE => Conv.no_conv ct
      end

    fun assms_rewrs_conv tactic rules = Conv.first_conv (map (assms_rewr_conv tactic) rules)

    fun simp_arrows_conv ctm =
      let
        val unfold_conv = Conv.rewrs_conv 
          [@{thm rel_fun_eq_eq_onp[THEN eq_reflection]}, 
            @{thm rel_fun_eq_onp_rel[THEN eq_reflection]},
            @{thm rel_fun_eq[THEN eq_reflection]},
            @{thm rel_fun_eq_rel[THEN eq_reflection]}, 
            @{thm rel_fun_def[THEN eq_reflection]}]
        fun binop_conv2 cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2
        val eq_onp_assms_tac_rules = @{thm left_unique_OO} :: 
            eq_onp_assms_tac_fixed_rules @ (Transfer.get_transfer_raw lthy)
        val eq_onp_assms_tac = (TRY o REPEAT_ALL_NEW (resolve_tac eq_onp_assms_tac_rules) 
          THEN_ALL_NEW (DETERM o Transfer.eq_tac lthy)) 1
        val relator_eq_onp_conv = Conv.bottom_conv
          (K (Conv.try_conv (assms_rewrs_conv eq_onp_assms_tac
            (Lifting_Info.get_relator_eq_onp_rules lthy)))) lthy
        val relator_eq_conv = Conv.bottom_conv
          (K (Conv.try_conv (Conv.rewrs_conv (Transfer.get_relator_eq lthy)))) lthy
      in
        case (Thm.term_of ctm) of
          Const (@{const_name "rel_fun"}, _) $ _ $ _ => 
            (binop_conv2 simp_arrows_conv simp_arrows_conv then_conv unfold_conv) ctm
          | _ => (relator_eq_onp_conv then_conv relator_eq_conv) ctm
      end
    
    val unfold_ret_val_invs = Conv.bottom_conv 
      (K (Conv.try_conv (Conv.rewr_conv @{thm eq_onp_same_args[THEN eq_reflection]}))) lthy
    val unfold_inv_conv = 
      Conv.top_sweep_conv (K (Conv.rewr_conv @{thm eq_onp_def[THEN eq_reflection]})) lthy
    val simp_conv = HOLogic.Trueprop_conv (Conv.fun2_conv simp_arrows_conv)
    val univq_conv = Conv.rewr_conv @{thm HOL.all_simps(6)[symmetric, THEN eq_reflection]}
    val univq_prenex_conv = Conv.top_conv (K (Conv.try_conv univq_conv)) lthy
    val beta_conv = Thm.beta_conversion true
    val eq_thm = 
      (simp_conv then_conv univq_prenex_conv then_conv beta_conv then_conv unfold_ret_val_invs
         then_conv unfold_inv_conv) ctm
  in
    Object_Logic.rulify lthy (eq_thm RS Drule.equal_elim_rule2)
  end
end

fun rename_to_tnames ctxt term =
  let
    fun all_typs (Const (@{const_name Pure.all}, _) $ Abs (_, T, t)) = T :: all_typs t
      | all_typs _ = []

    fun rename (Const (@{const_name Pure.all}, T1) $ Abs (_, T2, t)) (new_name :: names) = 
        (Const (@{const_name Pure.all}, T1) $ Abs (new_name, T2, rename t names)) 
      | rename t _ = t

    val (fixed_def_t, _) = yield_singleton (Variable.importT_terms) term ctxt
    val new_names = Old_Datatype_Prop.make_tnames (all_typs fixed_def_t)
  in
    rename term new_names
  end

(* This is not very cheap way of getting the rules but we have only few active
  liftings in the current setting *)
fun get_cr_pcr_eqs ctxt =
  let
    fun collect (data : Lifting_Info.quotient) l =
      if is_some (#pcr_info data) 
      then ((Thm.symmetric o safe_mk_meta_eq o #pcr_cr_eq o the o #pcr_info) data :: l) 
      else l
    val table = Lifting_Info.get_quotients ctxt
  in
    Symtab.fold (fn (_, data) => fn l => collect data l) table []
  end

(*

  lifting_definition command. It opens a proof of a corresponding respectfulness 
  theorem in a user-friendly, readable form. Then add_lift_def is called internally.

*)

fun lift_def_cmd (raw_var, rhs_raw, par_xthms) lthy =
  let
    val ((binding, SOME qty, mx), lthy) = yield_singleton Proof_Context.read_vars raw_var lthy 
    val rhs = (Syntax.check_term lthy o Syntax.parse_term lthy) rhs_raw
    val rsp_rel = Lifting_Term.equiv_relation lthy (fastype_of rhs, qty)
    val rty_forced = (domain_type o fastype_of) rsp_rel;
    val forced_rhs = force_rty_type lthy rty_forced rhs;
    val cr_to_pcr_conv = HOLogic.Trueprop_conv (Conv.fun2_conv 
      (Raw_Simplifier.rewrite lthy false (get_cr_pcr_eqs lthy)))
    val (prsp_tm, rsp_prsp_eq) = HOLogic.mk_Trueprop (rsp_rel $ forced_rhs $ forced_rhs)
      |> cterm_of (Proof_Context.theory_of lthy)
      |> cr_to_pcr_conv
      |> ` concl_of
      |>> Logic.dest_equals
      |>> snd
    val to_rsp = rsp_prsp_eq RS Drule.equal_elim_rule2
    val opt_proven_rsp_thm = try_prove_reflexivity lthy prsp_tm
    val par_thms = Attrib.eval_thms lthy par_xthms
    
    fun after_qed internal_rsp_thm lthy = 
      add_lift_def (binding, mx) qty rhs (internal_rsp_thm RS to_rsp) par_thms lthy
  in
    case opt_proven_rsp_thm of
      SOME thm => Proof.theorem NONE (K (after_qed thm)) [] lthy
      | NONE =>  
        let
          val readable_rsp_thm_eq = mk_readable_rsp_thm_eq prsp_tm lthy
          val (readable_rsp_tm, _) = Logic.dest_implies (prop_of readable_rsp_thm_eq)
          val readable_rsp_tm_tnames = rename_to_tnames lthy readable_rsp_tm
      
          fun after_qed' thm_list lthy = 
            let
              val internal_rsp_thm = Goal.prove lthy [] [] prsp_tm 
                  (fn {context = ctxt, ...} =>
                    rtac readable_rsp_thm_eq 1 THEN Proof_Context.fact_tac ctxt (hd thm_list) 1)
            in
              after_qed internal_rsp_thm lthy
            end
        in
          Proof.theorem NONE after_qed' [[(readable_rsp_tm_tnames,[])]] lthy
        end 
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
          Pretty.str "The type of the term cannot be instantiated to",
          Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt rty_forced),
          Pretty.str "."]))]
    in
      error error_msg
    end

fun lift_def_cmd_with_err_handling (raw_var, rhs_raw, par_xthms) lthy =
  (lift_def_cmd (raw_var, rhs_raw, par_xthms) lthy
    handle Lifting_Term.QUOT_THM (rty, qty, msg) => quot_thm_err lthy (rty, qty) msg)
    handle Lifting_Term.CHECK_RTY (rty_schematic, rty_forced) => 
      check_rty_err lthy (rty_schematic, rty_forced) (raw_var, rhs_raw)

(* parser and command *)
val liftdef_parser =
  (((Parse.binding -- (@{keyword "::"} |-- (Parse.typ >> SOME) -- Parse.opt_mixfix')) >> Parse.triple2)
    --| @{keyword "is"} -- Parse.term -- 
      Scan.optional (@{keyword "parametric"} |-- Parse.!!! Parse.xthms1) []) >> Parse.triple1
val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "lift_definition"}
    "definition for constants over the quotient type"
      (liftdef_parser >> lift_def_cmd_with_err_handling)


end (* structure *)
