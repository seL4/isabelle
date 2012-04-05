(*  Title:      HOL/Tools/Lifting/lifting_def.ML
    Author:     Ondrej Kuncar

Definitions for constants on quotient types.
*)

signature LIFTING_DEF =
sig
  exception FORCE_RTY of typ * term

  val add_lift_def:
    (binding * mixfix) -> typ -> term -> thm -> local_theory -> local_theory

  val lift_def_cmd:
    (binding * string option * mixfix) * string -> local_theory -> Proof.state

  val can_generate_code_cert: thm -> bool
end;

structure Lifting_Def: LIFTING_DEF =
struct

(** Interface and Syntax Setup **)

(* Generation of the code certificate from the rsp theorem *)

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

exception FORCE_RTY of typ * term

fun get_body_types (Type ("fun", [_, U]), Type ("fun", [_, V])) = get_body_types (U, V)
  | get_body_types (U, V)  = (U, V)

fun get_binder_types (Type ("fun", [T, U]), Type ("fun", [V, W])) = (T, V) :: get_binder_types (U, W)
  | get_binder_types _ = []

fun force_rty_type ctxt rty rhs = 
  let
    val thy = Proof_Context.theory_of ctxt
    val rhs_schematic = singleton (Variable.polymorphic ctxt) rhs
    val rty_schematic = fastype_of rhs_schematic
    val match = Sign.typ_match thy (rty_schematic, rty) Vartab.empty
      handle Type.TYPE_MATCH => raise FORCE_RTY (rty, rhs)
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
    val try_beta_conv = Conv.try_conv (Thm.beta_conversion false)
  in
    (Conv.arg_conv (Conv.fun_conv unfold_conv then_conv try_beta_conv)) ctm
  end

fun prove_rel ctxt rsp_thm (rty, qty) =
  let
    val ty_args = get_binder_types (rty, qty)
    fun disch_arg args_ty thm = 
      let
        val quot_thm = Lifting_Term.prove_quot_theorem ctxt args_ty
      in
        [quot_thm, thm] MRSL @{thm apply_rsp''}
      end
  in
    fold disch_arg ty_args rsp_thm
  end

exception CODE_CERT_GEN of string

fun simplify_code_eq ctxt def_thm = 
  Local_Defs.unfold ctxt [@{thm o_def}, @{thm map_fun_def}, @{thm id_def}] def_thm

fun can_generate_code_cert quot_thm  =
  case Lifting_Term.quot_thm_rel quot_thm of
    Const (@{const_name HOL.eq}, _) => true
    | Const (@{const_name invariant}, _) $ _  => true
    | _ => false

fun generate_code_cert ctxt def_thm rsp_thm (rty, qty) =
  let
    val thy = Proof_Context.theory_of ctxt
    val quot_thm = Lifting_Term.prove_quot_theorem ctxt (get_body_types (rty, qty))
    val fun_rel = prove_rel ctxt rsp_thm (rty, qty)
    val abs_rep_thm = [quot_thm, fun_rel] MRSL @{thm Quotient_rep_abs}
    val abs_rep_eq = 
      case (HOLogic.dest_Trueprop o prop_of) fun_rel of
        Const (@{const_name HOL.eq}, _) $ _ $ _ => abs_rep_thm
        | Const (@{const_name invariant}, _) $ _ $ _ $ _ => abs_rep_thm RS @{thm invariant_to_eq}
        | _ => raise CODE_CERT_GEN "relation is neither equality nor invariant"
    val unfolded_def = Conv.fconv_rule unfold_fun_maps def_thm
    val unabs_def = unabs_all_def ctxt unfolded_def
    val rep = (cterm_of thy o Lifting_Term.quot_thm_rep) quot_thm
    val rep_refl = Thm.reflexive rep RS @{thm meta_eq_to_obj_eq}
    val repped_eq = [rep_refl, unabs_def RS @{thm meta_eq_to_obj_eq}] MRSL @{thm cong}
    val code_cert = [repped_eq, abs_rep_eq] MRSL @{thm trans}
  in
    simplify_code_eq ctxt code_cert
  end

fun define_code_cert code_eqn_thm_name def_thm rsp_thm (rty, qty) lthy = 
  let
    val quot_thm = Lifting_Term.prove_quot_theorem lthy (get_body_types (rty, qty))
  in
    if can_generate_code_cert quot_thm then
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


fun add_lift_def var qty rhs rsp_thm lthy =
  let
    val rty = fastype_of rhs
    val quotient_thm = Lifting_Term.prove_quot_theorem lthy (rty, qty)
    val absrep_trm =  Lifting_Term.quot_thm_abs quotient_thm
    val rty_forced = (domain_type o fastype_of) absrep_trm
    val forced_rhs = force_rty_type lthy rty_forced rhs
    val lhs = Free (Binding.print (#1 var), qty)
    val prop = Logic.mk_equals (lhs, absrep_trm $ forced_rhs)
    val (_, prop') = Local_Defs.cert_def lthy prop
    val (_, newrhs) = Local_Defs.abs_def prop'

    val ((_, (_ , def_thm)), lthy') = 
      Local_Theory.define (var, ((Thm.def_binding (#1 var), []), newrhs)) lthy

    val transfer_thm = [quotient_thm, rsp_thm, def_thm] MRSL @{thm Quotient_to_transfer}

    fun qualify defname suffix = Binding.name suffix
      |> Binding.qualify true defname

    val lhs_name = Binding.name_of (#1 var)
    val rsp_thm_name = qualify lhs_name "rsp"
    val code_eqn_thm_name = qualify lhs_name "rep_eq"
    val transfer_thm_name = qualify lhs_name "transfer"
    val transfer_attr = Attrib.internal (K Transfer.transfer_add)
  in
    lthy'
      |> (snd oo Local_Theory.note) ((rsp_thm_name, []), [rsp_thm])
      |> (snd oo Local_Theory.note) ((transfer_thm_name, [transfer_attr]), [transfer_thm])
      |> define_code code_eqn_thm_name def_thm rsp_thm (rty_forced, qty)
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
      in
        case (Thm.term_of ctm) of
          Const (@{const_name "fun_rel"}, _) $ _ $ _ => 
            (binop_conv2  left_conv simp_arrows_conv then_conv unfold_conv) ctm
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
    Object_Logic.rulify(eq_thm RS Drule.equal_elim_rule2)
  end



fun lift_def_cmd (raw_var, rhs_raw) lthy =
  let
    val ((binding, SOME qty, mx), ctxt) = yield_singleton Proof_Context.read_vars raw_var lthy 
    val rhs = (Syntax.check_term ctxt o Syntax.parse_term ctxt) rhs_raw
 
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

    val rsp_rel = Lifting_Term.equiv_relation lthy (fastype_of rhs, qty)
    val rty_forced = (domain_type o fastype_of) rsp_rel;
    val forced_rhs = force_rty_type lthy rty_forced rhs;
    val internal_rsp_tm = HOLogic.mk_Trueprop (rsp_rel $ forced_rhs $ forced_rhs)
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
        add_lift_def (binding, mx) qty rhs internal_rsp_thm lthy
      end

  in
    case maybe_proven_rsp_thm of
      SOME _ => Proof.theorem NONE after_qed [] lthy
      | NONE =>  Proof.theorem NONE after_qed [[(readable_rsp_tm,[])]] lthy
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

fun force_rty_err ctxt rty rhs =
  let
    val error_msg = cat_lines
       ["Lifting failed for the following term:",
        Pretty.string_of (Pretty.block
         [Pretty.str "Term:", Pretty.brk 2, Syntax.pretty_term ctxt rhs]),
        Pretty.string_of (Pretty.block
         [Pretty.str "Type:", Pretty.brk 2, Syntax.pretty_typ ctxt (fastype_of rhs)]),
        "",
        (Pretty.string_of (Pretty.block
         [Pretty.str "Reason:", 
          Pretty.brk 2, 
          Pretty.str "The type of the term cannot be instancied to",
          Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt rty),
          Pretty.str "."]))]
    in
      error error_msg
    end

fun lift_def_cmd_with_err_handling (raw_var, rhs_raw) lthy =
  (lift_def_cmd (raw_var, rhs_raw) lthy
    handle Lifting_Term.QUOT_THM (rty, qty, msg) => quot_thm_err lthy (rty, qty) msg)
    handle FORCE_RTY (rty, rhs) => force_rty_err lthy rty rhs

(* parser and command *)
val liftdef_parser =
  ((Parse.binding -- (@{keyword "::"} |-- (Parse.typ >> SOME) -- Parse.opt_mixfix')) >> Parse.triple2)
    --| @{keyword "is"} -- Parse.term

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "lift_definition"}
    "definition for constants over the quotient type"
      (liftdef_parser >> lift_def_cmd_with_err_handling)


end; (* structure *)
