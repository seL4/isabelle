(*  Title:      HOL/Tools/Lifting/lifting_def.ML
    Author:     Ondrej Kuncar

Definitions for constants on quotient types.
*)

signature LIFTING_DEF =
sig
  datatype code_eq = UNKNOWN_EQ | NONE_EQ | ABS_EQ | REP_EQ
  type lift_def
  val rty_of_lift_def: lift_def -> typ
  val qty_of_lift_def: lift_def -> typ
  val rhs_of_lift_def: lift_def -> term
  val lift_const_of_lift_def: lift_def -> term
  val def_thm_of_lift_def: lift_def -> thm
  val rsp_thm_of_lift_def: lift_def -> thm
  val abs_eq_of_lift_def: lift_def -> thm
  val rep_eq_of_lift_def: lift_def -> thm option
  val code_eq_of_lift_def: lift_def -> code_eq
  val transfer_rules_of_lift_def: lift_def -> thm list
  val morph_lift_def: morphism -> lift_def -> lift_def
  val inst_of_lift_def: Proof.context -> typ -> lift_def -> lift_def
  val mk_lift_const_of_lift_def: typ -> lift_def -> term

  type config = { notes: bool }
  val map_config: (bool -> bool) -> config -> config
  val default_config: config

  val generate_parametric_transfer_rule:
    Proof.context -> thm -> thm -> thm

  val add_lift_def:
    config -> binding * mixfix -> typ -> term -> thm -> thm list -> local_theory ->
      lift_def * local_theory

  val prepare_lift_def:
    (binding * mixfix -> typ -> term -> thm -> thm list -> Proof.context ->
      lift_def * local_theory) ->
    binding * mixfix -> typ -> term -> thm list -> local_theory ->
    term option * (thm -> Proof.context -> lift_def * local_theory)

  val gen_lift_def:
    (binding * mixfix -> typ -> term -> thm -> thm list -> local_theory ->
      lift_def * local_theory) ->
    binding * mixfix -> typ -> term -> (Proof.context -> tactic) -> thm list ->
    local_theory -> lift_def * local_theory

  val lift_def:
    config -> binding * mixfix -> typ -> term -> (Proof.context -> tactic) -> thm list ->
    local_theory -> lift_def * local_theory

  val can_generate_code_cert: thm -> bool
end

structure Lifting_Def: LIFTING_DEF =
struct

open Lifting_Util

infix 0 MRSL

datatype code_eq = UNKNOWN_EQ | NONE_EQ | ABS_EQ | REP_EQ

datatype lift_def = LIFT_DEF of {
  rty: typ,
  qty: typ,
  rhs: term,
  lift_const: term,
  def_thm: thm,
  rsp_thm: thm,
  abs_eq: thm,
  rep_eq: thm option,
  code_eq: code_eq,
  transfer_rules: thm list
};

fun rep_lift_def (LIFT_DEF lift_def) = lift_def;
val rty_of_lift_def = #rty o rep_lift_def;
val qty_of_lift_def = #qty o rep_lift_def;
val rhs_of_lift_def = #rhs o rep_lift_def;
val lift_const_of_lift_def = #lift_const o rep_lift_def;
val def_thm_of_lift_def = #def_thm o rep_lift_def;
val rsp_thm_of_lift_def = #rsp_thm o rep_lift_def;
val abs_eq_of_lift_def = #abs_eq o rep_lift_def;
val rep_eq_of_lift_def = #rep_eq o rep_lift_def;
val code_eq_of_lift_def = #code_eq o rep_lift_def;
val transfer_rules_of_lift_def = #transfer_rules o rep_lift_def;

fun mk_lift_def rty qty rhs lift_const def_thm rsp_thm abs_eq rep_eq code_eq transfer_rules =
  LIFT_DEF {rty = rty, qty = qty,
            rhs = rhs, lift_const = lift_const,
            def_thm = def_thm, rsp_thm = rsp_thm, abs_eq = abs_eq, rep_eq = rep_eq,
            code_eq = code_eq, transfer_rules = transfer_rules };

fun map_lift_def f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
  (LIFT_DEF {rty = rty, qty = qty, rhs = rhs, lift_const = lift_const,
  def_thm = def_thm, rsp_thm = rsp_thm, abs_eq = abs_eq, rep_eq = rep_eq, code_eq = code_eq,
  transfer_rules = transfer_rules }) =
  LIFT_DEF {rty = f1 rty, qty = f2 qty, rhs = f3 rhs, lift_const = f4 lift_const,
            def_thm = f5 def_thm, rsp_thm = f6 rsp_thm, abs_eq = f7 abs_eq, rep_eq = f8 rep_eq,
            code_eq = f9 code_eq, transfer_rules = f10 transfer_rules }

fun morph_lift_def phi =
  let
    val mtyp = Morphism.typ phi
    val mterm = Morphism.term phi
    val mthm = Morphism.thm phi
  in
    map_lift_def mtyp mtyp mterm mterm mthm mthm mthm (Option.map mthm) I (map mthm)
  end

fun mk_inst_of_lift_def qty lift_def = Vartab.empty |> Type.raw_match (qty_of_lift_def lift_def, qty)

fun mk_lift_const_of_lift_def qty lift_def = Envir.subst_term_types (mk_inst_of_lift_def qty lift_def)
  (lift_const_of_lift_def lift_def)

fun inst_of_lift_def ctxt qty lift_def =
  let
    val instT =
      Vartab.fold (fn (a, (S, T)) => cons ((a, S), Thm.ctyp_of ctxt T))
        (mk_inst_of_lift_def qty lift_def) []
    val phi = Morphism.instantiate_morphism (TVars.make instT, Vars.empty)
  in morph_lift_def phi lift_def end


(* Config *)

type config = { notes: bool };
fun map_config f1 { notes = notes } = { notes = f1 notes }
val default_config = { notes = true };

(* Reflexivity prover *)

fun mono_eq_prover ctxt prop =
  let
    val refl_rules = Lifting_Info.get_reflexivity_rules ctxt
    val transfer_rules = Transfer.get_transfer_raw ctxt

    fun main_tac i = (REPEAT_ALL_NEW (DETERM o resolve_tac ctxt refl_rules) THEN_ALL_NEW
      (REPEAT_ALL_NEW (DETERM o resolve_tac ctxt transfer_rules))) i
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
        Const (\<^const_name>\<open>less_eq\<close>, T --> T --> HOLogic.boolT) $
          (Const (\<^const_name>\<open>HOL.eq\<close>, T)) $ x
      end;
    val goal = HOLogic.mk_Trueprop (mk_ge_eq rel);
  in
     mono_eq_prover ctxt goal
  end;

fun try_prove_reflexivity ctxt prop =
  let
    val cprop = Thm.cterm_of ctxt prop
    val rule = @{thm ge_eq_refl}
    val concl_pat = Drule.strip_imp_concl (Thm.cprop_of rule)
    val insts = Thm.first_order_match (concl_pat, cprop)
    val rule = Drule.instantiate_normalize insts rule
    val prop = hd (Thm.prems_of rule)
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

fun generate_parametric_transfer_rule ctxt0 transfer_rule parametric_transfer_rule =
  let
    fun preprocess ctxt thm =
      let
        val tm = (strip_args 2 o HOLogic.dest_Trueprop o Thm.concl_of) thm;
        val param_rel = (snd o dest_comb o fst o dest_comb) tm;
        val free_vars = Term.add_vars param_rel [];

        fun make_subst (xi, typ) subst =
          let
            val [rty, rty'] = binder_types typ
          in
            if Term.is_TVar rty andalso Term.is_Type rty' then
              (xi, Thm.cterm_of ctxt (HOLogic.eq_const rty')) :: subst
            else
              subst
          end;

        val inst_thm = infer_instantiate ctxt (fold make_subst free_vars []) thm;
      in
        Conv.fconv_rule
          ((Conv.concl_conv (Thm.nprems_of inst_thm) o
            HOLogic.Trueprop_conv o Conv.fun2_conv o Conv.arg1_conv)
            (Raw_Simplifier.rewrite ctxt false (Transfer.get_sym_relator_eq ctxt))) inst_thm
      end

    fun inst_relcomppI ctxt ant1 ant2 =
      let
        val t1 = (HOLogic.dest_Trueprop o Thm.concl_of) ant1
        val t2 = (HOLogic.dest_Trueprop o Thm.prop_of) ant2
        val fun1 = Thm.cterm_of ctxt (strip_args 2 t1)
        val args1 = map (Thm.cterm_of ctxt) (get_args 2 t1)
        val fun2 = Thm.cterm_of ctxt (strip_args 2 t2)
        val args2 = map (Thm.cterm_of ctxt) (get_args 1 t2)
        val relcomppI = Drule.incr_indexes2 ant1 ant2 @{thm relcomppI}
        val vars = map #1 (rev (Term.add_vars (Thm.prop_of relcomppI) []))
      in
        infer_instantiate ctxt (vars ~~ ([fun1] @ args1 @ [fun2] @ args2)) relcomppI
      end

    fun zip_transfer_rules ctxt thm =
      let
        fun mk_POS ty = Const (\<^const_name>\<open>POS\<close>, ty --> ty --> HOLogic.boolT)
        val rel = (Thm.dest_fun2 o Thm.dest_arg o Thm.cprop_of) thm
        val typ = Thm.typ_of_cterm rel
        val POS_const = Thm.cterm_of ctxt (mk_POS typ)
        val var = Thm.cterm_of ctxt (Var (("X", Thm.maxidx_of_cterm rel + 1), typ))
        val goal =
          Thm.apply (Thm.cterm_of ctxt HOLogic.Trueprop) (Thm.apply (Thm.apply POS_const rel) var)
      in
        [Lifting_Term.merge_transfer_relations ctxt goal, thm] MRSL @{thm POS_apply}
      end

    val thm =
      inst_relcomppI ctxt0 parametric_transfer_rule transfer_rule
        OF [parametric_transfer_rule, transfer_rule]
    val preprocessed_thm = preprocess ctxt0 thm
    val (fixed_thm, ctxt1) = ctxt0
      |> yield_singleton (apfst snd oo Variable.import true) preprocessed_thm
    val assms = cprems_of fixed_thm
    val add_transfer_rule = Thm.attribute_declaration Transfer.transfer_add
    val (prems, ctxt2) = ctxt1 |> fold_map Thm.assume_hyps assms
    val ctxt3 =  ctxt2 |> Context.proof_map (fold add_transfer_rule prems)
    val zipped_thm =
      fixed_thm
      |> undisch_all
      |> zip_transfer_rules ctxt3
      |> implies_intr_list assms
      |> singleton (Variable.export ctxt3 ctxt0)
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

fun get_binder_types_by_rel (Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ S) (Type ("fun", [T, U]), Type ("fun", [V, W])) =
    (T, V) :: get_binder_types_by_rel S (U, W)
  | get_binder_types_by_rel _ _ = []

fun get_body_type_by_rel (Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ S) (Type ("fun", [_, U]), Type ("fun", [_, V])) =
    get_body_type_by_rel S (U, V)
  | get_body_type_by_rel _ (U, V)  = (U, V)

fun get_binder_rels (Const (\<^const_name>\<open>rel_fun\<close>, _) $ R $ S) = R :: get_binder_rels S
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
    val (_, rhs) = Thm.dest_equals (Thm.cprop_of def)
    fun dest_abs (Abs (var_name, T, _)) = (var_name, T)
      | dest_abs tm = raise TERM("get_abs_var",[tm])
    val (var_name, T) = dest_abs (Thm.term_of rhs)
    val (new_var_names, ctxt') = Variable.variant_fixes [var_name] ctxt
    val refl_thm = Thm.reflexive (Thm.cterm_of ctxt' (Free (hd new_var_names, T)))
  in
    Thm.combination def refl_thm |>
    singleton (Proof_Context.export ctxt' ctxt)
  end

fun unabs_all_def ctxt def =
  let
    val (_, rhs) = Thm.dest_equals (Thm.cprop_of def)
    val xs = strip_abs_vars (Thm.term_of rhs)
  in
    fold (K (unabs_def ctxt)) xs def
  end

val map_fun_unfolded =
  @{thm map_fun_def[abs_def]} |>
  unabs_def \<^context> |>
  unabs_def \<^context> |>
  Local_Defs.unfold0 \<^context> [@{thm comp_def}]

fun unfold_fun_maps ctm =
  let
    fun unfold_conv ctm =
      case (Thm.term_of ctm) of
        Const (\<^const_name>\<open>map_fun\<close>, _) $ _ $ _ =>
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
  Local_Defs.unfold0 ctxt [@{thm o_apply}, @{thm map_fun_def}, @{thm id_apply}] def_thm

(*
  quot_thm - quotient theorem (Quotient R Abs Rep T).
  returns: whether the Lifting package is capable to generate code for the abstract type
    represented by quot_thm
*)

fun can_generate_code_cert quot_thm  =
  case quot_thm_rel quot_thm of
    Const (\<^const_name>\<open>HOL.eq\<close>, _) => true
    | Const (\<^const_name>\<open>eq_onp\<close>, _) $ _  => true
    | _ => false

fun generate_rep_eq ctxt def_thm rsp_thm (rty, qty) =
  let
    val unfolded_def = Conv.fconv_rule (Conv.arg_conv unfold_fun_maps_beta) def_thm
    val unabs_def = unabs_all_def ctxt unfolded_def
  in
    if body_type rty = body_type qty then
      SOME (simplify_code_eq ctxt (HOLogic.mk_obj_eq unabs_def))
    else
      let
        val quot_thm = Lifting_Term.prove_quot_thm ctxt (get_body_types (rty, qty))
        val rel_fun = prove_rel ctxt rsp_thm (rty, qty)
        val rep_abs_thm = [quot_thm, rel_fun] MRSL @{thm Quotient_rep_abs_eq}
      in
        case mono_eq_prover ctxt (hd (Thm.prems_of rep_abs_thm)) of
          SOME mono_eq_thm =>
            let
              val rep_abs_eq = mono_eq_thm RS rep_abs_thm
              val rep = Thm.cterm_of ctxt (quot_thm_rep quot_thm)
              val rep_refl = HOLogic.mk_obj_eq (Thm.reflexive rep)
              val repped_eq = [rep_refl, HOLogic.mk_obj_eq unabs_def] MRSL @{thm cong}
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
            val ctm = Thm.dest_equals_lhs (Thm.cprop_of rep_id)
            val unfolded_maps_eq = unfold_fun_maps ctm
            val t1 = [quot_thm, def_thm, rsp_thm] MRSL @{thm Quotient_rep_abs_fold_unmap}
            val prems_pat = (hd o Drule.cprems_of) t1
            val insts = Thm.first_order_match (prems_pat, Thm.cprop_of unfolded_maps_eq)
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
      andalso no_abstr (Thm.prop_of eqn)
    fun is_valid_abs_eq abs_eq = can (Code.assert_abs_eqn thy NONE) (mk_meta_eq abs_eq)

  in
    if is_valid_eq abs_eq_thm then
      (ABS_EQ, Code.declare_default_eqns_global [(abs_eq_thm, true)] thy)
    else
      let
        val (rty_body, qty_body) = get_body_types (rty, qty)
      in
        if rty_body = qty_body then
          (REP_EQ, Code.declare_default_eqns_global [(the opt_rep_eq_thm, true)] thy)
        else
          if is_some opt_rep_eq_thm andalso is_valid_abs_eq (the opt_rep_eq_thm)
          then
            (REP_EQ, Code.declare_abstract_eqn_global (the opt_rep_eq_thm) thy)
          else
            (NONE_EQ, thy)
      end
  end

local
  fun no_no_code ctxt (rty, qty) =
    if same_type_constrs (rty, qty) then
      forall (no_no_code ctxt) (Targs rty ~~ Targs qty)
    else
      if Term.is_Type qty then
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

  fun encode_code_eq ctxt abs_eq opt_rep_eq (rty, qty) =
    let
      fun mk_type typ = typ |> Logic.mk_type |> Thm.cterm_of ctxt |> Drule.mk_term
    in
      Conjunction.intr_balanced [abs_eq, (the_default TrueI opt_rep_eq), mk_type rty, mk_type qty]
    end

  exception DECODE

  fun decode_code_eq thm =
    if Thm.nprems_of thm > 0 then raise DECODE
    else
      let
        val [abs_eq, rep_eq, rty, qty] = Conjunction.elim_balanced 4 thm
        val opt_rep_eq = if Thm.eq_thm_prop (rep_eq, TrueI) then NONE else SOME rep_eq
        fun dest_type typ = typ |> Drule.dest_term |> Thm.term_of |> Logic.dest_type
      in
        (abs_eq, opt_rep_eq, (dest_type rty, dest_type qty))
      end

  structure Data = Generic_Data
  (
    type T = code_eq option
    val empty = NONE
    val extend = I
    fun merge _ = NONE
  );

  fun register_encoded_code_eq thm thy =
    let
      val (abs_eq_thm, opt_rep_eq_thm, (rty, qty)) = decode_code_eq thm
      val (code_eq, thy) = register_code_eq_thy abs_eq_thm opt_rep_eq_thm (rty, qty) thy
    in
      Context.theory_map (Data.put (SOME code_eq)) thy
    end
    handle DECODE => thy

  val register_code_eq_attribute = Thm.declaration_attribute
    (fn thm => Context.mapping (register_encoded_code_eq thm) I)
  val register_code_eq_attrib = Attrib.internal (K register_code_eq_attribute)

in

fun register_code_eq abs_eq_thm opt_rep_eq_thm (rty, qty) lthy =
  let
    val encoded_code_eq = encode_code_eq lthy abs_eq_thm opt_rep_eq_thm (rty, qty)
  in
    if no_no_code lthy (rty, qty) then
      let
        val lthy' = lthy
          |> (#2 oo Local_Theory.note) ((Binding.empty, [register_code_eq_attrib]), [encoded_code_eq])
        val opt_code_eq = Data.get (Context.Theory (Proof_Context.theory_of lthy'))
        val code_eq =
          if is_some opt_code_eq then the opt_code_eq
          else UNKNOWN_EQ (* UNKNOWN_EQ means that we are in a locale and we do not know
            which code equation is going to be used. This is going to be resolved at the
            point when an interpretation of the locale is executed. *)
        val lthy'' = lthy'
          |> Local_Theory.declaration {syntax = false, pervasive = true} (K (Data.put NONE))
      in (code_eq, lthy'') end
    else
      (NONE_EQ, lthy)
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

fun add_lift_def (config: config) (binding, mx) qty rhs rsp_thm par_thms lthy0 =
  let
    val rty = fastype_of rhs
    val quot_thm = Lifting_Term.prove_quot_thm lthy0 (rty, qty)
    val absrep_trm =  quot_thm_abs quot_thm
    val rty_forced = (domain_type o fastype_of) absrep_trm
    val forced_rhs = force_rty_type lthy0 rty_forced rhs
    val lhs = Free (Binding.name_of binding, qty)
    val prop = Logic.mk_equals (lhs, absrep_trm $ forced_rhs)
    val (_, prop') = Local_Defs.cert_def lthy0 (K []) prop
    val (_, newrhs) = Local_Defs.abs_def prop'
    val var = ((#notes config = false ? Binding.concealed) binding, mx)
    val def_name = Thm.make_def_binding (#notes config) (#1 var)

    val ((lift_const, (_ , def_thm)), lthy1) = lthy0
      |> Local_Theory.define (var, ((def_name, []), newrhs))

    val transfer_rules = generate_transfer_rules lthy1 quot_thm rsp_thm def_thm par_thms

    val abs_eq_thm = generate_abs_eq lthy1 def_thm rsp_thm quot_thm
    val opt_rep_eq_thm = generate_rep_eq lthy1 def_thm rsp_thm (rty_forced, qty)

    fun notes names =
      let
        val lhs_name = Binding.reset_pos (#1 var)
        val rsp_thmN = Binding.qualify_name true lhs_name "rsp"
        val abs_eq_thmN = Binding.qualify_name true lhs_name "abs_eq"
        val rep_eq_thmN = Binding.qualify_name true lhs_name "rep_eq"
        val transfer_ruleN = Binding.qualify_name true lhs_name "transfer"
        val notes =
          [(rsp_thmN, [], [rsp_thm]),
          (transfer_ruleN, @{attributes [transfer_rule]}, transfer_rules),
          (abs_eq_thmN, [], [abs_eq_thm])]
          @ (case opt_rep_eq_thm of SOME rep_eq_thm => [(rep_eq_thmN, [], [rep_eq_thm])] | NONE => [])
      in
        if names then map (fn (name, attrs, thms) => ((name, []), [(thms, attrs)])) notes
        else map_filter (fn (_, attrs, thms) => if null attrs then NONE
          else SOME (Binding.empty_atts, [(thms, attrs)])) notes
      end
    val (code_eq, lthy2) = lthy1
      |> register_code_eq abs_eq_thm opt_rep_eq_thm (rty_forced, qty)
    val lift_def = mk_lift_def rty_forced qty newrhs lift_const def_thm rsp_thm abs_eq_thm
          opt_rep_eq_thm code_eq transfer_rules
  in
    lthy2
    |> (snd o Local_Theory.begin_nested)
    |> Local_Theory.notes (notes (#notes config)) |> snd
    |> `(fn lthy => morph_lift_def (Local_Theory.target_morphism lthy) lift_def)
    ||> Local_Theory.end_nested
  end

(* This is not very cheap way of getting the rules but we have only few active
  liftings in the current setting *)
fun get_cr_pcr_eqs ctxt =
  let
    fun collect (data : Lifting_Info.quotient) l =
      if is_some (#pcr_info data)
      then ((Thm.symmetric o safe_mk_meta_eq o Thm.transfer' ctxt o #pcr_cr_eq o the o #pcr_info) data :: l)
      else l
    val table = Lifting_Info.get_quotients ctxt
  in
    Symtab.fold (fn (_, data) => fn l => collect data l) table []
  end

fun prepare_lift_def add_lift_def var qty rhs par_thms ctxt =
  let
    val rsp_rel = Lifting_Term.equiv_relation ctxt (fastype_of rhs, qty)
    val rty_forced = (domain_type o fastype_of) rsp_rel;
    val forced_rhs = force_rty_type ctxt rty_forced rhs;
    val cr_to_pcr_conv = HOLogic.Trueprop_conv (Conv.fun2_conv
      (Raw_Simplifier.rewrite ctxt false (get_cr_pcr_eqs ctxt)))
    val (prsp_tm, rsp_prsp_eq) = HOLogic.mk_Trueprop (rsp_rel $ forced_rhs $ forced_rhs)
      |> Thm.cterm_of ctxt
      |> cr_to_pcr_conv
      |> `Thm.concl_of
      |>> Logic.dest_equals
      |>> snd
    val to_rsp = rsp_prsp_eq RS Drule.equal_elim_rule2
    val opt_proven_rsp_thm = try_prove_reflexivity ctxt prsp_tm

    fun after_qed internal_rsp_thm =
      add_lift_def var qty rhs (internal_rsp_thm RS to_rsp) par_thms
  in
    case opt_proven_rsp_thm of
      SOME thm => (NONE, K (after_qed thm))
      | NONE => (SOME prsp_tm, after_qed)
  end

fun gen_lift_def add_lift_def var qty rhs tac par_thms lthy =
  let
    val (goal, after_qed) = prepare_lift_def add_lift_def var qty rhs par_thms lthy
  in
    case goal of
      SOME goal =>
        let
          val rsp_thm =
            Goal.prove_sorry lthy [] [] goal (tac o #context)
            |> Thm.close_derivation \<^here>
        in
          after_qed rsp_thm lthy
        end
      | NONE => after_qed Drule.dummy_thm lthy
  end

val lift_def = gen_lift_def o add_lift_def

end (* structure *)
