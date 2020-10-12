(*  Title:      HOL/Tools/Lifting/lifting_setup.ML
    Author:     Ondrej Kuncar

Setting up the lifting infrastructure.
*)

signature LIFTING_SETUP =
sig
  exception SETUP_LIFTING_INFR of string

  type config = { notes: bool };
  val default_config: config;

  val setup_by_quotient: config -> thm -> thm option -> thm option -> local_theory -> 
    binding * local_theory

  val setup_by_typedef_thm: config -> thm -> local_theory -> binding * local_theory

  val lifting_restore: Lifting_Info.quotient -> Context.generic -> Context.generic

  val lifting_forget: string -> local_theory -> local_theory
  val update_transfer_rules: string -> local_theory -> local_theory
  val pointer_of_bundle_binding: Proof.context -> binding -> string
end

structure Lifting_Setup: LIFTING_SETUP =
struct

open Lifting_Util

infix 0 MRSL

exception SETUP_LIFTING_INFR of string

(* Config *)

type config = { notes: bool };
val default_config = { notes = true };

fun define_crel (config: config) rep_fun lthy =
  let
    val (qty, rty) = (dest_funT o fastype_of) rep_fun
    val rep_fun_graph = (HOLogic.eq_const rty) $ Bound 1 $ (rep_fun $ Bound 0)
    val def_term = Abs ("x", rty, Abs ("y", qty, rep_fun_graph))
    val qty_name = (Binding.name o Long_Name.base_name o fst o dest_Type) qty
    val crel_name = Binding.prefix_name "cr_" qty_name
    val (fixed_def_term, lthy1) = lthy |> yield_singleton (Variable.importT_terms) def_term
    val ((_, (_ , def_thm)), lthy2) =
      if #notes config then
        Local_Theory.define
          ((crel_name, NoSyn), ((Thm.def_binding crel_name, []), fixed_def_term)) lthy1
      else 
        Local_Theory.define
          ((Binding.concealed crel_name, NoSyn), (Binding.empty_atts, fixed_def_term)) lthy1
  in  
    (def_thm, lthy2)
  end

fun print_define_pcrel_warning msg = 
  let
    val warning_msg = cat_lines 
      ["Generation of a parametrized correspondence relation failed.",
      (Pretty.string_of (Pretty.block
         [Pretty.str "Reason:", Pretty.brk 2, msg]))]
  in
    warning warning_msg
  end

fun define_pcrel (config: config) crel lthy0 =
  let
    val (fixed_crel, lthy1) = yield_singleton Variable.importT_terms crel lthy0
    val [rty', qty] = (binder_types o fastype_of) fixed_crel
    val (param_rel, args) = Lifting_Term.generate_parametrized_relator lthy1 rty'
    val rty_raw = (domain_type o range_type o fastype_of) param_rel
    val tyenv_match = Sign.typ_match (Proof_Context.theory_of lthy1) (rty_raw, rty') Vartab.empty
    val param_rel_subst = Envir.subst_term (tyenv_match,Vartab.empty) param_rel
    val args_subst = map (Envir.subst_term (tyenv_match,Vartab.empty)) args
    val (instT, lthy2) = lthy1
      |> Variable.declare_names fixed_crel
      |> Variable.importT_inst (param_rel_subst :: args_subst)
    val args_fixed = (map (Term_Subst.instantiate (instT, []))) args_subst
    val param_rel_fixed = Term_Subst.instantiate (instT, []) param_rel_subst
    val rty = (domain_type o fastype_of) param_rel_fixed
    val relcomp_op = Const (\<^const_name>\<open>relcompp\<close>, 
          (rty --> rty' --> HOLogic.boolT) --> 
          (rty' --> qty --> HOLogic.boolT) --> 
          rty --> qty --> HOLogic.boolT)
    val qty_name = (fst o dest_Type) qty
    val pcrel_name = Binding.prefix_name "pcr_" ((Binding.name o Long_Name.base_name) qty_name)
    val relator_type = foldr1 (op -->) ((map type_of args_fixed) @ [rty, qty, HOLogic.boolT])
    val lhs = Library.foldl (op $) ((Free (Binding.name_of pcrel_name, relator_type)), args_fixed)
    val rhs = relcomp_op $ param_rel_fixed $ fixed_crel
    val definition_term = Logic.mk_equals (lhs, rhs)
    fun note_def lthy =
      Specification.definition (SOME (pcrel_name, SOME relator_type, NoSyn)) [] []
        (Binding.empty_atts, definition_term) lthy |>> (snd #> snd);
    fun raw_def lthy =
      let
        val ((_, rhs), prove) =
          Local_Defs.derived_def lthy (K []) {conditional = true} definition_term;
        val ((_, (_, raw_th)), lthy') =
          Local_Theory.define
            ((Binding.concealed pcrel_name, NoSyn), (Binding.empty_atts, rhs)) lthy;
        val th = prove lthy' raw_th;
      in
        (th, lthy')
      end
    val (def_thm, lthy3) = if #notes config then note_def lthy2 else raw_def lthy2
  in
    (SOME def_thm, lthy3)
  end
  handle Lifting_Term.PARAM_QUOT_THM (_, msg) => (print_define_pcrel_warning msg; (NONE, lthy0))


local
  val eq_OO_meta = mk_meta_eq @{thm eq_OO} 

  fun print_generate_pcr_cr_eq_error ctxt term = 
    let
      val goal = Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ term $ Const (\<^const_name>\<open>HOL.eq\<close>, dummyT)
      val error_msg = cat_lines 
        ["Generation of a pcr_cr_eq failed.",
        (Pretty.string_of (Pretty.block
           [Pretty.str "Reason: Cannot prove this: ", Pretty.brk 2, Syntax.pretty_term ctxt goal])),
         "Most probably a relator_eq rule for one of the involved types is missing."]
    in
      error error_msg
    end
in
  fun define_pcr_cr_eq (config: config) lthy pcr_rel_def =
    let
      val lhs = (Thm.term_of o Thm.lhs_of) pcr_rel_def
      val qty_name =
        (Binding.name o Long_Name.base_name o fst o dest_Type o
          List.last o binder_types o fastype_of) lhs
      val args = (snd o strip_comb) lhs
      
      fun make_inst var ctxt = 
        let 
          val typ = snd (relation_types (#2 (dest_Var var)))
          val sort = Type.sort_of_atyp typ
          val (fresh_var, ctxt') = yield_singleton Variable.invent_types sort ctxt
          val inst = (#1 (dest_Var var), Thm.cterm_of ctxt' (HOLogic.eq_const (TFree fresh_var)))
        in (inst, ctxt') end
      
      val (args_inst, args_ctxt) = fold_map make_inst args lthy
      val pcr_cr_eq = 
        pcr_rel_def
        |> infer_instantiate args_ctxt args_inst
        |> Conv.fconv_rule (Conv.arg_conv (Conv.arg1_conv 
          (Transfer.bottom_rewr_conv (Transfer.get_relator_eq args_ctxt))))
  in
    case (Thm.term_of o Thm.rhs_of) pcr_cr_eq of
      Const (\<^const_name>\<open>relcompp\<close>, _) $ Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ =>
        let
          val thm = 
            pcr_cr_eq
            |> Conv.fconv_rule (Conv.arg_conv (Conv.rewr_conv eq_OO_meta))
            |> HOLogic.mk_obj_eq
            |> singleton (Variable.export args_ctxt lthy)
          val lthy' = lthy
            |> #notes config ?
              (Local_Theory.note ((Binding.qualify_name true qty_name "pcr_cr_eq", []), [thm]) #> #2)
        in
          (thm, lthy')
        end
      | Const (\<^const_name>\<open>relcompp\<close>, _) $ t $ _ => print_generate_pcr_cr_eq_error args_ctxt t
      | _ => error "generate_pcr_cr_eq: implementation error"
  end
end

fun define_code_constr quot_thm lthy =
  let
    val abs = quot_thm_abs quot_thm
  in
    if is_Const abs then
      let
        val (fixed_abs, lthy') = yield_singleton Variable.importT_terms abs lthy
      in  
         Local_Theory.background_theory
           (Code.declare_datatype_global [dest_Const fixed_abs]) lthy'
      end
    else
      lthy
  end

fun define_abs_type quot_thm =
  Lifting_Def.can_generate_code_cert quot_thm ?
    Code.declare_abstype (quot_thm RS @{thm Quotient_abs_rep});

local
  exception QUOT_ERROR of Pretty.T list
in
fun quot_thm_sanity_check ctxt quot_thm =
  let
    val _ = 
      if (Thm.nprems_of quot_thm > 0) then   
          raise QUOT_ERROR [Pretty.block
            [Pretty.str "The Quotient theorem has extra assumptions:",
             Pretty.brk 1,
             Thm.pretty_thm ctxt quot_thm]]
      else ()
    val _ = quot_thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_Quotient
    handle TERM _ => raise QUOT_ERROR
          [Pretty.block
            [Pretty.str "The Quotient theorem is not of the right form:",
             Pretty.brk 1,
             Thm.pretty_thm ctxt quot_thm]]
    val ((_, [quot_thm_fixed]), ctxt') = Variable.importT [quot_thm] ctxt 
    val (rty, qty) = quot_thm_rty_qty quot_thm_fixed
    val rty_tfreesT = Term.add_tfree_namesT rty []
    val qty_tfreesT = Term.add_tfree_namesT qty []
    val extra_rty_tfrees =
      case subtract (op =) qty_tfreesT rty_tfreesT of
        [] => []
      | extras => [Pretty.block ([Pretty.str "Extra variables in the raw type:",
                                 Pretty.brk 1] @ 
                                 ((Pretty.commas o map (Pretty.str o quote)) extras) @
                                 [Pretty.str "."])]
    val not_type_constr = 
      case qty of
         Type _ => []
         | _ => [Pretty.block [Pretty.str "The quotient type ",
                                Pretty.quote (Syntax.pretty_typ ctxt' qty),
                                Pretty.brk 1,
                                Pretty.str "is not a type constructor."]]
    val errs = extra_rty_tfrees @ not_type_constr
  in
    if null errs then () else raise QUOT_ERROR errs
  end
  handle QUOT_ERROR errs => error (cat_lines (["Sanity check of the quotient theorem failed:"] 
                                            @ (map (Pretty.string_of o Pretty.item o single) errs)))
end

fun lifting_bundle qty_full_name qinfo lthy = 
  let
    val thy = Proof_Context.theory_of lthy

    val binding =
      Binding.qualify_name true (qty_full_name |> Long_Name.base_name |> Binding.name) "lifting"
    val morphed_binding = Morphism.binding (Local_Theory.target_morphism lthy) binding
    val bundle_name =
      Name_Space.full_name (Name_Space.naming_of (Context.Theory thy)) morphed_binding
    fun phi_qinfo phi = Lifting_Info.transform_quotient phi qinfo

    val dummy_thm = Thm.transfer thy Drule.dummy_thm
    val restore_lifting_att = 
      ([dummy_thm],
        [map (Token.make_string o rpair Position.none)
          ["Lifting.lifting_restore_internal", bundle_name]])
  in
    lthy
    |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Lifting_Info.init_restore_data bundle_name (phi_qinfo phi))
    |> Bundle.bundle ((binding, [restore_lifting_att])) []
    |> pair binding
  end

fun setup_lifting_infr config quot_thm opt_reflp_thm lthy =
  let
    val _ = quot_thm_sanity_check lthy quot_thm
    val (_, qty) = quot_thm_rty_qty quot_thm
    val (pcrel_def, lthy1) = define_pcrel config (quot_thm_crel quot_thm) lthy
    (**)
    val pcrel_def = Option.map (Morphism.thm (Local_Theory.target_morphism lthy1)) pcrel_def
    (**)
    val (pcr_cr_eq, lthy2) =
      case pcrel_def of
        SOME pcrel_def => apfst SOME (define_pcr_cr_eq config lthy1 pcrel_def)
      | NONE => (NONE, lthy1)
    val pcr_info = case pcrel_def of
      SOME pcrel_def => SOME { pcrel_def = pcrel_def, pcr_cr_eq = the pcr_cr_eq }
      | NONE => NONE
    val quotients = { quot_thm = quot_thm, pcr_info = pcr_info }
    val qty_full_name = (fst o dest_Type) qty
    fun quot_info phi = Lifting_Info.transform_quotient phi quotients
    val reflexivity_rule_attr = Attrib.internal (K Lifting_Info.add_reflexivity_rule_attribute)
    val lthy3 =
      case opt_reflp_thm of
        SOME reflp_thm =>
          lthy2
          |> (#2 oo Local_Theory.note)
              ((Binding.empty, [reflexivity_rule_attr]), [reflp_thm RS @{thm reflp_ge_eq}])
          |> define_code_constr quot_thm
      | NONE => lthy2 |> define_abs_type quot_thm
  in
    lthy3
    |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Lifting_Info.update_quotients qty_full_name (quot_info phi))
    |> lifting_bundle qty_full_name quotients
  end

local
  fun importT_inst_exclude exclude ts ctxt =
    let
      val tvars = rev (subtract op= exclude (fold Term.add_tvars ts []))
      val (tfrees, ctxt') = Variable.invent_types (map #2 tvars) ctxt
    in (tvars ~~ map TFree tfrees, ctxt') end
  
  fun import_inst_exclude exclude ts ctxt =
    let
      val excludeT = fold (Term.add_tvarsT o snd) exclude []
      val (instT, ctxt') = importT_inst_exclude excludeT ts ctxt
      val vars = map (apsnd (Term_Subst.instantiateT instT)) 
        (rev (subtract op= exclude (fold Term.add_vars ts [])))
      val (xs, ctxt'') = Variable.variant_fixes (map (#1 o #1) vars) ctxt'
      val inst = vars ~~ map Free (xs ~~ map #2 vars)
    in ((instT, inst), ctxt'') end
  
  fun import_terms_exclude exclude ts ctxt =
    let val (inst, ctxt') = import_inst_exclude exclude ts ctxt
    in (map (Term_Subst.instantiate inst) ts, ctxt') end
in
  fun reduce_goal not_fix goal tac ctxt =
    let
      val (fixed_goal, ctxt') = yield_singleton (import_terms_exclude not_fix) goal ctxt
      val init_goal = Goal.init (Thm.cterm_of ctxt' fixed_goal)
    in
      (singleton (Variable.export ctxt' ctxt) o Goal.conclude) (the (SINGLE tac init_goal))
    end
end

local 
  val OO_rules = @{thms left_total_OO left_unique_OO right_total_OO right_unique_OO bi_total_OO
    bi_unique_OO}
in
  fun parametrize_class_constraint ctxt0 pcr_def constraint =
    let
      fun generate_transfer_rule pcr_def constraint goal ctxt =
        let
          val (fixed_goal, ctxt') = yield_singleton (Variable.import_terms true) goal ctxt
          val init_goal = Goal.init (Thm.cterm_of ctxt' fixed_goal)
          val rules = Transfer.get_transfer_raw ctxt'
          val rules = constraint :: OO_rules @ rules
          val tac =
            K (Local_Defs.unfold0_tac ctxt' [pcr_def]) THEN' REPEAT_ALL_NEW (resolve_tac ctxt' rules)
        in
          (singleton (Variable.export ctxt' ctxt) o Goal.conclude) (the (SINGLE (tac 1) init_goal))
        end
      
      fun make_goal pcr_def constr =
        let 
          val pred_name =
            (fst o dest_Const o strip_args 1 o HOLogic.dest_Trueprop o Thm.prop_of) constr
          val arg = (fst o Logic.dest_equals o Thm.prop_of) pcr_def
        in
          HOLogic.mk_Trueprop ((Const (pred_name, (fastype_of arg) --> HOLogic.boolT)) $ arg)
        end
      
      val check_assms =
        let 
          val right_names = ["right_total", "right_unique", "left_total", "left_unique", "bi_total",
            "bi_unique"]
      
          fun is_right_name name = member op= right_names (Long_Name.base_name name)
      
          fun is_trivial_assm (Const (name, _) $ Var (_, _)) = is_right_name name
            | is_trivial_assm (Const (name, _) $ Free (_, _)) = is_right_name name
            | is_trivial_assm _ = false
        in
          fn thm => 
            let
              val prems = map HOLogic.dest_Trueprop (Thm.prems_of thm)
              val thm_name =
                (Long_Name.base_name o fst o dest_Const o strip_args 1 o HOLogic.dest_Trueprop o Thm.concl_of) thm
              val non_trivial_assms = filter_out is_trivial_assm prems
            in
              if null non_trivial_assms then ()
              else
                Pretty.block ([Pretty.str "Non-trivial assumptions in ",
                  Pretty.str thm_name,
                  Pretty.str " transfer rule found:",
                  Pretty.brk 1] @ 
                  Pretty.commas (map (Syntax.pretty_term ctxt0) non_trivial_assms))
                |> Pretty.string_of
                |> warning
            end
        end
  
      val goal = make_goal pcr_def constraint
      val thm = generate_transfer_rule pcr_def constraint goal ctxt0
      val _ = check_assms thm
    in
      thm
    end
end

local
  val id_unfold = (Conv.rewr_conv (mk_meta_eq @{thm id_def}))
in
  fun generate_parametric_id lthy rty id_transfer_rule =
    let
      (* it doesn't raise an exception because it would have already raised it in define_pcrel *)
      val (quot_thm, _, ctxt') = Lifting_Term.prove_param_quot_thm lthy rty
      val parametrized_relator =
        singleton (Variable.export_terms ctxt' lthy) (quot_thm_crel quot_thm)
      val id_transfer = 
         @{thm id_transfer}
        |> Thm.incr_indexes (Term.maxidx_of_term parametrized_relator + 1)
        |> Conv.fconv_rule(HOLogic.Trueprop_conv (Conv.arg_conv id_unfold then_conv Conv.arg1_conv id_unfold))
      val var = hd (Term.add_vars (Thm.prop_of id_transfer) [])
      val inst = [(#1 var, Thm.cterm_of lthy parametrized_relator)]
      val id_par_thm = infer_instantiate lthy inst id_transfer
    in
      Lifting_Def.generate_parametric_transfer_rule lthy id_transfer_rule id_par_thm
    end
    handle Lifting_Term.MERGE_TRANSFER_REL msg => 
      let
        val error_msg = cat_lines 
          ["Generation of a parametric transfer rule for the abs. or the rep. function failed.",
          "A non-parametric version will be used.",
          (Pretty.string_of (Pretty.block
             [Pretty.str "Reason:", Pretty.brk 2, msg]))]
      in
        (warning error_msg; id_transfer_rule)
      end
end

local
  fun rewrite_first_Domainp_arg rewr_thm thm = Conv.fconv_rule (Conv.concl_conv ~1 (HOLogic.Trueprop_conv 
      (Conv.arg1_conv (Conv.arg_conv (Conv.rewr_conv rewr_thm))))) thm
  
  fun fold_Domainp_pcrel pcrel_def thm =
    let
      val ct =
        thm |> Thm.cprop_of |> Drule.strip_imp_concl
        |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_arg
      val pcrel_def = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) pcrel_def
      val thm' = Thm.instantiate (Thm.match (ct, Thm.rhs_of pcrel_def)) thm
        handle Pattern.MATCH => raise CTERM ("fold_Domainp_pcrel", [ct, Thm.rhs_of pcrel_def])
    in
      rewrite_first_Domainp_arg (Thm.symmetric pcrel_def) thm'
    end

  fun reduce_Domainp ctxt rules thm =
    let
      val goal = thm |> Thm.prems_of |> hd
      val var = goal |> HOLogic.dest_Trueprop |> dest_comb |> snd |> dest_Var 
      val reduced_assm =
        reduce_goal [var] goal (TRY (REPEAT_ALL_NEW (resolve_tac ctxt rules) 1)) ctxt
    in
      reduced_assm RS thm
    end
in
  fun parametrize_domain dom_thm (pcr_info : Lifting_Info.pcr) ctxt0 =
    let
      fun reduce_first_assm ctxt rules thm =
        let
          val goal = thm |> Thm.prems_of |> hd
          val reduced_assm =
            reduce_goal [] goal (TRY (REPEAT_ALL_NEW (resolve_tac ctxt rules) 1)) ctxt
        in
          reduced_assm RS thm
        end

      val pcr_cr_met_eq = #pcr_cr_eq pcr_info RS @{thm eq_reflection}
      val pcr_Domainp_eq = rewrite_first_Domainp_arg (Thm.symmetric pcr_cr_met_eq) dom_thm
      val pcrel_def = #pcrel_def pcr_info
      val pcr_Domainp_par_left_total = 
        (dom_thm RS @{thm pcr_Domainp_par_left_total})
          |> fold_Domainp_pcrel pcrel_def
          |> reduce_first_assm ctxt0 (Lifting_Info.get_reflexivity_rules ctxt0)
      val pcr_Domainp_par = 
        (dom_thm RS @{thm pcr_Domainp_par})      
          |> fold_Domainp_pcrel pcrel_def
          |> reduce_Domainp ctxt0 (Transfer.get_relator_domain ctxt0)
      val pcr_Domainp = 
        (dom_thm RS @{thm pcr_Domainp})
          |> fold_Domainp_pcrel pcrel_def
      val thms =
        [("domain",                 [pcr_Domainp], @{attributes [transfer_domain_rule]}),
         ("domain_par",             [pcr_Domainp_par], @{attributes [transfer_domain_rule]}),
         ("domain_par_left_total",  [pcr_Domainp_par_left_total], @{attributes [transfer_domain_rule]}),
         ("domain_eq",              [pcr_Domainp_eq], @{attributes [transfer_domain_rule]})]
    in
      thms
    end

  fun parametrize_total_domain left_total pcrel_def ctxt =
    let
      val thm =
        (left_total RS @{thm pcr_Domainp_total})
          |> fold_Domainp_pcrel pcrel_def 
          |> reduce_Domainp ctxt (Transfer.get_relator_domain ctxt)
    in
      [("domain", [thm], @{attributes [transfer_domain_rule]})]
    end

end

fun get_pcrel_info ctxt qty_full_name =  
  #pcr_info (the (Lifting_Info.lookup_quotients ctxt qty_full_name))

fun get_Domainp_thm quot_thm =
   the (get_first (try(curry op RS quot_thm)) [@{thm eq_onp_to_Domainp}, @{thm Quotient_to_Domainp}])

fun notes names thms = 
  let
    val notes =
      if names then map (fn (name, thms, attrs) => ((name, []), [(thms, attrs)])) thms
      else map_filter (fn (_, thms, attrs) => if null attrs then NONE 
        else SOME (Binding.empty_atts, [(thms, attrs)])) thms
  in
    Local_Theory.notes notes #> snd
  end

fun map_thms map_name map_thm thms = 
  map (fn (name, thms, attr) => (map_name name, map map_thm thms, attr)) thms

(*
  Sets up the Lifting package by a quotient theorem.

  quot_thm - a quotient theorem (Quotient R Abs Rep T)
  opt_reflp_thm - a theorem saying that a relation from quot_thm is reflexive
    (in the form "reflp R")
  opt_par_thm - a parametricity theorem for R
*)

fun setup_by_quotient (config: config) quot_thm opt_reflp_thm opt_par_thm lthy0 =
  let
    (**)
    val quot_thm = Morphism.thm (Local_Theory.target_morphism lthy0) quot_thm
    (**)
    val (rty, qty) = quot_thm_rty_qty quot_thm
    val induct_attr = Attrib.internal (K (Induct.induct_type (fst (dest_Type qty))))
    val qty_full_name = (fst o dest_Type) qty
    val qty_name = (Binding.name o Long_Name.base_name) qty_full_name
    val qualify = Binding.qualify_name true qty_name
    val notes1 = case opt_reflp_thm of
      SOME reflp_thm =>
        let 
          val thms =
            [("abs_induct", @{thms Quotient_total_abs_induct}, [induct_attr]),
             ("abs_eq_iff", @{thms Quotient_total_abs_eq_iff}, [])]
        in map_thms qualify (fn thm => [quot_thm, reflp_thm] MRSL thm) thms end
      | NONE =>
        let val thms = [("abs_induct", @{thms Quotient_abs_induct}, [induct_attr])]
        in map_thms qualify (fn thm => quot_thm RS thm) thms end
    val dom_thm = get_Domainp_thm quot_thm

    fun setup_transfer_rules_nonpar notes =
      let
        val notes1 =
          case opt_reflp_thm of
            SOME reflp_thm =>
              let 
                val thms =
                  [("id_abs_transfer",@{thms Quotient_id_abs_transfer}, @{attributes [transfer_rule]}),
                   ("left_total",     @{thms Quotient_left_total},      @{attributes [transfer_rule]}),
                   ("bi_total",       @{thms Quotient_bi_total},        @{attributes [transfer_rule]})]
              in
                map_thms qualify (fn thm => [quot_thm, reflp_thm] MRSL thm) thms
              end
            | NONE => map_thms qualify I [("domain", [dom_thm], @{attributes [transfer_domain_rule]})]

        val notes2 = map_thms qualify (fn thm => quot_thm RS thm)
          [("rel_eq_transfer", @{thms Quotient_rel_eq_transfer}, @{attributes [transfer_rule]}),
           ("right_unique",    @{thms Quotient_right_unique},    @{attributes [transfer_rule]}), 
           ("right_total",     @{thms Quotient_right_total},     @{attributes [transfer_rule]})]
      in
         notes2 @ notes1 @ notes
      end

    fun generate_parametric_rel_eq ctxt transfer_rule opt_param_thm =
      (case opt_param_thm of
        NONE => transfer_rule
      | SOME param_thm =>
          (Lifting_Def.generate_parametric_transfer_rule ctxt transfer_rule param_thm
            handle Lifting_Term.MERGE_TRANSFER_REL msg =>
              error ("Generation of a parametric transfer rule for the quotient relation failed:\n"
                ^ Pretty.string_of msg)))

    fun setup_transfer_rules_par ctxt notes =
      let
        val pcrel_info = the (get_pcrel_info ctxt qty_full_name)
        val pcrel_def = #pcrel_def pcrel_info
        val notes1 =
          case opt_reflp_thm of
            SOME reflp_thm =>
              let
                val left_total = ([quot_thm, reflp_thm] MRSL @{thm Quotient_left_total})
                val bi_total = ([quot_thm, reflp_thm] MRSL @{thm Quotient_bi_total})
                val domain_thms = parametrize_total_domain left_total pcrel_def ctxt
                val id_abs_transfer = generate_parametric_id ctxt rty
                  (Lifting_Term.parametrize_transfer_rule ctxt
                    ([quot_thm, reflp_thm] MRSL @{thm Quotient_id_abs_transfer}))
                val left_total = parametrize_class_constraint ctxt pcrel_def left_total
                val bi_total = parametrize_class_constraint ctxt pcrel_def bi_total
                val thms = 
                  [("id_abs_transfer", [id_abs_transfer], @{attributes [transfer_rule]}),
                   ("left_total",      [left_total],      @{attributes [transfer_rule]}),  
                   ("bi_total",        [bi_total],        @{attributes [transfer_rule]})]
              in
                map_thms qualify I thms @ map_thms qualify I domain_thms
              end
          | NONE =>
              let
                val thms = parametrize_domain dom_thm pcrel_info ctxt
              in
                map_thms qualify I thms
              end

        val rel_eq_transfer = generate_parametric_rel_eq ctxt 
          (Lifting_Term.parametrize_transfer_rule ctxt (quot_thm RS @{thm Quotient_rel_eq_transfer}))
            opt_par_thm
        val right_unique = parametrize_class_constraint ctxt pcrel_def 
            (quot_thm RS @{thm Quotient_right_unique})
        val right_total = parametrize_class_constraint ctxt pcrel_def 
            (quot_thm RS @{thm Quotient_right_total})
        val notes2 = map_thms qualify I
          [("rel_eq_transfer", [rel_eq_transfer], @{attributes [transfer_rule]}),
           ("right_unique",    [right_unique],    @{attributes [transfer_rule]}), 
           ("right_total",     [right_total],     @{attributes [transfer_rule]})]      
      in
        notes2 @ notes1 @ notes
      end

    fun setup_rules lthy = 
      let
        val thms =
          if is_some (get_pcrel_info lthy qty_full_name)
          then setup_transfer_rules_par lthy notes1
          else setup_transfer_rules_nonpar notes1
      in notes (#notes config) thms lthy end
  in
    lthy0
    |> setup_lifting_infr config quot_thm opt_reflp_thm
    ||> setup_rules
  end

(*
  Sets up the Lifting package by a typedef theorem.

  gen_code - flag if an abstract type given by typedef_thm should be registred 
    as an abstract type in the code generator
  typedef_thm - a typedef theorem (type_definition Rep Abs S)
*)

fun setup_by_typedef_thm config typedef_thm lthy0 =
  let
    val (_ $ rep_fun $ _ $ typedef_set) = (HOLogic.dest_Trueprop o Thm.prop_of) typedef_thm
    val (T_def, lthy1) = define_crel config rep_fun lthy0
    (**)
    val T_def = Morphism.thm (Local_Theory.target_morphism lthy1) T_def
    (**)    
    val quot_thm = case typedef_set of
      Const (\<^const_name>\<open>top\<close>, _) => 
        [typedef_thm, T_def] MRSL @{thm UNIV_typedef_to_Quotient}
      | Const (\<^const_name>\<open>Collect\<close>, _) $ Abs (_, _, _) => 
        [typedef_thm, T_def] MRSL @{thm open_typedef_to_Quotient}
      | _ => 
        [typedef_thm, T_def] MRSL @{thm typedef_to_Quotient}
    val (rty, qty) = quot_thm_rty_qty quot_thm
    val qty_full_name = (fst o dest_Type) qty
    val qty_name = (Binding.name o Long_Name.base_name) qty_full_name
    val qualify = Binding.qualify_name true qty_name
    val opt_reflp_thm = 
      case typedef_set of
        Const (\<^const_name>\<open>top\<close>, _) => 
          SOME ((typedef_thm RS @{thm UNIV_typedef_to_equivp}) RS @{thm equivp_reflp2})
        | _ =>  NONE
    val dom_thm = get_Domainp_thm quot_thm

    fun setup_transfer_rules_nonpar notes =
      let
        val notes1 =
          case opt_reflp_thm of
            SOME reflp_thm =>
              let 
                val thms =
                  [("id_abs_transfer",@{thms Quotient_id_abs_transfer}, @{attributes [transfer_rule]}),
                   ("left_total",     @{thms Quotient_left_total},      @{attributes [transfer_rule]}),
                   ("bi_total",       @{thms Quotient_bi_total},        @{attributes [transfer_rule]})]
              in
                map_thms qualify (fn thm => [quot_thm, reflp_thm] MRSL thm) thms
              end
            | NONE =>
              map_thms qualify I [("domain", [dom_thm], @{attributes [transfer_domain_rule]})]
        val thms = 
          [("rep_transfer", @{thms typedef_rep_transfer}, @{attributes [transfer_rule]}),
           ("left_unique",  @{thms typedef_left_unique},  @{attributes [transfer_rule]}),
           ("right_unique", @{thms typedef_right_unique}, @{attributes [transfer_rule]}), 
           ("right_total",  @{thms typedef_right_total},  @{attributes [transfer_rule]}),
           ("bi_unique",    @{thms typedef_bi_unique},    @{attributes [transfer_rule]})]
      in                                               
        map_thms qualify (fn thm => [typedef_thm, T_def] MRSL thm) thms @ notes1 @ notes
      end

    fun setup_transfer_rules_par ctxt notes =
      let
        val pcrel_info = (the (get_pcrel_info ctxt qty_full_name))
        val pcrel_def = #pcrel_def pcrel_info

        val notes1 =
          case opt_reflp_thm of
            SOME reflp_thm =>
              let
                val left_total = ([quot_thm, reflp_thm] MRSL @{thm Quotient_left_total})
                val bi_total = ([quot_thm, reflp_thm] MRSL @{thm Quotient_bi_total})
                val domain_thms = parametrize_total_domain left_total pcrel_def ctxt
                val left_total = parametrize_class_constraint ctxt pcrel_def left_total
                val bi_total = parametrize_class_constraint ctxt pcrel_def bi_total
                val id_abs_transfer = generate_parametric_id ctxt rty
                  (Lifting_Term.parametrize_transfer_rule ctxt
                    ([quot_thm, reflp_thm] MRSL @{thm Quotient_id_abs_transfer}))
                val thms = 
                  [("left_total",     [left_total],      @{attributes [transfer_rule]}),
                   ("bi_total",       [bi_total],        @{attributes [transfer_rule]}),
                   ("id_abs_transfer",[id_abs_transfer], @{attributes [transfer_rule]})]              
              in
                map_thms qualify I thms @ map_thms qualify I domain_thms
              end
            | NONE =>
              let
                val thms = parametrize_domain dom_thm pcrel_info ctxt
              in
                map_thms qualify I thms
              end
              
        val notes2 = map_thms qualify (fn thm => generate_parametric_id ctxt rty 
            (Lifting_Term.parametrize_transfer_rule ctxt ([typedef_thm, T_def] MRSL thm)))
          [("rep_transfer", @{thms typedef_rep_transfer}, @{attributes [transfer_rule]})];
        val notes3 =
          map_thms qualify
          (fn thm => parametrize_class_constraint ctxt pcrel_def ([typedef_thm, T_def] MRSL thm))
          [("left_unique",  @{thms typedef_left_unique}, @{attributes [transfer_rule]}),
           ("right_unique", @{thms typedef_right_unique},@{attributes [transfer_rule]}),
           ("bi_unique",    @{thms typedef_bi_unique},   @{attributes [transfer_rule]}),
           ("right_total",  @{thms typedef_right_total}, @{attributes [transfer_rule]})]
      in
        notes3 @ notes2 @ notes1 @ notes
      end

    val notes1 = [(Binding.prefix_name "Quotient_" qty_name, [quot_thm], [])]

    fun setup_rules lthy = 
      let
        val thms =
          if is_some (get_pcrel_info lthy qty_full_name) 
          then setup_transfer_rules_par lthy notes1
          else setup_transfer_rules_nonpar notes1
      in notes (#notes config) thms lthy end
  in
    lthy1
    |> setup_lifting_infr config quot_thm opt_reflp_thm
    ||> setup_rules
  end

fun setup_lifting_cmd xthm opt_reflp_xthm opt_par_xthm lthy =
  let 
    val input_thm = singleton (Attrib.eval_thms lthy) xthm
    val input_term = (HOLogic.dest_Trueprop o Thm.prop_of) input_thm
      handle TERM _ => error "Unsupported type of a theorem. Only Quotient or type_definition are supported."

    fun sanity_check_reflp_thm reflp_thm = 
      let
        val reflp_tm = (HOLogic.dest_Trueprop o Thm.prop_of) reflp_thm
          handle TERM _ => error "Invalid form of the reflexivity theorem. Use \"reflp R\"."
      in
        case reflp_tm of
          Const (\<^const_name>\<open>reflp\<close>, _) $ _ => ()
          | _ => error "Invalid form of the reflexivity theorem. Use \"reflp R\"."
      end
      
    fun check_qty qty = if not (is_Type qty) 
          then error "The abstract type must be a type constructor."
          else ()
   
    fun setup_quotient () = 
      let
        val opt_reflp_thm = Option.map (singleton (Attrib.eval_thms lthy)) opt_reflp_xthm
        val _ = if is_some opt_reflp_thm then sanity_check_reflp_thm (the opt_reflp_thm) else ()
        val opt_par_thm = Option.map (singleton (Attrib.eval_thms lthy)) opt_par_xthm
        val _ = check_qty (snd (quot_thm_rty_qty input_thm))
      in
        setup_by_quotient default_config input_thm opt_reflp_thm opt_par_thm lthy |> snd
      end

    fun setup_typedef () = 
      let
        val qty = (range_type o fastype_of o hd o get_args 2) input_term
        val _ = check_qty qty
      in
        case opt_reflp_xthm of
          SOME _ => error "The reflexivity theorem cannot be specified if the type_definition theorem is used."
          | NONE => (
            case opt_par_xthm of
              SOME _ => error "The parametricity theorem cannot be specified if the type_definition theorem is used."
              | NONE => setup_by_typedef_thm default_config input_thm lthy |> snd
          )
      end
  in
    case input_term of
      (Const (\<^const_name>\<open>Quotient\<close>, _) $ _ $ _ $ _ $ _) => setup_quotient ()
      | (Const (\<^const_name>\<open>type_definition\<close>, _) $ _ $ _ $ _) => setup_typedef ()
      | _ => error "Unsupported type of a theorem. Only Quotient or type_definition are supported."
  end

val _ = 
  Outer_Syntax.local_theory \<^command_keyword>\<open>setup_lifting\<close>
    "setup lifting infrastructure" 
      (Parse.thm -- Scan.option Parse.thm 
      -- Scan.option (\<^keyword>\<open>parametric\<close> |-- Parse.!!! Parse.thm) >> 
        (fn ((xthm, opt_reflp_xthm), opt_par_xthm) => 
          setup_lifting_cmd xthm opt_reflp_xthm opt_par_xthm))

(* restoring lifting infrastructure *)

local
  exception PCR_ERROR of Pretty.T list
in

fun lifting_restore_sanity_check ctxt (qinfo:Lifting_Info.quotient) =
  let
    val quot_thm = (#quot_thm qinfo)
    val _ = quot_thm_sanity_check ctxt quot_thm
    val pcr_info_err =
      (case #pcr_info qinfo of
        SOME pcr => 
          let
            val pcrel_def = #pcrel_def pcr
            val pcr_cr_eq = #pcr_cr_eq pcr
            val (def_lhs, _) = Logic.dest_equals (Thm.prop_of pcrel_def)
              handle TERM _ => raise PCR_ERROR [Pretty.block 
                    [Pretty.str "The pcr definiton theorem is not a plain meta equation:",
                    Pretty.brk 1,
                    Thm.pretty_thm ctxt pcrel_def]]
            val pcr_const_def = head_of def_lhs
            val (eq_lhs, eq_rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of pcr_cr_eq))
              handle TERM _ => raise PCR_ERROR [Pretty.block 
                    [Pretty.str "The pcr_cr equation theorem is not a plain equation:",
                    Pretty.brk 1,
                    Thm.pretty_thm ctxt pcr_cr_eq]]
            val (pcr_const_eq, eqs) = strip_comb eq_lhs
            fun is_eq (Const (\<^const_name>\<open>HOL.eq\<close>, _)) = true
              | is_eq _ = false
            fun eq_Const (Const (name1, _)) (Const (name2, _)) = (name1 = name2)
              | eq_Const _ _ = false
            val all_eqs = if not (forall is_eq eqs) then 
              [Pretty.block
                    [Pretty.str "Arguments of the lhs of the pcr_cr equation theorem are not only equalities:",
                    Pretty.brk 1,
                    Thm.pretty_thm ctxt pcr_cr_eq]]
              else []
            val pcr_consts_not_equal = if not (eq_Const pcr_const_def pcr_const_eq) then
              [Pretty.block
                    [Pretty.str "Parametrized correspondence relation constants in pcr_def and pcr_cr_eq are not equal:",
                    Pretty.brk 1,
                    Syntax.pretty_term ctxt pcr_const_def,
                    Pretty.brk 1,
                    Pretty.str "vs.",
                    Pretty.brk 1,
                    Syntax.pretty_term ctxt pcr_const_eq]]
              else []
            val crel = quot_thm_crel quot_thm
            val cr_consts_not_equal = if not (eq_Const crel eq_rhs) then
              [Pretty.block
                    [Pretty.str "Correspondence relation constants in the Quotient theorem and pcr_cr_eq are not equal:",
                    Pretty.brk 1,
                    Syntax.pretty_term ctxt crel,
                    Pretty.brk 1,
                    Pretty.str "vs.",
                    Pretty.brk 1,
                    Syntax.pretty_term ctxt eq_rhs]]
              else []
          in
            all_eqs @ pcr_consts_not_equal @ cr_consts_not_equal
          end
        | NONE => [])
    val errs = pcr_info_err
  in
    if null errs then () else raise PCR_ERROR errs
  end
  handle PCR_ERROR errs => error (cat_lines (["Sanity check failed:"] 
                                            @ (map (Pretty.string_of o Pretty.item o single) errs)))
end

(*
  Registers the data in qinfo in the Lifting infrastructure.
*)

fun lifting_restore qinfo ctxt =
  let
    val _ = lifting_restore_sanity_check (Context.proof_of ctxt) qinfo
    val (_, qty) = quot_thm_rty_qty (#quot_thm qinfo)
    val qty_full_name = (fst o dest_Type) qty
    val stored_qinfo = Lifting_Info.lookup_quotients (Context.proof_of ctxt) qty_full_name
  in
    if is_some (stored_qinfo) andalso not (Lifting_Info.quotient_eq (qinfo, (the stored_qinfo)))
      then error (Pretty.string_of 
        (Pretty.block
          [Pretty.str "Lifting is already setup for the type",
           Pretty.brk 1,
           Pretty.quote (Syntax.pretty_typ (Context.proof_of ctxt) qty)]))
      else Lifting_Info.update_quotients qty_full_name qinfo ctxt
  end

val parse_opt_pcr =
  Scan.optional (Attrib.thm -- Attrib.thm >> 
    (fn (pcrel_def, pcr_cr_eq) => SOME {pcrel_def = pcrel_def, pcr_cr_eq = pcr_cr_eq})) NONE

val lifting_restore_attribute_setup =
  Attrib.setup \<^binding>\<open>lifting_restore\<close>
    ((Attrib.thm -- parse_opt_pcr) >>
      (fn (quot_thm, opt_pcr) =>
        let val qinfo = { quot_thm = quot_thm, pcr_info = opt_pcr}
        in Thm.declaration_attribute (K (lifting_restore qinfo)) end))
    "restoring lifting infrastructure"

val _ = Theory.setup lifting_restore_attribute_setup 

fun lifting_restore_internal bundle_name ctxt = 
  let 
    val restore_info = Lifting_Info.lookup_restore_data (Context.proof_of ctxt) bundle_name
  in
    case restore_info of
      SOME restore_info =>
        ctxt 
        |> lifting_restore (#quotient restore_info)
        |> fold_rev Transfer.transfer_raw_add (Item_Net.content (#transfer_rules restore_info))
    | NONE => ctxt
  end

val lifting_restore_internal_attribute_setup =
  Attrib.setup \<^binding>\<open>lifting_restore_internal\<close>
    (Scan.lift Parse.string >>
      (fn name => Thm.declaration_attribute (K (lifting_restore_internal name))))
    "restoring lifting infrastructure; internal attribute; not meant to be used directly by regular users"

val _ = Theory.setup lifting_restore_internal_attribute_setup 

(* lifting_forget *)

val monotonicity_names = [\<^const_name>\<open>right_unique\<close>, \<^const_name>\<open>left_unique\<close>, \<^const_name>\<open>right_total\<close>,
  \<^const_name>\<open>left_total\<close>, \<^const_name>\<open>bi_unique\<close>, \<^const_name>\<open>bi_total\<close>]

fun fold_transfer_rel f (Const (\<^const_name>\<open>Transfer.Rel\<close>, _) $ rel $ _ $ _) = f rel
  | fold_transfer_rel f (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ 
    (Const (\<^const_name>\<open>Domainp\<close>, _) $ rel) $ _) = f rel
  | fold_transfer_rel f (Const (name, _) $ rel) = 
    if member op= monotonicity_names name then f rel else f \<^term>\<open>undefined\<close>
  | fold_transfer_rel f _ = f \<^term>\<open>undefined\<close>

fun filter_transfer_rules_by_rel transfer_rel transfer_rules =
  let
    val transfer_rel_name = transfer_rel |> dest_Const |> fst;
    fun has_transfer_rel thm = 
      let
        val concl = thm |> Thm.concl_of |> HOLogic.dest_Trueprop
      in
        member op= (fold_transfer_rel (fn tm => Term.add_const_names tm []) concl) transfer_rel_name
      end
      handle TERM _ => false
  in
    filter has_transfer_rel transfer_rules
  end

type restore_data = {quotient : Lifting_Info.quotient, transfer_rules: thm Item_Net.T}

fun get_transfer_rel (qinfo : Lifting_Info.quotient) =
  let
    fun get_pcrel pcr_def = pcr_def |> Thm.concl_of |> Logic.dest_equals |> fst |> head_of
  in
    if is_some (#pcr_info qinfo) 
      then get_pcrel (#pcrel_def (the (#pcr_info qinfo)))
      else quot_thm_crel (#quot_thm qinfo)
  end

fun pointer_of_bundle_name bundle_name ctxt =
  let
    val bundle = Bundle.read ctxt bundle_name
    fun err () = error "The provided bundle is not a lifting bundle"
  in
    (case bundle of
      [(_, [arg_src])] => 
        let
          val (name, _) = Token.syntax (Scan.lift Parse.string) arg_src ctxt
            handle ERROR _ => err ()
        in name end
    | _ => err ())
  end

fun pointer_of_bundle_binding ctxt binding = Name_Space.full_name (Name_Space.naming_of 
      (Context.Theory (Proof_Context.theory_of ctxt))) binding

fun lifting_forget pointer lthy =
  let
    fun get_transfer_rules_to_delete qinfo ctxt =
      let
        val transfer_rel = get_transfer_rel qinfo
      in
         filter_transfer_rules_by_rel transfer_rel (Transfer.get_transfer_raw ctxt)
      end
  in
    case Lifting_Info.lookup_restore_data lthy pointer of
      SOME restore_info =>
        let
          val qinfo = #quotient restore_info
          val quot_thm = #quot_thm qinfo
          val transfer_rules = get_transfer_rules_to_delete qinfo lthy
        in
          Local_Theory.declaration {syntax = false, pervasive = true}
            (K (fold (Transfer.transfer_raw_del) transfer_rules #> Lifting_Info.delete_quotients quot_thm))
            lthy
        end
      | NONE => error "The lifting bundle refers to non-existent restore data."
    end
    

fun lifting_forget_cmd bundle_name lthy = 
  lifting_forget (pointer_of_bundle_name bundle_name lthy) lthy


val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>lifting_forget\<close> 
    "unsetup Lifting and Transfer for the given lifting bundle"
    (Parse.name_position >> lifting_forget_cmd)

(* lifting_update *)

fun update_transfer_rules pointer lthy =
  let
    fun new_transfer_rules ({ quotient = qinfo, ... }:Lifting_Info.restore_data) lthy =
      let
        val transfer_rel = get_transfer_rel qinfo
        val transfer_rules = filter_transfer_rules_by_rel transfer_rel (Transfer.get_transfer_raw lthy)
      in
        fn phi => fold_rev 
          (Item_Net.update o Morphism.thm phi) transfer_rules Thm.full_rules
      end
  in
    case Lifting_Info.lookup_restore_data lthy pointer of
      SOME refresh_data => 
        Local_Theory.declaration {syntax = false, pervasive = true}
          (fn phi => Lifting_Info.add_transfer_rules_in_restore_data pointer 
            (new_transfer_rules refresh_data lthy phi)) lthy
    | NONE => error "The lifting bundle refers to non-existent restore data."
  end

fun lifting_update_cmd bundle_name lthy = 
  update_transfer_rules (pointer_of_bundle_name bundle_name lthy) lthy

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>lifting_update\<close>
    "add newly introduced transfer rules to a bundle storing the state of Lifting and Transfer"
    (Parse.name_position >> lifting_update_cmd)

end
