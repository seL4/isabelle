(*  Title:      HOL/Tools/Lifting/lifting_setup.ML
    Author:     Ondrej Kuncar

Setting up the lifting infrastructure.
*)

signature LIFTING_SETUP =
sig
  exception SETUP_LIFTING_INFR of string

  val setup_by_quotient: bool -> thm -> thm option -> local_theory -> local_theory

  val setup_by_typedef_thm: bool -> thm -> local_theory -> local_theory
end;

structure Lifting_Setup: LIFTING_SETUP =
struct

open Lifting_Util

infix 0 MRSL

exception SETUP_LIFTING_INFR of string

fun define_cr_rel rep_fun lthy =
  let
    val (qty, rty) = (dest_funT o fastype_of) rep_fun
    val rep_fun_graph = (HOLogic.eq_const rty) $ Bound 1 $ (rep_fun $ Bound 0)
    val def_term = Abs ("x", rty, Abs ("y", qty, rep_fun_graph));
    val qty_name = (fst o dest_Type) qty
    val cr_rel_name = Binding.prefix_name "cr_" (Binding.qualified_name qty_name)  
    val (fixed_def_term, lthy') = yield_singleton (Variable.importT_terms) def_term lthy
    val ((_, (_ , def_thm)), lthy'') =
      Local_Theory.define ((cr_rel_name, NoSyn), ((Thm.def_binding cr_rel_name, []), fixed_def_term)) lthy'
  in
    (def_thm, lthy'')
  end

fun define_code_constr gen_code quot_thm lthy =
  let
    val abs = Lifting_Term.quot_thm_abs quot_thm
    val abs_background = Morphism.term (Local_Theory.target_morphism lthy) abs
  in
    if gen_code andalso is_Const abs_background then
      let
        val (const_name, typ) = dest_Const abs_background
        val fake_term = Logic.mk_type typ
        val (fixed_fake_term, lthy') = yield_singleton(Variable.importT_terms) fake_term lthy
        val fixed_type = Logic.dest_type fixed_fake_term
      in  
         Local_Theory.background_theory(Code.add_datatype [(const_name, fixed_type)]) lthy'
      end
    else
      lthy
  end

fun define_abs_type gen_code quot_thm lthy =
  if gen_code andalso Lifting_Def.can_generate_code_cert quot_thm then
    let
      val abs_type_thm = quot_thm RS @{thm Quotient_abs_rep}
      val add_abstype_attribute = 
          Thm.declaration_attribute (fn thm => Context.mapping (Code.add_abstype thm) I)
        val add_abstype_attrib = Attrib.internal (K add_abstype_attribute);
    in
      lthy
        |> (snd oo Local_Theory.note) ((Binding.empty, [add_abstype_attrib]), [abs_type_thm])
    end
  else
    lthy

fun quot_thm_sanity_check ctxt quot_thm =
  let
    val ((_, [quot_thm_fixed]), ctxt') = Variable.importT [quot_thm] ctxt 
    val (rty, qty) = Lifting_Term.quot_thm_rty_qty quot_thm_fixed
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
    if null errs then () else error (cat_lines (["Sanity check of the quotient theorem failed:",""] 
                                                @ (map Pretty.string_of errs)))
  end

fun setup_lifting_infr gen_code quot_thm maybe_reflp_thm lthy =
  let
    val _ = quot_thm_sanity_check lthy quot_thm
    val (_, qtyp) = Lifting_Term.quot_thm_rty_qty quot_thm
    val qty_full_name = (fst o dest_Type) qtyp
    val quotients = { quot_thm = quot_thm }
    fun quot_info phi = Lifting_Info.transform_quotients phi quotients
    val lthy' = case maybe_reflp_thm of
      SOME reflp_thm => lthy
        |> (snd oo Local_Theory.note) ((Binding.empty, [Lifting_Info.add_reflp_preserve_rule_attrib]),
              [reflp_thm])
        |> define_code_constr gen_code quot_thm
      | NONE => lthy
        |> define_abs_type gen_code quot_thm
  in
    lthy'
      |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Lifting_Info.update_quotients qty_full_name (quot_info phi))
  end

(*
  Sets up the Lifting package by a quotient theorem.

  gen_code - flag if an abstract type given by quot_thm should be registred 
    as an abstract type in the code generator
  quot_thm - a quotient theorem (Quotient R Abs Rep T)
  maybe_reflp_thm - a theorem saying that a relation from quot_thm is reflexive
    (in the form "reflp R")
*)

fun setup_by_quotient gen_code quot_thm maybe_reflp_thm lthy =
  let
    val transfer_attr = Attrib.internal (K Transfer.transfer_add)
    val (_, qty) = Lifting_Term.quot_thm_rty_qty quot_thm
    val induct_attr = Attrib.internal (K (Induct.induct_type (fst (dest_Type qty))))
    val qty_name = (Binding.name o Long_Name.base_name o fst o dest_Type) qty
    fun qualify suffix = Binding.qualified true suffix qty_name
    val lthy' = case maybe_reflp_thm of
      SOME reflp_thm => lthy
        |> (snd oo Local_Theory.note) ((qualify "bi_total", [transfer_attr]), 
          [[quot_thm, reflp_thm] MRSL @{thm Quotient_bi_total}])
        |> (snd oo Local_Theory.note) ((qualify "id_abs_transfer", [transfer_attr]), 
          [[quot_thm, reflp_thm] MRSL @{thm Quotient_id_abs_transfer}])
        |> (snd oo Local_Theory.note) ((qualify "abs_induct", [induct_attr]),
          [[quot_thm, reflp_thm] MRSL @{thm Quotient_total_abs_induct}])
        |> (snd oo Local_Theory.note) ((qualify "abs_eq_iff", []),
          [[quot_thm, reflp_thm] MRSL @{thm Quotient_total_abs_eq_iff}])
      | NONE => lthy
        |> (snd oo Local_Theory.note) ((qualify "All_transfer", [transfer_attr]), 
          [quot_thm RS @{thm Quotient_All_transfer}])
        |> (snd oo Local_Theory.note) ((qualify "Ex_transfer", [transfer_attr]), 
          [quot_thm RS @{thm Quotient_Ex_transfer}])
        |> (snd oo Local_Theory.note) ((qualify "forall_transfer", [transfer_attr]), 
          [quot_thm RS @{thm Quotient_forall_transfer}])
        |> (snd oo Local_Theory.note) ((qualify "abs_induct", [induct_attr]),
          [quot_thm RS @{thm Quotient_abs_induct}])
  in
    lthy'
      |> (snd oo Local_Theory.note) ((qualify "right_unique", [transfer_attr]), 
        [quot_thm RS @{thm Quotient_right_unique}])
      |> (snd oo Local_Theory.note) ((qualify "right_total", [transfer_attr]), 
        [quot_thm RS @{thm Quotient_right_total}])
      |> (snd oo Local_Theory.note) ((qualify "rel_eq_transfer", [transfer_attr]), 
        [quot_thm RS @{thm Quotient_rel_eq_transfer}])
      |> setup_lifting_infr gen_code quot_thm maybe_reflp_thm
  end

(*
  Sets up the Lifting package by a typedef theorem.

  gen_code - flag if an abstract type given by typedef_thm should be registred 
    as an abstract type in the code generator
  typedef_thm - a typedef theorem (type_definition Rep Abs S)
*)

fun setup_by_typedef_thm gen_code typedef_thm lthy =
  let
    val transfer_attr = Attrib.internal (K Transfer.transfer_add)
    val (_ $ rep_fun $ _ $ typedef_set) = (HOLogic.dest_Trueprop o prop_of) typedef_thm
    val (T_def, lthy') = define_cr_rel rep_fun lthy

    val quot_thm = case typedef_set of
      Const ("Orderings.top_class.top", _) => 
        [typedef_thm, T_def] MRSL @{thm UNIV_typedef_to_Quotient}
      | Const (@{const_name "Collect"}, _) $ Abs (_, _, _) => 
        [typedef_thm, T_def] MRSL @{thm open_typedef_to_Quotient}
      | _ => 
        [typedef_thm, T_def] MRSL @{thm typedef_to_Quotient}

    val (_, qty) = Lifting_Term.quot_thm_rty_qty quot_thm
    val qty_name = (Binding.name o Long_Name.base_name o fst o dest_Type) qty
    fun qualify suffix = Binding.qualified true suffix qty_name
    val simplify = Raw_Simplifier.rewrite_rule [mk_meta_eq @{thm mem_Collect_eq}]

    val (maybe_reflp_thm, lthy'') = case typedef_set of
      Const ("Orderings.top_class.top", _) => 
        let
          val equivp_thm = typedef_thm RS @{thm UNIV_typedef_to_equivp}
          val reflp_thm = equivp_thm RS @{thm equivp_reflp2}
        in
          lthy'
            |> (snd oo Local_Theory.note) ((qualify "bi_total", [transfer_attr]), 
              [[quot_thm, reflp_thm] MRSL @{thm Quotient_bi_total}])
            |> (snd oo Local_Theory.note) ((qualify "id_abs_transfer", [transfer_attr]), 
              [[quot_thm, reflp_thm] MRSL @{thm Quotient_id_abs_transfer}])
            |> pair (SOME reflp_thm)
        end
      | _ => lthy'
        |> (snd oo Local_Theory.note) ((qualify "All_transfer", [transfer_attr]), 
          [[typedef_thm, T_def] MRSL @{thm typedef_All_transfer}])
        |> (snd oo Local_Theory.note) ((qualify "Ex_transfer", [transfer_attr]), 
          [[typedef_thm, T_def] MRSL @{thm typedef_Ex_transfer}])
        |> (snd oo Local_Theory.note) ((qualify "forall_transfer", [transfer_attr]), 
          [simplify ([typedef_thm, T_def] MRSL @{thm typedef_forall_transfer})])
        |> pair NONE
  in
    lthy''
      |> (snd oo Local_Theory.note) ((qualify "bi_unique", [transfer_attr]), 
        [[typedef_thm, T_def] MRSL @{thm typedef_bi_unique}])
      |> (snd oo Local_Theory.note) ((qualify "rep_transfer", [transfer_attr]), 
        [[typedef_thm, T_def] MRSL @{thm typedef_rep_transfer}])
      |> (snd oo Local_Theory.note) ((qualify "right_unique", [transfer_attr]), 
        [[quot_thm] MRSL @{thm Quotient_right_unique}])
      |> (snd oo Local_Theory.note) ((qualify "right_total", [transfer_attr]), 
        [[quot_thm] MRSL @{thm Quotient_right_total}])
      |> setup_lifting_infr gen_code quot_thm maybe_reflp_thm
  end

fun setup_lifting_cmd gen_code xthm opt_reflp_xthm lthy =
  let 
    val input_thm = singleton (Attrib.eval_thms lthy) xthm
    val input_term = (HOLogic.dest_Trueprop o prop_of) input_thm
      handle TERM _ => error "Unsupported type of a theorem. Only Quotient or type_definition are supported."

    fun sanity_check_reflp_thm reflp_thm = 
      let
        val reflp_tm = (HOLogic.dest_Trueprop o prop_of) reflp_thm
          handle TERM _ => error "Invalid form of the reflexivity theorem. Use \"reflp R\"."
      in
        case reflp_tm of
          Const (@{const_name reflp}, _) $ _ => ()
          | _ => error "Invalid form of the reflexivity theorem. Use \"reflp R\"."
      end

    fun setup_quotient () = 
      case opt_reflp_xthm of
        SOME reflp_xthm => 
          let
            val reflp_thm = singleton (Attrib.eval_thms lthy) reflp_xthm
            val _ = sanity_check_reflp_thm reflp_thm
          in
            setup_by_quotient gen_code input_thm (SOME reflp_thm) lthy
          end
        | NONE => setup_by_quotient gen_code input_thm NONE lthy

    fun setup_typedef () = 
      case opt_reflp_xthm of
        SOME _ => error "The reflexivity theorem cannot be specified if the type_definition theorem is used."
        | NONE => setup_by_typedef_thm gen_code input_thm lthy
  in
    case input_term of
      (Const (@{const_name Quotient}, _) $ _ $ _ $ _ $ _) => setup_quotient ()
      | (Const (@{const_name type_definition}, _) $ _ $ _ $ _) => setup_typedef ()
      | _ => error "Unsupported type of a theorem. Only Quotient or type_definition are supported."
  end

val opt_gen_code =
  Scan.optional (@{keyword "("} |-- Parse.!!! ((Parse.reserved "no_code" >> K false) --| @{keyword ")"})) true

val _ = 
  Outer_Syntax.local_theory @{command_spec "setup_lifting"}
    "Setup lifting infrastructure" 
      (opt_gen_code -- Parse_Spec.xthm -- Scan.option Parse_Spec.xthm >> 
        (fn ((gen_code, xthm), opt_reflp_xthm) => setup_lifting_cmd gen_code xthm opt_reflp_xthm))
end;
