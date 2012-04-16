(*  Title:      HOL/Tools/Lifting/lifting_setup.ML
    Author:     Ondrej Kuncar

Setting up the lifting infrastructure.
*)

signature LIFTING_SETUP =
sig
  exception SETUP_LIFTING_INFR of string

  val setup_lifting_infr: thm -> thm -> local_theory -> local_theory

  val setup_by_typedef_thm: thm -> local_theory -> local_theory
end;

structure Lifting_Setup: LIFTING_SETUP =
struct

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

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

fun define_abs_type quot_thm lthy =
  if Lifting_Def.can_generate_code_cert quot_thm then
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
      (case subtract (op =) qty_tfreesT rty_tfreesT of
        [] => []
      | extras => [Pretty.block ([Pretty.str "Extra variables in the raw type:",
                                 Pretty.brk 1] @ 
                                 ((Pretty.commas o map (Pretty.str o quote)) extras) @
                                 [Pretty.str "."])])
    val not_type_constr = 
      (case qty of
         Type _ => []
         | _ => [Pretty.block [Pretty.str "The quotient type ",
                                Pretty.quote (Syntax.pretty_typ ctxt' qty),
                                Pretty.brk 1,
                                Pretty.str "is not a type constructor."]])
    val errs = extra_rty_tfrees @ not_type_constr
  in
    if null errs then () else error (cat_lines (["Sanity check of the quotient theorem failed:",""] 
                                                @ (map Pretty.string_of errs)))
  end

fun setup_lifting_infr quot_thm equiv_thm lthy =
  let
    val _ = quot_thm_sanity_check lthy quot_thm
    val (_, qtyp) = Lifting_Term.quot_thm_rty_qty quot_thm
    val qty_full_name = (fst o dest_Type) qtyp
    val quotients = { quot_thm = quot_thm }
    fun quot_info phi = Lifting_Info.transform_quotients phi quotients
  in
    lthy
      |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Lifting_Info.update_quotients qty_full_name (quot_info phi))
      |> define_abs_type quot_thm
  end

fun setup_by_typedef_thm typedef_thm lthy =
  let
    fun derive_quot_and_equiv_thm to_quot_thm to_equiv_thm typedef_thm lthy =
      let
        val (_ $ rep_fun $ _ $ _) = (HOLogic.dest_Trueprop o prop_of) typedef_thm
        val equiv_thm = typedef_thm RS to_equiv_thm
        val (T_def, lthy') = define_cr_rel rep_fun lthy
        val quot_thm =  [typedef_thm, T_def] MRSL to_quot_thm
      in
        (quot_thm, equiv_thm, lthy')
      end

    val typedef_set = (snd o dest_comb o HOLogic.dest_Trueprop o prop_of) typedef_thm
    val (quot_thm, equiv_thm, lthy') = (case typedef_set of
      Const ("Orderings.top_class.top", _) => 
        derive_quot_and_equiv_thm @{thm UNIV_typedef_to_Quotient} @{thm UNIV_typedef_to_equivp} 
          typedef_thm lthy
      | Const (@{const_name "Collect"}, _) $ Abs (_, _, _) => 
        derive_quot_and_equiv_thm @{thm open_typedef_to_Quotient} @{thm open_typedef_to_part_equivp} 
          typedef_thm lthy
      | _ => derive_quot_and_equiv_thm @{thm typedef_to_Quotient} @{thm typedef_to_part_equivp} 
          typedef_thm lthy)
  in
    setup_lifting_infr quot_thm equiv_thm lthy'
  end

fun setup_by_typedef_thm_aux xthm lthy = setup_by_typedef_thm (singleton (Attrib.eval_thms lthy) xthm) lthy

val _ = 
  Outer_Syntax.local_theory @{command_spec "setup_lifting"}
    "Setup lifting infrastructure" 
      (Parse_Spec.xthm >> (fn xthm => setup_by_typedef_thm_aux xthm))
end;
