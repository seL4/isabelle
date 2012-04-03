(*  Title:      HOL/Tools/Lifting/lifting_setup.ML
    Author:     Ondrej Kuncar

Setting the lifting infranstructure up.
*)

signature LIFTING_SETUP =
sig
  exception SETUP_LIFTING_INFR of string

  val setup_lifting_infr: thm -> thm -> local_theory -> local_theory

  val setup_by_typedef_thm: thm -> local_theory -> local_theory
end;

structure Lifting_Seup: LIFTING_SETUP =
struct

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

exception SETUP_LIFTING_INFR of string

fun define_cr_rel equiv_thm abs_fun lthy =
  let
    fun force_type_of_rel rel forced_ty =
      let
        val thy = Proof_Context.theory_of lthy
        val rel_ty = (domain_type o fastype_of) rel
        val ty_inst = Sign.typ_match thy (rel_ty, forced_ty) Vartab.empty
      in
        Envir.subst_term_types ty_inst rel
      end

    val (rty, qty) = (dest_funT o fastype_of) abs_fun
    val abs_fun_graph = HOLogic.mk_eq(abs_fun $ Bound 1, Bound 0)
    val Abs_body = (case (HOLogic.dest_Trueprop o prop_of) equiv_thm of
      Const (@{const_name equivp}, _) $ _ => abs_fun_graph
      | Const (@{const_name part_equivp}, _) $ rel => 
        HOLogic.mk_conj (force_type_of_rel rel rty $ Bound 1 $ Bound 1, abs_fun_graph)
      | _ => raise SETUP_LIFTING_INFR "unsopported equivalence theorem"
      )
    val def_term = Abs ("x", rty, Abs ("y", qty, Abs_body));
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

fun setup_lifting_infr quot_thm equiv_thm lthy =
  let
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
        val (_ $ _ $ abs_fun $ _) = (HOLogic.dest_Trueprop o prop_of) typedef_thm
        val equiv_thm = typedef_thm RS to_equiv_thm
        val (T_def, lthy') = define_cr_rel equiv_thm abs_fun lthy
        val quot_thm =  [typedef_thm, T_def] MRSL to_quot_thm
      in
        (quot_thm, equiv_thm, lthy')
      end

    val typedef_set = (snd o dest_comb o HOLogic.dest_Trueprop o prop_of) typedef_thm
    val (quot_thm, equiv_thm, lthy') = (case typedef_set of
      Const ("Orderings.top_class.top", _) => 
        derive_quot_and_equiv_thm @{thm copy_type_to_Quotient} @{thm copy_type_to_equivp} 
          typedef_thm lthy
      | Const (@{const_name "Collect"}, _) $ Abs (_, _, _) => 
        derive_quot_and_equiv_thm @{thm invariant_type_to_Quotient} @{thm invariant_type_to_part_equivp} 
          typedef_thm lthy
      | _ => raise SETUP_LIFTING_INFR "unsupported typedef theorem")
  in
    setup_lifting_infr quot_thm equiv_thm lthy'
  end

fun setup_by_typedef_thm_aux xthm lthy = setup_by_typedef_thm (singleton (Attrib.eval_thms lthy) xthm) lthy

val _ = 
  Outer_Syntax.local_theory @{command_spec "setup_lifting"}
    "Setup lifting infrastracture" 
      (Parse_Spec.xthm >> (fn xthm => setup_by_typedef_thm_aux xthm))

end;
