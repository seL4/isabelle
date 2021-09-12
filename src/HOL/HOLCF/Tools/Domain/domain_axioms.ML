(*  Title:      HOL/HOLCF/Tools/Domain/domain_axioms.ML
    Author:     David von Oheimb
    Author:     Brian Huffman

Syntax generator for domain command.
*)

signature DOMAIN_AXIOMS =
sig
  val axiomatize_isomorphism :
      binding * (typ * typ) ->
      theory -> Domain_Take_Proofs.iso_info * theory

  val axiomatize_lub_take :
      binding * term -> theory -> thm * theory

  val add_axioms :
      (binding * mixfix * (typ * typ)) list -> theory ->
      (Domain_Take_Proofs.iso_info list
       * Domain_Take_Proofs.take_induct_info) * theory
end


structure Domain_Axioms : DOMAIN_AXIOMS =
struct

open HOLCF_Library

infixr 6 ->>
infix -->>
infix 9 `

fun axiomatize_isomorphism
    (dbind : binding, (lhsT, rhsT))
    (thy : theory)
    : Domain_Take_Proofs.iso_info * theory =
  let
    val abs_bind = Binding.suffix_name "_abs" dbind
    val rep_bind = Binding.suffix_name "_rep" dbind

    val (abs_const, thy) =
        Sign.declare_const_global ((abs_bind, rhsT ->> lhsT), NoSyn) thy
    val (rep_const, thy) =
        Sign.declare_const_global ((rep_bind, lhsT ->> rhsT), NoSyn) thy

    val x = Free ("x", lhsT)
    val y = Free ("y", rhsT)

    val abs_iso_eqn =
        Logic.all y (mk_trp (mk_eq (rep_const ` (abs_const ` y), y)))
    val rep_iso_eqn =
        Logic.all x (mk_trp (mk_eq (abs_const ` (rep_const ` x), x)))

    val abs_iso_bind = Binding.qualify_name true dbind "abs_iso"
    val rep_iso_bind = Binding.qualify_name true dbind "rep_iso"

    val (abs_iso_thm, thy) = Specification.axiom ((abs_iso_bind, []), abs_iso_eqn) thy
    val (rep_iso_thm, thy) = Specification.axiom ((rep_iso_bind, []), rep_iso_eqn) thy

    val result =
        {
          absT = lhsT,
          repT = rhsT,
          abs_const = abs_const,
          rep_const = rep_const,
          abs_inverse = Drule.export_without_context abs_iso_thm,
          rep_inverse = Drule.export_without_context rep_iso_thm
        }
  in
    (result, thy)
  end

fun axiomatize_lub_take
    (dbind : binding, take_const : term)
    (thy : theory)
    : thm * theory =
  let
    val i = Free ("i", \<^Type>\<open>nat\<close>)
    val T = (fst o dest_cfunT o range_type o fastype_of) take_const

    val lub_take_eqn =
        mk_trp (mk_eq (mk_lub (lambda i (take_const $ i)), mk_ID T))

    val lub_take_bind = Binding.qualify_name true dbind "lub_take"

    val (lub_take_thm, thy) = Specification.axiom ((lub_take_bind, []), lub_take_eqn) thy
  in
    (lub_take_thm, thy)
  end

fun add_axioms
    (dom_eqns : (binding * mixfix * (typ * typ)) list)
    (thy : theory) =
  let

    val dbinds = map #1 dom_eqns

    (* declare new types *)
    fun thy_type (dbind, mx, (lhsT, _)) =
        (dbind, (length o snd o dest_Type) lhsT, mx)
    val thy = Sign.add_types_global (map thy_type dom_eqns) thy

    (* axiomatize type constructor arities *)
    fun thy_arity (_, _, (lhsT, _)) =
        let val (dname, tvars) = dest_Type lhsT
        in (dname, map (snd o dest_TFree) tvars, \<^sort>\<open>pcpo\<close>) end
    val thy = fold (Axclass.arity_axiomatization o thy_arity) dom_eqns thy

    (* declare and axiomatize abs/rep *)
    val (iso_infos, thy) =
        fold_map axiomatize_isomorphism
          (map (fn (dbind, _, eqn) => (dbind, eqn)) dom_eqns) thy

    (* define take functions *)
    val (take_info, thy) =
        Domain_Take_Proofs.define_take_functions
          (dbinds ~~ iso_infos) thy

    (* declare lub_take axioms *)
    val (lub_take_thms, thy) =
        fold_map axiomatize_lub_take
          (dbinds ~~ #take_consts take_info) thy

    (* prove additional take theorems *)
    val (take_info2, thy) =
        Domain_Take_Proofs.add_lub_take_theorems
          (dbinds ~~ iso_infos) take_info lub_take_thms thy

    (* define map functions *)
    val (_, thy) =
        Domain_Isomorphism.define_map_functions
          (dbinds ~~ iso_infos) thy

  in
    ((iso_infos, take_info2), thy)
  end

end (* struct *)
