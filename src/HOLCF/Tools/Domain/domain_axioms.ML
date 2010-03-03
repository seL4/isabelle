(*  Title:      HOLCF/Tools/Domain/domain_axioms.ML
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

  val copy_of_dtyp :
      string Symtab.table -> (int -> term) -> Datatype.dtyp -> term

  val add_axioms :
      (binding * (typ * typ)) list ->
      theory -> theory
end;


structure Domain_Axioms : DOMAIN_AXIOMS =
struct

(* TODO: move copy_of_dtyp somewhere else! *)
local open Domain_Library in

infixr 0 ===>;infixr 0 ==>;infix 0 == ; 
infix 1 ===; infix 1 ~= ; infix 1 <<; infix 1 ~<<;
infix 9 `   ; infix 9 `% ; infix 9 `%%; infixr 9 oo;

(* FIXME: use theory data for this *)
val copy_tab : string Symtab.table =
    Symtab.make [(@{type_name cfun}, @{const_name "cfun_map"}),
                 (@{type_name ssum}, @{const_name "ssum_map"}),
                 (@{type_name sprod}, @{const_name "sprod_map"}),
                 (@{type_name "*"}, @{const_name "cprod_map"}),
                 (@{type_name "u"}, @{const_name "u_map"})];

fun copy_of_dtyp tab r dt =
    if Datatype_Aux.is_rec_type dt then copy tab r dt else ID
and copy tab r (Datatype_Aux.DtRec i) = r i
  | copy tab r (Datatype_Aux.DtTFree a) = ID
  | copy tab r (Datatype_Aux.DtType (c, ds)) =
    case Symtab.lookup tab c of
      SOME f => list_ccomb (%%:f, map (copy_of_dtyp tab r) ds)
    | NONE => (warning ("copy_of_dtyp: unknown type constructor " ^ c); ID);

end; (* local open *)

open HOLCF_Library;

fun axiomatize_isomorphism
    (dbind : binding, (lhsT, rhsT))
    (thy : theory)
    : Domain_Take_Proofs.iso_info * theory =
  let
    val dname = Long_Name.base_name (Binding.name_of dbind);

    val abs_bind = Binding.suffix_name "_abs" dbind;
    val rep_bind = Binding.suffix_name "_rep" dbind;

    val (abs_const, thy) =
        Sign.declare_const ((abs_bind, rhsT ->> lhsT), NoSyn) thy;
    val (rep_const, thy) =
        Sign.declare_const ((rep_bind, lhsT ->> rhsT), NoSyn) thy;

    val x = Free ("x", lhsT);
    val y = Free ("y", rhsT);

    val abs_iso_eqn =
        Logic.all y (mk_trp (mk_eq (rep_const ` (abs_const ` y), y)));
    val rep_iso_eqn =
        Logic.all x (mk_trp (mk_eq (abs_const ` (rep_const ` x), x)));

    val thy = Sign.add_path dname thy;

    val (abs_iso_thm, thy) =
        yield_singleton PureThy.add_axioms
        ((Binding.name "abs_iso", abs_iso_eqn), []) thy;

    val (rep_iso_thm, thy) =
        yield_singleton PureThy.add_axioms
        ((Binding.name "rep_iso", rep_iso_eqn), []) thy;

    val thy = Sign.parent_path thy;

    val result =
        {
          absT = lhsT,
          repT = rhsT,
          abs_const = abs_const,
          rep_const = rep_const,
          abs_inverse = abs_iso_thm,
          rep_inverse = rep_iso_thm
        };
  in
    (result, thy)
  end;

fun axiomatize_lub_take
    (dbind : binding, take_const : term)
    (thy : theory)
    : thm * theory =
  let
    val dname = Long_Name.base_name (Binding.name_of dbind);

    val i = Free ("i", natT);
    val T = (fst o dest_cfunT o range_type o fastype_of) take_const;

    val lub_take_eqn =
        mk_trp (mk_eq (mk_lub (lambda i (take_const $ i)), mk_ID T));

    val thy = Sign.add_path dname thy;

    val (lub_take_thm, thy) =
        yield_singleton PureThy.add_axioms
        ((Binding.name "lub_take", lub_take_eqn), []) thy;

    val thy = Sign.parent_path thy;
  in
    (lub_take_thm, thy)
  end;

fun add_axioms
    (dom_eqns : (binding * (typ * typ)) list)
    (thy : theory) =
  let

    (* declare and axiomatize abs/rep *)
    val (iso_infos, thy) =
        fold_map axiomatize_isomorphism dom_eqns thy;

    (* define take functions *)
    val (take_info, thy) =
        Domain_Take_Proofs.define_take_functions
          (map fst dom_eqns ~~ iso_infos) thy;

    (* declare lub_take axioms *)
    val (lub_take_thms, thy) =
        fold_map axiomatize_lub_take
          (map fst dom_eqns ~~ #take_consts take_info) thy;

  in
    thy (* TODO: also return iso_infos, take_info, lub_take_thms *)
  end;

end; (* struct *)
