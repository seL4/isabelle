(*  Title:      HOL/Tools/Lifting/lifting_term.ML
    Author:     Ondrej Kuncar

Proves Quotient theorem.
*)

signature LIFTING_TERM =
sig
  exception QUOT_THM of typ * typ * Pretty.T

  val prove_quot_theorem: Proof.context -> typ * typ -> thm

  val absrep_fun: Proof.context -> typ * typ -> term

  (* Allows Nitpick to represent quotient types as single elements from raw type *)
  (* val absrep_const_chk: Proof.context -> flag -> string -> term *)

  val equiv_relation: Proof.context -> typ * typ -> term

  val quot_thm_rel: thm -> term
  val quot_thm_abs: thm -> term
  val quot_thm_rep: thm -> term
  val quot_thm_rty_qty: thm -> typ * typ
end

structure Lifting_Term: LIFTING_TERM =
struct

(* generation of the Quotient theorem  *)

exception QUOT_THM_INTERNAL of Pretty.T
exception QUOT_THM of typ * typ * Pretty.T

(* matches a type pattern with a type *)
fun match ctxt err ty_pat ty =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    Sign.typ_match thy (ty_pat, ty) Vartab.empty
      handle Type.TYPE_MATCH => err ctxt ty_pat ty
  end

fun equiv_match_err ctxt ty_pat ty =
  let
    val ty_pat_str = Syntax.string_of_typ ctxt ty_pat
    val ty_str = Syntax.string_of_typ ctxt ty
  in
    raise QUOT_THM_INTERNAL (Pretty.block
      [Pretty.str ("The quotient type " ^ quote ty_str),
       Pretty.brk 1,
       Pretty.str ("and the quotient type pattern " ^ quote ty_pat_str),
       Pretty.brk 1,
       Pretty.str "don't match."])
  end

fun get_quot_thm ctxt s =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    (case Lifting_Info.lookup_quotients ctxt s of
      SOME qdata => Thm.transfer thy (#quot_thm qdata)
    | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
      [Pretty.str ("No quotient type " ^ quote s), 
       Pretty.brk 1, 
       Pretty.str "found."]))
  end

fun get_rel_quot_thm ctxt s =
   let
    val thy = Proof_Context.theory_of ctxt
  in
    (case Lifting_Info.lookup_quotmaps ctxt s of
      SOME map_data => Thm.transfer thy (#quot_thm map_data)
    | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
      [Pretty.str ("No relator for the type " ^ quote s), 
       Pretty.brk 1,
       Pretty.str "found."]))
  end

fun is_id_quot thm = (prop_of thm = prop_of @{thm identity_quotient})

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

exception NOT_IMPL of string

fun dest_Quotient (Const (@{const_name Quotient}, _) $ rel $ abs $ rep $ cr)
      = (rel, abs, rep, cr)
  | dest_Quotient t = raise TERM ("dest_Quotient", [t])

fun quot_thm_rel quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (rel, _, _, _) => rel

fun quot_thm_abs quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (_, abs, _, _) => abs

fun quot_thm_rep quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (_, _, rep, _) => rep

fun quot_thm_rty_qty quot_thm =
  let
    val abs = quot_thm_abs quot_thm
    val abs_type = fastype_of abs  
  in
    (domain_type abs_type, range_type abs_type)
  end

fun check_raw_types (provided_rty_name, rty_of_qty_name) qty_name =
  if provided_rty_name <> rty_of_qty_name then
    raise QUOT_THM_INTERNAL (Pretty.block 
        [Pretty.str ("The type " ^ quote provided_rty_name),
         Pretty.brk 1,
         Pretty.str ("is not a raw type for the quotient type " ^ quote qty_name ^ ";"),
         Pretty.brk 1,
         Pretty.str ("the correct raw type is " ^ quote rty_of_qty_name ^ ".")])
  else
    ()

fun prove_quot_theorem' ctxt (rty, qty) =
  (case (rty, qty) of
    (Type (s, tys), Type (s', tys')) =>
      if s = s'
      then
        let
          val args = map (prove_quot_theorem' ctxt) (tys ~~ tys')
        in
          if forall is_id_quot args
          then
            @{thm identity_quotient}
          else
            args MRSL (get_rel_quot_thm ctxt s)
        end
      else
        let
          val quot_thm = get_quot_thm ctxt s'
          val (Type (rs, rtys), qty_pat) = quot_thm_rty_qty quot_thm
          val _ = check_raw_types (s, rs) s'
          val qtyenv = match ctxt equiv_match_err qty_pat qty
          val rtys' = map (Envir.subst_type qtyenv) rtys
          val args = map (prove_quot_theorem' ctxt) (tys ~~ rtys')
        in
          if forall is_id_quot args
          then
            quot_thm
          else
            let
              val rel_quot_thm = args MRSL (get_rel_quot_thm ctxt s)
            in
              [rel_quot_thm, quot_thm] MRSL @{thm Quotient_compose}
           end
        end
  | _ => @{thm identity_quotient})
    handle QUOT_THM_INTERNAL pretty_msg => raise QUOT_THM (rty, qty, pretty_msg)

fun force_qty_type thy qty quot_thm =
  let
    val abs_schematic = quot_thm_abs quot_thm 
    val qty_schematic = (range_type o fastype_of) abs_schematic  
    val match_env = Sign.typ_match thy (qty_schematic, qty) Vartab.empty
    fun prep_ty thy (x, (S, ty)) =
      (ctyp_of thy (TVar (x, S)), ctyp_of thy ty)
    val ty_inst = Vartab.fold (cons o (prep_ty thy)) match_env []
  in
    Thm.instantiate (ty_inst, []) quot_thm
  end

fun prove_quot_theorem ctxt (rty, qty) =
  let
    val thy = Proof_Context.theory_of ctxt
    val quot_thm = prove_quot_theorem' ctxt (rty, qty)
  in
    force_qty_type thy qty quot_thm
  end

fun absrep_fun ctxt (rty, qty) =
  quot_thm_abs (prove_quot_theorem ctxt (rty, qty))

fun equiv_relation ctxt (rty, qty) =
  quot_thm_rel (prove_quot_theorem ctxt (rty, qty))

end;
