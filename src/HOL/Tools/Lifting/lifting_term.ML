(*  Title:      HOL/Tools/Lifting/lifting_term.ML
    Author:     Ondrej Kuncar

Proves Quotient theorem.
*)

signature LIFTING_TERM =
sig
  exception QUOT_THM of typ * typ * Pretty.T
  exception CHECK_RTY of typ * typ

  val prove_quot_thm: Proof.context -> typ * typ -> thm

  val abs_fun: Proof.context -> typ * typ -> term

  val equiv_relation: Proof.context -> typ * typ -> term
end

structure Lifting_Term: LIFTING_TERM =
struct

open Lifting_Util

infix 0 MRSL

exception QUOT_THM_INTERNAL of Pretty.T
exception QUOT_THM of typ * typ * Pretty.T
exception CHECK_RTY of typ * typ

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
      SOME map_data => Thm.transfer thy (#rel_quot_thm map_data)
    | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
      [Pretty.str ("No relator for the type " ^ quote s), 
       Pretty.brk 1,
       Pretty.str "found."]))
  end

fun is_id_quot thm = (prop_of thm = prop_of @{thm identity_quotient})

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

fun zip_Tvars ctxt type_name rty_Tvars qty_Tvars =
  case try (get_rel_quot_thm ctxt) type_name of
    NONE => rty_Tvars ~~ qty_Tvars
    | SOME rel_quot_thm =>
      let 
        fun quot_term_absT quot_term = 
          let 
            val (_, abs, _, _) = (dest_Quotient o HOLogic.dest_Trueprop) quot_term
          in
            fastype_of abs
          end

        fun equiv_univ_err ctxt ty_pat ty =
          let
            val ty_pat_str = Syntax.string_of_typ ctxt ty_pat
            val ty_str = Syntax.string_of_typ ctxt ty
          in
            raise QUOT_THM_INTERNAL (Pretty.block
              [Pretty.str ("The type " ^ quote ty_str),
               Pretty.brk 1,
               Pretty.str ("and the relator type pattern " ^ quote ty_pat_str),
               Pretty.brk 1,
               Pretty.str "don't unify."])
          end

        fun raw_match (TVar (v, S), T) subs =
              (case Vartab.defined subs v of
                false => Vartab.update_new (v, (S, T)) subs
              | true => subs)
          | raw_match (Type (_, Ts), Type (_, Us)) subs =
              raw_matches (Ts, Us) subs
          | raw_match _ subs = subs
        and raw_matches (T :: Ts, U :: Us) subs = raw_matches (Ts, Us) (raw_match (T, U) subs)
          | raw_matches _ subs = subs

        val rty = Type (type_name, rty_Tvars)
        val qty = Type (type_name, qty_Tvars)
        val rel_quot_thm_concl = (Logic.strip_imp_concl o prop_of) rel_quot_thm
        val schematic_rel_absT = quot_term_absT rel_quot_thm_concl;
        val ctxt' = Variable.declare_typ schematic_rel_absT ctxt
        val thy = Proof_Context.theory_of ctxt'
        val absT = rty --> qty
        val schematic_absT = Logic.type_map (singleton (Variable.polymorphic ctxt')) absT
        val maxidx = Term.maxidx_of_typs [schematic_rel_absT, schematic_absT]
        val _ = Sign.typ_unify thy (schematic_rel_absT, schematic_absT) (Vartab.empty,maxidx)
          handle Type.TUNIFY => equiv_univ_err ctxt schematic_rel_absT schematic_absT
        val subs = raw_match (schematic_rel_absT, absT) Vartab.empty
        val rel_quot_thm_prems = (Logic.strip_imp_prems o prop_of) rel_quot_thm
      in
        map (dest_funT o 
             Envir.subst_type subs o
             quot_term_absT) 
          rel_quot_thm_prems
      end

fun prove_schematic_quot_thm ctxt (rty, qty) =
  (case (rty, qty) of
    (Type (s, tys), Type (s', tys')) =>
      if s = s'
      then
        let
          val args = map (prove_schematic_quot_thm ctxt) (zip_Tvars ctxt s tys tys')
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
          val args = map (prove_schematic_quot_thm ctxt) (tys ~~ rtys')
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
    | (_, Type (s', tys')) => 
      (case try (get_quot_thm ctxt) s' of
        SOME quot_thm => 
          let
            val rty_pat = (fst o quot_thm_rty_qty) quot_thm
          in
            prove_schematic_quot_thm ctxt (rty_pat, qty)
          end
        | NONE =>
          let
            val rty_pat = Type (s', map (fn _ => TFree ("a",[])) tys')
          in
            prove_schematic_quot_thm ctxt (rty_pat, qty)
          end)
    | _ => @{thm identity_quotient})
    handle QUOT_THM_INTERNAL pretty_msg => raise QUOT_THM (rty, qty, pretty_msg)

fun force_qty_type thy qty quot_thm =
  let
    val (_, qty_schematic) = quot_thm_rty_qty quot_thm
    val match_env = Sign.typ_match thy (qty_schematic, qty) Vartab.empty
    fun prep_ty thy (x, (S, ty)) =
      (ctyp_of thy (TVar (x, S)), ctyp_of thy ty)
    val ty_inst = Vartab.fold (cons o (prep_ty thy)) match_env []
  in
    Thm.instantiate (ty_inst, []) quot_thm
  end

fun check_rty_type ctxt rty quot_thm =
  let  
    val thy = Proof_Context.theory_of ctxt
    val (rty_forced, _) = quot_thm_rty_qty quot_thm
    val rty_schematic = Logic.type_map (singleton (Variable.polymorphic ctxt)) rty
    val _ = Sign.typ_match thy (rty_schematic, rty_forced) Vartab.empty
      handle Type.TYPE_MATCH => raise CHECK_RTY (rty_schematic, rty_forced)
  in
    ()
  end

(*
  The function tries to prove that rty and qty form a quotient.

  Returns: Quotient theorem; an abstract type of the theorem is exactly
    qty, a representation type of the theorem is an instance of rty in general.
*)

fun prove_quot_thm ctxt (rty, qty) =
  let
    val thy = Proof_Context.theory_of ctxt
    val schematic_quot_thm = prove_schematic_quot_thm ctxt (rty, qty)
    val quot_thm = force_qty_type thy qty schematic_quot_thm
    val _ = check_rty_type ctxt rty quot_thm
  in
    quot_thm
  end

fun abs_fun ctxt (rty, qty) =
  quot_thm_abs (prove_quot_thm ctxt (rty, qty))

fun equiv_relation ctxt (rty, qty) =
  quot_thm_rel (prove_quot_thm ctxt (rty, qty))

end;
