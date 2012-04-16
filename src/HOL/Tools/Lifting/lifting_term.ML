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

fun quotient_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val (_, abs, _, _) = dest_Quotient (HOLogic.dest_Trueprop t)
    val (rty, qty) = Term.dest_funT (fastype_of abs)
  in
    case (rty, qty) of
      (Type (s, _), Type (s', _)) =>
      if s = s'
      then
        let
          val thm1 = SOME @{thm identity_quotient}
          val thm2 = try (get_rel_quot_thm ctxt) s
        in
          resolve_tac (map_filter I [thm1, thm2]) i
        end
      else
        let
          val quot_thm = get_quot_thm ctxt s'
          val (Type (rs, _), _) = quot_thm_rty_qty quot_thm
          val _ = check_raw_types (s, rs) s'
        in
          resolve_tac [quot_thm, quot_thm RSN (2, @{thm Quotient_compose})] i
        end
    | (_, Type (s, _)) =>
      let
        val thm1 = try (get_quot_thm ctxt) s
        val thm2 = SOME @{thm identity_quotient}
        val thm3 = try (get_rel_quot_thm ctxt) s
      in
        resolve_tac (map_filter I [thm1, thm2, thm3]) i
      end
  | _ => rtac @{thm identity_quotient} i
    handle QUOT_THM_INTERNAL pretty_msg => raise QUOT_THM (rty, qty, pretty_msg)
  end)

fun prove_quot_theorem ctxt (rty, qty) =
  let
    val relT = [rty, rty] ---> HOLogic.boolT
    val absT = rty --> qty
    val repT = qty --> rty
    val crT = [rty, qty] ---> HOLogic.boolT
    val quotT = [relT, absT, repT, crT] ---> HOLogic.boolT
    val rel = Var (("R", 0), relT)
    val abs = Var (("Abs", 0), absT)
    val rep = Var (("Rep", 0), repT)
    val cr = Var (("T", 0), crT)
    val quot = Const (@{const_name Quotient}, quotT)
    val goal = HOLogic.Trueprop $ (quot $ rel $ abs $ rep $ cr)
    val cgoal = Thm.cterm_of (Proof_Context.theory_of ctxt) goal
    val tac = REPEAT (quotient_tac ctxt 1)
  in
    Goal.prove_internal [] cgoal (K tac)
  end

fun absrep_fun ctxt (rty, qty) =
  quot_thm_abs (prove_quot_theorem ctxt (rty, qty))

fun equiv_relation ctxt (rty, qty) =
  quot_thm_rel (prove_quot_theorem ctxt (rty, qty))

end;
