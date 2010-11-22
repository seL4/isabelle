(*  Title:      HOL/Tools/SMT/z3_proof_methods.ML
    Author:     Sascha Boehme, TU Muenchen

Proof methods for Z3 proof reconstruction.
*)

signature Z3_PROOF_METHODS =
sig
  val prove_injectivity: Proof.context -> cterm -> thm
end

structure Z3_Proof_Methods: Z3_PROOF_METHODS =
struct

structure U = SMT_Utils


fun apply tac st =
  (case Seq.pull (tac 1 st) of
    NONE => raise THM ("tactic failed", 1, [st])
  | SOME (st', _) => st')



(* injectivity *)

local

val B = @{typ bool}
fun mk_univ T = Const (@{const_name top}, T --> B)
fun mk_inj_on T U =
  Const (@{const_name inj_on}, (T --> U) --> (T --> B) --> B)
fun mk_inv_into T U =
  Const (@{const_name inv_into}, [T --> B, T --> U, U] ---> T)

fun mk_inv_of ctxt ct =
  let
    val T = #T (Thm.rep_cterm ct)
    val dT = Term.domain_type T
    val inv = U.certify ctxt (mk_inv_into dT (Term.range_type T))
    val univ = U.certify ctxt (mk_univ dT)
  in Thm.mk_binop inv univ ct end

fun mk_inj_prop ctxt ct =
  let
    val T = #T (Thm.rep_cterm ct)
    val dT = Term.domain_type T
    val inj = U.certify ctxt (mk_inj_on dT (Term.range_type T))
    val univ = U.certify ctxt (mk_univ dT)
  in U.mk_cprop (Thm.mk_binop inj ct univ) end


val disjE = @{lemma "~P | Q ==> P ==> Q" by fast}

fun prove_inj_prop ctxt hdef lhs =
  let
    val (ct, ctxt') = U.dest_all_cabs (Thm.rhs_of hdef) ctxt
    val rule = disjE OF [Object_Logic.rulify (Thm.assume lhs)]
  in
    Goal.init (mk_inj_prop ctxt' (Thm.dest_arg ct))
    |> apply (Tactic.rtac @{thm injI})
    |> apply (Tactic.solve_tac [rule, rule RS @{thm sym}])
    |> Goal.norm_result o Goal.finish ctxt'
    |> singleton (Variable.export ctxt' ctxt)
  end

fun prove_rhs ctxt hdef lhs rhs =
  Goal.init rhs
  |> apply (CONVERSION (Conv.top_sweep_conv (K (Conv.rewr_conv hdef)) ctxt))
  |> apply (REPEAT_ALL_NEW (Tactic.match_tac @{thms allI}))
  |> apply (Tactic.rtac (@{thm inv_f_f} OF [prove_inj_prop ctxt hdef lhs]))
  |> Goal.norm_result o Goal.finish ctxt


fun expand thm ct =
  let
    val cpat = Thm.dest_arg (Thm.rhs_of thm)
    val (cl, cr) = Thm.dest_binop (Thm.dest_arg (Thm.dest_arg1 ct))
    val thm1 = Thm.instantiate (Thm.match (cpat, cl)) thm
    val thm2 = Thm.instantiate (Thm.match (cpat, cr)) thm
  in Conv.arg_conv (Conv.binop_conv (Conv.rewrs_conv [thm1, thm2])) ct end

fun prove_lhs ctxt rhs lhs =
  let
    val eq = Thm.symmetric (mk_meta_eq (Object_Logic.rulify (Thm.assume rhs)))
  in
    Goal.init lhs
    |> apply (CONVERSION (U.prop_conv (U.binders_conv (K (expand eq)) ctxt)))
    |> apply (Simplifier.simp_tac HOL_ss)
    |> Goal.finish ctxt
  end


fun mk_hdef ctxt rhs =
  let
    val (ct, ctxt') = U.dest_all_cbinders (U.dest_cprop rhs) ctxt
    val (cl, cv) = Thm.dest_binop ct
    val (cg, (cargs, cf)) = Drule.strip_comb cl ||> split_last
    val cu = fold_rev Thm.cabs cargs (mk_inv_of ctxt' (Thm.cabs cv cf))
  in Thm.assume (U.mk_cequals cg cu) end

fun prove_inj_eq ctxt ct =
  let
    val (lhs, rhs) = pairself U.mk_cprop (Thm.dest_binop (U.dest_cprop ct))
    val hdef = mk_hdef ctxt rhs
    val lhs_thm = Thm.implies_intr rhs (prove_lhs ctxt rhs lhs)
    val rhs_thm = Thm.implies_intr lhs (prove_rhs ctxt hdef lhs rhs)
  in lhs_thm COMP (rhs_thm COMP @{thm iffI}) end


val swap_eq_thm = mk_meta_eq @{thm eq_commute}
val swap_disj_thm = mk_meta_eq @{thm disj_commute}

fun swap_conv dest eq =
  U.if_true_conv ((op <) o pairself Term.size_of_term o dest)
    (Conv.rewr_conv eq)

val swap_eq_conv = swap_conv HOLogic.dest_eq swap_eq_thm
val swap_disj_conv = swap_conv U.dest_disj swap_disj_thm

fun norm_conv ctxt =
  swap_eq_conv then_conv
  Conv.arg1_conv (U.binders_conv (K swap_disj_conv) ctxt) then_conv
  Conv.arg_conv (U.binders_conv (K swap_eq_conv) ctxt)

in

fun prove_injectivity ctxt ct =
  ct
  |> Goal.init
  |> apply (CONVERSION (U.prop_conv (norm_conv ctxt)))
  |> apply (CSUBGOAL (uncurry (Tactic.rtac o prove_inj_eq ctxt)))
  |> Goal.norm_result o Goal.finish ctxt

end

end
