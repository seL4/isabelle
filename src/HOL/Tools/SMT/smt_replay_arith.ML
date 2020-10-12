(*  Title:      HOL/Tools/SMT/smt_replay_arith.ML
    Author:     Mathias Fleury, MPII, JKU

Proof methods for replaying arithmetic steps with Farkas Lemma.
*)

signature SMT_REPLAY_ARITH =
sig
  val la_farkas_tac: Subgoal.focus -> term list -> thm -> thm Seq.seq;
  val la_farkas: term list -> Proof.context -> int -> tactic;
end;

structure SMT_Replay_Arith: SMT_REPLAY_ARITH =
struct

fun extract_number (Const ("SMT.z3div", _) $ (Const ("Groups.uminus_class.uminus", _) $ n1) $ n2) =
      (n1, n2, false)
  | extract_number (Const ("SMT.z3div", _) $ n1 $ n2) = (n1, n2, true)
  | extract_number (Const ("Groups.uminus_class.uminus", _) $ n) =
      (n, HOLogic.numeral_const (fastype_of n) $ HOLogic.one_const, false)
  | extract_number n = (n, HOLogic.numeral_const (fastype_of n) $ HOLogic.one_const, true)

fun try_OF _ thm1 thm2 =
    (thm1 OF [thm2])
    |> single
  handle THM _ => []

fun try_OF_inst ctxt thm1 ((r, q, pos), thm2) =
    map (fn thm =>
      (Drule.infer_instantiate' ctxt (map SOME [Thm.cterm_of ctxt q, Thm.cterm_of ctxt r]) thm,
        pos))
      (try_OF ctxt thm1 thm2)
  handle THM _ => []

fun try_OF_insts ctxt thms thm = map (fn thm1 => try_OF_inst ctxt thm1 thm) thms |> flat

fun try_OFs ctxt thms thm = map (fn thm1 => try_OF ctxt thm1 thm) thms |> flat

fun la_farkas_tac ({context = ctxt, prems, concl,  ...}: Subgoal.focus) args thm =
  let
    fun trace v = (SMT_Config.verit_arith_msg ctxt v; v)
    val _ = trace (fn () => @{print} (prems, concl))
    val arith_thms = Named_Theorems.get ctxt @{named_theorems smt_arith_simplify}
    val verit_arith = Named_Theorems.get ctxt @{named_theorems smt_arith_combine}
    val verit_arith_multiplication = Named_Theorems.get ctxt @{named_theorems smt_arith_multiplication}
    val _ = trace (fn () => @{print}  "******************************************************")
    val _ = trace (fn () => @{print}  "       Multiply by constants                          ")
    val _ = trace (fn () => @{print}  "******************************************************")
    val coeff_prems =
       map extract_number args
       |> (fn xs => ListPair.zip (xs, prems))
    val _ = trace (fn () => @{print} coeff_prems)
    fun negate_if_needed (thm, pos) =
       if pos then thm
       else map (fn thm0 => try_OF ctxt thm0 thm) @{thms verit_negate_coefficient}
         |> flat |> the_single
    val normalized =
      map (try_OF_insts ctxt verit_arith_multiplication) coeff_prems
      |> flat
      |> map negate_if_needed
    fun import_assumption thm (Trues, ctxt) =
       let val (assms, ctxt) = Assumption.add_assumes ((map (Thm.cterm_of ctxt) o Thm.prems_of) thm) ctxt in
         (thm OF assms, (Trues + length assms, ctxt)) end
    val (n :: normalized, (Trues, ctxt_with_assms)) = fold_map import_assumption normalized (0, ctxt)

    val _ = trace (fn () => @{print} (n :: normalized))
    val _ = trace (fn () => @{print}   "*****************************************************")
    val _ = trace (fn () => @{print}  "       Combine equalities                             ")
    val _ = trace (fn () => @{print}  "******************************************************")

    val combined =
      List.foldl
         (fn (thm1, thm2) =>
           try_OFs ctxt verit_arith thm1
           |> (fn thms => try_OFs ctxt thms thm2)
           |> the_single)
         n
         normalized
      |> singleton (Proof_Context.export ctxt_with_assms ctxt)
    val _ = trace (fn () => @{print} combined)
    fun arith_full_simps ctxt thms =
      ctxt
       |> empty_simpset
      |> put_simpset HOL_basic_ss
       |> (fn ctxt => ctxt addsimps thms
           addsimps arith_thms
           addsimprocs [@{simproc int_div_cancel_numeral_factors}, @{simproc int_combine_numerals},
             @{simproc divide_cancel_numeral_factor}, @{simproc intle_cancel_numerals},
             @{simproc field_combine_numerals}, @{simproc intless_cancel_numerals}])
      |> asm_full_simplify
    val final_False = combined
      |> arith_full_simps ctxt (Named_Theorems.get ctxt @{named_theorems ac_simps})
    val _ = trace (fn () => @{print} final_False)
    val final_theorem = try_OF ctxt thm final_False
  in
    (case final_theorem of
       [thm] => Seq.single (thm OF replicate Trues @{thm TrueI})
    | _ => Seq.empty)
  end

fun TRY' tac = fn i => TRY (tac i)
fun REPEAT' tac = fn i => REPEAT (tac i)

fun rewrite_only_thms ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps thms)
  |> Simplifier.full_simp_tac

fun la_farkas args ctxt =
  REPEAT' (resolve_tac ctxt @{thms verit_and_pos(2,3)})
  THEN' TRY' (resolve_tac ctxt @{thms ccontr})
  THEN' TRY' (rewrite_only_thms ctxt @{thms linorder_class.not_less linorder_class.not_le not_not})
  THEN' (Subgoal.FOCUS (fn focus => la_farkas_tac focus args) ctxt)

end