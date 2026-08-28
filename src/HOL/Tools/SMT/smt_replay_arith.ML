(*  Title:      HOL/Tools/SMT/smt_replay_arith.ML
    Author:     Mathias Fleury, MPII, JKU

Proof methods for replaying arithmetic steps with Farkas Lemma.
*)

signature SMT_REPLAY_ARITH =
sig
  val la_farkas_tac: Subgoal.focus -> tactic_args option -> thm -> thm Seq.seq;
  val la_farkas: tactic_args option -> Proof.context -> int -> tactic;
end;

structure SMT_Replay_Arith: SMT_REPLAY_ARITH =
struct

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

fun try_OF_insts ctxt thms thm = (map (fn thm1 => try_OF_inst ctxt thm1 thm) thms |> flat)

fun try_OFs ctxt thms thm = map (fn thm1 => try_OF ctxt thm1 thm) thms |> flat

fun la_farkas_tac ({context = ctxt, prems, concl,  ...}: Subgoal.focus) (SOME (Farkas_Coefficients coeffs)) thm =
  let

    fun trace v = (SMT_Config.verit_arith_msg ctxt v; v)
    val _ = trace (fn () => @{print} ("prems",prems))
    val _ = trace (fn () => @{print} ("concl",concl))
    val _ = trace (fn () => @{print} ("coeffs",coeffs))
    val arith_thms = Named_Theorems.get ctxt @{named_theorems smt_arith_simplify}
    val alethe_arith = Named_Theorems.get ctxt @{named_theorems smt_arith_combine}
    val alethe_arith_multiplication = Named_Theorems.get ctxt @{named_theorems smt_arith_multiplication}

    val _ = trace (fn () => @{print}  "******************************************************")
    val _ = trace (fn () => @{print}  "          Normalize premises                          ")
    val _ = trace (fn () => @{print}  "******************************************************")

    fun basic_simps ctxt thms =
      ctxt
      |> Simplifier.empty_simpset
      |> put_simpset HOL_basic_ss
      |> Simplifier.add_simps thms
      |> asm_full_simplify

    (*Determine if we need to return the equation: \<not>\<le> \<rightarrow> \<ge> but only \<le> exists for Isabelle*)

    fun as_prop (t as Const (\<^const_name>\<open>Trueprop\<close>, _) $ _) = t
      | as_prop t = HOLogic.mk_Trueprop t
    fun discharge _ [] thm = thm
      | discharge i (rule :: rules) thm = discharge (i + Thm.nprems_of rule) rules (rule RSN (i, thm))

    fun normalize_prem thm =
      let
        val thm' = basic_simps ctxt @{thms linorder_class.not_less linorder_class.not_le} thm
        (*fun ttt ctxt = resolve_tac ctxt @{thms arith_prems_normalize}
        fun f t = Goal.prove ctxt [] [] (as_prop (Thm.concl_of t))
          (fn {context, prems} =>  (print_tac ctxt "here") THEN TRY (REPEAT (ALLGOALS (resolve_tac ctxt @{thms arith_prems_normalize}))) THEN  (print_tac ctxt "here1")) 
        val thm'' = thm' |> f |> @{print}*)
      in (thm', Thm.prop_of thm <> Thm.prop_of thm') end
    val prems = map normalize_prem prems
    val _ = trace (fn () => @{print} ("normalize_prem",prems))

    val typ = hd prems
      |> fst
      |> Thm.concl_of
      |> Thm.cterm_of ctxt
      |> Object_Logic.dest_judgment ctxt
      |> Thm.term_of
      |> (fn (Const _ $ r1 $r2) => r1)
      |> fastype_of
    fun convert_coefficients (a,b) =
      (HOLogic.mk_number typ (if a < 0 then ~a else a), HOLogic.mk_number typ b, a > 0)
    val coeff_prems = map convert_coefficients coeffs
       |> (fn xs => ListPair.zip (xs, prems))
       |> tap (fn x => trace (fn () => @{print} x))
       |> map (fn ((num1, num2, pos), (prems, inverted)) => ((num1, num2, (pos, inverted)), prems))
    val _ = trace (fn () => @{print} ("coeff_prems",coeff_prems))

    val _ = trace (fn () => @{print}  "******************************************************")
    val _ = trace (fn () => @{print}  "       Multiply by constants                          ")
    val _ = trace (fn () => @{print}  "******************************************************")
    val _ = trace (fn () => @{print} coeff_prems)
    fun negate_if_needed (thm, (pos, no_inversion_needed)) =
      let
        fun manipulate_thm thms cond thm =
          if cond then thm
          else map (fn thm0 => try_OF ctxt thm0 thm) thms
            |> flat |> the_single
      in 
        thm
        |> manipulate_thm @{thms alethe_negate_coefficient} pos
        |> manipulate_thm @{thms alethe_invert_farkas_equation} no_inversion_needed
      end

    val normalized =
      map (try_OF_insts ctxt alethe_arith_multiplication) coeff_prems
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
           (try_OFs ctxt alethe_arith (thm1) )
           |> (fn thms => try_OFs ctxt thms thm2) 
           |> the_single)
         n
         normalized
      |> singleton (Proof_Context.export ctxt_with_assms ctxt)
    val _ = trace (fn () => @{print} combined)

    fun arith_full_simps ctxt thms =
      ctxt
       |> Simplifier.empty_simpset
       |> put_simpset HOL_basic_ss
       |> Simplifier.add_simps thms
       |> Simplifier.add_simps @{thms simp_thms}
       |> Simplifier.add_simps arith_thms
       |> fold Simplifier.add_proc
        [@{simproc int_div_cancel_numeral_factors}, @{simproc int_combine_numerals},
         @{simproc divide_cancel_numeral_factor}, @{simproc intle_cancel_numerals},
         @{simproc field_combine_numerals}, @{simproc intless_cancel_numerals},
         @{simproc inteq_cancel_numerals}]
      |> Simplifier.add_cong @{thm if_weak_cong}
      |> asm_full_simplify
    val final_False = combined
      |> arith_full_simps ctxt (Named_Theorems.get ctxt @{named_theorems ac_simps})
    val _ =  trace (fn () => ("final arith theorem after simplification", final_False))

    val _ = trace (fn () => @{print} final_False)
    val final_theorem = try_OF ctxt thm final_False
  in
    (case final_theorem of
       [thm] => Seq.single (thm OF replicate Trues @{thm TrueI})
    | _ => Seq.empty)
  end
  | la_farkas_tac _ _ _ = raise Fail "invalid application"

fun TRY' tac = fn i => TRY (tac i)
fun REPEAT' tac = fn i => REPEAT (tac i)

fun rewrite_only_thms ctxt thms =
  ctxt
  |> Simplifier.empty_simpset
  |> put_simpset HOL_basic_ss
  |> Simplifier.add_simps thms
  |> Simplifier.full_simp_tac

fun la_farkas args ctxt =
  REPEAT' (resolve_tac ctxt @{thms alethe_farkas})
  THEN' TRY' (resolve_tac ctxt @{thms ccontr})
  THEN' TRY' (rewrite_only_thms ctxt @{thms not_not})
  THEN' (Subgoal.FOCUS (fn focus => la_farkas_tac focus args) ctxt)

end
