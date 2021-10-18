(*  Title:      HOL/Library/simps_case_conv.ML
    Author:     Lars Noschinski, TU Muenchen
    Author:     Gerwin Klein, NICTA

Convert function specifications between the representation as a list
of equations (with patterns on the lhs) and a single equation (with a
nested case expression on the rhs).
*)

signature SIMPS_CASE_CONV =
sig
  val to_case: Proof.context -> thm list -> thm
  val gen_to_simps: Proof.context -> thm list -> thm -> thm list
  val to_simps: Proof.context -> thm -> thm list
end

structure Simps_Case_Conv: SIMPS_CASE_CONV =
struct

(* Collects all type constructors in a type *)
fun collect_Tcons (Type (name,Ts)) = name :: maps collect_Tcons Ts
  | collect_Tcons (TFree _) = []
  | collect_Tcons (TVar _) = []

fun get_type_infos ctxt =
    maps collect_Tcons
    #> distinct (op =)
    #> map_filter (Ctr_Sugar.ctr_sugar_of ctxt)

fun get_split_ths ctxt = get_type_infos ctxt #> map #split

val strip_eq = Thm.prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq

(*
  For a list
    f p_11 ... p_1n = t1
    f p_21 ... p_2n = t2
    ...
    f p_mn ... p_mn = tm
  of theorems, prove a single theorem
    f x1 ... xn = t
  where t is a (nested) case expression. f must not be a function
  application.
*)
fun to_case ctxt ths =
  let
    fun ctr_count (ctr, T) = 
      let
        val tyco = body_type T |> dest_Type |> fst
        val info = Ctr_Sugar.ctr_sugar_of ctxt tyco
        val _ = if is_none info then error ("Pattern match on non-constructor constant " ^ ctr) else ()
      in
        info |> the |> #ctrs |> length
      end
    val thms = Case_Converter.to_case ctxt Case_Converter.keep_constructor_context ctr_count ths
  in
    case thms of SOME thms => hd thms
      | _ => error ("Conversion to case expression failed.")
  end

local

fun was_split t =
  let
    val is_free_eq_imp = is_Free o fst o HOLogic.dest_eq o fst o HOLogic.dest_imp
    val get_conjs = HOLogic.dest_conj o HOLogic.dest_Trueprop
    val dest_alls = Term.strip_qnt_body \<^const_name>\<open>All\<close>
  in forall (is_free_eq_imp o dest_alls) (get_conjs t) end
  handle TERM _ => false

fun apply_split ctxt split thm = Seq.of_list
  let val ((_,thm'), ctxt') = Variable.import false [thm] ctxt in
    (Variable.export ctxt' ctxt) (filter (was_split o Thm.prop_of) (thm' RL [split]))
  end

fun forward_tac rules t = Seq.of_list ([t] RL rules)

val refl_imp = refl RSN (2, mp)

val get_rules_once_split =
  REPEAT (forward_tac [conjunct1, conjunct2])
    THEN REPEAT (forward_tac [spec])
    THEN (forward_tac [refl_imp])

fun do_split ctxt split =
  case try op RS (split, iffD1) of
    NONE => raise TERM ("malformed split rule", [Thm.prop_of split])
  | SOME split' =>
      let val split_rhs = Thm.concl_of (hd (snd (fst (Variable.import false [split'] ctxt))))
      in if was_split split_rhs
         then DETERM (apply_split ctxt split') THEN get_rules_once_split
         else raise TERM ("malformed split rule", [split_rhs])
      end

val atomize_meta_eq = forward_tac [meta_eq_to_obj_eq]

in

fun gen_to_simps ctxt splitthms thm =
  let val splitthms' = filter (fn t => not (Thm.eq_thm (t, Drule.dummy_thm))) splitthms
  in
    Seq.list_of ((TRY atomize_meta_eq THEN (REPEAT (FIRST (map (do_split ctxt) splitthms')))) thm)
  end

fun to_simps ctxt thm =
  let
    val T = thm |> strip_eq |> fst |> strip_comb |> fst |> fastype_of
    val splitthms = get_split_ths ctxt [T]
  in gen_to_simps ctxt splitthms thm end


end

fun case_of_simps_cmd (bind, thms_ref) lthy =
  let
    val bind' = apsnd (map (Attrib.check_src lthy)) bind
    val thm = Attrib.eval_thms lthy thms_ref |> to_case lthy
  in
    Local_Theory.note (bind', [thm]) lthy |> snd
  end

fun simps_of_case_cmd ((bind, thm_ref), splits_ref) lthy =
  let
    val bind' = apsnd (map (Attrib.check_src lthy)) bind
    val thm = singleton (Attrib.eval_thms lthy) thm_ref
    val simps = if null splits_ref
      then to_simps lthy thm
      else gen_to_simps lthy (Attrib.eval_thms lthy splits_ref) thm
  in
    Local_Theory.note (bind', simps) lthy |> snd
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>case_of_simps\<close>
    "turn a list of equations into a case expression"
    (Parse_Spec.opt_thm_name ":"  -- Parse.thms1 >> case_of_simps_cmd)

val parse_splits = \<^keyword>\<open>(\<close> |-- Parse.reserved "splits" |-- \<^keyword>\<open>:\<close> |--
  Parse.thms1 --| \<^keyword>\<open>)\<close>

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>simps_of_case\<close>
    "perform case split on rule"
    (Parse_Spec.opt_thm_name ":"  -- Parse.thm --
      Scan.optional parse_splits [] >> simps_of_case_cmd)

end

