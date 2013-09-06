(*  Title:      HOL/Library/simps_case_conv.ML
    Author:     Lars Noschinski, TU Muenchen
                Gerwin Klein, NICTA

  Converts function specifications between the representation as
  a list of equations (with patterns on the lhs) and a single
  equation (with a nested case expression on the rhs).
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

fun get_split_ths thy = collect_Tcons
    #> distinct (op =)
    #> map_filter (Datatype_Data.get_info thy)
    #> map #split

val strip_eq = prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq


local

(*Creates free variables for a list of types*)
fun mk_Frees Ts ctxt =
  let
    val (names,ctxt') = Variable.variant_fixes (replicate (length Ts) "x") ctxt
    val ts = map Free (names ~~ Ts)
  in (ts, ctxt') end

fun tac ctxt {splits, intros, defs} =
  let val ctxt' = Classical.addSIs (ctxt, intros) in
    REPEAT_DETERM1 (FIRSTGOAL (split_tac splits))
    THEN Local_Defs.unfold_tac ctxt defs
    THEN safe_tac ctxt'
  end

fun import [] ctxt = ([], ctxt)
  | import (thm :: thms) ctxt =
    let
      val fun_ct = strip_eq #> fst #> strip_comb #> fst #> Logic.mk_term
        #> Thm.cterm_of (Proof_Context.theory_of ctxt)
      val ct = fun_ct thm
      val cts = map fun_ct thms
      val pairs = map (fn s => (s,ct)) cts
      val thms' = map (fn (th,p) => Thm.instantiate (Thm.match p) th) (thms ~~ pairs)
    in Variable.import true (thm :: thms') ctxt |> apfst snd end

in

(*
  For a list
    f p_11 ... p_1n = t1
    f p_21 ... p_2n = t2
    ...
    f p_mn ... p_mn = tm
  of theorems, prove a single theorem
    f x1 ... xn = t
  where t is a (nested) case expression. The terms p_11, ..., p_mn must
  be exhaustive, non-overlapping datatype patterns. f must not be a function
  application.
*)
fun to_case ctxt ths =
  let
    val (iths, ctxt') = import ths ctxt
    val (fun_t, arg_ts) = hd iths |> strip_eq |> fst |> strip_comb
    val eqs = map (strip_eq #> apfst (snd o strip_comb)) iths
    val (arg_Frees, ctxt'') = mk_Frees (map fastype_of arg_ts) ctxt'

    fun hide_rhs ((pat, rhs), name) lthy = let
        val frees = fold Term.add_frees pat []
        val abs_rhs = fold absfree frees rhs
        val ((f,def), lthy') = Local_Defs.add_def
          ((Binding.name name, Mixfix.NoSyn), abs_rhs) lthy
      in ((list_comb (f, map Free (rev frees)), def), lthy') end

    val ((def_ts, def_thms), ctxt3) = let
        val nctxt = Variable.names_of ctxt''
        val names = Name.invent nctxt "rhs" (length eqs)
      in fold_map hide_rhs (eqs ~~ names) ctxt'' |> apfst split_list end

    val (cases, split_thms) =
      let
        val pattern = map (fst #> HOLogic.mk_tuple) eqs
        val case_arg = HOLogic.mk_tuple arg_Frees
        val cases = Case_Translation.make_case ctxt Case_Translation.Warning Name.context
          case_arg (pattern ~~ def_ts)
        val split_thms = get_split_ths (Proof_Context.theory_of ctxt3) (fastype_of case_arg)
      in (cases, split_thms) end

    val t = (list_comb (fun_t, arg_Frees), cases)
      |> HOLogic.mk_eq
      |> HOLogic.mk_Trueprop
    val th = Goal.prove ctxt3 [] [] t (fn {context=ctxt, ...} =>
          tac ctxt {splits=split_thms, intros=ths, defs=def_thms})
  in th
    |> singleton (Proof_Context.export ctxt3 ctxt)
    |> Goal.norm_result
  end

end

local

fun was_split t =
  let
    val is_free_eq_imp = is_Free o fst o HOLogic.dest_eq
              o fst o HOLogic.dest_imp
    val get_conjs = HOLogic.dest_conj o HOLogic.dest_Trueprop
    fun dest_alls (Const ("HOL.All", _) $ Abs (_, _, t)) = dest_alls t
      | dest_alls t = t
  in forall (is_free_eq_imp o dest_alls) (get_conjs t) end
        handle TERM _ => false

fun apply_split ctxt split thm = Seq.of_list
  let val ((_,thm'), ctxt') = Variable.import false [thm] ctxt in
    (Variable.export ctxt' ctxt) (filter (was_split o prop_of) (thm' RL [split]))
  end

fun forward_tac rules t = Seq.of_list ([t] RL rules)

val refl_imp = refl RSN (2, mp)

val get_rules_once_split =
  REPEAT (forward_tac [conjunct1, conjunct2])
    THEN REPEAT (forward_tac [spec])
    THEN (forward_tac [refl_imp])

fun do_split ctxt split =
  let
    val split' = split RS iffD1;
    val split_rhs = concl_of (hd (snd (fst (Variable.import false [split'] ctxt))))
  in if was_split split_rhs
     then DETERM (apply_split ctxt split') THEN get_rules_once_split
     else raise TERM ("malformed split rule", [split_rhs])
  end

val atomize_meta_eq = forward_tac [meta_eq_to_obj_eq]

in

fun gen_to_simps ctxt splitthms thm =
  Seq.list_of ((TRY atomize_meta_eq
                 THEN (REPEAT (FIRST (map (do_split ctxt) splitthms)))) thm)

fun to_simps ctxt thm =
  let
    val T = thm |> strip_eq |> fst |> strip_comb |> fst |> fastype_of
    val splitthms = get_split_ths (Proof_Context.theory_of ctxt) T
  in gen_to_simps ctxt splitthms thm end


end

fun case_of_simps_cmd (bind, thms_ref) lthy =
  let
    val thy = Proof_Context.theory_of lthy
    val bind' = apsnd (map (Attrib.intern_src thy)) bind
    val thm = (Attrib.eval_thms lthy) thms_ref |> to_case lthy
  in
    Local_Theory.note (bind', [thm]) lthy |> snd
  end

fun simps_of_case_cmd ((bind, thm_ref), splits_ref) lthy =
  let
    val thy = Proof_Context.theory_of lthy
    val bind' = apsnd (map (Attrib.intern_src thy)) bind
    val thm = singleton (Attrib.eval_thms lthy) thm_ref
    val simps = if null splits_ref
      then to_simps lthy thm
      else gen_to_simps lthy (Attrib.eval_thms lthy splits_ref) thm
  in
    Local_Theory.note (bind', simps) lthy |> snd
  end

val _ =
  Outer_Syntax.local_theory @{command_spec "case_of_simps"}
    "turns a list of equations into a case expression"
    (Parse_Spec.opt_thm_name ":"  -- Parse_Spec.xthms1 >> case_of_simps_cmd)

val parse_splits = @{keyword "("} |-- Parse.reserved "splits" |-- @{keyword ":"} |--
  Parse_Spec.xthms1 --| @{keyword ")"}

val _ =
  Outer_Syntax.local_theory @{command_spec "simps_of_case"}
    "perform case split on rule"
    (Parse_Spec.opt_thm_name ":"  -- Parse_Spec.xthm --
      Scan.optional parse_splits [] >> simps_of_case_cmd)

end

