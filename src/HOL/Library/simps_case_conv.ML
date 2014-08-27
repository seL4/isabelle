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

fun get_split_ths ctxt = collect_Tcons
    #> distinct (op =)
    #> map_filter (Ctr_Sugar.ctr_sugar_of ctxt)
    #> map #split

val strip_eq = prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq


local

  fun transpose [] = []
    | transpose ([] :: xss) = transpose xss
    | transpose xss = map hd xss :: transpose (map tl xss);

  fun same_fun (ts as _ $ _ :: _) =
      let
        val (fs, argss) = map strip_comb ts |> split_list
        val f = hd fs
      in if forall (fn x => f = x) fs then SOME (f, argss) else NONE end
    | same_fun _ = NONE

  (* pats must be non-empty *)
  fun split_pat pats ctxt =
      case same_fun pats of
        NONE =>
          let
            val (name, ctxt') = yield_singleton Variable.variant_fixes "x" ctxt
            val var = Free (name, fastype_of (hd pats))
          in (((var, [var]), map single pats), ctxt') end
      | SOME (f, argss) =>
          let
            val (((def_pats, def_frees), case_patss), ctxt') =
              split_pats argss ctxt
            val def_pat = list_comb (f, def_pats)
          in (((def_pat, flat def_frees), case_patss), ctxt') end
  and
      split_pats patss ctxt =
        let
          val (splitted, ctxt') = fold_map split_pat (transpose patss) ctxt
          val r = splitted |> split_list |> apfst split_list |> apsnd (transpose #> map flat)
        in (r, ctxt') end

(*
  Takes a list lhss of left hand sides (which are lists of patterns)
  and a list rhss of right hand sides. Returns
    - a single equation with a (nested) case-expression on the rhs
    - a list of all split-thms needed to split the rhs
  Patterns which have the same outer context in all lhss remain
  on the lhs of the computed equation.
*)
fun build_case_t fun_t lhss rhss ctxt =
  let
    val (((def_pats, def_frees), case_patss), ctxt') =
      split_pats lhss ctxt
    val pattern = map HOLogic.mk_tuple case_patss
    val case_arg = HOLogic.mk_tuple (flat def_frees)
    val cases = Case_Translation.make_case ctxt' Case_Translation.Warning Name.context
      case_arg (pattern ~~ rhss)
    val split_thms = get_split_ths ctxt' (fastype_of case_arg)
    val t = (list_comb (fun_t, def_pats), cases)
      |> HOLogic.mk_eq
      |> HOLogic.mk_Trueprop
  in ((t, split_thms), ctxt') end

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
  where t is a (nested) case expression. f must not be a function
  application. Moreover, the terms p_11, ..., p_mn must be non-overlapping
  datatype patterns. The patterns must be exhausting up to common constructor
  contexts.
*)
fun to_case ctxt ths =
  let
    val (iths, ctxt') = import ths ctxt
    val fun_t = hd iths |> strip_eq |> fst |> head_of
    val eqs = map (strip_eq #> apfst (snd o strip_comb)) iths

    fun hide_rhs ((pat, rhs), name) lthy = let
        val frees = fold Term.add_frees pat []
        val abs_rhs = fold absfree frees rhs
        val ((f,def), lthy') = Local_Defs.add_def
          ((Binding.name name, Mixfix.NoSyn), abs_rhs) lthy
      in ((list_comb (f, map Free (rev frees)), def), lthy') end

    val ((def_ts, def_thms), ctxt2) = let
        val nctxt = Variable.names_of ctxt'
        val names = Name.invent nctxt "rhs" (length eqs)
      in fold_map hide_rhs (eqs ~~ names) ctxt' |> apfst split_list end

    val ((t, split_thms), ctxt3) = build_case_t fun_t (map fst eqs) def_ts ctxt2

    val th = Goal.prove ctxt3 [] [] t (fn {context=ctxt, ...} =>
          tac ctxt {splits=split_thms, intros=ths, defs=def_thms})
  in th
    |> singleton (Proof_Context.export ctxt3 ctxt)
    |> Goal.norm_result ctxt
  end

end

local

fun was_split t =
  let
    val is_free_eq_imp = is_Free o fst o HOLogic.dest_eq o fst o HOLogic.dest_imp
    val get_conjs = HOLogic.dest_conj o HOLogic.dest_Trueprop
    fun dest_alls (Const (@{const_name All}, _) $ Abs (_, _, t)) = dest_alls t
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
    val splitthms = get_split_ths ctxt T
  in gen_to_simps ctxt splitthms thm end


end

fun case_of_simps_cmd (bind, thms_ref) lthy =
  let
    val bind' = apsnd (map (Attrib.check_src lthy)) bind
    val thm = (Attrib.eval_thms lthy) thms_ref |> to_case lthy
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
  Outer_Syntax.local_theory @{command_spec "case_of_simps"}
    "turn a list of equations into a case expression"
    (Parse_Spec.opt_thm_name ":"  -- Parse.xthms1 >> case_of_simps_cmd)

val parse_splits = @{keyword "("} |-- Parse.reserved "splits" |-- @{keyword ":"} |--
  Parse.xthms1 --| @{keyword ")"}

val _ =
  Outer_Syntax.local_theory @{command_spec "simps_of_case"}
    "perform case split on rule"
    (Parse_Spec.opt_thm_name ":"  -- Parse.xthm --
      Scan.optional parse_splits [] >> simps_of_case_cmd)

end

