(*  Title:      HOL/TPTP/atp_problem_import.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Import TPTP problems as Isabelle terms or goals.
*)

signature ATP_PROBLEM_IMPORT =
sig
  val read_tptp_file : theory -> (string * term -> 'a) -> string ->
    'a list * ('a list * 'a list) * local_theory
  val nitpick_tptp_file : theory -> int -> string -> unit
  val refute_tptp_file : theory -> int -> string -> unit
  val can_tac : Proof.context -> (Proof.context -> tactic) -> term -> bool
  val SOLVE_TIMEOUT :  int -> string -> tactic -> tactic
  val atp_tac : local_theory -> int -> (string * string) list -> int -> term list -> string ->
    int -> tactic
  val smt_solver_tac : string -> local_theory -> int -> tactic
  val make_conj : term list * term list -> term list -> term
  val sledgehammer_tptp_file : theory -> int -> string -> unit
  val isabelle_tptp_file : theory -> int -> string -> unit
  val isabelle_hot_tptp_file : theory -> int -> string -> unit
  val translate_tptp_file : theory -> string -> string -> unit
end;

structure ATP_Problem_Import : ATP_PROBLEM_IMPORT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate

val debug = false
val overlord = false


(** TPTP parsing **)

fun exploded_absolute_path file_name =
  Path.explode file_name
  |> (fn path => path |> not (Path.is_absolute path) ? Path.append (Path.explode "$PWD"))

fun read_tptp_file thy postproc file_name =
  let
    fun has_role role (_, role', _, _) = (role' = role)
    fun get_prop f (name, _, P, _) = P |> f |> close_form |> pair name |> postproc

    val path = exploded_absolute_path file_name
    val ((_, _, problem), thy) =
      TPTP_Interpret.interpret_file true [Path.dir path, Path.explode "$TPTP"] path [] [] thy
    val (conjs, defs_and_nondefs) = problem
      |> List.partition (has_role TPTP_Syntax.Role_Conjecture)
      ||> List.partition (has_role TPTP_Syntax.Role_Definition)
  in
    (map (get_prop I) conjs,
     apply2 (map (get_prop Logic.varify_global)) defs_and_nondefs,
     Named_Target.theory_init thy)
  end


(** Nitpick **)

fun aptrueprop f ((t0 as \<^const>\<open>Trueprop\<close>) $ t1) = t0 $ f t1
  | aptrueprop f t = f t

fun is_legitimate_tptp_def (\<^const>\<open>Trueprop\<close> $ t) = is_legitimate_tptp_def t
  | is_legitimate_tptp_def (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t $ u) =
    (is_Const t orelse is_Free t) andalso not (exists_subterm (curry (op =) t) u)
  | is_legitimate_tptp_def _ = false

fun nitpick_tptp_file thy timeout file_name =
  let
    val (conjs, (defs, nondefs), lthy) = read_tptp_file thy snd file_name
    val thy = Proof_Context.theory_of lthy
    val (defs, pseudo_defs) = defs
      |> map (ATP_Util.abs_extensionalize_term lthy #> aptrueprop (hol_open_form I))
      |> List.partition (is_legitimate_tptp_def o perhaps (try HOLogic.dest_Trueprop)
        o ATP_Util.unextensionalize_def)
    val nondefs = pseudo_defs @ nondefs
    val state = Proof.init lthy
    val params =
      [("card", "1-100"),
       ("box", "false"),
       ("max_threads", "1"),
       ("batch_size", "5"),
       ("falsify", if null conjs then "false" else "true"),
       ("verbose", "true"),
       ("debug", if debug then "true" else "false"),
       ("overlord", if overlord then "true" else "false"),
       ("show_consts", "true"),
       ("format", "1"),
       ("max_potential", "0"),
       ("timeout", string_of_int timeout),
       ("tac_timeout", string_of_int ((timeout + 49) div 50))]
      |> Nitpick_Commands.default_params thy
    val i = 1
    val n = 1
    val step = 0
    val subst = []
  in
    Nitpick.pick_nits_in_term state params Nitpick.TPTP i n step subst defs nondefs
      (case conjs of conj :: _ => conj | [] => \<^prop>\<open>True\<close>);
    ()
  end


(** Refute **)

fun refute_tptp_file thy timeout file_name =
  let
    fun print_szs_of_outcome falsify s =
      "% SZS status " ^
      (if s = "genuine" then
         if falsify then "CounterSatisfiable" else "Satisfiable"
       else
         "GaveUp")
      |> writeln
    val (conjs, (defs, nondefs), lthy) = read_tptp_file thy snd file_name
    val params =
      [("maxtime", string_of_int timeout),
       ("maxvars", "100000")]
  in
    Refute.refute_term lthy params (defs @ nondefs)
      (case conjs of conj :: _ => conj | [] => \<^prop>\<open>True\<close>)
    |> print_szs_of_outcome (not (null conjs))
  end


(** Sledgehammer and Isabelle (combination of provers) **)

fun can_tac ctxt tactic conj =
  can (Goal.prove_internal ctxt [] (Thm.cterm_of ctxt conj)) (fn [] => tactic ctxt)

fun SOLVE_TIMEOUT seconds name tac st =
  let
    val _ = writeln ("running " ^ name ^ " for " ^ string_of_int seconds ^ " s")
    val result =
      Timeout.apply (Time.fromSeconds seconds) (fn () => SINGLE (SOLVE tac) st) ()
      handle Timeout.TIMEOUT _ => NONE | ERROR _ => NONE
  in
    (case result of
      NONE => (writeln ("FAILURE: " ^ name); Seq.empty)
    | SOME st' => (writeln ("SUCCESS: " ^ name); Seq.single st'))
  end

fun nitpick_finite_oracle_tac lthy timeout i th =
  let
    fun is_safe (Type (\<^type_name>\<open>fun\<close>, Ts)) = forall is_safe Ts
      | is_safe \<^typ>\<open>prop\<close> = true
      | is_safe \<^typ>\<open>bool\<close> = true
      | is_safe _ = false

    val conj = Thm.term_of (Thm.cprem_of th i)
  in
    if exists_type (not o is_safe) conj then
      Seq.empty
    else
      let
        val thy = Proof_Context.theory_of lthy
        val state = Proof.init lthy
        val params =
          [("box", "false"),
           ("max_threads", "1"),
           ("verbose", "true"),
           ("debug", if debug then "true" else "false"),
           ("overlord", if overlord then "true" else "false"),
           ("max_potential", "0"),
           ("timeout", string_of_int timeout)]
          |> Nitpick_Commands.default_params thy
        val i = 1
        val n = 1
        val step = 0
        val subst = []
        val (outcome, _) =
          Nitpick.pick_nits_in_term state params Nitpick.Normal i n step subst [] [] conj
      in
        if outcome = "none" then ALLGOALS (Skip_Proof.cheat_tac lthy) th else Seq.empty
      end
  end

fun atp_tac lthy completeness override_params timeout assms prover =
  let
    val thy = Proof_Context.theory_of lthy
    val assm_ths0 = map (Skip_Proof.make_thm thy) assms
    val ((assm_name, _), lthy) = lthy
      |> Config.put Sledgehammer_Prover_ATP.atp_completish (if completeness > 0 then 3 else 0)
      |> Local_Theory.note ((\<^binding>\<open>thms\<close>, []), assm_ths0)

    fun ref_of th = (Facts.named (Thm.derivation_name th), [])
    val ref_of_assms = (Facts.named assm_name, [])
  in
    Sledgehammer_Tactics.sledgehammer_as_oracle_tac lthy
      ([("debug", if debug then "true" else "false"),
        ("overlord", if overlord then "true" else "false"),
        ("provers", prover),
        ("timeout", string_of_int timeout)] @
       (if completeness > 0 then
          [("type_enc", if completeness = 1 then "mono_native" else "poly_tags")]
        else
          []) @
       override_params)
      {add = ref_of_assms :: map ref_of [ext, @{thm someI}], del = [], only = true} []
  end

fun sledgehammer_tac demo lthy timeout assms i =
  let
    val frac = if demo then 16 else 12
    fun slice mult completeness prover =
      SOLVE_TIMEOUT (mult * timeout div frac)
        (prover ^ (if completeness > 0 then "(" ^ string_of_int completeness ^ ")" else ""))
        (atp_tac lthy completeness [] (mult * timeout div frac) assms prover i)
  in
    slice 2 0 ATP_Proof.spassN
    ORELSE slice 2 0 ATP_Proof.vampireN
    ORELSE slice 2 0 ATP_Proof.eN
    ORELSE slice 2 0 ATP_Proof.z3_tptpN
    ORELSE slice 1 1 ATP_Proof.spassN
    ORELSE slice 1 2 ATP_Proof.eN
    ORELSE slice 1 1 ATP_Proof.vampireN
    ORELSE slice 1 2 ATP_Proof.vampireN
    ORELSE
      (if demo then
         slice 2 0 ATP_Proof.satallaxN
         ORELSE slice 2 0 ATP_Proof.leo2N
       else
         no_tac)
  end

fun smt_solver_tac solver lthy =
  let
    val lthy = lthy |> Context.proof_map (SMT_Config.select_solver solver)
  in SMT_Solver.smt_tac lthy [] end

fun auto_etc_tac lthy timeout assms i =
  SOLVE_TIMEOUT (timeout div 20) "nitpick" (nitpick_finite_oracle_tac lthy (timeout div 20) i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "simp" (asm_full_simp_tac lthy i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "blast" (blast_tac lthy i)
  ORELSE SOLVE_TIMEOUT (timeout div 5) "auto+spass"
    (auto_tac lthy THEN ALLGOALS (atp_tac lthy 0 [] (timeout div 5) assms ATP_Proof.spassN))
  ORELSE SOLVE_TIMEOUT (timeout div 10) "fast" (fast_tac lthy i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "z3" (smt_solver_tac "z3" lthy i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "cvc4" (smt_solver_tac "cvc4" lthy i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "best" (best_tac lthy i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "force" (force_tac lthy i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "meson" (Meson.meson_tac lthy [] i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "fastforce" (fast_force_tac lthy i)

fun problem_const_prefix thy = Context.theory_name thy ^ Long_Name.separator

fun make_conj (defs, nondefs) conjs =
  Logic.list_implies (rev defs @ rev nondefs, case conjs of conj :: _ => conj | [] => \<^prop>\<open>False\<close>)

fun print_szs_of_success conjs success =
  writeln ("% SZS status " ^
    (if success then
       if null conjs then "Unsatisfiable" else "Theorem"
     else
       "GaveUp"))

fun sledgehammer_tptp_file thy timeout file_name =
  let
    val (conjs, assms, lthy) = read_tptp_file thy snd file_name
    val conj = make_conj ([], []) conjs
    val assms = op @ assms
  in
    can_tac lthy (fn lthy => sledgehammer_tac true lthy timeout assms 1) conj
    |> print_szs_of_success conjs
  end

fun generic_isabelle_tptp_file demo thy timeout file_name =
  let
    val (conjs, assms, lthy) = read_tptp_file thy snd file_name
    val conj = make_conj ([], []) conjs
    val full_conj = make_conj assms conjs
    val assms = op @ assms
    val (last_hope_atp, last_hope_completeness) =
      if demo then (ATP_Proof.satallaxN, 0) else (ATP_Proof.vampireN, 2)
  in
    (can_tac lthy (fn lthy => auto_etc_tac lthy (timeout div 2) assms 1) full_conj orelse
     can_tac lthy (fn lthy => sledgehammer_tac demo lthy (timeout div 2) assms 1) conj orelse
     can_tac lthy (fn lthy => SOLVE_TIMEOUT timeout (last_hope_atp ^ "(*)")
       (atp_tac lthy last_hope_completeness [] timeout assms last_hope_atp 1)) full_conj)
    |> print_szs_of_success conjs
  end

val isabelle_tptp_file = generic_isabelle_tptp_file false
val isabelle_hot_tptp_file = generic_isabelle_tptp_file true


(** Translator between TPTP(-like) file formats **)

fun translate_tptp_file thy format_str file_name =
  let
    val (conjs, (defs, nondefs), lthy) = read_tptp_file thy I file_name
    val conj = make_conj ([], []) (map snd conjs)

    val (format, type_enc, lam_trans) =
      (case format_str of
        "FOF" => (FOF, "mono_guards??", liftingN)
      | "TF0" => (TFF Monomorphic, "mono_native", liftingN)
      | "TH0" => (THF (Monomorphic, THF_Without_Choice), "mono_native_higher", keep_lamsN)
      | "DFG" => (DFG Monomorphic, "mono_native", liftingN)
      | _ => error ("Unknown format " ^ quote format_str ^
        " (expected \"FOF\", \"TF0\", \"TH0\", or \"DFG\")"))
    val generate_info = false
    val uncurried_aliases = false
    val readable_names = true
    val presimp = true
    val facts =
      map (apfst (rpair (Global, Non_Rec_Def))) defs @
      map (apfst (rpair (Global, General))) nondefs
    val (atp_problem, _, _, _) =
      generate_atp_problem lthy generate_info format Hypothesis (type_enc_of_string Strict type_enc)
        Translator
        lam_trans uncurried_aliases readable_names presimp [] conj facts

    val ord = Sledgehammer_ATP_Systems.effective_term_order lthy spassN
    val ord_info = K []
    val lines = lines_of_atp_problem format ord ord_info atp_problem
  in
    List.app Output.physical_stdout lines
  end

end;
