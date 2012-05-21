(*  Title:      HOL/TPTP/atp_problem_import.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Import TPTP problems as Isabelle terms or goals.
*)

signature ATP_PROBLEM_IMPORT =
sig
  val read_tptp_file :
    theory -> (term -> term) -> string
    -> term list * (term list * term list) * Proof.context
  val nitpick_tptp_file : theory -> int -> string -> unit
  val refute_tptp_file : theory -> int -> string -> unit
  val can_tac : Proof.context -> tactic -> term -> bool
  val SOLVE_TIMEOUT :  int -> string -> tactic -> tactic
  val atp_tac :
    Proof.context -> int -> (string * string) list -> int -> string -> int
    -> tactic
  val smt_solver_tac : string -> Proof.context -> int -> tactic
  val freeze_problem_consts : theory -> term -> term
  val make_conj : term list * term list -> term list -> term
  val sledgehammer_tptp_file : theory -> int -> string -> unit
  val isabelle_demo_tptp_file : theory -> int -> string -> unit
  val isabelle_comp_tptp_file : theory -> int -> string -> unit
  val translate_tptp_file : string -> string -> string -> unit
end;

structure ATP_Problem_Import : ATP_PROBLEM_IMPORT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof

val debug = false
val overlord = false


(** TPTP parsing **)

(* cf. "close_form" in "refute.ML" *)
fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
           Logic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
       (Term.add_vars t []) t

fun read_tptp_file thy postproc file_name =
  let
    fun has_role role (_, role', _, _) = (role' = role)
    fun get_prop (_, _, P, _) =
      P |> Logic.varify_global |> close_form |> postproc
    val path =
      Path.explode file_name
      |> (fn path =>
             path |> not (Path.is_absolute path)
                     ? Path.append (Path.explode "$PWD"))
    val ((_, _, problem), thy) =
      TPTP_Interpret.interpret_file true (Path.explode "$TPTP") path [] [] thy
    val (conjs, defs_and_nondefs) =
      problem |> List.partition (has_role TPTP_Syntax.Role_Conjecture)
              ||> List.partition (has_role TPTP_Syntax.Role_Definition)
  in
    (map get_prop conjs, pairself (map get_prop) defs_and_nondefs,
     thy |> Theory.checkpoint |> Proof_Context.init_global)
  end


(** Nitpick (alias Nitrox) **)

fun aptrueprop f ((t0 as @{const Trueprop}) $ t1) = t0 $ f t1
  | aptrueprop f t = f t

fun nitpick_tptp_file thy timeout file_name =
  let
    val (conjs, (defs, nondefs), ctxt) = read_tptp_file thy I file_name
    val thy = Proof_Context.theory_of ctxt
    val defs = defs |> map (ATP_Util.extensionalize_term ctxt
                            #> aptrueprop (open_form I))
    val state = Proof.init ctxt
    val params =
      [("card", "1\<emdash>100"),
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
      |> Nitpick_Isar.default_params thy
    val i = 1
    val n = 1
    val step = 0
    val subst = []
  in
    Nitpick.pick_nits_in_term state params Nitpick.TPTP i n step subst
        defs nondefs (case conjs of conj :: _ => conj | [] => @{prop True});
    ()
  end


(** Refute **)

fun refute_tptp_file thy timeout file_name =
  let
    fun print_szs_from_outcome falsify s =
      "% SZS status " ^
      (if s = "genuine" then
         if falsify then "CounterSatisfiable" else "Satisfiable"
       else
         "Unknown")
      |> Output.urgent_message
    val (conjs, (defs, nondefs), ctxt) = read_tptp_file thy I file_name
    val params =
      [("maxtime", string_of_int timeout),
       ("maxvars", "100000")]
  in
    Refute.refute_term ctxt params (defs @ nondefs)
        (case conjs of conj :: _ => conj | [] => @{prop True})
    |> print_szs_from_outcome (not (null conjs))
  end


(** Sledgehammer and Isabelle (combination of provers) **)

fun can_tac ctxt tactic conj = can (Goal.prove ctxt [] [] conj) (K tactic)

fun SOLVE_TIMEOUT seconds name tac st =
  let
    val _ = Output.urgent_message ("running " ^ name ^ " for " ^
                                   string_of_int seconds ^ " s")
    val result =
      TimeLimit.timeLimit (Time.fromSeconds seconds)
        (fn () => SINGLE (SOLVE tac) st) ()
      handle TimeLimit.TimeOut => NONE
        | ERROR _ => NONE
  in
    case result of
      NONE => (Output.urgent_message ("FAILURE: " ^ name); Seq.empty)
    | SOME st' => (Output.urgent_message ("SUCCESS: " ^ name); Seq.single st')
  end

fun nitpick_finite_oracle_tac ctxt timeout i th =
  let
    fun is_safe (Type (@{type_name fun}, Ts)) = forall is_safe Ts
      | is_safe @{typ prop} = true
      | is_safe @{typ bool} = true
      | is_safe _ = false
    val conj = Thm.term_of (Thm.cprem_of th i)
  in
    if exists_type (not o is_safe) conj then
      Seq.empty
    else
      let
        val thy = Proof_Context.theory_of ctxt
        val state = Proof.init ctxt
        val params =
          [("box", "false"),
           ("max_threads", "1"),
           ("verbose", "true"),
           ("debug", if debug then "true" else "false"),
           ("overlord", if overlord then "true" else "false"),
           ("max_potential", "0"),
           ("timeout", string_of_int timeout)]
          |> Nitpick_Isar.default_params thy
        val i = 1
        val n = 1
        val step = 0
        val subst = []
        val (outcome, _) =
          Nitpick.pick_nits_in_term state params Nitpick.Normal i n step subst
                                    [] [] conj
      in if outcome = "none" then Skip_Proof.cheat_tac thy th else Seq.empty end
  end

fun atp_tac ctxt aggressivity override_params timeout prover =
  let
    val ctxt =
      ctxt |> Config.put Sledgehammer_Provers.aggressive (aggressivity > 0)
  in
    Sledgehammer_Tactics.sledgehammer_as_oracle_tac ctxt
        ([("debug", if debug then "true" else "false"),
          ("overlord", if overlord then "true" else "false"),
          ("provers", prover),
          ("timeout", string_of_int timeout)] @
         (if aggressivity > 0 then
            [("type_enc",
              if aggressivity = 1 then "mono_native" else "poly_guards??"),
             ("slicing", "false")]
          else
            []) @
         override_params)
        {add = [(Facts.named (Thm.derivation_name ext), [])],
         del = [], only = true}
  end

fun sledgehammer_tac demo ctxt timeout i =
  let
    val frac = if demo then 16 else 12
    fun slice mult aggressivity prover =
      SOLVE_TIMEOUT (mult * timeout div frac)
          (prover ^
           (if aggressivity > 0 then "(" ^ string_of_int aggressivity ^ ")"
            else ""))
          (atp_tac ctxt aggressivity [] (timeout div frac) prover i)
  in
    slice 2 0 ATP_Systems.spassN
    ORELSE slice 2 0 ATP_Systems.vampireN
    ORELSE slice 2 0 ATP_Systems.eN
    ORELSE slice 2 0 ATP_Systems.z3_tptpN
    ORELSE slice 1 1 ATP_Systems.spassN
    ORELSE slice 1 2 ATP_Systems.eN
    ORELSE slice 1 1 ATP_Systems.vampireN
    ORELSE slice 1 2 ATP_Systems.vampireN
    ORELSE
      (if demo then
         slice 2 0 ATP_Systems.satallaxN
         ORELSE slice 2 0 ATP_Systems.leo2N
       else
         no_tac)
  end

fun smt_solver_tac solver ctxt =
  let
    val ctxt = ctxt |> Context.proof_map (SMT_Config.select_solver solver)
  in SMT_Solver.smt_tac ctxt [] end

fun auto_etc_tac ctxt timeout i =
  SOLVE_TIMEOUT (timeout div 20) "nitpick"
      (nitpick_finite_oracle_tac ctxt (timeout div 20) i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "simp"
      (asm_full_simp_tac (simpset_of ctxt) i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "blast" (blast_tac ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 5) "auto+spass"
      (auto_tac ctxt
       THEN ALLGOALS (atp_tac ctxt 0 [] (timeout div 5) ATP_Systems.spassN))
  ORELSE SOLVE_TIMEOUT (timeout div 10) "fast" (fast_tac ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "z3" (smt_solver_tac "z3" ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "cvc3" (smt_solver_tac "cvc3" ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "best" (best_tac ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "force" (force_tac ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "meson" (Meson.meson_tac ctxt [] i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "fastforce" (fast_force_tac ctxt i)

fun problem_const_prefix thy = Context.theory_name thy ^ Long_Name.separator

(* Isabelle's standard automatic tactics ("auto", etc.) are more eager to
   unfold "definitions" of free variables than of constants (cf. PUZ107^5). *)
fun freeze_problem_consts thy =
  let val is_problem_const = String.isPrefix (problem_const_prefix thy) in
    map_aterms (fn t as Const (s, T) =>
                   if is_problem_const s then Free (Long_Name.base_name s, T)
                   else t
                 | t => t)
  end

fun make_conj (defs, nondefs) conjs =
  Logic.list_implies (rev defs @ rev nondefs,
                      case conjs of conj :: _ => conj | [] => @{prop False})

fun print_szs_from_success conjs success =
  Output.urgent_message ("% SZS status " ^
                         (if success then
                            if null conjs then "Unsatisfiable" else "Theorem"
                          else
                            "Unknown"))

fun sledgehammer_tptp_file thy timeout file_name =
  let
    val (conjs, assms, ctxt) =
      read_tptp_file thy (freeze_problem_consts thy) file_name
    val conj = make_conj assms conjs
  in
    can_tac ctxt (sledgehammer_tac true ctxt timeout 1) conj
    |> print_szs_from_success conjs
  end

fun isabelle_tptp_file demo thy timeout file_name =
  let
    val (conjs, assms, ctxt) =
      read_tptp_file thy (freeze_problem_consts thy) file_name
    val conj = make_conj assms conjs
    val last_hope = if demo then ATP_Systems.satallaxN else ATP_Systems.vampireN
  in
    (can_tac ctxt (auto_etc_tac ctxt (timeout div 2) 1) conj orelse
     can_tac ctxt (sledgehammer_tac demo ctxt (timeout div 2) 1) conj orelse
     can_tac ctxt (atp_tac ctxt 2 [] timeout last_hope 1) conj)
    |> print_szs_from_success conjs
  end

val isabelle_demo_tptp_file = isabelle_tptp_file true
val isabelle_comp_tptp_file = isabelle_tptp_file false


(** Translator between TPTP(-like) file formats **)

fun translate_tptp_file format in_file_name out_file_name = ()

end;
