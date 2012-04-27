(*  Title:      HOL/TPTP/atp_problem_import.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Import TPTP problems as Isabelle terms or goals.
*)

signature ATP_PROBLEM_IMPORT =
sig
  val nitpick_tptp_file : int -> string -> unit
  val refute_tptp_file : int -> string -> unit
  val sledgehammer_tptp_file : int -> string -> unit
  val isabelle_tptp_file : int -> string -> unit
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

fun nitpick_tptp_file timeout file_name =
  let
    val (conjs, (defs, nondefs), ctxt) = read_tptp_file @{theory} I file_name
    val thy = Proof_Context.theory_of ctxt
    val defs = defs |> map (ATP_Util.extensionalize_term ctxt
                            #> aptrueprop (open_form I))
    val state = Proof.init ctxt
    val params =
      [("card", "1\<emdash>100"),
       ("box", "false"),
       ("sat_solver", "smart"),
       ("max_threads", "1"),
       ("batch_size", "10"),
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

fun refute_tptp_file timeout file_name =
  let
    fun print_szs_from_outcome falsify s =
      "% SZS status " ^
      (if s = "genuine" then
         if falsify then "CounterSatisfiable" else "Satisfiable"
       else
         "Unknown")
      |> Output.urgent_message
    val (conjs, (defs, nondefs), ctxt) = read_tptp_file @{theory} I file_name
    val params =
      [("maxtime", string_of_int timeout),
       ("maxvars", "100000")]
  in
    Refute.refute_term ctxt params (defs @ nondefs)
        (case conjs of conj :: _ => conj | [] => @{prop True})
    |> print_szs_from_outcome (not (null conjs))
  end


(** Sledgehammer and Isabelle (combination of provers) **)

val cvc3N = "cvc3"
val z3N = "z3"

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

fun atp_tac ctxt override_params timeout prover =
  Sledgehammer_Tactics.sledgehammer_as_oracle_tac ctxt
      ([("debug", if debug then "true" else "false"),
        ("overlord", if overlord then "true" else "false"),
        ("provers", prover),
        ("timeout", string_of_int timeout)] @ override_params)
      {add = [], del = [], only = true}

fun sledgehammer_tac ctxt timeout i =
  let
    fun slice overload_params fraq prover =
      SOLVE_TIMEOUT (timeout div fraq) prover
                    (atp_tac ctxt overload_params timeout prover i)
  in
    slice [] 7 ATP_Systems.satallaxN
    ORELSE slice [] 7 ATP_Systems.spassN
    ORELSE slice [] 7 z3N
    ORELSE slice [] 7 ATP_Systems.vampireN
    ORELSE slice [] 7 ATP_Systems.eN
    ORELSE slice [] 7 cvc3N
    ORELSE slice [] 7 ATP_Systems.leo2N
  end

fun auto_etc_tac ctxt timeout i =
  SOLVE_TIMEOUT (timeout div 10) "simp" (asm_full_simp_tac (simpset_of ctxt) i)
  ORELSE SOLVE_TIMEOUT (timeout div 10) "blast" (blast_tac ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "auto+spass"
      (auto_tac ctxt
       THEN ALLGOALS (atp_tac ctxt [] (timeout div 20) ATP_Systems.spassN))
  ORELSE SOLVE_TIMEOUT (timeout div 20) "fast" (fast_tac ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "best" (best_tac ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "force" (force_tac ctxt i)
  ORELSE SOLVE_TIMEOUT (timeout div 20) "arith" (Arith_Data.arith_tac ctxt i)
  ORELSE SOLVE_TIMEOUT timeout "fastforce" (fast_force_tac ctxt i)

val problem_const_prefix = Context.theory_name @{theory} ^ Long_Name.separator

(* Isabelle's standard automatic tactics ("auto", etc.) are more eager to
   unfold "definitions" of free variables than of constants (cf. PUZ107^5). *)
val freeze_problem_consts =
  map_aterms (fn t as Const (s, T) =>
                 if String.isPrefix problem_const_prefix s then
                   Free (Long_Name.base_name s, T)
                 else
                   t
               | t => t)

fun make_conj (defs, nondefs) conjs =
  Logic.list_implies (rev defs @ rev nondefs,
                      case conjs of conj :: _ => conj | [] => @{prop False})

fun print_szs_from_success conjs success =
  Output.urgent_message ("% SZS status " ^
                         (if success then
                            if null conjs then "Unsatisfiable" else "Theorem"
                          else
                            "% SZS status Unknown"))

fun sledgehammer_tptp_file timeout file_name =
  let
    val (conjs, assms, ctxt) =
      read_tptp_file @{theory} freeze_problem_consts file_name
    val conj = make_conj assms conjs
  in
    can_tac ctxt (sledgehammer_tac ctxt timeout 1) conj
    |> print_szs_from_success conjs
  end

fun isabelle_tptp_file timeout file_name =
  let
    val (conjs, assms, ctxt) =
      read_tptp_file @{theory} freeze_problem_consts file_name
    val conj = make_conj assms conjs
  in
    (can_tac ctxt (sledgehammer_tac ctxt (timeout div 2) 1) conj orelse
     can_tac ctxt (auto_etc_tac ctxt (timeout div 2) 1) conj orelse
     can_tac ctxt (atp_tac ctxt [] timeout ATP_Systems.satallaxN 1) conj)
    |> print_szs_from_success conjs
  end

(** Translator between TPTP(-like) file formats **)

fun translate_tptp_file format in_file_name out_file_name = ()

end;
