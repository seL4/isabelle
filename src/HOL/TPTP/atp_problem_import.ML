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


(** TPTP parsing based on ML-Yacc-generated "TPTP_Parser" **)

(* cf. "close_form" in "refute.ML" *)
fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
           Logic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
       (Term.add_vars t []) t

fun read_tptp_file thy file_name =
  let
    fun has_role role (_, role', _, _) = (role' = role)
    fun get_prop (_, _, P, _) = P |> Logic.varify_global |> close_form
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
     Theory.checkpoint thy)
  end

(** Nitpick (alias Nitrox) **)

fun aptrueprop f ((t0 as @{const Trueprop}) $ t1) = t0 $ f t1
  | aptrueprop f t = f t

fun nitpick_tptp_file timeout file_name =
  let
    val (conjs, (defs, nondefs), thy) = read_tptp_file @{theory} file_name
    val ctxt = Proof_Context.init_global thy
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
(*
       ("debug", "true"),
       ("overlord", "true"),
*)
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
      |> writeln
    val (conjs, (defs, nondefs), thy) = read_tptp_file @{theory} file_name
    val ctxt = Proof_Context.init_global thy
    val params =
      [("maxtime", string_of_int timeout),
       ("maxvars", "100000")]
  in
    Refute.refute_term ctxt params (defs @ nondefs)
        (case conjs of conj :: _ => conj | [] => @{prop True})
    |> print_szs_from_outcome (not (null conjs))
  end


(** Sledgehammer and Isabelle (combination of provers) **)

fun SOLVE_TIMEOUT seconds name tac st =
  let
    val result =
      TimeLimit.timeLimit (Time.fromSeconds seconds)
        (fn () => SINGLE (SOLVE tac) st) ()
      handle TimeLimit.TimeOut => NONE
        | ERROR _ => NONE
  in
    (case result of
      NONE => (warning ("FAILURE: " ^ name); Seq.empty)
    | SOME st' => (warning ("SUCCESS: " ^ name); Seq.single st'))
  end

fun apply_tactic_to_tptp_file tactic timeout file_name =
  let
    val (conjs, (defs, nondefs), thy) = read_tptp_file @{theory} file_name
    val ctxt = Proof_Context.init_global thy
    val conj =
      Logic.list_implies (defs @ nondefs,
                          case conjs of conj :: _ => conj | [] => @{prop False})
  in
    case try (Goal.prove ctxt [] [] conj) (K (tactic ctxt timeout)) of
      SOME _ =>
      writeln ("% SZS status " ^
               (if null conjs then "Unsatisfiable" else "Theorem"))
    | NONE => writeln ("% SZS status Unknown")
  end

fun atp_tac ctxt timeout prover =
  Sledgehammer_Tactics.sledgehammer_as_oracle_tac ctxt
      [
(*
       ("debug", "true"),
       ("overlord", "true"),
*)
       ("provers", prover),
       ("timeout", string_of_int timeout)]
      Sledgehammer_Filter.no_relevance_override

val cvc3N = "cvc3"
val z3N = "z3"

fun sledgehammer_tac ctxt timeout =
  let
    fun slice timeout prover =
      SOLVE_TIMEOUT timeout prover (ALLGOALS (atp_tac ctxt timeout prover))
  in
    slice (timeout div 10) ATP_Systems.spassN
    ORELSE
    slice (timeout div 10) z3N
    ORELSE
    slice (timeout div 10) ATP_Systems.vampireN
    ORELSE
    slice (timeout div 10) ATP_Systems.eN
    ORELSE
    slice (timeout div 10) cvc3N
    ORELSE
    slice (timeout div 10) ATP_Systems.leo2N
    ORELSE
    slice timeout ATP_Systems.satallaxN
  end

val sledgehammer_tptp_file = apply_tactic_to_tptp_file sledgehammer_tac

(** Isabelle (combination of provers) **)

fun isabelle_tac ctxt timeout =
  sledgehammer_tac ctxt (timeout div 2)
  ORELSE
  SOLVE_TIMEOUT (timeout div 10) "simp"
      (ALLGOALS (asm_full_simp_tac (simpset_of ctxt)))
  ORELSE
  SOLVE_TIMEOUT (timeout div 10) "blast" (ALLGOALS (blast_tac ctxt))
  ORELSE
  SOLVE_TIMEOUT (timeout div 20) "auto+spass"
      (auto_tac ctxt
       THEN ALLGOALS (atp_tac ctxt (timeout div 20) ATP_Systems.spassN))
  ORELSE
  SOLVE_TIMEOUT (timeout div 20) "fast" (ALLGOALS (fast_tac ctxt))
  ORELSE
  SOLVE_TIMEOUT (timeout div 20) "best" (ALLGOALS (best_tac ctxt))
  ORELSE
  SOLVE_TIMEOUT (timeout div 20) "force" (ALLGOALS (force_tac ctxt))
  ORELSE
  SOLVE_TIMEOUT (timeout div 20) "arith" (ALLGOALS (Arith_Data.arith_tac ctxt))
  ORELSE
  SOLVE_TIMEOUT timeout "fastforce" (ALLGOALS (fast_force_tac ctxt))
  ORELSE
  SOLVE_TIMEOUT timeout "satallax"
      (ALLGOALS (atp_tac ctxt timeout ATP_Systems.satallaxN))

val isabelle_tptp_file = apply_tactic_to_tptp_file isabelle_tac


(** Translator between TPTP(-like) file formats **)

fun translate_tptp_file format in_file_name out_file_name = ()

end;
