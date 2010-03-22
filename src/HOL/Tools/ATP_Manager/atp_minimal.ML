(*  Title:      HOL/Tools/ATP_Manager/atp_minimal.ML
    Author:     Philipp Meyer, TU Muenchen

Minimization of theorem list for Metis using automatic theorem provers.
*)

signature ATP_MINIMAL =
sig
  type prover = ATP_Manager.prover
  type prover_result = ATP_Manager.prover_result
  type 'a minimize_fun = ('a list -> bool) -> 'a list -> 'a list

  val linear_minimize : 'a minimize_fun
  val binary_minimize : 'a minimize_fun
  val minimize_theorems :
    (string * thm list) minimize_fun -> prover -> string -> int
    -> Proof.state -> (string * thm list) list
    -> (string * thm list) list option * string
end;

structure ATP_Minimal : ATP_MINIMAL =
struct

open Sledgehammer_Fact_Preprocessor
open ATP_Manager

type 'a minimize_fun = ('a list -> bool) -> 'a list -> 'a list

(* Linear minimization algorithm *)

fun linear_minimize p s =
  let
    fun aux [] needed = needed
      | aux (x :: xs) needed = aux xs (needed |> not (p (xs @ needed)) ? cons x)
  in aux s [] end;

(* Binary minimalization *)

local
  fun isplit (l, r) [] = (l, r)
    | isplit (l, r) [h] = (h :: l, r)
    | isplit (l, r) (h1 :: h2 :: t) = isplit (h1 :: l, h2 :: r) t
in
  fun split lst = isplit ([], []) lst
end

local
  fun min _ _ [] = raise Empty
    | min _ _ [s0] = [s0]
    | min p sup s =
      let
        val (l0, r0) = split s
      in
        if p (sup @ l0) then
          min p sup l0
        else if p (sup @ r0) then
          min p sup r0
        else
          let
            val l = min p (sup @ r0) l0
            val r = min p (sup @ l) r0
          in l @ r end
      end
in
  (* return a minimal subset v of s that satisfies p
   @pre p(s) & ~p([]) & monotone(p)
   @post v subset s & p(v) &
         forall e in v. ~p(v \ e)
   *)
  fun binary_minimize p s =
    case min p [] s of
      [x] => if p [] then [] else [x]
    | m => m
end


(* failure check and producing answer *)

datatype 'a prove_result = Success of 'a | Failure | Timeout | Error

val string_of_result =
  fn Success _ => "Success"
   | Failure => "Failure"
   | Timeout => "Timeout"
   | Error => "Error"

val failure_strings =
  [("SPASS beiseite: Ran out of time.", Timeout),
   ("Timeout", Timeout),
   ("time limit exceeded", Timeout),
   ("# Cannot determine problem status within resource limit", Timeout),
   ("Error", Error)]

fun produce_answer ({success, proof, internal_thm_names, filtered_clauses, ...}
                    : prover_result) =
  if success then
    (Success (Vector.foldr (op ::) [] internal_thm_names, filtered_clauses),
     proof)
  else
    let
      val failure = failure_strings |> get_first (fn (s, t) =>
          if String.isSubstring s proof then SOME (t, proof) else NONE)
    in
      (case failure of
        SOME res => res
      | NONE => (Failure, proof))
    end


(* wrapper for calling external prover *)

fun sledgehammer_test_theorems prover time_limit subgoalno state filtered
                               name_thms_pairs =
  let
    val _ = priority ("Testing " ^ string_of_int (length name_thms_pairs) ^
                      " theorems... ")
    val name_thm_pairs = maps (fn (n, ths) => map (pair n) ths) name_thms_pairs
    val axclauses = cnf_rules_pairs (Proof.theory_of state) name_thm_pairs
    val {context = ctxt, facts, goal} = Proof.goal state
    val problem =
     {with_full_types = ! ATP_Manager.full_types,
      subgoal = subgoalno,
      goal = (ctxt, (facts, goal)),
      axiom_clauses = SOME axclauses,
      filtered_clauses = filtered}
    val (result, proof) = produce_answer (prover time_limit problem)
    val _ = priority (string_of_result result)
  in (result, proof) end


(* minimalization of thms *)

fun minimize_theorems gen_min prover prover_name time_limit state
                      name_thms_pairs =
  let
    val _ =
      priority ("Minimize called with " ^ string_of_int (length name_thms_pairs) ^
        " theorems, prover: " ^ prover_name ^
        ", time limit: " ^ string_of_int time_limit ^ " seconds")
    val test_thms_fun = sledgehammer_test_theorems prover time_limit 1 state
    fun test_thms filtered thms =
      case test_thms_fun filtered thms of (Success _, _) => true | _ => false
  in
    (* try prove first to check result and get used theorems *)
    (case test_thms_fun NONE name_thms_pairs of
      (Success (used, filtered), _) =>
        let
          val ordered_used = sort_distinct string_ord used
          val to_use =
            if length ordered_used < length name_thms_pairs then
              filter (fn (name1, _) => List.exists (equal name1) ordered_used) name_thms_pairs
            else name_thms_pairs
          val min_thms =
            if null to_use then []
            else gen_min (test_thms (SOME filtered)) to_use
          val min_names = sort_distinct string_ord (map fst min_thms)
          val _ = priority (cat_lines
            ["Minimal " ^ string_of_int (length min_thms) ^ " theorems"])
        in
          (SOME min_thms, "Try this command: " ^
            Markup.markup Markup.sendback ("apply (metis " ^ space_implode " " min_names ^ ")"))
        end
    | (Timeout, _) =>
        (NONE, "Timeout: You may need to increase the time limit of " ^
          string_of_int time_limit ^ " seconds. Call atp_minimize [time=...] ")
    | (Error, msg) =>
        (NONE, "Error in prover: " ^ msg)
    | (Failure, _) =>
        (NONE, "Failure: No proof with the theorems supplied"))
    handle Sledgehammer_HOL_Clause.TRIVIAL =>
        (SOME [], "Trivial: Try this command: " ^ Markup.markup Markup.sendback "apply metis")
      | ERROR msg => (NONE, "Error: " ^ msg)
  end

end;
