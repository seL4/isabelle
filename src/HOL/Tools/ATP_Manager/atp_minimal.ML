(*  Title:      HOL/Tools/ATP_Manager/atp_minimal.ML
    Author:     Philipp Meyer, TU Muenchen

Minimalization of theorem list for metis by using an external automated theorem prover
*)

structure AtpMinimal: sig end =
struct

(* output control *)

fun debug str = Output.debug (fn () => str)
fun debug_fn f = if ! Output.debugging then f () else ()
fun answer str = Output.writeln str
fun println str = Output.priority str

fun order_unique name_list = OrdList.make (String.collate Char.compare) name_list
fun length_string namelist = Int.toString (length namelist)

fun print_names name_thms_pairs =
  let
    val names = map fst name_thms_pairs
    val ordered = order_unique names
  in
    app (fn name => (debug ("  " ^ name))) ordered
  end


(* minimalization algorithm *)

local
  fun isplit (l,r) [] = (l,r)
    | isplit (l,r) (h::[]) = (h::l, r)
    | isplit (l,r) (h1::h2::t) = isplit (h1::l, h2::r) t
in
  fun split lst = isplit ([],[]) lst
end

local
  fun min p sup [] = raise Empty
    | min p sup [s0] = [s0]
    | min p sup s =
      let
        val (l0, r0) = split s
      in
        if p (sup @ l0)
        then min p sup l0
        else
          if p (sup @ r0)
          then min p sup r0
          else
            let
              val l = min p (sup @ r0) l0
              val r = min p (sup @ l) r0
            in
              l @ r
            end
      end
in
  (* return a minimal subset v of s that satisfies p
   @pre p(s) & ~p([]) & monotone(p)
   @post v subset s & p(v) &
         forall e in v. ~p(v \ e)
   *)
  fun minimal p s = min p [] s
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

fun produce_answer (success, message, _, result_string, thm_name_vec, filtered) =
  if success then
    (Success (Vector.foldr op:: [] thm_name_vec, filtered), result_string)
  else
    let
      val failure = failure_strings |> get_first (fn (s, t) =>
          if String.isSubstring s result_string then SOME (t, result_string) else NONE)
    in
      if is_some failure then
        the failure
      else
        (Failure, result_string)
    end


(* wrapper for calling external prover *)

fun sh_test_thms prover prover_name time_limit subgoalno state filtered name_thms_pairs =
  let
    val _ = println ("Testing " ^ (length_string name_thms_pairs) ^ " theorems... ")
    val name_thm_pairs =
      flat (map (fn (n, ths) => map_index (fn (i, th) => (n, th)) ths) name_thms_pairs)
    val _ = debug_fn (fn () => print_names name_thm_pairs)
    val axclauses = ResAxioms.cnf_rules_pairs (Proof.theory_of state) name_thm_pairs
    val (result, proof) =
      produce_answer
        (prover time_limit (SOME axclauses) filtered prover_name subgoalno (Proof.get_goal state))
    val _ = println (string_of_result result)
    val _ = debug proof
  in
    (result, proof)
  end


(* minimalization of thms *)

fun minimalize prover prover_name time_limit state name_thms_pairs =
  let
    val _ =
      println ("Minimize called with " ^ length_string name_thms_pairs ^ " theorems, prover: "
        ^ prover_name ^ ", time limit: " ^ Int.toString time_limit ^ " seconds")
    val _ = debug_fn (fn () => app (fn (n, tl) =>
        (debug n; app (fn t =>
          debug ("  " ^ Display.string_of_thm (Proof.context_of state) t)) tl)) name_thms_pairs)
    val test_thms_fun = sh_test_thms prover prover_name time_limit 1 state
    fun test_thms filtered thms =
      case test_thms_fun filtered thms of (Success _, _) => true | _ => false
  in
    (* try prove first to check result and get used theorems *)
    (case test_thms_fun NONE name_thms_pairs of
      (Success (used, filtered), _) =>
        let
          val ordered_used = order_unique used
          val to_use =
            if length ordered_used < length name_thms_pairs then
              filter (fn (name1, _) => List.exists (equal name1) ordered_used) name_thms_pairs
            else
              name_thms_pairs
          val min_thms = (minimal (test_thms (SOME filtered)) to_use)
          val min_names = order_unique (map fst min_thms)
          val _ = println ("Minimal " ^ (length_string min_thms) ^ " theorems")
          val _ = debug_fn (fn () => print_names min_thms)
        in
          answer ("Try this command: " ^
            Markup.markup Markup.sendback ("apply (metis " ^ space_implode " " min_names ^ ")"))
        end
    | (Timeout, _) =>
        answer ("Timeout: You may need to increase the time limit of " ^
          Int.toString time_limit ^ " seconds. Call atp_minimize [time=...] ")
    | (Error, msg) =>
        answer ("Error in prover: " ^ msg)
    | (Failure, _) =>
        answer "Failure: No proof with the theorems supplied")
    handle ResHolClause.TOO_TRIVIAL =>
        answer ("Trivial: Try this command: " ^ Markup.markup Markup.sendback "apply metis")
    | ERROR msg =>
        answer ("Error: " ^ msg)
  end


(* Isar command and parsing input *)

local structure K = OuterKeyword and P = OuterParse and T = OuterLex in

fun get_thms context =
  map (fn (name, interval) =>
    let
      val thmref = Facts.Named ((name, Position.none), interval)
      val ths = ProofContext.get_fact context thmref
      val name' = Facts.string_of_ref thmref
    in
      (name', ths)
    end)

val default_prover = "remote_vampire"
val default_time_limit = 5

fun get_time_limit_arg time_string =
  (case Int.fromString time_string of
    SOME t => t
  | NONE => error ("Invalid time limit: " ^ quote time_string))

val get_options =
  let
    val def = (default_prover, default_time_limit)
  in
    foldl (fn ((name, a), (p, t)) =>
      (case name of
        "time" => (p, (get_time_limit_arg a))
      | "atp" => (a, t)
      | n => error ("Invalid argument: " ^ n))) def
  end

fun sh_min_command args thm_names state =
  let
    val (prover_name, time_limit) = get_options args
    val prover =
      case AtpManager.get_prover prover_name (Proof.theory_of state) of
        SOME prover => prover
      | NONE => error ("Unknown prover: " ^ quote prover_name)
    val name_thms_pairs = get_thms (Proof.context_of state) thm_names
  in
    minimalize prover prover_name time_limit state name_thms_pairs
  end

val parse_args = Scan.optional (Args.bracks (P.list (P.xname --| P.$$$ "=" -- P.xname))) []
val parse_thm_names = Scan.repeat (P.xname -- Scan.option Attrib.thm_sel)

val _ =
  OuterSyntax.command "atp_minimize" "minimize theorem list with external prover" K.diag
    (parse_args -- parse_thm_names >> (fn (args, thm_names) =>
      Toplevel.no_timing o Toplevel.unknown_proof o
        Toplevel.keep (sh_min_command args thm_names o Toplevel.proof_of)))

end

end

