(*  Title:      HOL/Tools/Nunchaku/nunchaku.ML
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

The core of the Nunchaku integration in Isabelle.
*)

signature NUNCHAKU =
sig
  type isa_model = Nunchaku_Reconstruct.isa_model

  datatype mode = Auto_Try | Try | Normal

  type mode_of_operation_params =
    {solvers: string list,
     falsify: bool,
     assms: bool,
     spy: bool,
     overlord: bool,
     expect: string}

  type scope_of_search_params =
    {wfs: ((string * typ) option * bool option) list,
     whacks: (term option * bool) list,
     min_bound: int,
     max_bound: int option,
     bound_increment: int,
     cards: (typ option * (int option * int option)) list,
     monos: (typ option * bool option) list}

  type output_format_params =
    {verbose: bool,
     debug: bool,
     max_potential: int,
     max_genuine: int,
     evals: term list,
     atomss: (typ option * string list) list}

  type optimization_params =
    {specialize: bool,
     multithread: bool}

  type timeout_params =
    {timeout: Time.time,
     wf_timeout: Time.time}

  type params =
    {mode_of_operation_params: mode_of_operation_params,
     scope_of_search_params: scope_of_search_params,
     output_format_params: output_format_params,
     optimization_params: optimization_params,
     timeout_params: timeout_params}

  val genuineN: string
  val quasi_genuineN: string
  val potentialN: string
  val noneN: string
  val unknownN: string
  val no_nunchakuN: string

  val run_chaku_on_prop: Proof.state -> params -> mode -> int -> term list -> term ->
    string * isa_model option
  val run_chaku_on_subgoal: Proof.state -> params -> mode -> int -> string * isa_model option
end;

structure Nunchaku : NUNCHAKU =
struct

open Nunchaku_Util;
open Nunchaku_Collect;
open Nunchaku_Problem;
open Nunchaku_Translate;
open Nunchaku_Model;
open Nunchaku_Reconstruct;
open Nunchaku_Display;
open Nunchaku_Tool;

datatype mode = Auto_Try | Try | Normal;

type mode_of_operation_params =
  {solvers: string list,
   falsify: bool,
   assms: bool,
   spy: bool,
   overlord: bool,
   expect: string};

type scope_of_search_params =
  {wfs: ((string * typ) option * bool option) list,
   whacks: (term option * bool) list,
   min_bound: int,
   max_bound: int option,
   bound_increment: int,
   cards: (typ option * (int option * int option)) list,
   monos: (typ option * bool option) list};

type output_format_params =
  {verbose: bool,
   debug: bool,
   max_potential: int,
   max_genuine: int,
   evals: term list,
   atomss: (typ option * string list) list};

type optimization_params =
  {specialize: bool,
   multithread: bool};

type timeout_params =
  {timeout: Time.time,
   wf_timeout: Time.time};

type params =
  {mode_of_operation_params: mode_of_operation_params,
   scope_of_search_params: scope_of_search_params,
   output_format_params: output_format_params,
   optimization_params: optimization_params,
   timeout_params: timeout_params};

val genuineN = "genuine";
val quasi_genuineN = "quasi_genuine";
val potentialN = "potential";
val noneN = "none";
val unknownN = "unknown";

val no_nunchakuN = "no_nunchaku";

fun str_of_mode Auto_Try = "Auto_Try"
  | str_of_mode Try = "Try"
  | str_of_mode Normal = "Normal";

fun none_true assigns = forall (curry (op <>) (SOME true) o snd) assigns;

fun has_lonely_bool_var \<^Const_>\<open>Pure.conjunction for \<^Const_>\<open>Trueprop for \<open>Free _\<close>\<close> _\<close> = true
  | has_lonely_bool_var _ = false;

val syntactic_sorts =
  \<^sort>\<open>{default,zero,one,plus,minus,uminus,times,inverse,abs,sgn,ord,equal}\<close> @ \<^sort>\<open>numeral\<close>;

fun has_tfree_syntactic_sort (TFree (_, S as _ :: _)) = subset (op =) (S, syntactic_sorts)
  | has_tfree_syntactic_sort _ = false;

val has_syntactic_sorts = exists_type (exists_subtype has_tfree_syntactic_sort);

val unprefix_error =
  perhaps (try (unprefix "failure: "))
  #> perhaps (try (unprefix "Error: "));

(* Give the soft timeout a chance. *)
val timeout_slack = seconds 1.0;

fun run_chaku_on_prop state
    ({mode_of_operation_params = {solvers, falsify, assms, spy, overlord, expect},
      scope_of_search_params = {wfs, whacks, min_bound, max_bound, bound_increment, cards, monos},
      output_format_params = {verbose, debug, evals, atomss, ...},
      optimization_params = {specialize, ...},
      timeout_params = {timeout, wf_timeout}})
    mode i all_assms subgoal =
  let
    val ctxt = Proof.context_of state;

    val time_start = Time.now ()

    val print = writeln;
    val print_n = if mode = Normal then writeln else K ();
    fun print_v f = if verbose then writeln (f ()) else ();
    fun print_d f = if debug then writeln (f ()) else ();

    val das_wort_Model = if falsify then "Countermodel" else "Model";
    val das_wort_model = if falsify then "countermodel" else "model";

    val tool_params =
      {solvers = solvers, overlord = overlord, min_bound = min_bound, max_bound = max_bound,
       bound_increment = bound_increment, debug = debug, specialize = specialize,
       timeout = timeout};

    fun run () =
      let
        val outcome as (outcome_code, _) =
          let
            val (poly_axioms, isa_problem as {sound, complete, ...}) =
              isa_problem_of_subgoal ctxt falsify wfs whacks cards debug wf_timeout evals
                (if assms then all_assms else []) subgoal;
            val _ = print_d (fn () => "*** Isabelle problem ***\n" ^
              str_of_isa_problem ctxt isa_problem);
            val ugly_nun_problem = nun_problem_of_isa ctxt isa_problem;
            val _ = print_d (fn () => "*** Ugly Nunchaku problem ***\n" ^
              str_of_nun_problem ugly_nun_problem);
            val (nice_nun_problem, pool) = nice_nun_problem ugly_nun_problem;
            val _ = print_d (fn () => "*** Nice Nunchaku problem ***\n" ^
              str_of_nun_problem nice_nun_problem);

            fun print_any_hints () =
              if has_lonely_bool_var subgoal then
                print "Hint: Maybe you forgot a colon after the lemma's name?"
              else if has_syntactic_sorts subgoal then
                print "Hint: Maybe you forgot a type constraint?"
              else
                ();

            fun get_isa_model_opt output =
              let
                val nice_nun_model = nun_model_of_str output;
                val _ = print_d (fn () => "*** Nice Nunchaku model ***\n" ^
                  str_of_nun_model nice_nun_model);
                val ugly_nun_model = ugly_nun_model pool nice_nun_model;
                val _ = print_d (fn () => "*** Ugly Nunchaku model ***\n" ^
                  str_of_nun_model ugly_nun_model);

                val pat_completes = pat_completes_of_isa_problem isa_problem;
                val raw_isa_model = isa_model_of_nun ctxt pat_completes atomss ugly_nun_model;
                val _ = print_d (fn () => "*** Raw Isabelle model ***\n" ^
                  str_of_isa_model ctxt raw_isa_model);

                val cleaned_isa_model = clean_up_isa_model ctxt raw_isa_model;
                val _ = print_d (fn () => "*** Cleaned-up Isabelle model ***\n" ^
                  str_of_isa_model ctxt cleaned_isa_model);
              in
                cleaned_isa_model
              end;

            fun isa_model_opt output =
              if debug then SOME (get_isa_model_opt output) else try get_isa_model_opt output;

            val model_str = isa_model_opt #> pretty_of_isa_model_opt ctxt #> Pretty.string_of;

            fun unsat_means_theorem () =
              null whacks andalso null cards andalso null monos;

            fun unknown () =
              (print_n ("No " ^ das_wort_model ^ " found"); (unknownN, NONE));

            fun unsat_or_unknown solver complete =
              if complete then
                (print_n ("No " ^ das_wort_model ^ " exists (according to " ^ solver ^ ")" ^
                   (if falsify andalso unsat_means_theorem () then "\nThe goal is a theorem"
                    else ""));
                 (noneN, NONE))
              else
                unknown ();

            fun sat_or_maybe_sat solver sound output =
              let val header = if sound then das_wort_Model else "Potential " ^ das_wort_model in
                (case (null poly_axioms, none_true wfs) of
                  (true, true) =>
                  (print (header ^ " (according to " ^ solver ^ "):\n" ^
                     model_str output); print_any_hints ();
                   (genuineN, isa_model_opt output))
                | (no_poly, no_wf) =>
                  let
                    val ignorings = []
                      |> not no_poly ? cons "polymorphic axioms"
                      |> not no_wf ? cons "unchecked well-foundedness";
                  in
                    (print (header ^ " (according to " ^ solver ^
                       ", ignoring " ^ space_implode " and " ignorings ^ "):\n" ^
                       model_str output ^
                       (if no_poly then
                          ""
                        else
                          "\nIgnored axioms:\n" ^
                          cat_lines (map (prefix "  " o Syntax.string_of_term ctxt) poly_axioms)));
                     print_any_hints ();
                     (quasi_genuineN, isa_model_opt output))
                  end)
              end;
          in
            (case solve_nun_problem tool_params nice_nun_problem of
              Unsat solver => unsat_or_unknown solver complete
            | Sat (solver, output, _) => sat_or_maybe_sat solver sound output
            | Unknown NONE => unknown ()
            | Unknown (SOME (solver, output, _)) => sat_or_maybe_sat solver false output
            | Timeout => (print_n "Time out"; (unknownN, NONE))
            | Nunchaku_Var_Not_Set =>
              (print_n ("Variable $" ^ nunchaku_home_env_var ^ " not set"); (unknownN, NONE))
            | Nunchaku_Cannot_Execute =>
              (print_n "External tool \"nunchaku\" cannot execute"; (unknownN, NONE))
            | Nunchaku_Not_Found =>
              (print_n "External tool \"nunchaku\" not found"; (unknownN, NONE))
            | CVC4_Cannot_Execute =>
              (print_n "External tool \"cvc4\" cannot execute"; (unknownN, NONE))
            | CVC4_Not_Found => (print_n "External tool \"cvc4\" not found"; (unknownN, NONE))
            | Unknown_Error (code, msg) =>
              (print_n ("Error: " ^ unprefix_error msg ^
                 (if code = 0 then "" else " (code " ^ string_of_int code ^ ")"));
               (unknownN, NONE)))
          end
          handle
            CYCLIC_DEPS () =>
            (print_n "Cyclic dependencies (or bug in Nunchaku)"; (unknownN, NONE))
          | TOO_DEEP_DEPS () =>
            (print_n "Too deep dependencies (or bug in Nunchaku)"; (unknownN, NONE))
          | TOO_META t =>
            (print_n ("Formula too meta for Nunchaku:\n" ^ Syntax.string_of_term ctxt t);
             (unknownN, NONE))
          | UNEXPECTED_POLYMORPHISM t =>
            (print_n ("Unexpected polymorphism in term\n" ^ Syntax.string_of_term ctxt t);
             (unknownN, NONE))
          | UNEXPECTED_VAR t =>
            (print_n ("Unexpected schematic variables in term\n" ^ Syntax.string_of_term ctxt t);
             (unknownN, NONE))
          | UNSUPPORTED_FUNC t =>
            (print_n ("Unsupported low-level constant in problem: " ^ Syntax.string_of_term ctxt t);
             (unknownN, NONE));
      in
        if expect = "" orelse outcome_code = expect then outcome
        else error ("Unexpected outcome: " ^ quote outcome_code)
      end;

    val _ = spying spy (fn () => (state, i, "starting " ^ str_of_mode mode ^ " mode"));

    val outcome as (outcome_code, _) =
      Timeout.apply (timeout + timeout_slack) run ()
      handle Timeout.TIMEOUT _ => (print_n "Time out"; (unknownN, NONE));

    val _ = print_v (fn () => "Total time: " ^ string_of_time (Time.now () - time_start));

    val _ = spying spy (fn () => (state, i, "outcome: " ^ outcome_code));
  in
    if expect = "" orelse outcome_code = expect then outcome
    else error ("Unexpected outcome: " ^ quote outcome_code)
  end;

fun run_chaku_on_subgoal state params mode i =
  let
    val ctxt = Proof.context_of state;
    val goal = Thm.prop_of (#goal (Proof.raw_goal state));
  in
    if Logic.count_prems goal = 0 then
      (writeln "No subgoal!"; (noneN, NONE))
    else
      let
        val subgoal = fst (Logic.goal_params goal i);
        val all_assms = map Thm.term_of (Assumption.all_assms_of ctxt);
      in
        run_chaku_on_prop state params mode i all_assms subgoal
      end
  end;

end;
