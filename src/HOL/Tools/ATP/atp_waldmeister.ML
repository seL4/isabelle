(*  Title:      HOL/Tools/ATP/atp_waldmeister.ML
    Author:     Albert Steckermeier, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature ATP_WALDMEISTER =
sig
  type ('a, 'b) atp_term = ('a, 'b) ATP_Problem.atp_term
  type atp_connective = ATP_Problem.atp_connective
  type ('a, 'b, 'c, 'd) atp_formula = ('a, 'b, 'c, 'd) ATP_Problem.atp_formula
  type atp_format = ATP_Problem.atp_format
  type atp_formula_role = ATP_Problem.atp_formula_role
  type 'a atp_problem = 'a ATP_Problem.atp_problem
  type ('a, 'b) atp_step = ('a,'b) ATP_Proof.atp_step

  val const_prefix : char
  val var_prefix : char
  val free_prefix : char
  val thm_prefix : string
  val hypothesis_prefix : string
  val thms_header : string
  val conjecture_condition_name : string
  val hypothesis_header : string
  val waldmeister_output_file_path : string

  val waldmeister_simp_header : string
  val waldmeister_simp_thms : thm list

  val thm_to_atps : bool -> thm -> (string * string, 'a) atp_term list
  val trm_to_atp : term -> (string * string, 'a) atp_term
  val atp_to_trm : (string, 'a) atp_term -> term
  val trm_to_atp_to_trm : term -> term
  val create_tptp_input : thm list -> term ->
    (string * ((string * string ATP_Problem.atp_problem_line list) list
      * (string Symtab.table * string Symtab.table) option)) option
  val run_waldmeister :
    string * (string ATP_Proof.atp_problem * (string Symtab.table * string Symtab.table) option)
    -> string ATP_Proof.atp_proof
  val atp_proof_step_to_term :
    ((string, string, (string, string) atp_term, string) atp_formula,string) atp_step
    -> (term,string) atp_step
  val fix_waldmeister_proof :
    ((string, string, (string, string) atp_term, string) atp_formula,string) atp_step list ->
    ((string, string, (string, string) atp_term, string) atp_formula,string) atp_step list
end;

structure ATP_Waldmeister : ATP_WALDMEISTER =
struct

open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct

type ('a, 'b) atp_term = ('a, 'b) ATP_Problem.atp_term
type atp_connective = ATP_Problem.atp_connective
type ('a, 'b, 'c, 'd) atp_formula = ('a, 'b, 'c, 'd) ATP_Problem.atp_formula
type atp_format = ATP_Problem.atp_format
type atp_formula_role = ATP_Problem.atp_formula_role
type 'a atp_problem = 'a ATP_Problem.atp_problem

val const_prefix = #"c"
val var_prefix = #"V"
val free_prefix = #"f"
val thm_prefix = "fact"
val hypothesis_prefix = "hypothesis"
val thms_header = "facts"
val conjecture_condition_name = "condition"
val hypothesis_header = "hypothesis"
val broken_waldmeister_formula_prefix = #"1"

val waldmeister_simp_header = "Waldmeister first order logic facts"
val waldmeister_simp_thms = @{thms waldmeister_fol}

val temp_files_dir = "/home/albert/waldmeister"
val input_file_name = "input.tptp"
val output_file_name = "output.tptp"
val waldmeister_input_file_path = temp_files_dir ^ "/" ^ input_file_name
val waldmeister_output_file_path = temp_files_dir ^ "/" ^ output_file_name
val script_path = "/opt/Isabelle/src/HOL/Tools/ATP/scripts/remote_atp -s Waldmeister---710 -t 30"

exception Failure
exception FailureMessage of string

(*
Some utilitary functions for translation.
*)

fun is_eq (Const (@{const_name "HOL.eq"}, _) $ _ $ _) = true
  | is_eq _ = false

fun is_eq_thm thm = thm |> Thm.prop_of |> Object_Logic.atomize_term @{theory } |> is_eq

fun gen_ascii_tuple str = (str, ascii_of str)

(*
Translation from Isabelle theorms and terms to ATP terms.
*)

fun trm_to_atp'' (Const (x, _)) args = [ATerm ((gen_ascii_tuple (String.str const_prefix ^ x), []), args)]
  | trm_to_atp'' (Free (x, _)) args = ATerm ((gen_ascii_tuple (String.str free_prefix ^ x), []), [])::args
  | trm_to_atp'' (Var ((x, _), _)) args = ATerm ((gen_ascii_tuple (String.str var_prefix ^ x), []), [])::args
  | trm_to_atp'' (trm1 $ trm2) args = trm_to_atp'' trm1 (trm_to_atp'' trm2 [] @ args)
  | trm_to_atp'' _ args = args

fun trm_to_atp' trm = trm_to_atp'' trm [] |> hd

fun eq_trm_to_atp (Const (@{const_name HOL.eq}, _) $ lhs $ rhs) =
  ATerm (((tptp_equal, tptp_equal), []), [trm_to_atp' lhs, trm_to_atp' rhs])
  | eq_trm_to_atp _ = raise Failure

fun trm_to_atp trm =
  if is_eq trm then
    eq_trm_to_atp trm
  else
    HOLogic.mk_eq (trm, @{term True}) |> eq_trm_to_atp

fun thm_to_atps split_conj thm =
  let
    val prop_term = Thm.prop_of thm |> Object_Logic.atomize_term @{theory}
  in
    if split_conj then
      map trm_to_atp (prop_term |> HOLogic.dest_conj)
    else
      [prop_term |> trm_to_atp]
  end

fun prepare_conjecture conj_term =
  let
    fun split_conj_trm (Const (@{const_name Pure.imp}, _)$ condition $ consequence) =
        (SOME condition, consequence)
      | split_conj_trm conj = (NONE, conj)
    val (condition, consequence) = split_conj_trm conj_term
  in
    (case condition of SOME x => HOLogic.dest_conj x |> map trm_to_atp | NONE => []
    , trm_to_atp consequence)
  end

(* Translation from ATP terms to Isabelle terms. *)

fun construct_term (ATerm ((name, _), _)) =
  let
    val prefix = String.sub (name, 0)
  in
    if prefix = const_prefix then
      Const (String.extract (name, 1, NONE), Type ("", []))
    else if prefix = free_prefix then
      Free (String.extract (name, 1, NONE), TFree ("", []))
    else if Char.isUpper prefix then
      Var ((name, 0), TVar (("", 0), []))
    else
      raise Failure
  end
  | construct_term _ = raise Failure

fun atp_to_trm' (ATerm (descr, args)) =
    (case args of
      [] => construct_term (ATerm (descr, args))
     | _ => Term.list_comb (construct_term (ATerm (descr, args)), map atp_to_trm' args))
     | atp_to_trm' _ = raise Failure

fun atp_to_trm  (ATerm (("equal", _), [lhs, rhs])) =
    Const (@{const_name HOL.eq}, Type ("", [])) $ atp_to_trm' lhs $ atp_to_trm' rhs
  | atp_to_trm (ATerm (("$true", _), _)) = Const ("HOL.True", Type ("", []))
  | atp_to_trm _ = raise Failure

fun formula_to_trm (AAtom aterm) = atp_to_trm aterm
  | formula_to_trm (AConn (ANot, [aterm])) =
    Const (@{const_name HOL.Not}, @{typ "bool \<Rightarrow> bool"}) $ formula_to_trm aterm
  | formula_to_trm _ = raise Failure

(* Simple testing function for translation *)

fun atp_only_readable_names (ATerm ((("=", _), ty), args)) =
    ATerm (("equal", ty), map atp_only_readable_names args)
  | atp_only_readable_names (ATerm (((descr, _), ty), args)) =
    ATerm ((descr, ty), map atp_only_readable_names args)
  | atp_only_readable_names _ = raise Failure

val trm_to_atp_to_trm = eq_trm_to_atp #> atp_only_readable_names #> atp_to_trm

(* Abstract translation from here on. *)

fun name_of_thm thm =
  Thm.get_tags thm
  |> List.find (fn (x, _) => x = "name")
  |> the |> snd

fun mk_formula prefix_name name atype aterm =
  Formula ((prefix_name ^ "_" ^ ascii_of name, name), atype, AAtom aterm, NONE, [])

fun thms_to_problem_lines [] = []
  | thms_to_problem_lines (t::thms) =
    (thm_to_atps false t |>
      map (mk_formula thm_prefix (name_of_thm t) Axiom)) @ thms_to_problem_lines thms

fun make_nice problem = nice_atp_problem true CNF problem

fun problem_to_string [] = ""
  | problem_to_string ((kind, lines)::problems) =
    "% " ^ kind ^ "\n"
    ^ String.concat (map (tptp_string_of_line CNF) lines)
    ^ "\n"
    ^ problem_to_string problems

fun mk_conjecture aterm =
  let
    val formula = mk_anot (AAtom aterm)
  in
    Formula (gen_ascii_tuple hypothesis_prefix, Hypothesis, formula, NONE, [])
  end

fun mk_condition_lines [] = []
  | mk_condition_lines (term::terms) =
    mk_formula thm_prefix conjecture_condition_name Axiom term::mk_condition_lines terms

fun create_tptp_input thms conj_t =
    let
      val (conditions, consequence) = prepare_conjecture conj_t
      val thms_lines = thms_to_problem_lines thms
      val condition_lines = mk_condition_lines conditions
      val axiom_lines = thms_lines @ condition_lines
      val conj_line = consequence |> mk_conjecture
      val waldmeister_simp_lines =
        if List.exists (fn x => not (is_eq_thm x)) thms orelse not (is_eq conj_t) then
          [(waldmeister_simp_header, thms_to_problem_lines waldmeister_simp_thms)]
        else
          []
      val problem =
        waldmeister_simp_lines @ [(thms_header, axiom_lines), (hypothesis_header, [conj_line])]
      val (problem_nice, symtabs) = make_nice problem
    in
      SOME (problem_to_string problem_nice, (problem_nice, symtabs))
    end

val waldmeister_proof_delims =
  [("% SZS output start CNFRefutation", "% SZS output end CNFRefutation")]
val known_waldmeister_failures = [(OutOfResources, "Too many function symbols"),
     (Inappropriate, "****  Unexpected end of file."),
     (Crashed, "Unrecoverable Segmentation Fault")]

fun extract_proof_part output =
  case
    extract_tstplike_proof_and_outcome true
      waldmeister_proof_delims known_waldmeister_failures output of
    (x, NONE) => x | (_, SOME y) => raise FailureMessage (string_of_atp_failure y)

fun cleanup () =
  (OS.Process.system ("rm " ^ waldmeister_input_file_path);
   OS.Process.system ("rm " ^ waldmeister_output_file_path))

fun run_script input =
  let
    val outputFile = TextIO.openOut waldmeister_input_file_path
  in
    (TextIO.output (outputFile, input);
    TextIO.flushOut outputFile;
    TextIO.closeOut outputFile;
    OS.Process.system (script_path ^ " " ^ waldmeister_input_file_path ^ " > " ^
      waldmeister_output_file_path))
  end

fun read_result () =
  let
    val inputFile = TextIO.openIn waldmeister_output_file_path
    fun readAllLines is =
      if TextIO.endOfStream is then (TextIO.closeIn is; [])
      else (TextIO.inputLine is |> the) :: readAllLines is
  in
    readAllLines inputFile |> String.concat
  end

fun run_waldmeister (input, (problem, SOME (_, nice_to_nasty_table))) =
    (cleanup ();
     run_script input;
     read_result ()
     |> extract_proof_part
     |> atp_proof_of_tstplike_proof waldmeister_newN problem
     |> nasty_atp_proof nice_to_nasty_table)
  | run_waldmeister _ = raise Failure

fun atp_proof_step_to_term (name, role, formula, formula_name, step_names) =
  (name, role, formula_to_trm formula, formula_name, step_names)

fun fix_waldmeister_proof [] = []
  | fix_waldmeister_proof (((name, extra_names), role, formula, formula_name, step_names)::steps) =
    if String.sub (name, 0) = broken_waldmeister_formula_prefix then
      ((name, extra_names), role, mk_anot formula, formula_name, step_names)::fix_waldmeister_proof steps
    else
      ((name, extra_names), role, formula, formula_name, step_names)::fix_waldmeister_proof steps

end;
