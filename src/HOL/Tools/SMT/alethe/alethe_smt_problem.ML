(*  Title:      HOL/Tools/SMT/alethe/alethe_smt_problem.ML
    Author:     Mathias Fleury, University of Freiburg
    Author:     Hanna Lachnitt, Stanford University

Parsing smt problems into alethe nodes

For practical reasons using raw_alethe_node but not solver dependent.
*)

open Alethe_Node

signature ALETHE_SMT_PROBLEM =
sig
  exception ALETHE_PROBLEM_PARSE of string

  val parse_raw_problem_steps: SMTLIB.tree list -> SMTLIB_Proof.name_bindings ->
     int -> raw_alethe_node list * SMTLIB.tree list * SMTLIB_Proof.name_bindings
end;

structure Alethe_SMT_Problem: ALETHE_SMT_PROBLEM =
struct

exception ALETHE_PROBLEM_PARSE of string

open SMTLIB_Proof
open Alethe_Node

datatype command_kind = ASSERT | FUN_DEF | FUN_DECL

fun parse_raw_problem_steps (commands : SMTLIB.tree list) (cx : name_bindings) (assms_nbr : int):
     (raw_alethe_node list * SMTLIB.tree list * name_bindings) =
  let
    fun command_kind "assert" = ASSERT
      | command_kind "define-fun" = FUN_DEF
      | command_kind "declare-fun" = FUN_DECL
      | command_kind kind = raise ALETHE_PROBLEM_PARSE ("kind of command unrec: " ^ @{make_string} kind)

    fun split_commands [] = NONE
      | split_commands ((step as SMTLIB.S (SMTLIB.Sym kind :: _)) :: remaining_steps) =
          SOME (command_kind kind, step, remaining_steps)
      | split_commands steps = raise ALETHE_PROBLEM_PARSE ("malformed command: " ^ @{make_string} steps)

    fun parse_fun_decl (SMTLIB.S [SMTLIB.Sym "declare-fun", SMTLIB.Sym id, typ, def]) cx =
         (*replace the name binding by the constant instead of the full term in order to reduce
           the size of the generated terms and therefore the reconstruction time*)
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) def cx
         in
           (mk_raw_node (id ^ Alethe_Proof.skolem_def) Alethe_Proof.skolem_def [(SMTLIB.S [SMTLIB.Sym id, typ, l])] [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, def]) [] (SMTLIB.S []), cx)
         end |
       parse_fun_decl _ _ = raise ALETHE_PROBLEM_PARSE ("malformed func_decl")

  in
    case split_commands commands of
     SOME (ASSERT, p, l) =>
          let
            val (id, term) = (case p of
                SMTLIB.S [SMTLIB.Sym "assert", SMTLIB.S [SMTLIB.Sym "!", term, SMTLIB.Key "named", SMTLIB.Sym id]] => (id, term)
              | SMTLIB.S [SMTLIB.Sym "assert", term] => (Int.toString assms_nbr, term)
              | xs => (@{print}("xs",xs);raise ERROR "unknown SMTLIB command"))
            val ((t, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings term cx
            val s = mk_raw_node id Alethe_Proof.input_rule [] [] [] t [] (SMTLIB.S [])
            val (rp, rl, cx) = parse_raw_problem_steps l cx (assms_nbr + 1)
       in (s :: rp, rl, cx) end
      | SOME (FUN_DEF, p, l) =>
          let
            val (s, cx) = Alethe_Proof.parse_fun_def p cx
            val (rp, rl, cx) = parse_raw_problem_steps l cx assms_nbr
          in (s :: rp, rl, cx) end
      | SOME (FUN_DECL, p, l) =>
          let
            val (s, cx) = parse_fun_decl p cx
            val (rp, rl, cx) = parse_raw_problem_steps l cx assms_nbr
          in (s :: rp, rl, cx) end
      | NONE => ([],[], cx)

  end
end;