(*  Title:      HOL/Tools/SMT/alethe/alethe_node.ML
    Author:     Mathias Fleury, University of Freiburg
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

Alethe: abstract syntax tree utils.
*)

signature ALETHE_NODE =
sig

  datatype alethe_step = Alethe_Step of {
    id: string,
    rule: string,
    prems: string list,
    prop_skeleton: term,
    concl: term}

  val mk_step : string -> string -> string list -> term -> term -> alethe_step

  (* Pass information added during pre-processing to reconstruction *)
  datatype tactic_args =
    Insts of term Symtab.table | (*only used for forall_inst*)
    Sko_Def_Prems of string list * string list | (*only used for sko_forall and sko_exists*)
    Solver_Name of string | (*used for refl and cong*)
    Index of int | (*used for and, not_or, and_pos and or_neg*)
    CommOp of term | (*only used for shuffle*)
    Farkas_Coefficients of (int * int) list

  val transform_tactic_args : (term -> term) -> tactic_args option -> tactic_args option

  datatype alethe_replay_node = Alethe_Replay_Node of {
    id: string,
    rule: string,
    step_args: term list,
    context_assignments: term list,
    prems: string list,
    prop_skeleton: term,
    concl: term,
    subproof: (string * typ) list * term list * term list * alethe_replay_node list,
    args: tactic_args option}
  | Alethe_Definition_Node of {
    id: string,
    rule: string,
    skolem_name : string,
    skolem_term : term}

  val mk_replay_node: string -> string -> term list -> term list -> string list -> term ->
    (string * typ) list * term list * term list * alethe_replay_node list -> tactic_args option ->
    term -> alethe_replay_node

  datatype raw_alethe_node = Raw_Alethe_Node of {
    id: string,
    rule: string,
    step_args: SMTLIB.tree list,
    context_assignments: SMTLIB.tree list,
    prems: string list,
    concl: SMTLIB.tree,
    prop_skeleton: SMTLIB.tree,
    subproof: raw_alethe_node list}
  | Raw_Definition_Node of {
    id: string,
    rule: string,
    skolem_name : string,
    skolem_term : SMTLIB.tree}

  val mk_raw_node : string -> string -> SMTLIB.tree list -> SMTLIB.tree list -> string list ->
    SMTLIB.tree -> raw_alethe_node list -> SMTLIB.tree -> raw_alethe_node

  val mk_raw_definition_node : string -> string -> string -> SMTLIB.tree -> raw_alethe_node

end;

structure Alethe_Node: ALETHE_NODE =
struct

datatype raw_alethe_node = Raw_Alethe_Node of {
  id: string,
  rule: string,
  step_args: SMTLIB.tree list,
  context_assignments: SMTLIB.tree list,
  prems: string list,
  concl: SMTLIB.tree,
  prop_skeleton: SMTLIB.tree,
  subproof: raw_alethe_node list}
| Raw_Definition_Node of {
  id: string,
  rule: string,
  skolem_name : string,
  skolem_term : SMTLIB.tree}

fun mk_raw_node id rule step_args context_ass prems concl subproof prop_skeleton =
  Raw_Alethe_Node {id = id, rule = rule, step_args = step_args,
    context_assignments = context_ass, prems = prems,
    concl = concl, subproof = subproof, prop_skeleton = prop_skeleton}

fun mk_raw_definition_node id rule skolem_name skolem_term =
  Raw_Definition_Node {id = id, rule = rule, skolem_name = skolem_name, skolem_term = skolem_term}

datatype tactic_args =
  Insts of term Symtab.table | (*only used for forall_inst*)
  Sko_Def_Prems of string list * string list | (*only used for sko_forall and sko_exists*)
  Solver_Name of string | (*used for refl and cong*)
  Index of int | (*used for and, not_or, and_pos and or_neg*)
  CommOp of term | (*only used for shuffle*)
  Farkas_Coefficients of (int * int) list

fun transform_tactic_args _ NONE = NONE
  | transform_tactic_args f (SOME (Insts insts)) = SOME (Insts (Symtab.map (K f) insts))
  | transform_tactic_args _ x = x

datatype alethe_replay_node = Alethe_Replay_Node of {
  id: string,
  rule: string,
  step_args: term list,
  context_assignments: term list,
  prems: string list,
  prop_skeleton: term,
  concl: term,
  subproof: (string * typ) list * term list * term list * alethe_replay_node list,
  args: tactic_args option}
| Alethe_Definition_Node of {
  id: string,
  rule: string,
  skolem_name : string,
  skolem_term : term}

datatype alethe_step = Alethe_Step of {
  id: string,
  rule: string,
  prems: string list,
  prop_skeleton : term,
  concl: term}

fun mk_step id rule prems concl prop_skeleton =
  Alethe_Step {id = id, rule = rule, prems = prems, concl = concl,
    prop_skeleton = prop_skeleton}

fun mk_replay_node id rule step_args context_ass prems concl subproof tactic_args prop_skeleton =
  Alethe_Replay_Node {id = id, rule = rule, step_args = step_args,
    context_assignments = context_ass, prems = prems, concl = concl, subproof = subproof,
    args = tactic_args, prop_skeleton = prop_skeleton}

end;