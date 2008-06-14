(*  Title:      HOL/Tools/induct_tacs.ML
    ID:         $Id$
    Author:     Makarius

Unstructured induction and cases analysis for Isabelle/HOL.
*)

signature INDUCT_TACS =
sig
  val case_tac: Proof.context -> string -> int -> tactic
  val case_rule_tac: Proof.context -> string -> thm -> int -> tactic
  val induct_tac: Proof.context -> string option list list -> int -> tactic
  val induct_rule_tac: Proof.context -> string option list list -> thm -> int -> tactic
  val setup: theory -> theory
end

structure InductTacs: INDUCT_TACS =
struct

(* case analysis *)

fun check_type ctxt t =
  let
    val u = singleton (Variable.polymorphic ctxt) t;
    val U = Term.fastype_of u;
    val _ = Term.is_TVar U andalso
      error ("Cannot determine type of " ^ Syntax.string_of_term ctxt u);
  in U end;

fun gen_case_tac ctxt0 (s, opt_rule) i st =
  let
    val ((_, goal), ctxt) = Variable.focus_subgoal i st ctxt0;
    val rule =
      (case opt_rule of
        SOME rule => rule
      | NONE =>
          (case Induct.find_casesT ctxt
              (check_type ctxt (ProofContext.read_term_schematic ctxt s)) of
            rule :: _ => rule
          | [] => @{thm case_split}));
    val _ = Method.trace ctxt [rule];

    val xi =
      (case Induct.vars_of (Thm.term_of (Thm.cprem_of rule 1)) of
        Var (xi, _) :: _ => xi
      | _ => raise THM ("Malformed cases rule", 0, [rule]));
  in RuleInsts.res_inst_tac ctxt [(xi, s)] rule i st end
  handle THM _ => Seq.empty;

fun case_tac ctxt s = gen_case_tac ctxt (s, NONE);
fun case_rule_tac ctxt s rule = gen_case_tac ctxt (s, SOME rule);


(* induction *)

local

fun prep_var (Var (ixn, _), SOME x) = SOME (ixn, x)
  | prep_var _ = NONE;

fun prep_inst (concl, xs) =
  let val vs = Induct.vars_of concl
  in map_filter prep_var (Library.drop (length vs - length xs, vs) ~~ xs) end;

in

fun gen_induct_tac ctxt0 (varss, opt_rule) i st =
  let
    val ((_, goal), ctxt) = Variable.focus_subgoal i st ctxt0;
    val (prems, concl) = Logic.strip_horn (Thm.term_of goal);

    fun induct_var name =
      let
        val t = Syntax.read_term ctxt name;
        val (x, _) = Term.dest_Free t handle TERM _ =>
          error ("Induction argument not a variable: " ^ Syntax.string_of_term ctxt t);
        val eq_x = fn Free (y, _) => x = y | _ => false;
        val _ =
          if Term.exists_subterm eq_x concl then ()
          else error ("No such variable in subgoal: " ^ Syntax.string_of_term ctxt t);
        val _ =
          if (exists o Term.exists_subterm) eq_x prems then
            warning ("Induction variable occurs also among premises: " ^ Syntax.string_of_term ctxt t)
          else ();
      in check_type ctxt t end;

    val var_types = map_filter (Option.map induct_var) (flat varss);
    val rule =
      (case opt_rule of
        SOME rule => rule
      | NONE =>
          (case var_types of
            T :: _ =>
              (case filter_out PureThy.is_internal (Induct.find_inductT ctxt T) of
                rule :: _ => rule
              | [] => raise THM ("No induction rules", 0, []))
          | _ => raise THM ("No induction arguments", 0, [])));
    val _ = Method.trace ctxt [rule];

    val concls = HOLogic.dest_concls (Thm.concl_of rule);
    val insts = maps prep_inst (concls ~~ varss) handle Library.UnequalLengths =>
      error "Induction rule has different numbers of variables";
  in RuleInsts.res_inst_tac ctxt insts rule i st end
  handle THM _ => Seq.empty;

end;

fun induct_tac ctxt args = gen_induct_tac ctxt (args, NONE);
fun induct_rule_tac ctxt args rule = gen_induct_tac ctxt (args, SOME rule);


(* method syntax *)

local

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.$$$ ":");
val opt_rule = Scan.option (rule_spec |-- Attrib.thm);

val varss =
  Args.and_list (Scan.repeat (Scan.unless rule_spec (Scan.lift (Args.maybe Args.name))));

in

val setup =
  Method.add_methods
   [("case_tac", Method.goal_args_ctxt' (Scan.lift Args.name -- opt_rule) gen_case_tac,
      "unstructured case analysis on types"),
    ("induct_tac", Method.goal_args_ctxt' (varss -- opt_rule) gen_induct_tac,
      "unstructured induction on types")];

end;

end;

