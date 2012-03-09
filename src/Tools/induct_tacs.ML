(*  Title:      Tools/induct_tacs.ML
    Author:     Makarius

Unstructured induction and cases analysis.
*)

signature INDUCT_TACS =
sig
  val case_tac: Proof.context -> string -> int -> tactic
  val case_rule_tac: Proof.context -> string -> thm -> int -> tactic
  val induct_tac: Proof.context -> string option list list -> int -> tactic
  val induct_rules_tac: Proof.context -> string option list list -> thm list -> int -> tactic
  val setup: theory -> theory
end

structure Induct_Tacs: INDUCT_TACS =
struct

(* case analysis *)

fun check_type ctxt (t, pos) =
  let
    val u = singleton (Variable.polymorphic ctxt) t;
    val U = Term.fastype_of u;
    val _ = Term.is_TVar U andalso
      error ("Cannot determine type of " ^ Syntax.string_of_term ctxt u ^ Position.str_of pos);
  in (u, U) end;

fun gen_case_tac ctxt0 s opt_rule i st =
  let
    val (_, ctxt) = Variable.focus_subgoal i st ctxt0;
    val rule =
      (case opt_rule of
        SOME rule => rule
      | NONE =>
          (case Induct.find_casesT ctxt
              (#2 (check_type ctxt (Proof_Context.read_term_schematic ctxt s,
                Syntax.read_token_pos s))) of
            rule :: _ => rule
          | [] => @{thm case_split}));
    val _ = Method.trace ctxt [rule];

    val xi =
      (case Induct.vars_of (Thm.term_of (Thm.cprem_of rule 1)) of
        Var (xi, _) :: _ => xi
      | _ => raise THM ("Malformed cases rule", 0, [rule]));
  in res_inst_tac ctxt [(xi, s)] rule i st end
  handle THM _ => Seq.empty;

fun case_tac ctxt s = gen_case_tac ctxt s NONE;
fun case_rule_tac ctxt s rule = gen_case_tac ctxt s (SOME rule);


(* induction *)

local

fun prep_var (Var (ixn, _), SOME x) = SOME (ixn, x)
  | prep_var _ = NONE;

fun prep_inst (concl, xs) =
  let val vs = Induct.vars_of concl
  in map_filter prep_var (drop (length vs - length xs) vs ~~ xs) end;

in

fun gen_induct_tac ctxt0 varss opt_rules i st =
  let
    val ((_, goal), ctxt) = Variable.focus_subgoal i st ctxt0;
    val (prems, concl) = Logic.strip_horn (Thm.term_of goal);

    fun induct_var name =
      let
        val t = Syntax.read_term ctxt name;
        val pos = Syntax.read_token_pos name;
        val (x, _) = Term.dest_Free t handle TERM _ =>
          error ("Induction argument not a variable: " ^
            Syntax.string_of_term ctxt t ^ Position.str_of pos);
        val eq_x = fn Free (y, _) => x = y | _ => false;
        val _ =
          if Term.exists_subterm eq_x concl then ()
          else
            error ("No such variable in subgoal: " ^
              Syntax.string_of_term ctxt t ^ Position.str_of pos);
        val _ =
          if (exists o Term.exists_subterm) eq_x prems then
            warning ("Induction variable occurs also among premises: " ^
              Syntax.string_of_term ctxt t ^ Position.str_of pos)
          else ();
      in #1 (check_type ctxt (t, pos)) end;

    val argss = map (map (Option.map induct_var)) varss;
    val rule =
      (case opt_rules of
        SOME rules => #2 (Rule_Cases.strict_mutual_rule ctxt rules)
      | NONE =>
          (case map_filter (Rule_Cases.mutual_rule ctxt) (Induct.get_inductT ctxt argss) of
            (_, rule) :: _ => rule
          | [] => raise THM ("No induction rules", 0, [])));

    val rule' = rule |> Conv.fconv_rule (Conv.concl_conv ~1 Object_Logic.atomize);
    val _ = Method.trace ctxt [rule'];

    val concls = Logic.dest_conjunctions (Thm.concl_of rule);
    val insts = maps prep_inst (concls ~~ varss) handle ListPair.UnequalLengths =>
      error "Induction rule has different numbers of variables";
  in res_inst_tac ctxt insts rule' i st end
  handle THM _ => Seq.empty;

end;

fun induct_tac ctxt args = gen_induct_tac ctxt args NONE;
fun induct_rules_tac ctxt args rules = gen_induct_tac ctxt args (SOME rules);


(* method syntax *)

local

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.$$$ ":");
val opt_rule = Scan.option (rule_spec |-- Attrib.thm);
val opt_rules = Scan.option (rule_spec |-- Attrib.thms);

val varss =
  Parse.and_list' (Scan.repeat (Scan.unless rule_spec (Scan.lift (Args.maybe Args.name_source))));

in

val setup =
  Method.setup @{binding case_tac}
    (Args.goal_spec -- Scan.lift Args.name_source -- opt_rule >>
      (fn ((quant, s), r) => fn ctxt => SIMPLE_METHOD'' quant (gen_case_tac ctxt s r)))
    "unstructured case analysis on types" #>
  Method.setup @{binding induct_tac}
    (Args.goal_spec -- varss -- opt_rules >>
      (fn ((quant, vs), rs) => fn ctxt => SIMPLE_METHOD'' quant (gen_induct_tac ctxt vs rs)))
    "unstructured induction on types";

end;

end;

