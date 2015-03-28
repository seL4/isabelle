(*  Title:      Tools/induct_tacs.ML
    Author:     Makarius

Unstructured induction and cases analysis.
*)

signature INDUCT_TACS =
sig
  val case_tac: Proof.context -> string -> (binding * string option * mixfix) list ->
    thm option -> int -> tactic
  val induct_tac: Proof.context -> string option list list ->
    thm list option -> int -> tactic
end

structure Induct_Tacs: INDUCT_TACS =
struct

(* case analysis *)

fun check_type ctxt (t, pos) =
  let
    val u = singleton (Variable.polymorphic ctxt) t;
    val U = Term.fastype_of u;
    val _ = Term.is_TVar U andalso
      error ("Cannot determine type of " ^
        quote (Syntax.string_of_term ctxt u) ^ Position.here pos);
  in (u, U) end;

fun case_tac ctxt s fixes opt_rule = SUBGOAL (fn (goal, i) =>
  let
    val rule =
      (case opt_rule of
        SOME rule => rule
      | NONE =>
          let
            val (t, ctxt') = ctxt
              |> Rule_Insts.goal_context goal |> #2
              |> Context_Position.set_visible false
              |> Rule_Insts.read_term s;
            val pos = Syntax.read_input_pos s;
          in
            (case Induct.find_casesT ctxt' (#2 (check_type ctxt' (t, pos))) of
              rule :: _ => rule
            | [] => @{thm case_split})
          end);
    val _ = Method.trace ctxt [rule];
  in
    (case Induct.vars_of (Thm.term_of (Thm.cprem_of rule 1)) handle THM _ => [] of
      Var (xi, _) :: _ => Rule_Insts.res_inst_tac ctxt [((xi, Position.none), s)] fixes rule i
    | _ => no_tac)
  end);


(* induction *)

local

fun prep_var (Var (xi, _), SOME x) = SOME ((xi, Position.none), x)
  | prep_var _ = NONE;

fun prep_inst (concl, xs) =
  let val vs = Induct.vars_of concl
  in map_filter prep_var (drop (length vs - length xs) vs ~~ xs) end;

in

fun induct_tac ctxt varss opt_rules i st =
  let
    val goal = Thm.cprem_of st i;
    val (_, goal_ctxt) = Rule_Insts.goal_context (Thm.term_of goal) ctxt
    and ((_, goal'), _) = Variable.focus_cterm goal ctxt;
    val (prems, concl) = Logic.strip_horn (Thm.term_of goal');

    fun induct_var name =
      let
        val t = Syntax.read_term goal_ctxt name;
        val pos = Syntax.read_input_pos name;
        val (x, _) = Term.dest_Free t handle TERM _ =>
          error ("Induction argument not a variable: " ^
            quote (Syntax.string_of_term goal_ctxt t) ^ Position.here pos);
        val eq_x = fn Free (y, _) => x = y | _ => false;
        val _ =
          if Term.exists_subterm eq_x concl then ()
          else
            error ("No such variable in subgoal: " ^
              quote (Syntax.string_of_term goal_ctxt t) ^ Position.here pos);
        val _ =
          if (exists o Term.exists_subterm) eq_x prems then
            warning ("Induction variable occurs also among premises: " ^
              quote (Syntax.string_of_term goal_ctxt t) ^ Position.here pos)
          else ();
      in #1 (check_type goal_ctxt (t, pos)) end;

    val argss = (map o map o Option.map) induct_var varss;
    val rule =
      (case opt_rules of
        SOME rules => #2 (Rule_Cases.strict_mutual_rule ctxt rules)
      | NONE =>
          (case map_filter (Rule_Cases.mutual_rule ctxt) (Induct.get_inductT ctxt argss) of
            (_, rule) :: _ => rule
          | [] => raise THM ("No induction rules", 0, [])));

    val rule' = rule |> Conv.fconv_rule (Conv.concl_conv ~1 (Object_Logic.atomize ctxt));
    val _ = Method.trace ctxt [rule'];

    val concls = Logic.dest_conjunctions (Thm.concl_of rule);
    val insts = maps prep_inst (concls ~~ varss) handle ListPair.UnequalLengths =>
      error "Induction rule has different numbers of variables";
  in Rule_Insts.res_inst_tac ctxt insts [] rule' i st end
  handle THM _ => Seq.empty;

end;


(* method syntax *)

local

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.$$$ ":");
val opt_rule = Scan.option (rule_spec |-- Attrib.thm);
val opt_rules = Scan.option (rule_spec |-- Attrib.thms);

val varss =
  Parse.and_list'
    (Scan.repeat (Scan.unless rule_spec (Scan.lift (Args.maybe Args.name_inner_syntax))));

in

val _ =
  Theory.setup
   (Method.setup @{binding case_tac}
      (Args.goal_spec -- Scan.lift (Args.name_inner_syntax -- Parse.for_fixes) -- opt_rule >>
        (fn ((quant, (s, xs)), r) => fn ctxt => SIMPLE_METHOD'' quant (case_tac ctxt s xs r)))
      "unstructured case analysis on types" #>
    Method.setup @{binding induct_tac}
      (Args.goal_spec -- varss -- opt_rules >>
        (fn ((quant, vs), rs) => fn ctxt => SIMPLE_METHOD'' quant (induct_tac ctxt vs rs)))
      "unstructured induction on types");

end;

end;
