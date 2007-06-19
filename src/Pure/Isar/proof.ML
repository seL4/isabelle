(*  Title:      Pure/Isar/proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isar/VM proof language interpreter: maintains a structured flow of
context elements, goals, refinements, and facts.
*)

signature PROOF =
sig
  type context (*= Context.proof*)
  type method (*= Method.method*)
  type state
  val init: context -> state
  val level: state -> int
  val assert_bottom: bool -> state -> state
  val context_of: state -> context
  val theory_of: state -> theory
  val map_context: (context -> context) -> state -> state
  val add_binds_i: (indexname * term option) list -> state -> state
  val put_thms: string * thm list option -> state -> state
  val the_facts: state -> thm list
  val the_fact: state -> thm
  val put_facts: thm list option -> state -> state
  val assert_forward: state -> state
  val assert_chain: state -> state
  val assert_forward_or_chain: state -> state
  val assert_backward: state -> state
  val assert_no_chain: state -> state
  val enter_forward: state -> state
  val get_goal: state -> context * (thm list * thm)
  val schematic_goal: state -> bool
  val show_main_goal: bool ref
  val verbose: bool ref
  val pretty_state: int -> state -> Pretty.T list
  val pretty_goals: bool -> state -> Pretty.T list
  val refine: Method.text -> state -> state Seq.seq
  val refine_end: Method.text -> state -> state Seq.seq
  val refine_insert: thm list -> state -> state
  val goal_tac: thm -> int -> tactic
  val refine_goals: (context -> thm -> unit) -> context -> thm list -> state -> state Seq.seq
  val match_bind: (string list * string) list -> state -> state
  val match_bind_i: (term list * term) list -> state -> state
  val let_bind: (string list * string) list -> state -> state
  val let_bind_i: (term list * term) list -> state -> state
  val fix: (string * string option * mixfix) list -> state -> state
  val fix_i: (string * typ option * mixfix) list -> state -> state
  val assm: Assumption.export ->
    ((string * Attrib.src list) * (string * string list) list) list -> state -> state
  val assm_i: Assumption.export ->
    ((string * attribute list) * (term * term list) list) list -> state -> state
  val assume: ((string * Attrib.src list) * (string * string list) list) list -> state -> state
  val assume_i: ((string * attribute list) * (term * term list) list) list -> state -> state
  val presume: ((string * Attrib.src list) * (string * string list) list) list -> state -> state
  val presume_i: ((string * attribute list) * (term * term list) list) list -> state -> state
  val def: ((string * Attrib.src list) *
    ((string * mixfix) * (string * string list))) list -> state -> state
  val def_i: ((string * attribute list) *
    ((string * mixfix) * (term * term list))) list -> state -> state
  val chain: state -> state
  val chain_facts: thm list -> state -> state
  val get_thmss: state -> (thmref * Attrib.src list) list -> thm list
  val note_thmss: ((string * Attrib.src list) *
    (thmref * Attrib.src list) list) list -> state -> state
  val note_thmss_i: ((string * attribute list) *
    (thm list * attribute list) list) list -> state -> state
  val from_thmss: ((thmref * Attrib.src list) list) list -> state -> state
  val from_thmss_i: ((thm list * attribute list) list) list -> state -> state
  val with_thmss: ((thmref * Attrib.src list) list) list -> state -> state
  val with_thmss_i: ((thm list * attribute list) list) list -> state -> state
  val using: ((thmref * Attrib.src list) list) list -> state -> state
  val using_i: ((thm list * attribute list) list) list -> state -> state
  val unfolding: ((thmref * Attrib.src list) list) list -> state -> state
  val unfolding_i: ((thm list * attribute list) list) list -> state -> state
  val invoke_case: string * string option list * Attrib.src list -> state -> state
  val invoke_case_i: string * string option list * attribute list -> state -> state
  val begin_block: state -> state
  val next_block: state -> state
  val end_block: state -> state
  val proof: Method.text option -> state -> state Seq.seq
  val defer: int option -> state -> state Seq.seq
  val prefer: int -> state -> state Seq.seq
  val apply: Method.text -> state -> state Seq.seq
  val apply_end: Method.text -> state -> state Seq.seq
  val local_goal: (context -> ((string * string) * (string * thm list) list) -> unit) ->
    (theory -> 'a -> attribute) ->
    (context * 'b list -> context * (term list list * (context -> context))) ->
    string -> Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * 'a list) * 'b) list -> state -> state
  val local_qed: Method.text option * bool -> state -> state Seq.seq
  val theorem: Method.text option -> (thm list list -> context -> context) ->
    (string * string list) list list -> context -> state
  val theorem_i: Method.text option -> (thm list list -> context -> context) ->
    (term * term list) list list -> context -> state
  val global_qed: Method.text option * bool -> state -> context
  val local_terminal_proof: Method.text * Method.text option -> state -> state Seq.seq
  val local_default_proof: state -> state Seq.seq
  val local_immediate_proof: state -> state Seq.seq
  val local_done_proof: state -> state Seq.seq
  val local_skip_proof: bool -> state -> state Seq.seq
  val global_terminal_proof: Method.text * Method.text option -> state -> context
  val global_default_proof: state -> context
  val global_immediate_proof: state -> context
  val global_done_proof: state -> context
  val global_skip_proof: bool -> state -> context
  val have: Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * Attrib.src list) * (string * string list) list) list -> bool -> state -> state
  val have_i: Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * attribute list) * (term * term list) list) list -> bool -> state -> state
  val show: Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * Attrib.src list) * (string * string list) list) list -> bool -> state -> state
  val show_i: Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * attribute list) * (term * term list) list) list -> bool -> state -> state
end;

structure Proof: PROOF =
struct

type context = Context.proof;
type method = Method.method;


(** proof state **)

(* datatype state *)

datatype mode = Forward | Chain | Backward;

datatype state =
  State of node Stack.T
and node =
  Node of
   {context: context,
    facts: thm list option,
    mode: mode,
    goal: goal option}
and goal =
  Goal of
   {statement: string * term list list,     (*goal kind and statement, starting with vars*)
    using: thm list,                        (*goal facts*)
    goal: thm,                              (*subgoals ==> statement*)
    before_qed: Method.text option,
    after_qed:
      (thm list list -> state -> state Seq.seq) *
      (thm list list -> context -> context)};

fun make_goal (statement, using, goal, before_qed, after_qed) =
  Goal {statement = statement, using = using, goal = goal,
    before_qed = before_qed, after_qed = after_qed};

fun make_node (context, facts, mode, goal) =
  Node {context = context, facts = facts, mode = mode, goal = goal};

fun map_node f (Node {context, facts, mode, goal}) =
  make_node (f (context, facts, mode, goal));

val init_context =
  ProofContext.set_stmt true #> ProofContext.reset_naming;

fun init ctxt =
  State (Stack.init (make_node (init_context ctxt, NONE, Forward, NONE)));

fun current (State st) = Stack.top st |> (fn Node node => node);
fun map_current f (State st) = State (Stack.map_top (map_node f) st);



(** basic proof state operations **)

(* block structure *)

fun open_block (State st) = State (Stack.push st);

fun close_block (State st) = State (Stack.pop st)
  handle Empty => error "Unbalanced block parentheses";

fun level (State st) = Stack.level st;

fun assert_bottom b state =
  let val b' = (level state <= 2) in
    if b andalso not b' then error "Not at bottom of proof!"
    else if not b andalso b' then error "Already at bottom of proof!"
    else state
  end;


(* context *)

val context_of = #context o current;
val theory_of = ProofContext.theory_of o context_of;

fun map_context f =
  map_current (fn (ctxt, facts, mode, goal) => (f ctxt, facts, mode, goal));

fun map_context_result f state =
  f (context_of state) ||> (fn ctxt => map_context (K ctxt) state);

val add_binds_i = map_context o ProofContext.add_binds_i;
val put_thms = map_context o ProofContext.put_thms;


(* facts *)

val get_facts = #facts o current;

fun the_facts state =
  (case get_facts state of SOME facts => facts
  | NONE => error "No current facts available");

fun the_fact state =
  (case the_facts state of [thm] => thm
  | _ => error "Single theorem expected");

fun put_facts facts =
  map_current (fn (ctxt, _, mode, goal) => (ctxt, facts, mode, goal)) #>
  put_thms (AutoBind.thisN, facts);

fun these_factss more_facts (named_factss, state) =
  (named_factss, state |> put_facts (SOME (maps snd named_factss @ more_facts)));

fun export_facts inner outer =
  (case get_facts inner of
    NONE => put_facts NONE outer
  | SOME thms =>
      thms
      |> ProofContext.export (context_of inner) (context_of outer)
      |> (fn ths => put_facts (SOME ths) outer));


(* mode *)

val get_mode = #mode o current;
fun put_mode mode = map_current (fn (ctxt, facts, _, goal) => (ctxt, facts, mode, goal));

val mode_name = (fn Forward => "state" | Chain => "chain" | Backward => "prove");

fun assert_mode pred state =
  let val mode = get_mode state in
    if pred mode then state
    else error ("Illegal application of proof command in " ^ quote (mode_name mode) ^ " mode")
  end;

val assert_forward = assert_mode (fn mode => mode = Forward);
val assert_chain = assert_mode (fn mode => mode = Chain);
val assert_forward_or_chain = assert_mode (fn mode => mode = Forward orelse mode = Chain);
val assert_backward = assert_mode (fn mode => mode = Backward);
val assert_no_chain = assert_mode (fn mode => mode <> Chain);

val enter_forward = put_mode Forward;
val enter_chain = put_mode Chain;
val enter_backward = put_mode Backward;


(* current goal *)

fun current_goal state =
  (case current state of
    {context, goal = SOME (Goal goal), ...} => (context, goal)
  | _ => error "No current goal!");

fun assert_current_goal g state =
  let val g' = can current_goal state in
    if g andalso not g' then error "No goal in this block!"
    else if not g andalso g' then error "Goal present in this block!"
    else state
  end;

fun put_goal goal = map_current (fn (ctxt, using, mode, _) => (ctxt, using, mode, goal));

val before_qed = #before_qed o #2 o current_goal;


(* nested goal *)

fun map_goal f g (State (Node {context, facts, mode, goal = SOME goal}, nodes)) =
      let
        val Goal {statement, using, goal, before_qed, after_qed} = goal;
        val goal' = make_goal (g (statement, using, goal, before_qed, after_qed));
      in State (make_node (f context, facts, mode, SOME goal'), nodes) end
  | map_goal f g (State (nd, node :: nodes)) =
      let val State (node', nodes') = map_goal f g (State (node, nodes))
      in map_context f (State (nd, node' :: nodes')) end
  | map_goal _ _ state = state;

fun set_goal goal = map_goal I (fn (statement, using, _, before_qed, after_qed) =>
  (statement, using, goal, before_qed, after_qed));

fun using_facts using = map_goal I (fn (statement, _, goal, before_qed, after_qed) =>
  (statement, using, goal, before_qed, after_qed));

local
  fun find i state =
    (case try current_goal state of
      SOME (ctxt, goal) => (ctxt, (i, goal))
    | NONE => find (i + 1) (close_block state handle ERROR _ => error "No goal present"));
in val find_goal = find 0 end;

fun get_goal state =
  let val (ctxt, (_, {using, goal, ...})) = find_goal state
  in (ctxt, (using, goal)) end;

fun schematic_goal state =
  let val (_, (_, {statement = (_, propss), ...})) = find_goal state in
    exists (exists (Term.exists_subterm Term.is_Var)) propss orelse
    exists (exists (Term.exists_type (Term.exists_subtype Term.is_TVar))) propss
  end;



(** pretty_state **)

val show_main_goal = ref false;
val verbose = ProofContext.verbose;

val pretty_goals_local = Display.pretty_goals_aux o ProofContext.pp;

fun pretty_facts _ _ NONE = []
  | pretty_facts s ctxt (SOME ths) =
      [Pretty.big_list (s ^ "this:") (map (ProofContext.pretty_thm ctxt) ths), Pretty.str ""];

fun pretty_state nr state =
  let
    val {context, facts, mode, goal = _} = current state;
    val ref (_, _, bg) = Display.current_goals_markers;

    fun levels_up 0 = ""
      | levels_up 1 = "1 level up"
      | levels_up i = string_of_int i ^ " levels up";

    fun subgoals 0 = ""
      | subgoals 1 = "1 subgoal"
      | subgoals n = string_of_int n ^ " subgoals";

    fun description strs =
      (case filter_out (equal "") strs of [] => ""
      | strs' => enclose " (" ")" (commas strs'));

    fun prt_goal (SOME (ctxt, (i, {statement = _, using, goal, before_qed, after_qed}))) =
          pretty_facts "using " ctxt
            (if mode <> Backward orelse null using then NONE else SOME using) @
          [Pretty.str ("goal" ^
            description [levels_up (i div 2), subgoals (Thm.nprems_of goal)] ^ ":")] @
          pretty_goals_local ctxt bg (true, ! show_main_goal) (! Display.goals_limit) goal
      | prt_goal NONE = [];

    val prt_ctxt =
      if ! verbose orelse mode = Forward then ProofContext.pretty_context context
      else if mode = Backward then ProofContext.pretty_ctxt context
      else [];
  in
    [Pretty.str ("proof (" ^ mode_name mode ^ "): step " ^ string_of_int nr ^
      (if ! verbose then ", depth " ^ string_of_int (level state div 2 - 1) else "")),
      Pretty.str ""] @
    (if null prt_ctxt then [] else prt_ctxt @ [Pretty.str ""]) @
    (if ! verbose orelse mode = Forward then
       pretty_facts "" context facts @ prt_goal (try find_goal state)
     else if mode = Chain then pretty_facts "picking " context facts
     else prt_goal (try find_goal state))
  end;

fun pretty_goals main state =
  let val (ctxt, (_, goal)) = get_goal state
  in pretty_goals_local ctxt "" (false, main) (! Display.goals_limit) goal end;



(** proof steps **)

(* refine via method *)

local

fun goalN i = "goal" ^ string_of_int i;
fun goals st = map goalN (1 upto Thm.nprems_of st);

fun no_goal_cases st = map (rpair NONE) (goals st);

fun goal_cases st =
  RuleCases.make_common true (Thm.theory_of_thm st, Thm.prop_of st) (map (rpair []) (goals st));

fun apply_method current_context pos meth_fun state =
  let
    val (goal_ctxt, (_, {statement, using, goal, before_qed, after_qed})) = find_goal state;
    val ctxt = ContextPosition.put pos (if current_context then context_of state else goal_ctxt);
    val meth = meth_fun ctxt;
  in
    Method.apply meth using goal |> Seq.map (fn (meth_cases, goal') =>
      state
      |> map_goal
          (ProofContext.add_cases false (no_goal_cases goal @ goal_cases goal') #>
           ProofContext.add_cases true meth_cases)
          (K (statement, using, goal', before_qed, after_qed)))
  end;

fun select_goals n meth state =
  state
  |> (#2 o #2 o get_goal)
  |> ALLGOALS Goal.conjunction_tac
  |> Seq.maps (fn goal =>
    state
    |> Seq.lift set_goal (Goal.extract 1 n goal |> Seq.maps (Goal.conjunction_tac 1))
    |> Seq.maps meth
    |> Seq.maps (fn state' => state'
      |> Seq.lift set_goal (Goal.retrofit 1 n (#2 (#2 (get_goal state'))) goal))
    |> Seq.maps (apply_method true Position.none (K Method.succeed)));

fun apply_text cc text state =
  let
    val thy = theory_of state;
    val pos_of = #2 o Args.dest_src;

    fun eval (Method.Basic (m, pos)) = apply_method cc pos m
      | eval (Method.Source src) = apply_method cc (pos_of src) (Method.method thy src)
      | eval (Method.Source_i src) = apply_method cc (pos_of src) (Method.method_i thy src)
      | eval (Method.Then txts) = Seq.EVERY (map eval txts)
      | eval (Method.Orelse txts) = Seq.FIRST (map eval txts)
      | eval (Method.Try txt) = Seq.TRY (eval txt)
      | eval (Method.Repeat1 txt) = Seq.REPEAT1 (eval txt)
      | eval (Method.SelectGoals (n, txt)) = select_goals n (eval txt);
  in eval text state end;

in

val refine = apply_text true;
val refine_end = apply_text false;

fun refine_insert [] = I
  | refine_insert ths = Seq.hd o refine (Method.Basic (K (Method.insert ths), Position.none));

end;


(* refine via sub-proof *)

fun goal_tac rule =
  Goal.norm_hhf_tac THEN' Tactic.rtac rule THEN_ALL_NEW
    (Goal.norm_hhf_tac THEN' (SUBGOAL (fn (goal, i) =>
      if can Logic.unprotect (Logic.strip_assums_concl goal) then
        Tactic.etac Drule.protectI i
      else all_tac)));

fun refine_goals print_rule inner raw_rules state =
  let
    val (outer, (_, goal)) = get_goal state;
    fun refine rule st = (print_rule outer rule; FINDGOAL (goal_tac rule) st);
  in
    raw_rules
    |> ProofContext.goal_export inner outer
    |> (fn rules => Seq.lift set_goal (EVERY (map refine rules) goal) state)
  end;


(* conclude_goal *)

fun conclude_goal state goal propss =
  let
    val thy = theory_of state;
    val ctxt = context_of state;
    val string_of_term = ProofContext.string_of_term ctxt;
    val string_of_thm = ProofContext.string_of_thm ctxt;

    val ngoals = Thm.nprems_of goal;
    val _ = ngoals = 0 orelse error (Pretty.string_of (Pretty.chunks
        (pretty_goals_local ctxt "" (true, ! show_main_goal) (! Display.goals_limit) goal @
          [Pretty.str (string_of_int ngoals ^ " unsolved goal(s)!")])));

    val extra_hyps = Assumption.extra_hyps ctxt goal;
    val _ = null extra_hyps orelse
      error ("Additional hypotheses:\n" ^ cat_lines (map string_of_term extra_hyps));

    fun lost_structure () = error ("Lost goal structure:\n" ^ string_of_thm goal);

    val th = Goal.conclude goal handle THM _ => lost_structure ();
    val goal_propss = filter_out null propss;
    val results =
      Conjunction.elim_balanced (length goal_propss) th
      |> map2 Conjunction.elim_balanced (map length goal_propss)
      handle THM _ => lost_structure ();
    val _ = Unify.matches_list thy (flat goal_propss) (map Thm.prop_of (flat results)) orelse
      error ("Proved a different theorem:\n" ^ string_of_thm th);

    fun recover_result ([] :: pss) thss = [] :: recover_result pss thss
      | recover_result (_ :: pss) (ths :: thss) = ths :: recover_result pss thss
      | recover_result [] [] = []
      | recover_result _ _ = lost_structure ();
  in recover_result propss results end;



(*** structured proof commands ***)

(** context elements **)

(* bindings *)

local

fun gen_bind bind args state =
  state
  |> assert_forward
  |> map_context (bind args #> snd)
  |> put_facts NONE;

in

val match_bind = gen_bind (ProofContext.match_bind false);
val match_bind_i = gen_bind (ProofContext.match_bind_i false);
val let_bind = gen_bind (ProofContext.match_bind true);
val let_bind_i = gen_bind (ProofContext.match_bind_i true);

end;


(* fix *)

local

fun gen_fix add_fixes args =
  assert_forward
  #> map_context (snd o add_fixes args)
  #> put_facts NONE;

in

val fix = gen_fix ProofContext.add_fixes;
val fix_i = gen_fix ProofContext.add_fixes_i;

end;


(* assume etc. *)

local

fun gen_assume asm prep_att exp args state =
  state
  |> assert_forward
  |> map_context_result (asm exp (Attrib.map_specs (prep_att (theory_of state)) args))
  |> these_factss [] |> #2;

in

val assm      = gen_assume ProofContext.add_assms Attrib.attribute;
val assm_i    = gen_assume ProofContext.add_assms_i (K I);
val assume    = assm Assumption.assume_export;
val assume_i  = assm_i Assumption.assume_export;
val presume   = assm Assumption.presume_export;
val presume_i = assm_i Assumption.presume_export;

end;


(* def *)

local

fun gen_def prep_att prep_vars prep_binds args state =
  let
    val _ = assert_forward state;
    val thy = theory_of state;
    val ctxt = context_of state;

    val (raw_name_atts, (raw_vars, raw_rhss)) = args |> split_list ||> split_list;
    val name_atts = map (apsnd (map (prep_att thy))) raw_name_atts;
  in
    state
    |> map_context_result (prep_vars (map (fn (x, mx) => (x, NONE, mx)) raw_vars))
    |>> map (fn (x, _, mx) => (x, mx))
    |-> (fn vars =>
      map_context_result (prep_binds false (map swap raw_rhss))
      #-> (fn rhss => map_context_result (LocalDefs.add_defs (vars ~~ (name_atts ~~ rhss)))))
    |-> (put_facts o SOME o map (#2 o #2))
  end;

in

val def = gen_def Attrib.attribute ProofContext.read_vars ProofContext.match_bind;
val def_i = gen_def (K I) ProofContext.cert_vars ProofContext.match_bind_i;

end;



(** facts **)

(* chain *)

val chain =
  assert_forward
  #> tap the_facts
  #> enter_chain;

fun chain_facts facts =
  put_facts (SOME facts)
  #> chain;


(* note etc. *)

fun no_binding args = map (pair ("", [])) args;

local

fun gen_thmss note_ctxt more_facts opt_chain opt_result prep_atts args state =
  state
  |> assert_forward
  |> map_context_result (note_ctxt (Attrib.map_facts (prep_atts (theory_of state)) args))
  |> these_factss (more_facts state)
  ||> opt_chain
  |> opt_result;

in

val note_thmss = gen_thmss (ProofContext.note_thmss "") (K []) I #2 Attrib.attribute;
val note_thmss_i = gen_thmss (ProofContext.note_thmss_i "") (K []) I #2 (K I);

val from_thmss =
  gen_thmss (ProofContext.note_thmss "") (K []) chain #2 Attrib.attribute o no_binding;
val from_thmss_i = gen_thmss (ProofContext.note_thmss_i "") (K []) chain #2 (K I) o no_binding;

val with_thmss =
  gen_thmss (ProofContext.note_thmss "") the_facts chain #2 Attrib.attribute o no_binding;
val with_thmss_i = gen_thmss (ProofContext.note_thmss_i "") the_facts chain #2 (K I) o no_binding;

val local_results =
  gen_thmss (ProofContext.note_thmss_i "") (K []) I I (K I) o map (apsnd Thm.simple_fact);

fun get_thmss state srcs = the_facts (note_thmss [(("", []), srcs)] state);

end;


(* using/unfolding *)

local

fun gen_using f g note prep_atts args state =
  state
  |> assert_backward
  |> map_context_result
    (note "" (Attrib.map_facts (prep_atts (theory_of state)) (no_binding args)))
  |> (fn (named_facts, state') =>
    state' |> map_goal I (fn (statement, using, goal, before_qed, after_qed) =>
      let
        val ctxt = context_of state';
        val ths = maps snd named_facts;
      in (statement, f ctxt ths using, g ctxt ths goal, before_qed, after_qed) end));

fun append_using _ ths using = using @ ths;
fun unfold_using ctxt ths = map (LocalDefs.unfold ctxt ths);
val unfold_goals = LocalDefs.unfold_goals;

in

val using = gen_using append_using (K (K I)) ProofContext.note_thmss Attrib.attribute;
val using_i = gen_using append_using (K (K I)) ProofContext.note_thmss_i (K I);
val unfolding = gen_using unfold_using unfold_goals ProofContext.note_thmss Attrib.attribute;
val unfolding_i = gen_using unfold_using unfold_goals ProofContext.note_thmss_i (K I);

end;


(* case *)

local

fun gen_invoke_case prep_att (name, xs, raw_atts) state =
  let
    val atts = map (prep_att (theory_of state)) raw_atts;
    val (asms, state') = state |> map_context_result (fn ctxt =>
      ctxt |> ProofContext.apply_case (ProofContext.get_case ctxt name xs));
    val assumptions = asms |> map (fn (a, ts) => ((a, atts), map (rpair []) ts));
  in
    state'
    |> map_context (ProofContext.qualified_names #> ProofContext.no_base_names)
    |> assume_i assumptions
    |> add_binds_i AutoBind.no_facts
    |> map_context (ProofContext.restore_naming (context_of state))
    |> `the_facts |-> (fn thms => note_thmss_i [((name, []), [(thms, [])])])
  end;

in

val invoke_case = gen_invoke_case Attrib.attribute;
val invoke_case_i = gen_invoke_case (K I);

end;



(** proof structure **)

(* blocks *)

val begin_block =
  assert_forward
  #> open_block
  #> put_goal NONE
  #> open_block;

val next_block =
  assert_forward
  #> close_block
  #> open_block
  #> put_goal NONE
  #> put_facts NONE;

fun end_block state =
  state
  |> assert_forward
  |> close_block
  |> assert_current_goal false
  |> close_block
  |> export_facts state;


(* sub-proofs *)

fun proof opt_text =
  assert_backward
  #> refine (the_default Method.default_text opt_text)
  #> Seq.map (using_facts [] #> enter_forward);

fun end_proof bot txt state =
  state
  |> assert_forward
  |> assert_bottom bot
  |> close_block
  |> assert_current_goal true
  |> using_facts []
  |> `before_qed |-> (refine o the_default Method.succeed_text)
  |> Seq.maps (refine (Method.finish_text txt (ContextPosition.get (context_of state))));


(* unstructured refinement *)

fun defer i = assert_no_chain #> refine (Method.Basic (K (Method.defer i), Position.none));
fun prefer i = assert_no_chain #> refine (Method.Basic (K (Method.prefer i), Position.none));

fun apply text = assert_backward #> refine text #> Seq.map (using_facts []);
fun apply_end text = assert_forward #> refine_end text;



(** goals **)

(* generic goals *)

local

fun implicit_vars dest add props =
  let
    val (explicit_vars, props') = take_prefix (can dest) props |>> map dest;
    val vars = rev (subtract (op =) explicit_vars (fold add props []));
    val _ =
      if null vars then ()
      else warning ("Goal statement contains unbound schematic variable(s): " ^
        commas_quote (map (Term.string_of_vname o fst) vars));
  in (rev vars, props') end;

fun refine_terms n =
  refine (Method.Basic (K (Method.RAW_METHOD
    (K (HEADGOAL (PRECISE_CONJUNCTS n
      (HEADGOAL (CONJUNCTS (ALLGOALS (rtac Drule.termI)))))))), Position.none))
  #> Seq.hd;

in

fun generic_goal prepp kind before_qed after_qed raw_propp state =
  let
    val thy = theory_of state;
    val cert = Thm.cterm_of thy;
    val chaining = can assert_chain state;

    val ((propss, after_ctxt), goal_state) =
      state
      |> assert_forward_or_chain
      |> enter_forward
      |> open_block
      |> map_context_result (fn ctxt => swap (prepp (ctxt, raw_propp)));
    val props = flat propss;

    val (_, props') =
      implicit_vars (dest_TVar o Logic.dest_type o Logic.dest_term) Term.add_tvars props;
    val (vars, _) = implicit_vars (dest_Var o Logic.dest_term) Term.add_vars props';

    val propss' = map (Logic.mk_term o Var) vars :: propss;
    val goal_propss = filter_out null propss';
    val goal = Goal.init (cert
      (Logic.mk_conjunction_balanced (map Logic.mk_conjunction_balanced goal_propss)));
    val after_qed' = after_qed |>> (fn after_local =>
      fn results => map_context after_ctxt #> after_local results);
  in
    goal_state
    |> map_context (init_context #> Variable.set_body true)
    |> put_goal (SOME (make_goal ((kind, propss'), [], goal, before_qed, after_qed')))
    |> map_context (ProofContext.add_cases false (AutoBind.cases thy props))
    |> map_context (ProofContext.auto_bind_goal props)
    |> chaining ? (`the_facts #-> using_facts)
    |> put_facts NONE
    |> open_block
    |> put_goal NONE
    |> enter_backward
    |> not (null vars) ? refine_terms (length goal_propss)
    |> null props ? (refine (Method.Basic (Method.assumption, Position.none)) #> Seq.hd)
  end;

fun generic_qed state =
  let
    val (goal_ctxt, {statement = (_, stmt), using = _, goal, before_qed = _, after_qed}) =
      current_goal state;
    val outer_state = state |> close_block;
    val outer_ctxt = context_of outer_state;

    val props =
      flat (tl stmt)
      |> Variable.exportT_terms goal_ctxt outer_ctxt;
    val results =
      tl (conclude_goal state goal stmt)
      |> burrow (ProofContext.export goal_ctxt outer_ctxt);
  in
    outer_state
    |> map_context (ProofContext.auto_bind_facts props)
    |> pair (after_qed, results)
  end;

end;


(* local goals *)

fun local_goal print_results prep_att prepp kind before_qed after_qed stmt state =
  let
    val thy = theory_of state;
    val ((names, attss), propp) =
      Attrib.map_specs (prep_att thy) stmt |> split_list |>> split_list;

    fun after_qed' results =
      local_results ((names ~~ attss) ~~ results)
      #-> (fn res => tap (fn st => print_results (context_of st) ((kind, ""), res) : unit))
      #> after_qed results;
  in
    state
    |> generic_goal prepp kind before_qed (after_qed', K I) propp
    |> tap (Variable.warn_extra_tfrees (context_of state) o context_of)
  end;

fun local_qed txt =
  end_proof false txt #>
  Seq.maps (generic_qed #-> (fn ((after_qed, _), results) => after_qed results));


(* global goals *)

fun global_goal prepp before_qed after_qed propp ctxt =
  init ctxt
  |> generic_goal (prepp #> ProofContext.auto_fixes) ""
    before_qed (K Seq.single, after_qed) propp;

val theorem = global_goal ProofContext.bind_propp_schematic;
val theorem_i = global_goal ProofContext.bind_propp_schematic_i;

fun check_result msg sq =
  (case Seq.pull sq of
    NONE => error msg
  | SOME (s', sq') => Seq.cons s' sq');

fun global_qeds txt =
  end_proof true txt
  #> Seq.map (generic_qed #> (fn (((_, after_qed), results), state) =>
    after_qed results (context_of state)))
  |> Seq.DETERM;   (*backtracking may destroy theory!*)

fun global_qed txt =
  global_qeds txt
  #> check_result "Failed to finish proof"
  #> Seq.hd;


(* concluding steps *)

fun local_terminal_proof (text, opt_text) =
  proof (SOME text) #> Seq.maps (local_qed (opt_text, true));

val local_default_proof = local_terminal_proof (Method.default_text, NONE);
val local_immediate_proof = local_terminal_proof (Method.this_text, NONE);
val local_done_proof = proof (SOME Method.done_text) #> Seq.maps (local_qed (NONE, false));
fun local_skip_proof int = local_terminal_proof (Method.sorry_text int, NONE);

fun global_term_proof immed (text, opt_text) =
  proof (SOME text)
  #> check_result "Terminal proof method failed"
  #> Seq.maps (global_qeds (opt_text, immed))
  #> check_result "Failed to finish proof (after successful terminal method)"
  #> Seq.hd;

val global_terminal_proof = global_term_proof true;
val global_default_proof = global_terminal_proof (Method.default_text, NONE);
val global_immediate_proof = global_terminal_proof (Method.this_text, NONE);
val global_done_proof = global_term_proof false (Method.done_text, NONE);
fun global_skip_proof int = global_terminal_proof (Method.sorry_text int, NONE);


(* common goal statements *)

local

fun gen_have prep_att prepp before_qed after_qed stmt int =
  local_goal (ProofDisplay.print_results int) prep_att prepp "have" before_qed after_qed stmt;

fun gen_show prep_att prepp before_qed after_qed stmt int state =
  let
    val testing = ref false;
    val rule = ref (NONE: thm option);
    fun fail_msg ctxt =
      "Local statement will fail to solve any pending goal" ::
      (case ! rule of NONE => [] | SOME th => [ProofDisplay.string_of_rule ctxt "Failed" th])
      |> cat_lines;

    fun print_results ctxt res =
      if ! testing then () else ProofDisplay.print_results int ctxt res;
    fun print_rule ctxt th =
      if ! testing then rule := SOME th
      else if int then priority (ProofDisplay.string_of_rule ctxt "Successful" th)
      else ();
    val test_proof =
      (Seq.pull oo local_skip_proof) true
      |> setmp testing true
      |> setmp proofs 0
      |> capture;

    fun after_qed' results =
      refine_goals print_rule (context_of state) (flat results)
      #> Seq.maps (after_qed results);
  in
    state
    |> local_goal print_results prep_att prepp "show" before_qed after_qed' stmt
    |> int ? (fn goal_state =>
      (case test_proof goal_state of
        Result (SOME _) => goal_state
      | Result NONE => error (fail_msg (context_of goal_state))
      | Exn Interrupt => raise Interrupt
      | Exn exn => raise EXCEPTION (exn, fail_msg (context_of goal_state))))
  end;

in

val have = gen_have Attrib.attribute ProofContext.bind_propp;
val have_i = gen_have (K I) ProofContext.bind_propp_i;
val show = gen_show Attrib.attribute ProofContext.bind_propp;
val show_i = gen_show (K I) ProofContext.bind_propp_i;

end;

end;
