(*  Title:      Pure/Isar/proof.ML
    Author:     Markus Wenzel, TU Muenchen

The Isar/VM proof language interpreter: maintains a structured flow of
context elements, goals, refinements, and facts.
*)

signature PROOF =
sig
  type context = Proof.context
  type method = Method.method
  type state
  val init: context -> state
  val level: state -> int
  val assert_bottom: bool -> state -> state
  val context_of: state -> context
  val theory_of: state -> theory
  val map_context: (context -> context) -> state -> state
  val map_contexts: (context -> context) -> state -> state
  val bind_terms: (indexname * term option) list -> state -> state
  val put_thms: bool -> string * thm list option -> state -> state
  val the_facts: state -> thm list
  val the_fact: state -> thm
  val put_facts: thm list option -> state -> state
  val assert_forward: state -> state
  val assert_chain: state -> state
  val assert_forward_or_chain: state -> state
  val assert_backward: state -> state
  val assert_no_chain: state -> state
  val enter_forward: state -> state
  val goal_message: (unit -> Pretty.T) -> state -> state
  val show_main_goal: bool Unsynchronized.ref
  val verbose: bool Unsynchronized.ref
  val pretty_state: int -> state -> Pretty.T list
  val pretty_goals: bool -> state -> Pretty.T list
  val refine: Method.text -> state -> state Seq.seq
  val refine_end: Method.text -> state -> state Seq.seq
  val refine_insert: thm list -> state -> state
  val goal_tac: thm -> int -> tactic
  val refine_goals: (context -> thm -> unit) -> context -> thm list -> state -> state Seq.seq
  val raw_goal: state -> {context: context, facts: thm list, goal: thm}
  val goal: state -> {context: context, facts: thm list, goal: thm}
  val simple_goal: state -> {context: context, goal: thm}
  val match_bind: (string list * string) list -> state -> state
  val match_bind_i: (term list * term) list -> state -> state
  val let_bind: (string list * string) list -> state -> state
  val let_bind_i: (term list * term) list -> state -> state
  val fix: (binding * string option * mixfix) list -> state -> state
  val fix_i: (binding * typ option * mixfix) list -> state -> state
  val assm: Assumption.export ->
    (Attrib.binding * (string * string list) list) list -> state -> state
  val assm_i: Assumption.export ->
    (Thm.binding * (term * term list) list) list -> state -> state
  val assume: (Attrib.binding * (string * string list) list) list -> state -> state
  val assume_i: (Thm.binding * (term * term list) list) list -> state -> state
  val presume: (Attrib.binding * (string * string list) list) list -> state -> state
  val presume_i: (Thm.binding * (term * term list) list) list -> state -> state
  val def: (Attrib.binding * ((binding * mixfix) * (string * string list))) list -> state -> state
  val def_i: (Thm.binding * ((binding * mixfix) * (term * term list))) list -> state -> state
  val chain: state -> state
  val chain_facts: thm list -> state -> state
  val get_thmss: state -> (Facts.ref * Attrib.src list) list -> thm list
  val note_thmss: (Attrib.binding * (Facts.ref * Attrib.src list) list) list -> state -> state
  val note_thmss_i: (Thm.binding * (thm list * attribute list) list) list -> state -> state
  val from_thmss: ((Facts.ref * Attrib.src list) list) list -> state -> state
  val from_thmss_i: ((thm list * attribute list) list) list -> state -> state
  val with_thmss: ((Facts.ref * Attrib.src list) list) list -> state -> state
  val with_thmss_i: ((thm list * attribute list) list) list -> state -> state
  val using: ((Facts.ref * Attrib.src list) list) list -> state -> state
  val using_i: ((thm list * attribute list) list) list -> state -> state
  val unfolding: ((Facts.ref * Attrib.src list) list) list -> state -> state
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
    string -> Method.text option -> (thm list list -> state -> state) ->
    ((binding * 'a list) * 'b) list -> state -> state
  val local_qed: Method.text option * bool -> state -> state
  val theorem: Method.text option -> (thm list list -> context -> context) ->
    (string * string list) list list -> context -> state
  val theorem_i: Method.text option -> (thm list list -> context -> context) ->
    (term * term list) list list -> context -> state
  val global_qed: Method.text option * bool -> state -> context
  val local_terminal_proof: Method.text * Method.text option -> state -> state
  val local_default_proof: state -> state
  val local_immediate_proof: state -> state
  val local_skip_proof: bool -> state -> state
  val local_done_proof: state -> state
  val global_terminal_proof: Method.text * Method.text option -> state -> context
  val global_default_proof: state -> context
  val global_immediate_proof: state -> context
  val global_skip_proof: bool -> state -> context
  val global_done_proof: state -> context
  val have: Method.text option -> (thm list list -> state -> state) ->
    (Attrib.binding * (string * string list) list) list -> bool -> state -> state
  val have_i: Method.text option -> (thm list list -> state -> state) ->
    (Thm.binding * (term * term list) list) list -> bool -> state -> state
  val show: Method.text option -> (thm list list -> state -> state) ->
    (Attrib.binding * (string * string list) list) list -> bool -> state -> state
  val show_i: Method.text option -> (thm list list -> state -> state) ->
    (Thm.binding * (term * term list) list) list -> bool -> state -> state
  val schematic_goal: state -> bool
  val is_relevant: state -> bool
  val local_future_proof: (state -> ('a * state) Future.future) ->
    state -> 'a Future.future * state
  val global_future_proof: (state -> ('a * Proof.context) Future.future) ->
    state -> 'a Future.future * context
  val local_future_terminal_proof: Method.text * Method.text option -> bool -> state -> state
  val global_future_terminal_proof: Method.text * Method.text option -> bool -> state -> context
end;

structure Proof: PROOF =
struct

type context = Proof.context;
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
   {statement: (string * Position.T) * term list list * term,
      (*goal kind and statement (starting with vars), initial proposition*)
    messages: (unit -> Pretty.T) list,    (*persistent messages (hints etc.)*)
    using: thm list,                      (*goal facts*)
    goal: thm,                            (*subgoals ==> statement*)
    before_qed: Method.text option,
    after_qed:
      (thm list list -> state -> state) *
      (thm list list -> context -> context)};

fun make_goal (statement, messages, using, goal, before_qed, after_qed) =
  Goal {statement = statement, messages = messages, using = using, goal = goal,
    before_qed = before_qed, after_qed = after_qed};

fun make_node (context, facts, mode, goal) =
  Node {context = context, facts = facts, mode = mode, goal = goal};

fun map_node f (Node {context, facts, mode, goal}) =
  make_node (f (context, facts, mode, goal));

val init_context =
  ProofContext.set_stmt true #>
  ProofContext.map_naming (K ProofContext.local_naming);

fun init ctxt =
  State (Stack.init (make_node (init_context ctxt, NONE, Forward, NONE)));

fun current (State st) = Stack.top st |> (fn Node node => node);
fun map_current f (State st) = State (Stack.map_top (map_node f) st);
fun map_all f (State st) = State (Stack.map_all (map_node f) st);



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

fun map_contexts f = map_all (fn (ctxt, facts, mode, goal) => (f ctxt, facts, mode, goal));

val bind_terms = map_context o ProofContext.bind_terms;
val put_thms = map_context oo ProofContext.put_thms;


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
  put_thms true (Auto_Bind.thisN, facts);

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
        val Goal {statement, messages, using, goal, before_qed, after_qed} = goal;
        val goal' = make_goal (g (statement, messages, using, goal, before_qed, after_qed));
      in State (make_node (f context, facts, mode, SOME goal'), nodes) end
  | map_goal f g (State (nd, node :: nodes)) =
      let val State (node', nodes') = map_goal f g (State (node, nodes))
      in map_context f (State (nd, node' :: nodes')) end
  | map_goal _ _ state = state;

fun set_goal goal = map_goal I (fn (statement, _, using, _, before_qed, after_qed) =>
  (statement, [], using, goal, before_qed, after_qed));

fun goal_message msg = map_goal I (fn (statement, messages, using, goal, before_qed, after_qed) =>
  (statement, msg :: messages, using, goal, before_qed, after_qed));

fun using_facts using = map_goal I (fn (statement, _, _, goal, before_qed, after_qed) =>
  (statement, [], using, goal, before_qed, after_qed));

local
  fun find i state =
    (case try current_goal state of
      SOME (ctxt, goal) => (ctxt, (i, goal))
    | NONE => find (i + 1) (close_block state handle ERROR _ => error "No goal present"));
in val find_goal = find 0 end;

fun get_goal state =
  let val (ctxt, (_, {using, goal, ...})) = find_goal state
  in (ctxt, (using, goal)) end;



(** pretty_state **)

val show_main_goal = Unsynchronized.ref false;
val verbose = ProofContext.verbose;

fun pretty_facts _ _ NONE = []
  | pretty_facts s ctxt (SOME ths) =
      [Pretty.big_list (s ^ "this:") (map (Display.pretty_thm ctxt) ths), Pretty.str ""];

fun pretty_state nr state =
  let
    val {context, facts, mode, goal = _} = current state;

    fun levels_up 0 = ""
      | levels_up 1 = "1 level up"
      | levels_up i = string_of_int i ^ " levels up";

    fun subgoals 0 = ""
      | subgoals 1 = "1 subgoal"
      | subgoals n = string_of_int n ^ " subgoals";

    fun description strs =
      (case filter_out (fn s => s = "") strs of [] => ""
      | strs' => enclose " (" ")" (commas strs'));

    fun prt_goal (SOME (ctxt, (i,
      {statement = ((_, pos), _, _), messages, using, goal, before_qed = _, after_qed = _}))) =
          pretty_facts "using " ctxt
            (if mode <> Backward orelse null using then NONE else SOME using) @
          [Pretty.str ("goal" ^
            description [levels_up (i div 2), subgoals (Thm.nprems_of goal)] ^ ":")] @
          Goal_Display.pretty_goals ctxt
            {total = true, main = ! show_main_goal, maxgoals = ! Display.goals_limit} goal @
          (map (fn msg => Position.setmp_thread_data pos msg ()) (rev messages))
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
  let val (ctxt, (_, goal)) = get_goal state in
    Goal_Display.pretty_goals ctxt
      {total = false, main = main, maxgoals = ! Display.goals_limit} goal
  end;



(** proof steps **)

(* refine via method *)

local

fun goalN i = "goal" ^ string_of_int i;
fun goals st = map goalN (1 upto Thm.nprems_of st);

fun no_goal_cases st = map (rpair NONE) (goals st);

fun goal_cases st =
  Rule_Cases.make_common true (Thm.theory_of_thm st, Thm.prop_of st) (map (rpair []) (goals st));

fun apply_method current_context meth state =
  let
    val (goal_ctxt, (_, {statement, messages = _, using, goal, before_qed, after_qed})) =
      find_goal state;
    val ctxt = if current_context then context_of state else goal_ctxt;
  in
    Method.apply meth ctxt using goal |> Seq.map (fn (meth_cases, goal') =>
      state
      |> map_goal
          (ProofContext.add_cases false (no_goal_cases goal @ goal_cases goal') #>
           ProofContext.add_cases true meth_cases)
          (K (statement, [], using, goal', before_qed, after_qed)))
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
    |> Seq.maps (apply_method true (K Method.succeed)));

fun apply_text cc text state =
  let
    val thy = theory_of state;

    fun eval (Method.Basic m) = apply_method cc m
      | eval (Method.Source src) = apply_method cc (Method.method thy src)
      | eval (Method.Source_i src) = apply_method cc (Method.method_i thy src)
      | eval (Method.Then txts) = Seq.EVERY (map eval txts)
      | eval (Method.Orelse txts) = Seq.FIRST (map eval txts)
      | eval (Method.Try txt) = Seq.TRY (eval txt)
      | eval (Method.Repeat1 txt) = Seq.REPEAT1 (eval txt)
      | eval (Method.SelectGoals (n, txt)) = select_goals n (eval txt);
  in eval text state end;

in

val refine = apply_text true;
val refine_end = apply_text false;
fun refine_insert ths = Seq.hd o refine (Method.Basic (K (Method.insert ths)));

end;


(* refine via sub-proof *)

fun finish_tac 0 = K all_tac
  | finish_tac n =
      Goal.norm_hhf_tac THEN'
      SUBGOAL (fn (goal, i) =>
        if can Logic.unprotect (Logic.strip_assums_concl goal) then
          Tactic.etac Drule.protectI i THEN finish_tac (n - 1) i
        else finish_tac (n - 1) (i + 1));

fun goal_tac rule =
  Goal.norm_hhf_tac THEN'
  Tactic.rtac rule THEN'
  finish_tac (Thm.nprems_of rule);

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

fun conclude_goal ctxt goal propss =
  let
    val thy = ProofContext.theory_of ctxt;
    val string_of_term = Syntax.string_of_term ctxt;
    val string_of_thm = Display.string_of_thm ctxt;

    val ngoals = Thm.nprems_of goal;
    val _ = ngoals = 0 orelse error (Pretty.string_of (Pretty.chunks
      (Goal_Display.pretty_goals ctxt
          {total = true, main = ! show_main_goal, maxgoals = ! Display.goals_limit} goal @
        [Pretty.str (string_of_int ngoals ^ " unsolved goal(s)!")])));

    val extra_hyps = Assumption.extra_hyps ctxt goal;
    val _ = null extra_hyps orelse
      error ("Additional hypotheses:\n" ^ cat_lines (map string_of_term extra_hyps));

    fun lost_structure () = error ("Lost goal structure:\n" ^ string_of_thm goal);

    val th = Goal.conclude
      (if length (flat propss) > 1 then Thm.norm_proof goal else goal)
      handle THM _ => lost_structure ();
    val goal_propss = filter_out null propss;
    val results =
      Conjunction.elim_balanced (length goal_propss) th
      |> map2 Conjunction.elim_balanced (map length goal_propss)
      handle THM _ => lost_structure ();
    val _ = Unify.matches_list thy (flat goal_propss) (map Thm.prop_of (flat results)) orelse
      error ("Proved a different theorem:\n" ^ string_of_thm th);
    val _ = Thm.check_shyps (Variable.sorts_of ctxt) th;

    fun recover_result ([] :: pss) thss = [] :: recover_result pss thss
      | recover_result (_ :: pss) (ths :: thss) = ths :: recover_result pss thss
      | recover_result [] [] = []
      | recover_result _ _ = lost_structure ();
  in recover_result propss results end;


(* goal views -- corresponding to methods *)

fun raw_goal state =
  let val (ctxt, (facts, goal)) = get_goal state
  in {context = ctxt, facts = facts, goal = goal} end;

val goal = raw_goal o refine_insert [];

fun simple_goal state =
  let
    val (_, (facts, _)) = get_goal state;
    val (ctxt, (_, goal)) = get_goal (refine_insert facts state);
  in {context = ctxt, goal = goal} end;



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

fun gen_fix prep_vars args =
  assert_forward
  #> map_context (fn ctxt => snd (ProofContext.add_fixes (prep_vars ctxt args) ctxt))
  #> put_facts NONE;

in

val fix = gen_fix (fn ctxt => fn args => fst (ProofContext.read_vars args ctxt));
val fix_i = gen_fix (K I);

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

fun clean_facts ctxt =
  put_facts (SOME (filter_out Thm.is_dummy (the_facts ctxt))) ctxt;

val chain =
  assert_forward
  #> clean_facts
  #> enter_chain;

fun chain_facts facts =
  put_facts (SOME facts)
  #> chain;


(* note etc. *)

fun no_binding args = map (pair (Binding.empty, [])) args;

local

fun gen_thmss more_facts opt_chain opt_result prep_atts prep_fact args state =
  state
  |> assert_forward
  |> map_context_result (ProofContext.note_thmss ""
    (Attrib.map_facts_refs (prep_atts (theory_of state)) (prep_fact (context_of state)) args))
  |> these_factss (more_facts state)
  ||> opt_chain
  |> opt_result;

in

val note_thmss = gen_thmss (K []) I #2 Attrib.attribute ProofContext.get_fact;
val note_thmss_i = gen_thmss (K []) I #2 (K I) (K I);

val from_thmss = gen_thmss (K []) chain #2 Attrib.attribute ProofContext.get_fact o no_binding;
val from_thmss_i = gen_thmss (K []) chain #2 (K I) (K I) o no_binding;

val with_thmss = gen_thmss the_facts chain #2 Attrib.attribute ProofContext.get_fact o no_binding;
val with_thmss_i = gen_thmss the_facts chain #2 (K I) (K I) o no_binding;

val local_results = gen_thmss (K []) I I (K I) (K I) o map (apsnd Thm.simple_fact);

fun get_thmss state srcs = the_facts (note_thmss [((Binding.empty, []), srcs)] state);

end;


(* using/unfolding *)

local

fun gen_using f g prep_atts prep_fact args state =
  state
  |> assert_backward
  |> map_context_result
    (ProofContext.note_thmss ""
      (Attrib.map_facts_refs (prep_atts (theory_of state)) (prep_fact (context_of state))
        (no_binding args)))
  |> (fn (named_facts, state') =>
    state' |> map_goal I (fn (statement, _, using, goal, before_qed, after_qed) =>
      let
        val ctxt = context_of state';
        val ths = maps snd named_facts;
      in (statement, [], f ctxt ths using, g ctxt ths goal, before_qed, after_qed) end));

fun append_using _ ths using = using @ filter_out Thm.is_dummy ths;
fun unfold_using ctxt ths = map (LocalDefs.unfold ctxt ths);
val unfold_goals = LocalDefs.unfold_goals;

in

val using = gen_using append_using (K (K I)) Attrib.attribute ProofContext.get_fact;
val using_i = gen_using append_using (K (K I)) (K I) (K I);
val unfolding = gen_using unfold_using unfold_goals Attrib.attribute ProofContext.get_fact;
val unfolding_i = gen_using unfold_using unfold_goals (K I) (K I);

end;


(* case *)

local

fun qualified_binding a =
  Binding.qualify true (Long_Name.qualifier a) (Binding.name (Long_Name.base_name a));

fun gen_invoke_case prep_att (name, xs, raw_atts) state =
  let
    val atts = map (prep_att (theory_of state)) raw_atts;
    val (asms, state') = state |> map_context_result (fn ctxt =>
      ctxt |> ProofContext.apply_case (ProofContext.get_case ctxt name xs));
    val assumptions = asms |> map (fn (a, ts) => ((qualified_binding a, atts), map (rpair []) ts));
  in
    state'
    |> assume_i assumptions
    |> bind_terms Auto_Bind.no_facts
    |> `the_facts |-> (fn thms => note_thmss_i [((Binding.name name, []), [(thms, [])])])
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
  |> Seq.maps (refine (Method.finish_text txt));

fun check_result msg sq =
  (case Seq.pull sq of
    NONE => error msg
  | SOME (s, _) => s);

fun check_finish sq = check_result "Failed to finish proof" sq;


(* unstructured refinement *)

fun defer i = assert_no_chain #> refine (Method.Basic (K (Method.defer i)));
fun prefer i = assert_no_chain #> refine (Method.Basic (K (Method.prefer i)));

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
  refine (Method.Basic (K (RAW_METHOD
    (K (HEADGOAL (PRECISE_CONJUNCTS n
      (HEADGOAL (CONJUNCTS (ALLGOALS (rtac Drule.termI))))))))))
  #> Seq.hd;

in

fun generic_goal prepp kind before_qed after_qed raw_propp state =
  let
    val thy = theory_of state;
    val cert = Thm.cterm_of thy;
    val chaining = can assert_chain state;
    val pos = Position.thread_data ();

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
    val goal =
      cert (Logic.mk_conjunction_balanced (map Logic.mk_conjunction_balanced goal_propss))
      |> Thm.weaken_sorts (Variable.sorts_of (context_of goal_state));
    val statement = ((kind, pos), propss', Thm.term_of goal);
    val after_qed' = after_qed |>> (fn after_local =>
      fn results => map_context after_ctxt #> after_local results);
  in
    goal_state
    |> map_context (init_context #> Variable.set_body true)
    |> put_goal (SOME (make_goal (statement, [], [], Goal.init goal, before_qed, after_qed')))
    |> map_context (ProofContext.auto_bind_goal props)
    |> chaining ? (`the_facts #-> using_facts)
    |> put_facts NONE
    |> open_block
    |> put_goal NONE
    |> enter_backward
    |> not (null vars) ? refine_terms (length goal_propss)
    |> null props ? (refine (Method.Basic Method.assumption) #> Seq.hd)
  end;

fun generic_qed after_ctxt state =
  let
    val (goal_ctxt, {statement, goal, after_qed, ...}) = current_goal state;
    val outer_state = state |> close_block;
    val outer_ctxt = context_of outer_state;

    val ((_, pos), stmt, _) = statement;
    val props =
      flat (tl stmt)
      |> Variable.exportT_terms goal_ctxt outer_ctxt;
    val results =
      tl (conclude_goal goal_ctxt goal stmt)
      |> burrow (ProofContext.export goal_ctxt outer_ctxt);

    val (after_local, after_global) = after_qed;
    fun after_local' x y = Position.setmp_thread_data pos (fn () => after_local x y) ();
    fun after_global' x y = Position.setmp_thread_data pos (fn () => after_global x y) ();
  in
    outer_state
    |> map_context (after_ctxt props)
    |> pair ((after_local', after_global'), results)
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

fun local_qeds txt =
  end_proof false txt
  #> Seq.map (generic_qed ProofContext.auto_bind_facts #->
    (fn ((after_qed, _), results) => after_qed results));

fun local_qed txt = local_qeds txt #> check_finish;


(* global goals *)

fun global_goal prepp before_qed after_qed propp ctxt =
  init ctxt
  |> generic_goal (prepp #> ProofContext.auto_fixes) "" before_qed (K I, after_qed) propp;

val theorem = global_goal ProofContext.bind_propp_schematic;
val theorem_i = global_goal ProofContext.bind_propp_schematic_i;

fun global_qeds txt =
  end_proof true txt
  #> Seq.map (generic_qed (K I) #> (fn (((_, after_qed), results), state) =>
    after_qed results (context_of state)));

fun global_qed txt = global_qeds txt #> check_finish;


(* concluding steps *)

fun terminal_proof qed initial terminal =
  proof (SOME initial) #> Seq.maps (qed terminal) #> check_finish;

fun local_terminal_proof (text, opt_text) = terminal_proof local_qeds text (opt_text, true);
val local_default_proof = local_terminal_proof (Method.default_text, NONE);
val local_immediate_proof = local_terminal_proof (Method.this_text, NONE);
fun local_skip_proof int = local_terminal_proof (Method.sorry_text int, NONE);
val local_done_proof = terminal_proof local_qeds Method.done_text (NONE, false);

fun global_terminal_proof (text, opt_text) = terminal_proof global_qeds text (opt_text, true);
val global_default_proof = global_terminal_proof (Method.default_text, NONE);
val global_immediate_proof = global_terminal_proof (Method.this_text, NONE);
fun global_skip_proof int = global_terminal_proof (Method.sorry_text int, NONE);
val global_done_proof = terminal_proof global_qeds Method.done_text (NONE, false);


(* common goal statements *)

local

fun gen_have prep_att prepp before_qed after_qed stmt int =
  local_goal (Proof_Display.print_results int) prep_att prepp "have" before_qed after_qed stmt;

fun gen_show prep_att prepp before_qed after_qed stmt int state =
  let
    val testing = Unsynchronized.ref false;
    val rule = Unsynchronized.ref (NONE: thm option);
    fun fail_msg ctxt =
      "Local statement will fail to refine any pending goal" ::
      (case ! rule of NONE => [] | SOME th => [Proof_Display.string_of_rule ctxt "Failed" th])
      |> cat_lines;

    fun print_results ctxt res =
      if ! testing then () else Proof_Display.print_results int ctxt res;
    fun print_rule ctxt th =
      if ! testing then rule := SOME th
      else if int then priority (Proof_Display.string_of_rule ctxt "Successful" th)
      else ();
    val test_proof =
      try (local_skip_proof true)
      |> setmp_noncritical testing true
      |> Exn.capture;

    fun after_qed' results =
      refine_goals print_rule (context_of state) (flat results)
      #> check_result "Failed to refine any pending goal"
      #> after_qed results;
  in
    state
    |> local_goal print_results prep_att prepp "show" before_qed after_qed' stmt
    |> int ? (fn goal_state =>
      (case test_proof goal_state of
        Exn.Result (SOME _) => goal_state
      | Exn.Result NONE => error (fail_msg (context_of goal_state))
      | Exn.Exn Exn.Interrupt => raise Exn.Interrupt
      | Exn.Exn exn => raise Exn.EXCEPTIONS ([exn, ERROR (fail_msg (context_of goal_state))])))
  end;

in

val have = gen_have Attrib.attribute ProofContext.bind_propp;
val have_i = gen_have (K I) ProofContext.bind_propp_i;
val show = gen_show Attrib.attribute ProofContext.bind_propp;
val show_i = gen_show (K I) ProofContext.bind_propp_i;

end;



(** future proofs **)

(* relevant proof states *)

fun is_schematic t =
  Term.exists_subterm Term.is_Var t orelse
  Term.exists_type (Term.exists_subtype Term.is_TVar) t;

fun schematic_goal state =
  let val (_, (_, {statement = (_, _, prop), ...})) = find_goal state
  in is_schematic prop end;

fun is_relevant state =
  (case try find_goal state of
    NONE => true
  | SOME (_, (_, {statement = (_, _, prop), goal, ...})) =>
      is_schematic prop orelse not (Logic.protect prop aconv Thm.concl_of goal));


(* full proofs *)

local

fun future_proof done get_context fork_proof state =
  let
    val _ = assert_backward state;
    val (goal_ctxt, (_, goal)) = find_goal state;
    val {statement as (kind, _, prop), messages, using, goal, before_qed, after_qed} = goal;
    val goal_txt = prop :: map Thm.term_of (Assumption.all_assms_of goal_ctxt);

    val _ = is_relevant state andalso error "Cannot fork relevant proof";

    val prop' = Logic.protect prop;
    val statement' = (kind, [[], [prop']], prop');
    val goal' = Thm.adjust_maxidx_thm (Thm.maxidx_of goal)
      (Drule.comp_no_flatten (goal, Thm.nprems_of goal) 1 Drule.protectI);

    fun after_local' [[th]] = put_thms false (Auto_Bind.thisN, SOME [th]);
    fun after_global' [[th]] = ProofContext.put_thms false (Auto_Bind.thisN, SOME [th]);
    val after_qed' = (after_local', after_global');
    val this_name = ProofContext.full_name goal_ctxt (Binding.name Auto_Bind.thisN);

    val result_ctxt =
      state
      |> map_contexts (fold Variable.declare_term goal_txt)
      |> map_goal I (K (statement', messages, using, goal', before_qed, after_qed'))
      |> fork_proof;

    val future_thm = result_ctxt |> Future.map (fn (_, x) =>
      ProofContext.get_fact_single (get_context x) (Facts.named this_name));
    val finished_goal = Goal.future_result goal_ctxt future_thm prop';
    val state' =
      state
      |> map_goal I (K (statement, messages, using, finished_goal, NONE, after_qed))
      |> done;
  in (Future.map #1 result_ctxt, state') end;

in

fun local_future_proof x = future_proof local_done_proof context_of x;
fun global_future_proof x = future_proof global_done_proof I x;

end;


(* terminal proofs *)

local

fun future_terminal_proof proof1 proof2 meths int state =
  if int orelse is_relevant state orelse not (Goal.local_future_enabled ())
  then proof1 meths state
  else snd (proof2 (fn state' => Future.fork_pri ~1 (fn () => ((), proof1 meths state'))) state);

in

fun local_future_terminal_proof x =
  future_terminal_proof local_terminal_proof local_future_proof x;

fun global_future_terminal_proof x =
  future_terminal_proof global_terminal_proof global_future_proof x;

end;

end;

