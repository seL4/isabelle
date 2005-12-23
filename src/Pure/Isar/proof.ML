(*  Title:      Pure/Isar/proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isar/VM proof language interpreter.
*)

signature PROOF =
sig
  type context (*= Context.proof*)
  type method (*= Method.method*)
  type state
  exception STATE of string * state
  val init: context -> state
  val level: state -> int
  val assert_bottom: bool -> state -> state
  val context_of: state -> context
  val theory_of: state -> theory
  val sign_of: state -> theory    (*obsolete*)
  val map_context: (context -> context) -> state -> state
  val warn_extra_tfrees: state -> state -> state
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
  val show_main_goal: bool ref
  val verbose: bool ref
  val pretty_state: int -> state -> Pretty.T list
  val pretty_goals: bool -> state -> Pretty.T list
  val refine: Method.text -> state -> state Seq.seq
  val refine_end: Method.text -> state -> state Seq.seq
  val refine_goals: (context -> thm -> unit) -> context -> thm list -> state -> state Seq.seq
  val match_bind: (string list * string) list -> state -> state
  val match_bind_i: (term list * term) list -> state -> state
  val let_bind: (string list * string) list -> state -> state
  val let_bind_i: (term list * term) list -> state -> state
  val fix: (string list * string option) list -> state -> state
  val fix_i: (string list * typ option) list -> state -> state
  val assm: ProofContext.exporter ->
    ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    state -> state
  val assm_i: ProofContext.exporter ->
    ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val assume: ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    state -> state
  val assume_i: ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val presume: ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> state -> state
  val presume_i: ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val def: ((string * Attrib.src list) * (string * (string * string list))) list ->
    state -> state
  val def_i: ((string * context attribute list) * (string * (term * term list))) list ->
    state -> state
  val chain: state -> state
  val chain_facts: thm list -> state -> state
  val get_thmss: state -> (thmref * Attrib.src list) list -> thm list
  val simple_note_thms: string -> thm list -> state -> state
  val note_thmss: ((string * Attrib.src list) *
    (thmref * Attrib.src list) list) list -> state -> state
  val note_thmss_i: ((string * context attribute list) *
    (thm list * context attribute list) list) list -> state -> state
  val from_thmss: ((thmref * Attrib.src list) list) list -> state -> state
  val from_thmss_i: ((thm list * context attribute list) list) list -> state -> state
  val with_thmss: ((thmref * Attrib.src list) list) list -> state -> state
  val with_thmss_i: ((thm list * context attribute list) list) list -> state -> state
  val using_thmss: ((thmref * Attrib.src list) list) list -> state -> state
  val using_thmss_i: ((thm list * context attribute list) list) list -> state -> state
  val invoke_case: string * string option list * Attrib.src list -> state -> state
  val invoke_case_i: string * string option list * context attribute list -> state -> state
  val begin_block: state -> state
  val next_block: state -> state
  val end_block: state -> state Seq.seq
  val proof: Method.text option -> state -> state Seq.seq
  val defer: int option -> state -> state Seq.seq
  val prefer: int -> state -> state Seq.seq
  val apply: Method.text -> state -> state Seq.seq
  val apply_end: Method.text -> state -> state Seq.seq
  val goal_names: string option -> string -> string list -> string
  val local_goal: (context -> ((string * string) * (string * thm list) list) -> unit) ->
    (theory -> 'a -> context attribute) ->
    (context * 'b list -> context * (term list list * (context -> context))) ->
    string -> Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * 'a list) * 'b) list -> state -> state
  val local_qed: Method.text option * bool -> state -> state Seq.seq
  val global_goal: (context -> (string * string) * (string * thm list) list -> unit) ->
    (theory -> 'a -> theory attribute) ->
    (context * 'b list -> context * (term list list * (context -> context))) ->
    string -> Method.text option -> (thm list list -> theory -> theory) ->
    string option -> string * 'a list -> ((string * 'a list) * 'b) list -> context -> state
  val global_qed: Method.text option * bool -> state -> theory * context
  val local_terminal_proof: Method.text * Method.text option -> state -> state Seq.seq
  val local_default_proof: state -> state Seq.seq
  val local_immediate_proof: state -> state Seq.seq
  val local_done_proof: state -> state Seq.seq
  val local_skip_proof: bool -> state -> state Seq.seq
  val global_terminal_proof: Method.text * Method.text option -> state -> theory * context
  val global_default_proof: state -> theory * context
  val global_immediate_proof: state -> theory * context
  val global_done_proof: state -> theory * context
  val global_skip_proof: bool -> state -> theory * context
  val have: Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    bool -> state -> state
  val have_i: Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * context attribute list) * (term * (term list * term list)) list) list ->
    bool -> state -> state
  val show: Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    bool -> state -> state
  val show_i: Method.text option -> (thm list list -> state -> state Seq.seq) ->
    ((string * context attribute list) * (term * (term list * term list)) list) list ->
    bool -> state -> state
  val theorem: string -> Method.text option -> (thm list list -> theory -> theory) ->
    string option -> string * Attrib.src list ->
    ((string * Attrib.src list) * (string * (string list * string list)) list) list ->
    context -> state
  val theorem_i: string -> Method.text option -> (thm list list -> theory -> theory) ->
    string option -> string * theory attribute list ->
    ((string * theory attribute list) * (term * (term list * term list)) list) list ->
    context -> state
end;

structure Proof: PROOF =
struct

type context = ProofContext.context;
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
   {statement: string * term list list,     (*goal kind and statement*)
    using: thm list,                        (*goal facts*)
    goal: thm,                              (*subgoals ==> statement*)
    before_qed: Method.text option,
    after_qed:
      (thm list list -> state -> state Seq.seq) *
      (thm list list -> theory -> theory)};

exception STATE of string * state;

fun make_goal (statement, using, goal, before_qed, after_qed) =
  Goal {statement = statement, using = using, goal = goal,
    before_qed = before_qed, after_qed = after_qed};

fun make_node (context, facts, mode, goal) =
  Node {context = context, facts = facts, mode = mode, goal = goal};

fun map_node f (Node {context, facts, mode, goal}) =
  make_node (f (context, facts, mode, goal));

fun init ctxt = State (Stack.init (make_node (ctxt, NONE, Forward, NONE)));

fun current (State st) = Stack.top st |> (fn Node node => node);
fun map_current f (State st) = State (Stack.map (map_node f) st);



(** basic proof state operations **)

(* block structure *)

fun open_block (State st) = State (Stack.push st);

fun close_block (state as State st) = State (Stack.pop st)
  handle Empty => raise STATE ("Unbalanced block parentheses", state);

fun level (State st) = Stack.level st;

fun assert_bottom b state =
  let val b' = (level state <= 2) in
    if b andalso not b' then raise STATE ("Not at bottom of proof!", state)
    else if not b andalso b' then raise STATE ("Already at bottom of proof!", state)
    else state
  end;


(* context *)

val context_of = #context o current;
val theory_of = ProofContext.theory_of o context_of;
val sign_of = theory_of;

fun map_context f =
  map_current (fn (ctxt, facts, mode, goal) => (f ctxt, facts, mode, goal));

fun map_context_result f state =
  f (context_of state) ||> (fn ctxt => map_context (K ctxt) state);

val warn_extra_tfrees = map_context o ProofContext.warn_extra_tfrees o context_of;
val add_binds_i = map_context o ProofContext.add_binds_i;
val put_thms = map_context o ProofContext.put_thms;
val get_case = ProofContext.get_case o context_of;


(* facts *)

val get_facts = #facts o current;

fun the_facts state =
  (case get_facts state of SOME facts => facts
  | NONE => raise STATE ("No current facts available", state));

fun the_fact state =
  (case the_facts state of [thm] => thm
  | _ => raise STATE ("Single theorem expected", state));

fun put_facts facts =
  map_current (fn (ctxt, _, mode, goal) => (ctxt, facts, mode, goal))
  #> put_thms (AutoBind.thisN, facts);

fun these_factss more_facts (named_factss, state) =
  (named_factss, state |> put_facts (SOME (List.concat (map snd named_factss) @ more_facts)));

fun export_facts inner outer =
  (case get_facts inner of
    NONE => Seq.single (put_facts NONE outer)
  | SOME thms =>
      thms
      |> Seq.map_list (ProofContext.exports (context_of inner) (context_of outer))
      |> Seq.map (fn ths => put_facts (SOME ths) outer));


(* mode *)

val get_mode = #mode o current;
fun put_mode mode = map_current (fn (ctxt, facts, _, goal) => (ctxt, facts, mode, goal));

val mode_name = (fn Forward => "state" | Chain => "chain" | Backward => "prove");

fun assert_mode pred state =
  let val mode = get_mode state in
    if pred mode then state
    else raise STATE ("Illegal application of proof command in "
      ^ quote (mode_name mode) ^ " mode", state)
  end;

val assert_forward = assert_mode (equal Forward);
val assert_chain = assert_mode (equal Chain);
val assert_forward_or_chain = assert_mode (equal Forward orf equal Chain);
val assert_backward = assert_mode (equal Backward);
val assert_no_chain = assert_mode (not_equal Chain);

val enter_forward = put_mode Forward;
val enter_chain = put_mode Chain;
val enter_backward = put_mode Backward;


(* current goal *)

fun current_goal state =
  (case current state of
    {context, goal = SOME (Goal goal), ...} => (context, goal)
  | _ => raise STATE ("No current goal!", state));

fun assert_current_goal g state =
  let val g' = can current_goal state in
    if g andalso not g' then raise STATE ("No goal in this block!", state)
    else if not g andalso g' then raise STATE ("Goal present in this block!", state)
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

fun using_facts using = map_goal I (fn (statement, _, goal, before_qed, after_qed) =>
  (statement, using, goal, before_qed, after_qed));

local
  fun find i state =
    (case try current_goal state of
      SOME (ctxt, goal) => (ctxt, (i, goal))
    | NONE => find (i + 1) (close_block state
        handle STATE _ => raise STATE ("No goal present", state)));
in val find_goal = find 0 end;

fun get_goal state =
  let val (ctxt, (_, {using, goal, ...})) = find_goal state
  in (ctxt, (using, goal)) end;



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

    fun prt_goal (SOME (ctxt, (i, {statement = (kind, _), using, goal, before_qed, after_qed}))) =
          pretty_facts "using " ctxt
            (if mode <> Backward orelse null using then NONE else SOME using) @
          [Pretty.str ("goal" ^ description [kind, levels_up (i div 2),
              subgoals (Thm.nprems_of goal)] ^ ":")] @
          pretty_goals_local ctxt bg (true, ! show_main_goal) (! Display.goals_limit) goal
      | prt_goal NONE = [];

    val prt_ctxt =
      if ! verbose orelse mode = Forward then ProofContext.pretty_context context
      else if mode = Backward then ProofContext.pretty_asms context
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
  let val (ctxt, (_, {goal, ...})) = find_goal state
  in pretty_goals_local ctxt "" (false, main) (! Display.goals_limit) goal end;



(** proof steps **)

(* refine via method *)

local

fun goalN i = "goal" ^ string_of_int i;
fun goals st = map goalN (1 upto Thm.nprems_of st);

fun no_goal_cases st = map (rpair NONE) (goals st);

fun goal_cases st =
  RuleCases.make true NONE (Thm.theory_of_thm st, Thm.prop_of st) (map (rpair []) (goals st));

fun check_theory thy state =
  if subthy (thy, theory_of state) then state
  else raise STATE ("Bad theory of method result: " ^ Context.str_of_thy thy, state);

fun apply_method current_context meth_fun state =
  let
    val (goal_ctxt, (_, {statement, using, goal, before_qed, after_qed})) = find_goal state;
    val meth = meth_fun (if current_context then context_of state else goal_ctxt);
  in
    Method.apply meth using goal |> Seq.map (fn (meth_cases, goal') =>
      state
      |> check_theory (Thm.theory_of_thm goal')
      |> map_goal
          (ProofContext.add_cases false (no_goal_cases goal @ goal_cases goal') #>
           ProofContext.add_cases true meth_cases)
          (K (statement, using, goal', before_qed, after_qed)))
  end;

fun apply_text cc text state =
  let
    val thy = theory_of state;

    fun eval (Method.Basic m) = apply_method cc m
      | eval (Method.Source src) = apply_method cc (Method.method thy src)
      | eval (Method.Then txts) = Seq.EVERY (map eval txts)
      | eval (Method.Orelse txts) = Seq.FIRST (map eval txts)
      | eval (Method.Try txt) = Seq.TRY (eval txt)
      | eval (Method.Repeat1 txt) = Seq.REPEAT1 (eval txt);
  in eval text state end;

in

val refine = apply_text true;
val refine_end = apply_text false;

end;


(* refine via sub-proof *)

local

fun refine_tac rule =
  Tactic.norm_hhf_tac THEN' Tactic.rtac rule THEN_ALL_NEW
    (Tactic.norm_hhf_tac THEN' (SUBGOAL (fn (goal, i) =>
      if can Logic.unprotect (Logic.strip_assums_concl goal) then
        Tactic.etac Drule.protectI i
      else all_tac)));

fun refine_goal print_rule inner raw_rule state =
  let val (outer, (_, {statement, using, goal, before_qed, after_qed})) = find_goal state in
    raw_rule
    |> ProofContext.goal_exports inner outer
    |> Seq.maps (fn rule =>
      (print_rule outer rule;
        goal
        |> FINDGOAL (refine_tac rule)
        |> Seq.map (fn goal' =>
          map_goal I (K (statement, using, goal', before_qed, after_qed)) state)))
  end;

in

fun refine_goals print_rule inner raw_rules =
  Seq.EVERY (map (refine_goal print_rule inner) raw_rules);

end;


(* conclude_goal *)

fun conclude_goal state goal propss =
  let
    val ctxt = context_of state;
    fun err msg = raise STATE (msg, state);

    val ngoals = Thm.nprems_of goal;
    val _ = conditional (ngoals > 0) (fn () =>
      err (Pretty.string_of (Pretty.chunks
        (pretty_goals_local ctxt "" (true, ! show_main_goal) (! Display.goals_limit) goal @
          [Pretty.str (string_of_int ngoals ^ " unsolved goal(s)!")]))));

    val {hyps, thy, ...} = Thm.rep_thm goal;
    val bad_hyps = fold (remove (op aconv)) (ProofContext.assms_of ctxt) hyps;
    val _ = conditional (not (null bad_hyps)) (fn () => err ("Additional hypotheses:\n" ^
        cat_lines (map (ProofContext.string_of_term ctxt) bad_hyps)));

    val th = Goal.conclude goal;
    val _ = conditional (not (Pattern.matches thy
        (Logic.mk_conjunction_list2 propss, Thm.prop_of th))) (fn () =>
      err ("Proved a different theorem:\n" ^ ProofContext.string_of_thm ctxt th));
  in Drule.conj_elim_precise (map length propss) th end;



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

fun gen_fix fix_ctxt args =
  assert_forward
  #> map_context (fix_ctxt args)
  #> put_facts NONE;

in

val fix = gen_fix ProofContext.fix;
val fix_i = gen_fix ProofContext.fix_i;

end;


(* assume etc. *)

local

fun gen_assume asm prep_att exp args state =
  state
  |> assert_forward
  |> map_context_result (asm exp (Attrib.map_specs (prep_att (theory_of state)) args))
  |> these_factss [] |> #2;

in

val assm      = gen_assume ProofContext.assume Attrib.local_attribute;
val assm_i    = gen_assume ProofContext.assume_i (K I);
val assume    = assm ProofContext.export_assume;
val assume_i  = assm_i ProofContext.export_assume;
val presume   = assm ProofContext.export_presume;
val presume_i = assm_i ProofContext.export_presume;

end;


(* def *)

local

fun gen_def fix prep_att prep_binds args state =
  let
    val _ = assert_forward state;
    val thy = theory_of state;

    val ((raw_names, raw_atts), (xs, raw_rhss)) = args |> split_list |>> split_list ||> split_list;
    val names = map (fn ("", x) => Thm.def_name x | (name, _) => name) (raw_names ~~ xs);
    val atts = map (map (prep_att thy)) raw_atts;
    val (rhss, state') = state |> map_context_result (prep_binds false (map swap raw_rhss));
    val eqs = ProofContext.mk_def (context_of state') (xs ~~ rhss);
  in
    state'
    |> fix [(xs, NONE)]
    |> assm_i ProofContext.export_def ((names ~~ atts) ~~ map (fn eq => [(eq, ([], []))]) eqs)
  end;

in

val def = gen_def fix Attrib.local_attribute ProofContext.match_bind;
val def_i = gen_def fix_i (K I) ProofContext.match_bind_i;

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

val note_thmss = gen_thmss ProofContext.note_thmss (K []) I #2 Attrib.local_attribute;
val note_thmss_i = gen_thmss ProofContext.note_thmss_i (K []) I #2 (K I);

val from_thmss =
  gen_thmss ProofContext.note_thmss (K []) chain #2 Attrib.local_attribute o no_binding;
val from_thmss_i = gen_thmss ProofContext.note_thmss_i (K []) chain #2 (K I) o no_binding;

val with_thmss =
  gen_thmss ProofContext.note_thmss the_facts chain #2 Attrib.local_attribute o no_binding;
val with_thmss_i = gen_thmss ProofContext.note_thmss_i the_facts chain #2 (K I) o no_binding;

val local_results = gen_thmss ProofContext.note_thmss_i (K []) I I (K I);
fun global_results kind =
  PureThy.note_thmss_i (Drule.kind kind) o map (apsnd Thm.simple_fact);

fun get_thmss state srcs = the_facts (note_thmss [(("", []), srcs)] state);
fun simple_note_thms name thms = note_thmss_i [((name, []), [(thms, [])])];

end;


(* using *)

local

fun gen_using_thmss note prep_atts args state =
  state
  |> assert_backward
  |> map_context_result (note (Attrib.map_facts (prep_atts (theory_of state)) (no_binding args)))
  |-> (fn named_facts => map_goal I (fn (statement, using, goal, before_qed, after_qed) =>
    (statement, using @ List.concat (map snd named_facts), goal, before_qed, after_qed)));

in

val using_thmss = gen_using_thmss ProofContext.note_thmss Attrib.local_attribute;
val using_thmss_i = gen_using_thmss ProofContext.note_thmss_i (K I);

end;


(* case *)

local

fun gen_invoke_case prep_att (name, xs, raw_atts) state =
  let
    val atts = map (prep_att (theory_of state)) raw_atts;
    val ((lets, asms), state') =
      map_context_result (ProofContext.apply_case (get_case state name xs)) state;
    val assumptions = asms |> map (fn (a, ts) =>
      ((NameSpace.qualified name a, atts), map (rpair ([], [])) ts));
  in
    state'
    |> add_binds_i lets
    |> map_context (ProofContext.qualified_names #> ProofContext.no_base_names)
    |> assume_i assumptions
    |> add_binds_i AutoBind.no_facts
    |> map_context (ProofContext.restore_naming (context_of state))
    |> `the_facts |-> simple_note_thms name
  end;

in

val invoke_case = gen_invoke_case Attrib.local_attribute;
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

fun end_proof bot txt =
  assert_forward
  #> assert_bottom bot
  #> close_block
  #> assert_current_goal true
  #> using_facts []
  #> `before_qed #-> (refine o the_default Method.succeed_text)
  #> Seq.maps (refine (Method.finish_text txt));


(* unstructured refinement *)

fun defer i = assert_no_chain #> refine (Method.Basic (K (Method.defer i)));
fun prefer i = assert_no_chain #> refine (Method.Basic (K (Method.prefer i)));

fun apply text = assert_backward #> refine text #> Seq.map (using_facts []);
fun apply_end text = assert_forward #> refine_end text;



(** goals **)

(* goal names *)

fun prep_names prep_att stmt =
  let
    val (names_attss, propp) = split_list (Attrib.map_specs prep_att stmt);
    val (names, attss) = split_list names_attss;
  in ((names, attss), propp) end;

fun goal_names target name names =
  (case target of NONE => "" | SOME "" => "" | SOME loc => " (in " ^ loc ^ ")") ^
  (if name = "" then "" else " " ^ name) ^
  (case filter_out (equal "") names of [] => ""
  | nms => " " ^ enclose "(" ")" (space_implode " and " (Library.take (7, nms) @
      (if length nms > 7 then ["..."] else []))));


(* generic goals *)

fun check_tvars props state =
  (case fold Term.add_tvars props [] of [] => ()
  | tvars => raise STATE ("Goal statement contains illegal schematic type variable(s): " ^
      commas (map (ProofContext.string_of_typ (context_of state) o TVar) tvars), state));

fun check_vars props state =
  (case fold Term.add_vars props [] of [] => ()
  | vars => warning ("Goal statement contains unbound schematic variable(s): " ^
      commas (map (ProofContext.string_of_term (context_of state) o Var) vars)));

fun generic_goal prepp kind before_qed after_qed raw_propp state =
  let
    val thy = theory_of state;
    val chaining = can assert_chain state;

    val ((propss, after_ctxt), goal_state) =
      state
      |> assert_forward_or_chain
      |> enter_forward
      |> open_block
      |> map_context_result (fn ctxt => swap (prepp (ctxt, raw_propp)));
    val props = List.concat propss;

    val goal = Goal.init (Thm.cterm_of thy (Logic.mk_conjunction_list2 propss));
    val after_qed' = after_qed |>> (fn after_local =>
      fn results => map_context after_ctxt #> after_local results);
  in
    goal_state
    |> tap (check_tvars props)
    |> tap (check_vars props)
    |> put_goal (SOME (make_goal ((kind, propss), [], goal, before_qed, after_qed')))
    |> map_context (ProofContext.add_cases false (AutoBind.cases thy props))
    |> map_context (ProofContext.auto_bind_goal props)
    |> K chaining ? (`the_facts #-> using_facts)
    |> put_facts NONE
    |> open_block
    |> put_goal NONE
    |> enter_backward
    |> K (null props) ? (refine (Method.Basic Method.assumption) #> Seq.hd)
  end;

fun generic_qed state =
  let
    val (goal_ctxt, {statement = (_, stmt), using, goal, before_qed = _, after_qed}) =
      current_goal state;
    val outer_state = state |> close_block;
    val outer_ctxt = context_of outer_state;

    val props =
      List.concat stmt
      |> ProofContext.generalize goal_ctxt outer_ctxt;
    val results =
      stmt
      |> conclude_goal state goal
      |> (Seq.map_list o Seq.map_list) (ProofContext.exports goal_ctxt outer_ctxt);
  in
    outer_state
    |> map_context (ProofContext.auto_bind_facts props)
    |> pair (after_qed, results)
  end;


(* local goals *)

fun local_goal print_results prep_att prepp kind before_qed after_qed stmt state =
  let
    val ((names, attss), propp) = prep_names (prep_att (theory_of state)) stmt;

    fun after_qed' results =
      local_results ((names ~~ attss) ~~ map Thm.simple_fact results)
      #-> (fn res => tap (fn st => print_results (context_of st) ((kind, ""), res) : unit))
      #> after_qed results;
  in
    state
    |> generic_goal prepp (kind ^ goal_names NONE "" names) before_qed (after_qed', K I) propp
    |> warn_extra_tfrees state
  end;

fun local_qed txt =
  end_proof false txt
  #> Seq.map generic_qed
  #> Seq.maps (uncurry (fn ((after_qed, _), results) => Seq.lifts after_qed results));


(* global goals *)

fun global_goal print_results prep_att prepp
    kind before_qed after_qed target (name, raw_atts) stmt ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val thy_ctxt = ProofContext.init thy;

    val atts = map (prep_att thy) raw_atts;
    val ((names, attss), propp) = prep_names (prep_att thy) stmt;

    fun store_results prfx res =
      K (prfx <> "") ? (Sign.add_path prfx #> Sign.no_base_names)
      #> global_results kind ((names ~~ attss) ~~ res)
      #-> (fn res' =>
        (print_results thy_ctxt ((kind, name), res') : unit;
          #2 o global_results kind [((name, atts), List.concat (map #2 res'))]))
      #> Sign.restore_naming thy;

    fun after_qed' results =
      (case target of NONE => I
      | SOME prfx => store_results (NameSpace.base prfx)
          (map (map (ProofContext.export ctxt thy_ctxt
            #> Drule.strip_shyps_warning)) results))
      #> after_qed results;
  in
    init ctxt
    |> generic_goal (prepp #> ProofContext.auto_fix) (kind ^ goal_names target name names)
      before_qed (K Seq.single, after_qed') propp
  end;

fun check_result msg state sq =
  (case Seq.pull sq of
    NONE => raise STATE (msg, state)
  | SOME res => Seq.cons res);

fun global_qeds txt =
  end_proof true txt
  #> Seq.map generic_qed
  #> Seq.maps (fn (((_, after_qed), results), state) =>
    Seq.lift after_qed results (theory_of state)
    |> Seq.map (rpair (context_of state)))
  |> Seq.DETERM;   (*backtracking may destroy theory!*)

fun global_qed txt state =
  state
  |> global_qeds txt
  |> check_result "Failed to finish proof" state
  |> Seq.hd;


(* concluding steps *)

fun local_terminal_proof (text, opt_text) =
  proof (SOME text) #> Seq.maps (local_qed (opt_text, true));

val local_default_proof = local_terminal_proof (Method.default_text, NONE);
val local_immediate_proof = local_terminal_proof (Method.this_text, NONE);
val local_done_proof = proof (SOME Method.done_text) #> Seq.maps (local_qed (NONE, false));
fun local_skip_proof int = local_terminal_proof (Method.sorry_text int, NONE);

fun global_term_proof immed (text, opt_text) state =
  state
  |> proof (SOME text)
  |> check_result "Terminal proof method failed" state
  |> Seq.maps (global_qeds (opt_text, immed))
  |> check_result "Failed to finish proof (after successful terminal method)" state
  |> Seq.hd;

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
      |> transform_error
      |> capture;

    fun after_qed' results =
      refine_goals print_rule (context_of state) (List.concat results)
      #> Seq.maps (after_qed results);
  in
    state
    |> local_goal print_results prep_att prepp "show" before_qed after_qed' stmt
    |> K int ? (fn goal_state =>
      (case test_proof goal_state of
        Result (SOME _) => goal_state
      | Result NONE => raise STATE (fail_msg (context_of goal_state), goal_state)
      | Exn Interrupt => raise Interrupt
      | Exn exn => raise EXCEPTION (exn, fail_msg (context_of goal_state))))
  end;

fun gen_theorem prep_att prepp kind before_qed after_qed target a =
  global_goal ProofDisplay.present_results prep_att prepp kind before_qed after_qed target a;

in

val have = gen_have Attrib.local_attribute ProofContext.bind_propp;
val have_i = gen_have (K I) ProofContext.bind_propp_i;
val show = gen_show Attrib.local_attribute ProofContext.bind_propp;
val show_i = gen_show (K I) ProofContext.bind_propp_i;
val theorem = gen_theorem Attrib.global_attribute ProofContext.bind_propp_schematic;
val theorem_i = gen_theorem (K I) ProofContext.bind_propp_schematic_i;

end;

end;
