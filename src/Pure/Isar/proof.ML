(*  Title:      Pure/Isar/proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Proof states and methods.
*)

signature BASIC_PROOF =
sig
  val FINDGOAL: (int -> thm -> 'a Seq.seq) -> thm -> 'a Seq.seq
  val HEADGOAL: (int -> thm -> 'a Seq.seq) -> thm -> 'a Seq.seq
end;

signature PROOF =
sig
  include BASIC_PROOF
  type context
  type state
  exception STATE of string * state
  val check_result: string -> state -> 'a Seq.seq -> 'a Seq.seq
  val init_state: theory -> state
  val context_of: state -> context
  val theory_of: state -> theory
  val sign_of: state -> Sign.sg
  val warn_extra_tfrees: state -> state -> state
  val reset_thms: string -> state -> state
  val the_facts: state -> thm list
  val the_fact: state -> thm
  val get_goal: state -> context * (thm list * thm)
  val goal_facts: (state -> thm list) -> state -> state
  val use_facts: state -> state
  val reset_facts: state -> state
  val is_chain: state -> bool
  val assert_forward: state -> state
  val assert_forward_or_chain: state -> state
  val assert_backward: state -> state
  val assert_no_chain: state -> state
  val enter_forward: state -> state
  val verbose: bool ref
  val print_state: int -> state -> unit
  val pretty_goals: bool -> state -> Pretty.T list
  val level: state -> int
  type method
  val method: (thm list -> tactic) -> method
  val method_cases: (thm list -> thm -> (thm * (string * RuleCases.T) list) Seq.seq) -> method
  val refine: (context -> method) -> state -> state Seq.seq
  val refine_end: (context -> method) -> state -> state Seq.seq
  val match_bind: (string list * string) list -> state -> state
  val match_bind_i: (term list * term) list -> state -> state
  val let_bind: (string list * string) list -> state -> state
  val let_bind_i: (term list * term) list -> state -> state
  val simple_have_thms: string -> thm list -> state -> state
  val have_thmss: ((string * context attribute list) *
    (thm list * context attribute list) list) list -> state -> state
  val with_thmss: ((string * context attribute list) *
    (thm list * context attribute list) list) list -> state -> state
  val fix: (string list * string option) list -> state -> state
  val fix_i: (string list * typ option) list -> state -> state
  val assm: ProofContext.exporter
    -> ((string * context attribute list) * (string * (string list * string list)) list) list
    -> state -> state
  val assm_i: ProofContext.exporter
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val assume:
    ((string * context attribute list) * (string * (string list * string list)) list) list
    -> state -> state
  val assume_i: ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val presume:
    ((string * context attribute list) * (string * (string list * string list)) list) list
    -> state -> state
  val presume_i: ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val def: string -> context attribute list -> string *  (string * string list) -> state -> state
  val def_i: string -> context attribute list -> string * (term * term list) -> state -> state
  val invoke_case: string * string option list * context attribute list -> state -> state
  val theorem: string -> xstring option -> context attribute Locale.element list -> bstring
    -> theory attribute list -> string * (string list * string list) -> theory -> state
  val theorem_i: string -> string option -> context attribute Locale.element_i list -> bstring
    -> theory attribute list -> term * (term list * term list) -> theory -> state
  val chain: state -> state
  val from_facts: thm list -> state -> state
  val show: (bool -> state -> state) -> (state -> state Seq.seq) -> string
    -> context attribute list -> string * (string list * string list) -> bool -> state -> state
  val show_i: (bool -> state -> state) -> (state -> state Seq.seq) -> string
    -> context attribute list -> term * (term list * term list) -> bool -> state -> state
  val have: (state -> state Seq.seq) -> string -> context attribute list
    -> string * (string list * string list) -> state -> state
  val have_i: (state -> state Seq.seq) -> string -> context attribute list
    -> term * (term list * term list) -> state -> state
  val at_bottom: state -> bool
  val local_qed: (state -> state Seq.seq)
    -> (context -> {kind: string, name: string, thm: thm} -> unit) *
      (context -> thm -> unit) -> state -> state Seq.seq
  val global_qed: (state -> state Seq.seq) -> state
    -> (theory * {kind: string, name: string, thm: thm}) Seq.seq
  val begin_block: state -> state
  val end_block: state -> state Seq.seq
  val next_block: state -> state
end;

signature PRIVATE_PROOF =
sig
  include PROOF
  val put_data: Object.kind -> ('a -> Object.T) -> 'a -> state -> state
end;

structure Proof: PRIVATE_PROOF =
struct


(** proof state **)

type context = ProofContext.context;


(* type goal *)

datatype kind =
  Theorem of string * string option * theory attribute list |    (*theorem with kind and locale*)
  Show of context attribute list |               (*intermediate result, solving subgoal*)
  Have of context attribute list;                (*intermediate result*)

fun kind_name _ (Theorem (s, None, _)) = s
  | kind_name sg (Theorem (s, Some loc, _)) = s ^ " (in " ^ Locale.cond_extern sg loc ^ ")"
  | kind_name _ (Show _) = "show"
  | kind_name _ (Have _) = "have";

type goal =
 (kind *        (*result kind*)
  string *      (*result name*)
  term) *       (*result statement*)
 (thm list *    (*use facts*)
  thm);         (*goal: subgoals ==> statement*)


(* type mode *)

datatype mode = Forward | ForwardChain | Backward;
val mode_name = (fn Forward => "state" | ForwardChain => "chain" | Backward => "prove");


(* datatype state *)

datatype node =
  Node of
   {context: context,
    facts: thm list option,
    mode: mode,
    goal: (goal * (state -> state Seq.seq)) option}
and state =
  State of
    node *              (*current*)
    node list;          (*parents wrt. block structure*)

fun make_node (context, facts, mode, goal) =
  Node {context = context, facts = facts, mode = mode, goal = goal};


exception STATE of string * state;

fun err_malformed name state =
  raise STATE (name ^ ": internal error -- malformed proof state", state);

fun check_result msg state sq =
  (case Seq.pull sq of
    None => raise STATE (msg, state)
  | Some s_sq => Seq.cons s_sq);


fun map_current f (State (Node {context, facts, mode, goal}, nodes)) =
  State (make_node (f (context, facts, mode, goal)), nodes);

fun init_state thy =
  State (make_node (ProofContext.init thy, None, Forward, None), []);



(** basic proof state operations **)

(* context *)

fun context_of (State (Node {context, ...}, _)) = context;
val theory_of = ProofContext.theory_of o context_of;
val sign_of = ProofContext.sign_of o context_of;

fun map_context f = map_current (fn (ctxt, facts, mode, goal) => (f ctxt, facts, mode, goal));

fun map_context_result f (state as State (Node {context, facts, mode, goal}, nodes)) =
  let val (context', result) = f context
  in (State (make_node (context', facts, mode, goal), nodes), result) end;


fun put_data kind f = map_context o ProofContext.put_data kind f;
val warn_extra_tfrees = map_context o ProofContext.warn_extra_tfrees o context_of;
val add_binds_i = map_context o ProofContext.add_binds_i;
val auto_bind_goal = map_context o ProofContext.auto_bind_goal;
val auto_bind_facts = map_context oo ProofContext.auto_bind_facts;
val put_thms = map_context o ProofContext.put_thms;
val put_thmss = map_context o ProofContext.put_thmss;
val reset_thms = map_context o ProofContext.reset_thms;
val get_case = ProofContext.get_case o context_of;


(* facts *)

fun the_facts (State (Node {facts = Some facts, ...}, _)) = facts
  | the_facts state = raise STATE ("No current facts available", state);

fun the_fact state =
  (case the_facts state of
    [thm] => thm
  | _ => raise STATE ("Single fact expected", state));

fun assert_facts state = (the_facts state; state);
fun get_facts (State (Node {facts, ...}, _)) = facts;


val thisN = "this";

fun put_facts facts state =
  state
  |> map_current (fn (ctxt, _, mode, goal) => (ctxt, facts, mode, goal))
  |> (case facts of None => reset_thms thisN | Some ths => put_thms (thisN, ths));

val reset_facts = put_facts None;

fun these_factss (state, named_factss) =
  state
  |> put_thmss named_factss
  |> put_facts (Some (flat (map #2 named_factss)));


(* goal *)

local
  fun find i (state as State (Node {goal = Some goal, ...}, _)) = (context_of state, (i, goal))
    | find i (State (Node {goal = None, ...}, node :: nodes)) = find (i + 1) (State (node, nodes))
    | find _ (state as State (_, [])) = err_malformed "find_goal" state;
in val find_goal = find 0 end;

fun get_goal state =
  let val (ctxt, (_, ((_, x), _))) = find_goal state
  in (ctxt, x) end;

fun put_goal goal = map_current (fn (ctxt, facts, mode, _) => (ctxt, facts, mode, goal));

fun map_goal f g (State (Node {context, facts, mode, goal = Some goal}, nodes)) =
      State (make_node (f context, facts, mode, Some (g goal)), nodes)
  | map_goal f g (State (nd, node :: nodes)) =
      let val State (node', nodes') = map_goal f g (State (node, nodes))
      in map_context f (State (nd, node' :: nodes')) end
  | map_goal _ _ state = state;

fun goal_facts get state =
  state
  |> map_goal I (fn ((result, (_, thm)), f) => ((result, (get state, thm)), f));

fun use_facts state =
  state
  |> goal_facts the_facts
  |> reset_facts;


(* mode *)

fun get_mode (State (Node {mode, ...}, _)) = mode;
fun put_mode mode = map_current (fn (ctxt, facts, _, goal) => (ctxt, facts, mode, goal));

val enter_forward = put_mode Forward;
val enter_forward_chain = put_mode ForwardChain;
val enter_backward = put_mode Backward;

fun assert_mode pred state =
  let val mode = get_mode state in
    if pred mode then state
    else raise STATE ("Illegal application of proof command in "
      ^ quote (mode_name mode) ^ " mode", state)
  end;

fun is_chain state = get_mode state = ForwardChain;
val assert_forward = assert_mode (equal Forward);
val assert_forward_or_chain = assert_mode (equal Forward orf equal ForwardChain);
val assert_backward = assert_mode (equal Backward);
val assert_no_chain = assert_mode (not_equal ForwardChain);


(* blocks *)

fun level (State (_, nodes)) = length nodes;

fun open_block (State (node, nodes)) = State (node, node :: nodes);

fun new_block state =
  state
  |> open_block
  |> put_goal None;

fun close_block (state as State (_, node :: nodes)) = State (node, nodes)
  | close_block state = raise STATE ("Unbalanced block parentheses", state);



(** print_state **)

val verbose = ProofContext.verbose;

fun pretty_facts _ _ None = []
  | pretty_facts s ctxt (Some ths) =
      [Pretty.big_list (s ^ "this:") (map (ProofContext.pretty_thm ctxt) ths), Pretty.str ""];

fun print_state nr (state as State (Node {context, facts, mode, goal = _}, nodes)) =
  let
    val ref (_, _, begin_goal) = Display.current_goals_markers;

    fun levels_up 0 = ""
      | levels_up 1 = ", 1 level up"
      | levels_up i = ", " ^ string_of_int i ^ " levels up";

    fun subgoals 0 = ""
      | subgoals 1 = ", 1 subgoal"
      | subgoals n = ", " ^ string_of_int n ^ " subgoals";
      
    fun pretty_goal (_, (i, (((kind, name, _), (goal_facts, thm)), _))) =
      pretty_facts "using " context
        (if mode <> Backward orelse null goal_facts then None else Some goal_facts) @
      [Pretty.str ("goal (" ^ kind_name (sign_of state) kind ^
          (if name = "" then "" else " " ^ name) ^
            levels_up (i div 2) ^ subgoals (Thm.nprems_of thm) ^ "):")] @
      Display.pretty_goals_marker begin_goal (! goals_limit) thm;

    val ctxt_prts =
      if ! verbose orelse mode = Forward then ProofContext.pretty_context context
      else if mode = Backward then ProofContext.pretty_asms context
      else [];

    val prts =
     [Pretty.str ("proof (" ^ mode_name mode ^ "): step " ^ string_of_int nr ^
        (if ! verbose then ", depth " ^ string_of_int (length nodes div 2 - 1)
        else "")), Pretty.str ""] @
     (if null ctxt_prts then [] else ctxt_prts @ [Pretty.str ""]) @
     (if ! verbose orelse mode = Forward then
       (pretty_facts "" context facts @ pretty_goal (find_goal state))
      else if mode = ForwardChain then pretty_facts "picking " context facts
      else pretty_goal (find_goal state))
  in Pretty.writeln (Pretty.chunks prts) end;

fun pretty_goals main_goal state =
  let val (_, (_, ((_, (_, thm)), _))) = find_goal state
  in Display.pretty_sub_goals main_goal (! goals_limit) thm end;



(** proof steps **)

(* datatype method *)

datatype method =
  Method of thm list -> thm -> (thm * (string * RuleCases.T) list) Seq.seq;

fun method tac = Method (fn facts => fn st => Seq.map (rpair []) (tac facts st));
val method_cases = Method;


(* refine goal *)

local

fun check_sign sg state =
  if Sign.subsig (sg, sign_of state) then state
  else raise STATE ("Bad signature of result: " ^ Sign.str_of_sg sg, state);

fun gen_refine current_context meth_fun state =
  let
    val (goal_ctxt, (_, ((result, (facts, thm)), f))) = find_goal state;
    val Method meth = meth_fun (if current_context then context_of state else goal_ctxt);

    fun refn (thm', cases) =
      state
      |> check_sign (Thm.sign_of_thm thm')
      |> map_goal (ProofContext.add_cases cases) (K ((result, (facts, thm')), f));
  in Seq.map refn (meth facts thm) end;

in

val refine = gen_refine true;
val refine_end = gen_refine false;

end;


(* goal addressing *)

fun FINDGOAL tac st =
  let fun find (i, n) = if i > n then Seq.fail else Seq.APPEND (tac i, find (i + 1, n))
  in find (1, Thm.nprems_of st) st end;

fun HEADGOAL tac = tac 1;


(* export results *)

fun refine_tac rule =
  Tactic.rtac rule THEN_ALL_NEW (SUBGOAL (fn (goal, i) =>
    if can Logic.dest_goal (Logic.strip_assums_concl goal) then
      Tactic.etac Drule.triv_goal i
    else all_tac));

fun export_goal print_rule raw_rule inner state =
  let
    val (outer, (_, ((result, (facts, thm)), f))) = find_goal state;
    val exp_tac = ProofContext.export true inner outer;
    fun exp_rule rule =
      let
        val _ = print_rule outer rule;
        val thmq = FINDGOAL (refine_tac rule) thm;
      in Seq.map (fn th => map_goal I (K ((result, (facts, th)), f)) state) thmq end;
  in raw_rule |> exp_tac |> (Seq.flat o Seq.map exp_rule) end;

fun transfer_facts inner_state state =
  (case get_facts inner_state of
    None => Seq.single (reset_facts state)
  | Some thms =>
      let
        val exp_tac = ProofContext.export false (context_of inner_state) (context_of state);
        val thmqs = map exp_tac thms;
      in Seq.map (fn ths => put_facts (Some ths) state) (Seq.commute thmqs) end);


(* prepare result *)

fun prep_result state t raw_thm =
  let
    val ctxt = context_of state;
    fun err msg = raise STATE (msg, state);

    val ngoals = Thm.nprems_of raw_thm;
    val _ =
      if ngoals = 0 then ()
      else (Display.print_goals ngoals raw_thm; err (string_of_int ngoals ^ " unsolved goal(s)!"));

    val thm = raw_thm RS Drule.rev_triv_goal;
    val {hyps, prop, sign, ...} = Thm.rep_thm thm;
    val tsig = Sign.tsig_of sign;

    val casms = flat (map #1 (ProofContext.assumptions_of (context_of state)));
    val bad_hyps = Library.gen_rems Term.aconv (hyps, map Thm.term_of casms);
  in
    if not (null bad_hyps) then err ("Additional hypotheses:\n" ^
        cat_lines (map (ProofContext.string_of_term ctxt) bad_hyps))
    else if not (Pattern.matches (Sign.tsig_of (sign_of state)) (t, prop)) then
      err ("Proved a different theorem: " ^ ProofContext.string_of_term ctxt prop)
    else thm
  end;



(*** structured proof commands ***)

(** context **)

(* bind *)

fun gen_bind f x state =
  state
  |> assert_forward
  |> map_context (f x)
  |> reset_facts;

val match_bind = gen_bind (ProofContext.match_bind false);
val match_bind_i = gen_bind (ProofContext.match_bind_i false);
val let_bind = gen_bind (ProofContext.match_bind true);
val let_bind_i = gen_bind (ProofContext.match_bind_i true);


(* have_thmss etc. *)

fun have_thmss args state =
  state
  |> assert_forward
  |> map_context_result (ProofContext.have_thmss args)
  |> these_factss;

fun simple_have_thms name thms = have_thmss [((name, []), [(thms, [])])];

fun with_thmss args state =
  let val state' = state |> have_thmss args
  in state' |> simple_have_thms "" (the_facts state' @ the_facts state) end;


(* fix *)

fun gen_fix f xs state =
  state
  |> assert_forward
  |> map_context (f xs)
  |> reset_facts;

val fix = gen_fix ProofContext.fix;
val fix_i = gen_fix ProofContext.fix_i;


(* assume and presume *)

fun gen_assume f exp args state =
  state
  |> assert_forward
  |> map_context_result (f exp args)
  |> these_factss;

val assm = gen_assume ProofContext.assume;
val assm_i = gen_assume ProofContext.assume_i;
val assume = assm ProofContext.export_assume;
val assume_i = assm_i ProofContext.export_assume;
val presume = assm ProofContext.export_presume;
val presume_i = assm_i ProofContext.export_presume;



(** local definitions **)

fun gen_def fix prep_term prep_pats raw_name atts (x, (raw_rhs, raw_pats)) state =
  let
    val _ = assert_forward state;
    val ctxt = context_of state;

    (*rhs*)
    val name = if raw_name = "" then Thm.def_name x else raw_name;
    val rhs = prep_term ctxt raw_rhs;
    val T = Term.fastype_of rhs;
    val pats = prep_pats T (ProofContext.declare_term rhs ctxt) raw_pats;

    (*lhs*)
    val lhs = ProofContext.bind_skolem ctxt [x] (Free (x, T));
  in
    state
    |> fix [([x], None)]
    |> match_bind_i [(pats, rhs)]
    |> assm_i ProofContext.export_def [((name, atts), [(Logic.mk_equals (lhs, rhs), ([], []))])]
  end;

val def = gen_def fix ProofContext.read_term ProofContext.read_term_pats;
val def_i = gen_def fix_i ProofContext.cert_term ProofContext.cert_term_pats;


(* invoke_case *)

fun invoke_case (name, xs, atts) state =
  let
    val (state', (lets, asms)) =
      map_context_result (ProofContext.apply_case (get_case state name xs)) state;
  in
    state'
    |> add_binds_i lets
    |> assume_i [((name, atts), map (rpair ([], [])) asms)]
  end;



(** goals **)

(* forward chaining *)

fun chain state =
  state
  |> assert_forward
  |> assert_facts
  |> enter_forward_chain;

fun from_facts facts state =
  state
  |> put_facts (Some facts)
  |> chain;


(* setup goals *)

val rule_contextN = "rule_context";

fun setup_goal opt_block prepp autofix kind after_qed name raw_propp state =
  let
    val (state', ([[prop]], gen_binds)) =
      state
      |> assert_forward_or_chain
      |> enter_forward
      |> opt_block
      |> map_context_result (fn ct => prepp (ct, [[raw_propp]]));
    val cprop = Thm.cterm_of (sign_of state') prop;
    val goal = Drule.mk_triv_goal cprop;

    val tvars = Term.term_tvars prop;
    val vars = Term.term_vars prop;
  in
    if null tvars then ()
    else raise STATE ("Goal statement contains illegal schematic type variable(s): " ^
      commas (map (Syntax.string_of_vname o #1) tvars), state);
    if null vars then ()
    else warning ("Goal statement contains unbound schematic variable(s): " ^
      commas (map (ProofContext.string_of_term (context_of state')) vars));
    state'
    |> map_context (autofix prop)
    |> put_goal (Some (((kind, name, prop), ([], goal)), after_qed o map_context gen_binds))
    |> map_context (ProofContext.add_cases (RuleCases.make true goal [rule_contextN]))
    |> auto_bind_goal prop
    |> (if is_chain state then use_facts else reset_facts)
    |> new_block
    |> enter_backward
  end;

(*global goals*)
fun global_goal prepp act_locale act_elems kind locale elems name atts x thy =
  thy |> init_state
  |> open_block |> (case locale of Some loc => map_context (act_locale loc) | None => I)
  |> open_block |> map_context (act_elems elems)
  |> setup_goal I prepp (ProofContext.fix_frees o single) (Theorem (kind, locale, atts))
    Seq.single name x;

val theorem = global_goal ProofContext.bind_propp_schematic
  Locale.activate_locale Locale.activate_elements;

val theorem_i = global_goal ProofContext.bind_propp_schematic_i
  Locale.activate_locale_i Locale.activate_elements_i;


(*local goals*)
fun local_goal' prepp kind (check: bool -> state -> state)
    f name atts args int state =
  state
  |> setup_goal open_block prepp (K I) (kind atts) f name args
  |> warn_extra_tfrees state
  |> check int;

fun local_goal prepp kind f name atts args =
  local_goal' prepp kind (K I) f name atts args false;

val show = local_goal' ProofContext.bind_propp Show;
val show_i = local_goal' ProofContext.bind_propp_i Show;
val have = local_goal ProofContext.bind_propp Have;
val have_i = local_goal ProofContext.bind_propp_i Have;



(** conclusions **)

(* current goal *)

fun current_goal (State (Node {context, goal = Some goal, ...}, _)) = (context, goal)
  | current_goal state = raise STATE ("No current goal!", state);

fun assert_current_goal true (state as State (Node {goal = None, ...}, _)) =
      raise STATE ("No goal in this block!", state)
  | assert_current_goal false (state as State (Node {goal = Some _, ...}, _)) =
      raise STATE ("Goal present in this block!", state)
  | assert_current_goal _ state = state;

fun assert_bottom b (state as State (_, nodes)) =
  let val bot = (length nodes <= 2) in
    if b andalso not bot then raise STATE ("Not at bottom of proof!", state)
    else if not b andalso bot then raise STATE ("Already at bottom of proof!", state)
    else state
  end;

val at_bottom = can (assert_bottom true o close_block);

fun end_proof bot state =
  state
  |> assert_forward
  |> close_block
  |> assert_bottom bot
  |> assert_current_goal true
  |> goal_facts (K []);


(* local_qed *)

fun finish_local (print_result, print_rule) state =
  let
    val (goal_ctxt, (((kind, name, t), (_, raw_thm)), after_qed)) = current_goal state;
    val outer_state = state |> close_block;
    val outer_ctxt = context_of outer_state;

    val result = prep_result state t raw_thm;
    val resultq = ProofContext.export false goal_ctxt outer_ctxt result;

    val (atts, opt_solve) =
      (case kind of
        Show atts => (atts, export_goal print_rule result goal_ctxt)
      | Have atts => (atts, Seq.single)
      | _ => err_malformed "finish_local" state);
  in
    print_result goal_ctxt {kind = kind_name (sign_of state) kind, name = name, thm = result};
    outer_state
    |> auto_bind_facts name [ProofContext.generalize goal_ctxt outer_ctxt t]
    |> (fn st => Seq.map (fn res =>
      have_thmss [((name, atts), [Thm.no_attributes [res]])] st) resultq)
    |> (Seq.flat o Seq.map opt_solve)
    |> (Seq.flat o Seq.map after_qed)
  end;

fun local_qed finalize print state =
  state
  |> end_proof false
  |> finalize
  |> (Seq.flat o Seq.map (finish_local print));


(* global_qed *)

fun finish_global state =
  let
    val (goal_ctxt, (((kind, name, t), (_, raw_thm)), _)) = current_goal state;
    val full_name = if name = "" then "" else Sign.full_name (sign_of state) name;
    val locale_context = context_of (state |> close_block);  (* FIXME unused *)
    val theory_context = context_of (state |> close_block |> close_block);

    val result = prep_result state t raw_thm;
    val resultq =
      ProofContext.export false goal_ctxt theory_context result
      |> Seq.map Drule.local_standard;

    val (atts, opt_locale) =
      (case kind of Theorem (s, loc, atts) => (atts @ [Drule.kind s], loc)
      | _ => err_malformed "finish_global" state);
    val thy = theory_of state;
  in
    resultq |> Seq.map (fn res =>
      let val (thy', res') = PureThy.store_thm ((name, res), atts) thy
      in (thy', {kind = kind_name (sign_of state) kind, name = name, thm = res'}) end)
  end;

(*note: clients should inspect first result only, as backtracking may destroy theory*)
fun global_qed finalize state =
  state
  |> end_proof true
  |> finalize
  |> Seq.map finish_global
  |> Seq.flat;



(** blocks **)

(* begin_block *)

fun begin_block state =
  state
  |> assert_forward
  |> new_block
  |> open_block;


(* end_block *)

fun end_block state =
  state
  |> assert_forward
  |> close_block
  |> assert_current_goal false
  |> close_block
  |> transfer_facts state;


(* next_block *)

fun next_block state =
  state
  |> assert_forward
  |> close_block
  |> new_block
  |> reset_facts;


end;

structure BasicProof: BASIC_PROOF = Proof;
open BasicProof;
