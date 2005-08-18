(*  Title:      Pure/Isar/proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isar/VM proof language interpreter.
*)

signature PROOF =
sig
  type context
  type method
  type state
  exception STATE of string * state
  val init: theory -> state
  val context_of: state -> context
  val theory_of: state -> theory
  val sign_of: state -> theory    (*obsolete*)
  val map_context: (context -> context) -> state -> state
  val warn_extra_tfrees: state -> state -> state
  val put_thms: string * thm list -> state -> state
  val reset_thms: string -> state -> state
  val the_facts: state -> thm list
  val the_fact: state -> thm
  val thisN: string
  val get_goal: state -> context * (thm list * thm)
  val goal_facts: (state -> thm list) -> state -> state
  val is_chain: state -> bool
  val assert_forward: state -> state
  val assert_forward_or_chain: state -> state
  val assert_backward: state -> state
  val assert_no_chain: state -> state
  val enter_forward: state -> state
  val level: state -> int
  val show_main_goal: bool ref
  val verbose: bool ref
  val pretty_state: int -> state -> Pretty.T list
  val pretty_goals: bool -> state -> Pretty.T list
  val refine: Method.text -> state -> state Seq.seq
  val refine_end: Method.text -> state -> state Seq.seq
  val match_bind: (string list * string) list -> state -> state
  val match_bind_i: (term list * term) list -> state -> state
  val let_bind: (string list * string) list -> state -> state
  val let_bind_i: (term list * term) list -> state -> state
  val simple_note_thms: string -> thm list -> state -> state
  val note_thmss: ((bstring * Attrib.src list) *
    (thmref * Attrib.src list) list) list -> state -> state
  val note_thmss_i: ((bstring * context attribute list) *
    (thm list * context attribute list) list) list -> state -> state
  val from_thmss: ((thmref * Attrib.src list) list) list -> state -> state
  val from_thmss_i: ((thm list * context attribute list) list) list -> state -> state
  val with_thmss: ((thmref * Attrib.src list) list) list -> state -> state
  val with_thmss_i: ((thm list * context attribute list) list) list -> state -> state
  val using_thmss: ((thmref * Attrib.src list) list) list -> state -> state
  val using_thmss_i: ((thm list * context attribute list) list) list -> state -> state
  val fix: (string list * string option) list -> state -> state
  val fix_i: (string list * typ option) list -> state -> state
  val assm: ProofContext.exporter
    -> ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> state -> state
  val assm_i: ProofContext.exporter
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val assume:
    ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> state -> state
  val assume_i: ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val presume:
    ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> state -> state
  val presume_i: ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val def: string * Attrib.src list -> string *  (string * string list) -> state -> state
  val def_i: string * context attribute list -> string * (term * term list) -> state -> state
  val invoke_case: string * string option list * Attrib.src list -> state -> state
  val invoke_case_i: string * string option list * context attribute list -> state -> state
  val chain: state -> state
  val from_facts: thm list -> state -> state
  val multi_theorem: string -> (thm list * thm list -> theory -> theory) ->
    (cterm list -> context -> context -> thm -> thm) ->
    (xstring * (Attrib.src list * Attrib.src list list)) option ->
    bstring * Attrib.src list -> Locale.element Locale.elem_expr list
    -> ((bstring * Attrib.src list) * (string * (string list * string list)) list) list
    -> theory -> state
  val multi_theorem_i: string -> (thm list * thm list -> theory -> theory) ->
    (cterm list -> context -> context -> thm -> thm) ->
    (string * (Attrib.src list * Attrib.src list list)) option
    -> bstring * theory attribute list
    -> Locale.element_i Locale.elem_expr list
    -> ((bstring * theory attribute list) * (term * (term list * term list)) list) list
    -> theory -> state
  val show: (bool -> state -> state) -> (thm list -> state -> state Seq.seq) -> bool
    -> ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> bool -> state -> state
  val show_i: (bool -> state -> state) -> (thm list -> state -> state Seq.seq) -> bool
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> bool -> state -> state
  val have: (thm list -> state -> state Seq.seq) -> bool
    -> ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> state -> state
  val have_i: (thm list -> state -> state Seq.seq) -> bool
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val at_bottom: state -> bool
  val local_qed: bool -> Method.text option
    -> (context -> string * (string * thm list) list -> unit) *
      (context -> thm -> unit) -> state -> state Seq.seq
  val global_qed: bool -> Method.text option
    -> state -> (theory * context) * ((string * string) * (string * thm list) list)
  val proof: Method.text option -> state -> state Seq.seq
  val local_terminal_proof: Method.text * Method.text option
    -> (context -> string * (string * thm list) list -> unit) *
      (context -> thm -> unit) -> state -> state Seq.seq
  val local_default_proof: (context -> string * (string * thm list) list -> unit) *
    (context -> thm -> unit) -> state -> state Seq.seq
  val local_immediate_proof: (context -> string * (string * thm list) list -> unit) *
    (context -> thm -> unit) -> state -> state Seq.seq
  val local_done_proof: (context -> string * (string * thm list) list -> unit) *
    (context -> thm -> unit) -> state -> state Seq.seq
  val global_terminal_proof: Method.text * Method.text option
    -> state -> (theory * context) * ((string * string) * (string * thm list) list)
  val global_default_proof: state ->
    (theory * context) * ((string * string) * (string * thm list) list)
  val global_immediate_proof: state ->
    (theory * context) * ((string * string) * (string * thm list) list)
  val global_done_proof: state ->
    (theory * context) * ((string * string) * (string * thm list) list)
  val defer: int option -> state -> state Seq.seq
  val prefer: int -> state -> state Seq.seq
  val apply: Method.text -> state -> state Seq.seq
  val apply_end: Method.text -> state -> state Seq.seq
  val begin_block: state -> state
  val next_block: state -> state
  val end_block: state -> state Seq.seq
end;

structure Proof: PROOF =
struct

type context = ProofContext.context;
type method = Method.method;


(** proof state **)

(* type goal *)

datatype kind =
  Theorem of {kind: string,
    theory_spec: (bstring * theory attribute list) * theory attribute list list,
    locale_spec: (string * (Attrib.src list * Attrib.src list list)) option,
    view: cterm list * cterm list,  (* target view and includes view *)
    export: cterm list -> context -> context -> thm -> thm} |
                                   (* exporter to be used in finish_global *)
  Show of context attribute list list |
  Have of context attribute list list;

fun kind_name _ (Theorem {kind = s, theory_spec = ((a, _), _),
        locale_spec = NONE, ...}) = s ^ (if a = "" then "" else " " ^ a)
  | kind_name thy (Theorem {kind = s, theory_spec = ((a, _), _),
        locale_spec = SOME (name, _), ...}) =
      s ^ " (in " ^ Locale.extern thy name ^ ")" ^ (if a = "" then "" else " " ^ a)
  | kind_name _ (Show _) = "show"
  | kind_name _ (Have _) = "have";

type goal =
 (kind *             (*result kind*)
  string list *      (*result names*)
  term list list) *  (*result statements*)
 (thm list *         (*use facts*)
  thm);              (*goal: subgoals ==> statement*)


(* type mode *)

datatype mode = Forward | Chain | Backward;
val mode_name = (fn Forward => "state" | Chain => "chain" | Backward => "prove");


(* datatype state *)

datatype node =
  Node of
   {context: context,
    facts: thm list option,
    mode: mode,
    goal: (goal * (after_qed * bool)) option}
and state =
  State of
    node *              (*current node*)
    node list           (*parent nodes wrt. block structure*)
and after_qed =
  AfterQed of
   (thm list -> state -> state Seq.seq) *      (*after local qed*)
   (thm list * thm list -> theory -> theory);  (*after global qed*)

fun make_node (context, facts, mode, goal) =
  Node {context = context, facts = facts, mode = mode, goal = goal};


exception STATE of string * state;

fun err_malformed name state =
  raise STATE (name ^ ": internal error -- malformed proof state", state);


fun map_current f (State (Node {context, facts, mode, goal}, nodes)) =
  State (make_node (f (context, facts, mode, goal)), nodes);

fun init thy =
  State (make_node (ProofContext.init thy, NONE, Forward, NONE), []);



(** basic proof state operations **)

(* context *)

fun context_of (State (Node {context, ...}, _)) = context;
val theory_of = ProofContext.theory_of o context_of;
val sign_of = theory_of;

fun map_context f = map_current (fn (ctxt, facts, mode, goal) => (f ctxt, facts, mode, goal));

fun map_context_result f (state as State (Node {context, facts, mode, goal}, nodes)) =
  let val (context', result) = f context
  in (State (make_node (context', facts, mode, goal), nodes), result) end;


val warn_extra_tfrees = map_context o ProofContext.warn_extra_tfrees o context_of;
val add_binds_i = map_context o ProofContext.add_binds_i;
val auto_bind_goal = map_context o ProofContext.auto_bind_goal;
val auto_bind_facts = map_context o ProofContext.auto_bind_facts;
val put_thms = map_context o ProofContext.put_thms;
val put_thmss = map_context o ProofContext.put_thmss;
val reset_thms = map_context o ProofContext.reset_thms;
val get_case = ProofContext.get_case o context_of;


(* facts *)

fun the_facts (State (Node {facts = SOME facts, ...}, _)) = facts
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
  |> (case facts of NONE => reset_thms thisN | SOME ths => put_thms (thisN, ths));

val reset_facts = put_facts NONE;

fun these_factss more_facts (state, named_factss) =
  state |> put_facts (SOME (List.concat (map snd named_factss) @ more_facts));


(* goal *)

local
  fun find i (state as State (Node {goal = SOME goal, ...}, _)) = (context_of state, (i, goal))
    | find i (State (Node {goal = NONE, ...}, node :: nodes)) =
        find (i + 1) (State (node, nodes))
    | find _ (state as State (_, [])) = raise STATE ("No goal present", state);
in val find_goal = find 0 end;

fun get_goal state =
  let val (ctxt, (_, ((_, x), _))) = find_goal state
  in (ctxt, x) end;

fun put_goal goal = map_current (fn (ctxt, facts, mode, _) => (ctxt, facts, mode, goal));

fun map_goal f g (State (Node {context, facts, mode, goal = SOME goal}, nodes)) =
      State (make_node (f context, facts, mode, SOME (g goal)), nodes)
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
val enter_forward_chain = put_mode Chain;
val enter_backward = put_mode Backward;

fun assert_mode pred state =
  let val mode = get_mode state in
    if pred mode then state
    else raise STATE ("Illegal application of proof command in "
      ^ quote (mode_name mode) ^ " mode", state)
  end;

fun is_chain state = get_mode state = Chain;
val assert_forward = assert_mode (equal Forward);
val assert_forward_or_chain = assert_mode (equal Forward orf equal Chain);
val assert_backward = assert_mode (equal Backward);
val assert_no_chain = assert_mode (not_equal Chain);


(* blocks *)

fun level (State (_, nodes)) = length nodes;

fun open_block (State (node, nodes)) = State (node, node :: nodes);

fun new_block state =
  state
  |> open_block
  |> put_goal NONE;

fun close_block (state as State (_, node :: nodes)) = State (node, nodes)
  | close_block state = raise STATE ("Unbalanced block parentheses", state);



(** pretty_state **)

val show_main_goal = ref false;
val verbose = ProofContext.verbose;

val pretty_goals_local = Display.pretty_goals_aux o ProofContext.pp;

fun pretty_facts _ _ NONE = []
  | pretty_facts s ctxt (SOME ths) =
      [Pretty.big_list (s ^ "this:") (map (ProofContext.pretty_thm ctxt) ths), Pretty.str ""];

fun pretty_state nr (state as State (Node {context = ctxt, facts, mode, goal = _}, nodes)) =
  let
    val ref (_, _, begin_goal) = Display.current_goals_markers;

    fun levels_up 0 = ""
      | levels_up 1 = ", 1 level up"
      | levels_up i = ", " ^ string_of_int i ^ " levels up";

    fun subgoals 0 = ""
      | subgoals 1 = ", 1 subgoal"
      | subgoals n = ", " ^ string_of_int n ^ " subgoals";

    fun prt_names names =
      (case filter_out (equal "") names of [] => ""
      | nms => " " ^ enclose "(" ")" (space_implode " and " (Library.take (7, nms) @
          (if length nms > 7 then ["..."] else []))));

    fun prt_goal (_, (i, (((kind, names, _), (goal_facts, thm)), _))) =
      pretty_facts "using " ctxt
        (if mode <> Backward orelse null goal_facts then NONE else SOME goal_facts) @
      [Pretty.str ("goal (" ^ kind_name (theory_of state) kind ^ prt_names names ^
          levels_up (i div 2) ^ subgoals (Thm.nprems_of thm) ^ "):")] @
      pretty_goals_local ctxt begin_goal (true, ! show_main_goal) (! Display.goals_limit) thm;

    val ctxt_prts =
      if ! verbose orelse mode = Forward then ProofContext.pretty_context ctxt
      else if mode = Backward then ProofContext.pretty_asms ctxt
      else [];

    val prts =
     [Pretty.str ("proof (" ^ mode_name mode ^ "): step " ^ string_of_int nr ^
        (if ! verbose then ", depth " ^ string_of_int (length nodes div 2 - 1)
        else "")), Pretty.str ""] @
     (if null ctxt_prts then [] else ctxt_prts @ [Pretty.str ""]) @
     (if ! verbose orelse mode = Forward then
       (pretty_facts "" ctxt facts @ prt_goal (find_goal state))
      else if mode = Chain then pretty_facts "picking " ctxt facts
      else prt_goal (find_goal state))
  in prts end;

fun pretty_goals main state =
  let val (ctxt, (_, ((_, (_, thm)), _))) = find_goal state
  in pretty_goals_local ctxt "" (false, main) (! Display.goals_limit) thm end;



(** proof steps **)

(* refine goal *)

local

fun goalN i = "goal" ^ string_of_int i;
fun goals st = map goalN (1 upto Thm.nprems_of st);

fun no_goal_cases st = map (rpair NONE) (goals st);

fun goal_cases st =
  RuleCases.make true NONE (Thm.theory_of_thm st, Thm.prop_of st) (goals st);

fun check_theory thy state =
  if subthy (thy, theory_of state) then state
  else raise STATE ("Bad theory of method result: " ^ Context.str_of_thy thy, state);

fun apply_method current_context meth_fun state =
  let
    val (goal_ctxt, (_, ((result, (facts, st)), x))) = find_goal state;
    val meth = meth_fun (if current_context then context_of state else goal_ctxt);
  in
    Method.apply meth facts st |> Seq.map (fn (st', meth_cases) =>
      state
      |> check_theory (Thm.theory_of_thm st')
      |> map_goal
          (ProofContext.add_cases (no_goal_cases st @ goal_cases st' @ meth_cases))
          (K ((result, (facts, st')), x)))
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


(* export results *)

fun refine_tac rule =
  Tactic.norm_hhf_tac THEN' Tactic.rtac rule THEN_ALL_NEW (SUBGOAL (fn (goal, i) =>
    if can Logic.dest_goal (Logic.strip_assums_concl goal) then
      Tactic.etac Drule.triv_goal i
    else all_tac));

fun export_goal inner print_rule raw_rule state =
  let
    val (outer, (_, ((result, (facts, thm)), x))) = find_goal state;
    val exp_tac = ProofContext.export true inner outer;
    fun exp_rule rule =
      let
        val _ = print_rule outer rule;
        val thmq = FINDGOAL (refine_tac rule) thm;
      in Seq.map (fn th => map_goal I (K ((result, (facts, th)), x)) state) thmq end;
  in raw_rule |> exp_tac |> (Seq.flat o Seq.map exp_rule) end;

fun export_goals inner print_rule raw_rules =
  Seq.EVERY (map (export_goal inner print_rule) raw_rules);

fun transfer_facts inner_state state =
  (case get_facts inner_state of
    NONE => Seq.single (reset_facts state)
  | SOME thms =>
      let
        val exp_tac = ProofContext.export false (context_of inner_state) (context_of state);
        val thmqs = map exp_tac thms;
      in Seq.map (fn ths => put_facts (SOME ths) state) (Seq.commute thmqs) end);


(* prepare result *)

fun prep_result state ts raw_th =
  let
    val ctxt = context_of state;
    fun err msg = raise STATE (msg, state);

    val ngoals = Thm.nprems_of raw_th;
    val _ =
      if ngoals = 0 then ()
      else (err (Pretty.string_of (Pretty.chunks
        (pretty_goals_local ctxt "" (true, !show_main_goal) (! Display.goals_limit) raw_th @
          [Pretty.str (string_of_int ngoals ^ " unsolved goal(s)!")]))));

    val {hyps, thy, ...} = Thm.rep_thm raw_th;
    val tsig = Sign.tsig_of thy;
    val casms = List.concat (map #1 (ProofContext.assumptions_of (context_of state)));
    val bad_hyps = Library.gen_rems Term.aconv (hyps, map Thm.term_of casms);

    val th = raw_th RS Drule.rev_triv_goal;
    val ths = Drule.conj_elim_precise (length ts) th
      handle THM _ => err "Main goal structure corrupted";
  in
    conditional (not (null bad_hyps)) (fn () => err ("Additional hypotheses:\n" ^
        cat_lines (map (ProofContext.string_of_term ctxt) bad_hyps)));
    conditional (exists (not o Pattern.matches tsig) (ts ~~ map Thm.prop_of ths)) (fn () =>
      err ("Proved a different theorem: " ^ Pretty.string_of (ProofContext.pretty_thm ctxt th)));
    ths
  end;



(*** structured proof commands ***)

(** context elements **)

(* bindings *)

local

fun gen_bind f args state =
  state
  |> assert_forward
  |> map_context (f args)
  |> reset_facts;

in

val match_bind = gen_bind (ProofContext.match_bind false);
val match_bind_i = gen_bind (ProofContext.match_bind_i false);
val let_bind = gen_bind (ProofContext.match_bind true);
val let_bind_i = gen_bind (ProofContext.match_bind_i true);

end;


(* fixes *)

local

fun gen_fix fix_ctxt args state =
  state
  |> assert_forward
  |> map_context (fix_ctxt args)
  |> reset_facts;

in

val fix = gen_fix ProofContext.fix;
val fix_i = gen_fix ProofContext.fix_i;

end;


(* assumptions *)

local

fun gen_assume asm prep_att exp args state =
  state
  |> assert_forward
  |> map_context_result (asm exp (Attrib.map_specs (prep_att (theory_of state)) args))
  |> these_factss [];

in

val assm      = gen_assume ProofContext.assume Attrib.local_attribute;
val assm_i    = gen_assume ProofContext.assume_i (K I);
val assume    = assm ProofContext.export_assume;
val assume_i  = assm_i ProofContext.export_assume;
val presume   = assm ProofContext.export_presume;
val presume_i = assm_i ProofContext.export_presume;

end;


(* local definitions *)

local

fun gen_def fix prep_att prep_term prep_pats
    (raw_name, raw_atts) (x, (raw_rhs, raw_pats)) state =
  let
    val _ = assert_forward state;
    val thy = theory_of state;
    val ctxt = context_of state;

    val rhs = prep_term ctxt raw_rhs;
    val T = Term.fastype_of rhs;
    val pats = prep_pats T (ProofContext.declare_term rhs ctxt) raw_pats;
    val lhs = ProofContext.bind_skolem ctxt [x] (Free (x, T));

    val name = if raw_name = "" then Thm.def_name x else raw_name;
    val atts = map (prep_att thy) raw_atts;
  in
    state
    |> fix [([x], NONE)]
    |> match_bind_i [(pats, rhs)]
    |> assm_i ProofContext.export_def [((name, atts), [(Logic.mk_equals (lhs, rhs), ([], []))])]
  end;

in

val def = gen_def fix Attrib.local_attribute ProofContext.read_term ProofContext.read_term_pats;
val def_i = gen_def fix_i (K I) ProofContext.cert_term ProofContext.cert_term_pats;

end;



(** facts **)

(* forward chaining *)

fun chain state =
  state
  |> assert_forward
  |> assert_facts
  |> enter_forward_chain;

fun from_facts facts state =
  state
  |> put_facts (SOME facts)
  |> chain;


(* note / from / with *)

fun no_result args = map (pair ("", [])) args;

local

fun gen_thmss note_ctxt more_facts opt_chain prep_atts args state =
  state
  |> assert_forward
  |> map_context_result (note_ctxt (Attrib.map_facts (prep_atts (theory_of state)) args))
  |> these_factss (more_facts state)
  |> opt_chain;

in

val note_thmss = gen_thmss ProofContext.note_thmss (K []) I Attrib.local_attribute;
val note_thmss_i = gen_thmss ProofContext.note_thmss_i (K []) I (K I);
fun simple_note_thms name thms = note_thmss_i [((name, []), [(thms, [])])];

val from_thmss =
  gen_thmss ProofContext.note_thmss (K []) chain Attrib.local_attribute o no_result;
val from_thmss_i = gen_thmss ProofContext.note_thmss_i (K []) chain (K I) o no_result;

val with_thmss =
  gen_thmss ProofContext.note_thmss the_facts chain Attrib.local_attribute o no_result;
val with_thmss_i = gen_thmss ProofContext.note_thmss_i the_facts chain (K I) o no_result;

end;


(* using *)

local

fun gen_using_thmss note prep_atts args state =
  state
  |> assert_backward
  |> map_context_result (note (Attrib.map_facts (prep_atts (theory_of state)) (no_result args)))
  |> (fn (st, named_facts) =>
    let val (_, (_, ((result, (facts, thm)), x))) = find_goal st;
    in st |> map_goal I (K ((result, (facts @ List.concat (map snd named_facts), thm)), x)) end);

in

val using_thmss = gen_using_thmss ProofContext.note_thmss Attrib.local_attribute;
val using_thmss_i = gen_using_thmss ProofContext.note_thmss_i (K I);

end;


(* case *)

local

fun gen_invoke_case prep_att (name, xs, raw_atts) state =
  let
    val atts = map (prep_att (theory_of state)) raw_atts;
    val (state', (lets, asms)) =
      map_context_result (ProofContext.apply_case (get_case state name xs)) state;
    val assumptions = asms |> map (fn (a, ts) =>
      ((NameSpace.qualified name a, atts), map (rpair ([], [])) ts));
  in
    state'
    |> add_binds_i lets
    |> map_context (ProofContext.no_base_names o ProofContext.qualified_names)
    |> assume_i assumptions
    |> map_context (ProofContext.restore_naming (context_of state))
    |> `the_facts |-> simple_note_thms name
  end;

in

val invoke_case = gen_invoke_case Attrib.local_attribute;
val invoke_case_i = gen_invoke_case (K I);

end;



(** goals **)

(* setup goals *)

local

val rule_contextN = "rule_context";

fun setup_goal opt_block prepp autofix kind after_qed pr names raw_propp state =
  let
    val (state', (propss, gen_binds)) =
      state
      |> assert_forward_or_chain
      |> enter_forward
      |> opt_block
      |> map_context_result (fn ctxt => prepp (ctxt, raw_propp));
    val thy' = theory_of state';

    val AfterQed (after_local, after_global) = after_qed;
    val after_qed' = AfterQed (fn res => after_local res o map_context gen_binds, after_global);

    val props = List.concat propss;
    val cprop = Thm.cterm_of thy' (Logic.mk_conjunction_list props);
    val goal = Drule.mk_triv_goal cprop;

    val tvars = foldr Term.add_term_tvars [] props;
    val vars = foldr Term.add_term_vars [] props;
  in
    if null tvars then ()
    else raise STATE ("Goal statement contains illegal schematic type variable(s): " ^
      commas (map (Syntax.string_of_vname o #1) tvars), state);
    if null vars then ()
    else warning ("Goal statement contains unbound schematic variable(s): " ^
      commas (map (ProofContext.string_of_term (context_of state')) vars));
    state'
    |> map_context (autofix props)
    |> put_goal (SOME (((kind, names, propss), ([], goal)), (after_qed', pr)))
    |> map_context (ProofContext.add_cases
     (if length props = 1 then
      RuleCases.make true NONE (Thm.theory_of_thm goal, Thm.prop_of goal) [rule_contextN]
      else [(rule_contextN, NONE)]))
    |> auto_bind_goal props
    |> (if is_chain state then use_facts else reset_facts)
    |> new_block
    |> enter_backward
  end;

fun global_goal prep_att prep kind after_global export raw_locale (name, atts) elems concl thy =
  let
    val prep_atts = map (prep_att thy);
    val init_state = init thy;
    val (opt_name, view, locale_ctxt, elems_ctxt, propp) =
      prep (Option.map fst raw_locale) elems (map snd concl) (context_of init_state);
  in
    init_state
    |> open_block
    |> map_context (K locale_ctxt)
    |> open_block
    |> map_context (K elems_ctxt)
    |> setup_goal I ProofContext.bind_propp_schematic_i ProofContext.fix_frees
      (Theorem {kind = kind,
        theory_spec = ((name, prep_atts atts), map (prep_atts o snd o fst) concl),
        locale_spec = (case raw_locale of NONE => NONE | SOME (_, x) => SOME (the opt_name, x)),
        view = view,
        export = export})
      (AfterQed (K Seq.single, after_global))
      true (map (fst o fst) concl) propp
  end;

fun local_goal' prep_att prepp kind (check: bool -> state -> state)
    after_local pr raw_args int state =
  let val args = Attrib.map_specs (prep_att (theory_of state)) raw_args in
    state
    |> setup_goal open_block prepp (K I) (kind (map (snd o fst) args))
      (AfterQed (after_local, K I)) pr (map (fst o fst) args) (map snd args)
    |> warn_extra_tfrees state
    |> check int
  end;

fun local_goal prep_att prepp kind f pr args =
  local_goal' prep_att prepp kind (K I) f pr args false;

in

val multi_theorem = global_goal Attrib.global_attribute Locale.read_context_statement;
val multi_theorem_i = global_goal (K I) Locale.cert_context_statement;
val show = local_goal' Attrib.local_attribute ProofContext.bind_propp Show;
val show_i = local_goal' (K I) ProofContext.bind_propp_i Show;
val have = local_goal Attrib.local_attribute ProofContext.bind_propp Have;
val have_i = local_goal (K I) ProofContext.bind_propp_i Have;

end;



(** conclusions **)

(* current goal *)

fun current_goal (State (Node {context, goal = SOME goal, ...}, _)) = (context, goal)
  | current_goal state = raise STATE ("No current goal!", state);

fun assert_current_goal true (state as State (Node {goal = NONE, ...}, _)) =
      raise STATE ("No goal in this block!", state)
  | assert_current_goal false (state as State (Node {goal = SOME _, ...}, _)) =
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
    val (goal_ctxt, (((kind, names, tss), (_, raw_thm)), (AfterQed (after_local, _), pr))) =
      current_goal state;
    val outer_state = state |> close_block;
    val outer_ctxt = context_of outer_state;

    val ts = List.concat tss;
    val results = prep_result state ts raw_thm;
    val resultq =
      results |> map (ProofContext.export false goal_ctxt outer_ctxt)
      |> Seq.commute |> Seq.map (Library.unflat tss);

    val (attss, opt_solve) =
      (case kind of
        Show attss => (attss,
          export_goals goal_ctxt (if pr then print_rule else (K (K ()))) results)
      | Have attss => (attss, Seq.single)
      | _ => err_malformed "finish_local" state);
  in
    conditional pr (fn () => print_result goal_ctxt
      (kind_name (theory_of state) kind, names ~~ Library.unflat tss results));
    outer_state
    |> auto_bind_facts (ProofContext.generalize goal_ctxt outer_ctxt ts)
    |> (fn st => Seq.map (fn res =>
      note_thmss_i ((names ~~ attss) ~~ map (single o Thm.no_attributes) res) st) resultq)
    |> (Seq.flat o Seq.map opt_solve)
    |> (Seq.flat o Seq.map (after_local results))
  end;

fun local_qed asm opt_text print state =
  state
  |> end_proof false
  |> refine (Method.finish_text asm opt_text)
  |> (Seq.flat o Seq.map (finish_local print));


(* global_qed *)

fun check_result msg state sq =
  (case Seq.pull sq of
    NONE => raise STATE (msg, state)
  | SOME res => Seq.cons res);

fun finish_global state =
  let
    val (goal_ctxt, (((kind, names, tss), (_, raw_thm)), (AfterQed (_, after_global), _))) =
      current_goal state;
    val locale_ctxt = context_of (state |> close_block);
    val theory_ctxt = context_of (state |> close_block |> close_block);
    val {kind = k, theory_spec = ((name, atts), attss),
        locale_spec, view = (target_view, elems_view), export} =
      (case kind of Theorem x => x | _ => err_malformed "finish_global" state);
    val locale_name = Option.map fst locale_spec;

    val ts = List.concat tss;
    val locale_results = map (export elems_view goal_ctxt locale_ctxt)
      (prep_result state ts raw_thm);

    val results = map (Drule.strip_shyps_warning o
      export target_view locale_ctxt theory_ctxt) locale_results;

    val (theory', results') =
      theory_of state
      |> (case locale_spec of NONE => I
                            | SOME (loc, (loc_atts, loc_attss)) => fn thy =>
        if length names <> length loc_attss then
          raise THEORY ("Bad number of locale attributes", [thy])
        else (thy, locale_ctxt)
          |> Locale.add_thmss k loc ((names ~~ Library.unflat tss locale_results) ~~ loc_attss)
          |> (fn ((thy', ctxt'), res) =>
            if name = "" andalso null loc_atts then thy'
            else (thy', ctxt')
              |> (#1 o #1 o Locale.add_thmss k loc [((name, List.concat (map #2 res)), loc_atts)])))
      |> Locale.smart_note_thmss k locale_name
        ((names ~~ attss) ~~ map (single o Thm.no_attributes) (Library.unflat tss results))
      |> (fn (thy, res) => (thy, res)
          |>> (#1 o Locale.smart_note_thmss k locale_name
            [((name, atts), [(List.concat (map #2 res), [])])]));
  in ((after_global (locale_results, results) theory', locale_ctxt), ((k, name), results')) end;

fun global_qeds asm opt_text =
  end_proof true
  #> refine (Method.finish_text asm opt_text)
  #> Seq.map finish_global
  |> Seq.DETERM;   (*backtracking may destroy theory!*)

fun global_qed asm opt_text state =
  state
  |> global_qeds asm opt_text
  |> check_result "Failed to finish proof" state
  |> Seq.hd;


(* structured proof steps *)

fun proof opt_text state =
  state
  |> assert_backward
  |> refine (if_none opt_text Method.default_text)
  |> Seq.map (goal_facts (K []))
  |> Seq.map enter_forward;

fun local_terminal_proof (text, opt_text) pr =
  Seq.THEN (proof (SOME text), local_qed true opt_text pr);

val local_default_proof = local_terminal_proof (Method.default_text, NONE);
val local_immediate_proof = local_terminal_proof (Method.this_text, NONE);
fun local_done_proof pr = Seq.THEN (proof (SOME Method.done_text), local_qed false NONE pr);

fun global_term_proof asm (text, opt_text) state =
  state
  |> proof (SOME text)
  |> check_result "Terminal proof method failed" state
  |> (Seq.flat o Seq.map (global_qeds asm opt_text))
  |> check_result "Failed to finish proof (after successful terminal method)" state
  |> Seq.hd;

val global_terminal_proof = global_term_proof true;
val global_default_proof = global_terminal_proof (Method.default_text, NONE);
val global_immediate_proof = global_terminal_proof (Method.this_text, NONE);
val global_done_proof = global_term_proof false (Method.done_text, NONE);


(* unstructured proof steps *)

fun defer i = assert_no_chain #> refine (Method.Basic (K (Method.defer i)));
fun prefer i = assert_no_chain #> refine (Method.Basic (K (Method.prefer i)));

fun apply text =
  assert_backward
  #> refine text
  #> Seq.map (goal_facts (K []));

fun apply_end text =
  assert_forward
  #> refine_end text;



(** blocks **)

fun begin_block state =
  state
  |> assert_forward
  |> new_block
  |> open_block;

fun next_block state =
  state
  |> assert_forward
  |> close_block
  |> new_block
  |> reset_facts;

fun end_block state =
  state
  |> assert_forward
  |> close_block
  |> assert_current_goal false
  |> close_block
  |> transfer_facts state;

end;
