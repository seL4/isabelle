(*  Title:      Pure/Isar/proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof states and methods.
*)


(*Jia Meng: added in atp_hook and modified enter_forward. *)

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
  datatype mode = Forward | ForwardChain | Backward
  exception STATE of string * state
  val check_result: string -> state -> 'a Seq.seq -> 'a Seq.seq
  val init_state: theory -> state
  val context_of: state -> context
  val theory_of: state -> theory
  val sign_of: state -> Sign.sg
  val map_context: (context -> context) -> state -> state
  val warn_extra_tfrees: state -> state -> state
  val put_thms: string * thm list -> state -> state
  val reset_thms: string -> state -> state
  val the_facts: state -> thm list
  val the_fact: state -> thm
  val get_goal: state -> context * (thm list * thm)
  val goal_facts: (state -> thm list) -> state -> state
  val get_mode: state -> mode
  val is_chain: state -> bool
  val assert_forward: state -> state
  val assert_forward_or_chain: state -> state
  val assert_backward: state -> state
  val assert_no_chain: state -> state
  val atp_hook: (ProofContext.context * Thm.thm -> unit) ref
  val enter_forward: state -> state
  val verbose: bool ref
  val show_main_goal: bool ref
  val pretty_state: int -> state -> Pretty.T list
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
  val simple_note_thms: string -> thm list -> state -> state
  val note_thmss: ((bstring * context attribute list) *
    (thmref * context attribute list) list) list -> state -> state
  val note_thmss_i: ((bstring * context attribute list) *
    (thm list * context attribute list) list) list -> state -> state
  val with_thmss: ((bstring * context attribute list) *
    (thmref * context attribute list) list) list -> state -> state
  val with_thmss_i: ((bstring * context attribute list) *
    (thm list * context attribute list) list) list -> state -> state
  val using_thmss: ((thmref * context attribute list) list) list -> state -> state
  val using_thmss_i: ((thm list * context attribute list) list) list -> state -> state
  val instantiate_locale: string * (string * context attribute list) -> state
    -> state
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
  val multi_theorem:
    string -> (theory -> theory) ->
    (cterm list -> context -> context -> thm -> thm) ->
    (xstring * (Locale.multi_attribute list * Locale.multi_attribute list list)) option
    -> bstring * theory attribute list -> Locale.multi_attribute Locale.element Locale.elem_expr list
    -> ((bstring * theory attribute list) * (string * (string list * string list)) list) list
    -> theory -> state
  val multi_theorem_i:
    string -> (theory -> theory)  ->
    (cterm list -> context -> context -> thm -> thm) ->
    (string * (Locale.multi_attribute list * Locale.multi_attribute list list)) option
    -> bstring * theory attribute list
    -> Locale.multi_attribute Locale.element_i Locale.elem_expr list
    -> ((bstring * theory attribute list) * (term * (term list * term list)) list) list
    -> theory -> state
  val chain: state -> state
  val from_facts: thm list -> state -> state
  val show: (bool -> state -> state) -> (state -> state Seq.seq) -> bool
    -> ((string * context attribute list) * (string * (string list * string list)) list) list
    -> bool -> state -> state
  val show_i: (bool -> state -> state) -> (state -> state Seq.seq) -> bool
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> bool -> state -> state
  val have: (state -> state Seq.seq) -> bool
    -> ((string * context attribute list) * (string * (string list * string list)) list) list
    -> state -> state
  val have_i: (state -> state Seq.seq) -> bool
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val interpret: (context -> context) -> (state -> state Seq.seq) -> bool
    -> ((string * context attribute list) * (string * (string list * string list)) list) list
    -> state -> state
  val interpret_i: (context -> context) -> (state -> state Seq.seq) -> bool
    -> ((string * context attribute list) * (term * (term list * term list)) list) list
    -> state -> state
  val at_bottom: state -> bool
  val local_qed: (state -> state Seq.seq)
    -> (context -> string * (string * thm list) list -> unit) * (context -> thm -> unit)
    -> state -> state Seq.seq
  val global_qed: (state -> state Seq.seq) -> state
    -> (theory * ((string * string) * (string * thm list) list)) Seq.seq
  val begin_block: state -> state
  val end_block: state -> state Seq.seq
  val next_block: state -> state
  val thisN: string
  val call_atp: bool ref;


end;

structure Proof: PROOF =
struct

(*Jia Meng: by default, no ATP is called. *)
val call_atp = ref false;

(** proof state **)

type context = ProofContext.context;


(* type goal *)

(* CB: four kinds of Isar goals are distinguished:
   - Theorem: global goal in a theory, corresponds to Isar commands theorem,
     lemma and corollary,
   - Have: local goal in a proof, Isar command have
   - Show: local goal in a proof, Isar command show
   - Interpret: local goal in a proof, Isar command interpret
*)

datatype kind =
  Theorem of {kind: string,
    theory_spec: (bstring * theory attribute list) * theory attribute list list,
    locale_spec: (string * (Locale.multi_attribute list * Locale.multi_attribute list list)) option,
    view: cterm list * cterm list, (* target view and includes view *)
    thy_mod: theory -> theory,     (* used in finish_global to modify final
                                      theory, normally set to I; used by
                                      registration command to activate
                                      registrations *)
    export: cterm list -> context -> context -> thm -> thm } |
                                   (* exporter to be used in finish_global *)
  Show of context attribute list list |
  Have of context attribute list list |
  Interpret of {attss: context attribute list list,
    ctxt_mod: context -> context}; (* used in finish_local to modify final
                                      context *)

(* CB: this function prints the goal kind (Isar command), name and target in
   the proof state *)

fun kind_name _ (Theorem {kind = s, theory_spec = ((a, _), _),
        locale_spec = NONE, ...}) = s ^ (if a = "" then "" else " " ^ a)
  | kind_name sg (Theorem {kind = s, theory_spec = ((a, _), _),
        locale_spec = SOME (name, _), ...}) =
      s ^ " (in " ^ Locale.cond_extern sg name ^ ")" ^ (if a = "" then "" else " " ^ a)
  | kind_name _ (Show _) = "show"
  | kind_name _ (Have _) = "have"
  | kind_name _ (Interpret _) = "interpret";

type goal =
 (kind *             (*result kind*)
  string list *      (*result names*)
  term list list) *  (*result statements*)
 (thm list *         (*use facts*)
  thm);              (*goal: subgoals ==> statement*)


(* type mode *)

datatype mode = Forward | ForwardChain | Backward;
val mode_name = (fn Forward => "state" | ForwardChain => "chain" | Backward => "prove");


(* datatype state *)

datatype node =
  Node of
   {context: context,
    facts: thm list option,
    mode: mode,
    goal: (goal * ((state -> state Seq.seq) * bool)) option}
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
    NONE => raise STATE (msg, state)
  | SOME s_sq => Seq.cons s_sq);


fun map_current f (State (Node {context, facts, mode, goal}, nodes)) =
  State (make_node (f (context, facts, mode, goal)), nodes);

fun init_state thy =
  State (make_node (ProofContext.init thy, NONE, Forward, NONE), []);



(** basic proof state operations **)

(* context *)

fun context_of (State (Node {context, ...}, _)) = context;
val theory_of = ProofContext.theory_of o context_of;
val sign_of = ProofContext.sign_of o context_of;

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

fun these_factss (state, named_factss) =
  state |> put_facts (SOME (List.concat (map snd named_factss)));


(* goal *)

local
  fun find i (state as State (Node {goal = SOME goal, ...}, _)) = (context_of state, (i, goal))
    | find i (State (Node {goal = NONE, ...}, node :: nodes)) = find (i + 1) (State (node, nodes))
    | find _ (state as State (_, [])) = err_malformed "find_goal" state;
in val find_goal = find 0 end;

fun get_goal state =
  let val (ctxt, (_, ((_, x), _))) = find_goal state
  in (ctxt, x) end;


(*
(* Jia: added here: get all goals from the state 10/01/05 *)
fun find_all i (state as State (Node {goal = SOME goal, ...}, node::nodes)) = 
    let val others = find_all (i+1) (State (node, nodes))
    in
	(context_of state, (i, goal)) :: others
    end
  | find_all i (State (Node {goal = NONE, ...}, node :: nodes)) = find_all (i + 1) (State (node, nodes))
  | find_all _ (state as State (_, [])) = [];

val find_all_goals = find_all 0;

fun find_all_goals_ctxts state =
    let val all_goals = find_all_goals state
	fun find_ctxt_g [] = []
	  | find_ctxt_g ((ctxt, (_, ((_, (_, thm)), _)))::others) = (ctxt,thm) :: (find_ctxt_g others)
    in
	find_ctxt_g all_goals
    end;
*)

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

val enter_forward_aux = put_mode Forward;
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


(*Jia Meng: a hook to be used for calling ATPs. *)
(* send the entire proof context *)
val atp_hook = ref (fn ctxt_state: ProofContext.context * Thm.thm => ());

(*Jia Meng: the modified version of enter_forward. *)
(*Jia Meng: atp: Proof.state -> unit *)
local
 fun atp state = 
     let val (ctxt, (_, ((_, (_, thm)), _))) = find_goal state
     in
	 (!atp_hook) (ctxt,thm)          
     end;
     
in

 fun enter_forward state = 
   if (!call_atp) then 
   ((atp state; enter_forward_aux state)
                           handle (STATE _) => enter_forward_aux state)
       else (enter_forward_aux state);

end;


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
      [Pretty.str ("goal (" ^ kind_name (sign_of state) kind ^ prt_names names ^
          levels_up (i div 2) ^ subgoals (Thm.nprems_of thm) ^ "):")] @
      pretty_goals_local ctxt begin_goal (true, !show_main_goal) (! Display.goals_limit) thm;

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
      else if mode = ForwardChain then pretty_facts "picking " ctxt facts
      else prt_goal (find_goal state))
  in prts end;

fun pretty_goals main state =
  let val (ctxt, (_, ((_, (_, thm)), _))) = find_goal state
  in pretty_goals_local ctxt "" (false, main) (! Display.goals_limit) thm end;



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

fun mk_goals_cases st =
  RuleCases.make true NONE (sign_of_thm st, prop_of st)
    (map (fn i => "goal" ^ string_of_int i) (1 upto nprems_of st));

fun gen_refine current_context meth_fun state =
  let
    val (goal_ctxt, (_, ((result, (facts, thm)), x))) = find_goal state;
    val Method meth = meth_fun (if current_context then context_of state else goal_ctxt);

    fun refn (thm', cases) =
      state
      |> check_sign (Thm.sign_of_thm thm')
      |> map_goal (ProofContext.add_cases (cases @ mk_goals_cases thm'))
           (K ((result, (facts, thm')), x));
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
      else (err (Pretty.string_of (Pretty.chunks (pretty_goals_local ctxt "" (true, !show_main_goal)
            (! Display.goals_limit) raw_th @
          [Pretty.str (string_of_int ngoals ^ " unsolved goal(s)!")]))));

    val {hyps, sign, ...} = Thm.rep_thm raw_th;
    val tsig = Sign.tsig_of sign;
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


(* note_thmss *)

local

fun gen_note_thmss f args state =
  state
  |> assert_forward
  |> map_context_result (f args)
  |> these_factss;

in

val note_thmss = gen_note_thmss ProofContext.note_thmss;
val note_thmss_i = gen_note_thmss ProofContext.note_thmss_i;

fun simple_note_thms name thms = note_thmss_i [((name, []), [(thms, [])])];

end;


(* with_thmss *)

local

fun gen_with_thmss f args state =
  let val state' = state |> f args
  in state' |> simple_note_thms "" (the_facts state' @ the_facts state) end;

in

val with_thmss = gen_with_thmss note_thmss;
val with_thmss_i = gen_with_thmss note_thmss_i;

end;


(* using_thmss *)

local

fun gen_using_thmss f args state =
  state
  |> assert_backward
  |> map_context_result (f (map (pair ("", [])) args))
  |> (fn (st, named_facts) =>
    let val (_, (_, ((result, (facts, thm)), x))) = find_goal st;
    in st |> map_goal I (K ((result, (facts @ List.concat (map snd named_facts), thm)), x)) end);

in

val using_thmss = gen_using_thmss ProofContext.note_thmss;
val using_thmss_i = gen_using_thmss ProofContext.note_thmss_i;

end;


(* locale instantiation *)

fun instantiate_locale (loc_name, prfx_attribs) state = let
    val facts = if is_chain state then get_facts state else NONE;
  in
    state
    |> assert_forward_or_chain
    |> enter_forward
    |> reset_facts
    |> map_context (Locale.instantiate loc_name prfx_attribs facts)
  end;

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
    |> fix [([x], NONE)]
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
    val assumptions = asms |> map (fn (a, ts) =>
      ((if a = "" then "" else NameSpace.append name a, atts), map (rpair ([], [])) ts));
    val qnames = filter_out (equal "") (map (#1 o #1) assumptions);
  in
    state'
    |> add_binds_i lets
    |> map_context (ProofContext.qualified true)
    |> assume_i assumptions
    |> map_context (ProofContext.hide_thms false qnames)
    |> (fn st => simple_note_thms name (the_facts st) st)
    |> map_context (ProofContext.restore_qualified (context_of state))
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
  |> put_facts (SOME facts)
  |> chain;


(* setup goals *)

val rule_contextN = "rule_context";

fun setup_goal opt_block prepp autofix kind after_qed pr names raw_propp state =
  let
    val (state', (propss, gen_binds)) =
      state
      |> assert_forward_or_chain
      |> enter_forward
      |> opt_block
      |> map_context_result (fn ctxt => prepp (ctxt, raw_propp));
    val sign' = sign_of state';

    val props = List.concat propss;
    val cprop = Thm.cterm_of sign' (Logic.mk_conjunction_list props);
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
    |> put_goal (SOME (((kind, names, propss), ([], goal)),
      (after_qed o map_context gen_binds, pr)))
    |> map_context (ProofContext.add_cases
     (if length props = 1 then
      RuleCases.make true NONE (Thm.sign_of_thm goal, Thm.prop_of goal) [rule_contextN]
      else [(rule_contextN, RuleCases.empty)]))
    |> auto_bind_goal props
    |> (if is_chain state then use_facts else reset_facts)
    |> new_block
    |> enter_backward
  end;

(*global goals*)
fun global_goal prep kind thy_mod export raw_locale a elems concl thy =
  let
    val init = init_state thy;
    val (opt_name, view, locale_ctxt, elems_ctxt, propp) =
      prep (Option.map fst raw_locale) elems (map snd concl) (context_of init);
  in
    init
    |> open_block
    |> map_context (K locale_ctxt)
    |> open_block
    |> map_context (K elems_ctxt)
(* CB: elems_ctxt is an extension of locale_ctxt, see prep_context_statement
   in locale.ML, naming there: ctxt and import_ctxt. *)
    |> setup_goal I ProofContext.bind_propp_schematic_i ProofContext.fix_frees
      (Theorem {kind = kind,
        theory_spec = (a, map (snd o fst) concl),
        locale_spec = (case raw_locale of NONE => NONE | SOME (_, x) => SOME (valOf opt_name, x)),
        view = view,
        thy_mod = thy_mod,
        export = export})
      Seq.single true (map (fst o fst) concl) propp
  end;

val multi_theorem = global_goal Locale.read_context_statement;
val multi_theorem_i = global_goal Locale.cert_context_statement;


(*local goals*)
fun local_goal' prepp kind (check: bool -> state -> state) f pr args int state =
  state
  |> setup_goal open_block prepp (K I) (kind (map (snd o fst) args))
    f pr (map (fst o fst) args) (map snd args)
  |> warn_extra_tfrees state
  |> check int;

fun local_goal prepp kind f pr args = local_goal' prepp kind (K I) f pr args false;

val show = local_goal' ProofContext.bind_propp Show;
val show_i = local_goal' ProofContext.bind_propp_i Show;
val have = local_goal ProofContext.bind_propp Have;
val have_i = local_goal ProofContext.bind_propp_i Have;
fun interpret ctxt_mod = local_goal ProofContext.bind_propp
  (fn attss => Interpret {attss = attss, ctxt_mod = ctxt_mod});
fun interpret_i ctxt_mod = local_goal ProofContext.bind_propp_i
  (fn attss => Interpret {attss = attss, ctxt_mod = ctxt_mod});


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
    val (goal_ctxt, (((kind, names, tss), (_, raw_thm)), (after_qed, pr))) = current_goal state;
    val outer_state = state |> close_block;
    val outer_ctxt = context_of outer_state;

    val ts = List.concat tss;
    val results = prep_result state ts raw_thm;
    val resultq =
      results |> map (ProofContext.export false goal_ctxt outer_ctxt)
      |> Seq.commute |> Seq.map (Library.unflat tss);

    val (attss, opt_solve, ctxt_mod) =
      (case kind of
        Show attss => (attss,
          export_goals goal_ctxt (if pr then print_rule else (K (K ())))
            results, I)
      | Have attss => (attss, Seq.single, I)
      | Interpret {attss, ctxt_mod} => (attss, Seq.single, ctxt_mod)
      | _ => err_malformed "finish_local" state);
  in
    conditional pr (fn () => print_result goal_ctxt
      (kind_name (sign_of state) kind, names ~~ Library.unflat tss results));
    outer_state
    |> auto_bind_facts (ProofContext.generalize goal_ctxt outer_ctxt ts)
(* original version
    |> (fn st => Seq.map (fn res =>
      note_thmss_i ((names ~~ attss) ~~
          map (single o Thm.no_attributes) res) st) resultq)
*)
    |> (fn st => Seq.map (fn res =>
      st |> note_thmss_i ((names ~~ attss) ~~
              map (single o Thm.no_attributes) res)
         |> map_context ctxt_mod) resultq)
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
    val (goal_ctxt, (((kind, names, tss), (_, raw_thm)), _)) = current_goal state;
    val locale_ctxt = context_of (state |> close_block);
    val theory_ctxt = context_of (state |> close_block |> close_block);
    val {kind = k, theory_spec = ((name, atts), attss), locale_spec, view = (target_view, elems_view), thy_mod, export} =
      (case kind of Theorem x => x | _ => err_malformed "finish_global" state);

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
      |> Locale.smart_note_thmss k locale_spec
        ((names ~~ attss) ~~ map (single o Thm.no_attributes) (Library.unflat tss results))
      |> (fn (thy, res) => (thy, res)
          |>> (#1 o Locale.smart_note_thmss k locale_spec
            [((name, atts), [(List.concat (map #2 res), [])])]));
  in (thy_mod theory', ((k, name), results')) end;


(*note: clients should inspect first result only, as backtracking may destroy theory*)
fun global_qed finalize state =
  state
  |> end_proof true
  |> finalize
  |> Seq.map finish_global;



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
