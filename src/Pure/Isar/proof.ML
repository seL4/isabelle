(*  Title:      Pure/Isar/proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof states and methods.
*)

signature PROOF =
sig
  type context
  type state
  exception STATE of string * state
  val check_result: string -> state -> 'a Seq.seq -> 'a Seq.seq
  val context_of: state -> context
  val theory_of: state -> theory
  val sign_of: state -> Sign.sg
  val the_facts: state -> thm list
  val the_fact: state -> thm
  val goal_facts: (state -> thm list) -> state -> state
  val use_facts: state -> state
  val reset_facts: state -> state
  val assert_forward: state -> state
  val assert_backward: state -> state
  val enter_forward: state -> state
  val verbose: bool ref
  val print_state: state -> unit
  val level: state -> int
  type method
  val method: (thm list -> tactic) -> method
  val refine: (context -> method) -> state -> state Seq.seq
  val export_thm: context -> thm -> thm
  val bind: (indexname * string) list -> state -> state
  val bind_i: (indexname * term) list -> state -> state
  val match_bind: (string list * string) list -> state -> state
  val match_bind_i: (term list * term) list -> state -> state
  val have_thmss: thm list -> string -> context attribute list ->
    (thm list * context attribute list) list -> state -> state
  val simple_have_thms: string -> thm list -> state -> state
  val fix: (string * string option) list -> state -> state
  val fix_i: (string * typ) list -> state -> state
  val assm: (int -> tactic) * (int -> tactic) -> string -> context attribute list
    -> (string * (string list * string list)) list -> state -> state
  val assm_i: (int -> tactic) * (int -> tactic) -> string -> context attribute list
    -> (term * (term list * term list)) list -> state -> state
  val assume: string -> context attribute list -> (string * (string list * string list)) list
    -> state -> state
  val assume_i: string -> context attribute list -> (term * (term list * term list)) list
    -> state -> state
  val presume: string -> context attribute list -> (string * (string list * string list)) list
    -> state -> state
  val presume_i: string -> context attribute list -> (term * (term list * term list)) list
    -> state -> state
  val theorem: bstring -> theory attribute list -> string * (string list * string list)
    -> theory -> state
  val theorem_i: bstring -> theory attribute list -> term * (term list * term list)
    -> theory -> state
  val lemma: bstring -> theory attribute list -> string * (string list * string list)
    -> theory -> state
  val lemma_i: bstring -> theory attribute list -> term * (term list * term list)
    -> theory -> state
  val chain: state -> state
  val export_chain: state -> state Seq.seq
  val from_facts: thm list -> state -> state
  val show: string -> context attribute list -> string * (string list * string list)
    -> state -> state
  val show_i: string -> context attribute list -> term * (term list * term list)
    -> state -> state
  val have: string -> context attribute list -> string * (string list * string list)
    -> state -> state
  val have_i: string -> context attribute list -> term * (term list * term list)
    -> state -> state
  val at_bottom: state -> bool
  val local_qed: (state -> state Seq.seq) -> ({kind: string, name: string, thm: thm} -> unit)
    -> state -> state Seq.seq
  val global_qed: (state -> state Seq.seq) -> state
    -> (theory * {kind: string, name: string, thm: thm}) Seq.seq
  val begin_block: state -> state
  val end_block: state -> state Seq.seq
  val next_block: state -> state
end;

signature PROOF_PRIVATE =
sig
  include PROOF
  val put_data: Object.kind -> ('a -> Object.T) -> 'a -> state -> state
end;

structure Proof: PROOF_PRIVATE =
struct


(** proof state **)

type context = ProofContext.context;


(* type goal *)

datatype kind =
  Theorem of theory attribute list |    (*top-level theorem*)
  Lemma of theory attribute list |      (*top-level lemma*)
  Goal of context attribute list |      (*intermediate result, solving subgoal*)
  Aux of context attribute list ;       (*intermediate result*)

val kind_name =
  fn Theorem _ => "theorem" | Lemma _ => "lemma" | Goal _ => "show" | Aux _ => "have";

type goal =
 (kind *        (*result kind*)
  string *      (*result name*)
  term) *       (*result statement*)
 (thm list *    (*use facts*)
  thm);         (*goal: subgoals ==> statement*)


(* type mode *)

datatype mode = Forward | ForwardChain | Backward;

val mode_name =
  enclose "`" "'" o
    (fn Forward => "state" | ForwardChain => "chain" | Backward => "prove");


(* type node *)

type node =
 {context: context,
  facts: thm list option,
  mode: mode,
  goal: goal option};

fun make_node (context, facts, mode, goal) =
  {context = context, facts = facts, mode = mode, goal = goal}: node;


(* datatype state *)

datatype state =
  State of
    node *              (*current*)
    node list;          (*parents wrt. block structure*)

exception STATE of string * state;

fun err_malformed name state =
  raise STATE (name ^ ": internal error -- malformed proof state", state);

fun check_result msg state sq =
  (case Seq.pull sq of
    None => raise STATE (msg, state)
  | Some s_sq => Seq.cons s_sq);


fun map_current f (State ({context, facts, mode, goal}, nodes)) =
  State (make_node (f (context, facts, mode, goal)), nodes);

fun init_state thy =
  State (make_node (ProofContext.init thy, None, Forward, None), []);



(** basic proof state operations **)

(* context *)

fun context_of (State ({context, ...}, _)) = context;
val theory_of = ProofContext.theory_of o context_of;
val sign_of = ProofContext.sign_of o context_of;

fun map_context f = map_current (fn (ctxt, facts, mode, goal) => (f ctxt, facts, mode, goal));

fun map_context_result f (state as State ({context, facts, mode, goal}, nodes)) =
  let val (context', result) = f context
  in (State (make_node (context', facts, mode, goal), nodes), result) end;


fun put_data kind f = map_context o ProofContext.put_data kind f;
val declare_term = map_context o ProofContext.declare_term;
val add_binds = map_context o ProofContext.add_binds_i;
val auto_bind_goal = map_context o ProofContext.auto_bind_goal;
val auto_bind_facts = map_context oo ProofContext.auto_bind_facts;
val put_thms = map_context o ProofContext.put_thms;
val put_thmss = map_context o ProofContext.put_thmss;
val assumptions = ProofContext.assumptions o context_of;


(* facts *)

fun the_facts (State ({facts = Some facts, ...}, _)) = facts
  | the_facts state = raise STATE ("No current facts available", state);

fun the_fact state =
  (case the_facts state of
    [fact] => fact
  | _ => raise STATE ("Single fact expected", state));

fun assert_facts state = (the_facts state; state);
fun get_facts (State ({facts, ...}, _)) = facts;

fun put_facts facts state =
  state
  |> map_current (fn (ctxt, _, mode, goal) => (ctxt, facts, mode, goal))
  |> put_thms ("facts", if_none facts []);

val reset_facts = put_facts None;

fun have_facts (name, facts) state =
  state
  |> put_facts (Some facts)
  |> put_thms (name, facts);

fun these_facts (state, ths) = have_facts ths state;


(* goal *)

fun find_goal i (state as State ({goal = Some goal, ...}, _)) = (context_of state, (i, goal))
  | find_goal i (State ({goal = None, ...}, node :: nodes)) =
      find_goal (i + 1) (State (node, nodes))
  | find_goal _ (state as State (_, [])) = err_malformed "find_goal" state;

fun put_goal goal = map_current (fn (ctxt, facts, mode, _) => (ctxt, facts, mode, goal));

fun map_goal f (State ({context, facts, mode, goal = Some goal}, nodes)) =
      State (make_node (context, facts, mode, Some (f goal)), nodes)
  | map_goal f (State (nd, node :: nodes)) =
      let val State (node', nodes') = map_goal f (State (node, nodes))
      in State (nd, node' :: nodes') end
  | map_goal _ state = state;

fun goal_facts get state =
  state
  |> map_goal (fn (result, (_, thm)) => (result, (get state, thm)));

fun use_facts state =
  state
  |> goal_facts the_facts
  |> reset_facts;


(* mode *)

fun get_mode (State ({mode, ...}, _)) = mode;
fun put_mode mode = map_current (fn (ctxt, facts, _, goal) => (ctxt, facts, mode, goal));

val enter_forward = put_mode Forward;
val enter_forward_chain = put_mode ForwardChain;
val enter_backward = put_mode Backward;

fun assert_mode pred state =
  let val mode = get_mode state in
    if pred mode then state
    else raise STATE ("Illegal application of proof command in " ^ mode_name mode ^ " mode", state)
  end;

fun is_chain state = get_mode state = ForwardChain;
val assert_forward = assert_mode (equal Forward);
val assert_forward_or_chain = assert_mode (equal Forward orf equal ForwardChain);
val assert_backward = assert_mode (equal Backward);


(* blocks *)

fun level (State (_, nodes)) = length nodes;

fun open_block (State (node, nodes)) = State (node, node :: nodes);

fun new_block state =
  state
  |> open_block
  |> put_goal None;

fun close_block (state as State (_, node :: nodes)) =
      State (node, nodes)
      |> map_context (ProofContext.transfer_used_names (context_of state))
  | close_block state = raise STATE ("Unbalanced block parentheses", state);



(** print_state **)

val verbose = ProofContext.verbose;

fun print_facts _ None = ()
  | print_facts s (Some ths) = Pretty.writeln (Pretty.big_list (s ^ " facts:")
      (map Display.pretty_thm_no_hyps ths));

fun print_state (state as State ({context, facts, mode, goal = _}, nodes)) =
  let
    val ref (_, _, begin_goal) = Goals.current_goals_markers;

    fun levels_up 0 = ""
      | levels_up 1 = " (1 level up)"
      | levels_up i = " (" ^ string_of_int i ^ " levels up)";

    fun print_goal (_, (i, ((kind, name, _), (goal_facts, thm)))) =
      (print_facts "Using" (if null goal_facts then None else Some goal_facts);
        writeln (kind_name kind ^ " " ^ quote name ^ levels_up (i div 2) ^ ":");
        Locale.print_goals_marker begin_goal (! goals_limit) thm);

    val ctxt_strings = ProofContext.strings_of_context context;
  in
    if ! verbose then writeln ("Nesting level: " ^ string_of_int (length nodes div 2)) else ();
    writeln "";
    writeln (mode_name mode ^ " mode");
    writeln "";
    if ! verbose orelse mode = Forward then
      (if null ctxt_strings then () else (seq writeln ctxt_strings; writeln "");
        print_facts "Current" facts;
        print_goal (find_goal 0 state))
    else if mode = ForwardChain then print_facts "Picking" facts
    else print_goal (find_goal 0 state)
  end;



(** proof steps **)

(* datatype method *)

datatype method = Method of thm list -> tactic;
val method = Method;


(* refine goal *)

fun check_sign sg state =
  if Sign.subsig (sg, sign_of state) then state
  else raise STATE ("Bad signature of result: " ^ Sign.str_of_sg sg, state);

fun refine meth_fun (state as State ({context, ...}, _)) =
  let
    val Method meth = meth_fun context;
    val (_, (_, (result, (facts, thm)))) = find_goal 0 state;

    fun refn thm' =
      state
      |> check_sign (Thm.sign_of_thm thm')
      |> map_goal (K (result, (facts, thm')));
  in Seq.map refn (meth facts thm) end;


(* export *)

local

fun varify_frees fixes thm =
  let
    fun get_free x (None, t as Free (y, _)) = if x = y then Some t else None
      | get_free _ (opt, _) = opt;

    fun find_free t x = foldl_aterms (get_free x) (None, t);

    val {sign, prop, ...} = Thm.rep_thm thm;
    val frees = map (Thm.cterm_of sign) (mapfilter (find_free prop) fixes);
  in
    thm
    |> Drule.forall_intr_list frees
    |> Drule.forall_elim_vars 0
  end;

fun most_general_varify_tfrees thm =
  let
    val {hyps, prop, ...} = Thm.rep_thm thm;
    val frees = foldr Term.add_term_frees (prop :: hyps, []);
    val leave_tfrees = foldr Term.add_term_tfree_names (frees, []);
  in thm |> Thm.varifyT' leave_tfrees end;

fun diff_context inner None = (ProofContext.fixed_names inner, ProofContext.assumptions inner)
  | diff_context inner (Some outer) =
      (ProofContext.fixed_names inner \\ ProofContext.fixed_names outer,
        Library.drop (length (ProofContext.assumptions outer), ProofContext.assumptions inner));

in

fun export fixes casms thm =
  thm
  |> Drule.implies_intr_list casms
  |> varify_frees fixes
  |> most_general_varify_tfrees;

fun export_wrt inner opt_outer =
  let
    val (fixes, asms) = diff_context inner opt_outer;
    val casms = map #1 asms;
    val tacs = map #2 asms;
  in (export fixes casms, tacs) end;

end;


(* export results *)

fun RANGE [] _ = all_tac
  | RANGE (tac :: tacs) i = RANGE tacs (i + 1) THEN tac i;

fun export_goal raw_rule inner state =
  let
    val (outer, (_, (result, (facts, thm)))) = find_goal 0 state;
    val (exp, tacs) = export_wrt inner (Some outer);
    val rule = exp raw_rule;
    val thmq = FIRSTGOAL (Tactic.rtac rule THEN' RANGE (map #1 tacs)) thm;
  in Seq.map (fn th => map_goal (K (result, (facts, th))) state) thmq end;


fun export_thm inner thm =
  let val (exp, tacs) = export_wrt inner None in
    (case Seq.chop (2, RANGE (map #2 tacs) 1 (exp thm)) of
      ([thm'], _) => thm'
    | ([], _) => raise THM ("export: failed", 0, [thm])
    | _ => raise THM ("export: more than one result", 0, [thm]))
  end;


fun export_facts inner_state opt_outer_state state =
  let
    val thms = the_facts inner_state;
    val (exp, tacs) = export_wrt (context_of inner_state) (apsome context_of opt_outer_state);
    val thmqs = map (RANGE (map #2 tacs) 1 o exp) thms;
  in Seq.map (fn ths => put_facts (Some ths) state) (Seq.commute thmqs) end;

fun transfer_facts inner_state state =
  (case get_facts inner_state of
    None => Seq.single (reset_facts state)
  | Some ths => export_facts inner_state (Some state) state);


(* prepare result *)

fun prep_result state t raw_thm =
  let
    val ctxt = context_of state;
    fun err msg = raise STATE (msg, state);

    val ngoals = Thm.nprems_of raw_thm;
    val _ =
      if ngoals = 0 then ()
      else (Locale.print_goals ngoals raw_thm; err (string_of_int ngoals ^ " unsolved goal(s)!"));

    val thm = raw_thm RS Drule.rev_triv_goal;
    val {hyps, prop, sign, maxidx, ...} = Thm.rep_thm thm;
    val tsig = Sign.tsig_of sign;

    val casms = map #1 (assumptions state);
    val bad_hyps = Library.gen_rems Term.aconv (hyps, map Thm.term_of casms);
  in
    if not (null bad_hyps) then
      err ("Additional hypotheses:\n" ^ cat_lines (map (Sign.string_of_term sign) bad_hyps))
(* FIXME    else if not (Pattern.matches tsig (t, Logic.skip_flexpairs prop)) then
      err ("Proved a different theorem: " ^ Sign.string_of_term sign prop) *)
    else Drule.forall_elim_vars (maxidx + 1) thm
  end;


(* prepare final result *)

fun strip_flexflex thm =
  Seq.hd (Thm.flexflex_rule thm) handle THM _ => thm;

fun final_result state pre_thm =
  let
    val thm =
      pre_thm
      |> strip_flexflex
      |> Thm.strip_shyps
      |> Drule.standard;

    val str_of_sort = Sign.str_of_sort (Thm.sign_of_thm thm);
    val xshyps = Thm.extra_shyps thm;
  in
    if not (null xshyps) then
      raise STATE ("Extra sort hypotheses: " ^ commas (map str_of_sort xshyps), state)
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

val bind = gen_bind ProofContext.add_binds;
val bind_i = gen_bind ProofContext.add_binds_i;

val match_bind = gen_bind ProofContext.match_binds;
val match_bind_i = gen_bind ProofContext.match_binds_i;


(* have_thmss *)

fun have_thmss ths name atts ths_atts state =
  state
  |> assert_forward
  |> map_context_result (ProofContext.have_thmss ths (PureThy.default_name name) atts ths_atts)
  |> these_facts;

fun simple_have_thms name thms = have_thmss [] name [] [(thms, [])];


(* fix *)

fun gen_fix f xs state =
  state
  |> assert_forward
  |> map_context (f xs)
  |> reset_facts;

val fix = gen_fix ProofContext.fix;
val fix_i = gen_fix ProofContext.fix_i;


(* assume *)

fun gen_assume f tacs name atts props state =
  state
  |> assert_forward
  |> map_context_result (f tacs (PureThy.default_name name) atts props)
  |> (fn (st, (facts, prems)) =>
    (st, facts)
    |> these_facts
    |> put_thms ("prems", prems));

val assm = gen_assume ProofContext.assume;
val assm_i = gen_assume ProofContext.assume_i;

val assume = assm (assume_tac, K all_tac);
val assume_i = assm_i (assume_tac, K all_tac);
val presume = assm (K all_tac, K all_tac);
val presume_i = assm_i (K all_tac, K all_tac);



(** goals **)

(* forward chaining *)

fun chain state =
  state
  |> assert_forward
  |> assert_facts
  |> enter_forward_chain;

fun export_chain state =
  state
  |> assert_forward
  |> export_facts state None
  |> Seq.map chain;

fun from_facts facts state =
  state
  |> put_facts (Some facts)
  |> chain;


(* setup goals *)

fun setup_goal opt_block prepp kind name atts raw_propp state =
  let
    val (state', prop) =
      state
      |> assert_forward_or_chain
      |> enter_forward
      |> opt_block
      |> map_context_result (fn c => prepp (c, raw_propp));
    val cprop = Thm.cterm_of (sign_of state') prop;
    val casms = map #1 (assumptions state');

    val revcut_rl = Drule.incr_indexes_wrt [] [] (cprop :: casms) [] Drule.revcut_rl;
    fun cut_asm (casm, thm) = Thm.rotate_rule ~1 1 ((Thm.assume casm COMP revcut_rl) RS thm);
    val goal = foldr cut_asm (casms, Drule.mk_triv_goal cprop);
  in
    state'
    |> put_goal (Some ((kind atts, (PureThy.default_name name), prop), ([], goal)))
    |> auto_bind_goal prop
    |> (if is_chain state then use_facts else reset_facts)
    |> new_block
    |> enter_backward
  end;


(*global goals*)
fun global_goal prep kind name atts x thy =
  setup_goal I prep kind name atts x (init_state thy);

val theorem = global_goal ProofContext.bind_propp Theorem;
val theorem_i = global_goal ProofContext.bind_propp_i Theorem;
val lemma = global_goal ProofContext.bind_propp Lemma;
val lemma_i = global_goal ProofContext.bind_propp_i Lemma;


(*local goals*)
fun local_goal prep kind name atts x =
  setup_goal open_block prep kind name atts x;

val show   = local_goal ProofContext.bind_propp Goal;
val show_i = local_goal ProofContext.bind_propp_i Goal;
val have   = local_goal ProofContext.bind_propp Aux;
val have_i = local_goal ProofContext.bind_propp_i Aux;



(** conclusions **)

(* current goal *)

fun current_goal (State ({context, goal = Some goal, ...}, _)) = (context, goal)
  | current_goal state = raise STATE ("No current goal!", state);

fun assert_current_goal true (state as State ({goal = None, ...}, _)) =
      raise STATE ("No goal in this block!", state)
  | assert_current_goal false (state as State ({goal = Some _, ...}, _)) =
      raise STATE ("Goal present in this block!", state)
  | assert_current_goal _ state = state;

fun assert_bottom true (state as State (_, _ :: _)) =
      raise STATE ("Not at bottom of proof!", state)
  | assert_bottom false (state as State (_, [])) =
      raise STATE ("Already at bottom of proof!", state)
  | assert_bottom _ state = state;

val at_bottom = can (assert_bottom true o close_block);

fun end_proof bot state =
  state
  |> assert_forward
  |> close_block
  |> assert_bottom bot
  |> assert_current_goal true;


(* local_qed *)

fun finish_local print_result state =
  let
    val (ctxt, ((kind, name, t), (_, raw_thm))) = current_goal state;
    val result = prep_result state t raw_thm;
    val (atts, opt_solve) =
      (case kind of
        Goal atts => (atts, export_goal result ctxt)
      | Aux atts => (atts, Seq.single)
      | _ => err_malformed "finish_local" state);
  in
    print_result {kind = kind_name kind, name = name, thm = result};
    state
    |> close_block
    |> auto_bind_facts name [t]
    |> have_thmss [] name atts [Thm.no_attributes [result]]
    |> opt_solve
  end;

fun local_qed finalize print_result state =
  state
  |> end_proof false
  |> finalize
  |> (Seq.flat o Seq.map (finish_local print_result));


(* global_qed *)

fun finish_global state =
  let
    val (_, ((kind, name, t), (_, raw_thm))) = current_goal state;
    val result = final_result state (prep_result state t raw_thm);

    val atts =
      (case kind of
        Theorem atts => atts
      | Lemma atts => atts @ [Drule.tag_lemma]
      | _ => err_malformed "finish_global" state);

    val (thy', result') = PureThy.store_thm ((name, result), atts) (theory_of state);
  in (thy', {kind = kind_name kind, name = name, thm = result'}) end;

(*Note: should inspect first result only, backtracking may destroy theory*)
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
  |> assert_current_goal true
  |> new_block;


end;
