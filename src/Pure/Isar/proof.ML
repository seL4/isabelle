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
  val assert_backward: state -> state
  val enter_forward: state -> state
  val verbose: bool ref
  val print_state: state -> unit
  val level: state -> int
  type method
  val method: (thm list -> tactic) -> method
  val refine: (context -> method) -> state -> state Seq.seq
  val bind: (indexname * string) list -> state -> state
  val bind_i: (indexname * term) list -> state -> state
  val match_bind: (string list * string) list -> state -> state
  val match_bind_i: (term list * term) list -> state -> state
  val have_thmss: string -> context attribute list ->
    (thm list * context attribute list) list -> state -> state
  val assume: (int -> tactic) -> string -> context attribute list -> (string * string list) list
    -> state -> state
  val assume_i: (int -> tactic) -> string -> context attribute list -> (term * term list) list
    -> state -> state
  val fix: (string * string option) list -> state -> state
  val fix_i: (string * typ) list -> state -> state
  val theorem: bstring -> theory attribute list -> string * string list -> theory -> state
  val theorem_i: bstring -> theory attribute list -> term * term list -> theory -> state
  val lemma: bstring -> theory attribute list -> string * string list -> theory -> state
  val lemma_i: bstring -> theory attribute list -> term * term list -> theory -> state
  val chain: state -> state
  val from_facts: thm list -> state -> state
  val show: string -> context attribute list -> string * string list -> state -> state
  val show_i: string -> context attribute list -> term * term list -> state -> state
  val have: string -> context attribute list -> string * string list -> state -> state
  val have_i: string -> context attribute list -> term * term list -> state -> state
  val begin_block: state -> state
  val next_block: state -> state
  val end_block: state -> state
  val at_bottom: state -> bool
  val local_qed: (state -> state Seq.seq) -> ({kind: string, name: string, thm: thm} -> unit)
    -> state -> state Seq.seq
  val global_qed: (state -> state Seq.seq) -> bstring option
    -> theory attribute list option -> state -> (theory * {kind: string, name: string, thm: thm}) Seq.seq
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
 (kind *               		(*result kind*)
  string *                      (*result name*)
  cterm list *			(*result assumptions*)
  (int -> tactic) list *      	(*tactics to solve result assumptions*)
  term) *                       (*result statement*)
 (thm list *                    (*use facts*)
  thm);                         (*goal: subgoals ==> statement*)


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


(* facts *)

fun the_facts (State ({facts = Some facts, ...}, _)) = facts
  | the_facts state = raise STATE ("No current facts available", state);

fun the_fact state =
  (case the_facts state of
    [fact] => fact
  | _ => raise STATE ("Single fact expected", state));

fun assert_facts state = (the_facts state; state);

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
fun fetch_facts (State ({facts, ...}, _)) = put_facts facts;


(* goal *)

fun find_goal i (State ({goal = Some goal, ...}, _)) = (i, goal)
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

fun close_block (State (_, node :: nodes)) = State (node, nodes)
  | close_block state = raise STATE ("Unbalanced block parentheses", state);



(** print_state **)

val verbose = ProofContext.verbose;

fun print_facts _ None = ()
  | print_facts s (Some ths) = Pretty.writeln (Pretty.big_list (s ^ " facts:")
      (map (setmp Display.show_hyps false Display.pretty_thm) ths));

fun print_state (state as State ({context, facts, mode, goal = _}, nodes)) =
  let
    val ref (_, _, begin_goal) = Goals.current_goals_markers;

    fun levels_up 0 = ""
      | levels_up i = " (" ^ string_of_int i ^ " levels up)";

    fun print_goal (i, ((kind, name, _, _, _), (goal_facts, thm))) =
      (print_facts "Using" (if null goal_facts then None else Some goal_facts);
        writeln (kind_name kind ^ " " ^ quote name ^ levels_up (i div 2) ^ ":");
        Locale.print_goals_marker begin_goal (! goals_limit) thm);

    val ctxt_strings = ProofContext.strings_of_context context;
  in
    writeln ("Nesting level: " ^ string_of_int (length nodes div 2));
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
    val (_, (result, (facts, thm))) = find_goal 0 state;

    fun refn thm' =
      state
      |> check_sign (Thm.sign_of_thm thm')
      |> map_goal (K (result, (facts, thm')));
  in Seq.map refn (meth facts thm) end;


(* prepare result *)

fun varify_frees names thm =
  let
    fun get_free x (None, t as Free (y, _)) = if x = y then Some t else None
      | get_free _ (opt, _) = opt;

    fun find_free t x = foldl_aterms (get_free x) (None, t);

    val {sign, maxidx, prop, ...} = Thm.rep_thm thm;
    val frees = map (Thm.cterm_of sign) (mapfilter (find_free prop) names);
  in
    thm
    |> Drule.forall_intr_list frees
    |> Drule.forall_elim_vars (maxidx + 1)
  end;

fun varify_tfrees thm =
  let
    val {hyps, prop, ...} = Thm.rep_thm thm;
    val frees = foldr Term.add_term_frees (prop :: hyps, []);
    val leave_tfrees = foldr Term.add_term_tfree_names (frees, []);
  in thm |> Thm.varifyT' leave_tfrees end;

fun implies_elim_hyps thm =
  foldl (uncurry Thm.implies_elim) (thm, map Thm.assume (Drule.cprems_of thm));


fun prep_result state asms t raw_thm =
  let
    val ctxt = context_of state;
    fun err msg = raise STATE (msg, state);

    val ngoals = Thm.nprems_of raw_thm;
    val _ =
      if ngoals = 0 then ()
      else (Locale.print_goals ngoals raw_thm; err (string_of_int ngoals ^ " unsolved goal(s)!"));

    val thm =
      raw_thm RS Drule.rev_triv_goal
      |> implies_elim_hyps
      |> Drule.implies_intr_list asms
      |> varify_frees (ProofContext.fixed_names ctxt)
      |> varify_tfrees;

    val {hyps, prop, sign, ...} = Thm.rep_thm thm;
    val tsig = Sign.tsig_of sign;
  in
(* FIXME
    if not (Pattern.matches tsig (t, Logic.skip_flexpairs prop)) then
      warning ("Proved a different theorem: " ^ Sign.string_of_term sign prop)
    else ();
*)
    if not (null hyps) then
      err ("Additional hypotheses:\n" ^ cat_lines (map (Sign.string_of_term sign) hyps))
(* FIXME    else if not (Pattern.matches tsig (t, Logic.skip_flexpairs prop)) then
      err ("Proved a different theorem: " ^ Sign.string_of_term sign prop) *)
    else thm
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


(* solve goal *)

fun RANGE [] _ = all_tac
  | RANGE (tac :: tacs) i = RANGE tacs (i + 1) THEN tac i;

fun solve_goal rule tacs state =
  let
    val (_, (result, (facts, thm))) = find_goal 0 state;
    val thms' = FIRSTGOAL (rtac rule THEN' RANGE tacs) thm;
  in Seq.map (fn thm' => map_goal (K (result, (facts, thm'))) state) thms' end;



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

fun have_thmss name atts ths_atts state =
  state
  |> assert_forward
  |> map_context_result (ProofContext.have_thmss (PureThy.default_name name) atts ths_atts)
  |> these_facts;


(* fix *)

fun gen_fix f xs state =
  state
  |> assert_forward
  |> map_context (f xs)
  |> reset_facts;

val fix = gen_fix ProofContext.fix;
val fix_i = gen_fix ProofContext.fix_i;


(* assume *)

fun gen_assume f tac name atts props state =
  state
  |> assert_forward
  |> map_context_result (f tac (PureThy.default_name name) atts props)
  |> (fn (st, (facts, prems)) =>
    (st, facts)
    |> these_facts
    |> put_thms ("prems", prems));

val assume = gen_assume ProofContext.assume;
val assume_i = gen_assume ProofContext.assume_i;



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

fun setup_goal opt_block prepp kind name atts raw_propp state =
  let
    val (state', concl) =
      state
      |> assert_forward_or_chain
      |> enter_forward
      |> opt_block
      |> map_context_result (fn c => prepp (c, raw_propp));
    val cterm_of = Thm.cterm_of (sign_of state);

    val (casms, asm_tacs) = Library.split_list (ProofContext.assumptions (context_of state'));
    val cprems = map cterm_of (Logic.strip_imp_prems concl);
    val prem_tacs = replicate (length cprems) (K all_tac);

    val prop = Logic.list_implies (map Thm.term_of casms, concl);
    val cprop = cterm_of prop;
    val thm = Drule.mk_triv_goal cprop;
  in
    state'
    |> put_goal (Some ((kind atts, (PureThy.default_name name), casms @ cprems,
        asm_tacs @ prem_tacs, prop), ([], thm)))
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



(** blocks **)

(* begin_block *)

fun begin_block state =
  state
  |> assert_forward
  |> new_block
  |> reset_facts
  |> open_block;


(* next_block *)

fun next_block state =
  state
  |> assert_forward
  |> close_block
  |> new_block;



(** conclusions **)

(* current goal *)

fun current_goal (State ({goal = Some goal, ...}, _)) = goal
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


(* finish proof *)

fun finish_proof bot state =
  state
  |> assert_forward
  |> close_block
  |> assert_bottom bot
  |> assert_current_goal true;


(* end_block *)

fun end_block state =
  state
  |> assert_forward
  |> close_block
  |> assert_current_goal false
  |> close_block
  |> fetch_facts state;


(* local_qed *)

fun finish_local print_result state =
  let
    val ((kind, name, asms, tacs, t), (_, raw_thm)) = current_goal state;
    val result = prep_result state asms t raw_thm;
    val (atts, opt_solve) =
      (case kind of
        Goal atts => (atts, solve_goal result tacs)
      | Aux atts => (atts, Seq.single)
      | _ => raise STATE ("No local goal!", state));
  in
    print_result {kind = kind_name kind, name = name, thm = result};
    state
    |> close_block
    |> auto_bind_facts name [t]
    |> have_thmss name atts [Thm.no_attributes [result]]
    |> opt_solve
  end;

fun local_qed finalize print_result state =
  state
  |> finish_proof false
  |> finalize
  |> (Seq.flat o Seq.map (finish_local print_result));


(* global_qed *)

fun finish_global alt_name alt_atts state =
  let
    val ((kind, def_name, asms, _, t), (_, raw_thm)) = current_goal state;
    val result = final_result state (prep_result state asms t raw_thm);

    val name = if_none alt_name def_name;
    val atts =
      (case kind of
        Theorem atts => if_none alt_atts atts
      | Lemma atts => (if_none alt_atts atts) @ [Drule.tag_lemma]
      | _ => raise STATE ("No global goal!", state));

    val (thy', result') = PureThy.store_thm ((name, result), atts) (theory_of state);
  in (thy', {kind = kind_name kind, name = name, thm = result'}) end;

(*Note: should inspect first result only, backtracking may destroy theory*)
fun global_qed finalize alt_name alt_atts state =
  state
  |> finish_proof true
  |> finalize
  |> Seq.map (finish_global alt_name alt_atts);


end;
