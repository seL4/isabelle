(*  Title:      Pure/Isar/proof.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Proof states and methods.
*)

signature BASIC_PROOF =
sig
  val RANGE: (int -> tactic) list -> int -> tactic
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
  val get_goal: state -> term * (thm list * thm)
  val goal_facts: (state -> thm list) -> state -> state
  val use_facts: state -> state
  val reset_facts: state -> state
  val is_chain: state -> bool
  val assert_forward: state -> state
  val assert_forward_or_chain: state -> state
  val assert_backward: state -> state
  val assert_no_chain: state -> state
  val enter_forward: state -> state
  val show_hyps: bool ref
  val pretty_thm: thm -> Pretty.T
  val pretty_thms: thm list -> Pretty.T
  val verbose: bool ref
  val print_state: int -> state -> unit
  val pretty_goals: bool -> state -> Pretty.T list
  val level: state -> int
  type method
  val method: (thm list -> tactic) -> method
  val method_cases: (thm list -> thm -> (thm * (string * RuleCases.T) list) Seq.seq) -> method
  val refine: (context -> method) -> state -> state Seq.seq
  val refine_end: (context -> method) -> state -> state Seq.seq
  val export_thm: context -> thm -> thm
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
  val norm_hhf_tac: int -> tactic
  val hard_asm_tac: int -> tactic
  val soft_asm_tac: int -> tactic
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
  val invoke_case: string * context attribute list -> state -> state
  val theorem: bstring -> theory attribute list -> string * (string list * string list)
    -> theory -> state
  val theorem_i: bstring -> theory attribute list -> term * (term list * term list)
    -> theory -> state
  val lemma: bstring -> theory attribute list -> string * (string list * string list)
    -> theory -> state
  val lemma_i: bstring -> theory attribute list -> term * (term list * term list)
    -> theory -> state
  val chain: state -> state
  val from_facts: thm list -> state -> state
  val show: (state -> state Seq.seq) -> string -> context attribute list
    -> string * (string list * string list) -> state -> state
  val show_i: (state -> state Seq.seq) -> string -> context attribute list
    -> term * (term list * term list) -> state -> state
  val have: (state -> state Seq.seq) -> string -> context attribute list
    -> string * (string list * string list) -> state -> state
  val have_i: (state -> state Seq.seq) -> string -> context attribute list
    -> term * (term list * term list) -> state -> state
  val at_bottom: state -> bool
  val local_qed: (state -> state Seq.seq)
    -> ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit) -> state -> state Seq.seq
  val name_refN: string
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
  Theorem of theory attribute list |    (*top-level theorem*)
  Lemma of theory attribute list |      (*top-level lemma*)
  Show of context attribute list |      (*intermediate result, solving subgoal*)
  Have of context attribute list ;       (*intermediate result*)

val kind_name =
  fn Theorem _ => "theorem" | Lemma _ => "lemma" | Show _ => "show" | Have _ => "have";

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
val auto_bind_goal = map_context o ProofContext.auto_bind_goal;
val auto_bind_facts = map_context oo ProofContext.auto_bind_facts;
val put_thms = map_context o ProofContext.put_thms;
val put_thmss = map_context o ProofContext.put_thmss;
val reset_thms = map_context o ProofContext.reset_thms;
val assumptions = ProofContext.assumptions o context_of;
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

fun find_goal i (state as State (Node {goal = Some goal, ...}, _)) = (context_of state, (i, goal))
  | find_goal i (State (Node {goal = None, ...}, node :: nodes)) =
      find_goal (i + 1) (State (node, nodes))
  | find_goal _ (state as State (_, [])) = err_malformed "find_goal" state;

fun get_goal state =
  let val (_, (_, (((_, _, t), goal), _))) = find_goal 0 state
  in (t, goal) end;

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
    else raise STATE ("Illegal application of proof command in " ^ quote (mode_name mode) ^ " mode", state)
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

val show_hyps = ProofContext.show_hyps;
val pretty_thm = ProofContext.pretty_thm;

fun pretty_thms [th] = pretty_thm th
  | pretty_thms ths = Pretty.blk (0, Pretty.fbreaks (map pretty_thm ths));


val verbose = ProofContext.verbose;

fun pretty_facts _ None = []
  | pretty_facts s (Some ths) =
      [Pretty.big_list (s ^ "this:") (map pretty_thm ths), Pretty.str ""];

fun print_state nr (state as State (Node {context, facts, mode, goal = _}, nodes)) =
  let
    val ref (_, _, begin_goal) = Goals.current_goals_markers;

    fun levels_up 0 = ""
      | levels_up 1 = ", 1 level up"
      | levels_up i = ", " ^ string_of_int i ^ " levels up";

    fun pretty_goal (_, (i, (((kind, name, _), (goal_facts, thm)), _))) =
      pretty_facts "using "
        (if mode <> Backward orelse null goal_facts then None else Some goal_facts) @
      [Pretty.str ("goal (" ^ kind_name kind ^ (if name = "" then "" else " " ^ name) ^
        levels_up (i div 2) ^ "):")] @
      Locale.pretty_goals_marker begin_goal (! goals_limit) thm;

    val ctxt_prts =
      if ! verbose orelse mode = Forward then ProofContext.pretty_context context
      else if mode = Backward then ProofContext.pretty_prems context
      else [];

    val prts =
     [Pretty.str ("proof (" ^ mode_name mode ^ "): step " ^ string_of_int nr ^
        (if ! verbose then ", depth " ^ string_of_int (length nodes div 2)
        else "")), Pretty.str ""] @
     (if null ctxt_prts then [] else ctxt_prts @ [Pretty.str ""]) @
     (if ! verbose orelse mode = Forward then
       (pretty_facts "" facts @ pretty_goal (find_goal 0 state))
      else if mode = ForwardChain then pretty_facts "picking " facts
      else pretty_goal (find_goal 0 state))
  in Pretty.writeln (Pretty.chunks prts) end;

fun pretty_goals main_goal state =
  let val (_, (_, ((_, (_, thm)), _))) = find_goal 0 state
  in Locale.pretty_sub_goals main_goal (!goals_limit) thm end;



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
    val (goal_ctxt, (_, ((result, (facts, thm)), f))) = find_goal 0 state;
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


(* tacticals *)

fun RANGE [] _ = all_tac
  | RANGE (tac :: tacs) i = RANGE tacs (i + 1) THEN tac i;

fun FINDGOAL tac st =
  let fun find (i, n) = if i > n then Seq.fail else Seq.APPEND (tac i, find (i + 1, n))
  in find (1, Thm.nprems_of st) st end;

fun HEADGOAL tac = tac 1;


(* export results *)

fun export_goal print_rule raw_rule inner state =
  let
    val (outer, (_, ((result, (facts, thm)), f))) = find_goal 0 state;
    val (exp_tac, tacs) = ProofContext.export_wrt true inner (Some outer);
    fun exp_rule rule =
      let
        val _ = print_rule rule;
        val thmq = FINDGOAL (Tactic.rtac rule THEN' RANGE tacs) thm;
      in Seq.map (fn th => map_goal I (K ((result, (facts, th)), f)) state) thmq end;
  in raw_rule |> exp_tac |> (Seq.flat o Seq.map exp_rule) end;

fun export_thm inner thm =
  let val (exp_tac, tacs) = ProofContext.export_wrt false inner None in
    (case Seq.chop (2, (exp_tac THEN RANGE tacs 1) thm) of
      ([thm'], _) => thm'
    | ([], _) => raise THM ("export: failed", 0, [thm])
    | _ => raise THM ("export: more than one result", 0, [thm]))
  end;

fun transfer_facts inner_state state =
  (case get_facts inner_state of
    None => Seq.single (reset_facts state)
  | Some thms =>
      let
        val (exp_tac, tacs) =
          ProofContext.export_wrt false (context_of inner_state) (Some (context_of state));
        val thmqs = map (exp_tac THEN RANGE tacs 1) thms;
      in Seq.map (fn ths => put_facts (Some ths) state) (Seq.commute thmqs) end);


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
    val {hyps, prop, sign, ...} = Thm.rep_thm thm;
    val tsig = Sign.tsig_of sign;

    val casms = flat (map #1 (assumptions state));
    val bad_hyps = Library.gen_rems Term.aconv (hyps, map (Thm.term_of o Drule.mk_cgoal) casms);
  in
    if not (null bad_hyps) then
      err ("Additional hypotheses:\n" ^ cat_lines (map (Sign.string_of_term sign) bad_hyps))
    else if not (t aconv prop) then
      err ("Proved a different theorem: " ^ Sign.string_of_term sign prop)
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


(* assume *)

val norm_hhf_tac = Tactic.rewrite_goal_tac [Drule.norm_hhf_eq];
val hard_asm_tac = Tactic.etac Drule.triv_goal;
val soft_asm_tac = Tactic.rtac Drule.triv_goal THEN' norm_hhf_tac;

local

fun gen_assume f exp args state =
  state
  |> assert_forward
  |> map_context_result (f exp args)
  |> (fn (st, (factss, prems)) =>
    these_factss (st, factss)
    |> put_thms ("prems", prems));

fun simple_exporter tac1 tac2 =
  (Seq.single oo Drule.implies_intr_list,
    fn is_goal => fn n => replicate n (norm_hhf_tac THEN' (if is_goal then tac1 else tac2)));

in

val assm = gen_assume ProofContext.assume;
val assm_i = gen_assume ProofContext.assume_i;
val assume = assm (simple_exporter hard_asm_tac soft_asm_tac);
val assume_i = assm_i (simple_exporter hard_asm_tac soft_asm_tac);
val presume = assm (simple_exporter soft_asm_tac soft_asm_tac);
val presume_i = assm_i (simple_exporter soft_asm_tac soft_asm_tac);

end;


(* invoke_case *)

fun invoke_case (name, atts) state =
  let
    val (vars, props) = get_case state name;
    val bind_skolem = ProofContext.bind_skolem (context_of state) (map #1 vars);
  in
    state
    |> fix_i (map (fn (x, T) => ([x], Some T)) vars)
    |> assume_i [((name, atts), map (fn t => (t, ([], []))) (map bind_skolem props))]
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

val antN = "antecedent";

fun setup_goal opt_block prepp kind after_qed name atts raw_propp state =
  let
    val (state', ([[prop]], gen_binds)) =
      state
      |> assert_forward_or_chain
      |> enter_forward
      |> opt_block
      |> map_context_result (fn ct => prepp (ct, [[raw_propp]]));
    val cprop = Thm.cterm_of (sign_of state') prop;
    val goal = Drule.mk_triv_goal cprop;
  in
    state'
    |> put_goal (Some (((kind atts, name, prop), ([], goal)), after_qed o map_context gen_binds))
    |> map_context (ProofContext.add_cases (RuleCases.make true goal [antN]))
    |> auto_bind_goal prop
    |> (if is_chain state then use_facts else reset_facts)
    |> new_block
    |> enter_backward
  end;


(*global goals*)
fun global_goal prepp kind name atts x thy =
  setup_goal I prepp kind Seq.single name atts x (init_state thy);

val theorem = global_goal ProofContext.bind_propp Theorem;
val theorem_i = global_goal ProofContext.bind_propp_i Theorem;
val lemma = global_goal ProofContext.bind_propp Lemma;
val lemma_i = global_goal ProofContext.bind_propp_i Lemma;


(*local goals*)
fun local_goal prepp kind f name atts args state =
  state
  |> setup_goal open_block prepp kind f name atts args
  |> warn_extra_tfrees state;

val show   = local_goal ProofContext.bind_propp Show;
val show_i = local_goal ProofContext.bind_propp_i Show;
val have   = local_goal ProofContext.bind_propp Have;
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
  |> assert_current_goal true
  |> goal_facts (K []);


(* local_qed *)

fun finish_local (print_result, print_rule) state =
  let
    val (goal_ctxt, (((kind, name, t), (_, raw_thm)), after_qed)) = current_goal state;
    val outer_state = state |> close_block;
    val outer_ctxt = context_of outer_state;

    val result = prep_result state t raw_thm;
    val resultq = #1 (ProofContext.export_wrt false goal_ctxt (Some outer_ctxt)) result;

    val (atts, opt_solve) =
      (case kind of
        Show atts => (atts, export_goal print_rule result goal_ctxt)
      | Have atts => (atts, Seq.single)
      | _ => err_malformed "finish_local" state);
  in
    print_result {kind = kind_name kind, name = name, thm = result};
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

val name_refN = "name_ref";

fun finish_global state =
  let
    val (_, (((kind, name, t), (_, raw_thm)), _)) = current_goal state;   (*ignores after_qed!*)
    val full_name = if name = "" then "" else Sign.full_name (sign_of state) name;
    val result =
      prep_result state t raw_thm
      |> Drule.standard
      |> Drule.tag_rule (name_refN, [full_name]);

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
  |> new_block
  |> reset_facts;


end;


structure BasicProof: BASIC_PROOF = Proof;
open BasicProof;
