(*  Title:      Pure/Isar/method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Proof methods.
*)

signature BASIC_METHOD =
sig
  val print_methods: theory -> unit
  val Method: bstring -> (Args.src -> Proof.context -> Proof.method) -> string -> unit
end;

signature METHOD =
sig
  include BASIC_METHOD
  val print_global_rules: theory -> unit
  val print_local_rules: Proof.context -> unit
  val dest_global: theory attribute
  val elim_global: theory attribute
  val intro_global: theory attribute
  val rule_del_global: theory attribute
  val dest_local: Proof.context attribute
  val elim_local: Proof.context attribute
  val intro_local: Proof.context attribute
  val rule_del_local: Proof.context attribute
  val METHOD: (thm list -> tactic) -> Proof.method
  val METHOD_CASES:
    (thm list -> thm -> (thm * (string * RuleCases.T) list) Seq.seq) -> Proof.method
  val SIMPLE_METHOD: tactic -> Proof.method
  val SIMPLE_METHOD': ((int -> tactic) -> tactic) -> (int -> tactic) -> Proof.method
  val fail: Proof.method
  val succeed: Proof.method
  val defer: int option -> Proof.method
  val prefer: int -> Proof.method
  val insert_tac: thm list -> int -> tactic
  val insert: thm list -> Proof.method
  val insert_facts: Proof.method
  val unfold: thm list -> Proof.method
  val fold: thm list -> Proof.method
  val atomize_tac: thm list -> int -> tactic
  val atomize_goal: thm list -> int -> thm -> thm
  val multi_resolve: thm list -> thm -> thm Seq.seq
  val multi_resolves: thm list -> thm list -> thm Seq.seq
  val resolveq_tac: thm Seq.seq -> int -> tactic
  val resolveq_cases_tac: bool -> (thm * string list) Seq.seq
    -> int -> thm -> (thm * (string * RuleCases.T) list) Seq.seq
  val rule_tac: thm list -> thm list -> int -> tactic
  val erule_tac: thm list -> thm list -> int -> tactic
  val some_rule_tac: thm list -> Proof.context -> thm list -> int -> tactic
  val rule: thm list -> Proof.method
  val erule: thm list -> Proof.method
  val drule: thm list -> Proof.method
  val frule: thm list -> Proof.method
  val this: Proof.method
  val assumption: Proof.context -> Proof.method
  val set_tactic: (Proof.context -> thm list -> tactic) -> unit
  val tactic: string -> Proof.context -> Proof.method
  exception METHOD_FAIL of (string * Position.T) * exn
  val method: theory -> Args.src -> Proof.context -> Proof.method
  val add_method: bstring * (Args.src -> Proof.context -> Proof.method) * string
    -> theory -> theory
  val add_methods: (bstring * (Args.src -> Proof.context -> Proof.method) * string) list
    -> theory -> theory
  val syntax: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list)) ->
    Args.src -> Proof.context -> Proof.context * 'a
  val simple_args: (Args.T list -> 'a * Args.T list)
    -> ('a -> Proof.context -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  val ctxt_args: (Proof.context -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  val no_args: Proof.method -> Args.src -> Proof.context -> Proof.method
  type modifier
  val sectioned_args: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list)) ->
    (Args.T list -> modifier * Args.T list) list ->
    ('a -> Proof.context -> 'b) -> Args.src -> Proof.context -> 'b
  val bang_sectioned_args:
    (Args.T list -> modifier * Args.T list) list ->
    (thm list -> Proof.context -> 'a) -> Args.src -> Proof.context -> 'a
  val bang_sectioned_args':
    (Args.T list -> modifier * Args.T list) list ->
    (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list)) ->
    ('a -> thm list -> Proof.context -> 'b) -> Args.src -> Proof.context -> 'b
  val only_sectioned_args:
    (Args.T list -> modifier * Args.T list) list ->
    (Proof.context -> 'a) -> Args.src -> Proof.context -> 'a
  val thms_ctxt_args: (thm list -> Proof.context -> 'a) -> Args.src -> Proof.context -> 'a
  val thms_args: (thm list -> 'a) -> Args.src -> Proof.context -> 'a
  val thm_args: (thm -> 'a) -> Args.src -> Proof.context -> 'a
  datatype text =
    Basic of (Proof.context -> Proof.method) |
    Source of Args.src |
    Then of text list |
    Orelse of text list |
    Try of text |
    Repeat1 of text
  val refine: text -> Proof.state -> Proof.state Seq.seq
  val refine_end: text -> Proof.state -> Proof.state Seq.seq
  val proof: text option -> Proof.state -> Proof.state Seq.seq
  val local_qed: bool -> text option
    -> ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val local_terminal_proof: text * text option
    -> ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val local_default_proof: ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val local_immediate_proof: ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val local_done_proof: ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val global_qed: bool -> text option
    -> Proof.state -> theory * {kind: string, name: string, thm: thm}
  val global_terminal_proof: text * text option
    -> Proof.state -> theory * {kind: string, name: string, thm: thm}
  val global_default_proof: Proof.state -> theory * {kind: string, name: string, thm: thm}
  val global_immediate_proof: Proof.state -> theory * {kind: string, name: string, thm: thm}
  val global_done_proof: Proof.state -> theory * {kind: string, name: string, thm: thm}
  val goal_args: (Args.T list -> 'a * Args.T list) -> ('a -> int -> tactic)
    -> Args.src -> Proof.context -> Proof.method
  val goal_args': (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list))
    -> ('a -> int -> tactic) -> Args.src -> Proof.context -> Proof.method
  val setup: (theory -> theory) list
end;

structure Method: METHOD =
struct


(** global and local rule data **)

local
  fun prt_rules kind sg ths =
    Pretty.writeln (Pretty.big_list ("standard " ^ kind ^ " rules:")
      (map (Display.pretty_thm_sg sg) ths));
in
  fun print_rules sg (intro, elim) =
    (prt_rules "introduction" sg intro; prt_rules "elimination" sg elim);
end;


(* theory data kind 'Isar/rules' *)

structure GlobalRulesArgs =
struct
  val name = "Isar/rules";
  type T = thm list * thm list;

  val empty = ([], []);
  val copy = I;
  val prep_ext = I;
  fun merge ((intro1, elim1), (intro2, elim2)) =
    (Drule.merge_rules (intro1, intro2), Drule.merge_rules (elim1, elim2));
  val print = print_rules;
end;

structure GlobalRules = TheoryDataFun(GlobalRulesArgs);
val print_global_rules = GlobalRules.print;


(* proof data kind 'Isar/rules' *)

structure LocalRulesArgs =
struct
  val name = "Isar/rules";
  type T = thm list * thm list;

  val init = GlobalRules.get;
  val print = print_rules o ProofContext.sign_of;
end;

structure LocalRules = ProofDataFun(LocalRulesArgs);
val print_local_rules = LocalRules.print;



(** attributes **)

(* add rules *)

local

fun add_dest th (intro, elim) = (intro, Drule.add_rules [Tactic.make_elim th] elim);
fun add_elim th (intro, elim) = (intro, Drule.add_rules [th] elim);
fun add_intro th (intro, elim) = (Drule.add_rules [th] intro, elim);

fun del_rule th (intro, elim) =
  let
    val th' = Tactic.make_elim th;
    val del = Drule.del_rules [th'] o Drule.del_rules [th];
  in (del intro, del elim) end;

fun mk_att f g (x, th) = (f (g th) x, th);

in

val dest_global = mk_att GlobalRules.map add_dest;
val elim_global = mk_att GlobalRules.map add_elim;
val intro_global = mk_att GlobalRules.map add_intro;
val rule_del_global = mk_att GlobalRules.map del_rule;

val dest_local = mk_att LocalRules.map add_dest;
val elim_local = mk_att LocalRules.map add_elim;
val intro_local = mk_att LocalRules.map add_intro;
val rule_del_local = mk_att LocalRules.map del_rule;

fun del_args att = Attrib.syntax (Scan.lift Args.del >> K att);

end;


(* concrete syntax *)

val rule_atts =
 [("dest", (Attrib.no_args dest_global, Attrib.no_args dest_local),
    "declaration of destruction rule"),
  ("elim", (Attrib.no_args elim_global, Attrib.no_args elim_local),
    "declaration of elimination rule"),
  ("intro", (Attrib.no_args intro_global, Attrib.no_args intro_local),
    "declaration of introduction rule"),
  ("rule", (del_args rule_del_global, del_args rule_del_local),
    "remove declaration of elim/intro rule")];



(** proof methods **)

(* make methods *)

val METHOD = Proof.method;
val METHOD_CASES = Proof.method_cases;


(* primitive *)

val fail = METHOD (K no_tac);
val succeed = METHOD (K all_tac);


(* shuffle *)

fun prefer i = METHOD (K (Tactic.defer_tac i THEN PRIMITIVE (Thm.permute_prems 0 ~1)));
fun defer opt_i = METHOD (K (Tactic.defer_tac (if_none opt_i 1)));


(* insert *)

local

fun cut_rule_tac raw_rule =
  let
    val rule = Drule.forall_intr_vars raw_rule;
    val revcut_rl = Drule.incr_indexes_wrt [] [] [] [rule] Drule.revcut_rl;
  in Tactic.rtac (rule COMP revcut_rl) end;

in

fun insert_tac [] i = all_tac
  | insert_tac facts i = EVERY (map (fn th => cut_rule_tac th i) facts);

val insert_facts = METHOD (ALLGOALS o insert_tac);
fun insert thms = METHOD (fn _ => ALLGOALS (insert_tac thms));

end;


(* simple methods *)

fun SIMPLE_METHOD tac = METHOD (fn facts => ALLGOALS (insert_tac facts) THEN tac);
fun SIMPLE_METHOD' quant tac = METHOD (fn facts => quant (insert_tac facts THEN' tac));


(* unfold / fold definitions *)

fun unfold thms = SIMPLE_METHOD (CHANGED (rewrite_goals_tac thms));
fun fold thms = SIMPLE_METHOD (CHANGED (fold_goals_tac thms));


(* atomize meta-connectives *)

fun atomize_tac rews i thm =
  if Logic.has_meta_prems (#prop (Thm.rep_thm thm)) i then
    Tactic.asm_rewrite_goal_tac (true, false, false) (K no_tac) (Thm.mss_of rews) i thm
  else all_tac thm;

fun atomize_goal rews i thm =
  (case Seq.pull (atomize_tac rews i thm) of
    None => thm
  | Some (thm', _) => thm');


(* multi_resolve *)

local

fun res th i rule =
  Thm.biresolution false [(false, th)] i rule handle THM _ => Seq.empty;

fun multi_res _ [] rule = Seq.single rule
  | multi_res i (th :: ths) rule = Seq.flat (Seq.map (res th i) (multi_res (i + 1) ths rule));

in

val multi_resolve = multi_res 1;
fun multi_resolves facts rules = Seq.flat (Seq.map (multi_resolve facts) (Seq.of_list rules));

end;


(* general rule *)

fun gen_resolveq_tac tac rules i st =
  Seq.flat (Seq.map (fn rule => tac rule i st) rules);

val resolveq_tac = gen_resolveq_tac Tactic.rtac;

fun resolveq_cases_tac open_parms = gen_resolveq_tac (fn (rule, cases) => fn i => fn st =>
  Seq.map (rpair (RuleCases.make (not open_parms) rule cases)) (Tactic.rtac rule i st));


(* simple rule *)

local

fun gen_rule_tac tac rules [] = tac rules
  | gen_rule_tac tac erules facts = gen_resolveq_tac (tac o single) (multi_resolves facts erules);

fun gen_some_rule_tac tac arg_rules ctxt facts =
  let val rules =
    if not (null arg_rules) then arg_rules
    else if null facts then #1 (LocalRules.get ctxt)
    else op @ (LocalRules.get ctxt);
  in tac rules facts end;

fun gen_rule tac rules = METHOD (HEADGOAL o tac rules);
fun gen_rule' tac arg_rules ctxt = METHOD (HEADGOAL o gen_some_rule_tac tac arg_rules ctxt);

fun setup raw_tac =
  let val tac = gen_rule_tac raw_tac
  in (tac, gen_rule tac, gen_rule' tac) end;

in

val some_rule_tac = gen_some_rule_tac (gen_rule_tac Tactic.resolve_tac);
val (rule_tac, rule, some_rule) = setup Tactic.resolve_tac;
val (erule_tac, erule, some_erule) = setup Tactic.eresolve_tac;
val (drule_tac, drule, some_drule) = setup Tactic.dresolve_tac;
val (frule_tac, frule, some_frule) = setup Tactic.forward_tac;

end;


(* this *)

val this = METHOD (EVERY o map (HEADGOAL o Tactic.rtac));


(* assumption *)

fun asm_tac ths =
  foldr (op APPEND') (map (fn th => Tactic.rtac th THEN_ALL_NEW assume_tac) ths, K no_tac);

fun assm_tac ctxt = assume_tac APPEND' asm_tac (ProofContext.prems_of ctxt);

fun assumption_tac ctxt [] = assm_tac ctxt
  | assumption_tac _ [fact] = asm_tac [fact]
  | assumption_tac _ _ = K no_tac;

fun assumption ctxt = METHOD (HEADGOAL o assumption_tac ctxt);


(* res_inst_tac etc. *)

(*Note: insts refer to the implicit (!!) goal context; use at your own risk*)
fun gen_res_inst _ tac (quant, ([], thms)) =
      METHOD (fn facts => (quant (insert_tac facts THEN' tac thms)))
  | gen_res_inst tac _ (quant, (insts, [thm])) =
      METHOD (fn facts => (quant (insert_tac facts THEN' tac insts thm)))
  | gen_res_inst _ _ _ = error "Cannot have instantiations with multiple rules";

val res_inst = gen_res_inst Tactic.res_inst_tac Tactic.resolve_tac;
val eres_inst = gen_res_inst Tactic.eres_inst_tac Tactic.eresolve_tac;
val dres_inst = gen_res_inst Tactic.dres_inst_tac Tactic.dresolve_tac;
val forw_inst = gen_res_inst Tactic.forw_inst_tac Tactic.forward_tac;
val cut_inst = gen_res_inst Tactic.cut_inst_tac Tactic.cut_facts_tac;


(* simple Prolog interpreter *)

fun prolog_tac rules facts =
  DEPTH_SOLVE_1 (HEADGOAL (Tactic.assume_tac APPEND' Tactic.resolve_tac (facts @ rules)));

val prolog = METHOD o prolog_tac;


(* ML tactics *)

val tactic_ref = ref ((fn _ => raise Match): Proof.context -> thm list -> tactic);
fun set_tactic f = tactic_ref := f;

fun tactic txt ctxt = METHOD (fn facts =>
  (Context.use_mltext
    ("let fun tactic (ctxt: PureIsar.Proof.context) (facts: thm list) : tactic = \
     \let val thm = PureIsar.ProofContext.get_thm_closure ctxt\n\
     \  and thms = PureIsar.ProofContext.get_thms_closure ctxt in\n"
     ^ txt ^
     "\nend in PureIsar.Method.set_tactic tactic end")
    false None;
    Context.setmp (Some (ProofContext.theory_of ctxt)) (! tactic_ref ctxt) facts));



(** methods theory data **)

(* data kind 'Isar/methods' *)

structure MethodsDataArgs =
struct
  val name = "Isar/methods";
  type T =
    {space: NameSpace.T,
     meths: (((Args.src -> Proof.context -> Proof.method) * string) * stamp) Symtab.table};

  val empty = {space = NameSpace.empty, meths = Symtab.empty};
  val copy = I;
  val prep_ext = I;
  fun merge ({space = space1, meths = meths1}, {space = space2, meths = meths2}) =
    {space = NameSpace.merge (space1, space2),
      meths = Symtab.merge eq_snd (meths1, meths2) handle Symtab.DUPS dups =>
        error ("Attempt to merge different versions of methods " ^ commas_quote dups)};

  fun print _ {space, meths} =
    let
      fun prt_meth (name, ((_, comment), _)) = Pretty.block
        [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    in
      [Pretty.big_list "methods:" (map prt_meth (NameSpace.cond_extern_table space meths))]
      |> Pretty.chunks |> Pretty.writeln
    end;
end;

structure MethodsData = TheoryDataFun(MethodsDataArgs);
val print_methods = MethodsData.print;


(* get methods *)

exception METHOD_FAIL of (string * Position.T) * exn;

fun method thy =
  let
    val {space, meths} = MethodsData.get thy;

    fun meth src =
      let
        val ((raw_name, _), pos) = Args.dest_src src;
        val name = NameSpace.intern space raw_name;
      in
        (case Symtab.lookup (meths, name) of
          None => error ("Unknown proof method: " ^ quote name ^ Position.str_of pos)
        | Some ((mth, _), _) => transform_failure (curry METHOD_FAIL (name, pos)) (mth src))
      end;
  in meth end;


(* add_method(s) *)

fun add_methods raw_meths thy =
  let
    val full = Sign.full_name (Theory.sign_of thy);
    val new_meths =
      map (fn (name, f, comment) => (full name, ((f, comment), stamp ()))) raw_meths;

    val {space, meths} = MethodsData.get thy;
    val space' = NameSpace.extend (space, map fst new_meths);
    val meths' = Symtab.extend (meths, new_meths) handle Symtab.DUPS dups =>
      error ("Duplicate declaration of method(s) " ^ commas_quote dups);
  in
    thy |> MethodsData.put {space = space', meths = meths'}
  end;

val add_method = add_methods o Library.single;

(*implicit version*)
fun Method name meth cmt = Context.>> (add_methods [(name, meth, cmt)]);



(** method syntax **)

(* basic *)

fun syntax (scan: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list))) =
  Args.syntax "method" scan;

fun simple_args scan f src ctxt : Proof.method =
  #2 (syntax (Scan.lift (scan >> (fn x => f x ctxt))) src ctxt);

fun ctxt_args (f: Proof.context -> Proof.method) src ctxt =
  #2 (syntax (Scan.succeed (f ctxt)) src ctxt);

fun no_args m = ctxt_args (K m);



(* sections *)

type modifier = (Proof.context -> Proof.context) * Proof.context attribute;

local

fun sect ss = Scan.first (map Scan.lift ss);
fun thms ss = Scan.unless (sect ss) Attrib.local_thms;
fun thmss ss = Scan.repeat (thms ss) >> flat;

fun apply (f, att) (ctxt, ths) = Thm.applys_attributes ((f ctxt, ths), [att]);

fun section ss = (sect ss -- thmss ss) :-- (fn (m, ths) => Scan.depend (fn ctxt =>
  Scan.succeed (apply m (ctxt, ths)))) >> #2;

fun sectioned args ss = args -- Scan.repeat (section ss);

in

fun sectioned_args args ss f src ctxt =
  let val (ctxt', (x, _)) = syntax (sectioned args ss) src ctxt
  in f x ctxt' end;

fun bang_sectioned_args ss f = sectioned_args Args.bang_facts ss f;
fun bang_sectioned_args' ss scan f =
  sectioned_args (Args.bang_facts -- scan >> swap) ss (uncurry f);
fun only_sectioned_args ss f = sectioned_args (Scan.succeed ()) ss (fn () => f);

fun thms_ctxt_args f = sectioned_args (thmss []) [] f;
fun thms_args f = thms_ctxt_args (K o f);
fun thm_args f = thms_args (fn [thm] => f thm | _ => error "Single theorem expected");

end;


(* tactic syntax *)

val insts =
  Scan.optional
    (Args.enum1 "and" (Scan.lift (Args.name -- (Args.$$$ "=" |-- Args.!!! Args.name))) --|
      Scan.lift (Args.$$$ "in")) [] -- Attrib.local_thmss;

fun inst_args f = f oo (#2 oo syntax (Args.goal_spec HEADGOAL -- insts));


fun goal_args' args tac = #2 oo syntax (Args.goal_spec HEADGOAL -- args >>
  (fn (quant, s) => SIMPLE_METHOD' quant (tac s)));

fun goal_args args tac = goal_args' (Scan.lift args) tac;



(** method text **)

(* datatype text *)

datatype text =
  Basic of (Proof.context -> Proof.method) |
  Source of Args.src |
  Then of text list |
  Orelse of text list |
  Try of text |
  Repeat1 of text;


(* refine *)

fun gen_refine f text state =
  let
    val thy = Proof.theory_of state;

    fun eval (Basic mth) = f mth
      | eval (Source src) = f (method thy src)
      | eval (Then txts) = Seq.EVERY (map eval txts)
      | eval (Orelse txts) = Seq.FIRST (map eval txts)
      | eval (Try txt) = Seq.TRY (eval txt)
      | eval (Repeat1 txt) = Seq.REPEAT1 (eval txt);
  in eval text state end;

val refine = gen_refine Proof.refine;
val refine_end = gen_refine Proof.refine_end;


(* structured proof steps *)

val default_text = Source (Args.src (("default", []), Position.none));
val this_text = Basic (K this);
val done_text = Basic (K (SIMPLE_METHOD all_tac));

fun close_text asm = Basic (fn ctxt => METHOD (K
  (FILTER Thm.no_prems ((if asm then ALLGOALS (assm_tac ctxt) else all_tac) THEN flexflex_tac))));

fun finish_text asm None = close_text asm
  | finish_text asm (Some txt) = Then [txt, close_text asm];

fun proof opt_text state =
  state
  |> Proof.assert_backward
  |> refine (if_none opt_text default_text)
  |> Seq.map (Proof.goal_facts (K []))
  |> Seq.map Proof.enter_forward;

fun local_qed asm opt_text = Proof.local_qed (refine (finish_text asm opt_text));
fun local_terminal_proof (text, opt_text) pr =
  Seq.THEN (proof (Some text), local_qed true opt_text pr);
val local_default_proof = local_terminal_proof (default_text, None);
val local_immediate_proof = local_terminal_proof (this_text, None);
fun local_done_proof pr = Seq.THEN (proof (Some done_text), local_qed false None pr);


fun global_qeds asm opt_text = Proof.global_qed (refine (finish_text asm opt_text));

fun global_qed asm opt_text state =
  state
  |> global_qeds asm opt_text
  |> Proof.check_result "Failed to finish proof" state
  |> Seq.hd;

fun global_term_proof asm (text, opt_text) state =
  state
  |> proof (Some text)
  |> Proof.check_result "Terminal proof method failed" state
  |> (Seq.flat o Seq.map (global_qeds asm opt_text))
  |> Proof.check_result "Failed to finish proof (after successful terminal method)" state
  |> Seq.hd;

val global_terminal_proof = global_term_proof true;
val global_default_proof = global_terminal_proof (default_text, None);
val global_immediate_proof = global_terminal_proof (this_text, None);
val global_done_proof = global_term_proof false (done_text, None);


(** theory setup **)

(* misc tactic emulations *)

val subgoal_meth = goal_args (Scan.repeat1 Args.name) Tactic.subgoals_tac;
val thin_meth = goal_args Args.name Tactic.thin_tac;
val rename_meth = goal_args (Scan.repeat1 Args.name) Tactic.rename_params_tac;
val rotate_meth = goal_args (Scan.optional Args.int 1) Tactic.rotate_tac;


(* pure_methods *)

val pure_methods =
 [("fail", no_args fail, "force failure"),
  ("succeed", no_args succeed, "succeed"),
  ("-", no_args insert_facts, "do nothing (insert current facts only)"),
  ("insert", thms_args insert, "insert theorems, ignoring facts (improper)"),
  ("unfold", thms_args unfold, "unfold definitions"),
  ("fold", thms_args fold, "fold definitions"),
  ("rule", thms_ctxt_args some_rule, "apply some rule"),
  ("erule", thms_ctxt_args some_erule, "apply some rule in elimination manner (improper)"),
  ("drule", thms_ctxt_args some_drule, "apply some rule in destruct manner (improper)"),
  ("frule", thms_ctxt_args some_frule, "apply some rule in forward manner (improper)"),
  ("this", no_args this, "apply current facts as rules"),
  ("assumption", ctxt_args assumption, "proof by assumption, preferring facts"),
  ("rule_tac", inst_args res_inst, "apply rule (dynamic instantiation!)"),
  ("erule_tac", inst_args eres_inst, "apply rule in elimination manner (dynamic instantiation!)"),
  ("drule_tac", inst_args dres_inst, "apply rule in destruct manner (dynamic instantiation!)"),
  ("frule_tac", inst_args forw_inst, "apply rule in forward manner (dynamic instantiation!)"),
  ("cut_tac", inst_args cut_inst, "cut rule (dynamic instantiation!)"),
  ("subgoal_tac", subgoal_meth, "insert subgoal (dynamic instantiation!)"),
  ("thin_tac", thin_meth, "remove premise (dynamic instantiation!)"),
  ("rename_tac", rename_meth, "rename parameters of goal (dynamic instantiation!)"),
  ("rotate_tac", rotate_meth, "rotate assumptions of goal"),
  ("prolog", thms_args prolog, "simple prolog interpreter"),
  ("tactic", simple_args Args.name tactic, "ML tactic as proof method")];


(* setup *)

val setup =
 [GlobalRules.init, LocalRules.init, Attrib.add_attributes rule_atts,
  MethodsData.init, add_methods pure_methods];


end;


structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
