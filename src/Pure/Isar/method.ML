(*  Title:      Pure/Isar/method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar proof methods.
*)

signature BASIC_METHOD =
sig
  val FINDGOAL: (int -> thm -> 'a Seq.seq) -> thm -> 'a Seq.seq
  val HEADGOAL: (int -> thm -> 'a Seq.seq) -> thm -> 'a Seq.seq
  type method
  val trace_rules: bool ref
  val print_methods: theory -> unit
end;

signature METHOD =
sig
  include BASIC_METHOD
  val apply: method -> thm list -> cases_tactic
  val RAW_METHOD_CASES: (thm list -> cases_tactic) -> method
  val RAW_METHOD: (thm list -> tactic) -> method
  val METHOD_CASES: (thm list -> cases_tactic) -> method
  val METHOD: (thm list -> tactic) -> method
  val fail: method
  val succeed: method
  val insert_tac: thm list -> int -> tactic
  val insert: thm list -> method
  val insert_facts: method
  val SIMPLE_METHOD: tactic -> method
  val SIMPLE_METHOD': (int -> tactic) -> method
  val SIMPLE_METHOD'': ((int -> tactic) -> tactic) -> (int -> tactic) -> method
  val defer: int option -> method
  val prefer: int -> method
  val cheating: bool -> Proof.context -> method
  val intro: thm list -> method
  val elim: thm list -> method
  val unfold: thm list -> Proof.context -> method
  val fold: thm list -> Proof.context -> method
  val atomize: bool -> method
  val this: method
  val fact: thm list -> Proof.context -> method
  val assumption: Proof.context -> method
  val close: bool -> Proof.context -> method
  val trace: Proof.context -> thm list -> unit
  val rule_tac: thm list -> thm list -> int -> tactic
  val some_rule_tac: thm list -> Proof.context -> thm list -> int -> tactic
  val rule: thm list -> method
  val erule: int -> thm list -> method
  val drule: int -> thm list -> method
  val frule: int -> thm list -> method
  val iprover_tac: Proof.context -> int option -> int -> tactic
  val set_tactic: (Proof.context -> thm list -> tactic) -> unit
  val tactic: string -> Proof.context -> method
  type src
  datatype text =
    Basic of (Proof.context -> method) |
    Source of src |
    Source_i of src |
    Then of text list |
    Orelse of text list |
    Try of text |
    Repeat1 of text |
    SelectGoals of int * text
  val primitive_text: (thm -> thm) -> text
  val succeed_text: text
  val default_text: text
  val this_text: text
  val done_text: text
  val sorry_text: bool -> text
  val finish_text: text option * bool -> text
  exception METHOD_FAIL of (string * Position.T) * exn
  val method: theory -> src -> Proof.context -> method
  val method_i: theory -> src -> Proof.context -> method
  val add_methods: (bstring * (src -> Proof.context -> method) * string) list
    -> theory -> theory
  val add_method: bstring * (src -> Proof.context -> method) * string
    -> theory -> theory
  val method_setup: bstring * string * string -> theory -> theory
  val syntax: (Context.generic * Args.T list -> 'a * (Context.generic * Args.T list))
    -> src -> Proof.context -> 'a * Proof.context
  val simple_args: (Args.T list -> 'a * Args.T list)
    -> ('a -> Proof.context -> method) -> src -> Proof.context -> method
  val ctxt_args: (Proof.context -> method) -> src -> Proof.context -> method
  val no_args: method -> src -> Proof.context -> method
  type modifier
  val sectioned_args: (Context.generic * Args.T list -> 'a * (Context.generic * Args.T list)) ->
    (Args.T list -> modifier * Args.T list) list ->
    ('a -> Proof.context -> 'b) -> src -> Proof.context -> 'b
  val bang_sectioned_args:
    (Args.T list -> modifier * Args.T list) list ->
    (thm list -> Proof.context -> 'a) -> src -> Proof.context -> 'a
  val bang_sectioned_args':
    (Args.T list -> modifier * Args.T list) list ->
    (Context.generic * Args.T list -> 'a * (Context.generic * Args.T list)) ->
    ('a -> thm list -> Proof.context -> 'b) -> src -> Proof.context -> 'b
  val only_sectioned_args:
    (Args.T list -> modifier * Args.T list) list ->
    (Proof.context -> 'a) -> src -> Proof.context -> 'a
  val thms_ctxt_args: (thm list -> Proof.context -> 'a) -> src ->
    Proof.context -> 'a
  val thms_args: (thm list -> 'a) -> src -> Proof.context -> 'a
  val thm_args: (thm -> 'a) -> src -> Proof.context -> 'a
  val goal_args: (Args.T list -> 'a * Args.T list) -> ('a -> int -> tactic)
    -> src -> Proof.context -> method
  val goal_args': (Context.generic * Args.T list -> 'a * (Context.generic * Args.T list))
    -> ('a -> int -> tactic) -> src -> Proof.context -> method
  val goal_args_ctxt: (Args.T list -> 'a * Args.T list) ->
    (Proof.context -> 'a -> int -> tactic) -> src -> Proof.context -> method
  val goal_args_ctxt': (Context.generic * Args.T list -> 'a * (Context.generic * Args.T list)) ->
    (Proof.context -> 'a -> int -> tactic) -> src -> Proof.context -> method
  val parse: OuterLex.token list -> text * OuterLex.token list
end;

structure Method: METHOD =
struct

(** generic tools **)

(* goal addressing *)

fun FINDGOAL tac st =
  let fun find i n = if i > n then Seq.fail else Seq.APPEND (tac i, find (i + 1) n)
  in find 1 (Thm.nprems_of st) st end;

fun HEADGOAL tac = tac 1;



(** proof methods **)

(* datatype method *)

datatype method = Meth of thm list -> cases_tactic;

fun apply (Meth m) = m;

val RAW_METHOD_CASES = Meth;

fun RAW_METHOD tac = RAW_METHOD_CASES (NO_CASES o tac);

fun METHOD_CASES tac = RAW_METHOD_CASES (fn facts =>
  Seq.THEN (ALLGOALS Goal.conjunction_tac, tac facts));

fun METHOD tac = RAW_METHOD (fn facts => ALLGOALS Goal.conjunction_tac THEN tac facts);

val fail = METHOD (K no_tac);
val succeed = METHOD (K all_tac);


(* insert facts *)

local

fun cut_rule_tac rule =
  Tactic.rtac (Drule.forall_intr_vars rule COMP_INCR revcut_rl);

in

fun insert_tac [] i = all_tac
  | insert_tac facts i = EVERY (map (fn th => cut_rule_tac th i) facts);

val insert_facts = METHOD (ALLGOALS o insert_tac);
fun insert thms = METHOD (fn _ => ALLGOALS (insert_tac thms));

fun SIMPLE_METHOD tac = METHOD (fn facts => ALLGOALS (insert_tac facts) THEN tac);
fun SIMPLE_METHOD'' quant tac = METHOD (fn facts => quant (insert_tac facts THEN' tac));
val SIMPLE_METHOD' = SIMPLE_METHOD'' HEADGOAL;

end;


(* shuffle subgoals *)

fun prefer i = METHOD (K (Tactic.defer_tac i THEN PRIMITIVE (Thm.permute_prems 0 ~1)));
fun defer opt_i = METHOD (K (Tactic.defer_tac (the_default 1 opt_i)));


(* cheating *)

fun cheating int ctxt = METHOD (K (setmp quick_and_dirty (int orelse ! quick_and_dirty)
    (SkipProof.cheat_tac (ProofContext.theory_of ctxt))));


(* unfold intro/elim rules *)

fun intro ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.match_tac ths));
fun elim ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.ematch_tac ths));


(* unfold/fold definitions *)

fun unfold_meth ths ctxt = SIMPLE_METHOD (CHANGED_PROP (LocalDefs.unfold_tac ctxt ths));
fun fold_meth ths ctxt = SIMPLE_METHOD (CHANGED_PROP (LocalDefs.fold_tac ctxt ths));


(* atomize rule statements *)

fun atomize false = SIMPLE_METHOD' (CHANGED_PROP o ObjectLogic.atomize_tac)
  | atomize true = RAW_METHOD (K (HEADGOAL (CHANGED_PROP o ObjectLogic.full_atomize_tac)));


(* this -- resolve facts directly *)

val this = METHOD (EVERY o map (HEADGOAL o Tactic.rtac));


(* fact -- composition by facts from context *)

fun fact [] ctxt = SIMPLE_METHOD' (ProofContext.some_fact_tac ctxt)
  | fact rules _ = SIMPLE_METHOD' (ProofContext.fact_tac rules);


(* assumption *)

local

fun asm_tac ths =
  fold_rev (curry op APPEND')
    (map (fn th => Tactic.rtac th THEN_ALL_NEW assume_tac) ths) (K no_tac);

fun cond_rtac cond rule = SUBGOAL (fn (prop, i) =>
  if cond (Logic.strip_assums_concl prop)
  then Tactic.rtac rule i else no_tac);

fun assm_tac ctxt =
  assume_tac APPEND'
  asm_tac (Assumption.prems_of ctxt) APPEND'
  cond_rtac (can Logic.dest_equals) Drule.reflexive_thm APPEND'
  cond_rtac (can Logic.dest_term) Drule.termI;

fun assumption_tac ctxt [] = assm_tac ctxt
  | assumption_tac _ [fact] = asm_tac [fact]
  | assumption_tac _ _ = K no_tac;

in

fun assumption ctxt = METHOD (HEADGOAL o assumption_tac ctxt);
fun close immed ctxt = METHOD (K
  (FILTER Thm.no_prems ((if immed then ALLGOALS (assm_tac ctxt) else all_tac) THEN flexflex_tac)));

end;


(* rule etc. -- single-step refinements *)

val trace_rules = ref false;

fun trace ctxt rules =
  if ! trace_rules andalso not (null rules) then
    Pretty.big_list "rules:" (map (ProofContext.pretty_thm ctxt) rules)
    |> Pretty.string_of |> tracing
  else ();

local

fun gen_rule_tac tac rules facts =
  (fn i => fn st =>
    if null facts then tac rules i st
    else Seq.maps (fn rule => (tac o single) rule i st) (Drule.multi_resolves facts rules))
  THEN_ALL_NEW Goal.norm_hhf_tac;

fun gen_arule_tac tac j rules facts =
  EVERY' (gen_rule_tac tac rules facts :: replicate j Tactic.assume_tac);

fun gen_some_rule_tac tac arg_rules ctxt facts = SUBGOAL (fn (goal, i) =>
  let
    val rules =
      if not (null arg_rules) then arg_rules
      else flat (ContextRules.find_rules false facts goal ctxt)
  in trace ctxt rules; tac rules facts i end);

fun meth tac x = METHOD (HEADGOAL o tac x);
fun meth' tac x y = METHOD (HEADGOAL o tac x y);

in

val rule_tac = gen_rule_tac Tactic.resolve_tac;
val rule = meth rule_tac;
val some_rule_tac = gen_some_rule_tac rule_tac;
val some_rule = meth' some_rule_tac;

val erule = meth' (gen_arule_tac Tactic.eresolve_tac);
val drule = meth' (gen_arule_tac Tactic.dresolve_tac);
val frule = meth' (gen_arule_tac Tactic.forward_tac);

end;


(* iprover -- intuitionistic proof search *)

local

val remdups_tac = SUBGOAL (fn (g, i) =>
  let val prems = Logic.strip_assums_hyp g in
    REPEAT_DETERM_N (length prems - length (distinct op aconv prems))
    (Tactic.ematch_tac [Drule.remdups_rl] i THEN Tactic.eq_assume_tac i)
  end);

fun REMDUPS tac = tac THEN_ALL_NEW remdups_tac;

val bires_tac = Tactic.biresolution_from_nets_tac ContextRules.orderlist;

fun safe_step_tac ctxt =
  ContextRules.Swrap ctxt
   (eq_assume_tac ORELSE'
    bires_tac true (ContextRules.netpair_bang ctxt));

fun unsafe_step_tac ctxt =
  ContextRules.wrap ctxt
   (assume_tac APPEND'
    bires_tac false (ContextRules.netpair_bang ctxt) APPEND'
    bires_tac false (ContextRules.netpair ctxt));

fun step_tac ctxt i =
  REPEAT_DETERM1 (REMDUPS (safe_step_tac ctxt) i) ORELSE
  REMDUPS (unsafe_step_tac ctxt) i;

fun intprover_tac ctxt gs d lim = SUBGOAL (fn (g, i) => if d > lim then no_tac else
  let
    val ps = Logic.strip_assums_hyp g;
    val c = Logic.strip_assums_concl g;
  in
    if member (fn ((ps1, c1), (ps2, c2)) =>
        c1 aconv c2 andalso
        length ps1 = length ps2 andalso
        gen_eq_set (op aconv) (ps1, ps2)) gs (ps, c) then no_tac
    else (step_tac ctxt THEN_ALL_NEW intprover_tac ctxt ((ps, c) :: gs) (d + 1) lim) i
  end);

in

fun iprover_tac ctxt opt_lim =
  SELECT_GOAL (DEEPEN (2, the_default 20 opt_lim) (intprover_tac ctxt [] 0) 4 1);

end;


(* ML tactics *)

val tactic_ref = ref ((fn _ => raise Match): Proof.context -> thm list -> tactic);
fun set_tactic f = tactic_ref := f;

fun tactic txt ctxt = METHOD (fn facts =>
 (ML_Context.use_mltext
   ("let fun tactic (ctxt: Proof.context) (facts: thm list) : tactic =\n"
     ^ txt ^ "\nin Method.set_tactic tactic end") false (SOME (Context.Proof ctxt));
  ML_Context.setmp (SOME (Context.Proof ctxt)) (! tactic_ref ctxt) facts));



(** method syntax **)

(* method text *)

type src = Args.src;

datatype text =
  Basic of (Proof.context -> method) |
  Source of src |
  Source_i of src |
  Then of text list |
  Orelse of text list |
  Try of text |
  Repeat1 of text |
  SelectGoals of int * text;

val primitive_text = Basic o K o SIMPLE_METHOD o PRIMITIVE;
val succeed_text = Basic (K succeed);
val default_text = Source (Args.src (("default", []), Position.none));
val this_text = Basic (K this);
val done_text = Basic (K (SIMPLE_METHOD all_tac));
val sorry_text = Basic o cheating;

fun finish_text (NONE, immed) = Basic (close immed)
  | finish_text (SOME txt, immed) = Then [txt, Basic (close immed)];


(* method definitions *)

structure MethodsData = TheoryDataFun
(
  type T = (((src -> Proof.context -> method) * string) * stamp) NameSpace.table;
  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;
  fun merge _ tables = NameSpace.merge_tables (eq_snd (op =)) tables handle Symtab.DUPS dups =>
    error ("Attempt to merge different versions of method(s) " ^ commas_quote dups);
);

fun print_methods thy =
  let
    val meths = MethodsData.get thy;
    fun prt_meth (name, ((_, comment), _)) = Pretty.block
      [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
  in
    [Pretty.big_list "methods:" (map prt_meth (NameSpace.extern_table meths))]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* get methods *)

exception METHOD_FAIL of (string * Position.T) * exn;

fun method_i thy =
  let
    val meths = #2 (MethodsData.get thy);
    fun meth src =
      let val ((name, _), pos) = Args.dest_src src in
        (case Symtab.lookup meths name of
          NONE => error ("Unknown proof method: " ^ quote name ^ Position.str_of pos)
        | SOME ((mth, _), _) => transform_failure (curry METHOD_FAIL (name, pos)) (mth src))
      end;
  in meth end;

fun method thy = method_i thy o Args.map_name (NameSpace.intern (#1 (MethodsData.get thy)));


(* add method *)

fun add_methods raw_meths thy =
  let
    val new_meths = raw_meths |> map (fn (name, f, comment) =>
      (name, ((f, comment), stamp ())));

    fun add meths = NameSpace.extend_table (Sign.naming_of thy) new_meths meths
      handle Symtab.DUPS dups =>
        error ("Duplicate declaration of method(s) " ^ commas_quote dups);
  in MethodsData.map add thy end;

val add_method = add_methods o Library.single;


(* method_setup *)

fun method_setup (name, txt, cmt) =
  ML_Context.use_let
    "val method: bstring * (Method.src -> Proof.context -> Proof.method) * string"
    "Context.map_theory (Method.add_method method)"
    ("(" ^ quote name ^ ", " ^ txt ^ ", " ^ quote cmt ^ ")")
  |> Context.theory_map;



(** concrete syntax **)

(* basic *)

fun syntax scan = Args.context_syntax "method" scan;

fun simple_args scan f src ctxt : method =
  fst (syntax (Scan.lift (scan >> (fn x => f x ctxt))) src ctxt);

fun ctxt_args (f: Proof.context -> method) src ctxt =
  fst (syntax (Scan.succeed (f ctxt)) src ctxt);

fun no_args m = ctxt_args (K m);


(* sections *)

type modifier = (Proof.context -> Proof.context) * attribute;

local

fun sect ss = Scan.first (map Scan.lift ss);
fun thms ss = Scan.repeat (Scan.unless (sect ss) Attrib.multi_thm) >> flat;

fun app (f, att) (context, ths) = foldl_map att (Context.map_proof f context, ths);

fun section ss = (sect ss -- thms ss) :-- (fn (m, ths) => Scan.depend (fn context =>
  Scan.succeed (app m (context, ths)))) >> #2;

fun sectioned args ss = args -- Scan.repeat (section ss);

in

fun sectioned_args args ss f src ctxt =
  let val ((x, _), ctxt') = syntax (sectioned args ss) src ctxt
  in f x ctxt' end;

fun bang_sectioned_args ss f = sectioned_args Args.bang_facts ss f;
fun bang_sectioned_args' ss scan f =
  sectioned_args (Args.bang_facts -- scan >> swap) ss (uncurry f);
fun only_sectioned_args ss f = sectioned_args (Scan.succeed ()) ss (fn () => f);

fun thms_ctxt_args f = sectioned_args (thms []) [] f;
fun thms_args f = thms_ctxt_args (K o f);
fun thm_args f = thms_args (fn [thm] => f thm | _ => error "Single theorem expected");

end;


(* iprover syntax *)

local

val introN = "intro";
val elimN = "elim";
val destN = "dest";
val ruleN = "rule";

fun modifier name kind kind' att =
  Args.$$$ name |-- (kind >> K NONE || kind' |-- Args.nat --| Args.colon >> SOME)
    >> (pair (I: Proof.context -> Proof.context) o att);

val iprover_modifiers =
 [modifier destN Args.bang_colon Args.bang ContextRules.dest_bang,
  modifier destN Args.colon (Scan.succeed ()) ContextRules.dest,
  modifier elimN Args.bang_colon Args.bang ContextRules.elim_bang,
  modifier elimN Args.colon (Scan.succeed ()) ContextRules.elim,
  modifier introN Args.bang_colon Args.bang ContextRules.intro_bang,
  modifier introN Args.colon (Scan.succeed ()) ContextRules.intro,
  Args.del -- Args.colon >> K (I, ContextRules.rule_del)];

in

val iprover_meth =
  bang_sectioned_args' iprover_modifiers (Scan.lift (Scan.option Args.nat))
    (fn n => fn prems => fn ctxt => METHOD (fn facts =>
      HEADGOAL (insert_tac (prems @ facts) THEN'
      ObjectLogic.atomize_tac THEN' iprover_tac ctxt n)));

end;


(* tactic syntax *)

fun nat_thms_args f = uncurry f oo
  (fst oo syntax (Scan.lift (Scan.optional (Args.parens Args.nat) 0) -- Attrib.thms));

fun goal_args' args tac src ctxt = fst (syntax (Args.goal_spec HEADGOAL -- args >>
  (fn (quant, s) => SIMPLE_METHOD'' quant (tac s))) src ctxt);

fun goal_args args tac = goal_args' (Scan.lift args) tac;

fun goal_args_ctxt' args tac src ctxt =
  fst (syntax (Args.goal_spec HEADGOAL -- args >>
  (fn (quant, s) => SIMPLE_METHOD'' quant (tac ctxt s))) src ctxt);

fun goal_args_ctxt args tac = goal_args_ctxt' (Scan.lift args) tac;


(* theory setup *)

val _ = Context.add_setup (add_methods
 [("fail", no_args fail, "force failure"),
  ("succeed", no_args succeed, "succeed"),
  ("-", no_args insert_facts, "do nothing (insert current facts only)"),
  ("insert", thms_args insert, "insert theorems, ignoring facts (improper)"),
  ("intro", thms_args intro, "repeatedly apply introduction rules"),
  ("elim", thms_args elim, "repeatedly apply elimination rules"),
  ("unfold", thms_ctxt_args unfold_meth, "unfold definitions"),
  ("fold", thms_ctxt_args fold_meth, "fold definitions"),
  ("atomize", (atomize o fst) oo syntax (Args.mode "full"),
    "present local premises as object-level statements"),
  ("iprover", iprover_meth, "intuitionistic proof search"),
  ("rule", thms_ctxt_args some_rule, "apply some intro/elim rule"),
  ("erule", nat_thms_args erule, "apply rule in elimination manner (improper)"),
  ("drule", nat_thms_args drule, "apply rule in destruct manner (improper)"),
  ("frule", nat_thms_args frule, "apply rule in forward manner (improper)"),
  ("this", no_args this, "apply current facts as rules"),
  ("fact", thms_ctxt_args fact, "composition by facts from context"),
  ("assumption", ctxt_args assumption, "proof by assumption, preferring facts"),
  ("rename_tac", goal_args (Scan.repeat1 Args.name) Tactic.rename_params_tac,
    "rename parameters of goal"),
  ("rotate_tac", goal_args (Scan.optional Args.int 1) Tactic.rotate_tac,
    "rotate assumptions of goal"),
  ("tactic", simple_args Args.name tactic, "ML tactic as proof method")]);


(* outer parser *)

local

structure T = OuterLex;
structure P = OuterParse;

fun is_symid_meth s =
  s <> "|" andalso s <> "?" andalso s <> "+" andalso T.is_sid s;

fun meth4 x =
 (P.position (P.xname >> rpair []) >> (Source o Args.src) ||
  P.$$$ "(" |-- P.!!! (meth0 --| P.$$$ ")")) x
and meth3 x =
 (meth4 --| P.$$$ "?" >> Try ||
  meth4 --| P.$$$ "+" >> Repeat1 ||
  meth4 -- (P.$$$ "[" |-- Scan.optional P.nat 1 --| P.$$$ "]") >> (SelectGoals o swap) ||
  meth4) x
and meth2 x =
 (P.position (P.xname -- P.args1 is_symid_meth false) >> (Source o Args.src) ||
  meth3) x
and meth1 x = (P.enum1 "," meth2 >> (fn [m] => m | ms => Then ms)) x
and meth0 x = (P.enum1 "|" meth1 >> (fn [m] => m | ms => Orelse ms)) x;

in val parse = meth3 end;


(*final declarations of this structure!*)
val unfold = unfold_meth;
val fold = fold_meth;

end;

structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
