(*  Title:      Pure/Isar/method.ML
    Author:     Markus Wenzel, TU Muenchen

Isar proof methods.
*)

signature BASIC_METHOD =
sig
  val FINDGOAL: (int -> thm -> 'a Seq.seq) -> thm -> 'a Seq.seq
  val HEADGOAL: (int -> thm -> 'a Seq.seq) -> thm -> 'a Seq.seq
  val trace_rules: bool ref
end;

signature METHOD =
sig
  include BASIC_METHOD
  type method
  val apply: Position.T -> (Proof.context -> method) -> Proof.context -> thm list -> cases_tactic
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
  val assm_tac: Proof.context -> int -> tactic
  val assumption: Proof.context -> method
  val close: bool -> Proof.context -> method
  val trace: Proof.context -> thm list -> unit
  val rule_tac: thm list -> thm list -> int -> tactic
  val some_rule_tac: thm list -> Proof.context -> thm list -> int -> tactic
  val intros_tac: thm list -> thm list -> tactic
  val rule: thm list -> method
  val erule: int -> thm list -> method
  val drule: int -> thm list -> method
  val frule: int -> thm list -> method
  val set_tactic: (thm list -> tactic) -> Proof.context -> Proof.context
  val tactic: string * Position.T -> Proof.context -> method
  val raw_tactic: string * Position.T -> Proof.context -> method
  type src = Args.src
  datatype text =
    Basic of (Proof.context -> method) * Position.T |
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
  val finish_text: text option * bool -> Position.T -> text
  val print_methods: theory -> unit
  val intern: theory -> xstring -> string
  val defined: theory -> string -> bool
  val method: theory -> src -> Proof.context -> method
  val method_i: theory -> src -> Proof.context -> method
  val add_methods: (bstring * (src -> Proof.context -> method) * string) list
    -> theory -> theory
  val add_method: bstring * (src -> Proof.context -> method) * string
    -> theory -> theory
  val syntax: 'a context_parser -> src -> Proof.context -> 'a * Proof.context
  val setup: binding -> (Proof.context -> method) context_parser -> string -> theory -> theory
  val method_setup: bstring * Position.T -> string * Position.T -> string -> theory -> theory
  val simple_args: 'a parser -> ('a -> Proof.context -> method) -> src -> Proof.context -> method
  val ctxt_args: (Proof.context -> method) -> src -> Proof.context -> method
  val no_args: method -> src -> Proof.context -> method
  type modifier = (Proof.context -> Proof.context) * attribute
  val section: modifier parser list -> thm list context_parser
  val sections: modifier parser list -> thm list list context_parser
  val sectioned_args: 'a context_parser -> modifier parser list ->
    ('a -> Proof.context -> 'b) -> src -> Proof.context -> 'b
  val bang_sectioned_args: modifier parser list ->
    (thm list -> Proof.context -> 'a) -> src -> Proof.context -> 'a
  val bang_sectioned_args': modifier parser list -> 'a context_parser ->
    ('a -> thm list -> Proof.context -> 'b) -> src -> Proof.context -> 'b
  val only_sectioned_args: modifier parser list -> (Proof.context -> 'a) -> src ->
    Proof.context -> 'a
  val thms_ctxt_args: (thm list -> Proof.context -> 'a) -> src -> Proof.context -> 'a
  val thms_args: (thm list -> 'a) -> src -> Proof.context -> 'a
  val thm_args: (thm -> 'a) -> src -> Proof.context -> 'a
  val goal_args: 'a parser -> ('a -> int -> tactic) -> src -> Proof.context -> method
  val goal_args': 'a context_parser -> ('a -> int -> tactic) -> src -> Proof.context -> method
  val goal_args_ctxt: 'a parser -> (Proof.context -> 'a -> int -> tactic) -> src ->
    Proof.context -> method
  val goal_args_ctxt': 'a context_parser -> (Proof.context -> 'a -> int -> tactic) -> src ->
    Proof.context -> method
  val parse: text parser
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

fun apply pos meth_fun ctxt facts goal = Position.setmp_thread_data_seq pos
  (fn () => let val Meth meth = meth_fun ctxt in meth facts goal end) ();

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

fun atomize false = SIMPLE_METHOD' (CHANGED_PROP o ObjectLogic.atomize_prems_tac)
  | atomize true = RAW_METHOD (K (HEADGOAL (CHANGED_PROP o ObjectLogic.full_atomize_tac)));


(* this -- resolve facts directly *)

val this = METHOD (EVERY o map (HEADGOAL o Tactic.rtac));


(* fact -- composition by facts from context *)

fun fact [] ctxt = SIMPLE_METHOD' (ProofContext.some_fact_tac ctxt)
  | fact rules _ = SIMPLE_METHOD' (ProofContext.fact_tac rules);


(* assumption *)

local

fun cond_rtac cond rule = SUBGOAL (fn (prop, i) =>
  if cond (Logic.strip_assums_concl prop)
  then Tactic.rtac rule i else no_tac);

in

fun assm_tac ctxt =
  assume_tac APPEND'
  Goal.assume_rule_tac ctxt APPEND'
  cond_rtac (can Logic.dest_equals) Drule.reflexive_thm APPEND'
  cond_rtac (can Logic.dest_term) Drule.termI;

fun assumption ctxt = METHOD (HEADGOAL o
  (fn [] => assm_tac ctxt
    | [fact] => solve_tac [fact]
    | _ => K no_tac));

fun close immed ctxt = METHOD (K
  (FILTER Thm.no_prems
    ((if immed then ALLGOALS (assm_tac ctxt) else all_tac) THEN flexflex_tac)));

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


(* intros_tac -- pervasive search spanned by intro rules *)

fun intros_tac intros facts =
  ALLGOALS (insert_tac facts THEN'
      REPEAT_ALL_NEW (resolve_tac intros))
    THEN Tactic.distinct_subgoals_tac;


(* ML tactics *)

structure TacticData = ProofDataFun
(
  type T = thm list -> tactic;
  fun init _ = undefined;
);

val set_tactic = TacticData.put;

fun ml_tactic (txt, pos) ctxt =
  let
    val ctxt' = ctxt |> Context.proof_map
      (ML_Context.expression pos
        "fun tactic (facts: thm list) : tactic"
        "Context.map_proof (Method.set_tactic tactic)" txt);
  in Context.setmp_thread_data (SOME (Context.Proof ctxt)) (TacticData.get ctxt') end;

fun tactic txt ctxt = METHOD (ml_tactic txt ctxt);
fun raw_tactic txt ctxt = RAW_METHOD (ml_tactic txt ctxt);



(** method syntax **)

(* method text *)

type src = Args.src;

datatype text =
  Basic of (Proof.context -> method) * Position.T |
  Source of src |
  Source_i of src |
  Then of text list |
  Orelse of text list |
  Try of text |
  Repeat1 of text |
  SelectGoals of int * text;

fun primitive_text r = Basic (K (SIMPLE_METHOD (PRIMITIVE r)), Position.none);
val succeed_text = Basic (K succeed, Position.none);
val default_text = Source (Args.src (("default", []), Position.none));
val this_text = Basic (K this, Position.none);
val done_text = Basic (K (SIMPLE_METHOD all_tac), Position.none);
fun sorry_text int = Basic (cheating int, Position.none);

fun finish_text (NONE, immed) pos = Basic (close immed, pos)
  | finish_text (SOME txt, immed) pos = Then [txt, Basic (close immed, pos)];


(* method definitions *)

structure Methods = TheoryDataFun
(
  type T = (((src -> Proof.context -> method) * string) * stamp) NameSpace.table;
  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;
  fun merge _ tables : T = NameSpace.merge_tables (eq_snd (op =)) tables handle Symtab.DUP dup =>
    error ("Attempt to merge different versions of method " ^ quote dup);
);

fun print_methods thy =
  let
    val meths = Methods.get thy;
    fun prt_meth (name, ((_, comment), _)) = Pretty.block
      [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
  in
    [Pretty.big_list "methods:" (map prt_meth (NameSpace.extern_table meths))]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* get methods *)

val intern = NameSpace.intern o #1 o Methods.get;
val defined = Symtab.defined o #2 o Methods.get;

fun method_i thy =
  let
    val meths = #2 (Methods.get thy);
    fun meth src =
      let val ((name, _), pos) = Args.dest_src src in
        (case Symtab.lookup meths name of
          NONE => error ("Unknown proof method: " ^ quote name ^ Position.str_of pos)
        | SOME ((mth, _), _) => (Position.report (Markup.method name) pos; mth src))
      end;
  in meth end;

fun method thy = method_i thy o Args.map_name (NameSpace.intern (#1 (Methods.get thy)));


(* add method *)

fun add_methods raw_meths thy =
  let
    val new_meths = raw_meths |> map (fn (name, f, comment) =>
      (Binding.name name, ((f, comment), stamp ())));

    fun add meths = fold (snd oo NameSpace.define (Sign.naming_of thy)) new_meths meths
      handle Symtab.DUP dup => error ("Duplicate declaration of method " ^ quote dup);
  in Methods.map add thy end;

val add_method = add_methods o Library.single;


(* method setup *)

fun syntax scan = Args.context_syntax "method" scan;

fun setup name scan comment =
  add_methods [(Binding.name_of name,
    fn src => fn ctxt => let val (m, ctxt') = syntax scan src ctxt in m ctxt' end, comment)];

fun method_setup name (txt, pos) cmt =
  Context.theory_map (ML_Context.expression pos
    "val (name, scan, comment): binding * (Proof.context -> Proof.method) context_parser * string"
    "Context.map_theory (Method.setup name scan comment)"
    ("(" ^ ML_Syntax.make_binding name ^ ", " ^ txt ^ ", " ^ ML_Syntax.print_string cmt ^ ")"));



(** concrete syntax **)

structure P = OuterParse;


(* basic *)

fun simple_args scan f src ctxt : method =
  fst (syntax (Scan.lift (scan >> (fn x => f x ctxt))) src ctxt);

fun ctxt_args (f: Proof.context -> method) src ctxt =
  fst (syntax (Scan.succeed (f ctxt)) src ctxt);

fun no_args m = ctxt_args (K m);


(* sections *)

type modifier = (Proof.context -> Proof.context) * attribute;

local

fun thms ss = Scan.repeat (Scan.unless (Scan.lift (Scan.first ss)) Attrib.multi_thm) >> flat;
fun app (f, att) (context, ths) = Library.foldl_map att (Context.map_proof f context, ths);

in

fun section ss = Scan.depend (fn context => (Scan.first ss -- Scan.pass context (thms ss)) :|--
  (fn (m, ths) => Scan.succeed (app m (context, ths))));

fun sections ss = Scan.repeat (section ss);

fun sectioned_args args ss f src ctxt =
  let val ((x, _), ctxt') = syntax (args -- sections ss) src ctxt
  in f x ctxt' end;

fun bang_sectioned_args ss f = sectioned_args Args.bang_facts ss f;
fun bang_sectioned_args' ss scan f =
  sectioned_args (Args.bang_facts -- scan >> swap) ss (uncurry f);
fun only_sectioned_args ss f = sectioned_args (Scan.succeed ()) ss (fn () => f);

fun thms_ctxt_args f = sectioned_args (thms []) [] f;
fun thms_args f = thms_ctxt_args (K o f);
fun thm_args f = thms_args (fn [thm] => f thm | _ => error "Single theorem expected");

end;


(* extra rule methods *)

fun xrule_meth m =
  Scan.lift (Scan.optional (Args.parens OuterParse.nat) 0) -- Attrib.thms >>
  (fn (n, ths) => K (m n ths));


(* tactic syntax *)

fun goal_args' args tac src ctxt = fst (syntax (Args.goal_spec -- args >>
  (fn (quant, s) => SIMPLE_METHOD'' quant (tac s))) src ctxt);

fun goal_args args tac = goal_args' (Scan.lift args) tac;

fun goal_args_ctxt' args tac src ctxt =
  fst (syntax (Args.goal_spec -- args >>
  (fn (quant, s) => SIMPLE_METHOD'' quant (tac ctxt s))) src ctxt);

fun goal_args_ctxt args tac = goal_args_ctxt' (Scan.lift args) tac;


(* outer parser *)

fun is_symid_meth s =
  s <> "|" andalso s <> "?" andalso s <> "+" andalso OuterLex.ident_or_symbolic s;

local

fun meth4 x =
 (P.position (P.xname >> rpair []) >> (Source o Args.src) ||
  P.$$$ "(" |-- P.!!! (meth0 --| P.$$$ ")")) x
and meth3 x =
 (meth4 --| P.$$$ "?" >> Try ||
  meth4 --| P.$$$ "+" >> Repeat1 ||
  meth4 -- (P.$$$ "[" |-- Scan.optional P.nat 1 --| P.$$$ "]") >> (SelectGoals o swap) ||
  meth4) x
and meth2 x =
 (P.position (P.xname -- Args.parse1 is_symid_meth) >> (Source o Args.src) ||
  meth3) x
and meth1 x = (P.enum1 "," meth2 >> (fn [m] => m | ms => Then ms)) x
and meth0 x = (P.enum1 "|" meth1 >> (fn [m] => m | ms => Orelse ms)) x;

in val parse = meth3 end;


(* theory setup *)

val _ = Context.>> (Context.map_theory
 (setup (Binding.name "fail") (Scan.succeed (K fail)) "force failure" #>
  setup (Binding.name "succeed") (Scan.succeed (K succeed)) "succeed" #>
  setup (Binding.name "-") (Scan.succeed (K insert_facts))
    "do nothing (insert current facts only)" #>
  setup (Binding.name "insert") (Attrib.thms >> (K o insert))
    "insert theorems, ignoring facts (improper)" #>
  setup (Binding.name "intro") (Attrib.thms >> (K o intro))
    "repeatedly apply introduction rules" #>
  setup (Binding.name "elim") (Attrib.thms >> (K o elim))
    "repeatedly apply elimination rules" #>
  setup (Binding.name "unfold") (Attrib.thms >> unfold_meth) "unfold definitions" #>
  setup (Binding.name "fold") (Attrib.thms >> fold_meth) "fold definitions" #>
  setup (Binding.name "atomize") (Args.mode "full" >> (K o atomize))
    "present local premises as object-level statements" #>
  setup (Binding.name "rule") (Attrib.thms >> some_rule) "apply some intro/elim rule" #>
  setup (Binding.name "erule") (xrule_meth erule) "apply rule in elimination manner (improper)" #>
  setup (Binding.name "drule") (xrule_meth drule) "apply rule in destruct manner (improper)" #>
  setup (Binding.name "frule") (xrule_meth frule) "apply rule in forward manner (improper)" #>
  setup (Binding.name "this") (Scan.succeed (K this)) "apply current facts as rules" #>
  setup (Binding.name "fact") (Attrib.thms >> fact) "composition by facts from context" #>
  setup (Binding.name "assumption") (Scan.succeed assumption)
    "proof by assumption, preferring facts" #>
  setup (Binding.name "rename_tac") (Args.goal_spec -- Scan.lift (Scan.repeat1 Args.name) >>
    (fn (quant, xs) => K (SIMPLE_METHOD'' quant (Tactic.rename_tac xs))))
    "rename parameters of goal" #>
  setup (Binding.name "rotate_tac") (Args.goal_spec -- Scan.lift (Scan.optional P.int 1) >>
    (fn (quant, i) => K (SIMPLE_METHOD'' quant (Tactic.rotate_tac i))))
      "rotate assumptions of goal" #>
  setup (Binding.name "tactic") (Scan.lift (P.position Args.name) >> tactic)
    "ML tactic as proof method" #>
  setup (Binding.name "raw_tactic") (Scan.lift (P.position Args.name) >> raw_tactic)
    "ML tactic as raw proof method"));


(*final declarations of this structure!*)
val unfold = unfold_meth;
val fold = fold_meth;

end;

structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;

val RAW_METHOD_CASES = Method.RAW_METHOD_CASES;
val RAW_METHOD = Method.RAW_METHOD;
val METHOD_CASES = Method.METHOD_CASES;
val METHOD = Method.METHOD;
val SIMPLE_METHOD = Method.SIMPLE_METHOD;
val SIMPLE_METHOD' = Method.SIMPLE_METHOD';
val SIMPLE_METHOD'' = Method.SIMPLE_METHOD'';

