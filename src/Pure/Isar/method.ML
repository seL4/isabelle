(*  Title:      Pure/Isar/method.ML
    Author:     Markus Wenzel, TU Muenchen

Isar proof methods.
*)

signature METHOD =
sig
  type method
  val apply: (Proof.context -> method) -> Proof.context -> thm list -> cases_tactic
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
  val all_assm_tac: Proof.context -> tactic
  val assumption: Proof.context -> method
  val close: bool -> Proof.context -> method
  val rule_trace: bool Config.T
  val trace: Proof.context -> thm list -> unit
  val rule_tac: thm list -> thm list -> int -> tactic
  val some_rule_tac: thm list -> Proof.context -> thm list -> int -> tactic
  val intros_tac: thm list -> thm list -> tactic
  val try_intros_tac: thm list -> thm list -> tactic
  val rule: thm list -> method
  val erule: int -> thm list -> method
  val drule: int -> thm list -> method
  val frule: int -> thm list -> method
  val set_tactic: (thm list -> tactic) -> Proof.context -> Proof.context
  val tactic: string * Position.T -> Proof.context -> method
  val raw_tactic: string * Position.T -> Proof.context -> method
  type src = Args.src
  datatype text =
    Basic of Proof.context -> method |
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
  val print_methods: theory -> unit
  val intern: theory -> xstring -> string
  val defined: theory -> string -> bool
  val method: theory -> src -> Proof.context -> method
  val method_i: theory -> src -> Proof.context -> method
  val syntax: 'a context_parser -> src -> Proof.context -> 'a * Proof.context
  val setup: binding -> (Proof.context -> method) context_parser -> string -> theory -> theory
  val method_setup: bstring * Position.T -> Symbol_Pos.text * Position.T -> string ->
    theory -> theory
  type modifier = (Proof.context -> Proof.context) * attribute
  val section: modifier parser list -> thm list context_parser
  val sections: modifier parser list -> thm list list context_parser
  val parse: text parser
end;

structure Method: METHOD =
struct

(** proof methods **)

(* datatype method *)

datatype method = Meth of thm list -> cases_tactic;

fun apply meth ctxt = let val Meth m = meth ctxt in m end;

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

fun cheating int ctxt =
  if int orelse ! quick_and_dirty then
    METHOD (K (Skip_Proof.cheat_tac (Proof_Context.theory_of ctxt)))
  else error "Cheating requires quick_and_dirty mode!";


(* unfold intro/elim rules *)

fun intro ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.match_tac ths));
fun elim ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.ematch_tac ths));


(* unfold/fold definitions *)

fun unfold_meth ths ctxt = SIMPLE_METHOD (CHANGED_PROP (Local_Defs.unfold_tac ctxt ths));
fun fold_meth ths ctxt = SIMPLE_METHOD (CHANGED_PROP (Local_Defs.fold_tac ctxt ths));


(* atomize rule statements *)

fun atomize false = SIMPLE_METHOD' (CHANGED_PROP o Object_Logic.atomize_prems_tac)
  | atomize true = RAW_METHOD (K (HEADGOAL (CHANGED_PROP o Object_Logic.full_atomize_tac)));


(* this -- resolve facts directly *)

val this = METHOD (EVERY o map (HEADGOAL o Tactic.rtac));


(* fact -- composition by facts from context *)

fun fact [] ctxt = SIMPLE_METHOD' (Proof_Context.some_fact_tac ctxt)
  | fact rules _ = SIMPLE_METHOD' (Proof_Context.fact_tac rules);


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

fun all_assm_tac ctxt st = EVERY1 (replicate (Thm.nprems_of st) (assm_tac ctxt)) st;

fun assumption ctxt = METHOD (HEADGOAL o
  (fn [] => assm_tac ctxt
    | [fact] => solve_tac [fact]
    | _ => K no_tac));

fun close immed ctxt = METHOD (K
  (FILTER Thm.no_prems ((if immed then all_assm_tac ctxt else all_tac) THEN flexflex_tac)));

end;


(* rule etc. -- single-step refinements *)

val rule_trace = Attrib.setup_config_bool (Binding.name "rule_trace") (fn _ => false);

fun trace ctxt rules =
  if Config.get ctxt rule_trace andalso not (null rules) then
    Pretty.big_list "rules:" (map (Display.pretty_thm ctxt) rules)
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
      else flat (Context_Rules.find_rules false facts goal ctxt)
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

fun gen_intros_tac goals intros facts =
  goals (insert_tac facts THEN'
      REPEAT_ALL_NEW (resolve_tac intros))
    THEN Tactic.distinct_subgoals_tac;

val intros_tac = gen_intros_tac ALLGOALS;
val try_intros_tac = gen_intros_tac TRYALL;


(* ML tactics *)

structure ML_Tactic = Proof_Data
(
  type T = thm list -> tactic;
  fun init _ = undefined;
);

val set_tactic = ML_Tactic.put;

fun ml_tactic (txt, pos) ctxt =
  let
    val ctxt' = ctxt |> Context.proof_map
      (ML_Context.expression pos
        "fun tactic (facts: thm list) : tactic"
        "Context.map_proof (Method.set_tactic tactic)" (ML_Lex.read pos txt));
  in Context.setmp_thread_data (SOME (Context.Proof ctxt)) (ML_Tactic.get ctxt') end;

fun tactic txt ctxt = METHOD (ml_tactic txt ctxt);
fun raw_tactic txt ctxt = RAW_METHOD (ml_tactic txt ctxt);



(** method syntax **)

(* method text *)

type src = Args.src;

datatype text =
  Basic of Proof.context -> method |
  Source of src |
  Source_i of src |
  Then of text list |
  Orelse of text list |
  Try of text |
  Repeat1 of text |
  SelectGoals of int * text;

fun primitive_text r = Basic (K (SIMPLE_METHOD (PRIMITIVE r)));
val succeed_text = Basic (K succeed);
val default_text = Source (Args.src (("default", []), Position.none));
val this_text = Basic (K this);
val done_text = Basic (K (SIMPLE_METHOD all_tac));
fun sorry_text int = Basic (cheating int);

fun finish_text (NONE, immed) = Basic (close immed)
  | finish_text (SOME txt, immed) = Then [txt, Basic (close immed)];


(* method definitions *)

structure Methods = Theory_Data
(
  type T = ((src -> Proof.context -> method) * string) Name_Space.table;
  val empty : T = Name_Space.empty_table "method";
  val extend = I;
  fun merge data : T = Name_Space.merge_tables data;
);

fun print_methods thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val meths = Methods.get thy;
    fun prt_meth (name, (_, "")) = Pretty.str name
      | prt_meth (name, (_, comment)) =
          Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
  in
    [Pretty.big_list "methods:" (map prt_meth (Name_Space.extern_table ctxt meths))]
    |> Pretty.chunks |> Pretty.writeln
  end;

fun add_method name meth comment thy = thy
  |> Methods.map
    (Name_Space.define (Proof_Context.init_global thy) true (Sign.naming_of thy)
      (name, (meth, comment)) #> snd);


(* get methods *)

val intern = Name_Space.intern o #1 o Methods.get;
val defined = Symtab.defined o #2 o Methods.get;

fun method_i thy =
  let
    val (space, tab) = Methods.get thy;
    fun meth src =
      let val ((name, _), pos) = Args.dest_src src in
        (case Symtab.lookup tab name of
          NONE => error ("Unknown proof method: " ^ quote name ^ Position.str_of pos)
        | SOME (mth, _) => (Position.report pos (Name_Space.markup space name); mth src))
      end;
  in meth end;

fun method thy = method_i thy o Args.map_name (intern thy);


(* method setup *)

fun syntax scan = Args.context_syntax "method" scan;

fun setup name scan =
  add_method name
    (fn src => fn ctxt => let val (m, ctxt') = syntax scan src ctxt in m ctxt' end);

fun method_setup name (txt, pos) cmt =
  Context.theory_map (ML_Context.expression pos
    "val (name, scan, comment): binding * (Proof.context -> Proof.method) context_parser * string"
    "Context.map_theory (Method.setup name scan comment)"
    (ML_Lex.read Position.none ("(" ^ ML_Syntax.make_binding name ^ ", ") @
      ML_Lex.read pos txt @
      ML_Lex.read Position.none (", " ^ ML_Syntax.print_string cmt ^ ")")));



(** concrete syntax **)

(* sections *)

type modifier = (Proof.context -> Proof.context) * attribute;

local

fun thms ss = Scan.repeat (Scan.unless (Scan.lift (Scan.first ss)) Attrib.multi_thm) >> flat;
fun app (f, att) (context, ths) =
  Library.foldl_map (Thm.apply_attribute att) (Context.map_proof f context, ths);

in

fun section ss = Scan.depend (fn context => (Scan.first ss -- Scan.pass context (thms ss)) :|--
  (fn (m, ths) => Scan.succeed (app m (context, ths))));

fun sections ss = Scan.repeat (section ss);

end;


(* extra rule methods *)

fun xrule_meth m =
  Scan.lift (Scan.optional (Args.parens Parse.nat) 0) -- Attrib.thms >>
  (fn (n, ths) => K (m n ths));


(* outer parser *)

fun is_symid_meth s =
  s <> "|" andalso s <> "?" andalso s <> "+" andalso Token.ident_or_symbolic s;

local

fun meth4 x =
 (Parse.position (Parse.xname >> rpair []) >> (Source o Args.src) ||
  Parse.$$$ "(" |-- Parse.!!! (meth0 --| Parse.$$$ ")")) x
and meth3 x =
 (meth4 --| Parse.$$$ "?" >> Try ||
  meth4 --| Parse.$$$ "+" >> Repeat1 ||
  meth4 -- (Parse.$$$ "[" |-- Scan.optional Parse.nat 1 --| Parse.$$$ "]") >> (SelectGoals o swap) ||
  meth4) x
and meth2 x =
 (Parse.position (Parse.xname -- Args.parse1 is_symid_meth) >> (Source o Args.src) ||
  meth3) x
and meth1 x = (Parse.enum1 "," meth2 >> (fn [m] => m | ms => Then ms)) x
and meth0 x = (Parse.enum1 "|" meth1 >> (fn [m] => m | ms => Orelse ms)) x;

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
  setup (Binding.name "rotate_tac") (Args.goal_spec -- Scan.lift (Scan.optional Parse.int 1) >>
    (fn (quant, i) => K (SIMPLE_METHOD'' quant (Tactic.rotate_tac i))))
      "rotate assumptions of goal" #>
  setup (Binding.name "tactic") (Scan.lift Args.name_source_position >> tactic)
    "ML tactic as proof method" #>
  setup (Binding.name "raw_tactic") (Scan.lift Args.name_source_position >> raw_tactic)
    "ML tactic as raw proof method"));


(*final declarations of this structure!*)
val unfold = unfold_meth;
val fold = fold_meth;

end;

val RAW_METHOD_CASES = Method.RAW_METHOD_CASES;
val RAW_METHOD = Method.RAW_METHOD;
val METHOD_CASES = Method.METHOD_CASES;
val METHOD = Method.METHOD;
val SIMPLE_METHOD = Method.SIMPLE_METHOD;
val SIMPLE_METHOD' = Method.SIMPLE_METHOD';
val SIMPLE_METHOD'' = Method.SIMPLE_METHOD'';

