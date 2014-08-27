(*  Title:      Pure/Isar/method.ML
    Author:     Markus Wenzel, TU Muenchen

Isar proof methods.
*)

signature METHOD =
sig
  type method = thm list -> cases_tactic
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
  val cheating: Proof.context -> bool -> method
  val intro: thm list -> method
  val elim: thm list -> method
  val unfold: thm list -> Proof.context -> method
  val fold: thm list -> Proof.context -> method
  val atomize: bool -> Proof.context -> method
  val this: method
  val fact: thm list -> Proof.context -> method
  val assm_tac: Proof.context -> int -> tactic
  val all_assm_tac: Proof.context -> tactic
  val assumption: Proof.context -> method
  val rule_trace: bool Config.T
  val trace: Proof.context -> thm list -> unit
  val rule_tac: Proof.context -> thm list -> thm list -> int -> tactic
  val some_rule_tac: Proof.context -> thm list -> thm list -> int -> tactic
  val intros_tac: thm list -> thm list -> tactic
  val try_intros_tac: thm list -> thm list -> tactic
  val rule: Proof.context -> thm list -> method
  val erule: Proof.context -> int -> thm list -> method
  val drule: Proof.context -> int -> thm list -> method
  val frule: Proof.context -> int -> thm list -> method
  val set_tactic: (morphism -> thm list -> tactic) -> Context.generic -> Context.generic
  type combinator_info
  val no_combinator_info: combinator_info
  datatype combinator = Then | Orelse | Try | Repeat1 | Select_Goals of int
  datatype text =
    Source of Token.src |
    Basic of Proof.context -> method |
    Combinator of combinator_info * combinator * text list
  val map_source: (Token.src -> Token.src) -> text -> text
  val primitive_text: (Proof.context -> thm -> thm) -> text
  val succeed_text: text
  val default_text: text
  val this_text: text
  val done_text: text
  val sorry_text: bool -> text
  val finish_text: text option * bool -> text
  val print_methods: Proof.context -> unit
  val check_name: Proof.context -> xstring * Position.T -> string
  val method_syntax: (Proof.context -> method) context_parser ->
    Token.src -> Proof.context -> method
  val setup: binding -> (Proof.context -> method) context_parser -> string -> theory -> theory
  val local_setup: binding -> (Proof.context -> method) context_parser -> string ->
    local_theory -> local_theory
  val method_setup: bstring * Position.T -> Symbol_Pos.source -> string ->
    local_theory -> local_theory
  val method: Proof.context -> Token.src -> Proof.context -> method
  val method_closure: Proof.context -> Token.src -> Token.src
  val method_cmd: Proof.context -> Token.src -> Proof.context -> method
  val evaluate: text -> Proof.context -> method
  type modifier = {init: Proof.context -> Proof.context, attribute: attribute, pos: Position.T}
  val modifier: attribute -> Position.T -> modifier
  val section: modifier parser list -> declaration context_parser
  val sections: modifier parser list -> declaration list context_parser
  type text_range = text * Position.range
  val text: text_range option -> text option
  val position: text_range option -> Position.T
  val reports_of: text_range -> Position.report list
  val report: text_range -> unit
  val parse: text_range parser
end;

structure Method: METHOD =
struct

(** proof methods **)

(* method *)

type method = thm list -> cases_tactic;

fun METHOD_CASES tac : method = fn facts => Seq.THEN (ALLGOALS Goal.conjunction_tac, tac facts);
fun METHOD tac : method = fn facts => NO_CASES (ALLGOALS Goal.conjunction_tac THEN tac facts);

val fail = METHOD (K no_tac);
val succeed = METHOD (K all_tac);


(* insert facts *)

local

fun cut_rule_tac rule =
  rtac (Drule.forall_intr_vars rule COMP_INCR revcut_rl);

in

fun insert_tac [] _ = all_tac
  | insert_tac facts i = EVERY (map (fn th => cut_rule_tac th i) facts);

val insert_facts = METHOD (ALLGOALS o insert_tac);
fun insert thms = METHOD (fn _ => ALLGOALS (insert_tac thms));

fun SIMPLE_METHOD tac = METHOD (fn facts => ALLGOALS (insert_tac facts) THEN tac);
fun SIMPLE_METHOD'' quant tac = METHOD (fn facts => quant (insert_tac facts THEN' tac));
val SIMPLE_METHOD' = SIMPLE_METHOD'' HEADGOAL;

end;


(* cheating *)

fun cheating ctxt int = METHOD (fn _ => fn st =>
  if int orelse Config.get ctxt quick_and_dirty then
    ALLGOALS Skip_Proof.cheat_tac st
  else error "Cheating requires quick_and_dirty mode!");


(* unfold intro/elim rules *)

fun intro ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (match_tac ths));
fun elim ths = SIMPLE_METHOD' (CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ths));


(* unfold/fold definitions *)

fun unfold_meth ths ctxt = SIMPLE_METHOD (CHANGED_PROP (Local_Defs.unfold_tac ctxt ths));
fun fold_meth ths ctxt = SIMPLE_METHOD (CHANGED_PROP (Local_Defs.fold_tac ctxt ths));


(* atomize rule statements *)

fun atomize false ctxt =
      SIMPLE_METHOD' (CHANGED_PROP o Object_Logic.atomize_prems_tac ctxt)
  | atomize true ctxt =
      NO_CASES o K (HEADGOAL (CHANGED_PROP o Object_Logic.full_atomize_tac ctxt));


(* this -- resolve facts directly *)

val this = METHOD (EVERY o map (HEADGOAL o rtac));


(* fact -- composition by facts from context *)

fun fact [] ctxt = SIMPLE_METHOD' (Proof_Context.some_fact_tac ctxt)
  | fact rules ctxt = SIMPLE_METHOD' (Proof_Context.fact_tac ctxt rules);


(* assumption *)

local

fun cond_rtac cond rule = SUBGOAL (fn (prop, i) =>
  if cond (Logic.strip_assums_concl prop)
  then rtac rule i else no_tac);

in

fun assm_tac ctxt =
  assume_tac APPEND'
  Goal.assume_rule_tac ctxt APPEND'
  cond_rtac (can Logic.dest_equals) Drule.reflexive_thm APPEND'
  cond_rtac (can Logic.dest_term) Drule.termI;

fun all_assm_tac ctxt =
  let
    fun tac i st =
      if i > Thm.nprems_of st then all_tac st
      else ((assm_tac ctxt i THEN tac i) ORELSE tac (i + 1)) st;
  in tac 1 end;

fun assumption ctxt = METHOD (HEADGOAL o
  (fn [] => assm_tac ctxt
    | [fact] => solve_tac [fact]
    | _ => K no_tac));

fun finish immed ctxt =
  METHOD (K ((if immed then all_assm_tac ctxt else all_tac) THEN flexflex_tac));

end;


(* rule etc. -- single-step refinements *)

val rule_trace = Attrib.setup_config_bool @{binding rule_trace} (fn _ => false);

fun trace ctxt rules =
  if Config.get ctxt rule_trace andalso not (null rules) then
    Pretty.big_list "rules:" (map (Display.pretty_thm_item ctxt) rules)
    |> Pretty.string_of |> tracing
  else ();

local

fun gen_rule_tac tac ctxt rules facts =
  (fn i => fn st =>
    if null facts then tac rules i st
    else Seq.maps (fn rule => (tac o single) rule i st) (Drule.multi_resolves facts rules))
  THEN_ALL_NEW Goal.norm_hhf_tac ctxt;

fun gen_arule_tac tac ctxt j rules facts =
  EVERY' (gen_rule_tac tac ctxt rules facts :: replicate j assume_tac);

fun gen_some_rule_tac tac ctxt arg_rules facts = SUBGOAL (fn (goal, i) =>
  let
    val rules =
      if not (null arg_rules) then arg_rules
      else flat (Context_Rules.find_rules false facts goal ctxt)
  in trace ctxt rules; tac ctxt rules facts i end);

fun meth tac x y = METHOD (HEADGOAL o tac x y);
fun meth' tac x y z = METHOD (HEADGOAL o tac x y z);

in

val rule_tac = gen_rule_tac resolve_tac;
val rule = meth rule_tac;
val some_rule_tac = gen_some_rule_tac rule_tac;
val some_rule = meth some_rule_tac;

val erule = meth' (gen_arule_tac eresolve_tac);
val drule = meth' (gen_arule_tac dresolve_tac);
val frule = meth' (gen_arule_tac forward_tac);

end;


(* intros_tac -- pervasive search spanned by intro rules *)

fun gen_intros_tac goals intros facts =
  goals (insert_tac facts THEN'
      REPEAT_ALL_NEW (resolve_tac intros))
    THEN Tactic.distinct_subgoals_tac;

val intros_tac = gen_intros_tac ALLGOALS;
val try_intros_tac = gen_intros_tac TRYALL;



(** method syntax **)

(* context data *)

structure Data = Generic_Data
(
  type T =
    ((Token.src -> Proof.context -> method) * string) Name_Space.table *  (*methods*)
    (morphism -> thm list -> tactic) option;  (*ML tactic*)
  val empty : T = (Name_Space.empty_table "method", NONE);
  val extend = I;
  fun merge ((tab, tac), (tab', tac')) : T =
    (Name_Space.merge_tables (tab, tab'), merge_options (tac, tac'));
);

val get_methods = fst o Data.get;
val map_methods = Data.map o apfst;


(* ML tactic *)

val set_tactic = Data.map o apsnd o K o SOME;

fun the_tactic context =
  (case snd (Data.get context) of
    SOME tac => tac
  | NONE => raise Fail "Undefined ML tactic");

val parse_tactic =
  Scan.state :|-- (fn context =>
    Scan.lift (Args.text_declaration (fn source =>
      let
        val context' = context |>
          ML_Context.expression (#pos source)
            "fun tactic (morphism: Morphism.morphism) (facts: thm list) : tactic"
            "Method.set_tactic tactic" (ML_Lex.read_source false source);
        val tac = the_tactic context';
      in
        fn phi =>
          set_tactic (fn _ => Context.setmp_thread_data (SOME context) (tac phi))
      end)) >> (fn decl => Morphism.form (the_tactic (Morphism.form decl context))));


(* method text *)

datatype combinator_info = Combinator_Info of {keywords: Position.T list};
fun combinator_info keywords = Combinator_Info {keywords = keywords};
val no_combinator_info = combinator_info [];

datatype combinator = Then | Orelse | Try | Repeat1 | Select_Goals of int;

datatype text =
  Source of Token.src |
  Basic of Proof.context -> method |
  Combinator of combinator_info * combinator * text list;

fun map_source f (Source src) = Source (f src)
  | map_source _ (Basic meth) = Basic meth
  | map_source f (Combinator (info, comb, txts)) = Combinator (info, comb, map (map_source f) txts);

fun primitive_text r = Basic (SIMPLE_METHOD o PRIMITIVE o r);
val succeed_text = Basic (K succeed);
val default_text = Source (Token.src ("default", Position.none) []);
val this_text = Basic (K this);
val done_text = Basic (K (SIMPLE_METHOD all_tac));
fun sorry_text int = Basic (fn ctxt => cheating ctxt int);

fun finish_text (NONE, immed) = Basic (finish immed)
  | finish_text (SOME txt, immed) =
      Combinator (no_combinator_info, Then, [txt, Basic (finish immed)]);


(* method definitions *)

fun transfer_methods ctxt =
  let
    val meths0 = get_methods (Context.Theory (Proof_Context.theory_of ctxt));
    val meths' = Name_Space.merge_tables (meths0, get_methods (Context.Proof ctxt));
  in Context.proof_map (map_methods (K meths')) ctxt end;

fun print_methods ctxt =
  let
    val meths = get_methods (Context.Proof ctxt);
    fun prt_meth (name, (_, "")) = Pretty.mark_str name
      | prt_meth (name, (_, comment)) =
          Pretty.block
            (Pretty.mark_str name :: Pretty.str ":" :: Pretty.brk 2 :: Pretty.text comment);
  in
    [Pretty.big_list "methods:" (map prt_meth (Name_Space.markup_table ctxt meths))]
    |> Pretty.writeln_chunks
  end;


(* define *)

fun define_global binding meth comment thy =
  let
    val context = Context.Theory thy;
    val (name, meths') =
      Name_Space.define context true (binding, (meth, comment)) (get_methods context);
  in (name, Context.the_theory (map_methods (K meths') context)) end;

fun define binding meth comment =
  Local_Theory.background_theory_result (define_global binding meth comment)
  #-> (fn name =>
    Local_Theory.map_contexts (K transfer_methods)
    #> Local_Theory.generic_alias map_methods binding name
    #> pair name);


(* check *)

fun check_name ctxt =
  let val context = Context.Proof ctxt
  in #1 o Name_Space.check context (get_methods context) end;

fun check_src ctxt src =
  Token.check_src ctxt (get_methods (Context.Proof ctxt)) src;


(* method setup *)

fun method_syntax scan src ctxt : method =
  let val (m, ctxt') = Token.syntax scan src ctxt in m ctxt' end;

fun setup binding scan comment = define_global binding (method_syntax scan) comment #> snd;
fun local_setup binding scan comment = define binding (method_syntax scan) comment #> snd;

fun method_setup name source cmt =
  (ML_Lex.read Position.none ("(" ^ ML_Syntax.make_binding name ^ ", ") @
    ML_Lex.read_source false source @
    ML_Lex.read Position.none (", " ^ ML_Syntax.print_string cmt ^ ")"))
  |> ML_Context.expression (#pos source)
    "val (name, scan, comment): binding * (Proof.context -> Proof.method) context_parser * string"
    "Context.map_proof (Method.local_setup name scan comment)"
  |> Context.proof_map;


(* prepare methods *)

fun method ctxt =
  let val table = get_methods (Context.Proof ctxt)
  in fn src => #1 (Name_Space.get table (#1 (Token.name_of_src src))) src end;

fun method_closure ctxt0 src0 =
  let
    val (src1, _) = check_src ctxt0 src0;
    val src2 = Token.init_assignable_src src1;
    val ctxt = Context_Position.not_really ctxt0;
    val _ = Seq.pull (method ctxt src2 ctxt [] (Goal.protect 0 Drule.dummy_thm));
  in Token.closure_src src2 end;

fun method_cmd ctxt = method ctxt o method_closure ctxt;


(* evaluate method text *)

local

fun APPEND_CASES (meth: cases_tactic) (cases, st) =
  meth st |> Seq.map (fn (cases', st') => (cases @ cases', st'));

fun BYPASS_CASES (tac: tactic) (cases, st) =
  tac st |> Seq.map (pair cases);

val op THEN = Seq.THEN;

fun SELECT_GOALS n method =
  BYPASS_CASES
    (ALLGOALS Goal.conjunction_tac THEN PRIMITIVE (Goal.restrict 1 n) THEN Goal.conjunction_tac 1)
  THEN method
  THEN BYPASS_CASES (PRIMITIVE (Goal.unrestrict 1));

fun COMBINATOR1 comb [meth] = comb meth
  | COMBINATOR1 _ _ = raise Fail "Method combinator requires exactly one argument";

fun combinator Then = Seq.EVERY
  | combinator Orelse = Seq.FIRST
  | combinator Try = COMBINATOR1 Seq.TRY
  | combinator Repeat1 = COMBINATOR1 Seq.REPEAT1
  | combinator (Select_Goals n) = COMBINATOR1 (SELECT_GOALS n);

in

fun evaluate text ctxt =
  let
    fun eval (Basic meth) = APPEND_CASES o meth ctxt
      | eval (Source src) = APPEND_CASES o method_cmd ctxt src ctxt
      | eval (Combinator (_, c, txts)) =
          let
            val comb = combinator c;
            val meths = map eval txts;
          in fn facts => comb (map (fn meth => meth facts) meths) end;
    val meth = eval text;
  in fn facts => fn st => meth facts ([], st) end;

end;



(** concrete syntax **)

(* type modifier *)

type modifier =
  {init: Proof.context -> Proof.context, attribute: attribute, pos: Position.T};

fun modifier attribute pos : modifier = {init = I, attribute = attribute, pos = pos};


(* sections *)

local

fun sect (modifier : modifier parser) = Scan.depend (fn context =>
  let
    val ctxt = Context.proof_of context;
    fun prep_att src =
      let
        val src' = Attrib.check_src ctxt src;
        val _ = List.app (Token.assign NONE) (Token.args_of_src src');
      in src' end;
    val parse_thm =
      Parse.xthm >> (fn (a, bs) => (Proof_Context.get_fact ctxt a, map prep_att bs));
  in
    Scan.ahead Parse.not_eof -- modifier -- Scan.repeat (Scan.unless modifier parse_thm) >>
      (fn ((tok, {init, attribute, pos}), thms) =>
        let
          val decl =
            (case Token.get_value tok of
              SOME (Token.Declaration decl) => decl
            | _ =>
                let
                  val facts =
                    Attrib.partial_evaluation ctxt [((Binding.name "dummy", []), thms)]
                    |> map (fn (_, bs) => ((Binding.empty, [Attrib.internal (K attribute)]), bs));
                  val _ =
                    Context_Position.report ctxt (Token.pos_of tok)
                      (Markup.entity Markup.method_modifierN ""
                        |> Markup.properties (Position.def_properties_of pos));
                  fun decl phi =
                    Context.mapping I init #>
                    Attrib.generic_notes "" (Attrib.transform_facts phi facts) #> snd;
                  val _ = Token.assign (SOME (Token.Declaration decl)) tok;
                in decl end);
        in (Morphism.form decl context, decl) end)
  end);

in

val section = sect o Scan.first;
val sections = Scan.repeat o section;

end;


(* extra rule methods *)

fun xrule_meth meth =
  Scan.lift (Scan.optional (Args.parens Parse.nat) 0) -- Attrib.thms >>
  (fn (n, ths) => fn ctxt => meth ctxt n ths);


(* text range *)

type text_range = text * Position.range;

fun text NONE = NONE
  | text (SOME (txt, _)) = SOME txt;

fun position NONE = Position.none
  | position (SOME (_, (pos, _))) = pos;


(* reports *)

local

fun keyword_positions (Source _) = []
  | keyword_positions (Basic _) = []
  | keyword_positions (Combinator (Combinator_Info {keywords}, _, texts)) =
      keywords @ maps keyword_positions texts;

in

fun reports_of ((text, (pos, _)): text_range) =
  (pos, Markup.language_method) ::
    maps (fn p => map (pair p) (Markup.keyword3 :: Completion.suppress_abbrevs ""))
      (keyword_positions text);

val report = Position.reports o reports_of;

end;


(* outer parser *)

fun is_symid_meth s =
  s <> "|" andalso s <> "?" andalso s <> "+" andalso Token.ident_or_symbolic s;

local

fun meth4 x =
 (Parse.position Parse.xname >> (fn name => Source (Token.src name [])) ||
  Scan.ahead Parse.cartouche |-- Parse.not_eof >> (fn tok =>
    Source (Token.src ("cartouche", Token.pos_of tok) [tok])) ||
  Parse.$$$ "(" |-- Parse.!!! (meth0 --| Parse.$$$ ")")) x
and meth3 x =
 (meth4 -- Parse.position (Parse.$$$ "?")
    >> (fn (m, (_, pos)) => Combinator (combinator_info [pos], Try, [m])) ||
  meth4 -- Parse.position (Parse.$$$ "+")
    >> (fn (m, (_, pos)) => Combinator (combinator_info [pos], Repeat1, [m])) ||
  meth4 --
    (Parse.position (Parse.$$$ "[") -- Scan.optional Parse.nat 1 -- Parse.position (Parse.$$$ "]"))
    >> (fn (m, (((_, pos1), n), (_, pos2))) =>
        Combinator (combinator_info [pos1, pos2], Select_Goals n, [m])) ||
  meth4) x
and meth2 x =
 (Parse.position Parse.xname -- Parse.args1 is_symid_meth >> (Source o uncurry Token.src) ||
  meth3) x
and meth1 x =
  (Parse.enum1_positions "," meth2
    >> (fn ([m], _) => m | (ms, ps) => Combinator (combinator_info ps, Then, ms))) x
and meth0 x =
  (Parse.enum1_positions "|" meth1
    >> (fn ([m], _) => m | (ms, ps) => Combinator (combinator_info ps, Orelse, ms))) x;

in

val parse =
  Scan.trace meth3 >> (fn (m, toks) => (m, Token.range_of toks));

end;


(* theory setup *)

val _ = Theory.setup
 (setup @{binding fail} (Scan.succeed (K fail)) "force failure" #>
  setup @{binding succeed} (Scan.succeed (K succeed)) "succeed" #>
  setup @{binding "-"} (Scan.succeed (K insert_facts))
    "do nothing (insert current facts only)" #>
  setup @{binding insert} (Attrib.thms >> (K o insert))
    "insert theorems, ignoring facts (improper)" #>
  setup @{binding intro} (Attrib.thms >> (K o intro))
    "repeatedly apply introduction rules" #>
  setup @{binding elim} (Attrib.thms >> (K o elim))
    "repeatedly apply elimination rules" #>
  setup @{binding unfold} (Attrib.thms >> unfold_meth) "unfold definitions" #>
  setup @{binding fold} (Attrib.thms >> fold_meth) "fold definitions" #>
  setup @{binding atomize} (Scan.lift (Args.mode "full") >> atomize)
    "present local premises as object-level statements" #>
  setup @{binding rule} (Attrib.thms >> (fn ths => fn ctxt => some_rule ctxt ths))
    "apply some intro/elim rule" #>
  setup @{binding erule} (xrule_meth erule) "apply rule in elimination manner (improper)" #>
  setup @{binding drule} (xrule_meth drule) "apply rule in destruct manner (improper)" #>
  setup @{binding frule} (xrule_meth frule) "apply rule in forward manner (improper)" #>
  setup @{binding this} (Scan.succeed (K this)) "apply current facts as rules" #>
  setup @{binding fact} (Attrib.thms >> fact) "composition by facts from context" #>
  setup @{binding assumption} (Scan.succeed assumption)
    "proof by assumption, preferring facts" #>
  setup @{binding rename_tac} (Args.goal_spec -- Scan.lift (Scan.repeat1 Args.name) >>
    (fn (quant, xs) => K (SIMPLE_METHOD'' quant (rename_tac xs))))
    "rename parameters of goal" #>
  setup @{binding rotate_tac} (Args.goal_spec -- Scan.lift (Scan.optional Parse.int 1) >>
    (fn (quant, i) => K (SIMPLE_METHOD'' quant (rotate_tac i))))
      "rotate assumptions of goal" #>
  setup @{binding tactic} (parse_tactic >> (K o METHOD))
    "ML tactic as proof method" #>
  setup @{binding raw_tactic} (parse_tactic >> (fn tac => fn _ => NO_CASES o tac))
    "ML tactic as raw proof method");


(*final declarations of this structure!*)
val unfold = unfold_meth;
val fold = fold_meth;

end;

val METHOD_CASES = Method.METHOD_CASES;
val METHOD = Method.METHOD;
val SIMPLE_METHOD = Method.SIMPLE_METHOD;
val SIMPLE_METHOD' = Method.SIMPLE_METHOD';
val SIMPLE_METHOD'' = Method.SIMPLE_METHOD'';

