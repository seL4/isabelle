(*  Title:      Pure/Isar/method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Proof methods.
*)

signature BASIC_METHOD =
sig
  val trace_rules: bool ref
  val print_methods: theory -> unit
  val Method: bstring -> (Args.src -> Proof.context -> Proof.method) -> string -> unit
end;

signature METHOD =
sig
  include BASIC_METHOD
  val trace: thm list -> unit
  val print_global_rules: theory -> unit
  val print_local_rules: Proof.context -> unit
  val dest_global: theory attribute
  val elim_global: theory attribute
  val intro_global: theory attribute
  val dest_bang_global: theory attribute
  val elim_bang_global: theory attribute
  val intro_bang_global: theory attribute
  val rule_del_global: theory attribute
  val dest_local: Proof.context attribute
  val elim_local: Proof.context attribute
  val intro_local: Proof.context attribute
  val dest_bang_local: Proof.context attribute
  val elim_bang_local: Proof.context attribute
  val intro_bang_local: Proof.context attribute
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
  val multi_resolve: thm list -> thm -> thm Seq.seq
  val multi_resolves: thm list -> thm list -> thm Seq.seq
  val rule_tac: thm list -> thm list -> int -> tactic
  val some_rule_tac: thm list -> Proof.context -> thm list -> int -> tactic
  val rule: thm list -> Proof.method
  val erule: int -> thm list -> Proof.method
  val drule: int -> thm list -> Proof.method
  val frule: int -> thm list -> Proof.method
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


(** tracing *)

val trace_rules = ref false;

fun trace rules =
  if not (! trace_rules) orelse null rules then ()
  else Pretty.writeln (Pretty.big_list "rules:" (map Display.pretty_thm rules));



(** global and local rule data **)

val intro_bangK = 0;
val elim_bangK = 1;
val introK = 2;
val elimK = 3;

local

fun kind_name 0 = "safe introduction rules (intro!)"
  | kind_name 1 = "safe elimination rules (elim!)"
  | kind_name 2 = "introduction rules (intro)"
  | kind_name 3 = "elimination rules (elim)"
  | kind_name _ = "unknown";

fun prt_rules sg (k, rs) =
  Pretty.writeln (Pretty.big_list (kind_name k ^ ":")
    (map (Display.pretty_thm_sg sg) (NetRules.rules rs)));

in
  fun print_rules sg rules = seq (prt_rules sg) (0 upto length rules - 1 ~~ rules);
end;


(* theory data kind 'Isar/rules' *)

structure GlobalRulesArgs =
struct
  val name = "Isar/rules";
  type T = thm NetRules.T list;

  val empty = [NetRules.intro, NetRules.elim, NetRules.intro, NetRules.elim];
  val copy = I;
  val prep_ext = I;
  fun merge x = map2 NetRules.merge x;
  val print = print_rules;
end;

structure GlobalRules = TheoryDataFun(GlobalRulesArgs);
val print_global_rules = GlobalRules.print;


(* proof data kind 'Isar/rules' *)

structure LocalRulesArgs =
struct
  val name = GlobalRulesArgs.name;
  type T = GlobalRulesArgs.T;
  val init = GlobalRules.get;
  val print = print_rules o ProofContext.sign_of;
end;

structure LocalRules = ProofDataFun(LocalRulesArgs);
val print_local_rules = LocalRules.print;



(** attributes **)

(* add rules *)

local

fun add_rule k view th = Library.map_nth_elem k (NetRules.insert (view th));

val add_intro      = add_rule introK I;
val add_elim       = add_rule elimK I;
val add_dest       = add_rule elimK Tactic.make_elim;
val add_intro_bang = add_rule intro_bangK I;
val add_elim_bang  = add_rule elim_bangK I;
val add_dest_bang  = add_rule elim_bangK Tactic.make_elim;

fun del_rule th = map (NetRules.delete th o NetRules.delete (Tactic.make_elim th));

fun mk_att f g (x, th) = (f (g th) x, th);

in

val dest_global = mk_att GlobalRules.map add_dest;
val elim_global = mk_att GlobalRules.map add_elim;
val intro_global = mk_att GlobalRules.map add_intro;
val dest_bang_global = mk_att GlobalRules.map add_dest_bang;
val elim_bang_global = mk_att GlobalRules.map add_elim_bang;
val intro_bang_global = mk_att GlobalRules.map add_intro_bang;
val rule_del_global = mk_att GlobalRules.map del_rule;

val dest_local = mk_att LocalRules.map add_dest;
val elim_local = mk_att LocalRules.map add_elim;
val intro_local = mk_att LocalRules.map add_intro;
val dest_bang_local = mk_att LocalRules.map add_dest_bang;
val elim_bang_local = mk_att LocalRules.map add_elim_bang;
val intro_bang_local = mk_att LocalRules.map add_intro_bang;
val rule_del_local = mk_att LocalRules.map del_rule;

fun del_args att = Attrib.syntax (Scan.lift Args.del >> K att);

end;


(* concrete syntax *)

val rule_atts =
 [("dest",
   (Attrib.bang_args dest_bang_global dest_global,
    Attrib.bang_args dest_bang_local dest_local),
    "declaration of destruction rule"),
  ("elim",
   (Attrib.bang_args elim_bang_global elim_global,
    Attrib.bang_args elim_bang_local elim_local),
    "declaration of elimination rule"),
  ("intro",
   (Attrib.bang_args intro_bang_global intro_global,
    Attrib.bang_args intro_bang_local intro_local),
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

fun unfold thms = SIMPLE_METHOD (CHANGED_PROP (rewrite_goals_tac thms));
fun fold thms = SIMPLE_METHOD (CHANGED_PROP (fold_goals_tac thms));


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


(* basic rules *)

local

fun gen_rule_tac tac rules [] i st = tac rules i st
  | gen_rule_tac tac erules facts i st =
      Seq.flat (Seq.map (fn rule => (tac o single) rule i st) (multi_resolves facts erules));

fun gen_arule_tac tac j rules facts =
  EVERY' (gen_rule_tac tac rules facts :: replicate j Tactic.assume_tac);

fun find_erules [] _ = []
  | find_erules (fact :: _) rs =
      NetRules.retrieve rs (Logic.strip_assums_concl (#prop (Thm.rep_thm fact)));

fun find_rules goal rs = NetRules.retrieve rs (Logic.strip_assums_concl goal);

fun gen_some_rule_tac tac arg_rules ctxt facts = SUBGOAL (fn (goal, i) =>
  let
    fun get k = nth_elem (k, LocalRules.get ctxt);
    val rules =
      if not (null arg_rules) then arg_rules
      else find_erules facts (get elim_bangK) @ find_erules facts (get elimK) @
        find_rules goal (get intro_bangK) @ find_rules goal (get introK);
  in trace rules; tac rules facts i end);

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


(* this *)

val this = METHOD (EVERY o map (HEADGOAL o Tactic.rtac));


(* assumption *)

fun asm_tac ths =
  foldr (op APPEND') (map (fn th => Tactic.rtac th THEN_ALL_NEW assume_tac) ths, K no_tac);

fun assm_tac ctxt =
  assume_tac APPEND'
  asm_tac (ProofContext.prems_of ctxt) APPEND'
  Tactic.rtac Drule.reflexive_thm;

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

fun nat_thms_args f = uncurry f oo
  (#2 oo syntax (Scan.lift (Scan.optional (Args.parens Args.nat) 0) -- Attrib.local_thmss));

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
  ("atomize", no_args (SIMPLE_METHOD' HEADGOAL ObjectLogic.atomize_tac),
    "present local premises as object-level statements"),
  ("rule", thms_ctxt_args some_rule, "apply some rule"),
  ("erule", nat_thms_args erule, "apply rule in elimination manner (improper)"),
  ("drule", nat_thms_args drule, "apply rule in destruct manner (improper)"),
  ("frule", nat_thms_args frule, "apply rule in forward manner (improper)"),
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
  MethodsData.init, add_methods pure_methods,
  (#1 o PureThy.add_thms [(("", Drule.equal_intr_rule), [intro_global])])];


end;


structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
