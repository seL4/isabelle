(*  Title:      Pure/Isar/method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

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
  val delrule_global: theory attribute
  val dest_local: Proof.context attribute
  val elim_local: Proof.context attribute
  val intro_local: Proof.context attribute
  val delrule_local: Proof.context attribute
  val METHOD: (thm list -> tactic) -> Proof.method
  val METHOD_CASES:
    (thm list -> thm -> (thm * (string * RuleCases.T) list) Seq.seq) -> Proof.method
  val METHOD0: tactic -> Proof.method
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
  val resolveq_tac: thm Seq.seq -> int -> tactic
  val resolveq_cases_tac: (thm * string list) Seq.seq
    -> int -> thm -> (thm * (string * RuleCases.T) list) Seq.seq
  val rule_tac: thm list -> thm list -> int -> tactic
  val rule: thm list -> Proof.method
  val erule: thm list -> Proof.method
  val drule: thm list -> Proof.method
  val frule: thm list -> Proof.method
  val this: Proof.method
  val assumption: Proof.context -> Proof.method
  val set_tactic: (Proof.context -> thm list -> tactic) -> unit
  val tactic: string -> Proof.context -> Proof.method
  exception METHOD_FAIL of (string * Position.T) * exn
  val help_methods: theory option -> unit
  val method: theory -> Args.src -> Proof.context -> Proof.method
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
    ('a -> Proof.context -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  val bang_sectioned_args:
    (Args.T list -> modifier * Args.T list) list ->
    (thm list -> Proof.context -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  val only_sectioned_args:
    (Args.T list -> modifier * Args.T list) list ->
    (Proof.context -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  val thms_ctxt_args: (thm list -> Proof.context -> Proof.method)
    -> Args.src -> Proof.context -> Proof.method
  val thms_args: (thm list -> Proof.method) -> Args.src -> Proof.context -> Proof.method
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
  val local_qed: text option
    -> ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val local_terminal_proof: text * text option
    -> ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val local_immediate_proof: ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val local_default_proof: ({kind: string, name: string, thm: thm} -> unit) * (thm -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val global_qed: text option -> Proof.state -> theory * {kind: string, name: string, thm: thm}
  val global_terminal_proof: text * text option
    -> Proof.state -> theory * {kind: string, name: string, thm: thm}
  val global_immediate_proof: Proof.state -> theory * {kind: string, name: string, thm: thm}
  val global_default_proof: Proof.state -> theory * {kind: string, name: string, thm: thm}
  val setup: (theory -> theory) list
end;

structure Method: METHOD =
struct


(** global and local rule data **)

fun prt_rules kind ths =
  Pretty.writeln (Pretty.big_list ("standard " ^ kind ^ " rules:") (map Display.pretty_thm ths));

fun print_rules (intro, elim) =
  (prt_rules "introduction" intro; prt_rules "elimination" elim);

fun merge_rules (ths1, ths2) = Library.generic_merge Thm.eq_thm I I ths1 ths2;


(* theory data kind 'Isar/rules' *)

structure GlobalRulesArgs =
struct
  val name = "Isar/rules";
  type T = thm list * thm list;

  val empty = ([], []);
  val copy = I;
  val prep_ext = I;
  fun merge ((intro1, elim1), (intro2, elim2)) =
    (merge_rules (intro1, intro2), merge_rules (elim1, elim2));
  fun print _ = print_rules;
end;

structure GlobalRules = TheoryDataFun(GlobalRulesArgs);
val print_global_rules = GlobalRules.print;


(* proof data kind 'Isar/rules' *)

structure LocalRulesArgs =
struct
  val name = "Isar/rules";
  type T = thm list * thm list;

  val init = GlobalRules.get;
  fun print _ = print_rules;
end;

structure LocalRules = ProofDataFun(LocalRulesArgs);
val print_local_rules = LocalRules.print;



(** attributes **)

(* add rules *)

local

fun add_rule thm rules = Library.gen_ins Thm.eq_thm (thm, rules);
fun del_rule thm rules = Library.gen_rem Thm.eq_thm (rules, thm);

fun add_dest thm (intro, elim) = (intro, add_rule (Tactic.make_elim thm) elim);
fun add_elim thm (intro, elim) = (intro, add_rule thm elim);
fun add_intro thm (intro, elim) = (add_rule thm intro, elim);
fun delrule thm (intro, elim) = (del_rule thm intro, del_rule thm elim);

fun mk_att f g (x, thm) = (f (g thm) x, thm);

in

val dest_global = mk_att GlobalRules.map add_dest;
val elim_global = mk_att GlobalRules.map add_elim;
val intro_global = mk_att GlobalRules.map add_intro;
val delrule_global = mk_att GlobalRules.map delrule;

val dest_local = mk_att LocalRules.map add_dest;
val elim_local = mk_att LocalRules.map add_elim;
val intro_local = mk_att LocalRules.map add_intro;
val delrule_local = mk_att LocalRules.map delrule;

end;


(* concrete syntax *)

val rule_atts =
 [("dest", (Attrib.no_args dest_global, Attrib.no_args dest_local), "destruction rule"),
  ("elim", (Attrib.no_args elim_global, Attrib.no_args elim_local), "elimination rule"),
  ("intro", (Attrib.no_args intro_global, Attrib.no_args intro_local), "introduction rule"),
  ("delrule", (Attrib.no_args delrule_global, Attrib.no_args delrule_local), "delete rule")];



(** proof methods **)

(* make methods *)

val METHOD = Proof.method;
val METHOD_CASES = Proof.method_cases;

fun METHOD0 tac = METHOD (fn [] => tac | _ => error "Method may not be used with facts");


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


(* unfold / fold definitions *)

fun unfold thms = METHOD (fn facts => ALLGOALS (insert_tac facts) THEN rewrite_goals_tac thms);
fun fold thms = METHOD (fn facts => ALLGOALS (insert_tac facts) THEN fold_goals_tac thms);


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

val resolveq_cases_tac = gen_resolveq_tac (fn (rule, cases) => fn i => fn st =>
  Seq.map (rpair (RuleCases.make rule cases)) (Tactic.rtac rule i st));


(* simple rule *)

local

fun gen_rule_tac tac rules [] = tac rules
  | gen_rule_tac tac erules facts = gen_resolveq_tac (tac o single) (multi_resolves facts erules);

fun gen_rule tac rules = METHOD (FINDGOAL o tac rules);

fun gen_rule' tac arg_rules ctxt = METHOD (fn facts =>
  let val rules =
    if not (null arg_rules) then arg_rules
    else if null facts then #1 (LocalRules.get ctxt)
    else op @ (LocalRules.get ctxt);
  in FINDGOAL (tac rules facts) end);

fun setup raw_tac =
  let val tac = gen_rule_tac raw_tac
  in (tac, gen_rule tac, gen_rule' tac) end;

in

val (rule_tac, rule, some_rule) = setup Tactic.resolve_tac;
val (erule_tac, erule, some_erule) = setup Tactic.eresolve_tac;
val (drule_tac, drule, some_drule) = setup Tactic.dresolve_tac;
val (frule_tac, frule, some_frule) = setup Tactic.forward_tac;

end;


(* this *)

val this = METHOD (EVERY o map (FINDGOAL o Tactic.rtac));


(* assumption *)

fun assm_tac ctxt =
  assume_tac APPEND' resolve_tac (filter Thm.no_prems (ProofContext.prems_of ctxt));

fun assumption_tac ctxt [] = assm_tac ctxt
  | assumption_tac _ [fact] = resolve_tac [fact]
  | assumption_tac _ _ = K no_tac;

fun assumption ctxt = METHOD (FINDGOAL o assumption_tac ctxt);


(* res_inst_tac emulations *)

(*Note: insts refer to the implicit (!) goal context; use at your own risk*)
fun gen_res_inst tac ((i, insts), thm) =
  METHOD (fn facts => (insert_tac facts THEN' tac insts thm) i);

val res_inst = gen_res_inst Tactic.res_inst_tac;
val eres_inst = gen_res_inst Tactic.eres_inst_tac;
val dres_inst = gen_res_inst Tactic.dres_inst_tac;
val forw_inst = gen_res_inst Tactic.forw_inst_tac;


(* simple Prolog interpreter *)

fun prolog_tac rules facts =
  DEPTH_SOLVE_1 (HEADGOAL (Tactic.assume_tac APPEND' Tactic.resolve_tac (facts @ rules)));

val prolog = METHOD o prolog_tac;


(* ML tactics *)

val tactic_ref = ref ((fn _ => raise Match): Proof.context -> thm list -> tactic);
fun set_tactic f = tactic_ref := f;

fun tactic txt ctxt = METHOD (fn facts =>
 (Context.use_mltext
   ("let fun (tactic: Proof.context -> thm list -> tactic) ctxt facts = \
    \let val thm = ProofContext.get_thm ctxt and thms = ProofContext.get_thms ctxt in\n"
    ^ txt ^
    "\nend in Method.set_tactic tactic end")
  false (Some (ProofContext.theory_of ctxt)); ! tactic_ref ctxt facts));



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

  fun print_meths verbose {space, meths} =
    let
      fun prt_meth (name, ((_, comment), _)) = Pretty.block
        [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    in
      if not verbose then ()
      else Pretty.writeln (Display.pretty_name_space ("method name space", space));
      Pretty.writeln (Pretty.big_list "methods:"
        (map prt_meth (NameSpace.cond_extern_table space meths)))
    end;

  fun print _ = print_meths true;
end;

structure MethodsData = TheoryDataFun(MethodsDataArgs);
val print_methods = MethodsData.print;

fun help_methods None = writeln "methods: (unkown theory context)"
  | help_methods (Some thy) = MethodsDataArgs.print_meths false (MethodsData.get thy);


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


(* add_methods *)

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
fun only_sectioned_args ss f = sectioned_args (Scan.succeed ()) ss (fn () => f);

fun thms_ctxt_args f = sectioned_args (thmss []) [] f;
fun thms_args f = thms_ctxt_args (K o f);

end;


(* insts *)

val insts =
  Scan.lift (Scan.optional (Args.$$$ "(" |-- Args.!!! (Args.nat --| Args.$$$ ")")) 1) --
    Args.enum1 "and" (Scan.lift (Args.name -- Args.!!! (Args.$$$ "=" |-- Args.name))) --
    (Scan.lift (Args.$$$ "in") |-- Attrib.local_thm);

fun inst_args f = f oo (#2 oo syntax insts);



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

fun finish ctxt = METHOD (K (FILTER Thm.no_prems (ALLGOALS (assm_tac ctxt) THEN flexflex_tac)));

fun finish_text None = Basic finish
  | finish_text (Some txt) = Then [txt, Basic finish];

fun proof opt_text state =
  state
  |> Proof.assert_backward
  |> refine (if_none opt_text default_text)
  |> Seq.map (Proof.goal_facts (K []))
  |> Seq.map Proof.enter_forward;

fun local_qed opt_text = Proof.local_qed (refine (finish_text opt_text));
fun local_terminal_proof (text, opt_text) pr = Seq.THEN (proof (Some text), local_qed opt_text pr);
val local_immediate_proof = local_terminal_proof (this_text, None);
val local_default_proof = local_terminal_proof (default_text, None);


fun global_qeds opt_text = Proof.global_qed (refine (finish_text opt_text));

fun global_qed opt_text state =
  state
  |> global_qeds opt_text
  |> Proof.check_result "Failed to finish proof" state
  |> Seq.hd;

fun global_terminal_proof (text, opt_text) state =
  state
  |> proof (Some text)
  |> Proof.check_result "Terminal proof method failed" state
  |> (Seq.flat o Seq.map (global_qeds opt_text))
  |> Proof.check_result "Failed to finish proof (after successful terminal method)" state
  |> Seq.hd;

val global_immediate_proof = global_terminal_proof (this_text, None);
val global_default_proof = global_terminal_proof (default_text, None);



(** theory setup **)

(* pure_methods *)

val pure_methods =
 [("fail", no_args fail, "force failure"),
  ("succeed", no_args succeed, "succeed"),
  ("-", no_args insert_facts, "do nothing, inserting current facts only"),
  ("insert", thms_args insert, "insert theorems, ignoring facts (improper!)"),
  ("unfold", thms_args unfold, "unfold definitions"),
  ("fold", thms_args fold, "fold definitions"),
  ("default", thms_ctxt_args some_rule, "apply some rule"),
  ("rule", thms_ctxt_args some_rule, "apply some rule"),
  ("erule", thms_ctxt_args some_erule, "apply some rule in elimination manner (improper!)"),
  ("drule", thms_ctxt_args some_drule, "apply some rule in destruct manner (improper!)"),
  ("frule", thms_ctxt_args some_frule, "apply some rule in forward manner (improper!)"),
  ("this", no_args this, "apply current facts as rules"),
  ("assumption", ctxt_args assumption, "proof by assumption, preferring facts"),
  ("res_inst_tac", inst_args res_inst, "res_inst_tac emulation (beware!)"),
  ("eres_inst_tac", inst_args eres_inst, "eres_inst_tac emulation (beware!)"),
  ("dres_inst_tac", inst_args dres_inst, "dres_inst_tac emulation (beware!)"),
  ("forw_inst_tac", inst_args forw_inst, "forw_inst_tac emulation (beware!)"),
  ("prolog", thms_args prolog, "simple prolog interpreter"),
  ("tactic", simple_args Args.name tactic, "ML tactic as proof method")];


(* setup *)

val setup =
 [GlobalRules.init, LocalRules.init, Attrib.add_attributes rule_atts,
  MethodsData.init, add_methods pure_methods];


end;


structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
