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
  val METHOD: (thm list -> tactic) -> Proof.method
  val METHOD0: tactic -> Proof.method
  val fail: Proof.method
  val succeed: Proof.method
  val insert_tac: thm list -> int -> tactic
  val insert: thm list -> Proof.method
  val insert_facts: Proof.method
  val unfold: thm list -> Proof.method
  val fold: thm list -> Proof.method
  val multi_resolve: thm list -> thm -> thm Seq.seq
  val multi_resolves: thm list -> thm list -> thm Seq.seq
  val rule_tac: thm list -> thm list -> int -> tactic
  val erule_tac: thm list -> thm list -> int -> tactic
  val rule: thm list -> Proof.method
  val erule: thm list -> Proof.method
  val assumption: Proof.context -> Proof.method
  exception METHOD_FAIL of (string * Position.T) * exn
  val help_methods: theory -> unit
  val method: theory -> Args.src -> Proof.context -> Proof.method
  val add_methods: (bstring * (Args.src -> Proof.context -> Proof.method) * string) list
    -> theory -> theory
  val syntax: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list)) ->
    Proof.context -> Args.src -> Proof.context * 'a
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
  val thms_args: (thm list -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  datatype text =
    Basic of (Proof.context -> Proof.method) |
    Source of Args.src |
    Then of text list |
    Orelse of text list |
    Try of text |
    Repeat1 of text
  val refine: text -> Proof.state -> Proof.state Seq.seq
  val refine_no_facts: text -> Proof.state -> Proof.state Seq.seq
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


(** proof methods **)

(* method from tactic *)

val METHOD = Proof.method;
fun METHOD0 tac = METHOD (fn [] => tac | _ => error "Method may not be used with facts");


(* primitive *)

val fail = METHOD (K no_tac);
val succeed = METHOD (K all_tac);


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
fun insert thms = METHOD (fn facts => ALLGOALS (insert_tac (thms @ facts)));

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


(* rule *)

local

fun gen_rule_tac tac rules [] = tac rules
  | gen_rule_tac tac erules facts =
      let
        val rules = multi_resolves facts erules;
        fun tactic i state = Seq.flat (Seq.map (fn rule => tac [rule] i state) rules);
      in tactic end;

in

val rule_tac = gen_rule_tac Tactic.resolve_tac;
val erule_tac = gen_rule_tac Tactic.eresolve_tac;

fun rule rules = METHOD (FIRSTGOAL o rule_tac rules);
fun erule rules = METHOD (FIRSTGOAL o erule_tac rules);

end;


(* assumption / finish *)

fun assm_tac ctxt =
  assume_tac APPEND' resolve_tac (filter Thm.no_prems (ProofContext.prems_of ctxt));

fun assumption_tac ctxt [] = assm_tac ctxt
  | assumption_tac _ [fact] = resolve_tac [fact]
  | assumption_tac _ _ = K no_tac;

fun assumption ctxt = METHOD (FIRSTGOAL o assumption_tac ctxt);
fun finish ctxt = METHOD (K (FILTER Thm.no_prems (ALLGOALS (assm_tac ctxt))));



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
val help_methods = MethodsDataArgs.print_meths false o MethodsData.get;


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

fun ctxt_args (f: Proof.context -> Proof.method) src ctxt =
  #2 (syntax (Scan.succeed (f ctxt)) ctxt src);

fun no_args m = ctxt_args (K m);


(* sections *)

type modifier = (Proof.context -> Proof.context) * Proof.context attribute;

local

fun sect ss = Scan.first (map (fn s => Scan.lift (s --| Args.$$$ ":")) ss);
fun thms ss = Scan.unless (sect ss) Attrib.local_thms;
fun thmss ss = Scan.repeat (thms ss) >> flat;

fun apply (f, att) (ctxt, ths) = Thm.applys_attributes ((f ctxt, ths), [att]);

fun section ss = (sect ss -- thmss ss) :-- (fn (m, ths) => Scan.depend (fn ctxt =>
  Scan.succeed (apply m (ctxt, ths)))) >> #2;

fun sectioned args ss = args -- Scan.repeat (section ss);

in

fun sectioned_args args ss f src ctxt =
  let val (ctxt', (x, _)) = syntax (sectioned args ss) ctxt src
  in f x ctxt' end;

fun bang_sectioned_args ss f = sectioned_args Args.bang_facts ss f;
fun only_sectioned_args ss f = sectioned_args (Scan.succeed ()) ss (fn () => f);

fun thms_args f = sectioned_args (thmss []) [] (fn ths => fn _ => f ths);

end;



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

fun refine text state =
  let
    val thy = Proof.theory_of state;

    fun eval (Basic mth) = Proof.refine mth
      | eval (Source src) = Proof.refine (method thy src)
      | eval (Then txts) = Seq.EVERY (map eval txts)
      | eval (Orelse txts) = Seq.FIRST (map eval txts)
      | eval (Try txt) = Seq.TRY (eval txt)
      | eval (Repeat1 txt) = Seq.REPEAT1 (eval txt);
  in eval text state end;

fun refine_no_facts text state =
  state
  |> Proof.goal_facts (K [])
  |> refine text;


(* structured proof steps *)

val default_text = Source (Args.src (("default", []), Position.none));

fun finish_text None = Basic finish
  | finish_text (Some txt) = Then [txt, Basic finish];

fun proof opt_text state =
  state
  |> Proof.assert_backward
  |> refine (if_none opt_text default_text)
  |> Seq.map Proof.enter_forward;

fun local_qed opt_text = Proof.local_qed (refine (finish_text opt_text));
fun local_terminal_proof (text, opt_text) pr = Seq.THEN (proof (Some text), local_qed opt_text pr);
val local_immediate_proof = local_terminal_proof (Basic assumption, None);
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

val global_immediate_proof = global_terminal_proof (Basic assumption, None);
val global_default_proof = global_terminal_proof (default_text, None);



(** theory setup **)

(* pure_methods *)

val pure_methods =
 [("fail", no_args fail, "force failure"),
  ("succeed", no_args succeed, "succeed"),
  ("-", no_args insert_facts, "do nothing, inserting current facts only"),
  ("insert", thms_args insert, "insert facts (improper!)"),
  ("unfold", thms_args unfold, "unfold definitions"),
  ("fold", thms_args fold, "fold definitions"),
  ("rule", thms_args rule, "apply some rule"),
  ("erule", thms_args erule, "apply some erule (improper!)"),
  ("assumption", ctxt_args assumption, "proof by assumption, preferring facts")];


(* setup *)

val setup = [MethodsData.init, add_methods pure_methods];


end;


structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
