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
  val LIFT: tactic -> thm -> (thm * (indexname * term) list * (string * tthm list) list) Seq.seq
  val METHOD: (tthm list -> tactic) -> Proof.method
  val METHOD0: tactic -> Proof.method
  val fail: Proof.method
  val succeed: Proof.method
  val trivial: Proof.method
  val assumption: Proof.method
  val forward_chain: thm list -> thm list -> thm Seq.seq
  val rule_tac: tthm list -> tthm list -> int -> tactic
  val rule: tthm list -> Proof.method
  val method: theory -> Args.src -> Proof.context -> Proof.method
  val add_methods: (bstring * (Args.src -> Proof.context -> Proof.method) * string) list
    -> theory -> theory
  val syntax: (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list)) ->
    Proof.context -> Args.src -> Proof.context * 'a
  val no_args: Proof.method -> Args.src -> Proof.context -> Proof.method
  val sectioned_args: ((Args.T list -> Proof.context attribute * Args.T list) list ->
      Proof.context * Args.T list -> 'a * (Proof.context * Args.T list)) ->
    (Args.T list -> Proof.context attribute * Args.T list) list ->
    ('a -> Proof.context -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  val default_sectioned_args: Proof.context attribute ->
    (Args.T list -> Proof.context attribute * Args.T list) list ->
    (Proof.context -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  val only_sectioned_args: (Args.T list -> Proof.context attribute * Args.T list) list ->
    (Proof.context -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  val thms_args: (tthm list -> Proof.method) -> Args.src -> Proof.context -> Proof.method
  datatype text =
    Basic of (Proof.context -> Proof.method) |
    Source of Args.src |
    Then of text list |
    Orelse of text list |
    Try of text |
    Repeat of text |
    Repeat1 of text
  val dynamic_method: string -> (Proof.context -> Proof.method)
  val refine: text -> Proof.state -> Proof.state Seq.seq
  val tac: text -> Proof.state -> Proof.state Seq.seq
  val then_tac: text -> Proof.state -> Proof.state Seq.seq
  val proof: text option -> Proof.state -> Proof.state Seq.seq
  val end_block: Proof.state -> Proof.state Seq.seq
  val terminal_proof: text -> Proof.state -> Proof.state Seq.seq
  val trivial_proof: Proof.state -> Proof.state Seq.seq
  val default_proof: Proof.state -> Proof.state Seq.seq
  val qed: bstring option -> theory attribute list option -> Proof.state
    -> theory * (string * string * tthm)
  val setup: (theory -> theory) list
end;

structure Method: METHOD =
struct


(** proof methods **)

(* method from tactic *)

fun LIFT tac goal = Seq.map (fn x => (x, [], [])) (tac goal);
fun METHOD tacf = Proof.method (LIFT o tacf);
fun METHOD0 tac = METHOD (fn [] => tac | _ => error "Method may not be used with facts");


(* primitive *)

val fail = METHOD (K no_tac);
val succeed = METHOD (K all_tac);


(* trivial, assumption *)

fun trivial_tac [] = K all_tac
  | trivial_tac facts =
      let
        val thms = Attribute.thms_of facts;
        val r = ~ (length facts);
      in metacuts_tac thms THEN' rotate_tac r end;

val trivial = METHOD (ALLGOALS o trivial_tac);
val assumption = METHOD (fn facts => FIRSTGOAL (trivial_tac facts THEN' assume_tac));

val asm_finish = METHOD (K (TRYALL assume_tac));


(* rule *)

fun res th i rule = Thm.biresolution false [(false, th)] i rule handle THM _ => Seq.empty;

fun multi_resolve facts rule =
  let
    fun multi_res i [] = Seq.single rule
      | multi_res i (th :: ths) = Seq.flat (Seq.map (res th i) (multi_res (i + 1) ths))
  in multi_res 1 facts end;

fun forward_chain facts rules = Seq.flat (Seq.map (multi_resolve facts) (Seq.of_list rules));

fun rule_tac rules [] = resolve_tac (Attribute.thms_of rules)
  | rule_tac erules facts =
      let
        val rules = forward_chain (Attribute.thms_of facts) (Attribute.thms_of erules);
        fun tac i state = Seq.flat (Seq.map (fn rule => Tactic.rtac rule i state) rules);
      in tac end;

fun rule rules = METHOD (FIRSTGOAL o rule_tac rules);



(** methods theory data **)

(* data kind 'Isar/methods' *)

structure MethodsDataArgs =
struct
  val name = "Isar/methods";
  type T =
    {space: NameSpace.T,
     meths: (((Args.src -> Proof.context -> Proof.method) * string) * stamp) Symtab.table};

  val empty = {space = NameSpace.empty, meths = Symtab.empty};
  val prep_ext = I;
  fun merge ({space = space1, meths = meths1}, {space = space2, meths = meths2}) =
    {space = NameSpace.merge (space1, space2),
      meths = Symtab.merge eq_snd (meths1, meths2) handle Symtab.DUPS dups =>
        error ("Attempt to merge different versions of methods " ^ commas_quote dups)};

  fun print _ {space, meths} =
    let
      fun prt_meth (name, ((_, comment), _)) = Pretty.block
        [Pretty.str (NameSpace.cond_extern space name ^ ":"), Pretty.brk 2, Pretty.str comment];
    in
      Pretty.writeln (Display.pretty_name_space ("method name space", space));
      Pretty.writeln (Pretty.big_list "methods:" (map prt_meth (Symtab.dest meths)))
    end;
end;

structure MethodsData = TheoryDataFun(MethodsDataArgs);
val print_methods = MethodsData.print;


(* get methods *)

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
        | Some ((mth, _), _) => mth src)
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

fun no_args (x: Proof.method) src ctxt = #2 (syntax (Scan.succeed x) ctxt src);


(* sections *)

fun sect ss = Scan.first (map (fn s => Scan.lift (s --| Args.$$$ ":")) ss);
fun thms ss = Scan.unless (sect ss) Attrib.local_thms;
fun thmss ss = Scan.repeat (thms ss) >> flat;

fun apply att (ctxt, ths) = Attribute.applys ((ctxt, ths), [att]);

fun section ss = (sect ss -- thmss ss) :-- (fn (att, ths) => Scan.depend (fn ctxt =>
  Scan.succeed (apply att (ctxt, ths)))) >> #2;

fun sectioned args ss = args ss -- Scan.repeat (section ss);


fun sectioned_args args ss f src ctxt =
  let val (ctxt', (x, thss)) = syntax (sectioned args ss) ctxt src
  in
    warning "TRACE thms:"; seq Attribute.print_tthm (flat thss);             (* FIXME *)
    f x ctxt'
  end;

fun default_sectioned_args att ss f src ctxt =
  sectioned_args thmss ss (fn ths => fn ctxt' => f (#1 (apply att (ctxt', ths)))) src ctxt;

fun only_sectioned_args ss f = sectioned_args (K (Scan.succeed ())) ss (fn () => f);
fun thms_args f = sectioned_args thmss [] (fn ths => fn _ => f ths);



(** method text **)

(* datatype text *)

datatype text =
  Basic of (Proof.context -> Proof.method) |
  Source of Args.src |
  Then of text list |
  Orelse of text list |
  Try of text |
  Repeat of text |
  Repeat1 of text;


(* dynamic methods *)

fun dynamic_method name = (fn ctxt =>
  method (ProofContext.theory_of ctxt) (Args.src ((name, []), Position.none)) ctxt);


(* refine *)

fun refine text state =
  let
    val thy = Proof.theory_of state;

    fun eval (Basic mth) = Proof.refine mth
      | eval (Source src) = Proof.refine (method thy src)
      | eval (Then txts) = Seq.EVERY (map eval txts)
      | eval (Orelse txts) = Seq.FIRST (map eval txts)
      | eval (Try txt) = Seq.TRY (eval txt)
      | eval (Repeat txt) = Seq.REPEAT (eval txt)
      | eval (Repeat1 txt) = Seq.REPEAT1 (eval txt);
  in eval text state end;


(* unstructured steps *)

fun tac text state =
  state
  |> Proof.goal_facts (K [])
  |> refine text;

fun then_tac text state =
  state
  |> Proof.goal_facts Proof.the_facts
  |> refine text;


(* proof steps *)

val default_txt = Source (Args.src (("default", []), Position.none));
val finishN = "finish";

fun proof opt_text state =
  state
  |> Proof.assert_backward
  |> refine (if_none opt_text default_txt)
  |> Seq.map Proof.enter_forward;


(* conclusions *)

val end_block = Proof.end_block (dynamic_method finishN);

fun terminal_proof text = Seq.THEN (proof (Some text), end_block);
val trivial_proof = terminal_proof (Basic (K trivial));
val default_proof = terminal_proof default_txt;

val qed = Proof.qed (dynamic_method finishN);



(** theory setup **)

(* pure_methods *)

val pure_methods =
 [("fail", no_args fail, "force failure"),
  ("succeed", no_args succeed, "succeed"),
  ("trivial", no_args trivial, "proof all goals trivially"),
  ("assumption", no_args assumption, "proof by assumption"),
  ("finish", no_args asm_finish, "finish proof by assumption"),
  ("rule", thms_args rule, "apply primitive rule")];


(* setup *)

val setup = [MethodsData.init, add_methods pure_methods];


end;


structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
