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
  val etac: text -> Proof.state -> Proof.state Seq.seq
  val proof: text option -> Proof.state -> Proof.state Seq.seq
  val end_block: Proof.state -> Proof.state Seq.seq
  val terminal_proof: text -> Proof.state -> Proof.state Seq.seq
  val trivial_proof: Proof.state -> Proof.state Seq.seq
  val default_proof: Proof.state -> Proof.state Seq.seq
  val qed: bstring option -> theory attribute list option -> Proof.state
    -> theory * (string * string * tthm)
  val syntax: (Args.T list -> 'a * Args.T list) -> ('a -> 'b) -> Args.src -> 'b
  val no_args: 'a -> Args.src -> Proof.context -> 'a
  val thm_args: (tthm list -> 'a) -> Args.src -> Proof.context -> 'a
  val sectioned_args: (Proof.context -> 'a) -> ('a * tthm list -> 'b) ->
    (string * ('b * tthm list -> 'b)) list -> ('b -> 'c) -> Args.src -> Proof.context -> 'c
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
        val thms = map Attribute.thm_of facts;
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

fun rule_tac rules [] = resolve_tac (map Attribute.thm_of rules)
  | rule_tac erules facts =
      let
        val rules = forward_chain (map Attribute.thm_of facts) (map Attribute.thm_of erules);
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

    fun meth ((raw_name, args), pos) =
      let val name = NameSpace.intern space raw_name in
        (case Symtab.lookup (meths, name) of
          None => error ("Unknown proof method: " ^ quote name ^ Position.str_of pos)
        | Some ((mth, _), _) => mth ((name, args), pos))
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


(* argument syntax *)

val methodN = "method";
fun syntax scan = Args.syntax methodN scan;

fun no_args x = syntax (Scan.succeed (fn (_: Proof.context) => x)) I;

(* FIXME move? *)
fun thm_args f = syntax (Scan.repeat Args.name)
  (fn names => fn ctxt => f (ProofContext.get_tthmss ctxt names));

fun sectioned_args get_data def_sect sects f =
  syntax (Args.sectioned (map fst sects))
    (fn (names, sect_names) => fn ctxt =>
      let
        val get_thms = ProofContext.get_tthmss ctxt;
        val thms = get_thms names;
        val sect_thms = map (apsnd get_thms) sect_names;

        fun apply_sect (data, (s, ths)) =
          (case assoc (sects, s) of
            Some add => add (data, ths)
          | None => error ("Unknown argument section " ^ quote s));
       in f (foldl apply_sect (def_sect (get_data ctxt, thms), sect_thms)) end);



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
  method (ProofContext.theory_of ctxt) ((name, []), Position.none) ctxt);


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

fun etac text state =
  state
  |> Proof.goal_facts Proof.the_facts
  |> refine text;


(* proof steps *)

val default_txt = Source (("default", []), Position.none);
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
  ("rule", thm_args rule, "apply primitive rule")];


(* setup *)

val setup = [MethodsData.init, add_methods pure_methods];


end;


structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
