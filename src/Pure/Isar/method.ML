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
  val Method: bstring -> (Args.src -> ProofContext.context -> method) -> string -> unit
end;

signature METHOD =
sig
  include BASIC_METHOD
  val multi_resolve: thm list -> thm -> thm Seq.seq
  val multi_resolves: thm list -> thm list -> thm Seq.seq
  val apply: method -> thm list -> RuleCases.tactic;
  val RAW_METHOD_CASES: (thm list -> RuleCases.tactic) -> method
  val RAW_METHOD: (thm list -> tactic) -> method
  val METHOD_CASES: (thm list -> RuleCases.tactic) -> method
  val METHOD: (thm list -> tactic) -> method
  val fail: method
  val succeed: method
  val insert_tac: thm list -> int -> tactic
  val insert: thm list -> method
  val insert_facts: method
  val SIMPLE_METHOD: tactic -> method
  val SIMPLE_METHOD': ((int -> tactic) -> tactic) -> (int -> tactic) -> method
  val defer: int option -> method
  val prefer: int -> method
  val cheating: bool -> ProofContext.context -> method
  val intro: thm list -> method
  val elim: thm list -> method
  val unfold: thm list -> method
  val fold: thm list -> method
  val atomize: bool -> method
  val this: method
  val assumption: ProofContext.context -> method
  val close: bool -> ProofContext.context -> method
  val trace: ProofContext.context -> thm list -> unit
  val rule_tac: thm list -> thm list -> int -> tactic
  val some_rule_tac: thm list -> ProofContext.context -> thm list -> int -> tactic
  val rule: thm list -> method
  val erule: int -> thm list -> method
  val drule: int -> thm list -> method
  val frule: int -> thm list -> method
  val iprover_tac: ProofContext.context -> int option -> int -> tactic
  val bires_inst_tac: bool -> ProofContext.context -> (indexname * string) list ->
    thm -> int -> tactic
  val set_tactic: (ProofContext.context -> thm list -> tactic) -> unit
  val tactic: string -> ProofContext.context -> method
  type src
  datatype text =
    Basic of (ProofContext.context -> method) |
    Source of src |
    Then of text list |
    Orelse of text list |
    Try of text |
    Repeat1 of text
  val default_text: text
  val this_text: text
  val done_text: text
  val sorry_text: bool -> text
  val finish_text: text option * bool -> text
  exception METHOD_FAIL of (string * Position.T) * exn
  val method: theory -> src -> ProofContext.context -> method
  val add_methods: (bstring * (src -> ProofContext.context -> method) * string) list
    -> theory -> theory
  val add_method: bstring * (src -> ProofContext.context -> method) * string
    -> theory -> theory
  val method_setup: bstring * string * string -> theory -> theory
  val syntax: (ProofContext.context * Args.T list -> 'a * (ProofContext.context * Args.T list))
    -> src -> ProofContext.context -> ProofContext.context * 'a
  val simple_args: (Args.T list -> 'a * Args.T list)
    -> ('a -> ProofContext.context -> method) -> src -> ProofContext.context -> method
  val ctxt_args: (ProofContext.context -> method) -> src -> ProofContext.context -> method
  val no_args: method -> src -> ProofContext.context -> method
  type modifier
  val sectioned_args: (ProofContext.context * Args.T list ->
      'a * (ProofContext.context * Args.T list)) ->
    (Args.T list -> modifier * Args.T list) list ->
    ('a -> ProofContext.context -> 'b) -> src -> ProofContext.context -> 'b
  val bang_sectioned_args:
    (Args.T list -> modifier * Args.T list) list ->
    (thm list -> ProofContext.context -> 'a) -> src -> ProofContext.context -> 'a
  val bang_sectioned_args':
    (Args.T list -> modifier * Args.T list) list ->
    (ProofContext.context * Args.T list -> 'a * (ProofContext.context * Args.T list)) ->
    ('a -> thm list -> ProofContext.context -> 'b) -> src -> ProofContext.context -> 'b
  val only_sectioned_args:
    (Args.T list -> modifier * Args.T list) list ->
    (ProofContext.context -> 'a) -> src -> ProofContext.context -> 'a
  val thms_ctxt_args: (thm list -> ProofContext.context -> 'a) -> src ->
    ProofContext.context -> 'a
  val thms_args: (thm list -> 'a) -> src -> ProofContext.context -> 'a
  val thm_args: (thm -> 'a) -> src -> ProofContext.context -> 'a
  val goal_args: (Args.T list -> 'a * Args.T list) -> ('a -> int -> tactic)
    -> src -> ProofContext.context -> method
  val goal_args': (ProofContext.context * Args.T list ->
      'a * (ProofContext.context * Args.T list))
    -> ('a -> int -> tactic) -> src -> ProofContext.context -> method
  val goal_args_ctxt: (Args.T list -> 'a * Args.T list) ->
    (ProofContext.context -> 'a -> int -> tactic) -> src -> ProofContext.context -> method
  val goal_args_ctxt': (ProofContext.context * Args.T list ->
    'a * (ProofContext.context * Args.T list)) ->
    (ProofContext.context -> 'a -> int -> tactic) -> src -> ProofContext.context -> method
end;

structure Method: METHOD =
struct

(** generic tools **)

(* goal addressing *)

fun FINDGOAL tac st =
  let fun find i n = if i > n then Seq.fail else Seq.APPEND (tac i, find (i + 1) n)
  in find 1 (Thm.nprems_of st) st end;

fun HEADGOAL tac = tac 1;


(* multi_resolve *)

local

fun res th i rule =
  Thm.biresolution false [(false, th)] i rule handle THM _ => Seq.empty;

fun multi_res _ [] rule = Seq.single rule
  | multi_res i (th :: ths) rule = Seq.maps (res th i) (multi_res (i + 1) ths rule);

in

val multi_resolve = multi_res 1;
fun multi_resolves facts rules = Seq.maps (multi_resolve facts) (Seq.of_list rules);

end;



(** proof methods **)

(* datatype method *)

datatype method = Meth of thm list -> RuleCases.tactic;

fun apply (Meth m) = m;

val RAW_METHOD_CASES = Meth;

fun RAW_METHOD tac = RAW_METHOD_CASES (NO_CASES o tac);

fun METHOD_CASES tac = RAW_METHOD_CASES (fn facts =>
  Seq.THEN (TRY Tactic.conjunction_tac, tac facts));

fun METHOD tac = RAW_METHOD (fn facts =>
  TRY Tactic.conjunction_tac THEN tac facts);

val fail = METHOD (K no_tac);
val succeed = METHOD (K all_tac);


(* insert facts *)

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

fun SIMPLE_METHOD tac = METHOD (fn facts => ALLGOALS (insert_tac facts) THEN tac);
fun SIMPLE_METHOD' quant tac = METHOD (fn facts => quant (insert_tac facts THEN' tac));

end;


(* shuffle subgoals *)

fun prefer i = METHOD (K (Tactic.defer_tac i THEN PRIMITIVE (Thm.permute_prems 0 ~1)));
fun defer opt_i = METHOD (K (Tactic.defer_tac (if_none opt_i 1)));


(* cheating *)

fun cheating int ctxt = METHOD (K (setmp quick_and_dirty (int orelse ! quick_and_dirty)
    (SkipProof.cheat_tac (ProofContext.theory_of ctxt))));


(* unfold intro/elim rules *)

fun intro ths = SIMPLE_METHOD' HEADGOAL (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.match_tac ths));
fun elim ths = SIMPLE_METHOD' HEADGOAL (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.ematch_tac ths));


(* unfold/fold definitions *)

fun unfold_meth ths = SIMPLE_METHOD (CHANGED_PROP (rewrite_goals_tac ths));
fun fold_meth ths = SIMPLE_METHOD (CHANGED_PROP (fold_goals_tac ths));


(* atomize rule statements *)

fun atomize false = SIMPLE_METHOD' HEADGOAL (CHANGED_PROP o ObjectLogic.atomize_tac)
  | atomize true = RAW_METHOD (K (HEADGOAL (CHANGED_PROP o ObjectLogic.full_atomize_tac)));


(* this -- apply facts directly *)

val this = METHOD (EVERY o map (HEADGOAL o Tactic.rtac));


(* assumption *)

local

fun asm_tac ths =
  foldr (op APPEND') (K no_tac) (map (fn th => Tactic.rtac th THEN_ALL_NEW assume_tac) ths);

val refl_tac = SUBGOAL (fn (prop, i) =>
  if can Logic.dest_equals (Logic.strip_assums_concl prop)
  then Tactic.rtac Drule.reflexive_thm i else no_tac);

fun assm_tac ctxt =
  assume_tac APPEND'
  asm_tac (ProofContext.prems_of ctxt) APPEND'
  refl_tac;

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
  conditional (! trace_rules andalso not (null rules)) (fn () =>
    Pretty.big_list "rules:" (map (ProofContext.pretty_thm ctxt) rules)
    |> Pretty.string_of |> tracing);

local

fun gen_rule_tac tac rules [] i st = tac rules i st
  | gen_rule_tac tac rules facts i st =
      Seq.maps (fn rule => (tac o single) rule i st) (multi_resolves facts rules);

fun gen_arule_tac tac j rules facts =
  EVERY' (gen_rule_tac tac rules facts :: replicate j Tactic.assume_tac);

fun gen_some_rule_tac tac arg_rules ctxt facts = SUBGOAL (fn (goal, i) =>
  let
    val rules =
      if not (null arg_rules) then arg_rules
      else List.concat (ContextRules.find_rules false facts goal ctxt)
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
    REPEAT_DETERM_N (length prems - length (gen_distinct op aconv prems))
    (Tactic.ematch_tac [Drule.remdups_rl] i THEN Tactic.eq_assume_tac i)
  end);

fun REMDUPS tac = tac THEN_ALL_NEW remdups_tac;

fun gen_eq_set e s1 s2 =
  length s1 = length s2 andalso
  gen_subset e (s1, s2) andalso gen_subset e (s2, s1);

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
    if gen_mem (fn ((ps1, c1), (ps2, c2)) =>
      c1 aconv c2 andalso gen_eq_set op aconv ps1 ps2) ((ps, c), gs) then no_tac
    else (step_tac ctxt THEN_ALL_NEW intprover_tac ctxt ((ps, c) :: gs) (d + 1) lim) i
  end);

in

fun iprover_tac ctxt opt_lim =
  SELECT_GOAL (DEEPEN (2, if_none opt_lim 20) (intprover_tac ctxt [] 0) 4 1);

end;


(* rule_tac etc. -- refer to dynamic goal state!! *)

fun bires_inst_tac bires_flag ctxt insts thm =
  let
    val thy = ProofContext.theory_of ctxt;
    (* Separate type and term insts *)
    fun has_type_var ((x, _), _) = (case Symbol.explode x of
          "'"::cs => true | cs => false);
    val Tinsts = List.filter has_type_var insts;
    val tinsts = filter_out has_type_var insts;
    (* Tactic *)
    fun tac i st =
      let
        (* Preprocess state: extract environment information:
           - variables and their types
           - type variables and their sorts
           - parameters and their types *)
        val (types, sorts) = types_sorts st;
    (* Process type insts: Tinsts_env *)
    fun absent xi = error
          ("No such variable in theorem: " ^ Syntax.string_of_vname xi);
    val (rtypes, rsorts) = types_sorts thm;
    fun readT (xi, s) =
        let val S = case rsorts xi of SOME S => S | NONE => absent xi;
            val T = Sign.read_typ (thy, sorts) s;
            val U = TVar (xi, S);
        in if Sign.typ_instance thy (T, U) then (U, T)
           else error
             ("Instantiation of " ^ Syntax.string_of_vname xi ^ " fails")
        end;
    val Tinsts_env = map readT Tinsts;
    (* Preprocess rule: extract vars and their types, apply Tinsts *)
    fun get_typ xi =
      (case rtypes xi of
           SOME T => typ_subst_atomic Tinsts_env T
         | NONE => absent xi);
    val (xis, ss) = Library.split_list tinsts;
    val Ts = map get_typ xis;
        val (_, _, Bi, _) = dest_state(st,i)
        val params = Logic.strip_params Bi
                             (* params of subgoal i as string typ pairs *)
        val params = rev(Term.rename_wrt_term Bi params)
                           (* as they are printed: bound variables with *)
                           (* the same name are renamed during printing *)
        fun types' (a, ~1) = (case AList.lookup (op =) params a of
                NONE => types (a, ~1)
              | some => some)
          | types' xi = types xi;
        fun internal x = is_some (types' (x, ~1));
        val used = Drule.add_used thm (Drule.add_used st []);
        val (ts, envT) =
          ProofContext.read_termTs_schematic ctxt internal types' sorts used (ss ~~ Ts);
        val envT' = map (fn (ixn, T) =>
          (TVar (ixn, the (rsorts ixn)), T)) envT @ Tinsts_env;
        val cenv =
          map
            (fn (xi, t) =>
              pairself (Thm.cterm_of thy) (Var (xi, fastype_of t), t))
            (gen_distinct
              (fn ((x1, t1), (x2, t2)) => x1 = x2 andalso t1 aconv t2)
              (xis ~~ ts));
        (* Lift and instantiate rule *)
        val {maxidx, ...} = rep_thm st;
        val paramTs = map #2 params
        and inc = maxidx+1
        fun liftvar (Var ((a,j), T)) =
              Var((a, j+inc), paramTs ---> Logic.incr_tvar inc T)
          | liftvar t = raise TERM("Variable expected", [t]);
        fun liftterm t = list_abs_free
              (params, Logic.incr_indexes(paramTs,inc) t)
        fun liftpair (cv,ct) =
              (cterm_fun liftvar cv, cterm_fun liftterm ct)
        val lifttvar = pairself (ctyp_of thy o Logic.incr_tvar inc);
        val rule = Drule.instantiate
              (map lifttvar envT', map liftpair cenv)
              (lift_rule (st, i) thm)
      in
        if i > nprems_of st then no_tac st
        else st |>
          compose_tac (bires_flag, rule, nprems_of thm) i
      end
           handle TERM (msg,_)   => (warning msg; no_tac st)
                | THM  (msg,_,_) => (warning msg; no_tac st);
  in
    tac
  end;

local

fun gen_inst _ tac _ (quant, ([], thms)) =
      METHOD (fn facts => quant (insert_tac facts THEN' tac thms))
  | gen_inst inst_tac _ ctxt (quant, (insts, [thm])) =
      METHOD (fn facts =>
        quant (insert_tac facts THEN' inst_tac ctxt insts thm))
  | gen_inst _ _ _ _ = error "Cannot have instantiations with multiple rules";

(* Preserve Var indexes of rl; increment revcut_rl instead.
   Copied from tactic.ML *)
fun make_elim_preserve rl =
  let val {maxidx,...} = rep_thm rl
      fun cvar xi = cterm_of ProtoPure.thy (Var(xi,propT));
      val revcut_rl' =
          instantiate ([],  [(cvar("V",0), cvar("V",maxidx+1)),
                             (cvar("W",0), cvar("W",maxidx+1))]) revcut_rl
      val arg = (false, rl, nprems_of rl)
      val [th] = Seq.list_of (bicompose false arg 1 revcut_rl')
  in  th  end
  handle Bind => raise THM("make_elim_preserve", 1, [rl]);

in

val res_inst_meth = gen_inst (bires_inst_tac false) Tactic.resolve_tac;

val eres_inst_meth = gen_inst (bires_inst_tac true) Tactic.eresolve_tac;

val cut_inst_meth =
  gen_inst
    (fn ctxt => fn insts => bires_inst_tac false ctxt insts o make_elim_preserve)
    Tactic.cut_rules_tac;

val dres_inst_meth =
  gen_inst
    (fn ctxt => fn insts => bires_inst_tac true ctxt insts o make_elim_preserve)
    Tactic.dresolve_tac;

val forw_inst_meth =
  gen_inst
    (fn ctxt => fn insts => fn rule =>
       bires_inst_tac false ctxt insts (make_elim_preserve rule) THEN'
       assume_tac)
    Tactic.forward_tac;

fun subgoal_tac ctxt sprop =
  DETERM o bires_inst_tac false ctxt [(("psi", 0), sprop)] cut_rl;

fun subgoals_tac ctxt sprops = EVERY' (map (subgoal_tac ctxt) sprops);

fun thin_tac ctxt s =
  bires_inst_tac true ctxt [(("V", 0), s)] thin_rl;

end;


(* ML tactics *)

val tactic_ref = ref ((fn _ => raise Match): ProofContext.context -> thm list -> tactic);
fun set_tactic f = tactic_ref := f;

fun tactic txt ctxt = METHOD (fn facts =>
  (Context.use_mltext
    ("let fun tactic (ctxt: ProofContext.context) (facts: thm list) : tactic = \
       \let val thm = ProofContext.get_thm_closure ctxt o PureThy.Name\n\
       \  and thms = ProofContext.get_thms_closure ctxt o PureThy.Name in\n"
       ^ txt ^
       "\nend in Method.set_tactic tactic end")
    false NONE;
    Context.setmp (SOME (ProofContext.theory_of ctxt)) (! tactic_ref ctxt) facts));



(** method syntax **)

(* method text *)

type src = Args.src;

datatype text =
  Basic of (ProofContext.context -> method) |
  Source of src |
  Then of text list |
  Orelse of text list |
  Try of text |
  Repeat1 of text;

val default_text = Source (Args.src (("default", []), Position.none));
val this_text = Basic (K this);
val done_text = Basic (K (SIMPLE_METHOD all_tac));
val sorry_text = Basic o cheating;

fun finish_text (NONE, immed) = Basic (close immed)
  | finish_text (SOME txt, immed) = Then [txt, Basic (close immed)];


(* method definitions *)

structure MethodsData = TheoryDataFun
(struct
  val name = "Isar/methods";
  type T = (((src -> ProofContext.context -> method) * string) * stamp) NameSpace.table;

  val empty = NameSpace.empty_table;
  val copy = I;
  val extend = I;
  fun merge _ tables = NameSpace.merge_tables (eq_snd (op =)) tables handle Symtab.DUPS dups =>
    error ("Attempt to merge different versions of method(s) " ^ commas_quote dups);

  fun print _ meths =
    let
      fun prt_meth (name, ((_, comment), _)) = Pretty.block
        [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    in
      [Pretty.big_list "methods:" (map prt_meth (NameSpace.extern_table meths))]
      |> Pretty.chunks |> Pretty.writeln
    end;
end);

val _ = Context.add_setup [MethodsData.init];
val print_methods = MethodsData.print;


(* get methods *)

exception METHOD_FAIL of (string * Position.T) * exn;

fun method thy =
  let
    val (space, meths) = MethodsData.get thy;
    fun meth src =
      let
        val ((raw_name, _), pos) = Args.dest_src src;
        val name = NameSpace.intern space raw_name;
      in
        (case Symtab.lookup meths name of
          NONE => error ("Unknown proof method: " ^ quote name ^ Position.str_of pos)
        | SOME ((mth, _), _) => transform_failure (curry METHOD_FAIL (name, pos)) (mth src))
      end;
  in meth end;


(* add method *)

fun add_methods raw_meths thy =
  let
    val new_meths = raw_meths |> map (fn (name, f, comment) =>
      (name, ((f, comment), stamp ())));

    fun add meths = NameSpace.extend_table (Sign.naming_of thy) (meths, new_meths)
      handle Symtab.DUPS dups =>
        error ("Duplicate declaration of method(s) " ^ commas_quote dups);
  in MethodsData.map add thy end;

val add_method = add_methods o Library.single;

fun Method name meth cmt = Context.>> (add_methods [(name, meth, cmt)]);


(* method_setup *)

fun method_setup (name, txt, cmt) =
  Context.use_let
    "val thm = PureThy.get_thm_closure (Context.the_context ()) o PureThy.Name;\n\
    \val thms = PureThy.get_thms_closure (Context.the_context ()) o PureThy.Name;\n\
    \val method: bstring * (Method.src -> ProofContext.context -> Proof.method) * string"
    "Method.add_method method"
    ("(" ^ Library.quote name ^ ", " ^ txt ^ ", " ^ Library.quote cmt ^ ")");



(** concrete syntax **)

(* basic *)

fun syntax (scan:
    (ProofContext.context * Args.T list -> 'a * (ProofContext.context * Args.T list))) =
  Args.syntax "method" scan;

fun simple_args scan f src ctxt : method =
  #2 (syntax (Scan.lift (scan >> (fn x => f x ctxt))) src ctxt);

fun ctxt_args (f: ProofContext.context -> method) src ctxt =
  #2 (syntax (Scan.succeed (f ctxt)) src ctxt);

fun no_args m = ctxt_args (K m);


(* sections *)

type modifier = (ProofContext.context -> ProofContext.context) * ProofContext.context attribute;

local

fun sect ss = Scan.first (map Scan.lift ss);
fun thms ss = Scan.unless (sect ss) Attrib.local_thms;
fun thmss ss = Scan.repeat (thms ss) >> List.concat;

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


(* iprover syntax *)

local

val introN = "intro";
val elimN = "elim";
val destN = "dest";
val ruleN = "rule";

fun modifier name kind kind' att =
  Args.$$$ name |-- (kind >> K NONE || kind' |-- Args.nat --| Args.colon >> SOME)
    >> (pair (I: ProofContext.context -> ProofContext.context) o att);

val iprover_modifiers =
 [modifier destN Args.bang_colon Args.bang ContextRules.dest_bang_local,
  modifier destN Args.colon (Scan.succeed ()) ContextRules.dest_local,
  modifier elimN Args.bang_colon Args.bang ContextRules.elim_bang_local,
  modifier elimN Args.colon (Scan.succeed ()) ContextRules.elim_local,
  modifier introN Args.bang_colon Args.bang ContextRules.intro_bang_local,
  modifier introN Args.colon (Scan.succeed ()) ContextRules.intro_local,
  Args.del -- Args.colon >> K (I, ContextRules.rule_del_local)];

in

fun iprover_args m = bang_sectioned_args' iprover_modifiers (Scan.lift (Scan.option Args.nat)) m;

fun iprover_meth n prems ctxt = METHOD (fn facts =>
  HEADGOAL (insert_tac (prems @ facts) THEN' ObjectLogic.atomize_tac THEN' iprover_tac ctxt n));

end;


(* tactic syntax *)

fun nat_thms_args f = uncurry f oo
  (#2 oo syntax (Scan.lift (Scan.optional (Args.parens Args.nat) 0) -- Attrib.local_thmss));

val insts =
  Scan.optional
    (Args.enum1 "and" (Scan.lift (Args.name -- (Args.$$$ "=" |-- Args.!!! Args.name))) --|
      Scan.lift (Args.$$$ "in")) [] -- Attrib.local_thmss;

fun inst_args f src ctxt = f ctxt (#2 (syntax (Args.goal_spec HEADGOAL -- insts) src ctxt));

val insts_var =
  Scan.optional
    (Args.enum1 "and" (Scan.lift (Args.var -- (Args.$$$ "=" |-- Args.!!! Args.name))) --|
      Scan.lift (Args.$$$ "in")) [] -- Attrib.local_thmss;

fun inst_args_var f src ctxt =
  f ctxt (#2 (syntax (Args.goal_spec HEADGOAL -- insts_var) src ctxt));

fun goal_args' args tac src ctxt = #2 (syntax (Args.goal_spec HEADGOAL -- args >>
  (fn (quant, s) => SIMPLE_METHOD' quant (tac s))) src ctxt);

fun goal_args args tac = goal_args' (Scan.lift args) tac;

fun goal_args_ctxt' args tac src ctxt =
  #2 (syntax (Args.goal_spec HEADGOAL -- args >>
  (fn (quant, s) => SIMPLE_METHOD' quant (tac ctxt s))) src ctxt);

fun goal_args_ctxt args tac = goal_args_ctxt' (Scan.lift args) tac;


(* misc tactic emulations *)

val subgoal_meth = goal_args_ctxt (Scan.repeat1 Args.name) subgoals_tac;
val thin_meth = goal_args_ctxt Args.name thin_tac;
val rename_meth = goal_args (Scan.repeat1 Args.name) Tactic.rename_params_tac;
val rotate_meth = goal_args (Scan.optional Args.int 1) Tactic.rotate_tac;


(* pure_methods *)

val pure_methods =
 [("fail", no_args fail, "force failure"),
  ("succeed", no_args succeed, "succeed"),
  ("-", no_args insert_facts, "do nothing (insert current facts only)"),
  ("insert", thms_args insert, "insert theorems, ignoring facts (improper)"),
  ("unfold", thms_args unfold_meth, "unfold definitions"),
  ("intro", thms_args intro, "repeatedly apply introduction rules"),
  ("elim", thms_args elim, "repeatedly apply elimination rules"),
  ("fold", thms_args fold_meth, "fold definitions"),
  ("atomize", (atomize o #2) oo syntax (Args.mode "full"),
    "present local premises as object-level statements"),
  ("iprover", iprover_args iprover_meth, "intuitionistic proof search"),
  ("rule", thms_ctxt_args some_rule, "apply some intro/elim rule"),
  ("erule", nat_thms_args erule, "apply rule in elimination manner (improper)"),
  ("drule", nat_thms_args drule, "apply rule in destruct manner (improper)"),
  ("frule", nat_thms_args frule, "apply rule in forward manner (improper)"),
  ("this", no_args this, "apply current facts as rules"),
  ("assumption", ctxt_args assumption, "proof by assumption, preferring facts"),
  ("rule_tac", inst_args_var res_inst_meth, "apply rule (dynamic instantiation)"),
  ("erule_tac", inst_args_var eres_inst_meth, "apply rule in elimination manner (dynamic instantiation)"),
  ("drule_tac", inst_args_var dres_inst_meth, "apply rule in destruct manner (dynamic instantiation)"),
  ("frule_tac", inst_args_var forw_inst_meth, "apply rule in forward manner (dynamic instantiation)"),
  ("cut_tac", inst_args_var cut_inst_meth, "cut rule (dynamic instantiation)"),
  ("subgoal_tac", subgoal_meth, "insert subgoal (dynamic instantiation)"),
  ("thin_tac", thin_meth, "remove premise (dynamic instantiation)"),
  ("rename_tac", rename_meth, "rename parameters of goal (dynamic instantiation)"),
  ("rotate_tac", rotate_meth, "rotate assumptions of goal"),
  ("tactic", simple_args Args.name tactic, "ML tactic as proof method")];

val _ = Context.add_setup [add_methods pure_methods];


(*final declarations of this structure!*)
val unfold = unfold_meth;
val fold = fold_meth;

end;

structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
