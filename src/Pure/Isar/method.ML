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
  val trace: Proof.context -> thm list -> unit
  val RAW_METHOD: (thm list -> tactic) -> Proof.method
  val RAW_METHOD_CASES:
    (thm list -> thm -> (thm * (string * RuleCases.T) list) Seq.seq) -> Proof.method
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
  val rules_tac: Proof.context -> int option -> int -> tactic
  val rule_tac: thm list -> thm list -> int -> tactic
  val some_rule_tac: thm list -> Proof.context -> thm list -> int -> tactic
  val rule: thm list -> Proof.method
  val erule: int -> thm list -> Proof.method
  val drule: int -> thm list -> Proof.method
  val frule: int -> thm list -> Proof.method
  val this: Proof.method
  val assumption: Proof.context -> Proof.method
  val bires_inst_tac: bool -> Proof.context -> (indexname * string) list -> thm -> int -> tactic
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
    -> (Proof.context -> string * (string * thm list) list -> unit) *
      (Proof.context -> thm -> unit) -> Proof.state -> Proof.state Seq.seq
  val local_terminal_proof: text * text option
    -> (Proof.context -> string * (string * thm list) list -> unit) *
      (Proof.context -> thm -> unit) -> Proof.state -> Proof.state Seq.seq
  val local_default_proof: (Proof.context -> string * (string * thm list) list -> unit) *
    (Proof.context -> thm -> unit) -> Proof.state -> Proof.state Seq.seq
  val local_immediate_proof: (Proof.context -> string * (string * thm list) list -> unit) *
    (Proof.context -> thm -> unit) -> Proof.state -> Proof.state Seq.seq
  val local_done_proof: (Proof.context -> string * (string * thm list) list -> unit) *
    (Proof.context -> thm -> unit) -> Proof.state -> Proof.state Seq.seq
  val global_qed: bool -> text option
    -> Proof.state -> theory * ((string * string) * (string * thm list) list)
  val global_terminal_proof: text * text option
    -> Proof.state -> theory * ((string * string) * (string * thm list) list)
  val global_default_proof: Proof.state -> theory * ((string * string) * (string * thm list) list)
  val global_immediate_proof: Proof.state ->
    theory * ((string * string) * (string * thm list) list)
  val global_done_proof: Proof.state -> theory * ((string * string) * (string * thm list) list)
  val goal_args: (Args.T list -> 'a * Args.T list) -> ('a -> int -> tactic)
    -> Args.src -> Proof.context -> Proof.method
  val goal_args': (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list))
    -> ('a -> int -> tactic) -> Args.src -> Proof.context -> Proof.method
  val goal_args_ctxt: (Args.T list -> 'a * Args.T list) -> (Proof.context -> 'a -> int -> tactic)
    -> Args.src -> Proof.context -> Proof.method
  val goal_args_ctxt': (Proof.context * Args.T list -> 'a * (Proof.context * Args.T list))
    -> (Proof.context -> 'a -> int -> tactic) -> Args.src -> Proof.context -> Proof.method
  val setup: (theory -> theory) list
end;

structure Method: METHOD =
struct


(** proof methods **)

(* tracing *)

val trace_rules = ref false;

fun trace ctxt rules =
  conditional (! trace_rules andalso not (null rules)) (fn () =>
    Pretty.big_list "rules:" (map (ProofContext.pretty_thm ctxt) rules)
    |> Pretty.string_of |> tracing);


(* make methods *)

val RAW_METHOD = Proof.method;
val RAW_METHOD_CASES = Proof.method_cases;

fun METHOD m = Proof.method (fn facts => TRY Tactic.conjunction_tac THEN m facts);
fun METHOD_CASES m =
  Proof.method_cases (fn facts => Seq.THEN (TRY Tactic.conjunction_tac, m facts));


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

fun SIMPLE_METHOD tac = METHOD (fn facts => ALLGOALS (insert_tac facts) THEN tac);
fun SIMPLE_METHOD' quant tac = METHOD (fn facts => quant (insert_tac facts THEN' tac));

end;


(* unfold/fold definitions *)

fun unfold ths = SIMPLE_METHOD (CHANGED_PROP (rewrite_goals_tac ths));
fun fold ths = SIMPLE_METHOD (CHANGED_PROP (fold_goals_tac ths));


(* atomize rule statements *)

fun atomize false = SIMPLE_METHOD' HEADGOAL (CHANGED_PROP o ObjectLogic.atomize_tac)
  | atomize true = RAW_METHOD (K (HEADGOAL (CHANGED_PROP o ObjectLogic.full_atomize_tac)));


(* unfold intro/elim rules *)

fun intro ths = SIMPLE_METHOD' HEADGOAL (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.match_tac ths));
fun elim ths = SIMPLE_METHOD' HEADGOAL (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.ematch_tac ths));


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


(* rules_tac *)

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

fun intpr_tac ctxt gs d lim = SUBGOAL (fn (g, i) => if d > lim then no_tac else
  let
    val ps = Logic.strip_assums_hyp g;
    val c = Logic.strip_assums_concl g;
  in
    if gen_mem (fn ((ps1, c1), (ps2, c2)) =>
      c1 aconv c2 andalso gen_eq_set op aconv ps1 ps2) ((ps, c), gs) then no_tac
    else (step_tac ctxt THEN_ALL_NEW intpr_tac ctxt ((ps, c) :: gs) (d + 1) lim) i
  end);

in

fun rules_tac ctxt opt_lim =
  SELECT_GOAL (DEEPEN (2, if_none opt_lim 20) (intpr_tac ctxt [] 0) 4 1);

end;


(* rule_tac etc. *)

local

fun gen_rule_tac tac rules [] i st = tac rules i st
  | gen_rule_tac tac rules facts i st =
      Seq.flat (Seq.map (fn rule => (tac o single) rule i st) (multi_resolves facts rules));

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

(* Reimplemented to support both static (Isar) and dynamic (proof state)
   context.  By Clemens Ballarin. *)

fun bires_inst_tac bires_flag ctxt insts thm =
  let
    val sign = ProofContext.sign_of ctxt;
    (* Separate type and term insts *)
    fun has_type_var ((x, _), _) = (case Symbol.explode x of
          "'"::cs => true | cs => false);
    val Tinsts = filter has_type_var insts;
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
        let val S = case rsorts xi of Some S => S | None => absent xi;
            val T = Sign.read_typ (sign, sorts) s;
        in if Sign.typ_instance sign (T, TVar (xi, S)) then (xi, T)
           else error
             ("Instantiation of " ^ Syntax.string_of_vname xi ^ " fails")
        end;
    val Tinsts_env = map readT Tinsts;
    (* Preprocess rule: extract vars and their types, apply Tinsts *)
    fun get_typ xi =
      (case rtypes xi of
           Some T => typ_subst_TVars Tinsts_env T
         | None => absent xi);
    val (xis, ss) = Library.split_list tinsts;
    val Ts = map get_typ xis;
	val (_, _, Bi, _) = dest_state(st,i)
	val params = Logic.strip_params Bi
			     (* params of subgoal i as string typ pairs *)
	val params = rev(Term.rename_wrt_term Bi params)
			   (* as they are printed: bound variables with *)
                           (* the same name are renamed during printing *)
        fun types' (a, ~1) = (case assoc (params, a) of
                None => types (a, ~1)
              | some => some)
          | types' xi = types xi;
        val used = add_term_tvarnames
                  (prop_of st $ prop_of thm,[])
	val (ts, envT) =
	  ProofContext.read_termTs_env (types', sorts, used) ctxt (ss ~~ Ts);
	val cenvT = map (apsnd (Thm.ctyp_of sign)) (envT @ Tinsts_env);
	val cenv =
	  map
	    (fn (xi, t) =>
	      pairself (Thm.cterm_of sign) (Var (xi, fastype_of t), t))
	    (gen_distinct
	      (fn ((x1, t1), (x2, t2)) => x1 = x2 andalso t1 aconv t2)
	      (xis ~~ ts));
	(* Lift and instantiate rule *)
	val {maxidx, ...} = rep_thm st;
	val paramTs = map #2 params
	and inc = maxidx+1
	fun liftvar (Var ((a,j), T)) =
	      Var((a, j+inc), paramTs ---> incr_tvar inc T)
	  | liftvar t = raise TERM("Variable expected", [t]);
	fun liftterm t = list_abs_free
	      (params, Logic.incr_indexes(paramTs,inc) t)
	fun liftpair (cv,ct) =
	      (cterm_fun liftvar cv, cterm_fun liftterm ct)
	fun lifttvar((a,i),ctyp) =
	    let val {T,sign} = rep_ctyp ctyp
	    in  ((a,i+inc), ctyp_of sign (incr_tvar inc T)) end
	val rule = Drule.instantiate
	      (map lifttvar cenvT, map liftpair cenv)
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

fun gen_inst _ tac _ (quant, ([], thms)) =
      METHOD (fn facts => quant (insert_tac facts THEN' tac thms))
  | gen_inst inst_tac _ ctxt (quant, (insts, [thm])) =
      METHOD (fn facts =>
        quant (insert_tac facts THEN' inst_tac ctxt insts thm))
  | gen_inst _ _ _ _ = error "Cannot have instantiations with multiple rules";
      
val res_inst_meth = gen_inst (bires_inst_tac false) Tactic.resolve_tac;

val eres_inst_meth = gen_inst (bires_inst_tac true) Tactic.eresolve_tac;

(* Preserve Var indexes of rl; increment revcut_rl instead.
   Copied from tactic.ML *)
fun make_elim_preserve rl =
  let val {maxidx,...} = rep_thm rl
      fun cvar xi = cterm_of (Theory.sign_of ProtoPure.thy) (Var(xi,propT));
      val revcut_rl' =
          instantiate ([],  [(cvar("V",0), cvar("V",maxidx+1)),
                             (cvar("W",0), cvar("W",maxidx+1))]) revcut_rl
      val arg = (false, rl, nprems_of rl)
      val [th] = Seq.list_of (bicompose false arg 1 revcut_rl')
  in  th  end
  handle Bind => raise THM("make_elim_preserve", 1, [rl]);

val cut_inst_meth =
  gen_inst
    (fn ctxt => fn insts => fn thm =>
       bires_inst_tac false ctxt insts (make_elim_preserve thm))
    Tactic.cut_rules_tac;

val dres_inst_meth =
  gen_inst
    (fn ctxt => fn insts => fn rule =>
       bires_inst_tac true ctxt insts (make_elim_preserve rule))
    Tactic.dresolve_tac;

val forw_inst_meth =
  gen_inst
    (fn ctxt => fn insts => fn rule =>
       bires_inst_tac false ctxt insts (make_elim_preserve rule) THEN'
       assume_tac)
    Tactic.forward_tac;

fun subgoal_tac ctxt sprop =
  DETERM o bires_inst_tac false ctxt [(("psi", 0), sprop)] cut_rl THEN'
  SUBGOAL (fn (prop, _) =>
    let val concl' = Logic.strip_assums_concl prop in
      if null (term_tvars concl') then ()
      else warning "Type variables in new subgoal: add a type constraint?";
      all_tac
  end);

fun subgoals_tac ctxt sprops = EVERY' (map (subgoal_tac ctxt) sprops);

fun thin_tac ctxt s =
  bires_inst_tac true ctxt [(("V", 0), s)] thin_rl;

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


(* rules syntax *)

local

val introN = "intro";
val elimN = "elim";
val destN = "dest";
val ruleN = "rule";

fun modifier name kind kind' att =
  Args.$$$ name |-- (kind >> K None || kind' |-- Args.nat --| Args.colon >> Some)
    >> (pair (I: Proof.context -> Proof.context) o att);

val rules_modifiers =
 [modifier destN Args.bang_colon Args.bang ContextRules.dest_bang_local,
  modifier destN Args.colon (Scan.succeed ()) ContextRules.dest_local,
  modifier elimN Args.bang_colon Args.bang ContextRules.elim_bang_local,
  modifier elimN Args.colon (Scan.succeed ()) ContextRules.elim_local,
  modifier introN Args.bang_colon Args.bang ContextRules.intro_bang_local,
  modifier introN Args.colon (Scan.succeed ()) ContextRules.intro_local,
  Args.del -- Args.colon >> K (I, ContextRules.rule_del_local)];

in

fun rules_args m = bang_sectioned_args' rules_modifiers (Scan.lift (Scan.option Args.nat)) m;

fun rules_meth n prems ctxt = METHOD (fn facts =>
  HEADGOAL (insert_tac (prems @ facts) THEN' ObjectLogic.atomize_tac THEN' rules_tac ctxt n));

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

fun inst_args_var f src ctxt = f ctxt (#2 (syntax (Args.goal_spec HEADGOAL -- insts_var) src ctxt));

fun goal_args' args tac src ctxt = #2 (syntax (Args.goal_spec HEADGOAL -- args >>
  (fn (quant, s) => SIMPLE_METHOD' quant (tac s))) src ctxt);

fun goal_args args tac = goal_args' (Scan.lift args) tac;

fun goal_args_ctxt' args tac src ctxt =
  #2 (syntax (Args.goal_spec HEADGOAL -- args >>
  (fn (quant, s) => SIMPLE_METHOD' quant (tac ctxt s))) src ctxt);

fun goal_args_ctxt args tac = goal_args_ctxt' (Scan.lift args) tac;

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
  ("unfold", thms_args unfold, "unfold definitions"),
  ("intro", thms_args intro, "repeatedly apply introduction rules"),
  ("elim", thms_args elim, "repeatedly apply elimination rules"),
  ("fold", thms_args fold, "fold definitions"),
  ("atomize", (atomize o #2) oo syntax (Args.mode "full"),
    "present local premises as object-level statements"),
  ("rules", rules_args rules_meth, "apply many rules, including proof search"),
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
  ("prolog", thms_args prolog, "simple prolog interpreter"),
  ("tactic", simple_args Args.name tactic, "ML tactic as proof method")];


(* setup *)

val setup =
 [MethodsData.init, add_methods pure_methods,
  (#1 o PureThy.add_thms [(("", Drule.equal_intr_rule), [ContextRules.intro_query_global None])])];


end;


structure BasicMethod: BASIC_METHOD = Method;
open BasicMethod;
