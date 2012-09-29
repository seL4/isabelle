(*  Title:      Pure/raw_simplifier.ML
    Author:     Tobias Nipkow and Stefan Berghofer, TU Muenchen

Higher-order Simplification.
*)

infix 4
  addsimps delsimps addsimprocs delsimprocs
  setloop' setloop addloop addloop' delloop
  setSSolver addSSolver setSolver addSolver;

signature BASIC_RAW_SIMPLIFIER =
sig
  val simp_depth_limit: int Config.T
  val simp_trace_depth_limit: int Config.T
  val simp_debug: bool Config.T
  val simp_trace: bool Config.T
  type rrule
  val eq_rrule: rrule * rrule -> bool
  type simpset
  type proc
  type solver
  val mk_solver: string -> (simpset -> int -> tactic) -> solver
  val empty_ss: simpset
  val merge_ss: simpset * simpset -> simpset
  val dest_ss: simpset ->
   {simps: (string * thm) list,
    procs: (string * cterm list) list,
    congs: (string * thm) list,
    weak_congs: string list,
    loopers: string list,
    unsafe_solvers: string list,
    safe_solvers: string list}
  type simproc
  val eq_simproc: simproc * simproc -> bool
  val transform_simproc: morphism -> simproc -> simproc
  val make_simproc: {name: string, lhss: cterm list,
    proc: morphism -> simpset -> cterm -> thm option, identifier: thm list} -> simproc
  val mk_simproc: string -> cterm list -> (theory -> simpset -> term -> thm option) -> simproc
  val addsimps: simpset * thm list -> simpset
  val delsimps: simpset * thm list -> simpset
  val addsimprocs: simpset * simproc list -> simpset
  val delsimprocs: simpset * simproc list -> simpset
  val setloop': simpset * (simpset -> int -> tactic) -> simpset
  val setloop: simpset * (int -> tactic) -> simpset
  val addloop': simpset * (string * (simpset -> int -> tactic)) -> simpset
  val addloop: simpset * (string * (int -> tactic)) -> simpset
  val delloop: simpset * string -> simpset
  val setSSolver: simpset * solver -> simpset
  val addSSolver: simpset * solver -> simpset
  val setSolver: simpset * solver -> simpset
  val addSolver: simpset * solver -> simpset

  val rewrite_rule: thm list -> thm -> thm
  val rewrite_goals_rule: thm list -> thm -> thm
  val rewrite_goals_tac: thm list -> tactic
  val rewrite_goal_tac: thm list -> int -> tactic
  val prune_params_tac: tactic
  val fold_rule: thm list -> thm -> thm
  val fold_goals_tac: thm list -> tactic
  val norm_hhf: thm -> thm
  val norm_hhf_protect: thm -> thm
end;

signature RAW_SIMPLIFIER =
sig
  include BASIC_RAW_SIMPLIFIER
  exception SIMPLIFIER of string * thm
  val internal_ss: simpset ->
   {rules: rrule Net.net,
    prems: thm list,
    bounds: int * ((string * typ) * string) list,
    depth: int * bool Unsynchronized.ref,
    context: Proof.context option} *
   {congs: (string * thm) list * string list,
    procs: proc Net.net,
    mk_rews:
     {mk: simpset -> thm -> thm list,
      mk_cong: simpset -> thm -> thm,
      mk_sym: simpset -> thm -> thm option,
      mk_eq_True: simpset -> thm -> thm option,
      reorient: theory -> term list -> term -> term -> bool},
    termless: term * term -> bool,
    subgoal_tac: simpset -> int -> tactic,
    loop_tacs: (string * (simpset -> int -> tactic)) list,
    solvers: solver list * solver list}
  val prems_of: simpset -> thm list
  val add_simp: thm -> simpset -> simpset
  val del_simp: thm -> simpset -> simpset
  val add_eqcong: thm -> simpset -> simpset
  val del_eqcong: thm -> simpset -> simpset
  val add_cong: thm -> simpset -> simpset
  val del_cong: thm -> simpset -> simpset
  val mksimps: simpset -> thm -> thm list
  val set_mksimps: (simpset -> thm -> thm list) -> simpset -> simpset
  val set_mkcong: (simpset -> thm -> thm) -> simpset -> simpset
  val set_mksym: (simpset -> thm -> thm option) -> simpset -> simpset
  val set_mkeqTrue: (simpset -> thm -> thm option) -> simpset -> simpset
  val set_termless: (term * term -> bool) -> simpset -> simpset
  val set_subgoaler: (simpset -> int -> tactic) -> simpset -> simpset
  val solver: simpset -> solver -> int -> tactic
  val simp_depth_limit_raw: Config.raw
  val clear_ss: simpset -> simpset
  val default_mk_sym: simpset -> thm -> thm option
  val simproc_global_i: theory -> string -> term list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val simproc_global: theory -> string -> string list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val simp_trace_depth_limit_raw: Config.raw
  val simp_trace_depth_limit_default: int Unsynchronized.ref
  val simp_trace_default: bool Unsynchronized.ref
  val simp_trace_raw: Config.raw
  val simp_debug_raw: Config.raw
  val add_prems: thm list -> simpset -> simpset
  val inherit_context: simpset -> simpset -> simpset
  val the_context: simpset -> Proof.context
  val context: Proof.context -> simpset -> simpset
  val global_context: theory -> simpset -> simpset
  val with_context: Proof.context -> (simpset -> simpset) -> simpset -> simpset
  val debug_bounds: bool Unsynchronized.ref
  val set_reorient: (theory -> term list -> term -> term -> bool) -> simpset -> simpset
  val set_solvers: solver list -> simpset -> simpset
  val rewrite_cterm: bool * bool * bool -> (simpset -> thm -> thm option) -> simpset -> conv
  val rewrite_term: theory -> thm list -> (term -> term option) list -> term -> term
  val rewrite_thm: bool * bool * bool ->
    (simpset -> thm -> thm option) -> simpset -> thm -> thm
  val generic_rewrite_goal_tac: bool * bool * bool ->
    (simpset -> tactic) -> simpset -> int -> tactic
  val rewrite: bool -> thm list -> conv
  val simplify: bool -> thm list -> thm -> thm
end;

structure Raw_Simplifier: RAW_SIMPLIFIER =
struct

(** datatype simpset **)

(* rewrite rules *)

type rrule =
 {thm: thm,         (*the rewrite rule*)
  name: string,     (*name of theorem from which rewrite rule was extracted*)
  lhs: term,        (*the left-hand side*)
  elhs: cterm,      (*the etac-contracted lhs*)
  extra: bool,      (*extra variables outside of elhs*)
  fo: bool,         (*use first-order matching*)
  perm: bool};      (*the rewrite rule is permutative*)

(*
Remarks:
  - elhs is used for matching,
    lhs only for preservation of bound variable names;
  - fo is set iff
    either elhs is first-order (no Var is applied),
      in which case fo-matching is complete,
    or elhs is not a pattern,
      in which case there is nothing better to do;
*)

fun eq_rrule ({thm = thm1, ...}: rrule, {thm = thm2, ...}: rrule) =
  Thm.eq_thm_prop (thm1, thm2);


(* simplification sets, procedures, and solvers *)

(*A simpset contains data required during conversion:
    rules: discrimination net of rewrite rules;
    prems: current premises;
    bounds: maximal index of bound variables already used
      (for generating new names when rewriting under lambda abstractions);
    depth: simp_depth and exceeded flag;
    congs: association list of congruence rules and
           a list of `weak' congruence constants.
           A congruence is `weak' if it avoids normalization of some argument.
    procs: discrimination net of simplification procedures
      (functions that prove rewrite rules on the fly);
    mk_rews:
      mk: turn simplification thms into rewrite rules;
      mk_cong: prepare congruence rules;
      mk_sym: turn == around;
      mk_eq_True: turn P into P == True;
    termless: relation for ordered rewriting;*)

datatype simpset =
  Simpset of
   {rules: rrule Net.net,
    prems: thm list,
    bounds: int * ((string * typ) * string) list,
    depth: int * bool Unsynchronized.ref,
    context: Proof.context option} *
   {congs: (string * thm) list * string list,
    procs: proc Net.net,
    mk_rews:
     {mk: simpset -> thm -> thm list,
      mk_cong: simpset -> thm -> thm,
      mk_sym: simpset -> thm -> thm option,
      mk_eq_True: simpset -> thm -> thm option,
      reorient: theory -> term list -> term -> term -> bool},
    termless: term * term -> bool,
    subgoal_tac: simpset -> int -> tactic,
    loop_tacs: (string * (simpset -> int -> tactic)) list,
    solvers: solver list * solver list}
and proc =
  Proc of
   {name: string,
    lhs: cterm,
    proc: simpset -> cterm -> thm option,
    id: stamp * thm list}
and solver =
  Solver of
   {name: string,
    solver: simpset -> int -> tactic,
    id: stamp};


fun internal_ss (Simpset args) = args;

fun make_ss1 (rules, prems, bounds, depth, context) =
  {rules = rules, prems = prems, bounds = bounds, depth = depth, context = context};

fun map_ss1 f {rules, prems, bounds, depth, context} =
  make_ss1 (f (rules, prems, bounds, depth, context));

fun make_ss2 (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =
  {congs = congs, procs = procs, mk_rews = mk_rews, termless = termless,
    subgoal_tac = subgoal_tac, loop_tacs = loop_tacs, solvers = solvers};

fun map_ss2 f {congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers} =
  make_ss2 (f (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers));

fun make_simpset (args1, args2) = Simpset (make_ss1 args1, make_ss2 args2);

fun map_simpset1 f (Simpset (r1, r2)) = Simpset (map_ss1 f r1, r2);
fun map_simpset2 f (Simpset (r1, r2)) = Simpset (r1, map_ss2 f r2);

fun prems_of (Simpset ({prems, ...}, _)) = prems;

fun eq_procid ((s1: stamp, ths1: thm list), (s2, ths2)) =
  s1 = s2 andalso eq_list Thm.eq_thm (ths1, ths2);
fun eq_proc (Proc {id = id1, ...}, Proc {id = id2, ...}) = eq_procid (id1, id2);

fun mk_solver name solver = Solver {name = name, solver = solver, id = stamp ()};

fun solver_name (Solver {name, ...}) = name;
fun solver ss (Solver {solver = tac, ...}) = tac ss;
fun eq_solver (Solver {id = id1, ...}, Solver {id = id2, ...}) = (id1 = id2);


(* simp depth *)

val simp_depth_limit_raw = Config.declare "simp_depth_limit" (K (Config.Int 100));
val simp_depth_limit = Config.int simp_depth_limit_raw;

val simp_trace_depth_limit_default = Unsynchronized.ref 1;
val simp_trace_depth_limit_raw = Config.declare "simp_trace_depth_limit"
  (fn _ => Config.Int (! simp_trace_depth_limit_default));
val simp_trace_depth_limit = Config.int simp_trace_depth_limit_raw;

fun simp_trace_depth_limit_of NONE = ! simp_trace_depth_limit_default
  | simp_trace_depth_limit_of (SOME ctxt) = Config.get ctxt simp_trace_depth_limit;

fun trace_depth (Simpset ({depth = (depth, exceeded), context, ...}, _)) msg =
  if depth > simp_trace_depth_limit_of context then
    if ! exceeded then () else (tracing "simp_trace_depth_limit exceeded!"; exceeded := true)
  else
    (tracing (enclose "[" "]" (string_of_int depth) ^ msg); exceeded := false);

val inc_simp_depth = map_simpset1 (fn (rules, prems, bounds, (depth, exceeded), context) =>
  (rules, prems, bounds,
    (depth + 1,
      if depth = simp_trace_depth_limit_of context then Unsynchronized.ref false else exceeded), context));

fun simp_depth (Simpset ({depth = (depth, _), ...}, _)) = depth;


(* diagnostics *)

exception SIMPLIFIER of string * thm;

val simp_debug_raw = Config.declare "simp_debug" (K (Config.Bool false));
val simp_debug = Config.bool simp_debug_raw;

val simp_trace_default = Unsynchronized.ref false;
val simp_trace_raw = Config.declare "simp_trace" (fn _ => Config.Bool (! simp_trace_default));
val simp_trace = Config.bool simp_trace_raw;

fun if_enabled (Simpset ({context, ...}, _)) flag f =
  (case context of
    SOME ctxt => if Config.get ctxt flag then f ctxt else ()
  | NONE => ())

fun if_visible (Simpset ({context, ...}, _)) f x =
  (case context of
    SOME ctxt => Context_Position.if_visible ctxt f x
  | NONE => ());

local

fun prnt ss warn a = if warn then warning a else trace_depth ss a;

fun show_bounds (Simpset ({bounds = (_, bs), ...}, _)) t =
  let
    val names = Term.declare_term_names t Name.context;
    val xs = rev (#1 (fold_map Name.variant (rev (map #2 bs)) names));
    fun subst (((b, T), _), x') = (Free (b, T), Syntax_Trans.mark_bound_abs (x', T));
  in Term.subst_atomic (ListPair.map subst (bs, xs)) t end;

fun print_term ss warn a t ctxt = prnt ss warn (a () ^ "\n" ^
  Syntax.string_of_term ctxt
    (if Config.get ctxt simp_debug then t else show_bounds ss t));

in

fun print_term_global ss warn a thy t =
  print_term ss warn (K a) t (Proof_Context.init_global thy);

fun debug warn a ss = if_enabled ss simp_debug (fn _ => prnt ss warn (a ()));
fun trace warn a ss = if_enabled ss simp_trace (fn _ => prnt ss warn (a ()));

fun debug_term warn a ss t = if_enabled ss simp_debug (print_term ss warn a t);
fun trace_term warn a ss t = if_enabled ss simp_trace (print_term ss warn a t);

fun trace_cterm warn a ss ct =
  if_enabled ss simp_trace (print_term ss warn a (Thm.term_of ct));

fun trace_thm a ss th =
  if_enabled ss simp_trace (print_term ss false a (Thm.full_prop_of th));

fun trace_named_thm a ss (th, name) =
  if_enabled ss simp_trace (print_term ss false
    (fn () => if name = "" then a () else a () ^ " " ^ quote name ^ ":")
    (Thm.full_prop_of th));

fun warn_thm a ss th =
  print_term_global ss true a (Thm.theory_of_thm th) (Thm.full_prop_of th);

fun cond_warn_thm a ss th = if_visible ss (fn () => warn_thm a ss th) ();

end;



(** simpset operations **)

(* context *)

fun eq_bound (x: string, (y, _)) = x = y;

fun add_bound bound = map_simpset1 (fn (rules, prems, (count, bounds), depth, context) =>
  (rules, prems, (count + 1, bound :: bounds), depth, context));

fun add_prems ths = map_simpset1 (fn (rules, prems, bounds, depth, context) =>
  (rules, ths @ prems, bounds, depth, context));

fun inherit_context (Simpset ({bounds, depth, context, ...}, _)) =
  map_simpset1 (fn (rules, prems, _, _, _) => (rules, prems, bounds, depth, context));

fun the_context (Simpset ({context = SOME ctxt, ...}, _)) = ctxt
  | the_context _ = raise Fail "Simplifier: no proof context in simpset";

fun context ctxt =
  map_simpset1 (fn (rules, prems, bounds, depth, _) => (rules, prems, bounds, depth, SOME ctxt));

val global_context = context o Proof_Context.init_global;

fun activate_context thy ss =
  let
    val ctxt = the_context ss;
    val ctxt' = ctxt
      |> Context.raw_transfer (Theory.merge (thy, Proof_Context.theory_of ctxt))
      |> Context_Position.set_visible false;
  in context ctxt' ss end;

fun with_context ctxt f ss = inherit_context ss (f (context ctxt ss));


(* maintain simp rules *)

(* FIXME: it seems that the conditions on extra variables are too liberal if
prems are nonempty: does solving the prems really guarantee instantiation of
all its Vars? Better: a dynamic check each time a rule is applied.
*)
fun rewrite_rule_extra_vars prems elhs erhs =
  let
    val elhss = elhs :: prems;
    val tvars = fold Term.add_tvars elhss [];
    val vars = fold Term.add_vars elhss [];
  in
    erhs |> Term.exists_type (Term.exists_subtype
      (fn TVar v => not (member (op =) tvars v) | _ => false)) orelse
    erhs |> Term.exists_subterm
      (fn Var v => not (member (op =) vars v) | _ => false)
  end;

fun rrule_extra_vars elhs thm =
  rewrite_rule_extra_vars [] (term_of elhs) (Thm.full_prop_of thm);

fun mk_rrule2 {thm, name, lhs, elhs, perm} =
  let
    val t = term_of elhs;
    val fo = Pattern.first_order t orelse not (Pattern.pattern t);
    val extra = rrule_extra_vars elhs thm;
  in {thm = thm, name = name, lhs = lhs, elhs = elhs, extra = extra, fo = fo, perm = perm} end;

fun del_rrule (rrule as {thm, elhs, ...}) ss =
  ss |> map_simpset1 (fn (rules, prems, bounds, depth, context) =>
    (Net.delete_term eq_rrule (term_of elhs, rrule) rules, prems, bounds, depth, context))
  handle Net.DELETE => (cond_warn_thm "Rewrite rule not in simpset:" ss thm; ss);

fun insert_rrule (rrule as {thm, name, ...}) ss =
 (trace_named_thm (fn () => "Adding rewrite rule") ss (thm, name);
  ss |> map_simpset1 (fn (rules, prems, bounds, depth, context) =>
    let
      val rrule2 as {elhs, ...} = mk_rrule2 rrule;
      val rules' = Net.insert_term eq_rrule (term_of elhs, rrule2) rules;
    in (rules', prems, bounds, depth, context) end)
  handle Net.INSERT => (cond_warn_thm "Ignoring duplicate rewrite rule:" ss thm; ss));

fun vperm (Var _, Var _) = true
  | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
  | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
  | vperm (t, u) = (t = u);

fun var_perm (t, u) =
  vperm (t, u) andalso eq_set (op =) (Term.add_vars t [], Term.add_vars u []);

(*simple test for looping rewrite rules and stupid orientations*)
fun default_reorient thy prems lhs rhs =
  rewrite_rule_extra_vars prems lhs rhs
    orelse
  is_Var (head_of lhs)
    orelse
(* turns t = x around, which causes a headache if x is a local variable -
   usually it is very useful :-(
  is_Free rhs andalso not(is_Free lhs) andalso not(Logic.occs(rhs,lhs))
  andalso not(exists_subterm is_Var lhs)
    orelse
*)
  exists (fn t => Logic.occs (lhs, t)) (rhs :: prems)
    orelse
  null prems andalso Pattern.matches thy (lhs, rhs)
    (*the condition "null prems" is necessary because conditional rewrites
      with extra variables in the conditions may terminate although
      the rhs is an instance of the lhs; example: ?m < ?n ==> f(?n) == f(?m)*)
    orelse
  is_Const lhs andalso not (is_Const rhs);

fun decomp_simp thm =
  let
    val thy = Thm.theory_of_thm thm;
    val prop = Thm.prop_of thm;
    val prems = Logic.strip_imp_prems prop;
    val concl = Drule.strip_imp_concl (Thm.cprop_of thm);
    val (lhs, rhs) = Thm.dest_equals concl handle TERM _ =>
      raise SIMPLIFIER ("Rewrite rule not a meta-equality", thm);
    val elhs = Thm.dest_arg (Thm.cprop_of (Thm.eta_conversion lhs));
    val erhs = Envir.eta_contract (term_of rhs);
    val perm =
      var_perm (term_of elhs, erhs) andalso
      not (term_of elhs aconv erhs) andalso
      not (is_Var (term_of elhs));
  in (thy, prems, term_of lhs, elhs, term_of rhs, perm) end;

fun decomp_simp' thm =
  let val (_, _, lhs, _, rhs, _) = decomp_simp thm in
    if Thm.nprems_of thm > 0 then raise SIMPLIFIER ("Bad conditional rewrite rule", thm)
    else (lhs, rhs)
  end;

fun mk_eq_True (ss as Simpset (_, {mk_rews = {mk_eq_True, ...}, ...})) (thm, name) =
  (case mk_eq_True ss thm of
    NONE => []
  | SOME eq_True =>
      let
        val (_, _, lhs, elhs, _, _) = decomp_simp eq_True;
      in [{thm = eq_True, name = name, lhs = lhs, elhs = elhs, perm = false}] end);

(*create the rewrite rule and possibly also the eq_True variant,
  in case there are extra vars on the rhs*)
fun rrule_eq_True (thm, name, lhs, elhs, rhs, ss, thm2) =
  let val rrule = {thm = thm, name = name, lhs = lhs, elhs = elhs, perm = false} in
    if rewrite_rule_extra_vars [] lhs rhs then
      mk_eq_True ss (thm2, name) @ [rrule]
    else [rrule]
  end;

fun mk_rrule ss (thm, name) =
  let val (_, prems, lhs, elhs, rhs, perm) = decomp_simp thm in
    if perm then [{thm = thm, name = name, lhs = lhs, elhs = elhs, perm = true}]
    else
      (*weak test for loops*)
      if rewrite_rule_extra_vars prems lhs rhs orelse is_Var (term_of elhs)
      then mk_eq_True ss (thm, name)
      else rrule_eq_True (thm, name, lhs, elhs, rhs, ss, thm)
  end;

fun orient_rrule ss (thm, name) =
  let
    val (thy, prems, lhs, elhs, rhs, perm) = decomp_simp thm;
    val Simpset (_, {mk_rews = {reorient, mk_sym, ...}, ...}) = ss;
  in
    if perm then [{thm = thm, name = name, lhs = lhs, elhs = elhs, perm = true}]
    else if reorient thy prems lhs rhs then
      if reorient thy prems rhs lhs
      then mk_eq_True ss (thm, name)
      else
        (case mk_sym ss thm of
          NONE => []
        | SOME thm' =>
            let val (_, _, lhs', elhs', rhs', _) = decomp_simp thm'
            in rrule_eq_True (thm', name, lhs', elhs', rhs', ss, thm) end)
    else rrule_eq_True (thm, name, lhs, elhs, rhs, ss, thm)
  end;

fun extract_rews (ss as Simpset (_, {mk_rews = {mk, ...}, ...}), thms) =
  maps (fn thm => map (rpair (Thm.get_name_hint thm)) (mk ss thm)) thms;

fun extract_safe_rrules (ss, thm) =
  maps (orient_rrule ss) (extract_rews (ss, [thm]));


(* add/del rules explicitly *)

fun comb_simps comb mk_rrule (ss, thms) =
  let
    val rews = extract_rews (ss, thms);
  in fold (fold comb o mk_rrule) rews ss end;

fun ss addsimps thms =
  comb_simps insert_rrule (mk_rrule ss) (ss, thms);

fun ss delsimps thms =
  comb_simps del_rrule (map mk_rrule2 o mk_rrule ss) (ss, thms);

fun add_simp thm ss = ss addsimps [thm];
fun del_simp thm ss = ss delsimps [thm];


(* congs *)

fun cong_name (Const (a, _)) = SOME a
  | cong_name (Free (a, _)) = SOME ("Free: " ^ a)
  | cong_name _ = NONE;

local

fun is_full_cong_prems [] [] = true
  | is_full_cong_prems [] _ = false
  | is_full_cong_prems (p :: prems) varpairs =
      (case Logic.strip_assums_concl p of
        Const ("==", _) $ lhs $ rhs =>
          let val (x, xs) = strip_comb lhs and (y, ys) = strip_comb rhs in
            is_Var x andalso forall is_Bound xs andalso
            not (has_duplicates (op =) xs) andalso xs = ys andalso
            member (op =) varpairs (x, y) andalso
            is_full_cong_prems prems (remove (op =) (x, y) varpairs)
          end
      | _ => false);

fun is_full_cong thm =
  let
    val prems = Thm.prems_of thm and concl = Thm.concl_of thm;
    val (lhs, rhs) = Logic.dest_equals concl;
    val (f, xs) = strip_comb lhs and (g, ys) = strip_comb rhs;
  in
    f = g andalso not (has_duplicates (op =) (xs @ ys)) andalso length xs = length ys andalso
    is_full_cong_prems prems (xs ~~ ys)
  end;

fun mk_cong (ss as Simpset (_, {mk_rews = {mk_cong = f, ...}, ...})) = f ss;

in

fun add_eqcong thm ss = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    let
      val (lhs, _) = Logic.dest_equals (Thm.concl_of thm)
        handle TERM _ => raise SIMPLIFIER ("Congruence not a meta-equality", thm);
    (*val lhs = Envir.eta_contract lhs;*)
      val a = the (cong_name (head_of lhs)) handle Option.Option =>
        raise SIMPLIFIER ("Congruence must start with a constant or free variable", thm);
      val (xs, weak) = congs;
      val _ =
        if AList.defined (op =) xs a
        then if_visible ss warning ("Overwriting congruence rule for " ^ quote a)
        else ();
      val xs' = AList.update (op =) (a, thm) xs;
      val weak' = if is_full_cong thm then weak else a :: weak;
    in ((xs', weak'), procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) end);

fun del_eqcong thm ss = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    let
      val (lhs, _) = Logic.dest_equals (Thm.concl_of thm)
        handle TERM _ => raise SIMPLIFIER ("Congruence not a meta-equality", thm);
    (*val lhs = Envir.eta_contract lhs;*)
      val a = the (cong_name (head_of lhs)) handle Option.Option =>
        raise SIMPLIFIER ("Congruence must start with a constant", thm);
      val (xs, _) = congs;
      val xs' = filter_out (fn (x : string, _) => x = a) xs;
      val weak' = xs' |> map_filter (fn (a, thm) =>
        if is_full_cong thm then NONE else SOME a);
    in ((xs', weak'), procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) end);

fun add_cong thm ss = add_eqcong (mk_cong ss thm) ss;
fun del_cong thm ss = del_eqcong (mk_cong ss thm) ss;

end;


(* simprocs *)

datatype simproc =
  Simproc of
    {name: string,
     lhss: cterm list,
     proc: morphism -> simpset -> cterm -> thm option,
     id: stamp * thm list};

fun eq_simproc (Simproc {id = id1, ...}, Simproc {id = id2, ...}) = eq_procid (id1, id2);

fun transform_simproc phi (Simproc {name, lhss, proc, id = (s, ths)}) =
  Simproc
   {name = name,
    lhss = map (Morphism.cterm phi) lhss,
    proc = Morphism.transform phi proc,
    id = (s, Morphism.fact phi ths)};

fun make_simproc {name, lhss, proc, identifier} =
  Simproc {name = name, lhss = lhss, proc = proc, id = (stamp (), identifier)};

fun mk_simproc name lhss proc =
  make_simproc {name = name, lhss = lhss, proc = fn _ => fn ss => fn ct =>
    proc (Proof_Context.theory_of (the_context ss)) ss (Thm.term_of ct), identifier = []};

(* FIXME avoid global thy and Logic.varify_global *)
fun simproc_global_i thy name = mk_simproc name o map (Thm.cterm_of thy o Logic.varify_global);
fun simproc_global thy name = simproc_global_i thy name o map (Syntax.read_term_global thy);


local

fun add_proc (proc as Proc {name, lhs, ...}) ss =
 (trace_cterm false (fn () => "Adding simplification procedure " ^ quote name ^ " for") ss lhs;
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    (congs, Net.insert_term eq_proc (term_of lhs, proc) procs,
      mk_rews, termless, subgoal_tac, loop_tacs, solvers)) ss
  handle Net.INSERT =>
    (if_visible ss warning ("Ignoring duplicate simplification procedure " ^ quote name); ss));

fun del_proc (proc as Proc {name, lhs, ...}) ss =
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    (congs, Net.delete_term eq_proc (term_of lhs, proc) procs,
      mk_rews, termless, subgoal_tac, loop_tacs, solvers)) ss
  handle Net.DELETE =>
    (if_visible ss warning ("Simplification procedure " ^ quote name ^ " not in simpset"); ss);

fun prep_procs (Simproc {name, lhss, proc, id}) =
  lhss |> map (fn lhs => Proc {name = name, lhs = lhs, proc = Morphism.form proc, id = id});

in

fun ss addsimprocs ps = fold (fold add_proc o prep_procs) ps ss;
fun ss delsimprocs ps = fold (fold del_proc o prep_procs) ps ss;

end;


(* mk_rews *)

local

fun map_mk_rews f = map_simpset2 (fn (congs, procs, {mk, mk_cong, mk_sym, mk_eq_True, reorient},
      termless, subgoal_tac, loop_tacs, solvers) =>
  let
    val (mk', mk_cong', mk_sym', mk_eq_True', reorient') =
      f (mk, mk_cong, mk_sym, mk_eq_True, reorient);
    val mk_rews' = {mk = mk', mk_cong = mk_cong', mk_sym = mk_sym', mk_eq_True = mk_eq_True',
      reorient = reorient'};
  in (congs, procs, mk_rews', termless, subgoal_tac, loop_tacs, solvers) end);

in

fun mksimps (ss as Simpset (_, {mk_rews = {mk, ...}, ...})) = mk ss;

fun set_mksimps mk = map_mk_rews (fn (_, mk_cong, mk_sym, mk_eq_True, reorient) =>
  (mk, mk_cong, mk_sym, mk_eq_True, reorient));

fun set_mkcong mk_cong = map_mk_rews (fn (mk, _, mk_sym, mk_eq_True, reorient) =>
  (mk, mk_cong, mk_sym, mk_eq_True, reorient));

fun set_mksym mk_sym = map_mk_rews (fn (mk, mk_cong, _, mk_eq_True, reorient) =>
  (mk, mk_cong, mk_sym, mk_eq_True, reorient));

fun set_mkeqTrue mk_eq_True = map_mk_rews (fn (mk, mk_cong, mk_sym, _, reorient) =>
  (mk, mk_cong, mk_sym, mk_eq_True, reorient));

fun set_reorient reorient = map_mk_rews (fn (mk, mk_cong, mk_sym, mk_eq_True, _) =>
  (mk, mk_cong, mk_sym, mk_eq_True, reorient));

end;


(* termless *)

fun set_termless termless =
  map_simpset2 (fn (congs, procs, mk_rews, _, subgoal_tac, loop_tacs, solvers) =>
   (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers));


(* tactics *)

fun set_subgoaler subgoal_tac =
  map_simpset2 (fn (congs, procs, mk_rews, termless, _, loop_tacs, solvers) =>
   (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers));

fun ss setloop' tac = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, _, solvers) =>
   (congs, procs, mk_rews, termless, subgoal_tac, [("", tac)], solvers));

fun ss setloop tac = ss setloop' (K tac);

fun ss addloop' (name, tac) = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    (congs, procs, mk_rews, termless, subgoal_tac,
     (if AList.defined (op =) loop_tacs name
      then if_visible ss warning ("Overwriting looper " ^ quote name)
      else (); AList.update (op =) (name, tac) loop_tacs), solvers));

fun ss addloop (name, tac) = ss addloop' (name, K tac);

fun ss delloop name = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    (congs, procs, mk_rews, termless, subgoal_tac,
     (if AList.defined (op =) loop_tacs name then ()
      else if_visible ss warning ("No such looper in simpset: " ^ quote name);
      AList.delete (op =) name loop_tacs), solvers));

fun ss setSSolver solver = ss |> map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (unsafe_solvers, _)) =>
    (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, (unsafe_solvers, [solver])));

fun ss addSSolver solver = ss |> map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (unsafe_solvers, solvers)) => (congs, procs, mk_rews, termless,
    subgoal_tac, loop_tacs, (unsafe_solvers, insert eq_solver solver solvers)));

fun ss setSolver solver = ss |> map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (_, solvers)) => (congs, procs, mk_rews, termless,
    subgoal_tac, loop_tacs, ([solver], solvers)));

fun ss addSolver solver = ss |> map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (unsafe_solvers, solvers)) => (congs, procs, mk_rews, termless,
    subgoal_tac, loop_tacs, (insert eq_solver solver unsafe_solvers, solvers)));

fun set_solvers solvers = map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, _) => (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (solvers, solvers)));


(* empty *)

fun init_ss mk_rews termless subgoal_tac solvers =
  make_simpset ((Net.empty, [], (0, []), (0, Unsynchronized.ref false), NONE),
    (([], []), Net.empty, mk_rews, termless, subgoal_tac, [], solvers));

fun clear_ss (ss as Simpset (_, {mk_rews, termless, subgoal_tac, solvers, ...})) =
  init_ss mk_rews termless subgoal_tac solvers
  |> inherit_context ss;

fun default_mk_sym _ th = SOME (th RS Drule.symmetric_thm);

val empty_ss =
  init_ss
    {mk = fn _ => fn th => if can Logic.dest_equals (Thm.concl_of th) then [th] else [],
      mk_cong = K I,
      mk_sym = default_mk_sym,
      mk_eq_True = K (K NONE),
      reorient = default_reorient}
    Term_Ord.termless (K (K no_tac)) ([], []);


(* merge *)  (*NOTE: ignores some fields of 2nd simpset*)

fun merge_ss (ss1, ss2) =
  if pointer_eq (ss1, ss2) then ss1
  else
    let
      val Simpset ({rules = rules1, prems = prems1, bounds = bounds1, depth = depth1, context = _},
       {congs = (congs1, weak1), procs = procs1, mk_rews, termless, subgoal_tac,
        loop_tacs = loop_tacs1, solvers = (unsafe_solvers1, solvers1)}) = ss1;
      val Simpset ({rules = rules2, prems = prems2, bounds = bounds2, depth = depth2, context = _},
       {congs = (congs2, weak2), procs = procs2, mk_rews = _, termless = _, subgoal_tac = _,
        loop_tacs = loop_tacs2, solvers = (unsafe_solvers2, solvers2)}) = ss2;

      val rules' = Net.merge eq_rrule (rules1, rules2);
      val prems' = Thm.merge_thms (prems1, prems2);
      val bounds' = if #1 bounds1 < #1 bounds2 then bounds2 else bounds1;
      val depth' = if #1 depth1 < #1 depth2 then depth2 else depth1;
      val congs' = merge (Thm.eq_thm_prop o pairself #2) (congs1, congs2);
      val weak' = merge (op =) (weak1, weak2);
      val procs' = Net.merge eq_proc (procs1, procs2);
      val loop_tacs' = AList.merge (op =) (K true) (loop_tacs1, loop_tacs2);
      val unsafe_solvers' = merge eq_solver (unsafe_solvers1, unsafe_solvers2);
      val solvers' = merge eq_solver (solvers1, solvers2);
    in
      make_simpset ((rules', prems', bounds', depth', NONE), ((congs', weak'), procs',
        mk_rews, termless, subgoal_tac, loop_tacs', (unsafe_solvers', solvers')))
    end;


(* dest_ss *)

fun dest_ss (Simpset ({rules, ...}, {congs, procs, loop_tacs, solvers, ...})) =
 {simps = Net.entries rules
    |> map (fn {name, thm, ...} => (name, thm)),
  procs = Net.entries procs
    |> map (fn Proc {name, lhs, id, ...} => ((name, lhs), id))
    |> partition_eq (eq_snd eq_procid)
    |> map (fn ps => (fst (fst (hd ps)), map (snd o fst) ps)),
  congs = #1 congs,
  weak_congs = #2 congs,
  loopers = map fst loop_tacs,
  unsafe_solvers = map solver_name (#1 solvers),
  safe_solvers = map solver_name (#2 solvers)};



(** rewriting **)

(*
  Uses conversions, see:
    L C Paulson, A higher-order implementation of rewriting,
    Science of Computer Programming 3 (1983), pages 119-149.
*)

fun check_conv msg ss thm thm' =
  let
    val thm'' = Thm.transitive thm thm' handle THM _ =>
     Thm.transitive thm (Thm.transitive
       (Thm.symmetric (Drule.beta_eta_conversion (Thm.lhs_of thm'))) thm')
  in if msg then trace_thm (fn () => "SUCCEEDED") ss thm' else (); SOME thm'' end
  handle THM _ =>
    let
      val _ $ _ $ prop0 = Thm.prop_of thm;
    in
      trace_thm (fn () => "Proved wrong thm (Check subgoaler?)") ss thm';
      trace_term false (fn () => "Should have proved:") ss prop0;
      NONE
    end;


(* mk_procrule *)

fun mk_procrule ss thm =
  let val (_, prems, lhs, elhs, rhs, _) = decomp_simp thm in
    if rewrite_rule_extra_vars prems lhs rhs
    then (cond_warn_thm "Extra vars on rhs:" ss thm; [])
    else [mk_rrule2 {thm = thm, name = "", lhs = lhs, elhs = elhs, perm = false}]
  end;


(* rewritec: conversion to apply the meta simpset to a term *)

(*Since the rewriting strategy is bottom-up, we avoid re-normalizing already
  normalized terms by carrying around the rhs of the rewrite rule just
  applied. This is called the `skeleton'. It is decomposed in parallel
  with the term. Once a Var is encountered, the corresponding term is
  already in normal form.
  skel0 is a dummy skeleton that is to enforce complete normalization.*)

val skel0 = Bound 0;

(*Use rhs as skeleton only if the lhs does not contain unnormalized bits.
  The latter may happen iff there are weak congruence rules for constants
  in the lhs.*)

fun uncond_skel ((_, weak), (lhs, rhs)) =
  if null weak then rhs  (*optimization*)
  else if exists_Const (member (op =) weak o #1) lhs then skel0
  else rhs;

(*Behaves like unconditional rule if rhs does not contain vars not in the lhs.
  Otherwise those vars may become instantiated with unnormalized terms
  while the premises are solved.*)

fun cond_skel (args as (_, (lhs, rhs))) =
  if subset (op =) (Term.add_vars rhs [], Term.add_vars lhs []) then uncond_skel args
  else skel0;

(*
  Rewriting -- we try in order:
    (1) beta reduction
    (2) unconditional rewrite rules
    (3) conditional rewrite rules
    (4) simplification procedures

  IMPORTANT: rewrite rules must not introduce new Vars or TVars!
*)

fun rewritec (prover, thyt, maxt) ss t =
  let
    val ctxt = the_context ss;
    val Simpset ({rules, ...}, {congs, procs, termless, ...}) = ss;
    val eta_thm = Thm.eta_conversion t;
    val eta_t' = Thm.rhs_of eta_thm;
    val eta_t = term_of eta_t';
    fun rew {thm, name, lhs, elhs, extra, fo, perm} =
      let
        val prop = Thm.prop_of thm;
        val (rthm, elhs') =
          if maxt = ~1 orelse not extra then (thm, elhs)
          else (Thm.incr_indexes (maxt + 1) thm, Thm.incr_indexes_cterm (maxt + 1) elhs);
        val insts =
          if fo then Thm.first_order_match (elhs', eta_t')
          else Thm.match (elhs', eta_t');
        val thm' = Thm.instantiate insts (Thm.rename_boundvars lhs eta_t rthm);
        val prop' = Thm.prop_of thm';
        val unconditional = (Logic.count_prems prop' = 0);
        val (lhs', rhs') = Logic.dest_equals (Logic.strip_imp_concl prop')
      in
        if perm andalso not (termless (rhs', lhs'))
        then (trace_named_thm (fn () => "Cannot apply permutative rewrite rule") ss (thm, name);
              trace_thm (fn () => "Term does not become smaller:") ss thm'; NONE)
        else (trace_named_thm (fn () => "Applying instance of rewrite rule") ss (thm, name);
           if unconditional
           then
             (trace_thm (fn () => "Rewriting:") ss thm';
              let
                val lr = Logic.dest_equals prop;
                val SOME thm'' = check_conv false ss eta_thm thm';
              in SOME (thm'', uncond_skel (congs, lr)) end)
           else
             (trace_thm (fn () => "Trying to rewrite:") ss thm';
              if simp_depth ss > Config.get ctxt simp_depth_limit
              then
                let
                  val s = "simp_depth_limit exceeded - giving up";
                  val _ = trace false (fn () => s) ss;
                  val _ = if_visible ss warning s;
                in NONE end
              else
              case prover ss thm' of
                NONE => (trace_thm (fn () => "FAILED") ss thm'; NONE)
              | SOME thm2 =>
                  (case check_conv true ss eta_thm thm2 of
                     NONE => NONE |
                     SOME thm2' =>
                       let val concl = Logic.strip_imp_concl prop
                           val lr = Logic.dest_equals concl
                       in SOME (thm2', cond_skel (congs, lr)) end)))
      end

    fun rews [] = NONE
      | rews (rrule :: rrules) =
          let val opt = rew rrule handle Pattern.MATCH => NONE
          in case opt of NONE => rews rrules | some => some end;

    fun sort_rrules rrs =
      let
        fun is_simple ({thm, ...}: rrule) =
          (case Thm.prop_of thm of
            Const ("==", _) $ _ $ _ => true
          | _ => false);
        fun sort [] (re1, re2) = re1 @ re2
          | sort (rr :: rrs) (re1, re2) =
              if is_simple rr
              then sort rrs (rr :: re1, re2)
              else sort rrs (re1, rr :: re2);
      in sort rrs ([], []) end;

    fun proc_rews [] = NONE
      | proc_rews (Proc {name, proc, lhs, ...} :: ps) =
          if Pattern.matches thyt (Thm.term_of lhs, Thm.term_of t) then
            (debug_term false (fn () => "Trying procedure " ^ quote name ^ " on:") ss eta_t;
             case proc ss eta_t' of
               NONE => (debug false (fn () => "FAILED") ss; proc_rews ps)
             | SOME raw_thm =>
                 (trace_thm (fn () => "Procedure " ^ quote name ^ " produced rewrite rule:")
                   ss raw_thm;
                  (case rews (mk_procrule ss raw_thm) of
                    NONE => (trace_cterm true (fn () => "IGNORED result of simproc " ^ quote name ^
                      " -- does not match") ss t; proc_rews ps)
                  | some => some)))
          else proc_rews ps;
  in
    (case eta_t of
      Abs _ $ _ => SOME (Thm.transitive eta_thm (Thm.beta_conversion false eta_t'), skel0)
    | _ =>
      (case rews (sort_rrules (Net.match_term rules eta_t)) of
        NONE => proc_rews (Net.match_term procs eta_t)
      | some => some))
  end;


(* conversion to apply a congruence rule to a term *)

fun congc prover ss maxt cong t =
  let val rthm = Thm.incr_indexes (maxt + 1) cong;
      val rlhs = fst (Thm.dest_equals (Drule.strip_imp_concl (cprop_of rthm)));
      val insts = Thm.match (rlhs, t)
      (* Thm.match can raise Pattern.MATCH;
         is handled when congc is called *)
      val thm' = Thm.instantiate insts (Thm.rename_boundvars (term_of rlhs) (term_of t) rthm);
      val _ = trace_thm (fn () => "Applying congruence rule:") ss thm';
      fun err (msg, thm) = (trace_thm (fn () => msg) ss thm; NONE)
  in
    (case prover thm' of
      NONE => err ("Congruence proof failed.  Could not prove", thm')
    | SOME thm2 =>
        (case check_conv true ss (Drule.beta_eta_conversion t) thm2 of
          NONE => err ("Congruence proof failed.  Should not have proved", thm2)
        | SOME thm2' =>
            if op aconv (pairself term_of (Thm.dest_equals (cprop_of thm2')))
            then NONE else SOME thm2'))
  end;

val (cA, (cB, cC)) =
  apsnd Thm.dest_equals (Thm.dest_implies (hd (cprems_of Drule.imp_cong)));

fun transitive1 NONE NONE = NONE
  | transitive1 (SOME thm1) NONE = SOME thm1
  | transitive1 NONE (SOME thm2) = SOME thm2
  | transitive1 (SOME thm1) (SOME thm2) = SOME (Thm.transitive thm1 thm2)

fun transitive2 thm = transitive1 (SOME thm);
fun transitive3 thm = transitive1 thm o SOME;

fun bottomc ((simprem, useprem, mutsimp), prover, thy, maxidx) =
  let
    fun botc skel ss t =
          if is_Var skel then NONE
          else
          (case subc skel ss t of
             some as SOME thm1 =>
               (case rewritec (prover, thy, maxidx) ss (Thm.rhs_of thm1) of
                  SOME (thm2, skel2) =>
                    transitive2 (Thm.transitive thm1 thm2)
                      (botc skel2 ss (Thm.rhs_of thm2))
                | NONE => some)
           | NONE =>
               (case rewritec (prover, thy, maxidx) ss t of
                  SOME (thm2, skel2) => transitive2 thm2
                    (botc skel2 ss (Thm.rhs_of thm2))
                | NONE => NONE))

    and try_botc ss t =
          (case botc skel0 ss t of
             SOME trec1 => trec1 | NONE => (Thm.reflexive t))

    and subc skel (ss as Simpset ({bounds, ...}, {congs, ...})) t0 =
       (case term_of t0 of
           Abs (a, T, _) =>
             let
                 val b = Name.bound (#1 bounds);
                 val (v, t') = Thm.dest_abs (SOME b) t0;
                 val b' = #1 (Term.dest_Free (Thm.term_of v));
                 val _ =
                   if b <> b' then
                     warning ("Simplifier: renamed bound variable " ^
                       quote b ^ " to " ^ quote b' ^ Position.here (Position.thread_data ()))
                   else ();
                 val ss' = add_bound ((b', T), a) ss;
                 val skel' = case skel of Abs (_, _, sk) => sk | _ => skel0;
             in case botc skel' ss' t' of
                  SOME thm => SOME (Thm.abstract_rule a v thm)
                | NONE => NONE
             end
         | t $ _ => (case t of
             Const ("==>", _) $ _  => impc t0 ss
           | Abs _ =>
               let val thm = Thm.beta_conversion false t0
               in case subc skel0 ss (Thm.rhs_of thm) of
                    NONE => SOME thm
                  | SOME thm' => SOME (Thm.transitive thm thm')
               end
           | _  =>
               let fun appc () =
                     let
                       val (tskel, uskel) = case skel of
                           tskel $ uskel => (tskel, uskel)
                         | _ => (skel0, skel0);
                       val (ct, cu) = Thm.dest_comb t0
                     in
                     (case botc tskel ss ct of
                        SOME thm1 =>
                          (case botc uskel ss cu of
                             SOME thm2 => SOME (Thm.combination thm1 thm2)
                           | NONE => SOME (Thm.combination thm1 (Thm.reflexive cu)))
                      | NONE =>
                          (case botc uskel ss cu of
                             SOME thm1 => SOME (Thm.combination (Thm.reflexive ct) thm1)
                           | NONE => NONE))
                     end
                   val (h, ts) = strip_comb t
               in case cong_name h of
                    SOME a =>
                      (case AList.lookup (op =) (fst congs) a of
                         NONE => appc ()
                       | SOME cong =>
  (*post processing: some partial applications h t1 ... tj, j <= length ts,
    may be a redex. Example: map (%x. x) = (%xs. xs) wrt map_cong*)
                          (let
                             val thm = congc (prover ss) ss maxidx cong t0;
                             val t = the_default t0 (Option.map Thm.rhs_of thm);
                             val (cl, cr) = Thm.dest_comb t
                             val dVar = Var(("", 0), dummyT)
                             val skel =
                               list_comb (h, replicate (length ts) dVar)
                           in case botc skel ss cl of
                                NONE => thm
                              | SOME thm' => transitive3 thm
                                  (Thm.combination thm' (Thm.reflexive cr))
                           end handle Pattern.MATCH => appc ()))
                  | _ => appc ()
               end)
         | _ => NONE)

    and impc ct ss =
      if mutsimp then mut_impc0 [] ct [] [] ss else nonmut_impc ct ss

    and rules_of_prem ss prem =
      if maxidx_of_term (term_of prem) <> ~1
      then (trace_cterm true
        (fn () => "Cannot add premise as rewrite rule because it contains (type) unknowns:")
          ss prem; ([], NONE))
      else
        let val asm = Thm.assume prem
        in (extract_safe_rrules (ss, asm), SOME asm) end

    and add_rrules (rrss, asms) ss =
      (fold o fold) insert_rrule rrss ss |> add_prems (map_filter I asms)

    and disch r prem eq =
      let
        val (lhs, rhs) = Thm.dest_equals (Thm.cprop_of eq);
        val eq' = Thm.implies_elim (Thm.instantiate
          ([], [(cA, prem), (cB, lhs), (cC, rhs)]) Drule.imp_cong)
          (Thm.implies_intr prem eq)
      in if not r then eq' else
        let
          val (prem', concl) = Thm.dest_implies lhs;
          val (prem'', _) = Thm.dest_implies rhs
        in Thm.transitive (Thm.transitive
          (Thm.instantiate ([], [(cA, prem'), (cB, prem), (cC, concl)])
             Drule.swap_prems_eq) eq')
          (Thm.instantiate ([], [(cA, prem), (cB, prem''), (cC, concl)])
             Drule.swap_prems_eq)
        end
      end

    and rebuild [] _ _ _ _ eq = eq
      | rebuild (prem :: prems) concl (_ :: rrss) (_ :: asms) ss eq =
          let
            val ss' = add_rrules (rev rrss, rev asms) ss;
            val concl' =
              Drule.mk_implies (prem, the_default concl (Option.map Thm.rhs_of eq));
            val dprem = Option.map (disch false prem)
          in
            (case rewritec (prover, thy, maxidx) ss' concl' of
              NONE => rebuild prems concl' rrss asms ss (dprem eq)
            | SOME (eq', _) => transitive2 (fold (disch false)
                  prems (the (transitive3 (dprem eq) eq')))
                (mut_impc0 (rev prems) (Thm.rhs_of eq') (rev rrss) (rev asms) ss))
          end

    and mut_impc0 prems concl rrss asms ss =
      let
        val prems' = strip_imp_prems concl;
        val (rrss', asms') = split_list (map (rules_of_prem ss) prems')
      in
        mut_impc (prems @ prems') (strip_imp_concl concl) (rrss @ rrss')
          (asms @ asms') [] [] [] [] ss ~1 ~1
      end

    and mut_impc [] concl [] [] prems' rrss' asms' eqns ss changed k =
        transitive1 (fold (fn (eq1, prem) => fn eq2 => transitive1 eq1
            (Option.map (disch false prem) eq2)) (eqns ~~ prems') NONE)
          (if changed > 0 then
             mut_impc (rev prems') concl (rev rrss') (rev asms')
               [] [] [] [] ss ~1 changed
           else rebuild prems' concl rrss' asms' ss
             (botc skel0 (add_rrules (rev rrss', rev asms') ss) concl))

      | mut_impc (prem :: prems) concl (rrs :: rrss) (asm :: asms)
          prems' rrss' asms' eqns ss changed k =
        case (if k = 0 then NONE else botc skel0 (add_rrules
          (rev rrss' @ rrss, rev asms' @ asms) ss) prem) of
            NONE => mut_impc prems concl rrss asms (prem :: prems')
              (rrs :: rrss') (asm :: asms') (NONE :: eqns) ss changed
              (if k = 0 then 0 else k - 1)
          | SOME eqn =>
            let
              val prem' = Thm.rhs_of eqn;
              val tprems = map term_of prems;
              val i = 1 + fold Integer.max (map (fn p =>
                find_index (fn q => q aconv p) tprems) (Thm.hyps_of eqn)) ~1;
              val (rrs', asm') = rules_of_prem ss prem'
            in mut_impc prems concl rrss asms (prem' :: prems')
              (rrs' :: rrss') (asm' :: asms') (SOME (fold_rev (disch true)
                (take i prems)
                (Drule.imp_cong_rule eqn (Thm.reflexive (Drule.list_implies
                  (drop i prems, concl))))) :: eqns)
                  ss (length prems') ~1
            end

     (*legacy code - only for backwards compatibility*)
    and nonmut_impc ct ss =
      let
        val (prem, conc) = Thm.dest_implies ct;
        val thm1 = if simprem then botc skel0 ss prem else NONE;
        val prem1 = the_default prem (Option.map Thm.rhs_of thm1);
        val ss1 =
          if not useprem then ss
          else add_rrules (apsnd single (apfst single (rules_of_prem ss prem1))) ss
      in
        (case botc skel0 ss1 conc of
          NONE =>
            (case thm1 of
              NONE => NONE
            | SOME thm1' => SOME (Drule.imp_cong_rule thm1' (Thm.reflexive conc)))
        | SOME thm2 =>
            let val thm2' = disch false prem1 thm2 in
              (case thm1 of
                NONE => SOME thm2'
              | SOME thm1' =>
                 SOME (Thm.transitive (Drule.imp_cong_rule thm1' (Thm.reflexive conc)) thm2'))
            end)
      end

 in try_botc end;


(* Meta-rewriting: rewrites t to u and returns the theorem t==u *)

(*
  Parameters:
    mode = (simplify A,
            use A in simplifying B,
            use prems of B (if B is again a meta-impl.) to simplify A)
           when simplifying A ==> B
    prover: how to solve premises in conditional rewrites and congruences
*)

val debug_bounds = Unsynchronized.ref false;

fun check_bounds ss ct =
  if ! debug_bounds then
    let
      val Simpset ({bounds = (_, bounds), ...}, _) = ss;
      val bs = fold_aterms (fn Free (x, _) =>
          if Name.is_bound x andalso not (AList.defined eq_bound bounds x)
          then insert (op =) x else I
        | _ => I) (term_of ct) [];
    in
      if null bs then ()
      else print_term_global ss true ("Simplifier: term contains loose bounds: " ^ commas_quote bs)
        (Thm.theory_of_cterm ct) (Thm.term_of ct)
    end
  else ();

fun rewrite_cterm mode prover raw_ss raw_ct =
  let
    val thy = Thm.theory_of_cterm raw_ct;
    val ct = Thm.adjust_maxidx_cterm ~1 raw_ct;
    val {maxidx, ...} = Thm.rep_cterm ct;
    val ss = inc_simp_depth (activate_context thy raw_ss);
    val depth = simp_depth ss;
    val _ =
      if depth mod 20 = 0 then
        if_visible ss warning ("Simplification depth " ^ string_of_int depth)
      else ();
    val _ = trace_cterm false (fn () => "SIMPLIFIER INVOKED ON THE FOLLOWING TERM:") ss ct;
    val _ = check_bounds ss ct;
  in bottomc (mode, Option.map Drule.flexflex_unique oo prover, thy, maxidx) ss ct end;

val simple_prover =
  SINGLE o (fn ss => ALLGOALS (resolve_tac (prems_of ss)));

fun rewrite _ [] ct = Thm.reflexive ct
  | rewrite full thms ct = rewrite_cterm (full, false, false) simple_prover
      (global_context (Thm.theory_of_cterm ct) empty_ss addsimps thms) ct;

fun simplify full thms = Conv.fconv_rule (rewrite full thms);
val rewrite_rule = simplify true;

(*simple term rewriting -- no proof*)
fun rewrite_term thy rules procs =
  Pattern.rewrite_term thy (map decomp_simp' rules) procs;

fun rewrite_thm mode prover ss = Conv.fconv_rule (rewrite_cterm mode prover ss);

(*Rewrite the subgoals of a proof state (represented by a theorem)*)
fun rewrite_goals_rule thms th =
  Conv.fconv_rule (Conv.prems_conv ~1 (rewrite_cterm (true, true, true) simple_prover
    (global_context (Thm.theory_of_thm th) empty_ss addsimps thms))) th;


(** meta-rewriting tactics **)

(*Rewrite all subgoals*)
fun rewrite_goals_tac defs = PRIMITIVE (rewrite_goals_rule defs);

(*Rewrite one subgoal*)
fun generic_rewrite_goal_tac mode prover_tac ss i thm =
  if 0 < i andalso i <= Thm.nprems_of thm then
    Seq.single (Conv.gconv_rule (rewrite_cterm mode (SINGLE o prover_tac) ss) i thm)
  else Seq.empty;

fun rewrite_goal_tac rews =
  let val ss = empty_ss addsimps rews in
    fn i => fn st => generic_rewrite_goal_tac (true, false, false) (K no_tac)
      (global_context (Thm.theory_of_thm st) ss) i st
  end;

(*Prunes all redundant parameters from the proof state by rewriting.*)
val prune_params_tac = rewrite_goals_tac [Drule.triv_forall_equality];


(* for folding definitions, handling critical pairs *)

(*The depth of nesting in a term*)
fun term_depth (Abs (_, _, t)) = 1 + term_depth t
  | term_depth (f $ t) = 1 + Int.max (term_depth f, term_depth t)
  | term_depth _ = 0;

val lhs_of_thm = #1 o Logic.dest_equals o prop_of;

(*folding should handle critical pairs!  E.g. K == Inl(0),  S == Inr(Inl(0))
  Returns longest lhs first to avoid folding its subexpressions.*)
fun sort_lhs_depths defs =
  let val keylist = AList.make (term_depth o lhs_of_thm) defs
      val keys = sort_distinct (rev_order o int_ord) (map #2 keylist)
  in map (AList.find (op =) keylist) keys end;

val rev_defs = sort_lhs_depths o map Thm.symmetric;

fun fold_rule defs = fold rewrite_rule (rev_defs defs);
fun fold_goals_tac defs = EVERY (map rewrite_goals_tac (rev_defs defs));


(* HHF normal form: !! before ==>, outermost !! generalized *)

local

fun gen_norm_hhf ss th =
  (if Drule.is_norm_hhf (Thm.prop_of th) then th
   else Conv.fconv_rule
    (rewrite_cterm (true, false, false) (K (K NONE)) (global_context (Thm.theory_of_thm th) ss)) th)
  |> Thm.adjust_maxidx_thm ~1
  |> Drule.gen_all;

val hhf_ss = empty_ss addsimps Drule.norm_hhf_eqs;

in

val norm_hhf = gen_norm_hhf hhf_ss;
val norm_hhf_protect = gen_norm_hhf (hhf_ss |> add_eqcong Drule.protect_cong);

end;

end;

structure Basic_Meta_Simplifier: BASIC_RAW_SIMPLIFIER = Raw_Simplifier;
open Basic_Meta_Simplifier;
