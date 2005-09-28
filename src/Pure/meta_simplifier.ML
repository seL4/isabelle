(*  Title:      Pure/meta_simplifier.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Stefan Berghofer

Meta-level Simplification.
*)

infix 4
  addsimps delsimps addeqcongs deleqcongs addcongs delcongs addsimprocs delsimprocs
  setmksimps setmkcong setmksym setmkeqTrue settermless setsubgoaler
  setloop addloop delloop setSSolver addSSolver setSolver addSolver;

signature BASIC_META_SIMPLIFIER =
sig
  val debug_simp: bool ref
  val trace_simp: bool ref
  val simp_depth_limit: int ref
  val trace_simp_depth_limit: int ref
  type rrule
  val eq_rrule: rrule * rrule -> bool
  type cong
  type simpset
  type proc
  type solver
  val mk_solver': string -> (simpset -> int -> tactic) -> solver
  val mk_solver: string -> (thm list -> int -> tactic) -> solver
  val rep_ss: simpset ->
   {rules: rrule Net.net,
    prems: thm list,
    bounds: int * ((string * typ) * string) list} *
   {congs: (string * cong) list * string list,
    procs: proc Net.net,
    mk_rews:
     {mk: thm -> thm list,
      mk_cong: thm -> thm,
      mk_sym: thm -> thm option,
      mk_eq_True: thm -> thm option},
    termless: term * term -> bool,
    subgoal_tac: simpset -> int -> tactic,
    loop_tacs: (string * (int -> tactic)) list,
    solvers: solver list * solver list}
  val print_ss: simpset -> unit
  val empty_ss: simpset
  val merge_ss: simpset * simpset -> simpset
  type simproc
  val mk_simproc: string -> cterm list ->
    (theory -> simpset -> term -> thm option) -> simproc
  val add_prems: thm list -> simpset -> simpset
  val prems_of_ss: simpset -> thm list
  val addsimps: simpset * thm list -> simpset
  val delsimps: simpset * thm list -> simpset
  val addeqcongs: simpset * thm list -> simpset
  val deleqcongs: simpset * thm list -> simpset
  val addcongs: simpset * thm list -> simpset
  val delcongs: simpset * thm list -> simpset
  val addsimprocs: simpset * simproc list -> simpset
  val delsimprocs: simpset * simproc list -> simpset
  val setmksimps: simpset * (thm -> thm list) -> simpset
  val setmkcong: simpset * (thm -> thm) -> simpset
  val setmksym: simpset * (thm -> thm option) -> simpset
  val setmkeqTrue: simpset * (thm -> thm option) -> simpset
  val settermless: simpset * (term * term -> bool) -> simpset
  val setsubgoaler: simpset * (simpset -> int -> tactic) -> simpset
  val setloop: simpset * (int -> tactic) -> simpset
  val addloop: simpset * (string * (int -> tactic)) -> simpset
  val delloop: simpset * string -> simpset
  val setSSolver: simpset * solver -> simpset
  val addSSolver: simpset * solver -> simpset
  val setSolver: simpset * solver -> simpset
  val addSolver: simpset * solver -> simpset
  val generic_simp_tac: bool -> bool * bool * bool -> simpset -> int -> tactic
end;

signature META_SIMPLIFIER =
sig
  include BASIC_META_SIMPLIFIER
  exception SIMPLIFIER of string * thm
  val clear_ss: simpset -> simpset
  exception SIMPROC_FAIL of string * exn
  val simproc_i: theory -> string -> term list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val simproc: theory -> string -> string list
    -> (theory -> simpset -> term -> thm option) -> simproc
  val inherit_bounds: simpset -> simpset -> simpset
  val rewrite_cterm: bool * bool * bool ->
    (simpset -> thm -> thm option) -> simpset -> cterm -> thm
  val rewrite_aux: (simpset -> thm -> thm option) -> bool -> thm list -> cterm -> thm
  val simplify_aux: (simpset -> thm -> thm option) -> bool -> thm list -> thm -> thm
  val rewrite_term: theory -> thm list -> (term -> term option) list -> term -> term
  val rewrite_thm: bool * bool * bool ->
    (simpset -> thm -> thm option) -> simpset -> thm -> thm
  val rewrite_goals_rule_aux: (simpset -> thm -> thm option) -> thm list -> thm -> thm
  val rewrite_goal_rule: bool * bool * bool ->
    (simpset -> thm -> thm option) -> simpset -> int -> thm -> thm
  val asm_rewrite_goal_tac: bool * bool * bool ->
    (simpset -> tactic) -> simpset -> int -> tactic
  val simp_thm: bool * bool * bool -> simpset -> thm -> thm
  val simp_cterm: bool * bool * bool -> simpset -> cterm -> thm
end;

structure MetaSimplifier: META_SIMPLIFIER =
struct


(** datatype simpset **)

(* rewrite rules *)

type rrule = {thm: thm, name: string, lhs: term, elhs: cterm, fo: bool, perm: bool};

(*thm: the rewrite rule;
  name: name of theorem from which rewrite rule was extracted;
  lhs: the left-hand side;
  elhs: the etac-contracted lhs;
  fo: use first-order matching;
  perm: the rewrite rule is permutative;

Remarks:
  - elhs is used for matching,
    lhs only for preservation of bound variable names;
  - fo is set iff
    either elhs is first-order (no Var is applied),
      in which case fo-matching is complete,
    or elhs is not a pattern,
      in which case there is nothing better to do;*)

fun eq_rrule ({thm = thm1, ...}: rrule, {thm = thm2, ...}: rrule) =
  Drule.eq_thm_prop (thm1, thm2);


(* congruences *)

type cong = {thm: thm, lhs: cterm};

fun eq_cong ({thm = thm1, ...}: cong, {thm = thm2, ...}: cong) =
  Drule.eq_thm_prop (thm1, thm2);


(* simplification sets, procedures, and solvers *)

(*A simpset contains data required during conversion:
    rules: discrimination net of rewrite rules;
    prems: current premises;
    bounds: maximal index of bound variables already used
      (for generating new names when rewriting under lambda abstractions);
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

type mk_rews =
 {mk: thm -> thm list,
  mk_cong: thm -> thm,
  mk_sym: thm -> thm option,
  mk_eq_True: thm -> thm option};

datatype simpset =
  Simpset of
   {rules: rrule Net.net,
    prems: thm list,
    bounds: int * ((string * typ) * string) list} *
   {congs: (string * cong) list * string list,
    procs: proc Net.net,
    mk_rews: mk_rews,
    termless: term * term -> bool,
    subgoal_tac: simpset -> int -> tactic,
    loop_tacs: (string * (int -> tactic)) list,
    solvers: solver list * solver list}
and proc =
  Proc of
   {name: string,
    lhs: cterm,
    proc: theory -> simpset -> term -> thm option,
    id: stamp}
and solver =
  Solver of
   {name: string,
    solver: simpset -> int -> tactic,
    id: stamp};


fun rep_ss (Simpset args) = args;

fun make_ss1 (rules, prems, bounds) =
  {rules = rules, prems = prems, bounds = bounds};

fun map_ss1 f {rules, prems, bounds} =
  make_ss1 (f (rules, prems, bounds));

fun make_ss2 (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =
  {congs = congs, procs = procs, mk_rews = mk_rews, termless = termless,
    subgoal_tac = subgoal_tac, loop_tacs = loop_tacs, solvers = solvers};

fun map_ss2 f {congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers} =
  make_ss2 (f (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers));

fun make_simpset (args1, args2) = Simpset (make_ss1 args1, make_ss2 args2);

fun map_simpset f (Simpset ({rules, prems, bounds},
    {congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers})) =
  make_simpset (f ((rules, prems, bounds),
    (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers)));

fun map_simpset1 f (Simpset (r1, r2)) = Simpset (map_ss1 f r1, r2);
fun map_simpset2 f (Simpset (r1, r2)) = Simpset (r1, map_ss2 f r2);

fun prems_of_ss (Simpset ({prems, ...}, _)) = prems;


fun eq_proc (Proc {id = id1, ...}, Proc {id = id2, ...}) = (id1 = id2);

fun mk_solver' name solver = Solver {name = name, solver = solver, id = stamp ()};
fun mk_solver name solver = mk_solver' name (solver o prems_of_ss);

fun solver_name (Solver {name, ...}) = name;
fun solver ths (Solver {solver = tacf, ...}) = tacf ths;
fun eq_solver (Solver {id = id1, ...}, Solver {id = id2, ...}) = (id1 = id2);
val merge_solvers = gen_merge_lists eq_solver;


(* diagnostics *)

exception SIMPLIFIER of string * thm;

val debug_simp = ref false;
val trace_simp = ref false;
val simp_depth = ref 0;
val simp_depth_limit = ref 100;
val trace_simp_depth_limit = ref 100;

local

fun println a =
  if ! simp_depth > ! trace_simp_depth_limit then ()
  else tracing (enclose "[" "]" (string_of_int (! simp_depth)) ^ a);

fun prnt warn a = if warn then warning a else println a;

fun show_bounds (Simpset ({bounds = (_, bs), ...}, _)) t =
  let
    val used = Term.add_term_names (t, []);
    val xs = rev (Term.variantlist (rev (map #2 bs), used));
    fun subst (((b, T), _), x') = (Free (b, T), Syntax.mark_boundT (x', T));
  in Term.subst_atomic (ListPair.map subst (bs, xs)) t end;

in

fun print_term warn a ss thy t = prnt warn (a ^ "\n" ^
  Sign.string_of_term thy (if ! debug_simp then t else show_bounds ss t));

fun debug warn a = if ! debug_simp then prnt warn a else ();
fun trace warn a = if ! trace_simp then prnt warn a else ();

fun debug_term warn a ss thy t = if ! debug_simp then print_term warn a ss thy t else ();
fun trace_term warn a ss thy t = if ! trace_simp then print_term warn a ss thy t else ();

fun trace_cterm warn a ss ct =
  if ! trace_simp then print_term warn a ss (Thm.theory_of_cterm ct) (Thm.term_of ct) else ();

fun trace_thm a ss th =
  if ! trace_simp then print_term false a ss (Thm.theory_of_thm th) (Thm.full_prop_of th) else ();

fun trace_named_thm a ss (th, name) =
  if ! trace_simp then
    print_term false (if name = "" then a else a ^ " " ^ quote name ^ ":") ss
      (Thm.theory_of_thm th) (Thm.full_prop_of th)
  else ();

fun warn_thm a ss th = print_term true a ss (Thm.theory_of_thm th) (Thm.full_prop_of th);

end;


(* print simpsets *)

fun print_ss ss =
  let
    val pretty_thms = map Display.pretty_thm;

    fun pretty_cong (name, th) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, Display.pretty_thm th];
    fun pretty_proc (name, lhss) =
      Pretty.big_list (name ^ ":") (map Display.pretty_cterm lhss);

    val Simpset ({rules, ...}, {congs, procs, loop_tacs, solvers, ...}) = ss;
    val smps = map #thm (Net.entries rules);
    val cngs = map (fn (name, {thm, ...}) => (name, thm)) (#1 congs);
    val prcs = Net.entries procs |>
      map (fn Proc {name, lhs, id, ...} => ((name, lhs), id))
      |> partition_eq (eq_snd (op =))
      |> map (fn ps => (#1 (#1 (hd ps)), map (#2 o #1) ps))
      |> Library.sort_wrt #1;
  in
    [Pretty.big_list "simplification rules:" (pretty_thms smps),
      Pretty.big_list "simplification procedures:" (map pretty_proc prcs),
      Pretty.big_list "congruences:" (map pretty_cong cngs),
      Pretty.strs ("loopers:" :: map (quote o #1) loop_tacs),
      Pretty.strs ("unsafe solvers:" :: map (quote o solver_name) (#1 solvers)),
      Pretty.strs ("safe solvers:" :: map (quote o solver_name) (#2 solvers))]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* empty simpsets *)

local

fun init_ss mk_rews termless subgoal_tac solvers =
  make_simpset ((Net.empty, [], (0, [])),
    (([], []), Net.empty, mk_rews, termless, subgoal_tac, [], solvers));

val basic_mk_rews: mk_rews =
 {mk = fn th => if can Logic.dest_equals (Thm.concl_of th) then [th] else [],
  mk_cong = I,
  mk_sym = SOME o Drule.symmetric_fun,
  mk_eq_True = K NONE};

in

val empty_ss = init_ss basic_mk_rews Term.termless (K (K no_tac)) ([], []);

fun clear_ss (Simpset (_, {mk_rews, termless, subgoal_tac, solvers, ...})) =
  init_ss mk_rews termless subgoal_tac solvers;

end;


(* merge simpsets *)            (*NOTE: ignores some fields of 2nd simpset*)

fun merge_ss (ss1, ss2) =
  let
    val Simpset ({rules = rules1, prems = prems1, bounds = bounds1},
     {congs = (congs1, weak1), procs = procs1, mk_rews, termless, subgoal_tac,
      loop_tacs = loop_tacs1, solvers = (unsafe_solvers1, solvers1)}) = ss1;
    val Simpset ({rules = rules2, prems = prems2, bounds = bounds2},
     {congs = (congs2, weak2), procs = procs2, mk_rews = _, termless = _, subgoal_tac = _,
      loop_tacs = loop_tacs2, solvers = (unsafe_solvers2, solvers2)}) = ss2;

    val rules' = Net.merge eq_rrule (rules1, rules2);
    val prems' = gen_merge_lists Drule.eq_thm_prop prems1 prems2;
    val bounds' = if #1 bounds1 < #1 bounds2 then bounds2 else bounds1;
    val congs' = gen_merge_lists (eq_cong o pairself #2) congs1 congs2;
    val weak' = merge_lists weak1 weak2;
    val procs' = Net.merge eq_proc (procs1, procs2);
    val loop_tacs' = merge_alists loop_tacs1 loop_tacs2;
    val unsafe_solvers' = merge_solvers unsafe_solvers1 unsafe_solvers2;
    val solvers' = merge_solvers solvers1 solvers2;
  in
    make_simpset ((rules', prems', bounds'), ((congs', weak'), procs',
      mk_rews, termless, subgoal_tac, loop_tacs', (unsafe_solvers', solvers')))
  end;


(* simprocs *)

exception SIMPROC_FAIL of string * exn;

datatype simproc = Simproc of proc list;

fun mk_simproc name lhss proc =
  let val id = stamp () in
    Simproc (lhss |> map (fn lhs =>
      Proc {name = name, lhs = lhs, proc = proc, id = id}))
  end;

fun simproc_i thy name = mk_simproc name o map (Thm.cterm_of thy o Logic.varify);
fun simproc thy name = simproc_i thy name o map (Sign.read_term thy);



(** simpset operations **)

(* bounds and prems *)

fun eq_bound (x: string, (y, _)) = x = y;

fun inherit_bounds (Simpset ({bounds, ...}, _)) =
  map_simpset1 (fn (rules, prems, _) => (rules, prems, bounds));

fun add_bound bound = map_simpset1 (fn (rules, prems, (count, bounds)) =>
  (rules, prems, (count + 1, bound :: bounds)));

fun add_prems ths = map_simpset1 (fn (rules, prems, bounds) =>
  (rules, ths @ prems, bounds));


(* addsimps *)

fun mk_rrule2 {thm, name, lhs, elhs, perm} =
  let
    val fo = Pattern.first_order (term_of elhs) orelse not (Pattern.pattern (term_of elhs))
  in {thm = thm, name = name, lhs = lhs, elhs = elhs, fo = fo, perm = perm} end;

fun insert_rrule quiet (ss, rrule as {thm, name, lhs, elhs, perm}) =
 (trace_named_thm "Adding rewrite rule" ss (thm, name);
  ss |> map_simpset1 (fn (rules, prems, bounds) =>
    let
      val rrule2 as {elhs, ...} = mk_rrule2 rrule;
      val rules' = Net.insert_term eq_rrule (term_of elhs, rrule2) rules;
    in (rules', prems, bounds) end)
  handle Net.INSERT =>
    (if quiet then () else warn_thm "Ignoring duplicate rewrite rule:" ss thm; ss));

fun vperm (Var _, Var _) = true
  | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
  | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
  | vperm (t, u) = (t = u);

fun var_perm (t, u) =
  vperm (t, u) andalso eq_set (term_varnames t, term_varnames u);

(* FIXME: it seems that the conditions on extra variables are too liberal if
prems are nonempty: does solving the prems really guarantee instantiation of
all its Vars? Better: a dynamic check each time a rule is applied.
*)
fun rewrite_rule_extra_vars prems elhs erhs =
  not (term_varnames erhs subset fold add_term_varnames prems (term_varnames elhs))
  orelse
  not (term_tvars erhs subset (term_tvars elhs union List.concat (map term_tvars prems)));

(*simple test for looping rewrite rules and stupid orientations*)
fun reorient thy prems lhs rhs =
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
    val {thy, prop, ...} = Thm.rep_thm thm;
    val prems = Logic.strip_imp_prems prop;
    val concl = Drule.strip_imp_concl (Thm.cprop_of thm);
    val (lhs, rhs) = Drule.dest_equals concl handle TERM _ =>
      raise SIMPLIFIER ("Rewrite rule not a meta-equality", thm);
    val (_, elhs) = Drule.dest_equals (Thm.cprop_of (Thm.eta_conversion lhs));
    val elhs = if term_of elhs aconv term_of lhs then lhs else elhs;  (*share identical copies*)
    val erhs = Pattern.eta_contract (term_of rhs);
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

fun mk_eq_True (Simpset (_, {mk_rews = {mk_eq_True, ...}, ...})) (thm, name) =
  (case mk_eq_True thm of
    NONE => []
  | SOME eq_True =>
      let val (_, _, lhs, elhs, _, _) = decomp_simp eq_True
      in [{thm = eq_True, name = name, lhs = lhs, elhs = elhs, perm = false}] end);

(*create the rewrite rule and possibly also the eq_True variant,
  in case there are extra vars on the rhs*)
fun rrule_eq_True (thm, name, lhs, elhs, rhs, ss, thm2) =
  let val rrule = {thm = thm, name = name, lhs = lhs, elhs = elhs, perm = false} in
    if term_varnames rhs subset term_varnames lhs andalso
      term_tvars rhs subset term_tvars lhs then [rrule]
    else mk_eq_True ss (thm2, name) @ [rrule]
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
  let val (thy, prems, lhs, elhs, rhs, perm) = decomp_simp thm in
    if perm then [{thm = thm, name = name, lhs = lhs, elhs = elhs, perm = true}]
    else if reorient thy prems lhs rhs then
      if reorient thy prems rhs lhs
      then mk_eq_True ss (thm, name)
      else
        let val Simpset (_, {mk_rews = {mk_sym, ...}, ...}) = ss in
          (case mk_sym thm of
            NONE => []
          | SOME thm' =>
              let val (_, _, lhs', elhs', rhs', _) = decomp_simp thm'
              in rrule_eq_True (thm', name, lhs', elhs', rhs', ss, thm) end)
        end
    else rrule_eq_True (thm, name, lhs, elhs, rhs, ss, thm)
  end;

fun extract_rews (Simpset (_, {mk_rews = {mk, ...}, ...}), thms) =
  List.concat (map (fn thm => map (rpair (Thm.name_of_thm thm)) (mk thm)) thms);

fun orient_comb_simps comb mk_rrule (ss, thms) =
  let
    val rews = extract_rews (ss, thms);
    val rrules = List.concat (map mk_rrule rews);
  in Library.foldl comb (ss, rrules) end;

fun extract_safe_rrules (ss, thm) =
  List.concat (map (orient_rrule ss) (extract_rews (ss, [thm])));

(*add rewrite rules explicitly; do not reorient!*)
fun ss addsimps thms =
  orient_comb_simps (insert_rrule false) (mk_rrule ss) (ss, thms);


(* delsimps *)

fun del_rrule (ss, rrule as {thm, elhs, ...}) =
  ss |> map_simpset1 (fn (rules, prems, bounds) =>
    (Net.delete_term eq_rrule (term_of elhs, rrule) rules, prems, bounds))
  handle Net.DELETE => (warn_thm "Rewrite rule not in simpset:" ss thm; ss);

fun ss delsimps thms =
  orient_comb_simps del_rrule (map mk_rrule2 o mk_rrule ss) (ss, thms);


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
            null (findrep xs) andalso xs = ys andalso
            (x, y) mem varpairs andalso
            is_full_cong_prems prems (varpairs \ (x, y))
          end
      | _ => false);

fun is_full_cong thm =
  let
    val prems = prems_of thm and concl = concl_of thm;
    val (lhs, rhs) = Logic.dest_equals concl;
    val (f, xs) = strip_comb lhs and (g, ys) = strip_comb rhs;
  in
    f = g andalso null (findrep (xs @ ys)) andalso length xs = length ys andalso
    is_full_cong_prems prems (xs ~~ ys)
  end;

fun add_cong (ss, thm) = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    let
      val (lhs, _) = Drule.dest_equals (Drule.strip_imp_concl (Thm.cprop_of thm))
        handle TERM _ => raise SIMPLIFIER ("Congruence not a meta-equality", thm);
    (*val lhs = Pattern.eta_contract lhs;*)
      val a = valOf (cong_name (head_of (term_of lhs))) handle Option =>
        raise SIMPLIFIER ("Congruence must start with a constant or free variable", thm);
      val (alist, weak) = congs;
      val alist2 = overwrite_warn (alist, (a, {lhs = lhs, thm = thm}))
        ("Overwriting congruence rule for " ^ quote a);
      val weak2 = if is_full_cong thm then weak else a :: weak;
    in ((alist2, weak2), procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) end);

fun del_cong (ss, thm) = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    let
      val (lhs, _) = Logic.dest_equals (Thm.concl_of thm) handle TERM _ =>
        raise SIMPLIFIER ("Congruence not a meta-equality", thm);
    (*val lhs = Pattern.eta_contract lhs;*)
      val a = valOf (cong_name (head_of lhs)) handle Option =>
        raise SIMPLIFIER ("Congruence must start with a constant", thm);
      val (alist, _) = congs;
      val alist2 = List.filter (fn (x, _) => x <> a) alist;
      val weak2 = alist2 |> List.mapPartial (fn (a, {thm, ...}) =>
        if is_full_cong thm then NONE else SOME a);
    in ((alist2, weak2), procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) end);

fun mk_cong (Simpset (_, {mk_rews = {mk_cong = f, ...}, ...})) = f;

in

val (op addeqcongs) = Library.foldl add_cong;
val (op deleqcongs) = Library.foldl del_cong;

fun ss addcongs congs = ss addeqcongs map (mk_cong ss) congs;
fun ss delcongs congs = ss deleqcongs map (mk_cong ss) congs;

end;


(* simprocs *)

local

fun add_proc (proc as Proc {name, lhs, ...}) ss =
 (trace_cterm false ("Adding simplification procedure " ^ quote name ^ " for") ss lhs;
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    (congs, Net.insert_term eq_proc (term_of lhs, proc) procs,
      mk_rews, termless, subgoal_tac, loop_tacs, solvers)) ss
  handle Net.INSERT =>
    (warning ("Ignoring duplicate simplification procedure " ^ quote name); ss));

fun del_proc (proc as Proc {name, lhs, ...}) ss =
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    (congs, Net.delete_term eq_proc (term_of lhs, proc) procs,
      mk_rews, termless, subgoal_tac, loop_tacs, solvers)) ss
  handle Net.DELETE =>
    (warning ("Simplification procedure " ^ quote name ^ " not in simpset"); ss);

in

fun ss addsimprocs ps = fold (fn Simproc procs => fold add_proc procs) ps ss;
fun ss delsimprocs ps = fold (fn Simproc procs => fold del_proc procs) ps ss;

end;


(* mk_rews *)

local

fun map_mk_rews f = map_simpset2 (fn (congs, procs, {mk, mk_cong, mk_sym, mk_eq_True},
      termless, subgoal_tac, loop_tacs, solvers) =>
  let val (mk', mk_cong', mk_sym', mk_eq_True') = f (mk, mk_cong, mk_sym, mk_eq_True) in
    (congs, procs, {mk = mk', mk_cong = mk_cong', mk_sym = mk_sym', mk_eq_True = mk_eq_True'},
      termless, subgoal_tac, loop_tacs, solvers)
  end);

in

fun ss setmksimps mk = ss |> map_mk_rews (fn (_, mk_cong, mk_sym, mk_eq_True) =>
  (mk, mk_cong, mk_sym, mk_eq_True));

fun ss setmkcong mk_cong = ss |> map_mk_rews (fn (mk, _, mk_sym, mk_eq_True) =>
  (mk, mk_cong, mk_sym, mk_eq_True));

fun ss setmksym mk_sym = ss |> map_mk_rews (fn (mk, mk_cong, _, mk_eq_True) =>
  (mk, mk_cong, mk_sym, mk_eq_True));

fun ss setmkeqTrue mk_eq_True = ss |> map_mk_rews (fn (mk, mk_cong, mk_sym, _) =>
  (mk, mk_cong, mk_sym, mk_eq_True));

end;


(* termless *)

fun ss settermless termless = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, _, subgoal_tac, loop_tacs, solvers) =>
   (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers));


(* tactics *)

fun ss setsubgoaler subgoal_tac = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, _, loop_tacs, solvers) =>
   (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers));

fun ss setloop tac = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, _, solvers) =>
   (congs, procs, mk_rews, termless, subgoal_tac, [("", tac)], solvers));

fun ss addloop (name, tac) = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    (congs, procs, mk_rews, termless, subgoal_tac,
      overwrite_warn (loop_tacs, (name, tac)) ("Overwriting looper " ^ quote name),
      solvers));

fun ss delloop name = ss |>
  map_simpset2 (fn (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, solvers) =>
    let val loop_tacs' = filter_out (equal name o #1) loop_tacs in
      if length loop_tacs <> length loop_tacs' then ()
      else warning ("No such looper in simpset: " ^ quote name);
      (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs', solvers)
    end);

fun ss setSSolver solver = ss |> map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (unsafe_solvers, _)) =>
    (congs, procs, mk_rews, termless, subgoal_tac, loop_tacs, (unsafe_solvers, [solver])));

fun ss addSSolver solver = ss |> map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (unsafe_solvers, solvers)) => (congs, procs, mk_rews, termless,
    subgoal_tac, loop_tacs, (unsafe_solvers, merge_solvers solvers [solver])));

fun ss setSolver solver = ss |> map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (_, solvers)) => (congs, procs, mk_rews, termless,
    subgoal_tac, loop_tacs, ([solver], solvers)));

fun ss addSolver solver = ss |> map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (unsafe_solvers, solvers)) => (congs, procs, mk_rews, termless,
    subgoal_tac, loop_tacs, (merge_solvers unsafe_solvers [solver], solvers)));

fun set_solvers solvers = map_simpset2 (fn (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, _) => (congs, procs, mk_rews, termless,
  subgoal_tac, loop_tacs, (solvers, solvers)));



(** rewriting **)

(*
  Uses conversions, see:
    L C Paulson, A higher-order implementation of rewriting,
    Science of Computer Programming 3 (1983), pages 119-149.
*)

val dest_eq = Drule.dest_equals o Thm.cprop_of;
val lhs_of = #1 o dest_eq;
val rhs_of = #2 o dest_eq;

fun check_conv msg ss thm thm' =
  let
    val thm'' = transitive thm (transitive
      (symmetric (Drule.beta_eta_conversion (lhs_of thm'))) thm')
  in if msg then trace_thm "SUCCEEDED" ss thm' else (); SOME thm'' end
  handle THM _ =>
    let val {thy, prop = _ $ _ $ prop0, ...} = Thm.rep_thm thm in
      trace_thm "Proved wrong thm (Check subgoaler?)" ss thm';
      trace_term false "Should have proved:" ss thy prop0;
      NONE
    end;


(* mk_procrule *)

fun mk_procrule ss thm =
  let val (_, prems, lhs, elhs, rhs, _) = decomp_simp thm in
    if rewrite_rule_extra_vars prems lhs rhs
    then (warn_thm "Extra vars on rhs:" ss thm; [])
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
  else if exists_Const (fn (c, _) => c mem weak) lhs then skel0
  else rhs;

(*Behaves like unconditional rule if rhs does not contain vars not in the lhs.
  Otherwise those vars may become instantiated with unnormalized terms
  while the premises are solved.*)

fun cond_skel (args as (congs, (lhs, rhs))) =
  if term_varnames rhs subset term_varnames lhs then uncond_skel args
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
    val Simpset ({rules, ...}, {congs, procs, termless, ...}) = ss;
    val eta_thm = Thm.eta_conversion t;
    val eta_t' = rhs_of eta_thm;
    val eta_t = term_of eta_t';
    fun rew {thm, name, lhs, elhs, fo, perm} =
      let
        val {thy, prop, maxidx, ...} = rep_thm thm;
        val (rthm, elhs') = if maxt = ~1 then (thm, elhs)
          else (Thm.incr_indexes (maxt+1) thm, Thm.cterm_incr_indexes (maxt+1) elhs);
        val insts = if fo then Thm.cterm_first_order_match (elhs', eta_t')
                          else Thm.cterm_match (elhs', eta_t');
        val thm' = Thm.instantiate insts (Thm.rename_boundvars lhs eta_t rthm);
        val prop' = Thm.prop_of thm';
        val unconditional = (Logic.count_prems (prop',0) = 0);
        val (lhs', rhs') = Logic.dest_equals (Logic.strip_imp_concl prop')
      in
        if perm andalso not (termless (rhs', lhs'))
        then (trace_named_thm "Cannot apply permutative rewrite rule" ss (thm, name);
              trace_thm "Term does not become smaller:" ss thm'; NONE)
        else (trace_named_thm "Applying instance of rewrite rule" ss (thm, name);
           if unconditional
           then
             (trace_thm "Rewriting:" ss thm';
              let val lr = Logic.dest_equals prop;
                  val SOME thm'' = check_conv false ss eta_thm thm'
              in SOME (thm'', uncond_skel (congs, lr)) end)
           else
             (trace_thm "Trying to rewrite:" ss thm';
              if !simp_depth > !simp_depth_limit
              then let val s = "simp_depth_limit exceeded - giving up"
                   in trace false s; warning s; NONE end
              else
              case prover ss thm' of
                NONE => (trace_thm "FAILED" ss thm'; NONE)
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

    fun sort_rrules rrs = let
      fun is_simple({thm, ...}:rrule) = case Thm.prop_of thm of
                                      Const("==",_) $ _ $ _ => true
                                      | _                   => false
      fun sort []        (re1,re2) = re1 @ re2
        | sort (rr::rrs) (re1,re2) = if is_simple rr
                                     then sort rrs (rr::re1,re2)
                                     else sort rrs (re1,rr::re2)
    in sort rrs ([],[]) end

    fun proc_rews [] = NONE
      | proc_rews (Proc {name, proc, lhs, ...} :: ps) =
          if Pattern.matches thyt (Thm.term_of lhs, Thm.term_of t) then
            (debug_term false ("Trying procedure " ^ quote name ^ " on:") ss thyt eta_t;
             case transform_failure (curry SIMPROC_FAIL name)
                 (fn () => proc thyt ss eta_t) () of
               NONE => (debug false "FAILED"; proc_rews ps)
             | SOME raw_thm =>
                 (trace_thm ("Procedure " ^ quote name ^ " produced rewrite rule:") ss raw_thm;
                  (case rews (mk_procrule ss raw_thm) of
                    NONE => (trace_cterm true ("IGNORED result of simproc " ^ quote name ^
                      " -- does not match") ss t; proc_rews ps)
                  | some => some)))
          else proc_rews ps;
  in case eta_t of
       Abs _ $ _ => SOME (transitive eta_thm
         (beta_conversion false eta_t'), skel0)
     | _ => (case rews (sort_rrules (Net.match_term rules eta_t)) of
               NONE => proc_rews (Net.match_term procs eta_t)
             | some => some)
  end;


(* conversion to apply a congruence rule to a term *)

fun congc prover ss maxt {thm=cong,lhs=lhs} t =
  let val rthm = Thm.incr_indexes (maxt+1) cong;
      val rlhs = fst (Drule.dest_equals (Drule.strip_imp_concl (cprop_of rthm)));
      val insts = Thm.cterm_match (rlhs, t)
      (* Pattern.match can raise Pattern.MATCH;
         is handled when congc is called *)
      val thm' = Thm.instantiate insts (Thm.rename_boundvars (term_of rlhs) (term_of t) rthm);
      val unit = trace_thm "Applying congruence rule:" ss thm';
      fun err (msg, thm) = (trace_thm msg ss thm; NONE)
  in case prover thm' of
       NONE => err ("Congruence proof failed.  Could not prove", thm')
     | SOME thm2 => (case check_conv true ss (Drule.beta_eta_conversion t) thm2 of
          NONE => err ("Congruence proof failed.  Should not have proved", thm2)
        | SOME thm2' =>
            if op aconv (pairself term_of (dest_equals (cprop_of thm2')))
            then NONE else SOME thm2')
  end;

val (cA, (cB, cC)) =
  apsnd dest_equals (dest_implies (hd (cprems_of Drule.imp_cong)));

fun transitive1 NONE NONE = NONE
  | transitive1 (SOME thm1) NONE = SOME thm1
  | transitive1 NONE (SOME thm2) = SOME thm2
  | transitive1 (SOME thm1) (SOME thm2) = SOME (transitive thm1 thm2)

fun transitive2 thm = transitive1 (SOME thm);
fun transitive3 thm = transitive1 thm o SOME;

fun bottomc ((simprem, useprem, mutsimp), prover, thy, maxidx) =
  let
    fun botc skel ss t =
          if is_Var skel then NONE
          else
          (case subc skel ss t of
             some as SOME thm1 =>
               (case rewritec (prover, thy, maxidx) ss (rhs_of thm1) of
                  SOME (thm2, skel2) =>
                    transitive2 (transitive thm1 thm2)
                      (botc skel2 ss (rhs_of thm2))
                | NONE => some)
           | NONE =>
               (case rewritec (prover, thy, maxidx) ss t of
                  SOME (thm2, skel2) => transitive2 thm2
                    (botc skel2 ss (rhs_of thm2))
                | NONE => NONE))

    and try_botc ss t =
          (case botc skel0 ss t of
             SOME trec1 => trec1 | NONE => (reflexive t))

    and subc skel (ss as Simpset ({bounds, ...}, {congs, ...})) t0 =
       (case term_of t0 of
           Abs (a, T, t) =>
             let
                 val b = Term.bound (#1 bounds);
                 val (v, t') = Thm.dest_abs (SOME b) t0;
                 val b' = #1 (Term.dest_Free (Thm.term_of v));
                 val _ = conditional (b <> b') (fn () =>
                   warning ("Simplifier: renamed bound variable " ^ quote b ^ " to " ^ quote b'));
                 val ss' = add_bound ((b', T), a) ss;
                 val skel' = case skel of Abs (_, _, sk) => sk | _ => skel0;
             in case botc skel' ss' t' of
                  SOME thm => SOME (abstract_rule a v thm)
                | NONE => NONE
             end
         | t $ _ => (case t of
             Const ("==>", _) $ _  => impc t0 ss
           | Abs _ =>
               let val thm = beta_conversion false t0
               in case subc skel0 ss (rhs_of thm) of
                    NONE => SOME thm
                  | SOME thm' => SOME (transitive thm thm')
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
                             SOME thm2 => SOME (combination thm1 thm2)
                           | NONE => SOME (combination thm1 (reflexive cu)))
                      | NONE =>
                          (case botc uskel ss cu of
                             SOME thm1 => SOME (combination (reflexive ct) thm1)
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
                             val t = getOpt (Option.map rhs_of thm, t0);
                             val (cl, cr) = Thm.dest_comb t
                             val dVar = Var(("", 0), dummyT)
                             val skel =
                               list_comb (h, replicate (length ts) dVar)
                           in case botc skel ss cl of
                                NONE => thm
                              | SOME thm' => transitive3 thm
                                  (combination thm' (reflexive cr))
                           end handle TERM _ => error "congc result"
                                    | Pattern.MATCH => appc ()))
                  | _ => appc ()
               end)
         | _ => NONE)

    and impc ct ss =
      if mutsimp then mut_impc0 [] ct [] [] ss else nonmut_impc ct ss

    and rules_of_prem ss prem =
      if maxidx_of_term (term_of prem) <> ~1
      then (trace_cterm true
        "Cannot add premise as rewrite rule because it contains (type) unknowns:" ss prem; ([], NONE))
      else
        let val asm = assume prem
        in (extract_safe_rrules (ss, asm), SOME asm) end

    and add_rrules (rrss, asms) ss =
      Library.foldl (insert_rrule true) (ss, List.concat rrss) |> add_prems (List.mapPartial I asms)

    and disch r (prem, eq) =
      let
        val (lhs, rhs) = dest_eq eq;
        val eq' = implies_elim (Thm.instantiate
          ([], [(cA, prem), (cB, lhs), (cC, rhs)]) Drule.imp_cong)
          (implies_intr prem eq)
      in if not r then eq' else
        let
          val (prem', concl) = dest_implies lhs;
          val (prem'', _) = dest_implies rhs
        in transitive (transitive
          (Thm.instantiate ([], [(cA, prem'), (cB, prem), (cC, concl)])
             Drule.swap_prems_eq) eq')
          (Thm.instantiate ([], [(cA, prem), (cB, prem''), (cC, concl)])
             Drule.swap_prems_eq)
        end
      end

    and rebuild [] _ _ _ _ eq = eq
      | rebuild (prem :: prems) concl (rrs :: rrss) (asm :: asms) ss eq =
          let
            val ss' = add_rrules (rev rrss, rev asms) ss;
            val concl' =
              Drule.mk_implies (prem, getOpt (Option.map rhs_of eq, concl));
            val dprem = Option.map (curry (disch false) prem)
          in case rewritec (prover, thy, maxidx) ss' concl' of
              NONE => rebuild prems concl' rrss asms ss (dprem eq)
            | SOME (eq', _) => transitive2 (Library.foldl (disch false o swap)
                  (valOf (transitive3 (dprem eq) eq'), prems))
                (mut_impc0 (rev prems) (rhs_of eq') (rev rrss) (rev asms) ss)
          end

    and mut_impc0 prems concl rrss asms ss =
      let
        val prems' = strip_imp_prems concl;
        val (rrss', asms') = split_list (map (rules_of_prem ss) prems')
      in mut_impc (prems @ prems') (strip_imp_concl concl) (rrss @ rrss')
        (asms @ asms') [] [] [] [] ss ~1 ~1
      end

    and mut_impc [] concl [] [] prems' rrss' asms' eqns ss changed k =
        transitive1 (Library.foldl (fn (eq2, (eq1, prem)) => transitive1 eq1
            (Option.map (curry (disch false) prem) eq2)) (NONE, eqns ~~ prems'))
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
              val prem' = rhs_of eqn;
              val tprems = map term_of prems;
              val i = 1 + Library.foldl Int.max (~1, map (fn p =>
                find_index_eq p tprems) (#hyps (rep_thm eqn)));
              val (rrs', asm') = rules_of_prem ss prem'
            in mut_impc prems concl rrss asms (prem' :: prems')
              (rrs' :: rrss') (asm' :: asms') (SOME (foldr (disch true)
                (Drule.imp_cong' eqn (reflexive (Drule.list_implies
                  (Library.drop (i, prems), concl)))) (Library.take (i, prems))) :: eqns) ss (length prems') ~1
            end

     (*legacy code - only for backwards compatibility*)
     and nonmut_impc ct ss =
       let val (prem, conc) = dest_implies ct;
           val thm1 = if simprem then botc skel0 ss prem else NONE;
           val prem1 = getOpt (Option.map rhs_of thm1, prem);
           val ss1 = if not useprem then ss else add_rrules
             (apsnd single (apfst single (rules_of_prem ss prem1))) ss
       in (case botc skel0 ss1 conc of
           NONE => (case thm1 of
               NONE => NONE
             | SOME thm1' => SOME (Drule.imp_cong' thm1' (reflexive conc)))
         | SOME thm2 =>
           let val thm2' = disch false (prem1, thm2)
           in (case thm1 of
               NONE => SOME thm2'
             | SOME thm1' =>
                 SOME (transitive (Drule.imp_cong' thm1' (reflexive conc)) thm2'))
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

val debug_bounds = ref false;

fun check_bounds ss ct = conditional (! debug_bounds) (fn () =>
  let
    val Simpset ({bounds = (_, bounds), ...}, _) = ss;
    val bs = fold_aterms (fn Free (x, _) =>
        if Term.is_bound x andalso not (AList.defined eq_bound bounds x)
        then insert (op =) x else I
      | _ => I) (term_of ct) [];
  in
    if null bs then ()
    else print_term true ("Simplifier: term contains loose bounds: " ^ commas bs) ss
      (Thm.theory_of_cterm ct) (Thm.term_of ct)
  end);

fun rewrite_cterm mode prover ss ct =
  (inc simp_depth;
   if !simp_depth mod 20 = 0
   then warning ("Simplification depth " ^ string_of_int (!simp_depth))
   else ();
   trace_cterm false "SIMPLIFIER INVOKED ON THE FOLLOWING TERM:" ss ct;
   check_bounds ss ct;
   let val {thy, t, maxidx, ...} = Thm.rep_cterm ct
       val res = bottomc (mode, prover, thy, maxidx) ss ct
         handle THM (s, _, thms) =>
         error ("Exception THM was raised in simplifier:\n" ^ s ^ "\n" ^
           Pretty.string_of (Display.pretty_thms thms))
   in dec simp_depth; res end
  ) handle exn => (dec simp_depth; raise exn);

(*Rewrite a cterm*)
fun rewrite_aux _ _ [] = (fn ct => Thm.reflexive ct)
  | rewrite_aux prover full thms =
      rewrite_cterm (full, false, false) prover (empty_ss addsimps thms);

(*Rewrite a theorem*)
fun simplify_aux _ _ [] = (fn th => th)
  | simplify_aux prover full thms =
      Drule.fconv_rule (rewrite_cterm (full, false, false) prover (empty_ss addsimps thms));

(*simple term rewriting -- no proof*)
fun rewrite_term thy rules procs =
  Pattern.rewrite_term thy (map decomp_simp' rules) procs;

fun rewrite_thm mode prover ss = Drule.fconv_rule (rewrite_cterm mode prover ss);

(*Rewrite the subgoals of a proof state (represented by a theorem) *)
fun rewrite_goals_rule_aux _ []   th = th
  | rewrite_goals_rule_aux prover thms th =
      Drule.fconv_rule (Drule.goals_conv (K true) (rewrite_cterm (true, true, false) prover
        (empty_ss addsimps thms))) th;

(*Rewrite the subgoal of a proof state (represented by a theorem)*)
fun rewrite_goal_rule mode prover ss i thm =
  if 0 < i  andalso  i <= nprems_of thm
  then Drule.fconv_rule (Drule.goals_conv (fn j => j=i) (rewrite_cterm mode prover ss)) thm
  else raise THM("rewrite_goal_rule",i,[thm]);

(*Rewrite subgoal i only.  SELECT_GOAL avoids inefficiencies in goals_conv.*)
fun asm_rewrite_goal_tac mode prover_tac ss =
  SELECT_GOAL
    (PRIMITIVE (rewrite_goal_rule mode (SINGLE o prover_tac) ss 1));



(** simplification tactics and rules **)

fun solve_all_tac solvers ss =
  let
    val Simpset (_, {subgoal_tac, ...}) = ss;
    val solve_tac = subgoal_tac (set_solvers solvers ss) THEN_ALL_NEW (K no_tac);
  in DEPTH_SOLVE (solve_tac 1) end;

(*NOTE: may instantiate unknowns that appear also in other subgoals*)
fun generic_simp_tac safe mode ss =
  let
    val Simpset (_, {loop_tacs, solvers = (unsafe_solvers, solvers), ...}) = ss;
    val loop_tac = FIRST' (map #2 loop_tacs);
    val solve_tac = FIRST' (map (solver ss) (if safe then solvers else unsafe_solvers));

    fun simp_loop_tac i =
      asm_rewrite_goal_tac mode (solve_all_tac unsafe_solvers) ss i THEN
      (solve_tac i ORELSE TRY ((loop_tac THEN_ALL_NEW simp_loop_tac) i));
  in simp_loop_tac end;

fun simp rew mode ss thm =
  let
    val Simpset (_, {solvers = (unsafe_solvers, _), ...}) = ss;
    val tacf = solve_all_tac unsafe_solvers;
    fun prover s th = Option.map #1 (Seq.pull (tacf s th));
  in rew mode prover ss thm end;

val simp_thm = simp rewrite_thm;
val simp_cterm = simp rewrite_cterm;

end;

structure BasicMetaSimplifier: BASIC_META_SIMPLIFIER = MetaSimplifier;
open BasicMetaSimplifier;
