(*  Title:      Tools/induct.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof by cases and induction.
*)

signature INDUCT_DATA =
sig
  val cases_default: thm
  val atomize: thm list
  val rulify: thm list
  val rulify_fallback: thm list
end;

signature INDUCT =
sig
  (*rule declarations*)
  val vars_of: term -> term list
  val dest_rules: Proof.context ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list,
      type_coinduct: (string * thm) list, set_coinduct: (string * thm) list}
  val print_rules: Proof.context -> unit
  val lookup_casesT: Proof.context -> string -> thm option
  val lookup_casesS: Proof.context -> string -> thm option
  val lookup_inductT: Proof.context -> string -> thm option
  val lookup_inductS: Proof.context -> string -> thm option
  val lookup_coinductT: Proof.context -> string -> thm option
  val lookup_coinductS: Proof.context -> string -> thm option
  val find_casesT: Proof.context -> typ -> thm list
  val find_casesS: Proof.context -> term -> thm list
  val find_inductT: Proof.context -> typ -> thm list
  val find_inductS: Proof.context -> term -> thm list
  val find_coinductT: Proof.context -> typ -> thm list
  val find_coinductS: Proof.context -> term -> thm list
  val cases_type: string -> attribute
  val cases_set: string -> attribute
  val induct_type: string -> attribute
  val induct_set: string -> attribute
  val coinduct_type: string -> attribute
  val coinduct_set: string -> attribute
  val casesN: string
  val inductN: string
  val coinductN: string
  val typeN: string
  val setN: string
  (*proof methods*)
  val fix_tac: Proof.context -> int -> (string * typ) list -> int -> tactic
  val add_defs: (string option * term) option list -> Proof.context ->
    (term option list * thm list) * Proof.context
  val atomize_term: theory -> term -> term
  val atomize_tac: int -> tactic
  val inner_atomize_tac: int -> tactic
  val rulified_term: thm -> theory * term
  val rulify_tac: int -> tactic
  val internalize: int -> thm -> thm
  val guess_instance: thm -> int -> thm -> thm Seq.seq
  val cases_tac: Proof.context -> bool -> term option list list -> thm option ->
    thm list -> int -> cases_tactic
  val induct_tac: Proof.context -> bool -> (string option * term) option list list ->
    (string * typ) list list -> term option list -> thm list option -> thm list -> int ->
    cases_tactic
  val coinduct_tac: Proof.context -> bool -> term option list -> term option list ->
    thm option -> thm list -> int -> cases_tactic
  val setup: theory -> theory
end;

functor InductFun(Data: INDUCT_DATA): INDUCT =
struct


(** misc utils **)

(* encode_type -- for indexing purposes *)

fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
  | encode_type (TFree (a, _)) = Free (a, dummyT)
  | encode_type (TVar (a, _)) = Var (a, dummyT);


(* variables -- ordered left-to-right, preferring right *)

fun vars_of tm =
  rev (distinct (op =) (Term.fold_aterms (fn (t as Var _) => cons t | _ => I) tm []));

local

val mk_var = encode_type o #2 o Term.dest_Var;

fun concl_var which thm = mk_var (which (vars_of (Thm.concl_of thm))) handle Empty =>
  raise THM ("No variables in conclusion of rule", 0, [thm]);

in

fun left_var_prem thm = mk_var (hd (vars_of (hd (Thm.prems_of thm)))) handle Empty =>
  raise THM ("No variables in major premise of rule", 0, [thm]);

val left_var_concl = concl_var hd;
val right_var_concl = concl_var List.last;

end;



(** induct data **)

(* rules *)

type rules = (string * thm) NetRules.T;

val init_rules =
  NetRules.init (fn ((s1: string, th1), (s2, th2)) => s1 = s2 andalso
    Thm.eq_thm_prop (th1, th2));

fun lookup_rule (rs: rules) = AList.lookup (op =) (NetRules.rules rs);

fun pretty_rules ctxt kind rs =
  let val thms = map snd (NetRules.rules rs)
  in Pretty.big_list kind (map (ProofContext.pretty_thm ctxt) thms) end;


(* context data *)

structure Induct = GenericDataFun
(
  type T = (rules * rules) * (rules * rules) * (rules * rules);
  val empty =
    ((init_rules (left_var_prem o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (right_var_concl o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (left_var_concl o #2), init_rules (Thm.concl_of o #2)));
  val extend = I;
  fun merge _ (((casesT1, casesS1), (inductT1, inductS1), (coinductT1, coinductS1)),
      ((casesT2, casesS2), (inductT2, inductS2), (coinductT2, coinductS2))) =
    ((NetRules.merge (casesT1, casesT2), NetRules.merge (casesS1, casesS2)),
      (NetRules.merge (inductT1, inductT2), NetRules.merge (inductS1, inductS2)),
      (NetRules.merge (coinductT1, coinductT2), NetRules.merge (coinductS1, coinductS2)));
);

val get_local = Induct.get o Context.Proof;

fun dest_rules ctxt =
  let val ((casesT, casesS), (inductT, inductS), (coinductT, coinductS)) = get_local ctxt in
    {type_cases = NetRules.rules casesT,
     set_cases = NetRules.rules casesS,
     type_induct = NetRules.rules inductT,
     set_induct = NetRules.rules inductS,
     type_coinduct = NetRules.rules coinductT,
     set_coinduct = NetRules.rules coinductS}
  end;

fun print_rules ctxt =
  let val ((casesT, casesS), (inductT, inductS), (coinductT, coinductS)) = get_local ctxt in
   [pretty_rules ctxt "coinduct type:" coinductT,
    pretty_rules ctxt "coinduct set:" coinductS,
    pretty_rules ctxt "induct type:" inductT,
    pretty_rules ctxt "induct set:" inductS,
    pretty_rules ctxt "cases type:" casesT,
    pretty_rules ctxt "cases set:" casesS]
    |> Pretty.chunks |> Pretty.writeln
  end;

val _ = OuterSyntax.add_parsers [
  OuterSyntax.improper_command "print_induct_rules" "print induction and cases rules"
    OuterKeyword.diag (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (print_rules o Toplevel.context_of)))];


(* access rules *)

val lookup_casesT = lookup_rule o #1 o #1 o get_local;
val lookup_casesS = lookup_rule o #2 o #1 o get_local;
val lookup_inductT = lookup_rule o #1 o #2 o get_local;
val lookup_inductS = lookup_rule o #2 o #2 o get_local;
val lookup_coinductT = lookup_rule o #1 o #3 o get_local;
val lookup_coinductS = lookup_rule o #2 o #3 o get_local;


fun find_rules which how ctxt x =
  map snd (NetRules.retrieve (which (get_local ctxt)) (how x));

val find_casesT = find_rules (#1 o #1) encode_type;
val find_casesS = find_rules (#2 o #1) I;
val find_inductT = find_rules (#1 o #2) encode_type;
val find_inductS = find_rules (#2 o #2) I;
val find_coinductT = find_rules (#1 o #3) encode_type;
val find_coinductS = find_rules (#2 o #3) I;



(** attributes **)

local

fun mk_att f g name arg =
  let val (x, thm) = g arg in (Induct.map (f (name, thm)) x, thm) end;

fun map1 f (x, y, z) = (f x, y, z);
fun map2 f (x, y, z) = (x, f y, z);
fun map3 f (x, y, z) = (x, y, f z);

fun add_casesT rule x = map1 (apfst (NetRules.insert rule)) x;
fun add_casesS rule x = map1 (apsnd (NetRules.insert rule)) x;
fun add_inductT rule x = map2 (apfst (NetRules.insert rule)) x;
fun add_inductS rule x = map2 (apsnd (NetRules.insert rule)) x;
fun add_coinductT rule x = map3 (apfst (NetRules.insert rule)) x;
fun add_coinductS rule x = map3 (apsnd (NetRules.insert rule)) x;

fun consumes0 x = RuleCases.consumes_default 0 x;
fun consumes1 x = RuleCases.consumes_default 1 x;

in

val cases_type = mk_att add_casesT consumes0;
val cases_set = mk_att add_casesS consumes1;
val induct_type = mk_att add_inductT consumes0;
val induct_set = mk_att add_inductS consumes1;
val coinduct_type = mk_att add_coinductT consumes0;
val coinduct_set = mk_att add_coinductS consumes1;

end;



(** attribute syntax **)

val casesN = "cases";
val inductN = "induct";
val coinductN = "coinduct";

val typeN = "type";
val setN = "set";

local

fun spec k arg =
  Scan.lift (Args.$$$ k -- Args.colon) |-- arg ||
  Scan.lift (Args.$$$ k) >> K "";

fun attrib add_type add_set =
  Attrib.syntax (spec typeN Args.tyname >> add_type || spec setN Args.const >> add_set);

val cases_att = attrib cases_type cases_set;
val induct_att = attrib induct_type induct_set;
val coinduct_att = attrib coinduct_type coinduct_set;

in

val attrib_setup = Attrib.add_attributes
 [(casesN, cases_att, "declaration of cases rule for type or set"),
  (inductN, induct_att, "declaration of induction rule for type or set"),
  (coinductN, coinduct_att, "declaration of coinduction rule for type or set")];

end;



(** method utils **)

(* alignment *)

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (Library.take (n, xs) ~~ ys) end;

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (Library.drop (m - n, xs) ~~ ys) end;


(* prep_inst *)

fun prep_inst thy align tune (tm, ts) =
  let
    val cert = Thm.cterm_of thy;
    fun prep_var (x, SOME t) =
          let
            val cx = cert x;
            val {T = xT, thy, ...} = Thm.rep_cterm cx;
            val ct = cert (tune t);
          in
            if Sign.typ_instance thy (#T (Thm.rep_cterm ct), xT) then SOME (cx, ct)
            else error (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Display.pretty_cterm ct, Pretty.str " ::", Pretty.brk 1,
              Display.pretty_ctyp (#T (Thm.crep_cterm ct))]))
          end
      | prep_var (_, NONE) = NONE;
    val xs = vars_of tm;
  in
    align "Rule has fewer variables than instantiations given" xs ts
    |> map_filter prep_var
  end;


(* trace_rules *)

fun trace_rules _ kind [] = error ("Unable to figure out " ^ kind ^ " rule")
  | trace_rules ctxt _ rules = Method.trace ctxt rules;


(* make_cases *)

fun make_cases is_open rule =
  RuleCases.make_common is_open (Thm.theory_of_thm rule, Thm.prop_of rule);

fun warn_open true = legacy_feature "open rule cases in proof method"
  | warn_open false = ();



(** cases method **)

(*
  rule selection scheme:
          cases         - default case split
    `x:A` cases ...     - set cases
          cases t       - type cases
    ...   cases ... r   - explicit rule
*)

local

fun get_casesT ctxt ((SOME t :: _) :: _) = find_casesT ctxt (Term.fastype_of t)
  | get_casesT _ _ = [];

fun get_casesS ctxt (fact :: _) = find_casesS ctxt (Thm.concl_of fact)
  | get_casesS _ _ = [];

in

fun cases_tac ctxt is_open insts opt_rule facts =
  let
    val _ = warn_open is_open;
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    fun inst_rule r =
      if null insts then `RuleCases.get r
      else (align_left "Rule has fewer premises than arguments given" (Thm.prems_of r) insts
        |> maps (prep_inst thy align_left I)
        |> Drule.cterm_instantiate) r |> pair (RuleCases.get r);

    val ruleq =
      (case opt_rule of
        SOME r => Seq.single (inst_rule r)
      | NONE =>
          (get_casesS ctxt facts @ get_casesT ctxt insts @ [Data.cases_default])
          |> tap (trace_rules ctxt casesN)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));
  in
    fn i => fn st =>
      ruleq
      |> Seq.maps (RuleCases.consume [] facts)
      |> Seq.maps (fn ((cases, (_, more_facts)), rule) =>
        CASES (make_cases is_open rule cases)
          (Method.insert_tac more_facts i THEN Tactic.rtac rule i) st)
  end;

end;



(** induct method **)

val conjunction_congs = [@{thm Pure.all_conjunction}, @{thm imp_conjunction}];


(* atomize *)

fun atomize_term thy =
  MetaSimplifier.rewrite_term thy Data.atomize []
  #> ObjectLogic.drop_judgment thy;

val atomize_cterm = MetaSimplifier.rewrite true Data.atomize;

val atomize_tac = Simplifier.rewrite_goal_tac Data.atomize;

val inner_atomize_tac =
  Simplifier.rewrite_goal_tac (map Thm.symmetric conjunction_congs) THEN' atomize_tac;


(* rulify *)

fun rulify_term thy =
  MetaSimplifier.rewrite_term thy (Data.rulify @ conjunction_congs) [] #>
  MetaSimplifier.rewrite_term thy Data.rulify_fallback [];

fun rulified_term thm =
  let
    val thy = Thm.theory_of_thm thm;
    val rulify = rulify_term thy;
    val (As, B) = Logic.strip_horn (Thm.prop_of thm);
  in (thy, Logic.list_implies (map rulify As, rulify B)) end;

val rulify_tac =
  Simplifier.rewrite_goal_tac (Data.rulify @ conjunction_congs) THEN'
  Simplifier.rewrite_goal_tac Data.rulify_fallback THEN'
  Goal.conjunction_tac THEN_ALL_NEW
  (Simplifier.rewrite_goal_tac [@{thm Pure.conjunction_imp}] THEN' Goal.norm_hhf_tac);


(* prepare rule *)

fun rule_instance thy inst rule =
  Drule.cterm_instantiate (prep_inst thy align_left I (Thm.prop_of rule, inst)) rule;

fun internalize k th =
  th |> Thm.permute_prems 0 k
  |> Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of th - k) atomize_cterm);


(* guess rule instantiation -- cannot handle pending goal parameters *)

local

fun dest_env thy (env as Envir.Envir {iTs, ...}) =
  let
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;
    val pairs = Envir.alist_of env;
    val ts = map (cert o Envir.norm_term env o #2 o #2) pairs;
    val xs = map2 (curry (cert o Var)) (map #1 pairs) (map (#T o Thm.rep_cterm) ts);
  in (map (fn (xi, (S, T)) => (certT (TVar (xi, S)), certT T)) (Vartab.dest iTs), xs ~~ ts) end;

in

fun guess_instance rule i st =
  let
    val {thy, maxidx, ...} = Thm.rep_thm st;
    val goal = Thm.term_of (Thm.cprem_of st i);  (*exception Subscript*)
    val params = rev (rename_wrt_term goal (Logic.strip_params goal));
  in
    if not (null params) then
      (warning ("Cannot determine rule instantiation due to pending parameter(s): " ^
        commas_quote (map (Sign.string_of_term thy o Syntax.mark_boundT) params));
      Seq.single rule)
    else
      let
        val rule' = Thm.incr_indexes (maxidx + 1) rule;
        val concl = Logic.strip_assums_concl goal;
      in
        Unify.smash_unifiers thy [(Thm.concl_of rule', concl)]
          (Envir.empty (#maxidx (Thm.rep_thm rule')))
        |> Seq.map (fn env => Drule.instantiate (dest_env thy env) rule')
      end
  end handle Subscript => Seq.empty;

end;


(* special renaming of rule parameters *)

fun special_rename_params ctxt [[SOME (Free (z, Type (T, _)))]] [thm] =
      let
        val x = ProofContext.revert_skolem ctxt z;
        fun index i [] = []
          | index i (y :: ys) =
              if x = y then x ^ string_of_int i :: index (i + 1) ys
              else y :: index i ys;
        fun rename_params [] = []
          | rename_params ((y, Type (U, _)) :: ys) =
              (if U = T then x else y) :: rename_params ys
          | rename_params ((y, _) :: ys) = y :: rename_params ys;
        fun rename_asm A =
          let
            val xs = rename_params (Logic.strip_params A);
            val xs' =
              (case List.filter (equal x) xs of
                [] => xs | [_] => xs | _ => index 1 xs);
          in Logic.list_rename_params (xs', A) end;
        fun rename_prop p =
          let val (As, C) = Logic.strip_horn p
          in Logic.list_implies (map rename_asm As, C) end;
        val cp' = cterm_fun rename_prop (Thm.cprop_of thm);
        val thm' = Thm.equal_elim (Thm.reflexive cp') thm;
      in [RuleCases.save thm thm'] end
  | special_rename_params _ _ ths = ths;


(* fix_tac *)

local

fun goal_prefix k ((c as Const ("all", _)) $ Abs (a, T, B)) = c $ Abs (a, T, goal_prefix k B)
  | goal_prefix 0 _ = Term.dummy_pattern propT
  | goal_prefix k ((c as Const ("==>", _)) $ A $ B) = c $ A $ goal_prefix (k - 1) B
  | goal_prefix _ _ = Term.dummy_pattern propT;

fun goal_params k (Const ("all", _) $ Abs (_, _, B)) = goal_params k B + 1
  | goal_params 0 _ = 0
  | goal_params k (Const ("==>", _) $ _ $ B) = goal_params (k - 1) B
  | goal_params _ _ = 0;

fun meta_spec_tac ctxt n (x, T) = SUBGOAL (fn (goal, i) =>
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;

    val v = Free (x, T);
    fun spec_rule prfx (xs, body) =
      @{thm Pure.meta_spec}
      |> Thm.rename_params_rule ([ProofContext.revert_skolem ctxt x], 1)
      |> Thm.lift_rule (cert prfx)
      |> `(Thm.prop_of #> Logic.strip_assums_concl)
      |-> (fn pred $ arg =>
        Drule.cterm_instantiate
          [(cert (Term.head_of pred), cert (Logic.rlist_abs (xs, body))),
           (cert (Term.head_of arg), cert (Logic.rlist_abs (xs, v)))]);

    fun goal_concl k xs (Const ("all", _) $ Abs (a, T, B)) = goal_concl k ((a, T) :: xs) B
      | goal_concl 0 xs B =
          if not (Term.exists_subterm (fn t => t aconv v) B) then NONE
          else SOME (xs, Term.absfree (x, T, Term.incr_boundvars 1 B))
      | goal_concl k xs (Const ("==>", _) $ _ $ B) = goal_concl (k - 1) xs B
      | goal_concl _ _ _ = NONE;
  in
    (case goal_concl n [] goal of
      SOME concl =>
        (compose_tac (false, spec_rule (goal_prefix n goal) concl, 1) THEN' rtac asm_rl) i
    | NONE => all_tac)
  end);

fun miniscope_tac p =
  CONVERSION (Conv.forall_conv p (MetaSimplifier.rewrite true [Thm.symmetric Drule.norm_hhf_eq]));

in

fun fix_tac _ _ [] = K all_tac
  | fix_tac ctxt n xs = SUBGOAL (fn (goal, i) =>
     (EVERY' (map (meta_spec_tac ctxt n) xs) THEN'
      (miniscope_tac (goal_params n goal))) i);

end;


(* add_defs *)

fun add_defs def_insts =
  let
    fun add (SOME (SOME x, t)) ctxt =
          let val ([(lhs, (_, th))], ctxt') = LocalDefs.add_defs [((x, NoSyn), (("", []), t))] ctxt
          in ((SOME lhs, [th]), ctxt') end
      | add (SOME (NONE, t)) ctxt = ((SOME t, []), ctxt)
      | add NONE ctxt = ((NONE, []), ctxt);
  in fold_map add def_insts #> apfst (split_list #> apsnd flat) end;


(* induct_tac *)

(*
  rule selection scheme:
    `x:A` induct ...     - set induction
          induct x       - type induction
    ...   induct ... r   - explicit rule
*)

local

fun get_inductT ctxt insts =
  fold_rev multiply (insts |> map_filter (fn [] => NONE | ts => List.last ts)
    |> map (find_inductT ctxt o Term.fastype_of)) [[]]
  |> filter_out (forall PureThy.is_internal);

fun get_inductS ctxt (fact :: _) = map single (find_inductS ctxt (Thm.concl_of fact))
  | get_inductS _ _ = [];

in

fun induct_tac ctxt is_open def_insts arbitrary taking opt_rule facts =
  let
    val _ = warn_open is_open;
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val ((insts, defs), defs_ctxt) = fold_map add_defs def_insts ctxt |>> split_list;
    val atomized_defs = map (map (Conv.fconv_rule ObjectLogic.atomize)) defs;

    fun inst_rule (concls, r) =
      (if null insts then `RuleCases.get r
       else (align_left "Rule has fewer conclusions than arguments given"
          (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
        |> maps (prep_inst thy align_right (atomize_term thy))
        |> Drule.cterm_instantiate) r |> pair (RuleCases.get r))
      |> (fn ((cases, consumes), th) => (((cases, concls), consumes), th));

    val ruleq =
      (case opt_rule of
        SOME rs => Seq.single (inst_rule (RuleCases.strict_mutual_rule ctxt rs))
      | NONE =>
          (get_inductS ctxt facts @
            map (special_rename_params defs_ctxt insts) (get_inductT ctxt insts))
          |> map_filter (RuleCases.mutual_rule ctxt)
          |> tap (trace_rules ctxt inductN o map #2)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));

    fun rule_cases rule =
      RuleCases.make_nested is_open (Thm.prop_of rule) (rulified_term rule);
  in
    (fn i => fn st =>
      ruleq
      |> Seq.maps (RuleCases.consume (flat defs) facts)
      |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
          (CONJUNCTS (ALLGOALS
            (Method.insert_tac (more_facts @ nth_list atomized_defs (j - 1))
              THEN' fix_tac defs_ctxt
                (nth concls (j - 1) + more_consumes)
                (nth_list arbitrary (j - 1))))
          THEN' inner_atomize_tac) j))
        THEN' atomize_tac) i st |> Seq.maps (fn st' =>
            guess_instance (internalize more_consumes rule) i st'
            |> Seq.map (rule_instance thy taking)
            |> Seq.maps (fn rule' =>
              CASES (rule_cases rule' cases)
                (Tactic.rtac rule' i THEN
                  PRIMITIVE (singleton (ProofContext.export defs_ctxt ctxt))) st'))))
    THEN_ALL_NEW_CASES rulify_tac
  end;

end;



(** coinduct method **)

(*
  rule selection scheme:
    goal "x:A" coinduct ...   - set coinduction
               coinduct x     - type coinduction
               coinduct ... r - explicit rule
*)

local

fun get_coinductT ctxt (SOME t :: _) = find_coinductT ctxt (Term.fastype_of t)
  | get_coinductT _ _ = [];

fun get_coinductS ctxt goal = find_coinductS ctxt (Logic.strip_assums_concl goal);

in

fun coinduct_tac ctxt is_open inst taking opt_rule facts =
  let
    val _ = warn_open is_open;
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    fun inst_rule r =
      if null inst then `RuleCases.get r
      else Drule.cterm_instantiate (prep_inst thy align_left I (Thm.concl_of r, inst)) r
        |> pair (RuleCases.get r);

    fun ruleq goal =
      (case opt_rule of
        SOME r => Seq.single (inst_rule r)
      | NONE =>
          (get_coinductS ctxt goal @ get_coinductT ctxt inst)
          |> tap (trace_rules ctxt coinductN)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));
  in
    SUBGOAL_CASES (fn (goal, i) => fn st =>
      ruleq goal
      |> Seq.maps (RuleCases.consume [] facts)
      |> Seq.maps (fn ((cases, (_, more_facts)), rule) =>
        guess_instance rule i st
        |> Seq.map (rule_instance thy taking)
        |> Seq.maps (fn rule' =>
          CASES (make_cases is_open rule' cases)
            (Method.insert_tac more_facts i THEN Tactic.rtac rule' i) st)))
  end;

end;



(** concrete syntax **)

val openN = "open";
val arbitraryN = "arbitrary";
val takingN = "taking";
val ruleN = "rule";

local

fun single_rule [rule] = rule
  | single_rule _ = error "Single rule expected";

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- Scan.repeat arg :|--
    (fn names => Scan.peek (fn context => Scan.succeed (names |> map (fn name =>
      (case get (Context.proof_of context) name of SOME x => x
      | NONE => error ("No rule for " ^ k ^ " " ^ quote name))))));

fun rule get_type get_set =
  named_rule typeN Args.tyname get_type ||
  named_rule setN Args.const get_set ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.thms;

val cases_rule = rule lookup_casesT lookup_casesS >> single_rule;
val induct_rule = rule lookup_inductT lookup_inductS;
val coinduct_rule = rule lookup_coinductT lookup_coinductS >> single_rule;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val def_inst =
  ((Scan.lift (Args.name --| (Args.$$$ "\\<equiv>" || Args.$$$ "==")) >> SOME)
      -- Args.term) >> SOME ||
    inst >> Option.map (pair NONE);

val free = Scan.state -- Args.term >> (fn (_, Free v) => v | (context, t) =>
  error ("Bad free variable: " ^ ProofContext.string_of_term (Context.proof_of context) t));

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ arbitraryN || Args.$$$ takingN || Args.$$$ typeN ||
    Args.$$$ setN || Args.$$$ ruleN) -- Args.colon)) scan;

val arbitrary = Scan.optional (Scan.lift (Args.$$$ arbitraryN -- Args.colon) |--
  Args.and_list1 (Scan.repeat (unless_more_args free))) [];

val taking = Scan.optional (Scan.lift (Args.$$$ takingN -- Args.colon) |--
  Scan.repeat1 (unless_more_args inst)) [];

in

fun cases_meth src =
  Method.syntax (Args.mode openN --
    (Args.and_list (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule)) src
  #> (fn ((is_open, (insts, opt_rule)), ctxt) =>
    Method.METHOD_CASES (fn facts =>
      Seq.DETERM (HEADGOAL (cases_tac ctxt is_open insts opt_rule facts))));

fun induct_meth src =
  Method.syntax (Args.mode openN --
    (Args.and_list (Scan.repeat (unless_more_args def_inst)) --
    (arbitrary -- taking -- Scan.option induct_rule))) src
  #> (fn ((is_open, (insts, ((arbitrary, taking), opt_rule))), ctxt) =>
    Method.RAW_METHOD_CASES (fn facts =>
      Seq.DETERM (HEADGOAL (induct_tac ctxt is_open insts arbitrary taking opt_rule facts))));

fun coinduct_meth src =
  Method.syntax (Args.mode openN --
    (Scan.repeat (unless_more_args inst) -- taking -- Scan.option coinduct_rule)) src
  #> (fn ((is_open, ((insts, taking), opt_rule)), ctxt) =>
    Method.RAW_METHOD_CASES (fn facts =>
      Seq.DETERM (HEADGOAL (coinduct_tac ctxt is_open insts taking opt_rule facts))));

end;



(** theory setup **)

val setup =
  attrib_setup #>
  Method.add_methods
    [(casesN, cases_meth, "case analysis on types or sets"),
     (inductN, induct_meth, "induction on types or sets"),
     (coinductN, coinduct_meth, "coinduction on types or sets")];

end;
