(*  Title:      Provers/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof by cases and induction on sets and types.
*)

signature INDUCT_METHOD_DATA =
sig
  val cases_default: thm
  val atomize: thm list
  val rulify: thm list
  val rulify_fallback: thm list
end;

signature INDUCT_METHOD =
sig
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
  val setup: (theory -> theory) list
end;

functor InductMethodFun(Data: INDUCT_METHOD_DATA): INDUCT_METHOD =
struct

val meta_spec = thm "Pure.meta_spec";
val all_conjunction = thm "Pure.all_conjunction";
val imp_conjunction = thm "Pure.imp_conjunction";
val conjunction_imp = thm "Pure.conjunction_imp";
val conjunction_assoc = thm "Pure.conjunction_assoc";
val conjunction_congs = [all_conjunction, imp_conjunction];



(** misc utils **)

(* alignment *)

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then raise ERROR_MESSAGE msg else (Library.take (n, xs) ~~ ys) end;

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then raise ERROR_MESSAGE msg else (Library.drop (m - n, xs) ~~ ys) end;


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
            else raise ERROR_MESSAGE (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Display.pretty_cterm ct, Pretty.str " ::", Pretty.brk 1,
              Display.pretty_ctyp (#T (Thm.crep_cterm ct))]))
          end
      | prep_var (_, NONE) = NONE;
    val xs = InductAttrib.vars_of tm;
  in
    align "Rule has fewer variables than instantiations given" xs ts
    |> List.mapPartial prep_var
  end;


(* trace_rules *)

fun trace_rules _ kind [] = error ("Unable to figure out " ^ kind ^ " rule")
  | trace_rules ctxt _ rules = Method.trace ctxt rules;


(* make_cases *)

fun make_cases is_open rule =
  RuleCases.make_common is_open (Thm.theory_of_thm rule, Thm.prop_of rule);

fun warn_open true = warning "Encountered open rule cases -- deprecated"
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

fun find_casesT ctxt ((SOME t :: _) :: _) = InductAttrib.find_casesT ctxt (Term.fastype_of t)
  | find_casesT _ _ = [];

fun find_casesS ctxt (fact :: _) = InductAttrib.find_casesS ctxt (Thm.concl_of fact)
  | find_casesS _ _ = [];

in

fun cases_tac ctxt is_open insts opt_rule facts =
  let
    val _ = warn_open is_open;
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    fun inst_rule r =
      if null insts then `RuleCases.get r
      else (align_left "Rule has fewer premises than arguments given" (Thm.prems_of r) insts
        |> (List.concat o map (prep_inst thy align_left I))
        |> Drule.cterm_instantiate) r |> pair (RuleCases.get r);

    val ruleq =
      (case opt_rule of
        SOME r => Seq.single (inst_rule r)
      | NONE =>
          (find_casesS ctxt facts @ find_casesT ctxt insts @ [Data.cases_default])
          |> tap (trace_rules ctxt InductAttrib.casesN)
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

(* atomize *)

fun atomize_term thy =
  MetaSimplifier.rewrite_term thy Data.atomize []
  #> ObjectLogic.drop_judgment thy;

val atomize_cterm = Tactic.rewrite true Data.atomize;

val atomize_tac = Tactic.rewrite_goal_tac Data.atomize;

val inner_atomize_tac =
  Tactic.rewrite_goal_tac (map Thm.symmetric conjunction_congs) THEN' atomize_tac;


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

val curry_prems_tac =
  let
    val rule = conjunction_imp;
    val thy = Thm.theory_of_thm rule;
    val proc = Simplifier.simproc_i thy "curry_prems"
      [#1 (Logic.dest_equals (Thm.prop_of rule))]
      (fn _ => fn ss => fn _ =>  (*WORKAROUND: prevent descending into meta conjunctions*)
        if exists (equal propT o #2 o #1) (#2 (#bounds (#1 (Simplifier.rep_ss ss))))
        then NONE else SOME rule);
    val ss = MetaSimplifier.theory_context thy Simplifier.empty_ss addsimprocs [proc];
  in Simplifier.full_simp_tac ss end;

val rulify_tac =
  Tactic.rewrite_goal_tac (Data.rulify @ conjunction_congs) THEN'
  Tactic.rewrite_goal_tac Data.rulify_fallback THEN'
  Tactic.conjunction_tac THEN_ALL_NEW
  (curry_prems_tac THEN' Tactic.norm_hhf_tac);


(* prepare rule *)

fun rule_instance thy inst rule =
  Drule.cterm_instantiate (prep_inst thy align_left I (Thm.prop_of rule, inst)) rule;

fun internalize k th =
  th |> Thm.permute_prems 0 k
  |> Drule.fconv_rule (Drule.concl_conv (Thm.nprems_of th - k) atomize_cterm);


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
        Unify.smash_unifiers (thy, Envir.empty (#maxidx (Thm.rep_thm rule')),
          [(Thm.concl_of rule', concl)])
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
      meta_spec
      |> Thm.rename_params_rule ([ProofContext.revert_skolem ctxt x], 1)
      |> Thm.lift_rule (cert prfx)
      |> `(Thm.prop_of #> Logic.strip_assums_concl)
      |-> (fn pred $ arg =>
        Drule.cterm_instantiate
          [(cert (Term.head_of pred), cert (Unify.rlist_abs (xs, body))),
           (cert (Term.head_of arg), cert (Unify.rlist_abs (xs, v)))]);

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
    | NONE => (warning ("Induction: no variable " ^ quote (ProofContext.string_of_term ctxt v) ^
        " to be fixed -- ignored"); all_tac))
  end);

fun miniscope_tac p i = PRIMITIVE (Drule.fconv_rule
  (Drule.goals_conv (Library.equal i)
    (Drule.forall_conv p (Tactic.rewrite true [Thm.symmetric Drule.norm_hhf_eq]))));

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
          let val ((lhs, def), ctxt') = ProofContext.add_def (x, t) ctxt
          in ((SOME (Free lhs), [def]), ctxt') end
      | add (SOME (NONE, t)) ctxt = ((SOME t, []), ctxt)
      | add NONE ctxt = ((NONE, []), ctxt);
  in fold_map add def_insts #> apfst (split_list #> apsnd List.concat) end;


(* induct_tac *)

(*
  rule selection scheme:
    `x:A` induct ...     - set induction
          induct x       - type induction
    ...   induct ... r   - explicit rule
*)

local

fun find_inductT ctxt insts =
  fold_rev multiply (insts |> List.mapPartial (fn [] => NONE | ts => List.last ts)
    |> map (InductAttrib.find_inductT ctxt o Term.fastype_of)) [[]]
  |> filter_out (forall Drule.is_internal);

fun find_inductS ctxt (fact :: _) = map single (InductAttrib.find_inductS ctxt (Thm.concl_of fact))
  | find_inductS _ _ = [];

in

fun induct_tac ctxt is_open def_insts fixing taking opt_rule facts =
  let
    val _ = warn_open is_open;
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val ((insts, defs), defs_ctxt) = fold_map add_defs def_insts ctxt |>> split_list;
    val atomized_defs = map (map ObjectLogic.atomize_thm) defs;

    fun inst_rule (concls, r) =
      (if null insts then `RuleCases.get r
       else (align_left "Rule has fewer conclusions than arguments given"
          (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
        |> (List.concat o map (prep_inst thy align_right (atomize_term thy)))
        |> Drule.cterm_instantiate) r |> pair (RuleCases.get r))
      |> (fn ((cases, consumes), th) => (((cases, concls), consumes), th));

    val ruleq =
      (case opt_rule of
        SOME rs => Seq.single (inst_rule (RuleCases.strict_mutual_rule rs))
      | NONE =>
          (find_inductS ctxt facts @
            map (special_rename_params defs_ctxt insts) (find_inductT ctxt insts))
          |> List.mapPartial RuleCases.mutual_rule
          |> tap (trace_rules ctxt InductAttrib.inductN o map #2)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));

    fun rule_cases rule =
      RuleCases.make_nested is_open (Thm.prop_of rule) (rulified_term rule);
  in
    (fn i => fn st =>
      ruleq
      |> Seq.maps (RuleCases.consume (List.concat defs) facts)
      |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
          (CONJUNCTS (ALLGOALS
            (Method.insert_tac (more_facts @ nth_list atomized_defs (j - 1))
              THEN' fix_tac defs_ctxt
                (nth concls (j - 1) + more_consumes)
                (nth_list fixing (j - 1))))
          THEN' inner_atomize_tac) j))
        THEN' atomize_tac) i st |> Seq.maps (fn st' =>
            guess_instance (internalize more_consumes rule) i st'
            |> Seq.map (rule_instance thy taking)
            |> Seq.maps (fn rule' =>
              CASES (rule_cases rule' cases)
                (Tactic.rtac rule' i THEN
                  PRIMSEQ (ProofContext.exports defs_ctxt ctxt)) st'))))
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

fun find_coinductT ctxt (SOME t :: _) = InductAttrib.find_coinductT ctxt (Term.fastype_of t)
  | find_coinductT _ _ = [];

fun find_coinductS ctxt goal = InductAttrib.find_coinductS ctxt (Logic.strip_assums_concl goal);

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
          (find_coinductS ctxt goal @ find_coinductT ctxt inst)
          |> tap (trace_rules ctxt InductAttrib.coinductN)
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
val fixingN = "fixing";
val takingN = "taking";
val ruleN = "rule";

local

fun single_rule [rule] = rule
  | single_rule _ = error "Single rule expected";

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- Scan.repeat arg :--
    (fn names => Scan.peek (fn ctxt => Scan.succeed (names |> map (fn name =>
      (case get ctxt name of SOME x => x
      | NONE => error ("No rule for " ^ k ^ " " ^ quote name)))))) >> #2;

fun rule get_type get_set =
  named_rule InductAttrib.typeN Args.local_tyname get_type ||
  named_rule InductAttrib.setN Args.local_const get_set ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.local_thmss;

val cases_rule = rule InductAttrib.lookup_casesT InductAttrib.lookup_casesS >> single_rule;
val induct_rule = rule InductAttrib.lookup_inductT InductAttrib.lookup_inductS;
val coinduct_rule =
  rule InductAttrib.lookup_coinductT InductAttrib.lookup_coinductS >> single_rule;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.local_term >> SOME;

val def_inst =
  ((Scan.lift (Args.name --| (Args.$$$ "\\<equiv>" || Args.$$$ "==")) >> SOME)
      -- Args.local_term) >> SOME ||
    inst >> Option.map (pair NONE);

val free = Scan.state -- Args.local_term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ ProofContext.string_of_term ctxt t));

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ fixingN || Args.$$$ takingN || Args.$$$ InductAttrib.typeN ||
    Args.$$$ InductAttrib.setN || Args.$$$ ruleN) -- Args.colon)) scan;

val fixing = Scan.optional (Scan.lift (Args.$$$ fixingN -- Args.colon) |--
  Args.and_list1 (Scan.repeat (unless_more_args free))) [];

val taking = Scan.optional (Scan.lift (Args.$$$ takingN -- Args.colon) |--
  Scan.repeat1 (unless_more_args inst)) [];

in

fun cases_meth src =
  Method.syntax (Args.mode openN --
    (Args.and_list (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule)) src
  #> (fn (ctxt, (is_open, (insts, opt_rule))) =>
    Method.METHOD_CASES (fn facts =>
      Seq.DETERM (HEADGOAL (cases_tac ctxt is_open insts opt_rule facts))));

fun induct_meth src =
  Method.syntax (Args.mode openN --
    (Args.and_list (Scan.repeat (unless_more_args def_inst)) --
    (fixing -- taking -- Scan.option induct_rule))) src
  #> (fn (ctxt, (is_open, (insts, ((fixing, taking), opt_rule)))) =>
    Method.RAW_METHOD_CASES (fn facts =>
      Seq.DETERM (HEADGOAL (induct_tac ctxt is_open insts fixing taking opt_rule facts))));

fun coinduct_meth src =
  Method.syntax (Args.mode openN --
    (Scan.repeat (unless_more_args inst) -- taking -- Scan.option coinduct_rule)) src
  #> (fn (ctxt, (is_open, ((insts, taking), opt_rule))) =>
    Method.RAW_METHOD_CASES (fn facts =>
      Seq.DETERM (HEADGOAL (coinduct_tac ctxt is_open insts taking opt_rule facts))));

end;



(** theory setup **)

val setup =
  [Method.add_methods
    [(InductAttrib.casesN, cases_meth, "case analysis on types or sets"),
     (InductAttrib.inductN, induct_meth, "induction on types or sets"),
     (InductAttrib.coinductN, coinduct_meth, "coinduction on types or sets")]];

end;
