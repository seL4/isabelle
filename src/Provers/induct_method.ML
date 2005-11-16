(*  Title:      Provers/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof by cases and induction on sets and types.
*)

signature INDUCT_METHOD_DATA =
sig
  val dest_concls: term -> term list
  val cases_default: thm
  val local_impI: thm
  val conjI: thm
  val atomize: thm list
  val rulify1: thm list
  val rulify2: thm list
  val localize: thm list
end;

signature INDUCT_METHOD =
sig
  val cases_tac: Proof.context -> bool -> term option list list -> thm option ->
    thm list -> int -> RuleCases.tactic
  val fix_tac: Proof.context -> (string * typ) list -> int -> tactic
  val induct_tac: Proof.context -> bool -> (string option * term) option list list ->
    thm option -> (string * typ) list -> thm list -> int -> RuleCases.tactic
  val setup: (theory -> theory) list
end;

functor InductMethodFun(Data: INDUCT_METHOD_DATA): INDUCT_METHOD =
struct


(** misc utils **)

(* align lists *)

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then raise ERROR_MESSAGE msg else (Library.take (n, xs) ~~ ys) end;

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then raise ERROR_MESSAGE msg else (Library.drop (m - n, xs) ~~ ys) end;


(* prep_inst *)

fun prep_inst align cert tune (tm, ts) =
  let
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


(* warn_open *)

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

fun find_casesS ctxt (fact :: _) = InductAttrib.find_casesS ctxt fact
  | find_casesS _ _ = [];

in

fun cases_tac ctxt is_open insts opt_rule facts =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    fun inst_rule r =
      if null insts then RuleCases.add r
      else (align_left "Rule has fewer premises than arguments given" (Thm.prems_of r) insts
        |> (List.concat o map (prep_inst align_left cert I))
        |> Drule.cterm_instantiate) r |> rpair (RuleCases.get r);

    val ruleq =
      (case opt_rule of
        NONE =>
          let val rules = find_casesS ctxt facts @ find_casesT ctxt insts @ [Data.cases_default] in
            Method.trace ctxt rules;
            Seq.maps (Seq.try inst_rule) (Seq.of_list rules)
          end
      | SOME r => Seq.single (inst_rule r));
    val ruleq_cases = ruleq |> Seq.maps (fn (th, (cases, n)) =>
      Method.multi_resolves (Library.take (n, facts)) [th]
      |> Seq.map (apsnd (rpair (Library.drop (n, facts))) o rpair cases));

    fun make_cases rule = RuleCases.make (tap warn_open is_open) NONE (thy, Thm.prop_of rule);
  in
    fn i => fn st =>
      ruleq_cases |> Seq.maps (fn (rule, (cases, facts)) =>
        (Method.insert_tac facts THEN' Tactic.rtac rule) i st
        |> Seq.map (rpair (make_cases rule cases)))
  end;

val cases_meth = Method.METHOD_CASES o ((Seq.DETERM o HEADGOAL) oo
  (fn (ctxt, (is_open, (insts, opt_rule))) => cases_tac ctxt is_open insts opt_rule));

end;



(** induct method **)

(* fixes *)

local

val meta_spec = PureThy.get_thm Pure.thy (Name "meta_spec");

fun meta_spec_tac ctxt (x, T) i st = SUBGOAL (fn (goal, _) =>
  let
    val thy = Thm.theory_of_thm st;
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;

    val v = Free (x, T);
    val _ = Term.exists_subterm (fn t => t aconv v) goal orelse
      error ("No variable " ^ ProofContext.string_of_term ctxt v ^ " in subgoal");
    val P = Term.absfree (x, T, goal);
    val rule = meta_spec
      |> Drule.instantiate' [SOME (certT T)] [SOME (cert P), SOME (cert v)]
      |> Thm.rename_params_rule ([x], 1);
  in compose_tac (false, rule, 1) end i) i st;

in

fun fix_tac ctxt fixes =
  (case gen_duplicates (op =) fixes of
    [] => EVERY' (map (meta_spec_tac ctxt) (rev fixes))
  | dups => error ("Duplicate specification of variable(s): " ^
      commas (map (ProofContext.string_of_term ctxt o Free) dups)));

end;


(* defs *)

fun add_defs def_insts =
  let
    fun add (SOME (SOME x, t)) ctxt =
          let val ((lhs, def), ctxt') = ProofContext.add_def (x, t) ctxt
          in ((SOME (Free lhs), [def]), ctxt') end
      | add (SOME (NONE, t)) ctxt = ((SOME t, []), ctxt)
      | add NONE ctxt = ((NONE, []), ctxt);
  in fold_map add def_insts #> apfst (split_list #> apsnd List.concat) end;


(* atomize and rulify *)

fun atomize_term thy =
  ObjectLogic.drop_judgment thy o MetaSimplifier.rewrite_term thy Data.atomize [];

fun rulified_term thm =
  let val thy = Thm.theory_of_thm thm in
    Thm.prop_of thm
    |> MetaSimplifier.rewrite_term thy Data.rulify1 []
    |> MetaSimplifier.rewrite_term thy Data.rulify2 []
    |> pair thy
  end;

val atomize_tac = Tactic.rewrite_goal_tac Data.atomize;

val rulify_tac =
  Tactic.rewrite_goal_tac Data.rulify1 THEN'
  Tactic.rewrite_goal_tac Data.rulify2 THEN'
  Tactic.norm_hhf_tac;

val localize = Goal.norm_hhf o Tactic.simplify false Data.localize;


(* internalize implications -- limited to atomic prems *)

local

fun imp_intr i raw_th =
  let
    val th = Thm.permute_prems (i - 1) 1 raw_th;
    val {thy, maxidx, ...} = Thm.rep_thm th;
    val cprems = Drule.cprems_of th;
    val As = Library.take (length cprems - 1, cprems);
    val C = Thm.cterm_of thy (Var (("C", maxidx + 1), propT));
  in th COMP Thm.lift_rule (Drule.list_implies (As, C)) Data.local_impI end;

in

fun internalize k th = if k > 0 then internalize (k - 1) (imp_intr k th) else th;

end;


(* join multi-rules *)

val eq_prems = curry (Term.aconvs o pairself Thm.prems_of);

fun join_rules [] = []
  | join_rules [th] = [th]
  | join_rules (rules as r :: rs) =
      if not (forall (eq_prems r) rs) then []
      else
        let
          val th :: ths = map Drule.freeze_all rules;
          val cprems = Drule.cprems_of th;
          val asms = map Thm.assume cprems;
        in
          [foldr1 (fn (x, x') => [x, x'] MRS Data.conjI)
            (map (fn x => Drule.implies_elim_list x asms) (th :: ths))
          |> Drule.implies_intr_list cprems
          |> Drule.standard'
          |> RuleCases.save r]
        end;


(* divinate rule instantiation -- cannot handle pending goal parameters *)

fun dest_env thy (env as Envir.Envir {iTs, ...}) =
  let
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;
    val pairs = Envir.alist_of env;
    val ts = map (cert o Envir.norm_term env o #2 o #2) pairs;
    val xs = map2 (cert o Var) (map #1 pairs, map (#T o Thm.rep_cterm) ts);
  in (map (fn (xi, (S, T)) => (certT (TVar (xi, S)), certT T)) (Vartab.dest iTs), xs ~~ ts) end;

fun divinate_inst rule i st =
  let
    val {thy, maxidx, ...} = Thm.rep_thm st;
    val goal = Thm.term_of (Thm.cprem_of st i);  (*exception Subscript*)
    val params = rev (rename_wrt_term goal (Logic.strip_params goal));  (*as they are printed :-*)
  in
    if not (null params) then
      (warning ("Cannot determine rule instantiation due to pending parameter(s): " ^
        commas (map (Sign.string_of_term thy o Syntax.mark_boundT) params));
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


(* special renaming of rule parameters *)

fun special_rename_params ctxt [[SOME (Free (z, Type (T, _)))]] thm =
      let
        val x = the_default z (ProofContext.revert_skolem ctxt z);
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
      in RuleCases.save thm thm' end
  | special_rename_params _ _ thm = thm;


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
    |> map (InductAttrib.find_inductT ctxt o fastype_of)) [[]]
  |> map join_rules |> List.concat;

fun find_inductS ctxt (fact :: _) = InductAttrib.find_inductS ctxt fact
  | find_inductS _ _ = [];

in

fun induct_tac ctxt is_open def_insts opt_rule fixes facts =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val ((insts, defs), defs_ctxt) = fold_map add_defs def_insts ctxt |>> split_list;

    fun rule_versions r = Seq.cons (r, Seq.filter (not o curry Thm.eq_thm r)
        (Seq.make (fn () => SOME (localize r, Seq.empty))))
      |> Seq.map (rpair (RuleCases.get r));

    val inst_rule = apfst (fn r =>
      if null insts then r
      else (align_right "Rule has fewer conclusions than arguments given"
          (Data.dest_concls (Thm.concl_of r)) insts
        |> (List.concat o map (prep_inst align_right cert (atomize_term thy)))
        |> Drule.cterm_instantiate) r);

    val ruleq =
      (case opt_rule of
        NONE =>
          let val rules = find_inductS ctxt facts @
            map (special_rename_params defs_ctxt insts) (find_inductT ctxt insts)
          in
            conditional (null rules) (fn () => error "Unable to figure out induct rule");
            Method.trace ctxt rules;
            rules |> Seq.of_list |> Seq.maps rule_versions |> Seq.maps (Seq.try inst_rule)
          end
      | SOME r => r |> rule_versions |> Seq.map inst_rule);
    val ruleq_cases = ruleq |> Seq.maps (fn (th, (cases, n)) =>
      Method.multi_resolves (Library.take (n, facts)) [th]
      |> Seq.map (rpair (cases, n - length facts, Library.drop (n, facts))));

    fun make_cases rule =
      RuleCases.make (tap warn_open is_open) (SOME (Thm.prop_of rule)) (rulified_term rule);
  in
    (fn i => fn st => ruleq_cases |> Seq.maps (fn (rule, (cases, k, more_facts)) =>
      (Method.insert_tac (List.concat defs @ more_facts)  (* FIXME CONJUNCTS *)
        THEN' fix_tac defs_ctxt fixes
        THEN' atomize_tac) i st |> Seq.maps (fn st' =>
        divinate_inst (internalize k rule) i st' |> Seq.maps (fn rule' =>
          Tactic.rtac rule' i st'
          |> Seq.maps (ProofContext.exports defs_ctxt ctxt)
          |> Seq.map (rpair (make_cases rule' cases))))))
    THEN_ALL_NEW_CASES rulify_tac
  end;

val induct_meth = Method.RAW_METHOD_CASES o ((Seq.DETERM o HEADGOAL) oo
  (fn (ctxt, (is_open, (insts, (opt_rule, fixes)))) =>
    induct_tac ctxt is_open insts opt_rule fixes));

end;



(** concrete syntax **)

val openN = "open";
val ruleN = "rule";
val ofN = "of";
val fixingN = "fixing";

local

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- arg :-- (fn name => Scan.peek (fn ctxt =>
    (case get ctxt name of SOME x => Scan.succeed x
    | NONE => error ("No rule for " ^ k ^ " " ^ quote name)))) >> #2;

fun rule get_type get_set =
  named_rule InductAttrib.typeN Args.local_tyname get_type ||
  named_rule InductAttrib.setN Args.local_const get_set ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.local_thm;

val cases_rule = rule InductAttrib.lookup_casesT InductAttrib.lookup_casesS;
val induct_rule = rule InductAttrib.lookup_inductT InductAttrib.lookup_inductS;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.local_term >> SOME;

val def_inst =
  ((Scan.lift (Args.name --| (Args.$$$ "\\<equiv>" || Args.$$$ "==")) >> SOME)
      -- Args.local_term) >> SOME ||
    inst >> Option.map (pair NONE);

val free = Scan.state -- Args.local_term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ ProofContext.string_of_term ctxt t));
val fixing = Scan.optional (Scan.lift (Args.$$$ fixingN -- Args.colon) |-- Scan.repeat1 free) [];

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ InductAttrib.typeN || Args.$$$ InductAttrib.setN || Args.$$$ ruleN ||
    Args.$$$ ofN || Args.$$$ fixingN) -- Args.colon)) scan;

in

val cases_args = Method.syntax (Args.mode openN --
  (Args.and_list (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule));

val induct_args = Method.syntax (Args.mode openN --
  (Args.and_list (Scan.repeat (unless_more_args def_inst)) --
  (Scan.option induct_rule -- fixing)));

end;



(** theory setup **)

val setup =
  [Method.add_methods
    [(InductAttrib.casesN, cases_meth oo cases_args, "case analysis on types or sets"),
     (InductAttrib.inductN, induct_meth oo induct_args, "induction on types or sets")]];

end;
