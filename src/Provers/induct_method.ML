(*  Title:      Provers/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

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
    fun prep_var (x, Some t) =
          let
            val cx = cert x;
            val {T = xT, sign, ...} = Thm.rep_cterm cx;
            val orig_ct = cert t;
            val ct = tune orig_ct;
          in
            if Sign.typ_instance sign (#T (Thm.rep_cterm ct), xT) then Some (cx, ct)
            else raise ERROR_MESSAGE (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Display.pretty_cterm ct, Pretty.str " ::", Pretty.brk 1,
              Display.pretty_ctyp (#T (Thm.crep_cterm ct))]))
          end
      | prep_var (_, None) = None;
    val xs = InductAttrib.vars_of tm;
  in
    align "Rule has fewer variables than instantiations given" xs ts
    |> mapfilter prep_var
  end;



(** cases method **)

(*
  rule selection scheme:
          cases         - classical case split
    <x:A> cases ...     - set cases
          cases t       - type cases
    ...   cases ... R   - explicit rule
*)

local

fun resolveq_cases_tac make ruleq i st =
  ruleq |> Seq.map (fn (rule, (cases, facts)) =>
    (Method.insert_tac facts THEN' Tactic.rtac rule) i st
    |> Seq.map (rpair (make rule cases)))
  |> Seq.flat;

fun find_casesT ctxt ((Some t :: _) :: _) = InductAttrib.find_casesT ctxt (fastype_of t)
  | find_casesT _ _ = [];

fun find_casesS ctxt (fact :: _) = InductAttrib.find_casesS ctxt fact
  | find_casesS _ _ = [];

fun cases_tac (ctxt, (open_parms, (insts, opt_rule))) facts =
  let
    val sg = ProofContext.sign_of ctxt;
    val cert = Thm.cterm_of sg;

    fun inst_rule r =
      if null insts then RuleCases.add r
      else (align_left "Rule has fewer premises than arguments given" (Thm.prems_of r) insts
        |> (flat o map (prep_inst align_left cert I))
        |> Drule.cterm_instantiate) r |> rpair (RuleCases.get r);

    val ruleq =
      (case (facts, insts, opt_rule) of
        ([], [], None) => Seq.single (RuleCases.add Data.cases_default)
      | (_, _, None) =>
          let val rules = find_casesS ctxt facts @ find_casesT ctxt insts in
            if null rules then error "Unable to figure out cases rule" else ();
            Method.trace ctxt rules;
            Seq.flat (Seq.map (Seq.try inst_rule) (Seq.of_list rules))
          end
      | (_, _, Some r) => Seq.single (inst_rule r));

    fun prep_rule (th, (cases, n)) = Seq.map (apsnd (rpair (drop (n, facts))) o rpair cases)
      (Method.multi_resolves (take (n, facts)) [th]);
  in resolveq_cases_tac (RuleCases.make open_parms) (Seq.flat (Seq.map prep_rule ruleq)) end;

in

val cases_meth = Method.METHOD_CASES o (HEADGOAL oo cases_tac);

end;



(** induct method **)

(*
  rule selection scheme:
    <x:A> induct ...     - set induction
          induct x       - type induction
    ...   induct ... R   - explicit rule
*)

local


(* atomize and rulify *)

fun atomize_cterm ct =
  Thm.cterm_fun (ObjectLogic.drop_judgment (#sign (Thm.rep_cterm ct)))
    (Tactic.rewrite_cterm true Data.atomize ct);

val atomize_tac = Tactic.rewrite_goal_tac Data.atomize;
val rulify = Tactic.simplify true Data.rulify2 o Tactic.simplify true Data.rulify1;

val rulify_tac =
  Tactic.rewrite_goal_tac Data.rulify1 THEN'
  Tactic.rewrite_goal_tac Data.rulify2 THEN'
  Tactic.norm_hhf_tac;

val localize = Tactic.norm_hhf o Tactic.simplify false Data.localize;


(* imp_intr --- limited to atomic prems *)

fun imp_intr i raw_th =
  let
    val th = Thm.permute_prems (i - 1) 1 raw_th;
    val cprems = Drule.cprems_of th;
    val As = take (length cprems - 1, cprems);
    val C = Thm.cterm_of (Thm.sign_of_thm th) (Var (("C", #maxidx (Thm.rep_thm th) + 1), propT));
    val dummy_st = Drule.mk_triv_goal (Drule.list_implies (As, C));
  in th COMP Thm.lift_rule (dummy_st, 1) Data.local_impI end;


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
          |> Drule.standard']
        end;


(* divinate rule instantiation (cannot handle pending goal parameters) *)

fun dest_env sign (env as Envir.Envir {asol, iTs, ...}) =
  let
    val pairs = Vartab.dest asol;
    val ts = map (Thm.cterm_of sign o Envir.norm_term env o #2) pairs;
    val xs = map2 (Thm.cterm_of sign o Var) (map #1 pairs, map (#T o Thm.rep_cterm) ts);
  in (map (apsnd (Thm.ctyp_of sign)) (Vartab.dest iTs), xs ~~ ts) end;

fun divinate_inst rule i st =
  let
    val {sign, maxidx, ...} = Thm.rep_thm st;
    val goal = List.nth (Thm.prems_of st, i - 1);  (*exception Subscript*)
    val params = rev (rename_wrt_term goal (Logic.strip_params goal));  (*as they are printed :-*)
  in
    if not (null params) then
      (warning ("Cannot determine rule instantiation due to pending parameter(s): " ^
        commas (map (Sign.string_of_term sign o Syntax.mark_boundT) params));
      Seq.single rule)
    else
      let
        val rule' = Thm.incr_indexes (maxidx + 1) rule;
        val concl = Logic.strip_assums_concl goal;
      in
        Unify.smash_unifiers (sign, Envir.empty (#maxidx (Thm.rep_thm rule')),
          [(Thm.concl_of rule', concl)])
        |> Seq.map (fn env => Drule.instantiate (dest_env sign env) rule')
      end
  end handle Subscript => Seq.empty;


(* compose tactics with cases *)

fun internalize k th = if k > 0 then internalize (k - 1) (imp_intr k th) else th;

fun resolveq_cases_tac' make ruleq i st =
  ruleq |> Seq.map (fn (rule, (cases, k, more_facts)) => st
    |> (Method.insert_tac more_facts THEN' atomize_tac) i
    |> Seq.map (fn st' => divinate_inst (internalize k rule) i st' |> Seq.map (fn rule' =>
          st' |> Tactic.rtac rule' i |> Seq.map (rpair (make (rulify rule') cases))) |> Seq.flat)
    |> Seq.flat)
  |> Seq.flat;

infix 1 THEN_ALL_NEW_CASES;

fun (tac1 THEN_ALL_NEW_CASES tac2) i st =
  st |> Seq.THEN (tac1 i, (fn (st', cases) =>
    Seq.map (rpair cases) (Seq.INTERVAL tac2 i (i + nprems_of st' - nprems_of st) st')));


(* find rules *)

fun find_inductT ctxt insts =
  foldr multiply (insts |> mapfilter (fn [] => None | ts => last_elem ts)
    |> map (InductAttrib.find_inductT ctxt o fastype_of), [[]])
  |> map join_rules |> flat;

fun find_inductS ctxt (fact :: _) = InductAttrib.find_inductS ctxt fact
  | find_inductS _ _ = [];


(* main tactic *)

fun induct_tac (ctxt, (open_parms, (insts, opt_rule))) facts =
  let
    val sg = ProofContext.sign_of ctxt;
    val cert = Thm.cterm_of sg;

    fun rule_versions r = Seq.cons (r, Seq.filter (not o curry eq_thm r)
        (Seq.make (fn () => Some (localize r, Seq.empty))))
      |> Seq.map (rpair (RuleCases.get r));

    val inst_rule = apfst (fn r =>
      if null insts then r
      else (align_right "Rule has fewer conclusions than arguments given"
          (Data.dest_concls (Thm.concl_of r)) insts
        |> (flat o map (prep_inst align_right cert atomize_cterm))
        |> Drule.cterm_instantiate) r);

    val ruleq =
      (case opt_rule of
        None =>
          let val rules = find_inductS ctxt facts @ find_inductT ctxt insts in
            conditional (null rules) (fn () => error "Unable to figure out induct rule");
            Method.trace ctxt rules;
            rules |> Seq.THEN (Seq.of_list, Seq.THEN (rule_versions, Seq.try inst_rule))
          end
      | Some r => r |> Seq.THEN (rule_versions, Seq.single o inst_rule));

    fun prep_rule (th, (cases, n)) =
      Seq.map (rpair (cases, n - length facts, drop (n, facts)))
        (Method.multi_resolves (take (n, facts)) [th]);
    val tac = resolveq_cases_tac' (RuleCases.make open_parms) (Seq.flat (Seq.map prep_rule ruleq));
  in tac THEN_ALL_NEW_CASES rulify_tac end;

in

val induct_meth = Method.RAW_METHOD_CASES o (HEADGOAL oo induct_tac);

end;



(** concrete syntax **)

val openN = "open";
val ruleN = "rule";
val ofN = "of";

local

fun check k get name =
  (case get name of Some x => x
  | None => error ("No rule for " ^ k ^ " " ^ quote name));

fun spec k = (Args.$$$ k -- Args.colon) |-- Args.!!! Args.name;

fun rule get_type get_set =
  Scan.depend (fn ctxt =>
    let val sg = ProofContext.sign_of ctxt in
      spec InductAttrib.typeN >> (check InductAttrib.typeN (get_type ctxt) o
        Sign.certify_tyname sg o Sign.intern_tycon sg) ||
      spec InductAttrib.setN >> (check InductAttrib.setN (get_set ctxt) o
        Sign.certify_const sg o Sign.intern_const sg)
    end >> pair ctxt) ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.local_thm;

val cases_rule = rule InductAttrib.lookup_casesT InductAttrib.lookup_casesS;
val induct_rule = rule InductAttrib.lookup_inductT InductAttrib.lookup_inductS;

val kind_inst =
  (Args.$$$ InductAttrib.typeN || Args.$$$ InductAttrib.setN || Args.$$$ ruleN || Args.$$$ ofN)
    -- Args.colon;
val term = Scan.unless (Scan.lift kind_inst) Args.local_term;
val term_dummy = Scan.unless (Scan.lift kind_inst)
  (Scan.lift (Args.$$$ "_") >> K None || Args.local_term >> Some);

val instss = Args.and_list (Scan.repeat1 term_dummy);

in

val cases_args = Method.syntax (Args.mode openN -- (instss -- Scan.option cases_rule));
val induct_args = Method.syntax (Args.mode openN -- (instss -- Scan.option induct_rule));

end;



(** theory setup **)

val setup =
  [Method.add_methods
    [(InductAttrib.casesN, cases_meth oo cases_args, "case analysis on types or sets"),
     (InductAttrib.inductN, induct_meth oo induct_args, "induction on types or sets")]];

end;
