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
  val conjI: thm
  val atomize: thm list
  val rulify1: thm list
  val rulify2: thm list
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


(* tactics with cases *)

fun resolveq_cases_tac make tac ruleq i st =
  ruleq |> Seq.map (fn (rule, (cases, facts)) =>
    (Method.insert_tac facts THEN' tac THEN' Tactic.rtac rule) i st
    |> Seq.map (rpair (make rule cases)))
  |> Seq.flat;


infix 1 THEN_ALL_NEW_CASES;

fun (tac1 THEN_ALL_NEW_CASES tac2) i st =
  st |> Seq.THEN (tac1 i, (fn (st', cases) =>
    Seq.map (rpair cases) (Seq.INTERVAL tac2 i (i + nprems_of st' - nprems_of st) st')));



(** cases method **)

(*
  rule selection scheme:
          cases         - classical case split
    <x:A> cases ...     - set cases
          cases t       - type cases
    ...   cases ... R   - explicit rule
*)

local

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
            Method.trace rules;
            Seq.flat (Seq.map (Seq.try inst_rule) (Seq.of_list rules))
          end
      | (_, _, Some r) => Seq.single (inst_rule r));

    fun prep_rule (th, (cases, n)) = Seq.map (apsnd (rpair (drop (n, facts))) o rpair cases)
      (Method.multi_resolves (take (n, facts)) [th]);
  in
    resolveq_cases_tac (RuleCases.make open_parms) (K all_tac)
      (Seq.flat (Seq.map prep_rule ruleq))
  end;

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

fun atomize_cterm ct =
  Thm.cterm_fun (ObjectLogic.drop_judgment (#sign (Thm.rep_cterm ct)))
    (Tactic.rewrite_cterm true Data.atomize ct);

val atomize_tac = Tactic.rewrite_goal_tac Data.atomize;
val rulify_cterm = Tactic.rewrite_cterm true Data.rulify2 o Tactic.rewrite_cterm true Data.rulify1;

val rulify_tac =
  Tactic.rewrite_goal_tac Data.rulify1 THEN'
  Tactic.rewrite_goal_tac Data.rulify2 THEN'
  Tactic.norm_hhf_tac;

fun rulify_cases sg cert =
  let
    val ruly = Thm.term_of o rulify_cterm o cert;
    fun ruly_case {fixes, assumes, binds} =
      {fixes = fixes, assumes = map ruly assumes,
        binds = map (apsnd (apsome (ObjectLogic.drop_judgment sg o ruly))) binds};
  in map (apsnd ruly_case) ooo RuleCases.make_raw end;


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

fun find_inductT ctxt insts =
  foldr multiply (insts |> mapfilter (fn [] => None | ts => last_elem ts)
    |> map (InductAttrib.find_inductT ctxt o fastype_of), [[]])
  |> map join_rules |> flat;

fun find_inductS ctxt (fact :: _) = InductAttrib.find_inductS ctxt fact
  | find_inductS _ _ = [];

fun induct_tac (ctxt, (open_parms, (insts, opt_rule))) facts =
  let
    val sg = ProofContext.sign_of ctxt;
    val cert = Thm.cterm_of sg;

    fun inst_rule r =
      if null insts then RuleCases.add r
      else (align_right "Rule has fewer conclusions than arguments given"
          (Data.dest_concls (Thm.concl_of r)) insts
        |> (flat o map (prep_inst align_right cert atomize_cterm))
        |> Drule.cterm_instantiate) r |> rpair (RuleCases.get r);

    val ruleq =
      (case opt_rule of
        None =>
          let val rules = find_inductS ctxt facts @ find_inductT ctxt insts in
            if null rules then error "Unable to figure out induct rule" else ();
            Method.trace rules;
            Seq.flat (Seq.map (Seq.try inst_rule) (Seq.of_list rules))
          end
      | Some r => Seq.single (inst_rule r));

    (* FIXME divinate rule_inst *)

    fun prep_rule (th, (cases, n)) =
      Seq.map (rpair (cases, drop (n, facts))) (Method.multi_resolves (take (n, facts)) [th]);
    val tac = resolveq_cases_tac (rulify_cases sg cert open_parms) atomize_tac
      (Seq.flat (Seq.map prep_rule ruleq));
  in tac THEN_ALL_NEW_CASES rulify_tac end;

in

val induct_meth = Method.METHOD_CASES o (HEADGOAL oo induct_tac);

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
