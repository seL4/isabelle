(*  Title:      HOL/Tools/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Proof by cases and induction on types and sets.
*)

signature INDUCT_METHOD =
sig
  val vars_of: term -> term list
  val concls_of: thm -> term list
  val simp_case_tac: bool -> simpset -> int -> tactic
  val setup: (theory -> theory) list
end;

structure InductMethod: INDUCT_METHOD =
struct


(** misc utils **)

(* align lists *)

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (Library.take (n, xs) ~~ ys) end;

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (Library.drop (m - n, xs) ~~ ys) end;


(* thms and terms *)

val concls_of = HOLogic.dest_conj o HOLogic.dest_Trueprop o Thm.concl_of;

fun vars_of tm =        (*ordered left-to-right, preferring right!*)
  Term.foldl_aterms (fn (ts, t as Var _) => t :: ts | (ts, _) => ts) ([], tm)
  |> Library.distinct |> rev;

fun type_name t =
  #1 (Term.dest_Type (Term.type_of t))
    handle TYPE _ => raise TERM ("Type of term argument is too general", [t]);

fun prep_inst align cert (tm, ts) =
  let
    fun prep_var (x, Some t) = Some (cert x, cert t)
      | prep_var (_, None) = None;
  in
    align "Rule has fewer variables than instantiations given" (vars_of tm) ts
    |> mapfilter prep_var
  end;


(* simplifying cases rules *)

local

(*delete needless equality assumptions*)
val refl_thin = prove_goal HOL.thy "!!P. [| a=a;  P |] ==> P"
     (fn _ => [assume_tac 1]);

val elim_rls = [asm_rl, FalseE, refl_thin, conjE, exE, Pair_inject];

val elim_tac = REPEAT o Tactic.eresolve_tac elim_rls;

in

fun simp_case_tac solved ss i =
  EVERY' [elim_tac, asm_full_simp_tac ss, elim_tac, REPEAT o bound_hyp_subst_tac] i
  THEN_MAYBE (if solved then no_tac else all_tac);

end;



(** cases method **)

(*
  rule selection:
        cases         - classical case split
        cases t       - datatype exhaustion
  <x:A> cases ...     - set elimination
  ...   cases ... R   - explicit rule
*)

val case_split = RuleCases.name ["True", "False"] case_split_thm;

local

fun simplified_cases ctxt cases thm =
  let
    val nprems = Thm.nprems_of thm;
    val opt_cases =
      Library.replicate (nprems - Int.min (nprems, length cases)) None @
      map Some (Library.take (nprems, cases));

    val tac = simp_case_tac true (Simplifier.get_local_simpset ctxt);
    fun simp ((i, c), (th, cs)) =
      (case try (Tactic.rule_by_tactic (tac i)) th of
        None => (th, c :: cs)
      | Some th' => (th', None :: cs));

    val (thm', opt_cases') = foldr simp (1 upto Thm.nprems_of thm ~~ opt_cases, (thm, []));
  in (thm', mapfilter I opt_cases') end;

fun cases_tac (ctxt, ((simplified, open_parms), args)) facts =
  let
    val sg = ProofContext.sign_of ctxt;
    val cert = Thm.cterm_of sg;

    fun inst_rule insts thm =
      (align_left "Rule has fewer premises than arguments given" (Thm.prems_of thm) insts
        |> (flat o map (prep_inst align_left cert))
        |> Drule.cterm_instantiate) thm;

    fun find_cases th =
      NetRules.may_unify (#2 (InductAttrib.get_cases ctxt))
        (Logic.strip_assums_concl (#prop (Thm.rep_thm th)));

    val rules =
      (case (args, facts) of
        (([], None), []) => [RuleCases.add case_split]
      | ((insts, None), []) =>
          let
            val name = type_name (hd (flat (map (mapfilter I) insts)))
              handle Library.LIST _ => error "Unable to figure out type cases rule"
          in
            (case InductAttrib.lookup_casesT ctxt name of
              None => error ("No cases rule for type: " ^ quote name)
            | Some thm => [(inst_rule insts thm, RuleCases.get thm)])
          end
      | (([], None), th :: _) => map (RuleCases.add o #2) (find_cases th)
      | ((insts, None), th :: _) =>
          (case find_cases th of        (*may instantiate first rule only!*)
            (_, thm) :: _ => [(inst_rule insts thm, RuleCases.get thm)]
          | [] => [])
      | (([], Some thm), _) => [RuleCases.add thm]
      | ((insts, Some thm), _) => [(inst_rule insts thm, RuleCases.get thm)]);

    val cond_simp = if simplified then simplified_cases ctxt else rpair;

    fun prep_rule (thm, cases) =
      Seq.map (cond_simp cases) (Method.multi_resolves facts [thm]);
  in Method.resolveq_cases_tac open_parms (Seq.flat (Seq.map prep_rule (Seq.of_list rules))) end;

in

val cases_meth = Method.METHOD_CASES o (HEADGOAL oo cases_tac);

end;



(** induct method **)

(*
  rule selection:
        induct         - mathematical induction
        induct x       - datatype induction
  <x:A> induct ...     - set induction
  ...   induct ... R   - explicit rule
*)

local

infix 1 THEN_ALL_NEW_CASES;

fun (tac1 THEN_ALL_NEW_CASES tac2) i st =
  st |> Seq.THEN (tac1 i, (fn (st', cases) =>
    Seq.map (rpair cases) (Seq.INTERVAL tac2 i (i + nprems_of st' - nprems_of st) st')));


fun induct_rule ctxt t =
  let val name = type_name t in
    (case InductAttrib.lookup_inductT ctxt name of
      None => error ("No induct rule for type: " ^ quote name)
    | Some thm => (name, thm))
  end;

fun join_rules [(_, thm)] = thm
  | join_rules raw_thms =
      let
        val thms = (map (apsnd Drule.freeze_all) raw_thms);
        fun eq_prems ((_, th1), (_, th2)) =
          Term.aconvs (Thm.prems_of th1, Thm.prems_of th2);
      in
        (case Library.gen_distinct eq_prems thms of
          [(_, thm)] =>
            let
              val cprems = Drule.cprems_of thm;
              val asms = map Thm.assume cprems;
              fun strip (_, th) = Drule.implies_elim_list th asms;
            in
              foldr1 (fn (th, th') => [th, th'] MRS conjI) (map strip thms)
              |> Drule.implies_intr_list cprems
              |> Drule.standard
            end
        | [] => error "No rule given"
        | bads => error ("Incompatible rules for " ^ commas_quote (map #1 bads)))
      end;


fun induct_tac (ctxt, ((stripped, open_parms), args)) facts =
  let
    val sg = ProofContext.sign_of ctxt;
    val cert = Thm.cterm_of sg;

    fun inst_rule insts thm =
      (align_right "Rule has fewer conclusions than arguments given" (concls_of thm) insts
        |> (flat o map (prep_inst align_right cert))
        |> Drule.cterm_instantiate) thm;

    fun find_induct th =
      NetRules.may_unify (#2 (InductAttrib.get_induct ctxt))
        (Logic.strip_assums_concl (#prop (Thm.rep_thm th)));

    val rules =
      (case (args, facts) of
        (([], None), []) => []
      | ((insts, None), []) =>
          let val thms = map (induct_rule ctxt o last_elem o mapfilter I) insts
            handle Library.LIST _ => error "Unable to figure out type induction rule"
          in [(inst_rule insts (join_rules thms), RuleCases.get (#2 (hd thms)))] end
      | (([], None), th :: _) => map (RuleCases.add o #2) (find_induct th)
      | ((insts, None), th :: _) =>
          (case find_induct th of       (*may instantiate first rule only!*)
            (_, thm) :: _ => [(inst_rule insts thm, RuleCases.get thm)]
          | [] => [])
      | (([], Some thm), _) => [RuleCases.add thm]
      | ((insts, Some thm), _) => [(inst_rule insts thm, RuleCases.get thm)]);

    fun prep_rule (thm, cases) =
      Seq.map (rpair cases) (Method.multi_resolves facts [thm]);
    val tac = Method.resolveq_cases_tac open_parms
      (Seq.flat (Seq.map prep_rule (Seq.of_list rules)));
  in
    if stripped then tac THEN_ALL_NEW_CASES (REPEAT o Tactic.match_tac [impI, allI, ballI])
    else tac
  end;

in

val induct_meth = Method.METHOD_CASES o (HEADGOAL oo induct_tac);

end;



(** concrete syntax **)

val simplifiedN = "simplified";
val strippedN = "stripped";
val openN = "open";
val ruleN = "rule";

local

fun err k get name =
  (case get name of Some x => x
  | None => error ("No rule for " ^ k ^ " " ^ quote name));

fun spec k = (Args.$$$ k -- Args.colon) |-- Args.!!! Args.name;

fun rule get_type get_set =
  Scan.depend (fn ctxt =>
    let val sg = ProofContext.sign_of ctxt in
      spec InductAttrib.typeN >> (err InductAttrib.typeN (get_type ctxt) o Sign.intern_tycon sg) ||
      spec InductAttrib.setN >> (err InductAttrib.setN (get_set ctxt) o Sign.intern_const sg)
    end >> pair ctxt) ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.local_thm;

val cases_rule = rule InductAttrib.lookup_casesT InductAttrib.lookup_casesS;
val induct_rule = rule InductAttrib.lookup_inductT InductAttrib.lookup_inductS;

val kind =
  (Args.$$$ InductAttrib.typeN || Args.$$$ InductAttrib.setN || Args.$$$ ruleN) -- Args.colon;
val term = Scan.unless (Scan.lift kind) Args.local_term;
val term_dummy = Scan.unless (Scan.lift kind)
  (Scan.lift (Args.$$$ "_") >> K None || Args.local_term >> Some);

val instss = Args.and_list (Scan.repeat1 term_dummy);

in

val cases_args = Method.syntax
  (Args.mode simplifiedN -- Args.mode openN -- (instss -- Scan.option cases_rule));

val induct_args = Method.syntax
  (Args.mode strippedN -- Args.mode openN -- (instss -- Scan.option induct_rule));

end;



(** theory setup **)

val setup =
  [Method.add_methods
    [(InductAttrib.casesN, cases_meth oo cases_args, "case analysis on types or sets"),
     (InductAttrib.inductN, induct_meth oo induct_args, "induction on types or sets")],
   (#1 o PureThy.add_thms [(("case_split", case_split), [])])];

end;
