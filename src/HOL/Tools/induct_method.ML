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
  val rewrite_cterm: thm list -> cterm -> cterm
  val simp_case_tac: bool -> simpset -> int -> tactic
  val setup: (theory -> theory) list
end;

structure InductMethod: INDUCT_METHOD =
struct


(** theory context references **)

val inductive_atomize = thms "inductive_atomize";
val inductive_rulify1 = thms "inductive_rulify1";
val inductive_rulify2 = thms "inductive_rulify2";



(** misc utils **)

(* align lists *)

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (Library.take (n, xs) ~~ ys) end;

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (Library.drop (m - n, xs) ~~ ys) end;


(* thms and terms *)

fun imp_concl_of t = imp_concl_of (#2 (HOLogic.dest_imp t)) handle TERM _ => t;
val concls_of = map imp_concl_of o HOLogic.dest_conj o HOLogic.dest_Trueprop o Thm.concl_of;

fun vars_of tm =        (*ordered left-to-right, preferring right!*)
  Term.foldl_aterms (fn (ts, t as Var _) => t :: ts | (ts, _) => ts) ([], tm)
  |> Library.distinct |> rev;

fun type_name t =
  #1 (Term.dest_Type (Term.type_of t))
    handle TYPE _ => raise TERM ("Type of term argument is too general", [t]);

fun prep_inst align cert f (tm, ts) =
  let
    fun prep_var (x, Some t) =
          let
            val cx = cert x;
            val {T = xT, sign, ...} = Thm.rep_cterm cx;
            val orig_ct = cert t;
            val ct = f orig_ct;
          in
            if Sign.typ_instance sign (#T (Thm.rep_cterm ct), xT) then Some (cx, ct)
            else error (Pretty.string_of (Pretty.block
              [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
                Display.pretty_cterm orig_ct, Pretty.str " ::", Pretty.brk 1,
                Display.pretty_ctyp (#T (Thm.crep_cterm orig_ct))]))
          end
      | prep_var (_, None) = None;
  in
    align "Rule has fewer variables than instantiations given" (vars_of tm) ts
    |> mapfilter prep_var
  end;

fun rewrite_cterm rews =
  #2 o Thm.dest_comb o #prop o Thm.crep_thm o Simplifier.full_rewrite (HOL_basic_ss addsimps rews);


(* simplifying cases rules *)

local

(*delete needless equality assumptions*)
val refl_thin = prove_goal HOL.thy "!!P. a = a ==> P ==> P" (fn _ => [assume_tac 1]);
val elim_rls = [asm_rl, FalseE, refl_thin, conjE, exE, Pair_inject];
val elim_tac = REPEAT o Tactic.eresolve_tac elim_rls;

in

fun simp_case_tac solved ss i =
  EVERY' [elim_tac, asm_full_simp_tac ss, elim_tac, REPEAT o bound_hyp_subst_tac] i
  THEN_MAYBE (if solved then no_tac else all_tac);

end;


(* resolution and cases *)

local

fun gen_resolveq_tac tac rules i st =
  Seq.flat (Seq.map (fn rule => tac rule i st) rules);

in

fun resolveq_cases_tac make tac = gen_resolveq_tac (fn (rule, (cases, facts)) => fn i => fn st =>
  Seq.map (rpair (make rule cases))
    ((Method.insert_tac facts THEN' tac THEN' Tactic.rtac rule) i st));

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
        |> (flat o map (prep_inst align_left cert I))
        |> Drule.cterm_instantiate) thm;

    fun find_cases th =
      NetRules.may_unify (#2 (InductAttrib.get_cases ctxt))
        (Logic.strip_assums_concl (#prop (Thm.rep_thm th)));

    val rules =
      (case (fst args, facts) of
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
      | ((insts, Some thm), _) => [(inst_rule insts thm, RuleCases.get thm)])
      |> map (Library.apfst (Attrib.read_inst' (snd args) ctxt));

    val cond_simp = if simplified then simplified_cases ctxt else rpair;

    fun prep_rule (thm, (cases, n)) = Seq.map (apsnd (rpair (drop (n, facts))) o cond_simp cases)
      (Method.multi_resolves (take (n, facts)) [thm]);
  in
    resolveq_cases_tac (RuleCases.make open_parms) (K all_tac)
      (Seq.flat (Seq.map prep_rule (Seq.of_list rules)))
  end;

in

val cases_meth = Method.METHOD_CASES o (HEADGOAL oo cases_tac);

end;



(** induct method **)

(*
  rule selection:
        induct x       - datatype induction
  <x:A> induct ...     - set induction
  ...   induct ... R   - explicit rule
*)

local

val atomize_cterm = Thm.cterm_fun AutoBind.drop_judgment o rewrite_cterm inductive_atomize;
val atomize_tac = Tactic.rewrite_goal_tac inductive_atomize;
val rulify_cterm = rewrite_cterm inductive_rulify2 o rewrite_cterm inductive_rulify1;

val rulify_tac =
  Tactic.rewrite_goal_tac inductive_rulify1 THEN'
  Tactic.rewrite_goal_tac inductive_rulify2 THEN'
  Tactic.norm_hhf_tac;

fun rulify_cases cert =
  let
    val ruly = Thm.term_of o rulify_cterm o cert;
    fun ruly_case {fixes, assumes, binds} =
      {fixes = fixes, assumes = map ruly assumes,
        binds = map (apsnd (apsome (AutoBind.drop_judgment o ruly))) binds};
  in map (apsnd ruly_case) ooo RuleCases.make_raw end;

val weak_strip_tac = REPEAT o Tactic.match_tac [impI, allI, ballI];


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
        |> (flat o map (prep_inst align_right cert atomize_cterm))
        |> Drule.cterm_instantiate) thm;

    fun find_induct th =
      NetRules.may_unify (#2 (InductAttrib.get_induct ctxt))
        (Logic.strip_assums_concl (#prop (Thm.rep_thm th)));

    val rules =
      (case (fst args, facts) of
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
      | ((insts, Some thm), _) => [(inst_rule insts thm, RuleCases.get thm)])
      |> map (Library.apfst (Attrib.read_inst' (snd args) ctxt));

    fun prep_rule (thm, (cases, n)) =
      Seq.map (rpair (cases, drop (n, facts))) (Method.multi_resolves (take (n, facts)) [thm]);
    val tac = resolveq_cases_tac (rulify_cases cert open_parms) atomize_tac
      (Seq.flat (Seq.map prep_rule (Seq.of_list rules)));
  in
    tac THEN_ALL_NEW_CASES (rulify_tac THEN' (if stripped then weak_strip_tac else K all_tac))
  end;

in

val induct_meth = Method.METHOD_CASES o (HEADGOAL oo induct_tac);

end;



(** concrete syntax **)

val simplifiedN = "simplified";
val strippedN = "stripped";
val openN = "open";
val ruleN = "rule";
val ofN = "of";

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

val kind_inst =
  (Args.$$$ InductAttrib.typeN || Args.$$$ InductAttrib.setN || Args.$$$ ruleN || Args.$$$ ofN)
    -- Args.colon;
val term = Scan.unless (Scan.lift kind_inst) Args.local_term;
val term_dummy = Scan.unless (Scan.lift kind_inst)
  (Scan.lift (Args.$$$ "_") >> K None || Args.local_term >> Some);

val instss = Args.and_list (Scan.repeat1 term_dummy);

(* FIXME Attrib.insts': better use actual term args *)
val rule_insts =
  Scan.lift (Scan.optional ((Args.$$$ ofN -- Args.colon) |-- Args.!!! Attrib.insts') ([], []));

in

val cases_args = Method.syntax
  (Args.mode simplifiedN -- Args.mode openN -- (instss -- Scan.option cases_rule -- rule_insts));

val induct_args = Method.syntax
  (Args.mode strippedN -- Args.mode openN -- (instss -- Scan.option induct_rule -- rule_insts));

end;



(** theory setup **)

val setup =
  [Method.add_methods
    [(InductAttrib.casesN, cases_meth oo cases_args, "case analysis on types or sets"),
     (InductAttrib.inductN, induct_meth oo induct_args, "induction on types or sets")],
   (#1 o PureThy.add_thms [(("case_split", case_split), [])])];

end;
