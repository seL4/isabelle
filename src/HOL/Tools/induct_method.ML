(*  Title:      HOL/Tools/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof by cases and induction on types and sets.
*)

signature INDUCT_METHOD =
sig
  val dest_global_rules: theory ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list}
  val print_global_rules: theory -> unit
  val dest_local_rules: Proof.context ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list}
  val print_local_rules: Proof.context -> unit
  val vars_of: term -> term list
  val cases_type_global: string -> theory attribute
  val cases_set_global: string -> theory attribute
  val cases_type_local: string -> Proof.context attribute
  val cases_set_local: string -> Proof.context attribute
  val induct_type_global: string -> theory attribute
  val induct_set_global: string -> theory attribute
  val induct_type_local: string -> Proof.context attribute
  val induct_set_local: string -> Proof.context attribute
  val con_elim_tac: simpset -> tactic
  val con_elim_solved_tac: simpset -> tactic
  val setup: (theory -> theory) list
end;

structure InductMethod: INDUCT_METHOD =
struct


(** global and local induct data **)

(* rules *)

type rules = (string * thm) NetRules.T;

fun eq_rule ((s1:string, th1), (s2, th2)) = s1 = s2 andalso Thm.eq_thm (th1, th2);

val type_rules = NetRules.init eq_rule (Thm.concl_of o #2);
val set_rules = NetRules.init eq_rule (Thm.major_prem_of o #2);

fun lookup_rule (rs:rules) name = Library.assoc (NetRules.rules rs, name);

fun print_rules kind rs =
  let val thms = map snd (NetRules.rules rs)
  in Pretty.writeln (Pretty.big_list kind (map Display.pretty_thm thms)) end;


(* theory data kind 'HOL/induct_method' *)

structure GlobalInductArgs =
struct
  val name = "HOL/induct_method";
  type T = (rules * rules) * (rules * rules);

  val empty = ((type_rules, set_rules), (type_rules, set_rules));
  val copy = I;
  val prep_ext = I;
  fun merge (((casesT1, casesS1), (inductT1, inductS1)),
      ((casesT2, casesS2), (inductT2, inductS2))) =
    ((NetRules.merge (casesT1, casesT2), NetRules.merge (casesS1, casesS2)),
      (NetRules.merge (inductT1, inductT2), NetRules.merge (inductS1, inductS2)));

  fun print _ ((casesT, casesS), (inductT, inductS)) =
    (print_rules "type cases:" casesT;
      print_rules "set cases:" casesS;
      print_rules "type induct:" inductT;
      print_rules "set induct:" inductS);

  fun dest ((casesT, casesS), (inductT, inductS)) =
    {type_cases = NetRules.rules casesT,
     set_cases = NetRules.rules casesS,
     type_induct = NetRules.rules inductT,
     set_induct = NetRules.rules inductS};
end;

structure GlobalInduct = TheoryDataFun(GlobalInductArgs);
val print_global_rules = GlobalInduct.print;
val dest_global_rules = GlobalInductArgs.dest o GlobalInduct.get;


(* proof data kind 'HOL/induct_method' *)

structure LocalInductArgs =
struct
  val name = "HOL/induct_method";
  type T = GlobalInductArgs.T;

  fun init thy = GlobalInduct.get thy;
  fun print x = GlobalInductArgs.print x;
end;

structure LocalInduct = ProofDataFun(LocalInductArgs);
val print_local_rules = LocalInduct.print;
val dest_local_rules = GlobalInductArgs.dest o LocalInduct.get;


(* access rules *)

val get_cases = #1 o LocalInduct.get;
val get_induct = #2 o LocalInduct.get;

val lookup_casesT = lookup_rule o #1 o get_cases;
val lookup_casesS = lookup_rule o #2 o get_cases;
val lookup_inductT = lookup_rule o #1 o get_induct;
val lookup_inductS = lookup_rule o #2 o get_induct;



(** attributes **)

local

fun mk_att f g name (x, thm) = (f (g (name, thm)) x, thm);

fun add_casesT rule x = apfst (apfst (NetRules.insert rule)) x;
fun add_casesS rule x = apfst (apsnd (NetRules.insert rule)) x;
fun add_inductT rule x = apsnd (apfst (NetRules.insert rule)) x;
fun add_inductS rule x = apsnd (apsnd (NetRules.insert rule)) x;

in

val cases_type_global = mk_att GlobalInduct.map add_casesT;
val cases_set_global = mk_att GlobalInduct.map add_casesS;
val induct_type_global = mk_att GlobalInduct.map add_inductT;
val induct_set_global = mk_att GlobalInduct.map add_inductS;

val cases_type_local = mk_att LocalInduct.map add_casesT;
val cases_set_local = mk_att LocalInduct.map add_casesS;
val induct_type_local = mk_att LocalInduct.map add_inductT;
val induct_set_local = mk_att LocalInduct.map add_inductS;

end;



(** misc utils **)

(* terms *)

fun vars_of tm =        (*ordered left-to-right, preferring right!*)
  Term.foldl_aterms (fn (ts, t as Var _) => t :: ts | (ts, _) => ts) ([], tm)
  |> Library.distinct |> rev;

fun type_name t =
  #1 (Term.dest_Type (Term.type_of t))
    handle TYPE _ => raise TERM ("Bad type of term argument", [t]);


(* simplifying cases rules *)

local

(*delete needless equality assumptions*)
val refl_thin = prove_goal HOL.thy "!!P. [| a=a;  P |] ==> P"
     (fn _ => [assume_tac 1]);

val elim_rls = [asm_rl, FalseE, refl_thin, conjE, exE, Pair_inject];

val elim_tac = REPEAT o Tactic.eresolve_tac elim_rls;

fun simp_case_tac ss = 
  EVERY' [elim_tac, asm_full_simp_tac ss, elim_tac, REPEAT o bound_hyp_subst_tac];

in

fun con_elim_tac ss = ALLGOALS (simp_case_tac ss) THEN prune_params_tac;

fun con_elim_solved_tac ss =
  ALLGOALS (fn i => TRY (simp_case_tac ss i THEN_MAYBE no_tac)) THEN prune_params_tac;

end;



(** cases method **)

(*
  rule selection:
        cases         - classical case split
        cases t       - datatype exhaustion
  <x:A> cases ...     - set elimination
  ...   cases ... r   - explicit rule
*)

local

fun cases_var thm =
  (case try (hd o vars_of o hd o Logic.strip_assums_hyp o Library.last_elem o Thm.prems_of) thm of
    None => raise THM ("Malformed cases rule", 0, [thm])
  | Some x => x);

fun simplify_cases ctxt =
  Tactic.rule_by_tactic (con_elim_solved_tac (Simplifier.get_local_simpset ctxt));

fun cases_tac (ctxt, (simplified, args)) facts =
  let
    val sg = ProofContext.sign_of ctxt;
    val cert = Thm.cterm_of sg;

    fun inst_rule t thm =
      Drule.cterm_instantiate [(cert (cases_var thm), cert t)] thm;

    val cond_simp = if simplified then simplify_cases ctxt else I;

    fun find_cases th =
      NetRules.may_unify (#2 (get_cases ctxt))
        (Logic.strip_assums_concl (#prop (Thm.rep_thm th)));

    val rules =
      (case (args, facts) of
        ((None, None), []) => [RuleCases.none case_split_thm]		(* FIXME add cases!? *)
      | ((Some t, None), []) =>
          let val name = type_name t in
            (case lookup_casesT ctxt name of
              None => error ("No cases rule for type: " ^ quote name)
            | Some thm => [(inst_rule t thm, RuleCases.get thm)])
          end
      | ((None, None), th :: _) => map (RuleCases.add o #2) (find_cases th)
      | ((Some t, None), th :: _) =>
          (case find_cases th of	(*may instantiate first rule only!*)
            (_, thm) :: _ => [(inst_rule t thm, RuleCases.get thm)]
          | [] => [])
      | ((None, Some thm), _) => [RuleCases.add thm]
      | ((Some t, Some thm), _) => [(inst_rule t thm, RuleCases.get thm)]);

    fun prep_rule (thm, cases) =
      Seq.map (rpair cases o cond_simp) (Method.multi_resolves facts [thm]);
  in Method.resolveq_cases_tac (Seq.flat (Seq.map prep_rule (Seq.of_list rules))) end;

in

val cases_meth = Method.METHOD_CASES o (FINDGOAL oo cases_tac);

end;



(** induct method **)

(*
  rule selection:
        induct         - mathematical induction
        induct x       - datatype induction
  <x:A> induct ...     - set induction
  ...   induct ... r   - explicit rule
*)

local

infix 1 THEN_ALL_NEW_CASES;

fun (tac1 THEN_ALL_NEW_CASES tac2) i st =
  st |> Seq.THEN (tac1 i, (fn (st', cases) =>
    Seq.map (rpair cases) (ALLGOALS_RANGE tac2 i (i + nprems_of st' - nprems_of st) st')));


fun induct_rule ctxt t =
  let val name = type_name t in
    (case lookup_inductT ctxt name of
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


fun induct_tac (ctxt, (stripped, args)) facts =
  let
    val sg = ProofContext.sign_of ctxt;
    val cert = Thm.cterm_of sg;

    fun prep_inst (concl, ts) =
      let val xs = vars_of concl; val n = length xs - length ts in
        if n < 0 then error "More arguments given than in induction rule"
        else map cert (Library.drop (n, xs)) ~~ map cert ts
      end;

    fun inst_rule insts thm =
      Drule.cterm_instantiate (flat (map2 prep_inst
        (HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of thm)), insts))) thm;

    fun find_induct th =
      NetRules.may_unify (#2 (get_induct ctxt))
        (Logic.strip_assums_concl (#prop (Thm.rep_thm th)));

    val rules =
      (case (args, facts) of
        (([], None), []) => [RuleCases.none nat_induct]		(* FIXME add cases!? *)
      | ((insts, None), []) =>
          let val thms = map (induct_rule ctxt o last_elem) insts
          in [(inst_rule insts (join_rules thms), RuleCases.get (#2 (hd thms)))] end
      | (([], None), th :: _) => map (RuleCases.add o #2) (find_induct th)
      | ((insts, None), th :: _) =>
          (case find_induct th of	(*may instantiate first rule only!*)
	    (_, thm) :: _ => [(inst_rule insts thm, RuleCases.get thm)]
          | [] => [])
      | (([], Some thm), _) => [RuleCases.add thm]
      | ((insts, Some thm), _) => [(inst_rule insts thm, RuleCases.get thm)]);

    fun prep_rule (thm, cases) =
      Seq.map (rpair cases) (Method.multi_resolves facts [thm]);
    val tac = Method.resolveq_cases_tac (Seq.flat (Seq.map prep_rule (Seq.of_list rules)));
  in
    if stripped then tac THEN_ALL_NEW_CASES (REPEAT o resolve_tac [impI, allI, ballI])
    else tac
  end;

in

val induct_meth = Method.METHOD_CASES o (FINDGOAL oo induct_tac);

end;



(** concrete syntax **)

val casesN = "cases";
val inductN = "induct";

val simplifiedN = "simplified";
val strippedN = "stripped";

val typeN = "type";
val setN = "set";
val ruleN = "rule";


(* attributes *)

fun spec k = (Args.$$$ k -- Args.$$$ ":") |-- Args.!!! Args.name;

fun attrib sign_of add_type add_set = Scan.depend (fn x =>
  let val sg = sign_of x in
    spec typeN >> (add_type o Sign.intern_tycon sg) ||
    spec setN  >> (add_set o Sign.intern_const sg)
  end >> pair x);

val cases_attr =
  (Attrib.syntax (attrib Theory.sign_of cases_type_global cases_set_global),
   Attrib.syntax (attrib ProofContext.sign_of cases_type_local cases_set_local));

val induct_attr =
  (Attrib.syntax (attrib Theory.sign_of induct_type_global induct_set_global),
   Attrib.syntax (attrib ProofContext.sign_of induct_type_local induct_set_local));


(* methods *)

local

fun err k get name =
  (case get name of Some x => x
  | None => error ("No rule for " ^ k ^ " " ^ quote name));

fun rule get_type get_set =
  Scan.depend (fn ctxt =>
    let val sg = ProofContext.sign_of ctxt in
      spec typeN >> (err typeN (get_type ctxt) o Sign.intern_tycon sg) ||
      spec setN >> (err setN (get_set ctxt) o Sign.intern_const sg)
    end >> pair ctxt) ||
  Scan.lift (Args.$$$ ruleN -- Args.$$$ ":") |-- Attrib.local_thm;

val cases_rule = rule lookup_casesT lookup_casesS;
val induct_rule = rule lookup_inductT lookup_inductS;

val kind = (Args.$$$ typeN || Args.$$$ setN || Args.$$$ ruleN) -- Args.$$$ ":";
val term = Scan.unless (Scan.lift kind) Args.local_term;

fun mode name =
  Scan.lift (Scan.optional (Args.$$$ name -- Args.$$$ ":" >> K true) false);

in

val cases_args =
  Method.syntax (mode simplifiedN -- (Scan.option term -- Scan.option cases_rule));
val induct_args =
  Method.syntax (mode strippedN -- (Args.and_list (Scan.repeat1 term) -- Scan.option induct_rule));

end;



(** theory setup **)

val setup =
  [GlobalInduct.init, LocalInduct.init,
   Attrib.add_attributes
    [(casesN, cases_attr, "cases rule for type or set"),
     (inductN, induct_attr, "induction rule for type or set")],
   Method.add_methods
    [("cases", cases_meth oo cases_args, "case analysis on types or sets"),
     ("induct", induct_meth oo induct_args, "induction on types or sets")]];

end;
