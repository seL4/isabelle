(*  Title:      HOL/Tools/induct_method.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Proof by cases and induction on types (intro) and sets (elim).
*)

signature INDUCT_METHOD =
sig
  val print_global_rules: theory -> unit
  val print_local_rules: Proof.context -> unit
  val cases_type_global: string -> theory attribute
  val cases_set_global: string -> theory attribute
  val cases_type_local: string -> Proof.context attribute
  val cases_set_local: string -> Proof.context attribute
  val induct_type_global: string -> theory attribute
  val induct_set_global: string -> theory attribute
  val induct_type_local: string -> Proof.context attribute
  val induct_set_local: string -> Proof.context attribute
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
end;

structure GlobalInduct = TheoryDataFun(GlobalInductArgs);
val print_global_rules = GlobalInduct.print;


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

fun vars_of tm =        (*ordered left-to-right, preferring right!*)
  Term.foldl_aterms (fn (ts, t as Var _) => t :: ts | (ts, _) => ts) ([], tm)
  |> Library.distinct |> rev;

fun type_name t =
  #1 (Term.dest_Type (Term.type_of t))
    handle TYPE _ => raise TERM ("Bad type of term argument", [t]);



(** cases method **)

(*
  rule selection:
        cases         - classical case split
  <x:A> cases         - set elimination
  ...   cases t       - datatype exhaustion
  ...   cases ... r   - explicit rule
*)

fun cases_var thm =
  (case try (hd o vars_of o hd o Logic.strip_assums_hyp o Library.last_elem o Thm.prems_of) thm of
    None => raise THM ("Malformed cases rule", 0, [thm])
  | Some x => x);

fun cases_tac (ctxt, args) facts =
  let
    val sg = ProofContext.sign_of ctxt;
    val cert = Thm.cterm_of sg;

    fun inst_rule t thm =
      Drule.cterm_instantiate [(cert (cases_var thm), cert t)] thm;

    val thms =
      (case (args, facts) of
        ((None, None), []) => [case_split_thm]
      | ((None, None), th :: _) =>
          NetRules.may_unify (#2 (get_cases ctxt))
            (Logic.strip_assums_concl (#prop (Thm.rep_thm th)))
          |> map #2
      | ((Some t, None), _) =>
          let val name = type_name t in
            (case lookup_casesT ctxt name of
              None => error ("No cases rule for type: " ^ quote name)
            | Some thm => [inst_rule t thm])
          end
      | ((None, Some thm), _) => [thm]
      | ((Some t, Some thm), _) => [inst_rule t thm]);
  in Method.rule_tac thms facts end;

val cases_meth = Method.METHOD o (FINDGOAL oo cases_tac);



(** induct method **)

(*
  rule selection:
        induct         - mathematical induction
  <x:A> induct         - set induction
  ...   induct x       - datatype induction
  ...   induct ... r   - explicit rule
*)

fun induct_rule ctxt t =
  let val name = type_name t in
    (case lookup_inductT ctxt name of
      None => error ("No induct rule for type: " ^ quote name)
    | Some thm => thm)
  end;

fun join_rules [thm] = thm
  | join_rules raw_thms =
      let
        val (thms, thm) = Library.split_last (map Drule.freeze_all raw_thms);
        val cprems = Drule.cprems_of thm;
        val asms = map Thm.assume cprems;
        fun strip th = Drule.implies_elim_list th asms;
      in
        foldr (fn (th, th') => [th, th'] MRS conjI) (map strip thms, strip thm)
        |> Drule.implies_intr_list cprems
        |> Drule.standard
      end;

fun induct_tac (ctxt, args) facts =
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

    val thms =
      (case (args, facts) of
        (([], None), []) => [nat_induct]
      | (([], None), th :: _) =>
          NetRules.may_unify (#2 (get_induct ctxt))
            (Logic.strip_assums_concl (#prop (Thm.rep_thm th)))
          |> map #2
      | ((insts, None), _) =>
          [inst_rule insts (join_rules (map (induct_rule ctxt o last_elem) insts))]
      | (([], Some thm), _) => [thm]
      | ((insts, Some thm), _) => [inst_rule insts thm]);
  in Method.rule_tac thms facts end;

val induct_meth = Method.METHOD o (FINDGOAL oo induct_tac);



(** concrete syntax **)

val casesN = "cases";
val inductN = "induct";
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

in

val cases_args = Method.syntax (Scan.option term -- Scan.option cases_rule);
val induct_args = Method.syntax (Args.and_list (Scan.repeat1 term) -- Scan.option induct_rule);

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
