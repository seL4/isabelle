(*  Title:      Pure/Isar/induct_attrib.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Declaration of rules for cases and induction.
*)

signature INDUCT_ATTRIB =
sig
  val vars_of: term -> term list
  val dest_global_rules: theory ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list}
  val print_global_rules: theory -> unit
  val dest_local_rules: Proof.context ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list}
  val print_local_rules: Proof.context -> unit
  val lookup_casesT : Proof.context -> string -> thm option
  val lookup_casesS : Proof.context -> string -> thm option
  val lookup_inductT : Proof.context -> string -> thm option
  val lookup_inductS : Proof.context -> string -> thm option
  val find_casesT: Proof.context -> typ -> thm list
  val find_casesS: Proof.context -> thm -> thm list
  val find_inductT: Proof.context -> typ -> thm list
  val find_inductS: Proof.context -> thm -> thm list
  val cases_type_global: string -> theory attribute
  val cases_set_global: string -> theory attribute
  val cases_type_local: string -> Proof.context attribute
  val cases_set_local: string -> Proof.context attribute
  val induct_type_global: string -> theory attribute
  val induct_set_global: string -> theory attribute
  val induct_type_local: string -> Proof.context attribute
  val induct_set_local: string -> Proof.context attribute
  val casesN: string
  val inductN: string
  val typeN: string
  val setN: string
  val setup: (theory -> theory) list
end;

structure InductAttrib: INDUCT_ATTRIB =
struct


(** misc utils **)

(* encode_type -- for indexing purposes *)

fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
  | encode_type (TFree (a, _)) = Free (a, dummyT)
  | encode_type (TVar (a, _)) = Var (a, dummyT);


(* variables -- ordered left-to-right, preferring right *)

local

fun rev_vars_of tm =
  Term.foldl_aterms (fn (ts, t as Var _) => t :: ts | (ts, _) => ts) ([], tm)
  |> Library.distinct;

val mk_var = encode_type o #2 o Term.dest_Var;

in

val vars_of = rev o rev_vars_of;

fun first_var thm = mk_var (hd (vars_of (hd (Thm.prems_of thm)))) handle LIST _ =>
  raise THM ("No variables in first premise of rule", 0, [thm]);

fun last_var thm = mk_var (hd (rev_vars_of (Thm.concl_of thm))) handle LIST _ =>
  raise THM ("No variables in conclusion of rule", 0, [thm]);

end;



(** global and local induct data **)

(* rules *)

type rules = (string * thm) NetRules.T;

val init_rules = NetRules.init (fn ((s1: string, th1), (s2, th2)) => s1 = s2
  andalso Thm.eq_thm (th1, th2)) (K 0);

fun lookup_rule (rs: rules) name = Library.assoc (NetRules.rules rs, name);

fun print_rules prt kind x rs =
  let val thms = map snd (NetRules.rules rs)
  in Pretty.writeln (Pretty.big_list kind (map (prt x) thms)) end;

fun print_all_rules prt x ((casesT, casesS), (inductT, inductS)) =
 (print_rules prt "induct type:" x inductT;
  print_rules prt "induct set:" x inductS;
  print_rules prt "cases type:" x casesT;
  print_rules prt "cases set:" x casesS);


(* theory data kind 'Isar/induction' *)

structure GlobalInductArgs =
struct
  val name = "Isar/induction";
  type T = (rules * rules) * (rules * rules);

  val empty =
    ((init_rules (first_var o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (last_var o #2), init_rules (Thm.major_prem_of o #2)));
  val copy = I;
  val prep_ext = I;
  fun merge (((casesT1, casesS1), (inductT1, inductS1)),
      ((casesT2, casesS2), (inductT2, inductS2))) =
    ((NetRules.merge (casesT1, casesT2), NetRules.merge (casesS1, casesS2)),
      (NetRules.merge (inductT1, inductT2), NetRules.merge (inductS1, inductS2)));

  fun print x = print_all_rules Display.pretty_thm_sg x;

  fun dest ((casesT, casesS), (inductT, inductS)) =
    {type_cases = NetRules.rules casesT,
     set_cases = NetRules.rules casesS,
     type_induct = NetRules.rules inductT,
     set_induct = NetRules.rules inductS};
end;

structure GlobalInduct = TheoryDataFun(GlobalInductArgs);
val print_global_rules = GlobalInduct.print;
val dest_global_rules = GlobalInductArgs.dest o GlobalInduct.get;


(* proof data kind 'Isar/induction' *)

structure LocalInductArgs =
struct
  val name = "Isar/induction";
  type T = GlobalInductArgs.T;

  fun init thy = GlobalInduct.get thy;
  fun print x = print_all_rules ProofContext.pretty_thm x;
end;

structure LocalInduct = ProofDataFun(LocalInductArgs);
val print_local_rules = LocalInduct.print;
val dest_local_rules = GlobalInductArgs.dest o LocalInduct.get;


(* access rules *)

val lookup_casesT = lookup_rule o #1 o #1 o LocalInduct.get;
val lookup_casesS = lookup_rule o #2 o #1 o LocalInduct.get;
val lookup_inductT = lookup_rule o #1 o #2 o LocalInduct.get;
val lookup_inductS = lookup_rule o #2 o #2 o LocalInduct.get;


fun find_rules which how ctxt x =
  map snd (NetRules.retrieve (which (LocalInduct.get ctxt)) (how x));

val find_casesT = find_rules (#1 o #1) encode_type;
val find_casesS = find_rules (#2 o #1) Thm.concl_of;
val find_inductT = find_rules (#1 o #2) encode_type;
val find_inductS = find_rules (#2 o #2) Thm.concl_of;



(** attributes **)

local

fun mk_att f g h name arg =
  let val (x, thm) = h arg in (f (g (name, thm)) x, thm) end;

fun add_casesT rule x = apfst (apfst (NetRules.insert rule)) x;
fun add_casesS rule x = apfst (apsnd (NetRules.insert rule)) x;
fun add_inductT rule x = apsnd (apfst (NetRules.insert rule)) x;
fun add_inductS rule x = apsnd (apsnd (NetRules.insert rule)) x;

fun consumes0 x = RuleCases.consumes_default 0 x;
fun consumes1 x = RuleCases.consumes_default 1 x;

in

val cases_type_global = mk_att GlobalInduct.map add_casesT consumes0;
val cases_set_global = mk_att GlobalInduct.map add_casesS consumes1;
val induct_type_global = mk_att GlobalInduct.map add_inductT consumes0;
val induct_set_global = mk_att GlobalInduct.map add_inductS consumes1;

val cases_type_local = mk_att LocalInduct.map add_casesT consumes0;
val cases_set_local = mk_att LocalInduct.map add_casesS consumes1;
val induct_type_local = mk_att LocalInduct.map add_inductT consumes0;
val induct_set_local = mk_att LocalInduct.map add_inductS consumes1;

end;


(** concrete syntax **)

val casesN = "cases";
val inductN = "induct";

val typeN = "type";
val setN = "set";

local

fun spec k cert =
  (Args.$$$ k -- Args.colon) |-- Args.!!! (Args.name >> cert) ||
  Args.$$$ k >> K "";

fun attrib sign_of add_type add_set = Scan.depend (fn x =>
  let val sg = sign_of x in
    spec typeN (Sign.certify_tyname sg o Sign.intern_tycon sg) >> add_type ||
    spec setN (Sign.certify_const sg o Sign.intern_const sg) >> add_set
  end >> pair x);

in

val cases_attr =
  (Attrib.syntax (attrib Theory.sign_of cases_type_global cases_set_global),
   Attrib.syntax (attrib ProofContext.sign_of cases_type_local cases_set_local));

val induct_attr =
  (Attrib.syntax (attrib Theory.sign_of induct_type_global induct_set_global),
   Attrib.syntax (attrib ProofContext.sign_of induct_type_local induct_set_local));

end;



(** theory setup **)

val setup =
  [GlobalInduct.init, LocalInduct.init,
   Attrib.add_attributes
    [(casesN, cases_attr, "declaration of cases rule for type or set"),
     (inductN, induct_attr, "declaration of induction rule for type or set")]];

end;
