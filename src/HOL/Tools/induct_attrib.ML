(*  Title:      HOL/Tools/induct_attrib.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Declaration of rules for cases and induction.
*)

signature INDUCT_ATTRIB =
sig
  val dest_global_rules: theory ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list}
  val print_global_rules: theory -> unit
  val dest_local_rules: Proof.context ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list}
  val print_local_rules: Proof.context -> unit
  val get_cases : Proof.context -> (string * thm) NetRules.T * (string * thm) NetRules.T
  val get_induct : Proof.context -> (string * thm) NetRules.T * (string * thm) NetRules.T
  val lookup_casesS : Proof.context -> string -> thm option
  val lookup_casesT : Proof.context -> string -> thm option
  val lookup_inductS : Proof.context -> string -> thm option
  val lookup_inductT : Proof.context -> string -> thm option
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


(** global and local induct data **)

(* rules *)

type rules = (string * thm) NetRules.T;

fun eq_rule ((s1:string, th1), (s2, th2)) = s1 = s2 andalso Thm.eq_thm (th1, th2);

val type_rules = NetRules.init eq_rule (Thm.concl_of o #2);
val set_rules = NetRules.init eq_rule (Thm.major_prem_of o #2);

fun lookup_rule (rs:rules) name = Library.assoc (NetRules.rules rs, name);

fun print_rules kind sg rs =
  let val thms = map snd (NetRules.rules rs)
  in Pretty.writeln (Pretty.big_list kind (map (Display.pretty_thm_sg sg) thms)) end;


(* theory data kind 'HOL/induction' *)

structure GlobalInductArgs =
struct
  val name = "HOL/induction";
  type T = (rules * rules) * (rules * rules);

  val empty = ((type_rules, set_rules), (type_rules, set_rules));
  val copy = I;
  val prep_ext = I;
  fun merge (((casesT1, casesS1), (inductT1, inductS1)),
      ((casesT2, casesS2), (inductT2, inductS2))) =
    ((NetRules.merge (casesT1, casesT2), NetRules.merge (casesS1, casesS2)),
      (NetRules.merge (inductT1, inductT2), NetRules.merge (inductS1, inductS2)));

  fun print sg ((casesT, casesS), (inductT, inductS)) =
    (print_rules "type cases:" sg casesT;
      print_rules "set cases:" sg casesS;
      print_rules "type induct:" sg inductT;
      print_rules "set induct:" sg inductS);

  fun dest ((casesT, casesS), (inductT, inductS)) =
    {type_cases = NetRules.rules casesT,
     set_cases = NetRules.rules casesS,
     type_induct = NetRules.rules inductT,
     set_induct = NetRules.rules inductS};
end;

structure GlobalInduct = TheoryDataFun(GlobalInductArgs);
val print_global_rules = GlobalInduct.print;
val dest_global_rules = GlobalInductArgs.dest o GlobalInduct.get;


(* proof data kind 'HOL/induction' *)

structure LocalInductArgs =
struct
  val name = "HOL/induction";
  type T = GlobalInductArgs.T;

  fun init thy = GlobalInduct.get thy;
  fun print x = GlobalInductArgs.print (ProofContext.sign_of x);
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


(** concrete syntax **)

val casesN = "cases";
val inductN = "induct";

val typeN = "type";
val setN = "set";

local

fun spec k = (Args.$$$ k -- Args.colon) |-- Args.!!! Args.name;

fun attrib sign_of add_type add_set = Scan.depend (fn x =>
  let val sg = sign_of x in
    spec typeN >> (add_type o Sign.intern_tycon sg) ||
    spec setN  >> (add_set o Sign.intern_const sg)
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
