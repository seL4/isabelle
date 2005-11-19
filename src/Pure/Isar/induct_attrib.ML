(*  Title:      Pure/Isar/induct_attrib.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Declaration of rules for cases and induction.
*)

signature INDUCT_ATTRIB =
sig
  val vars_of: term -> term list
  val dest_global_rules: theory ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list,
      type_coinduct: (string * thm) list, set_coinduct: (string * thm) list}
  val print_global_rules: theory -> unit
  val dest_local_rules: Proof.context ->
    {type_cases: (string * thm) list, set_cases: (string * thm) list,
      type_induct: (string * thm) list, set_induct: (string * thm) list,
      type_coinduct: (string * thm) list, set_coinduct: (string * thm) list}
  val print_local_rules: Proof.context -> unit
  val lookup_casesT : Proof.context -> string -> thm option
  val lookup_casesS : Proof.context -> string -> thm option
  val lookup_inductT : Proof.context -> string -> thm option
  val lookup_inductS : Proof.context -> string -> thm option
  val lookup_coinductT : Proof.context -> string -> thm option
  val lookup_coinductS : Proof.context -> string -> thm option
  val find_casesT: Proof.context -> typ -> thm list
  val find_casesS: Proof.context -> thm -> thm list
  val find_inductT: Proof.context -> typ -> thm list
  val find_inductS: Proof.context -> thm -> thm list
  val find_coinductT: Proof.context -> typ -> thm list
  val find_coinductS: Proof.context -> thm -> thm list
  val cases_type_global: string -> theory attribute
  val cases_set_global: string -> theory attribute
  val cases_type_local: string -> Proof.context attribute
  val cases_set_local: string -> Proof.context attribute
  val induct_type_global: string -> theory attribute
  val induct_set_global: string -> theory attribute
  val induct_type_local: string -> Proof.context attribute
  val induct_set_local: string -> Proof.context attribute
  val coinduct_type_global: string -> theory attribute
  val coinduct_set_global: string -> theory attribute
  val coinduct_type_local: string -> Proof.context attribute
  val coinduct_set_local: string -> Proof.context attribute
  val casesN: string
  val inductN: string
  val coinductN: string
  val typeN: string
  val setN: string
end;

structure InductAttrib: INDUCT_ATTRIB =
struct


(** misc utils **)

(* encode_type -- for indexing purposes *)

fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
  | encode_type (TFree (a, _)) = Free (a, dummyT)
  | encode_type (TVar (a, _)) = Var (a, dummyT);


(* variables -- ordered left-to-right, preferring right *)

fun vars_of tm =
  Term.fold_aterms (fn (t as Var _) => cons t | _ => I) tm []
  |> Library.distinct
  |> rev;

local

val mk_var = encode_type o #2 o Term.dest_Var;

fun concl_var which thm = mk_var (which (vars_of (Thm.concl_of thm))) handle Empty =>
  raise THM ("No variables in conclusion of rule", 0, [thm]);

in

fun left_var_prem thm = mk_var (hd (vars_of (hd (Thm.prems_of thm)))) handle Empty =>
  raise THM ("No variables in major premise of rule", 0, [thm]);

val left_var_concl = concl_var hd;
val right_var_concl = concl_var List.last;

end;



(** global and local induct data **)

(* rules *)

type rules = (string * thm) NetRules.T;

val init_rules =
  NetRules.init (fn ((s1: string, th1), (s2, th2)) => s1 = s2 andalso
    Drule.eq_thm_prop (th1, th2));

fun lookup_rule (rs: rules) = AList.lookup (op =) (NetRules.rules rs);

fun pretty_rules prt kind x rs =
  let val thms = map snd (NetRules.rules rs)
  in Pretty.big_list kind (map (prt x) thms) end;

fun print_all_rules prt x ((casesT, casesS), (inductT, inductS), (coinductT, coinductS)) =
 [pretty_rules prt "coinduct type:" x coinductT,
  pretty_rules prt "coinduct set:" x coinductS,
  pretty_rules prt "induct type:" x inductT,
  pretty_rules prt "induct set:" x inductS,
  pretty_rules prt "cases type:" x casesT,
  pretty_rules prt "cases set:" x casesS]
 |> Pretty.chunks |> Pretty.writeln;


(* theory data *)

structure GlobalInductArgs =
struct
  val name = "Isar/induct";
  type T = (rules * rules) * (rules * rules) * (rules * rules);

  val empty =
    ((init_rules (left_var_prem o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (right_var_concl o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (left_var_concl o #2), init_rules (Thm.concl_of o #2)));
  val copy = I;
  val extend = I;
  fun merge _ (((casesT1, casesS1), (inductT1, inductS1), (coinductT1, coinductS1)),
      ((casesT2, casesS2), (inductT2, inductS2), (coinductT2, coinductS2))) =
    ((NetRules.merge (casesT1, casesT2), NetRules.merge (casesS1, casesS2)),
      (NetRules.merge (inductT1, inductT2), NetRules.merge (inductS1, inductS2)),
      (NetRules.merge (coinductT1, coinductT2), NetRules.merge (coinductS1, coinductS2)));

  fun print x = print_all_rules Display.pretty_thm_sg x;

  fun dest ((casesT, casesS), (inductT, inductS), (coinductT, coinductS)) =
    {type_cases = NetRules.rules casesT,
     set_cases = NetRules.rules casesS,
     type_induct = NetRules.rules inductT,
     set_induct = NetRules.rules inductS,
     type_coinduct = NetRules.rules coinductT,
     set_coinduct = NetRules.rules coinductS};
end;

structure GlobalInduct = TheoryDataFun(GlobalInductArgs);
val _ = Context.add_setup [GlobalInduct.init];
val print_global_rules = GlobalInduct.print;
val dest_global_rules = GlobalInductArgs.dest o GlobalInduct.get;


(* proof data *)

structure LocalInduct = ProofDataFun
(struct
  val name = "Isar/induct";
  type T = GlobalInductArgs.T;

  fun init thy = GlobalInduct.get thy;
  fun print x = print_all_rules ProofContext.pretty_thm x;
end);

val _ = Context.add_setup [LocalInduct.init];
val print_local_rules = LocalInduct.print;
val dest_local_rules = GlobalInductArgs.dest o LocalInduct.get;


(* access rules *)

val lookup_casesT = lookup_rule o #1 o #1 o LocalInduct.get;
val lookup_casesS = lookup_rule o #2 o #1 o LocalInduct.get;
val lookup_inductT = lookup_rule o #1 o #2 o LocalInduct.get;
val lookup_inductS = lookup_rule o #2 o #2 o LocalInduct.get;
val lookup_coinductT = lookup_rule o #1 o #3 o LocalInduct.get;
val lookup_coinductS = lookup_rule o #2 o #3 o LocalInduct.get;


fun find_rules which how ctxt x =
  map snd (NetRules.retrieve (which (LocalInduct.get ctxt)) (how x));

val find_casesT = find_rules (#1 o #1) encode_type;
val find_casesS = find_rules (#2 o #1) Thm.concl_of;
val find_inductT = find_rules (#1 o #2) encode_type;
val find_inductS = find_rules (#2 o #2) Thm.concl_of;
val find_coinductT = find_rules (#1 o #3) encode_type;
val find_coinductS = find_rules (#2 o #3) Thm.concl_of;



(** attributes **)

local

fun mk_att f g h name arg =
  let val (x, thm) = h arg in (f (g (name, thm)) x, thm) end;

fun map1 f (x, y, z) = (f x, y, z);
fun map2 f (x, y, z) = (x, f y, z);
fun map3 f (x, y, z) = (x, y, f z);

fun add_casesT rule x = map1 (apfst (NetRules.insert rule)) x;
fun add_casesS rule x = map1 (apsnd (NetRules.insert rule)) x;
fun add_inductT rule x = map2 (apfst (NetRules.insert rule)) x;
fun add_inductS rule x = map2 (apsnd (NetRules.insert rule)) x;
fun add_coinductT rule x = map3 (apfst (NetRules.insert rule)) x;
fun add_coinductS rule x = map3 (apsnd (NetRules.insert rule)) x;

fun consumes0 x = RuleCases.consumes_default 0 x;
fun consumes1 x = RuleCases.consumes_default 1 x;

in

val cases_type_global = mk_att GlobalInduct.map add_casesT consumes0;
val cases_set_global = mk_att GlobalInduct.map add_casesS consumes1;
val induct_type_global = mk_att GlobalInduct.map add_inductT consumes0;
val induct_set_global = mk_att GlobalInduct.map add_inductS consumes1;
val coinduct_type_global = mk_att GlobalInduct.map add_coinductT consumes0;
val coinduct_set_global = mk_att GlobalInduct.map add_coinductS consumes1;

val cases_type_local = mk_att LocalInduct.map add_casesT consumes0;
val cases_set_local = mk_att LocalInduct.map add_casesS consumes1;
val induct_type_local = mk_att LocalInduct.map add_inductT consumes0;
val induct_set_local = mk_att LocalInduct.map add_inductS consumes1;
val coinduct_type_local = mk_att LocalInduct.map add_coinductT consumes0;
val coinduct_set_local = mk_att LocalInduct.map add_coinductS consumes1;

end;


(** concrete syntax **)

val casesN = "cases";
val inductN = "induct";
val coinductN = "coinduct";

val typeN = "type";
val setN = "set";

local

fun spec k arg =
  Scan.lift (Args.$$$ k -- Args.colon) |-- arg ||
  Scan.lift (Args.$$$ k) >> K "";

fun attrib tyname const add_type add_set =
  Attrib.syntax (spec typeN tyname >> add_type || spec setN const >> add_set);

in

val cases_attr =
 (attrib Args.global_tyname Args.global_const cases_type_global cases_set_global,
  attrib Args.local_tyname Args.local_const cases_type_local cases_set_local);

val induct_attr =
 (attrib Args.global_tyname Args.global_const induct_type_global induct_set_global,
  attrib Args.local_tyname Args.local_const induct_type_local induct_set_local);

val coinduct_attr =
 (attrib Args.global_tyname Args.global_const coinduct_type_global coinduct_set_global,
  attrib Args.local_tyname Args.local_const coinduct_type_local coinduct_set_local);

end;

val _ = Context.add_setup
 [Attrib.add_attributes
  [(casesN, cases_attr, "declaration of cases rule for type or set"),
   (inductN, induct_attr, "declaration of induction rule for type or set"),
   (coinductN, coinduct_attr, "declaration of coinduction rule for type or set")]];

end;
