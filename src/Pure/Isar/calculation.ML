(*  Title:      Pure/Isar/calculation.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Support for calculational proofs.
*)

signature CALCULATION =
sig
  val print_global_rules: theory -> unit
  val print_local_rules: Proof.context -> unit
  val trans_add_global: theory attribute
  val trans_del_global: theory attribute
  val trans_add_local: Proof.context attribute
  val trans_del_local: Proof.context attribute
  val sym_add_global: theory attribute
  val sym_del_global: theory attribute
  val sym_add_local: Proof.context attribute
  val sym_del_local: Proof.context attribute
  val symmetric_global: theory attribute
  val symmetric_local: Proof.context attribute
  val also: thm list option -> (Proof.context -> thm list -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val finally: thm list option -> (Proof.context -> thm list -> unit)
    -> Proof.state -> Proof.state Seq.seq
  val moreover: (Proof.context -> thm list -> unit) -> Proof.state -> Proof.state
  val ultimately: (Proof.context -> thm list -> unit) -> Proof.state -> Proof.state
  val setup: (theory -> theory) list
end;

structure Calculation: CALCULATION =
struct

(** global and local calculation data **)

(* theory data kind 'Isar/calculation' *)

fun print_rules prt x (trans, sym) =
  [Pretty.big_list "transitivity rules:" (map (prt x) (NetRules.rules trans)),
    Pretty.big_list "symmetry rules:" (map (prt x) sym)]
  |> Pretty.chunks |> Pretty.writeln;

structure GlobalCalculationArgs =
struct
  val name = "Isar/calculation";
  type T = thm NetRules.T * thm list

  val empty = (NetRules.elim, []);
  val copy = I;
  val prep_ext = I;
  fun merge ((trans1, sym1), (trans2, sym2)) =
    (NetRules.merge (trans1, trans2), Drule.merge_rules (sym1, sym2));
  val print = print_rules Display.pretty_thm_sg;
end;

structure GlobalCalculation = TheoryDataFun(GlobalCalculationArgs);
val print_global_rules = GlobalCalculation.print;


(* proof data kind 'Isar/calculation' *)

structure LocalCalculationArgs =
struct
  val name = "Isar/calculation";
  type T = (thm NetRules.T * thm list) * (thm list * int) option;

  fun init thy = (GlobalCalculation.get thy, None);
  fun print ctxt (rs, _) = print_rules ProofContext.pretty_thm ctxt rs;
end;

structure LocalCalculation = ProofDataFun(LocalCalculationArgs);
val get_local_rules = #1 o LocalCalculation.get o Proof.context_of;
val print_local_rules = LocalCalculation.print;


(* access calculation *)

fun get_calculation state =
  (case #2 (LocalCalculation.get (Proof.context_of state)) of
    None => None
  | Some (thms, lev) => if lev = Proof.level state then Some thms else None);

fun put_calculation thms state =
  Proof.map_context
    (LocalCalculation.put (get_local_rules state, Some (thms, Proof.level state))) state;

fun reset_calculation state =
  Proof.map_context (LocalCalculation.put (get_local_rules state, None)) state;



(** attributes **)

(* add/del rules *)

fun global_att f (x, thm) = (GlobalCalculation.map (f thm) x, thm);
fun local_att f (x, thm) = (LocalCalculation.map (apfst (f thm)) x, thm);

val trans_add_global = global_att (apfst o NetRules.insert);
val trans_del_global = global_att (apfst o NetRules.delete);
val trans_add_local = local_att (apfst o NetRules.insert);
val trans_del_local = local_att (apfst o NetRules.delete);

val sym_add_global = global_att (apsnd o Drule.add_rule) o ContextRules.elim_query_global None;
val sym_del_global = global_att (apsnd o Drule.del_rule) o ContextRules.rule_del_global;
val sym_add_local = local_att (apsnd o Drule.add_rule) o ContextRules.elim_query_local None;
val sym_del_local = local_att (apsnd o Drule.del_rule) o ContextRules.rule_del_local;


(* symmetry *)

fun gen_symmetric get_sym = Drule.rule_attribute (fn x => fn th =>
  (case Seq.chop (2, Method.multi_resolves [th] (get_sym x)) of
    ([th'], _) => th'
  | ([], _) => raise THM ("symmetric: no unifiers", 1, [th])
  | _ => raise THM ("symmetric: multiple unifiers", 1, [th])));

val symmetric_global = gen_symmetric (#2 o GlobalCalculation.get);
val symmetric_local = gen_symmetric (#2 o #1 o LocalCalculation.get);


(* concrete syntax *)

val trans_attr =
 (Attrib.add_del_args trans_add_global trans_del_global,
  Attrib.add_del_args trans_add_local trans_del_local);

val sym_attr =
 (Attrib.add_del_args sym_add_global sym_del_global,
  Attrib.add_del_args sym_add_local sym_del_local);



(** proof commands **)

(* maintain calculation register *)

val calculationN = "calculation";

fun maintain_calculation false calc state =
      state
      |> put_calculation calc
      |> Proof.simple_have_thms calculationN calc
  | maintain_calculation true calc state =
      state
      |> reset_calculation
      |> Proof.reset_thms calculationN
      |> Proof.simple_have_thms "" calc
      |> Proof.chain;


(* 'also' and 'finally' *)

fun err_if state b msg = if b then raise Proof.STATE (msg, state) else ();

fun calculate final opt_rules print state =
  let
    val strip_assums_concl = Logic.strip_assums_concl o Thm.prop_of;
    val eq_prop = op aconv o pairself (Pattern.eta_contract o strip_assums_concl);
    fun projection ths th = Library.exists (Library.curry eq_prop th) ths;

    fun combine ths =
      (case opt_rules of Some rules => rules
      | None =>
          (case ths of [] => NetRules.rules (#1 (get_local_rules state))
          | th :: _ => NetRules.retrieve (#1 (get_local_rules state)) (strip_assums_concl th)))
      |> Seq.of_list |> Seq.map (Method.multi_resolve ths) |> Seq.flat
      |> Seq.filter (not o projection ths);

    val facts = Proof.the_facts (Proof.assert_forward state);
    val (initial, calculations) =
      (case get_calculation state of
        None => (true, Seq.single facts)
      | Some calc => (false, Seq.map single (combine (calc @ facts))));
  in
    err_if state (initial andalso final) "No calculation yet";
    err_if state (initial andalso is_some opt_rules) "Initial calculation -- no rules to be given";
    calculations |> Seq.map (fn calc => (print (Proof.context_of state) calc;
        state |> maintain_calculation final calc))
  end;

fun also print = calculate false print;
fun finally print = calculate true print;


(* 'moreover' and 'ultimately' *)

fun collect final print state =
  let
    val facts = Proof.the_facts (Proof.assert_forward state);
    val (initial, thms) =
      (case get_calculation state of
        None => (true, [])
      | Some thms => (false, thms));
    val calc = thms @ facts;
  in
    err_if state (initial andalso final) "No calculation yet";
    print (Proof.context_of state) calc;
    state |> maintain_calculation final calc
  end;

fun moreover print = collect false print;
fun ultimately print = collect true print;



(** theory setup **)

val setup =
 [GlobalCalculation.init, LocalCalculation.init,
  Attrib.add_attributes
   [("trans", trans_attr, "declaration of transitivity rule"),
    ("sym", sym_attr, "declaration of symmetry rule"),
    ("symmetric", (Attrib.no_args symmetric_global, Attrib.no_args symmetric_local),
      "resolution with symmetry rule")],
  #1 o PureThy.add_thms
   [(("", transitive_thm), [trans_add_global]),
    (("", symmetric_thm), [sym_add_global])]];

end;
