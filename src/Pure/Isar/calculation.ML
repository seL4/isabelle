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

fun print_rules prt x rs =
  Pretty.writeln (Pretty.big_list "transitivity rules:" (map (prt x) (NetRules.rules rs)));

structure GlobalCalculationArgs =
struct
  val name = "Isar/calculation";
  type T = thm NetRules.T

  val empty = NetRules.elim;
  val copy = I;
  val prep_ext = I;
  val merge = NetRules.merge;
  val print = print_rules Display.pretty_thm_sg;
end;

structure GlobalCalculation = TheoryDataFun(GlobalCalculationArgs);
val print_global_rules = GlobalCalculation.print;


(* proof data kind 'Isar/calculation' *)

structure LocalCalculationArgs =
struct
  val name = "Isar/calculation";
  type T = thm NetRules.T * (thm list * int) option;

  fun init thy = (GlobalCalculation.get thy, None);
  fun print ctxt (rs, _) = print_rules ProofContext.pretty_thm ctxt rs;
end;

structure LocalCalculation = ProofDataFun(LocalCalculationArgs);
val get_local_rules = #1 o LocalCalculation.get_st;
val print_local_rules = LocalCalculation.print;


(* access calculation *)

fun get_calculation state =
  (case #2 (LocalCalculation.get_st state) of
    None => None
  | Some (thms, lev) => if lev = Proof.level state then Some thms else None);

fun put_calculation thms state =
  LocalCalculation.put_st (get_local_rules state, Some (thms, Proof.level state)) state;

fun reset_calculation state =
  LocalCalculation.put_st (get_local_rules state, None) state;



(** attributes **)

(* trans add/del *)

fun mk_att f g (x, thm) = (f (g thm) x, thm);

val trans_add_global = mk_att GlobalCalculation.map NetRules.insert;
val trans_del_global = mk_att GlobalCalculation.map NetRules.delete;
val trans_add_local = mk_att LocalCalculation.map (Library.apfst o NetRules.insert);
val trans_del_local = mk_att LocalCalculation.map (Library.apfst o NetRules.delete);


(* concrete syntax *)

val trans_attr =
 (Attrib.add_del_args trans_add_global trans_del_global,
  Attrib.add_del_args trans_add_local trans_del_local);



(** proof commands **)

(* maintain calculation register *)

val calculationN = "calculation";

fun maintain_calculation false calc state =
      state
      |> put_calculation calc
      |> Proof.simple_have_thms calculationN calc
      |> Proof.reset_facts
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
    val strip_assums_concl = Logic.strip_assums_concl o #prop o Thm.rep_thm;
    val eq_prop = op aconv o pairself (Pattern.eta_contract o strip_assums_concl);
    fun projection ths th = Library.exists (Library.curry eq_prop th) ths;

    fun combine ths =
      (case opt_rules of Some rules => rules
      | None =>
          (case ths of [] => NetRules.rules (get_local_rules state)
          | th :: _ => NetRules.retrieve (get_local_rules state) (strip_assums_concl th)))
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

val setup = [GlobalCalculation.init, LocalCalculation.init,
  Attrib.add_attributes [("trans", trans_attr, "declaration of transitivity rule")],
  #1 o PureThy.add_thms [(("", transitive_thm), [trans_add_global])]];


end;
