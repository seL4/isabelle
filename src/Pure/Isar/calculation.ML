(*  Title:      Pure/Isar/calculation.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

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
  val also: thm list option -> (thm list -> unit) -> Proof.state -> Proof.state Seq.seq
  val finally: thm list option -> (thm list -> unit) -> Proof.state -> Proof.state Seq.seq
  val setup: (theory -> theory) list
end;

structure Calculation: CALCULATION =
struct


(** global and local calculation data **)

fun print_rules ths =
  Pretty.writeln (Pretty.big_list "calculation rules:" (map Display.pretty_thm ths));


(* theory data kind 'Isar/calculation' *)

structure GlobalCalculationArgs =
struct
  val name = "Isar/calculation";
  type T = thm list;

  val empty = [];
  val copy = I;
  val prep_ext = I;
  fun merge (ths1, ths2) = Library.generic_merge Thm.eq_thm I I ths1 ths2;
  fun print _ = print_rules;
end;

structure GlobalCalculation = TheoryDataFun(GlobalCalculationArgs);
val print_global_rules = GlobalCalculation.print;


(* proof data kind 'Isar/calculation' *)

structure LocalCalculationArgs =
struct
  val name = "Isar/calculation";
  type T = thm list * (thm list * int) option;

  fun init thy = (GlobalCalculation.get thy, None);
  fun print _ (ths, _) = print_rules ths;
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

local

fun add_trans thm rules = Library.gen_ins Thm.eq_thm (thm, rules);
fun del_trans thm rules = Library.gen_rem Thm.eq_thm (rules, thm);

fun mk_att f g (x, thm) = (f (g thm) x, thm);

in

val trans_add_global = mk_att GlobalCalculation.map add_trans;
val trans_del_global = mk_att GlobalCalculation.map del_trans;
val trans_add_local = mk_att LocalCalculation.map (Library.apfst o add_trans);
val trans_del_local = mk_att LocalCalculation.map (Library.apfst o del_trans);

end;


(* concrete syntax *)

val transN = "trans";
val addN = "add";
val delN = "del";

fun trans_att add del =
  Attrib.syntax (Scan.lift (Args.$$$ addN >> K add || Args.$$$ delN >> K del || Scan.succeed add));

val trans_attr =
  (trans_att trans_add_global trans_del_global, trans_att trans_add_local trans_del_local);



(** proof commands **)

val calculationN = "calculation";

fun calculate final opt_rules print state =
  let
    fun err_if b msg = if b then raise Proof.STATE (msg, state) else ();
    val facts = Proof.the_facts state;
    val rules = Seq.of_list (if_none opt_rules [] @ get_local_rules state);

    val eq_prop = op aconv o pairself (#prop o Thm.rep_thm);
    fun differ thms thms' = not (Library.equal_lists eq_prop (thms, thms'));
    fun combine thms =
      Seq.map Library.single (Seq.flat (Seq.map (Method.multi_resolve (thms @ facts)) rules));

    val (initial, calculations) =
      (case get_calculation state of
        None => (true, Seq.single facts)
      | Some thms => (false, Seq.filter (differ thms) (combine thms)))
  in
    err_if (initial andalso final) "No calculation yet";
    err_if (initial andalso is_some opt_rules) "Initial calculation -- no rules to be given";
    calculations |> Seq.map (fn calc =>
      (print calc;
        (if final then
          state
          |> reset_calculation
          |> Proof.reset_thms calculationN
          |> Proof.simple_have_thms "" calc
          |> Proof.chain
        else
          state
          |> put_calculation calc
          |> Proof.simple_have_thms calculationN calc
          |> Proof.reset_facts)))
  end;

fun also print = calculate false print;
fun finally print = calculate true print;



(** theory setup **)

val setup = [GlobalCalculation.init, LocalCalculation.init,
  Attrib.add_attributes [(transN, trans_attr, "transitivity rule")]];


end;
