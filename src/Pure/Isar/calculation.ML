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
  val also: (thm -> unit) -> Proof.state -> Proof.state Seq.seq
  val finally: (thm -> unit) -> Proof.state -> Proof.state Seq.seq
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
  type T = thm list * (thm * int) option;

  fun init thy = (GlobalCalculation.get thy, None);
  fun print _ (ths, _) = print_rules ths;
end;

structure LocalCalculation = ProofDataFun(LocalCalculationArgs);
val get_local_rules = #1 o LocalCalculation.get o Proof.context_of;
val print_local_rules = LocalCalculation.print;


(* access calculation *)

fun get_calculation state =
  (case #2 (LocalCalculation.get (Proof.context_of state)) of
    None => None
  | Some (thm, lev) => if lev = Proof.level state then Some thm else None);

fun put_calculation thm state =
  LocalCalculation.put_st (get_local_rules state, Some (thm, Proof.level state)) state;



(** attributes **)

(* trans add/del *)

local

fun map_rules_global f thy = GlobalCalculation.put (f (GlobalCalculation.get thy)) thy;
fun map_rules_local f ctxt = LocalCalculation.put (f (LocalCalculation.get ctxt)) ctxt;

fun add_trans thm rules = Library.gen_ins Thm.eq_thm (thm, rules);
fun del_trans thm rules = Library.gen_rem Thm.eq_thm (rules, thm);

fun mk_att f g (x, thm) = (f (g thm) x, thm);

in

val trans_add_global = mk_att map_rules_global add_trans;
val trans_del_global = mk_att map_rules_global del_trans;
val trans_add_local = mk_att map_rules_local (Library.apfst o add_trans);
val trans_del_local = mk_att map_rules_local (Library.apfst o del_trans);

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

fun dest_arg tm =
  (case ObjectLogic.dest_main_statement tm of
    _ $ t => t
  | _ => raise TERM ("dest_arg", [tm]));

val calculationN = "calculation";

fun calculate final print state =
  let
    val fact = Proof.the_fact state;
    val dddot = dest_arg (#prop (Thm.rep_thm fact)) handle TERM _ =>
      raise Proof.STATE ("Unable to bind '...' pattern from current fact", state);

    val name = if final then "" else calculationN;
    fun have_thm thm = Proof.have_thmss name [] [([thm], [])];

    val rules = Seq.of_list (get_local_rules state);
    val calculations =
      (case get_calculation state of
        None => Seq.single fact
      | Some thm => Seq.flat (Seq.map (Method.multi_resolve [thm, fact]) rules));
  in
    calculations |> Seq.map (fn calc =>
      (print calc;
        state
        |> Proof.bind_i [(Syntax.dddot_indexname, dddot)]
        |> put_calculation calc
        |> have_thm calc
        |> (if final then Proof.chain else Proof.reset_facts)))
  end;

fun also print = calculate false print;
fun finally print = calculate true print;



(** theory setup **)

val setup = [GlobalCalculation.init, LocalCalculation.init,
  Attrib.add_attributes [(transN, trans_attr, "transitivity rule")]];


end;
