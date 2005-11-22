(*  Title:      Pure/Isar/calculation.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic calculational proofs.
*)

signature CALCULATION =
sig
  val get_calculation: Proof.state -> thm list option
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
  val also: (thmref * Attrib.src list) list option -> bool -> Proof.state -> Proof.state Seq.seq
  val also_i: thm list option -> bool -> Proof.state -> Proof.state Seq.seq
  val finally: (thmref * Attrib.src list) list option -> bool ->
    Proof.state -> Proof.state Seq.seq
  val finally_i: thm list option -> bool -> Proof.state -> Proof.state Seq.seq
  val moreover: bool -> Proof.state -> Proof.state
  val ultimately: bool -> Proof.state -> Proof.state
end;

structure Calculation: CALCULATION =
struct

(** global and local calculation data **)

(* global calculation *)

fun print_rules prt x (trans, sym) =
  [Pretty.big_list "transitivity rules:" (map (prt x) (NetRules.rules trans)),
    Pretty.big_list "symmetry rules:" (map (prt x) sym)]
  |> Pretty.chunks |> Pretty.writeln;

structure GlobalCalculation = TheoryDataFun
(struct
  val name = "Isar/calculation";
  type T = thm NetRules.T * thm list

  val empty = (NetRules.elim, []);
  val copy = I;
  val extend = I;
  fun merge _ ((trans1, sym1), (trans2, sym2)) =
    (NetRules.merge (trans1, trans2), Drule.merge_rules (sym1, sym2));
  val print = print_rules Display.pretty_thm_sg;
end);

val _ = Context.add_setup [GlobalCalculation.init];
val print_global_rules = GlobalCalculation.print;


(* local calculation *)

structure LocalCalculation = ProofDataFun
(struct
  val name = "Isar/calculation";
  type T = (thm NetRules.T * thm list) * (thm list * int) option;

  fun init thy = (GlobalCalculation.get thy, NONE);
  fun print ctxt (rs, _) = print_rules ProofContext.pretty_thm ctxt rs;
end);

val _ = Context.add_setup [LocalCalculation.init];
val get_local_rules = #1 o LocalCalculation.get o Proof.context_of;
val print_local_rules = LocalCalculation.print;


(* access calculation *)

fun get_calculation state =
  (case #2 (LocalCalculation.get (Proof.context_of state)) of
    NONE => NONE
  | SOME (thms, lev) => if lev = Proof.level state then SOME thms else NONE);

val calculationN = "calculation";

fun put_calculation calc =
  `Proof.level #-> (fn lev => Proof.map_context
    (LocalCalculation.map (apsnd (K (Option.map (rpair lev) calc)))))
  #> Proof.put_thms (calculationN, calc);


(** attributes **)

(* add/del rules *)

fun global_att f (x, thm) = (GlobalCalculation.map (f thm) x, thm);
fun local_att f (x, thm) = (LocalCalculation.map (apfst (f thm)) x, thm);

val trans_add_global = global_att (apfst o NetRules.insert);
val trans_del_global = global_att (apfst o NetRules.delete);
val trans_add_local = local_att (apfst o NetRules.insert);
val trans_del_local = local_att (apfst o NetRules.delete);

val sym_add_global = global_att (apsnd o Drule.add_rule) o ContextRules.elim_query_global NONE;
val sym_del_global = global_att (apsnd o Drule.del_rule) o ContextRules.rule_del_global;
val sym_add_local = local_att (apsnd o Drule.add_rule) o ContextRules.elim_query_local NONE;
val sym_del_local = local_att (apsnd o Drule.del_rule) o ContextRules.rule_del_local;


(* symmetry *)

fun gen_symmetric get_sym = Drule.rule_attribute (fn x => fn th =>
  (case Seq.chop (2, Drule.multi_resolves [th] (get_sym x)) of
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

val _ = Context.add_setup
 [Attrib.add_attributes
   [("trans", trans_attr, "declaration of transitivity rule"),
    ("sym", sym_attr, "declaration of symmetry rule"),
    ("symmetric", (Attrib.no_args symmetric_global, Attrib.no_args symmetric_local),
      "resolution with symmetry rule")],
  #1 o PureThy.add_thms
   [(("", transitive_thm), [trans_add_global]),
    (("", symmetric_thm), [sym_add_global])]];



(** proof commands **)

fun err_if state b msg = if b then raise Proof.STATE (msg, state) else ();

fun assert_sane final =
  if final then Proof.assert_forward else Proof.assert_forward_or_chain;

fun maintain_calculation false calc = put_calculation (SOME calc)
  | maintain_calculation true calc = put_calculation NONE #> Proof.chain_facts calc;

fun print_calculation false _ _ = ()
  | print_calculation true ctxt calc =
      Pretty.writeln (ProofContext.pretty_fact ctxt (calculationN, calc));


(* also and finally *)

fun calculate prep_rules final raw_rules int state =
  let
    val strip_assums_concl = Logic.strip_assums_concl o Thm.prop_of;
    val eq_prop = op aconv o pairself (Pattern.eta_contract o strip_assums_concl);
    fun projection ths th = Library.exists (Library.curry eq_prop th) ths;

    val opt_rules = Option.map (prep_rules state) raw_rules;
    fun combine ths =
      (case opt_rules of SOME rules => rules
      | NONE =>
          (case ths of [] => NetRules.rules (#1 (get_local_rules state))
          | th :: _ => NetRules.retrieve (#1 (get_local_rules state)) (strip_assums_concl th)))
      |> Seq.of_list |> Seq.maps (Drule.multi_resolve ths)
      |> Seq.filter (not o projection ths);

    val facts = Proof.the_facts (assert_sane final state);
    val (initial, calculations) =
      (case get_calculation state of
        NONE => (true, Seq.single facts)
      | SOME calc => (false, Seq.map single (combine (calc @ facts))));
  in
    err_if state (initial andalso final) "No calculation yet";
    err_if state (initial andalso is_some opt_rules) "Initial calculation -- no rules to be given";
    calculations |> Seq.map (fn calc => (print_calculation int (Proof.context_of state) calc;
        state |> maintain_calculation final calc))
  end;

val also = calculate Proof.get_thmss false;
val also_i = calculate (K I) false;
val finally = calculate Proof.get_thmss true;
val finally_i = calculate (K I) true;


(* moreover and ultimately *)

fun collect final int state =
  let
    val facts = Proof.the_facts (assert_sane final state);
    val (initial, thms) =
      (case get_calculation state of
        NONE => (true, [])
      | SOME thms => (false, thms));
    val calc = thms @ facts;
  in
    err_if state (initial andalso final) "No calculation yet";
    print_calculation int (Proof.context_of state) calc;
    state |> maintain_calculation final calc
  end;

val moreover = collect false;
val ultimately = collect true;

end;
