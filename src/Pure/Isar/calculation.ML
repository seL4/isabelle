(*  Title:      Pure/Isar/calculation.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic calculational proofs.
*)

signature CALCULATION =
sig
  val print_rules: Context.generic -> unit
  val get_calculation: Proof.state -> thm list option
  val trans_add: Context.generic attribute
  val trans_del: Context.generic attribute
  val sym_add: Context.generic attribute
  val sym_del: Context.generic attribute
  val symmetric: Context.generic attribute
  val also: (thmref * Attrib.src list) list option -> bool -> Proof.state -> Proof.state Seq.seq
  val also_i: thm list option -> bool -> Proof.state -> Proof.state Seq.seq
  val finally: (thmref * Attrib.src list) list option -> bool -> Proof.state -> Proof.state Seq.seq
  val finally_i: thm list option -> bool -> Proof.state -> Proof.state Seq.seq
  val moreover: bool -> Proof.state -> Proof.state
  val ultimately: bool -> Proof.state -> Proof.state
end;

structure Calculation: CALCULATION =
struct

(** calculation data **)

structure CalculationData = GenericDataFun
(
  val name = "Isar/calculation";
  type T = (thm NetRules.T * thm list) * (thm list * int) option;
  val empty = ((NetRules.elim, []), NONE);
  val extend = I;

  fun merge _ (((trans1, sym1), _), ((trans2, sym2), _)) =
    ((NetRules.merge (trans1, trans2), Drule.merge_rules (sym1, sym2)), NONE);

  fun print generic ((trans, sym), _) =
    let val ctxt = Context.proof_of generic in
      [Pretty.big_list "transitivity rules:"
          (map (ProofContext.pretty_thm ctxt) (NetRules.rules trans)),
        Pretty.big_list "symmetry rules:" (map (ProofContext.pretty_thm ctxt) sym)]
      |> Pretty.chunks |> Pretty.writeln
    end;
);

val _ = Context.add_setup [CalculationData.init];
val print_rules = CalculationData.print;


(* access calculation *)

fun get_calculation state =
  (case #2 (CalculationData.get (Context.Proof (Proof.context_of state))) of
    NONE => NONE
  | SOME (thms, lev) => if lev = Proof.level state then SOME thms else NONE);

val calculationN = "calculation";

fun put_calculation calc =
  `Proof.level #-> (fn lev =>
    Proof.map_context (Context.the_proof o
        CalculationData.map (apsnd (K (Option.map (rpair lev) calc))) o Context.Proof))
  #> Proof.put_thms (calculationN, calc);



(** attributes **)

(* add/del rules *)

val trans_add = Attrib.declaration (CalculationData.map o apfst o apfst o NetRules.insert);
val trans_del = Attrib.declaration (CalculationData.map o apfst o apfst o NetRules.delete);

val sym_add =
  Attrib.declaration (CalculationData.map o apfst o apsnd o Drule.add_rule)
  #> ContextRules.elim_query NONE;
val sym_del =
  Attrib.declaration (CalculationData.map o apfst o apsnd o Drule.del_rule)
  #> ContextRules.rule_del;


(* symmetric *)

val symmetric = Attrib.rule (fn x => fn th =>
  (case Seq.chop (2, Drule.multi_resolves [th] (#2 (#1 (CalculationData.get x)))) of
    ([th'], _) => th'
  | ([], _) => raise THM ("symmetric: no unifiers", 1, [th])
  | _ => raise THM ("symmetric: multiple unifiers", 1, [th])));


(* concrete syntax *)

val trans_att = Attrib.add_del_args trans_add trans_del;
val sym_att = Attrib.add_del_args sym_add sym_del;

val _ = Context.add_setup
 [Attrib.add_attributes
   [("trans", Attrib.common trans_att, "declaration of transitivity rule"),
    ("sym", Attrib.common sym_att, "declaration of symmetry rule"),
    ("symmetric", Attrib.common (Attrib.no_args symmetric), "resolution with symmetry rule")],
  snd o PureThy.add_thms
   [(("", transitive_thm), [Attrib.theory trans_add]),
    (("", symmetric_thm), [Attrib.theory sym_add])]];



(** proof commands **)

fun err_if b msg = if b then error msg else ();

fun assert_sane final =
  if final then Proof.assert_forward else Proof.assert_forward_or_chain;

fun maintain_calculation false calc = put_calculation (SOME calc)
  | maintain_calculation true calc = put_calculation NONE #> Proof.chain_facts calc;

fun print_calculation false _ _ = ()
  | print_calculation true ctxt calc =
      Pretty.writeln (ProofContext.pretty_fact ctxt (calculationN, calc));


(* also and finally *)

val get_rules = #1 o CalculationData.get o Context.Proof o Proof.context_of;

fun calculate prep_rules final raw_rules int state =
  let
    val strip_assums_concl = Logic.strip_assums_concl o Thm.prop_of;
    val eq_prop = op aconv o pairself (Pattern.eta_contract o strip_assums_concl);
    fun projection ths th = Library.exists (Library.curry eq_prop th) ths;

    val opt_rules = Option.map (prep_rules state) raw_rules;
    fun combine ths =
      (case opt_rules of SOME rules => rules
      | NONE =>
          (case ths of [] => NetRules.rules (#1 (get_rules state))
          | th :: _ => NetRules.retrieve (#1 (get_rules state)) (strip_assums_concl th)))
      |> Seq.of_list |> Seq.maps (Drule.multi_resolve ths)
      |> Seq.filter (not o projection ths);

    val facts = Proof.the_facts (assert_sane final state);
    val (initial, calculations) =
      (case get_calculation state of
        NONE => (true, Seq.single facts)
      | SOME calc => (false, Seq.map single (combine (calc @ facts))));
  in
    err_if (initial andalso final) "No calculation yet";
    err_if (initial andalso is_some opt_rules) "Initial calculation -- no rules to be given";
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
    err_if (initial andalso final) "No calculation yet";
    print_calculation int (Proof.context_of state) calc;
    state |> maintain_calculation final calc
  end;

val moreover = collect false;
val ultimately = collect true;

end;
