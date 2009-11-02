(*  Title:      Pure/Isar/calculation.ML
    Author:     Markus Wenzel, TU Muenchen

Generic calculational proofs.
*)

signature CALCULATION =
sig
  val print_rules: Proof.context -> unit
  val get_calculation: Proof.state -> thm list option
  val trans_add: attribute
  val trans_del: attribute
  val sym_add: attribute
  val sym_del: attribute
  val symmetric: attribute
  val also: (Facts.ref * Attrib.src list) list option -> bool -> Proof.state -> Proof.state Seq.seq
  val also_i: thm list option -> bool -> Proof.state -> Proof.state Seq.seq
  val finally: (Facts.ref * Attrib.src list) list option -> bool ->
    Proof.state -> Proof.state Seq.seq
  val finally_i: thm list option -> bool -> Proof.state -> Proof.state Seq.seq
  val moreover: bool -> Proof.state -> Proof.state
  val ultimately: bool -> Proof.state -> Proof.state
end;

structure Calculation: CALCULATION =
struct

(** calculation data **)

structure CalculationData = GenericDataFun
(
  type T = (thm Item_Net.T * thm list) * (thm list * int) option;
  val empty = ((Thm.elim_rules, []), NONE);
  val extend = I;

  fun merge _ (((trans1, sym1), _), ((trans2, sym2), _)) =
    ((Item_Net.merge (trans1, trans2), Thm.merge_thms (sym1, sym2)), NONE);
);

fun print_rules ctxt =
  let val ((trans, sym), _) = CalculationData.get (Context.Proof ctxt) in
    [Pretty.big_list "transitivity rules:"
        (map (Display.pretty_thm ctxt) (Item_Net.content trans)),
      Pretty.big_list "symmetry rules:" (map (Display.pretty_thm ctxt) sym)]
    |> Pretty.chunks |> Pretty.writeln
  end;


(* access calculation *)

fun get_calculation state =
  (case #2 (CalculationData.get (Context.Proof (Proof.context_of state))) of
    NONE => NONE
  | SOME (thms, lev) => if lev = Proof.level state then SOME thms else NONE);

val calculationN = "calculation";

fun put_calculation calc =
  `Proof.level #-> (fn lev => Proof.map_context (Context.proof_map
     (CalculationData.map (apsnd (K (Option.map (rpair lev) calc))))))
  #> Proof.put_thms false (calculationN, calc);



(** attributes **)

(* add/del rules *)

val trans_add = Thm.declaration_attribute (CalculationData.map o apfst o apfst o Item_Net.update);
val trans_del = Thm.declaration_attribute (CalculationData.map o apfst o apfst o Item_Net.remove);

val sym_add =
  Thm.declaration_attribute (CalculationData.map o apfst o apsnd o Thm.add_thm)
  #> Context_Rules.elim_query NONE;

val sym_del =
  Thm.declaration_attribute (CalculationData.map o apfst o apsnd o Thm.del_thm)
  #> Context_Rules.rule_del;


(* symmetric *)

val symmetric = Thm.rule_attribute (fn x => fn th =>
  (case Seq.chop 2 (Drule.multi_resolves [th] (#2 (#1 (CalculationData.get x)))) of
    ([th'], _) => Drule.zero_var_indexes th'
  | ([], _) => raise THM ("symmetric: no unifiers", 1, [th])
  | _ => raise THM ("symmetric: multiple unifiers", 1, [th])));


(* concrete syntax *)

val _ = Context.>> (Context.map_theory
 (Attrib.setup (Binding.name "trans") (Attrib.add_del trans_add trans_del)
    "declaration of transitivity rule" #>
  Attrib.setup (Binding.name "sym") (Attrib.add_del sym_add sym_del)
    "declaration of symmetry rule" #>
  Attrib.setup (Binding.name "symmetric") (Scan.succeed symmetric)
    "resolution with symmetry rule" #>
  PureThy.add_thms
   [((Binding.empty, transitive_thm), [trans_add]),
    ((Binding.empty, symmetric_thm), [sym_add])] #> snd));



(** proof commands **)

fun err_if b msg = if b then error msg else ();

fun assert_sane final =
  if final then Proof.assert_forward else Proof.assert_forward_or_chain;

fun maintain_calculation false calc = put_calculation (SOME calc)
  | maintain_calculation true calc = put_calculation NONE #> Proof.chain_facts calc;

fun print_calculation false _ _ = ()
  | print_calculation true ctxt calc = Pretty.writeln
      (ProofContext.pretty_fact ctxt (ProofContext.full_name ctxt (Binding.name calculationN), calc));


(* also and finally *)

val get_rules = #1 o CalculationData.get o Context.Proof o Proof.context_of;

fun calculate prep_rules final raw_rules int state =
  let
    val strip_assums_concl = Logic.strip_assums_concl o Thm.prop_of;
    val eq_prop = op aconv o pairself (Envir.beta_eta_contract o strip_assums_concl);
    fun projection ths th = Library.exists (Library.curry eq_prop th) ths;

    val opt_rules = Option.map (prep_rules state) raw_rules;
    fun combine ths =
      (case opt_rules of SOME rules => rules
      | NONE =>
          (case ths of
            [] => Item_Net.content (#1 (get_rules state))
          | th :: _ => Item_Net.retrieve (#1 (get_rules state)) (strip_assums_concl th)))
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
