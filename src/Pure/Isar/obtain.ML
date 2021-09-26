(*  Title:      Pure/Isar/obtain.ML
    Author:     Markus Wenzel, TU Muenchen

Generalized existence and cases rules within Isar proof text.
*)

signature OBTAIN =
sig
  val obtain_export: Proof.context -> thm -> cterm list -> Assumption.export
  val obtain_thesis: Proof.context -> ((string * typ) * term) * Proof.context
  val obtains_attributes: ('typ, 'term) Element.obtain list -> attribute list
  val obtains_attribs: ('typ, 'term) Element.obtain list -> Token.src list
  val read_obtains: Proof.context -> term -> Element.obtains -> (binding * term) list
  val cert_obtains: Proof.context -> term -> Element.obtains_i -> (binding * term) list
  val parse_obtains: Proof.context -> term -> Element.obtains -> (binding * term) list
  val consider: Element.obtains_i -> bool -> Proof.state -> Proof.state
  val consider_cmd: Element.obtains -> bool -> Proof.state -> Proof.state
  val obtain: binding -> (binding * typ option * mixfix) list ->
    (binding * typ option * mixfix) list -> (term * term list) list list ->
    (Thm.binding * (term * term list) list) list -> bool -> Proof.state -> Proof.state
  val obtain_cmd: binding -> (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list -> (string * string list) list list ->
    (Attrib.binding * (string * string list) list) list -> bool -> Proof.state -> Proof.state
  val check_result: Proof.context -> term -> thm -> thm
  val result: (Proof.context -> tactic) -> thm list -> Proof.context ->
    ((string * cterm) list * thm list) * Proof.context
end;

structure Obtain: OBTAIN =
struct

(** specification elements **)

(* obtain_export *)

(*
  [x, A x]
     :
     B
  --------
     B
*)
fun eliminate_term ctxt xs tm =
  let
    val vs = map (dest_Free o Thm.term_of) xs;
    val bads = Term.fold_aterms (fn t as Free v =>
      if member (op =) vs v then insert (op aconv) t else I | _ => I) tm [];
    val _ = null bads orelse
      error ("Result contains obtained parameters: " ^
        space_implode " " (map (Syntax.string_of_term ctxt) bads));
  in tm end;

fun eliminate ctxt rule xs As thm =
  let
    val _ = eliminate_term ctxt xs (Thm.full_prop_of thm);
    val _ = Object_Logic.is_judgment ctxt (Thm.concl_of thm) orelse
      error "Conclusion in obtained context must be object-logic judgment";

    val ((_, [thm']), ctxt') = Variable.import true [thm] ctxt;
    val prems = Drule.strip_imp_prems (Thm.cprop_of thm');
  in
    ((Drule.implies_elim_list thm' (map Thm.assume prems)
        |> Drule.implies_intr_list (map (Drule.norm_hhf_cterm ctxt') As)
        |> Drule.forall_intr_list xs)
      COMP rule)
    |> Drule.implies_intr_list prems
    |> singleton (Variable.export ctxt' ctxt)
  end;

fun obtain_export ctxt rule xs _ As =
  (eliminate ctxt rule xs As, eliminate_term ctxt xs);


(* result declaration *)

fun case_names (obtains: ('typ, 'term) Element.obtain list) =
  obtains |> map_index (fn (i, (b, _)) =>
    if Binding.is_empty b then string_of_int (i + 1) else Name_Space.base_name b);

fun obtains_attributes obtains =
  [Rule_Cases.consumes (~ (length obtains)), Rule_Cases.case_names (case_names obtains)];

fun obtains_attribs obtains =
  [Attrib.consumes (~ (length obtains)), Attrib.case_names (case_names obtains)];


(* obtain thesis *)

fun obtain_thesis ctxt =
  let
    val ([x], ctxt') =
      Proof_Context.add_fixes [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)] ctxt;
    val t = Object_Logic.fixed_judgment ctxt x;
    val v = dest_Free (Object_Logic.drop_judgment ctxt t);
  in ((v, t), ctxt') end;


(* obtain clauses *)

local

val mk_all_external = Logic.all_constraint o Variable.default_type;

fun mk_all_internal ctxt (y, z) t =
  let
    val frees = Frees.build (t |> Term.fold_aterms (fn Free v => Frees.add_set v | _ => I));
    val T =
      (case Frees.get_first (fn ((x, T), _) => if x = z then SOME T else NONE) frees of
        SOME T => T
      | NONE => the_default dummyT (Variable.default_type ctxt z));
  in Logic.all_const T $ Term.lambda_name (y, Free (z, T)) t end;

fun prepare_clause prep_var parse_prop mk_all ctxt thesis raw_vars raw_props =
  let
    val ((xs', vars), ctxt') = ctxt
      |> fold_map prep_var raw_vars
      |-> (fn vars => Proof_Context.add_fixes vars ##>> pair vars);
    val xs = map (Variable.check_name o #1) vars;
  in
    Logic.list_implies (map (parse_prop ctxt') raw_props, thesis)
    |> fold_rev (mk_all ctxt') (xs ~~ xs')
  end;

fun prepare_obtains prep_clause check_terms
    ctxt thesis (raw_obtains: ('typ, 'term) Element.obtain list) =
  let
    val clauses = raw_obtains
      |> map (fn (_, (raw_vars, raw_props)) => prep_clause ctxt thesis raw_vars raw_props)
      |> check_terms ctxt;
  in map fst raw_obtains ~~ clauses end;

val parse_clause = prepare_clause Proof_Context.read_var Syntax.parse_prop mk_all_external;
val cert_clause = prepare_clause Proof_Context.cert_var (K I) mk_all_internal;

in

val read_obtains = prepare_obtains parse_clause Syntax.check_terms;
val cert_obtains = prepare_obtains cert_clause (K I);
val parse_obtains = prepare_obtains parse_clause (K I);

end;



(** consider: generalized elimination and cases rule **)

(*
  consider (a) x where "A x" | (b) y where "B y" | ... \<equiv>

  have thesis
    if a [intro?]: "\<And>x. A x \<Longrightarrow> thesis"
    and b [intro?]: "\<And>y. B y \<Longrightarrow> thesis"
    and ...
    for thesis
    apply (insert that)
*)

local

fun gen_consider prep_obtains raw_obtains int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val ctxt = Proof.context_of state;

    val ((_, thesis), thesis_ctxt) = obtain_thesis ctxt;
    val obtains = prep_obtains thesis_ctxt thesis raw_obtains;
    val atts = Rule_Cases.cases_open :: obtains_attributes raw_obtains;
  in
    state
    |> Proof.have true NONE (K I)
      [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)]
      (map (fn (a, A) => ((a, [Context_Rules.intro_query NONE]), [(A, [])])) obtains)
      [((Binding.empty, atts), [(thesis, [])])] int
    |-> Proof.refine_insert
  end;

in

val consider = gen_consider cert_obtains;
val consider_cmd = gen_consider read_obtains;

end;



(** obtain: augmented context based on generalized existence rule **)

(*
  obtain (a) x where "A x" <proof> \<equiv>

  have thesis if a [intro?]: "\<And>x. A x \<Longrightarrow> thesis" for thesis
    apply (insert that)
    <proof>
  fix x assm <<obtain_export>> "A x"
*)

local

fun gen_obtain prep_stmt prep_att that_binding raw_decls raw_fixes raw_prems raw_concls int state =
  let
    val _ = Proof.assert_forward_or_chain state;

    val ((_, thesis), thesis_ctxt) = obtain_thesis (Proof.context_of state);

    val ({vars, propss, binds, result_binds, ...}, params_ctxt) =
      prep_stmt (raw_decls @ raw_fixes) (raw_prems @ map #2 raw_concls) thesis_ctxt;
    val (decls, fixes) = chop (length raw_decls) vars ||> map #2;
    val (premss, conclss) = chop (length raw_prems) propss;
    val propss' = (map o map) (Logic.close_prop fixes (flat premss)) conclss;

    val that_prop =
      Logic.list_rename_params (map (#1 o #2) decls)
        (fold_rev (Logic.all o #2 o #2) decls (Logic.list_implies (flat propss', thesis)));

    val cparams = map (Thm.cterm_of params_ctxt o #2 o #2) decls;
    val asms =
      map (fn ((b, raw_atts), _) => (b, map (prep_att params_ctxt) raw_atts)) raw_concls ~~
      map (map (rpair [])) propss';

    fun after_qed (result_ctxt, results) state' =
      let val [rule] = Proof_Context.export result_ctxt (Proof.context_of state') (flat results) in
        state'
        |> Proof.fix (map #1 decls)
        |> Proof.map_context (fold (Variable.bind_term o apsnd (Logic.close_term fixes)) binds)
        |> Proof.assm (obtain_export params_ctxt rule cparams) [] [] asms
      end;
  in
    state
    |> Proof.have true NONE after_qed
      [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)]
      [((that_binding, [Context_Rules.intro_query NONE]), [(that_prop, [])])]
      [(Binding.empty_atts, [(thesis, [])])] int
    |-> Proof.refine_insert
    |> Proof.map_context (fold Variable.bind_term result_binds)
  end;

in

val obtain = gen_obtain Proof_Context.cert_stmt (K I);
val obtain_cmd = gen_obtain Proof_Context.read_stmt Attrib.attribute_cmd;

end;



(** tactical result **)

fun check_result ctxt thesis th =
  (case Thm.prems_of th of
    [prem] =>
      if Thm.concl_of th aconv thesis andalso
        Logic.strip_assums_concl prem aconv thesis then th
      else error ("Guessed a different clause:\n" ^ Thm.string_of_thm ctxt th)
  | [] => error "Goal solved -- nothing guessed"
  | _ => error ("Guess split into several cases:\n" ^ Thm.string_of_thm ctxt th));

fun result tac facts ctxt =
  let
    val ((thesis_var, thesis), thesis_ctxt) = obtain_thesis ctxt;
    val st = Goal.init (Thm.cterm_of ctxt thesis);
    val rule =
      (case SINGLE (Method.insert_tac thesis_ctxt facts 1 THEN tac thesis_ctxt) st of
        NONE => raise THM ("Obtain.result: tactic failed", 0, facts)
      | SOME th =>
          check_result thesis_ctxt thesis (Raw_Simplifier.norm_hhf thesis_ctxt (Goal.conclude th)));

    val closed_rule = Thm.forall_intr (Thm.cterm_of ctxt (Free thesis_var)) rule;
    val ((_, [rule']), ctxt') = Variable.import false [closed_rule] ctxt;
    val obtain_rule =
      Thm.forall_elim (Thm.cterm_of ctxt (Logic.varify_global (Free thesis_var))) rule';
    val ((params, stmt), fix_ctxt) = Variable.focus_cterm NONE (Thm.cprem_of obtain_rule 1) ctxt';
    val (prems, ctxt'') =
      Assumption.add_assms (obtain_export fix_ctxt obtain_rule (map #2 params))
        (Drule.strip_imp_prems stmt) fix_ctxt;
  in ((params, prems), ctxt'') end;

end;
