(*  Title:      Pure/Isar/obtain.ML
    Author:     Markus Wenzel, TU Muenchen

The 'obtain' and 'guess' language elements -- generalized existence at
the level of proof texts: 'obtain' involves a proof that certain
fixes/assumes may be introduced into the present context; 'guess' is
similar, but derives these elements from the course of reasoning!

  <chain_facts>
  obtain x where "A x" <proof> ==

  have "!!thesis. (!!x. A x ==> thesis) ==> thesis"
  proof succeed
    fix thesis
    assume that [intro?]: "!!x. A x ==> thesis"
    <chain_facts>
    show thesis
      apply (insert that)
      <proof>
  qed
  fix x assm <<obtain_export>> "A x"


  <chain_facts>
  guess x <proof body> <proof end> ==

  {
    fix thesis
    <chain_facts> have "PROP ?guess"
      apply magic      -- {* turns goal into "thesis ==> #thesis" *}
      <proof body>
      apply_end magic  -- {* turns final "(!!x. P x ==> thesis) ==> #thesis" into
        "#((!!x. A x ==> thesis) ==> thesis)" which is a finished goal state *}
      <proof end>
  }
  fix x assm <<obtain_export>> "A x"
*)

signature OBTAIN =
sig
  val thatN: string
  val obtain: string -> (binding * string option * mixfix) list ->
    (Attrib.binding * (string * string list) list) list -> bool -> Proof.state -> Proof.state
  val obtain_i: string -> (binding * typ option * mixfix) list ->
    (Thm.binding * (term * term list) list) list -> bool -> Proof.state -> Proof.state
  val result: (Proof.context -> tactic) -> thm list -> Proof.context ->
    ((string * cterm) list * thm list) * Proof.context
  val guess: (binding * string option * mixfix) list -> bool -> Proof.state -> Proof.state
  val guess_i: (binding * typ option * mixfix) list -> bool -> Proof.state -> Proof.state
end;

structure Obtain: OBTAIN =
struct

(** obtain_export **)

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

fun eliminate fix_ctxt rule xs As thm =
  let
    val thy = ProofContext.theory_of fix_ctxt;

    val _ = eliminate_term fix_ctxt xs (Thm.full_prop_of thm);
    val _ = ObjectLogic.is_judgment thy (Thm.concl_of thm) orelse
      error "Conclusion in obtained context must be object-logic judgment";

    val ((_, [thm']), ctxt') = Variable.import true [thm] fix_ctxt;
    val prems = Drule.strip_imp_prems (#prop (Thm.crep_thm thm'));
  in
    ((Drule.implies_elim_list thm' (map Thm.assume prems)
        |> Drule.implies_intr_list (map Drule.norm_hhf_cterm As)
        |> Drule.forall_intr_list xs)
      COMP rule)
    |> Drule.implies_intr_list prems
    |> singleton (Variable.export ctxt' fix_ctxt)
  end;

fun obtain_export ctxt rule xs _ As =
  (eliminate ctxt rule xs As, eliminate_term ctxt xs);



(** obtain **)

fun bind_judgment ctxt name =
  let
    val (bind, ctxt') = ProofContext.bind_fixes [name] ctxt;
    val (t as _ $ Free v) = bind (ObjectLogic.fixed_judgment (ProofContext.theory_of ctxt) name);
  in ((v, t), ctxt') end;

val thatN = "that";

local

fun gen_obtain prep_att prep_vars prep_propp
    name raw_vars raw_asms int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val thy = Proof.theory_of state;
    val cert = Thm.cterm_of thy;
    val ctxt = Proof.context_of state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    (*obtain vars*)
    val (vars, vars_ctxt) = prep_vars raw_vars ctxt;
    val (_, fix_ctxt) = vars_ctxt |> ProofContext.add_fixes vars;
    val xs = map (Name.of_binding o #1) vars;

    (*obtain asms*)
    val (asms_ctxt, proppss) = prep_propp (fix_ctxt, map snd raw_asms);
    val asm_props = maps (map fst) proppss;
    val asms = map fst (Attrib.map_specs (prep_att thy) raw_asms) ~~ proppss;

    val _ = Variable.warn_extra_tfrees fix_ctxt asms_ctxt;

    (*obtain statements*)
    val thesisN = Name.variant xs AutoBind.thesisN;
    val (thesis_var, thesis) = #1 (bind_judgment fix_ctxt thesisN);

    val asm_frees = fold Term.add_frees asm_props [];
    val parms = xs |> map (fn x =>
      let val x' = ProofContext.get_skolem fix_ctxt x
      in (x', the_default propT (AList.lookup (op =) asm_frees x')) end);

    val that_name = if name = "" then thatN else name;
    val that_prop =
      Term.list_all_free (parms, Logic.list_implies (asm_props, thesis))
      |> Library.curry Logic.list_rename_params xs;
    val obtain_prop =
      Logic.list_rename_params ([AutoBind.thesisN],
        Term.list_all_free ([thesis_var], Logic.mk_implies (that_prop, thesis)));

    fun after_qed _ =
      Proof.local_qed (NONE, false)
      #> `Proof.the_fact #-> (fn rule =>
        Proof.fix_i vars
        #> Proof.assm_i (obtain_export fix_ctxt rule (map (cert o Free) parms)) asms);
  in
    state
    |> Proof.enter_forward
    |> Proof.have_i NONE (K I) [(Thm.empty_binding, [(obtain_prop, [])])] int
    |> Proof.proof (SOME Method.succeed_text) |> Seq.hd
    |> Proof.fix_i [(Binding.name thesisN, NONE, NoSyn)]
    |> Proof.assume_i
      [((Binding.name that_name, [ContextRules.intro_query NONE]), [(that_prop, [])])]
    |> `Proof.the_facts
    ||> Proof.chain_facts chain_facts
    ||> Proof.show_i NONE after_qed [(Thm.empty_binding, [(thesis, [])])] false
    |-> Proof.refine_insert
  end;

in

val obtain = gen_obtain Attrib.attribute ProofContext.read_vars ProofContext.read_propp;
val obtain_i = gen_obtain (K I) ProofContext.cert_vars ProofContext.cert_propp;

end;



(** tactical result **)

fun check_result ctxt thesis th =
  (case Thm.prems_of th of
    [prem] =>
      if Thm.concl_of th aconv thesis andalso
        Logic.strip_assums_concl prem aconv thesis then th
      else error ("Guessed a different clause:\n" ^ Display.string_of_thm ctxt th)
  | [] => error "Goal solved -- nothing guessed."
  | _ => error ("Guess split into several cases:\n" ^ Display.string_of_thm ctxt th));

fun result tac facts ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val ((thesis_var, thesis), thesis_ctxt) = bind_judgment ctxt AutoBind.thesisN;
    val rule =
      (case SINGLE (Method.insert_tac facts 1 THEN tac thesis_ctxt) (Goal.init (cert thesis)) of
        NONE => raise THM ("Obtain.result: tactic failed", 0, facts)
      | SOME th => check_result ctxt thesis (MetaSimplifier.norm_hhf (Goal.conclude th)));

    val closed_rule = Thm.forall_intr (cert (Free thesis_var)) rule;
    val ((_, [rule']), ctxt') = Variable.import false [closed_rule] ctxt;
    val obtain_rule = Thm.forall_elim (cert (Logic.varify (Free thesis_var))) rule';
    val ((params, stmt), fix_ctxt) = Variable.focus (Thm.cprem_of obtain_rule 1) ctxt';
    val (prems, ctxt'') =
      Assumption.add_assms (obtain_export fix_ctxt obtain_rule (map #2 params))
        (Drule.strip_imp_prems stmt) fix_ctxt;
  in ((params, prems), ctxt'') end;



(** guess **)

local

fun unify_params vars thesis_var raw_rule ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val certT = Thm.ctyp_of thy;
    val cert = Thm.cterm_of thy;
    val string_of_term = setmp show_types true (Syntax.string_of_term ctxt);

    fun err msg th = error (msg ^ ":\n" ^ Display.string_of_thm ctxt th);

    val maxidx = fold (Term.maxidx_typ o snd o fst) vars ~1;
    val rule = Thm.incr_indexes (maxidx + 1) raw_rule;

    val params = RuleCases.strip_params (Logic.nth_prem (1, Thm.prop_of rule));
    val m = length vars;
    val n = length params;
    val _ = m <= n orelse err "More variables than parameters in obtained rule" rule;

    fun unify ((x, T), (y, U)) (tyenv, max) = Sign.typ_unify thy (T, U) (tyenv, max)
      handle Type.TUNIFY =>
        err ("Failed to unify variable " ^
          string_of_term (Free (x, Envir.norm_type tyenv T)) ^ " against parameter " ^
          string_of_term (Syntax.mark_boundT (y, Envir.norm_type tyenv U)) ^ " in") rule;
    val (tyenv, _) = fold unify (map #1 vars ~~ Library.take (m, params))
      (Vartab.empty, Int.max (maxidx, Thm.maxidx_of rule));
    val norm_type = Envir.norm_type tyenv;

    val xs = map (apsnd norm_type o fst) vars;
    val ys = map (apsnd norm_type) (Library.drop (m, params));
    val ys' = map Name.internal (Name.variant_list (map fst xs) (map fst ys)) ~~ map #2 ys;
    val terms = map (Drule.mk_term o cert o Free) (xs @ ys');

    val instT =
      fold (Term.add_tvarsT o #2) params []
      |> map (TVar #> (fn T => (certT T, certT (norm_type T))));
    val closed_rule = rule
      |> Thm.forall_intr (cert (Free thesis_var))
      |> Thm.instantiate (instT, []);

    val ((_, rule' :: terms'), ctxt') = Variable.import false (closed_rule :: terms) ctxt;
    val vars' =
      map (dest_Free o Thm.term_of o Drule.dest_term) terms' ~~
      (map snd vars @ replicate (length ys) NoSyn);
    val rule'' = Thm.forall_elim (cert (Logic.varify (Free thesis_var))) rule';
  in ((vars', rule''), ctxt') end;

fun inferred_type (binding, _, mx) ctxt =
  let
    val x = Name.of_binding binding;
    val (T, ctxt') = ProofContext.inferred_param x ctxt
  in ((x, T, mx), ctxt') end;

fun polymorphic ctxt vars =
  let val Ts = map Logic.dest_type (Variable.polymorphic ctxt (map (Logic.mk_type o #2) vars))
  in map2 (fn (x, _, mx) => fn T => ((x, T), mx)) vars Ts end;

fun gen_guess prep_vars raw_vars int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val thy = Proof.theory_of state;
    val cert = Thm.cterm_of thy;
    val ctxt = Proof.context_of state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    val (thesis_var, thesis) = #1 (bind_judgment ctxt AutoBind.thesisN);
    val vars = ctxt |> prep_vars raw_vars |-> fold_map inferred_type |> fst |> polymorphic ctxt;

    fun guess_context raw_rule state' =
      let
        val ((parms, rule), ctxt') =
          unify_params vars thesis_var raw_rule (Proof.context_of state');
        val (bind, _) = ProofContext.bind_fixes (map (#1 o #1) parms) ctxt';
        val ts = map (bind o Free o #1) parms;
        val ps = map dest_Free ts;
        val asms =
          Logic.strip_assums_hyp (Logic.nth_prem (1, Thm.prop_of rule))
          |> map (fn asm => (Term.betapplys (Term.list_abs (ps, asm), ts), []));
        val _ = not (null asms) orelse error "Trivial result -- nothing guessed";
      in
        state'
        |> Proof.map_context (K ctxt')
        |> Proof.fix_i (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) parms)
        |> `Proof.context_of |-> (fn fix_ctxt => Proof.assm_i
          (obtain_export fix_ctxt rule (map cert ts)) [(Thm.empty_binding, asms)])
        |> Proof.bind_terms AutoBind.no_facts
      end;

    val goal = Var (("guess", 0), propT);
    fun print_result ctxt' (k, [(s, [_, th])]) =
      ProofDisplay.print_results int ctxt' (k, [(s, [th])]);
    val before_qed = SOME (Method.primitive_text (Goal.conclude #> MetaSimplifier.norm_hhf #>
        (fn th => Goal.protect (Conjunction.intr (Drule.mk_term (Thm.cprop_of th)) th))));
    fun after_qed [[_, res]] =
      Proof.end_block #> guess_context (check_result ctxt thesis res);
  in
    state
    |> Proof.enter_forward
    |> Proof.begin_block
    |> Proof.fix_i [(Binding.name AutoBind.thesisN, NONE, NoSyn)]
    |> Proof.chain_facts chain_facts
    |> Proof.local_goal print_result (K I) (apsnd (rpair I))
      "guess" before_qed after_qed [(Thm.empty_binding, [Logic.mk_term goal, goal])]
    |> Proof.refine (Method.primitive_text (K (Goal.init (cert thesis)))) |> Seq.hd
  end;

in

val guess = gen_guess ProofContext.read_vars;
val guess_i = gen_guess ProofContext.cert_vars;

end;

end;
