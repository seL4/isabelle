(*  Title:      Pure/Isar/obtain.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The 'obtain' and 'guess' language elements -- generalized existence at
the level of proof texts: 'obtain' involves a proof that certain
fixes/assumes may be introduced into the present context; 'guess' is
similar, but derives these elements from the course of reasoning!

  <chain_facts>
  obtain x where "P x" <proof> ==

  have "!!thesis. (!!x. P x ==> thesis) ==> thesis"
  proof succeed
    fix thesis
    assume that [intro?]: "!!x. P x ==> thesis"
    <chain_facts> show thesis <proof (insert that)>
  qed
  fix x assm (obtained) "P x"


  <chain_facts>
  guess x <proof body> <proof end> ==

  {
    fix thesis
    <chain_facts> have "PROP ?guess"
      apply magic      -- {* turns goal into "thesis ==> Goal thesis" *}
      <proof body>
      apply_end magic  -- {* turns final "(!!x. P x ==> thesis) ==> Goal thesis" into
        "Goal ((!!x. P x ==> thesis) ==> thesis)" which is a finished goal state *}
      <proof end>
  }
  fix x assm (obtained) "P x"
*)

signature OBTAIN =
sig
  val obtain: (string list * string option) list ->
    ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> bool -> Proof.state -> Proof.state
  val obtain_i: (string list * typ option) list ->
    ((string * Proof.context attribute list) * (term * (term list * term list)) list) list
    -> bool -> Proof.state -> Proof.state
  val guess: (string list * string option) list -> bool -> Proof.state -> Proof.state
  val guess_i: (string list * typ option) list -> bool -> Proof.state -> Proof.state
end;

structure Obtain: OBTAIN =
struct

(** export_obtained **)

fun export_obtained state parms rule cprops thm =
  let
    val {thy, prop, maxidx, ...} = Thm.rep_thm thm;
    val cparms = map (Thm.cterm_of thy) parms;

    val thm' = thm
      |> Drule.implies_intr_protected cprops
      |> Drule.forall_intr_list cparms
      |> Drule.forall_elim_vars (maxidx + 1);
    val elim_tacs = replicate (length cprops) (Tactic.etac Drule.protectI);

    val concl = Logic.strip_assums_concl prop;
    val bads = parms inter (Term.term_frees concl);
  in
    if not (null bads) then
      raise Proof.STATE ("Conclusion contains obtained parameters: " ^
        space_implode " " (map (ProofContext.string_of_term (Proof.context_of state)) bads), state)
    else if not (ObjectLogic.is_judgment thy concl) then
      raise Proof.STATE ("Conclusion in obtained context must be object-logic judgments", state)
    else (Tactic.rtac thm' THEN' RANGE elim_tacs) 1 rule
  end;



(** obtain **)

fun bind_judgment ctxt name =
  let val (t as _ $ Free v) =
    ObjectLogic.fixed_judgment (ProofContext.theory_of ctxt) name
    |> ProofContext.bind_skolem ctxt [name]
  in (v, t) end;

local

val thatN = "that";

fun gen_obtain prep_att prep_vars prep_propp raw_vars raw_asms int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val ctxt = Proof.context_of state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    (*obtain vars*)
    val (vars, vars_ctxt) = fold_map prep_vars raw_vars ctxt;
    val fix_ctxt = vars_ctxt |> ProofContext.fix_i vars;
    val xs = List.concat (map fst vars);

    (*obtain asms*)
    val (asms_ctxt, proppss) = prep_propp (fix_ctxt, map snd raw_asms);
    val asm_props = List.concat (map (map fst) proppss);
    val asms = map fst (Attrib.map_specs (prep_att (Proof.theory_of state)) raw_asms) ~~ proppss;

    val _ = ProofContext.warn_extra_tfrees fix_ctxt asms_ctxt;

    (*obtain statements*)
    val thesisN = Term.variant xs AutoBind.thesisN;
    val (thesis_var, thesis) = bind_judgment fix_ctxt thesisN;

    fun occs_var x = Library.get_first (fn t =>
      Term.find_free t (ProofContext.get_skolem fix_ctxt x)) asm_props;
    val raw_parms = map occs_var xs;
    val parms = List.mapPartial I raw_parms;
    val parm_names =
      List.mapPartial (fn (SOME (Free a), x) => SOME (a, x) | _ => NONE) (raw_parms ~~ xs);

    val that_prop =
      Term.list_all_free (map #1 parm_names, Logic.list_implies (asm_props, thesis))
      |> Library.curry Logic.list_rename_params (map #2 parm_names);
    val obtain_prop =
      Logic.list_rename_params ([AutoBind.thesisN],
        Term.list_all_free ([thesis_var], Logic.mk_implies (that_prop, thesis)));

    fun after_qed _ =
      Proof.local_qed (NONE, false)
      #> Seq.map (`Proof.the_fact #-> (fn rule =>
        Proof.fix_i vars
        #> Proof.assm_i (K (export_obtained state parms rule)) asms));
  in
    state
    |> Proof.enter_forward
    |> Proof.have_i NONE (K Seq.single) [(("", []), [(obtain_prop, ([], []))])] int
    |> Proof.proof (SOME Method.succeed_text) |> Seq.hd
    |> Proof.fix_i [([thesisN], NONE)]
    |> Proof.assume_i
      [((thatN, [Attrib.context (ContextRules.intro_query NONE)]), [(that_prop, ([], []))])]
    |> `Proof.the_facts
    ||> Proof.chain_facts chain_facts
    ||> Proof.show_i NONE after_qed [(("", []), [(thesis, ([], []))])] false
    |-> (Proof.refine o Method.Basic o K o Method.insert) |> Seq.hd
  end;

in

val obtain = gen_obtain Attrib.local_attribute ProofContext.read_vars ProofContext.read_propp;
val obtain_i = gen_obtain (K I) ProofContext.cert_vars ProofContext.cert_propp;

end;



(** guess **)

local

fun match_params state vars rule =
  let
    val ctxt = Proof.context_of state;
    val thy = Proof.theory_of state;
    val string_of_typ = ProofContext.string_of_typ ctxt;
    val string_of_term = setmp show_types true (ProofContext.string_of_term ctxt);

    fun err msg th = raise Proof.STATE (msg ^ ":\n" ^ ProofContext.string_of_thm ctxt th, state);

    val params = RuleCases.strip_params (Logic.nth_prem (1, Thm.prop_of rule));
    val m = length vars;
    val n = length params;
    val _ = conditional (m > n)
      (fn () => err "More variables than parameters in obtained rule" rule);

    fun match ((x, SOME T), (y, U)) tyenv =
        ((x, T), Sign.typ_match thy (U, T) tyenv handle Type.TYPE_MATCH =>
          err ("Failed to match variable " ^
            string_of_term (Free (x, T)) ^ " against parameter " ^
            string_of_term (Syntax.mark_boundT (y, Envir.norm_type tyenv U)) ^ " in") rule)
      | match ((x, NONE), (_, U)) tyenv = ((x, U), tyenv);
    val (xs, tyenv) = fold_map match (vars ~~ Library.take (m, params)) Vartab.empty;
    val ys = Library.drop (m, params);
    val norm_type = Envir.norm_type tyenv;

    val xs' = xs |> map (apsnd norm_type);
    val ys' =
      map Syntax.internal (Term.variantlist (map fst ys, map fst xs)) ~~
      map (norm_type o snd) ys;
    val instT =
      fold (Term.add_tvarsT o #2) params []
      |> map (TVar #> (fn T => (Thm.ctyp_of thy T, Thm.ctyp_of thy (norm_type T))));
    val rule' = rule |> Thm.instantiate (instT, []);

    val tvars = Drule.tvars_of rule';
    val vars = fold (remove op =) (Term.add_vars (Thm.concl_of rule') []) (Drule.vars_of rule');
    val _ =
      if null tvars andalso null vars then ()
      else err ("Illegal schematic variable(s) " ^
        commas (map (string_of_typ o TVar) tvars @ map (string_of_term o Var) vars) ^ " in") rule';
  in (xs' @ ys', rule') end;

fun gen_guess prep_vars raw_vars int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val thy = Proof.theory_of state;
    val ctxt = Proof.context_of state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    val (thesis_var, thesis) = bind_judgment ctxt AutoBind.thesisN;
    val varss = #1 (fold_map prep_vars raw_vars ctxt);
    val vars = List.concat (map (fn (xs, T) => map (rpair T) xs) varss);

    fun check_result th =
      (case Thm.prems_of th of
        [prem] =>
          if Thm.concl_of th aconv thesis andalso
            Logic.strip_assums_concl prem aconv thesis then ()
          else raise Proof.STATE ("Guessed a different clause:\n" ^
            ProofContext.string_of_thm ctxt th, state)
      | [] => raise Proof.STATE ("Goal solved -- nothing guessed.", state)
      | _ => raise Proof.STATE ("Guess split into several cases:\n" ^
        ProofContext.string_of_thm ctxt th, state));

    fun guess_context raw_rule =
      let
        val (parms, rule) = match_params state vars raw_rule;
        val ts = map (ProofContext.bind_skolem ctxt (map #1 parms) o Free) parms;
        val ps = map dest_Free ts;
        val asms =
          Logic.strip_assums_hyp (Logic.nth_prem (1, Thm.prop_of rule))
          |> map (fn asm => (Term.betapplys (Term.list_abs (ps, asm), ts), ([], [])));
        val _ = conditional (null asms) (fn () =>
          raise Proof.STATE ("Trivial result -- nothing guessed", state));
      in
        Proof.fix_i (map (fn (x, T) => ([x], SOME T)) parms)
        #> Proof.assm_i (K (export_obtained state ts rule)) [(("", []), asms)]
        #> Proof.add_binds_i AutoBind.no_facts
      end;

    val before_qed = SOME (Method.primitive_text (Goal.conclude #> Goal.protect));
    fun after_qed [[res]] =
      (check_result res; Proof.end_block #> Seq.map (`Proof.the_fact #-> guess_context));
  in
    state
    |> Proof.enter_forward
    |> Proof.begin_block
    |> Proof.fix_i [([AutoBind.thesisN], NONE)]
    |> Proof.chain_facts chain_facts
    |> Proof.local_goal (ProofDisplay.print_results int) (K I) (apsnd (rpair I))
      "guess" before_qed after_qed [(("", []), [Var (("guess", 0), propT)])]
    |> Proof.refine (Method.primitive_text (K (Goal.init (Thm.cterm_of thy thesis)))) |> Seq.hd
  end;

in

val guess = gen_guess ProofContext.read_vars;
val guess_i = gen_guess ProofContext.cert_vars;

end;

end;
