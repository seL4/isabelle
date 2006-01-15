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
  val obtain: (string * string option) list ->
    ((string * Attrib.src list) * (string * (string list * string list)) list) list
    -> bool -> Proof.state -> Proof.state
  val obtain_i: (string * typ option) list ->
    ((string * Proof.context attribute list) * (term * (term list * term list)) list) list
    -> bool -> Proof.state -> Proof.state
  val guess: (string * string option) list -> bool -> Proof.state -> Proof.state
  val guess_i: (string * typ option) list -> bool -> Proof.state -> Proof.state
end;

structure Obtain: OBTAIN =
struct


(** obtain_export **)

fun obtain_export ctxt parms rule cprops thm =
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
      error ("Conclusion contains obtained parameters: " ^
        space_implode " " (map (ProofContext.string_of_term ctxt) bads))
    else if not (ObjectLogic.is_judgment thy concl) then
      error "Conclusion in obtained context must be object-logic judgments"
    else (Tactic.rtac thm' THEN' RANGE elim_tacs) 1 rule
  end;



(** obtain **)

fun bind_judgment ctxt name =
  let
    val (bind, _) = ProofContext.bind_fixes [name] ctxt;
    val (t as _ $ Free v) = bind (ObjectLogic.fixed_judgment (ProofContext.theory_of ctxt) name);
  in (v, t) end;

local

val thatN = "that";

fun gen_obtain prep_att prep_vars prep_propp raw_vars raw_asms int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val ctxt = Proof.context_of state;
    val thy = Proof.theory_of state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    (*obtain vars*)
    val (vars, vars_ctxt) = prep_vars (map Syntax.no_syn raw_vars) ctxt;
    val (_, fix_ctxt) = vars_ctxt |> ProofContext.add_fixes_i vars;
    val xs = map #1 vars;

    (*obtain asms*)
    val (asms_ctxt, proppss) = prep_propp (fix_ctxt, map snd raw_asms);
    val asm_props = List.concat (map (map fst) proppss);
    val asms = map fst (Attrib.map_specs (prep_att thy) raw_asms) ~~ proppss;

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
        Proof.fix_i (xs ~~ map #2 vars)
        #> Proof.assm_i (K (obtain_export ctxt parms rule)) asms));
  in
    state
    |> Proof.enter_forward
    |> Proof.have_i NONE (K Seq.single) [(("", []), [(obtain_prop, ([], []))])] int
    |> Proof.proof (SOME Method.succeed_text) |> Seq.hd
    |> Proof.fix_i [(thesisN, NONE)]
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

fun match_params ctxt vars rule =
  let
    val thy = ProofContext.theory_of ctxt;
    val string_of_typ = ProofContext.string_of_typ ctxt;
    val string_of_term = setmp show_types true (ProofContext.string_of_term ctxt);

    fun err msg th = error (msg ^ ":\n" ^ ProofContext.string_of_thm ctxt th);

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

fun inferred_type (x, _, mx) ctxt =
  let val ((_, T), ctxt') = ProofContext.inferred_type x ctxt
  in ((x, SOME T, mx), ctxt') end;

fun gen_guess prep_vars raw_vars int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val thy = Proof.theory_of state;
    val ctxt = Proof.context_of state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    val (thesis_var, thesis) = bind_judgment ctxt AutoBind.thesisN;
    val (vars, _) = ctxt |> prep_vars (map Syntax.no_syn raw_vars) |-> fold_map inferred_type;

    fun check_result th =
      (case Thm.prems_of th of
        [prem] =>
          if Thm.concl_of th aconv thesis andalso
            Logic.strip_assums_concl prem aconv thesis then ()
          else error ("Guessed a different clause:\n" ^ ProofContext.string_of_thm ctxt th)
      | [] => error "Goal solved -- nothing guessed."
      | _ => error ("Guess split into several cases:\n" ^ ProofContext.string_of_thm ctxt th));

    fun guess_context raw_rule =
      let
        val (parms, rule) = match_params ctxt (map (fn (x, T, _) => (x, T)) vars) raw_rule;
        val (bind, _) = ProofContext.bind_fixes (map #1 parms) ctxt;
        val ts = map (bind o Free) parms;
        val ps = map dest_Free ts;
        val asms =
          Logic.strip_assums_hyp (Logic.nth_prem (1, Thm.prop_of rule))
          |> map (fn asm => (Term.betapplys (Term.list_abs (ps, asm), ts), ([], [])));
        val _ = conditional (null asms) (fn () => error "Trivial result -- nothing guessed");
      in
        Proof.fix_i (map (apsnd SOME) parms)
        #> Proof.assm_i (K (obtain_export ctxt ts rule)) [(("", []), asms)]
        #> Proof.add_binds_i AutoBind.no_facts
      end;

    val before_qed = SOME (Method.primitive_text (Goal.conclude #> Goal.protect));
    fun after_qed [[res]] =
      (check_result res; Proof.end_block #> Seq.map (`Proof.the_fact #-> guess_context));
  in
    state
    |> Proof.enter_forward
    |> Proof.begin_block
    |> Proof.fix_i [(AutoBind.thesisN, NONE)]
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
