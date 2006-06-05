(*  Title:      Pure/Isar/obtain.ML
    ID:         $Id$
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
  val obtain: string -> (string * string option) list ->
    ((string * Attrib.src list) * (string * string list) list) list
    -> bool -> Proof.state -> Proof.state
  val obtain_i: string -> (string * typ option) list ->
    ((string * attribute list) * (term * term list) list) list
    -> bool -> Proof.state -> Proof.state
  val guess: (string * string option) list -> bool -> Proof.state -> Proof.state
  val guess_i: (string * typ option) list -> bool -> Proof.state -> Proof.state
  val statement: (string * ((string * 'typ option) list * 'term list)) list ->
    (('typ, 'term, 'fact) Element.ctxt list *
      ((string * Attrib.src list) * ('term * 'term list) list) list) *
    (((string * Attrib.src list) * (term * term list) list) list -> Proof.context ->
      (((string * Attrib.src list) * (term * term list) list) list * thm list) * Proof.context)
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

val thatN = "that";

local

fun gen_obtain prep_att prep_vars prep_propp
    name raw_vars raw_asms int state =
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
    val asm_props = maps (map fst) proppss;
    val asms = map fst (Attrib.map_specs (prep_att thy) raw_asms) ~~ proppss;

    val _ = ProofContext.warn_extra_tfrees fix_ctxt asms_ctxt;

    (*obtain statements*)
    val thesisN = Term.variant xs AutoBind.thesisN;
    val (thesis_var, thesis) = bind_judgment fix_ctxt thesisN;

    fun occs_var x = Library.get_first (fn t =>
      Term.find_free t (ProofContext.get_skolem fix_ctxt x)) asm_props;
    val raw_parms = map occs_var xs;
    val parms = map_filter I raw_parms;
    val parm_names =
      map_filter (fn (SOME (Free a), x) => SOME (a, x) | _ => NONE) (raw_parms ~~ xs);

    val that_name = if name = "" then thatN else name;
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
    |> Proof.have_i NONE (K Seq.single) [(("", []), [(obtain_prop, [])])] int
    |> Proof.proof (SOME Method.succeed_text) |> Seq.hd
    |> Proof.fix_i [(thesisN, NONE)]
    |> Proof.assume_i [((that_name, [ContextRules.intro_query NONE]), [(that_prop, [])])]
    |> `Proof.the_facts
    ||> Proof.chain_facts chain_facts
    ||> Proof.show_i NONE after_qed [(("", []), [(thesis, [])])] false
    |-> Proof.refine_insert
  end;

in

val obtain = gen_obtain Attrib.attribute ProofContext.read_vars ProofContext.read_propp;
val obtain_i = gen_obtain (K I) ProofContext.cert_vars ProofContext.cert_propp;

end;



(** guess **)

local

fun unify_params ctxt vars raw_rule =
  let
    val thy = ProofContext.theory_of ctxt;
    val string_of_typ = ProofContext.string_of_typ ctxt;
    val string_of_term = setmp show_types true (ProofContext.string_of_term ctxt);

    fun err msg th = error (msg ^ ":\n" ^ ProofContext.string_of_thm ctxt th);

    val maxidx = fold (Term.maxidx_typ o snd) vars ~1;
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
    val (tyenv, _) = fold unify (vars ~~ Library.take (m, params))
      (Vartab.empty, Int.max (maxidx, Thm.maxidx_of rule));
    val norm_type = Envir.norm_type tyenv;

    val xs = map (apsnd norm_type) vars;
    val ys = map (apsnd norm_type) (Library.drop (m, params));
    val ys' = map Syntax.internal (Term.variantlist (map fst ys, map fst xs)) ~~ map #2 ys;

    val instT =
      fold (Term.add_tvarsT o #2) params []
      |> map (TVar #> (fn T => (Thm.ctyp_of thy T, Thm.ctyp_of thy (norm_type T))));
    val rule' = rule |> Thm.instantiate (instT, []);

    val tvars = Drule.tvars_of rule';
    val vars = subtract (op =) (Term.add_vars (Thm.concl_of rule') []) (Drule.vars_of rule');
    val _ =
      if null tvars andalso null vars then ()
      else err ("Illegal schematic variable(s) " ^
        commas (map (string_of_typ o TVar) tvars @ map (string_of_term o Var) vars) ^ " in") rule';
  in (xs @ ys', rule') end;

fun inferred_type (x, _, mx) ctxt =
  let val ((_, T), ctxt') = ProofContext.inferred_param x ctxt
  in ((x, T, mx), ctxt') end;

fun polymorphic (vars, ctxt) =
  let val Ts = map Logic.dest_type (ProofContext.polymorphic ctxt (map (Logic.mk_type o #2) vars))
  in map2 (fn (x, _, mx) => fn T => ((x, T), mx)) vars Ts end;

fun gen_guess prep_vars raw_vars int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val thy = Proof.theory_of state;
    val ctxt = Proof.context_of state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    val (thesis_var, thesis) = bind_judgment ctxt AutoBind.thesisN;
    val vars = ctxt |> prep_vars (map Syntax.no_syn raw_vars)
      |-> fold_map inferred_type |> polymorphic;

    fun check_result th =
      (case Thm.prems_of th of
        [prem] =>
          if Thm.concl_of th aconv thesis andalso
            Logic.strip_assums_concl prem aconv thesis then ()
          else error ("Guessed a different clause:\n" ^ ProofContext.string_of_thm ctxt th)
      | [] => error "Goal solved -- nothing guessed."
      | _ => error ("Guess split into several cases:\n" ^ ProofContext.string_of_thm ctxt th));

    fun guess_context [_, raw_rule] =
      let
        val (parms, rule) = unify_params ctxt (map #1 vars) raw_rule;
        val (bind, _) = ProofContext.bind_fixes (map #1 parms) ctxt;
        val ts = map (bind o Free) parms;
        val ps = map dest_Free ts;
        val asms =
          Logic.strip_assums_hyp (Logic.nth_prem (1, Thm.prop_of rule))
          |> map (fn asm => (Term.betapplys (Term.list_abs (ps, asm), ts), []));
        val _ = not (null asms) orelse error "Trivial result -- nothing guessed";
      in
        Proof.fix_i (map (apsnd SOME) parms)
        #> Proof.assm_i (K (obtain_export ctxt ts rule)) [(("", []), asms)]
        #> Proof.add_binds_i AutoBind.no_facts
      end;

    val goal = Var (("guess", 0), propT);
    fun print_result ctxt' (k, [(s, [_, th])]) =
      ProofDisplay.print_results int ctxt' (k, [(s, [th])]);
    val before_qed = SOME (Method.primitive_text (Goal.conclude #> (fn th =>
      Goal.protect (Conjunction.intr (Drule.mk_term (Thm.cprop_of th)) th))));
    fun after_qed [[_, res]] =
      (check_result res; Proof.end_block #> Seq.map (`Proof.the_facts #-> guess_context));
  in
    state
    |> Proof.enter_forward
    |> Proof.begin_block
    |> Proof.fix_i [(AutoBind.thesisN, NONE)]
    |> Proof.chain_facts chain_facts
    |> Proof.local_goal print_result (K I) (apsnd (rpair I))
      "guess" before_qed after_qed [(("", []), [Logic.mk_term goal, goal])]
    |> Proof.refine (Method.primitive_text (K (Goal.init (Thm.cterm_of thy thesis)))) |> Seq.hd
  end;

in

val guess = gen_guess ProofContext.read_vars;
val guess_i = gen_guess ProofContext.cert_vars;

end;



(** statements with several cases **)

fun statement cases =
  let
    val names =
      cases |> map_index (fn (i, ("", _)) => string_of_int (i + 1) | (_, (name, _)) => name);
    val elems = cases |> map (fn (_, (vars, _)) =>
      Element.Constrains (vars |> map_filter (fn (x, SOME T) => SOME (x, T) | _ => NONE)));
    val concl = cases |> map (fn (_, (_, props)) => (("", []), map (rpair []) props));

    fun mk_stmt stmt ctxt =
      let
        val thesis =
          ObjectLogic.fixed_judgment (ProofContext.theory_of ctxt) AutoBind.thesisN;
        val atts = map Attrib.internal
          [RuleCases.consumes (~ (length cases)), RuleCases.case_names names];

        fun assume_case ((name, (vars, _)), (_, propp)) ctxt' =
          let
            val xs = map fst vars;
            val props = map fst propp;
            val (parms, ctxt'') =
              ctxt'
              |> fold ProofContext.declare_term props
              |> fold_map ProofContext.inferred_param xs;
            val asm = Term.list_all_free (parms, Logic.list_implies (props, thesis));
          in
            ctxt' |> (snd o ProofContext.add_fixes_i (map (fn x => (x, NONE, NoSyn)) xs));
            ctxt' |> ProofContext.add_assms_i ProofContext.assume_export
              [((name, [ContextRules.intro_query NONE]), [(asm, [])])]
            |>> (fn [(_, [th])] => th)
          end;
        val (ths, ctxt') = ctxt
          |> (snd o ProofContext.add_fixes_i [(AutoBind.thesisN, NONE, NoSyn)])
          |> fold_map assume_case (cases ~~ stmt)
          |-> (fn ths => ProofContext.note_thmss_i [((thatN, []), [(ths, [])])] #> #2 #> pair ths);
      in (([(("", atts), [(thesis, [])])], ths), ctxt') end;
  in ((elems, concl), mk_stmt) end;

end;
