(*  Title:      Pure/Isar/obtain.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The 'obtain' language element -- generalized existence at the level of
proof texts.

  <chain_facts>
  obtain x where "P x" <proof> ==

  {
    fix thesis
    assume that [intro]: "!!x. P x ==> thesis"
    <chain_facts> have thesis <proof (insert that)>
  }
  fix x assm (obtained) "P x"

*)

signature OBTAIN =
sig
  val obtain: (string list * string option) list ->
    ((string * Proof.context attribute list) * (string * (string list * string list)) list) list
    -> Proof.state -> Proof.state Seq.seq
  val obtain_i: (string list * typ option) list ->
    ((string * Proof.context attribute list) * (term * (term list * term list)) list) list
    -> Proof.state -> Proof.state Seq.seq
end;

structure Obtain: OBTAIN =
struct


(** export_obtain **)

fun export_obtain state parms rule _ cprops thm =
  let
    val {sign, prop, maxidx, ...} = Thm.rep_thm thm;
    val cparms = map (Thm.cterm_of sign) parms;

    val thm' = thm
      |> Drule.implies_intr_goals cprops
      |> Drule.forall_intr_list cparms
      |> Drule.forall_elim_vars (maxidx + 1);
    val elim_tacs = replicate (length cprops) (Tactic.etac Drule.triv_goal);

    val concl = Logic.strip_assums_concl prop;
    val bads = parms inter (Term.term_frees concl);
  in
    if not (null bads) then
      raise Proof.STATE ("Conclusion contains obtained parameters: " ^
        space_implode " " (map (ProofContext.string_of_term (Proof.context_of state)) bads), state)
    else if not (ObjectLogic.is_judgment sign (Logic.strip_assums_concl prop)) then
      raise Proof.STATE ("Conclusions of 'obtain' context must be object-logic judgments", state)
    else (Tactic.rtac thm' THEN' RANGE elim_tacs) 1 rule
  end;



(** obtain(_i) **)

val thatN = "that";

fun gen_obtain prep_vars prep_propp raw_vars raw_asms state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val chain_facts = if Proof.is_chain state then Proof.the_facts state else [];
    val thy = Proof.theory_of state;
    val sign = Theory.sign_of thy;

    (*obtain vars*)
    val (vars_ctxt, vars) = foldl_map prep_vars (Proof.context_of state, raw_vars);
    val xs = flat (map fst vars);
    val fix_ctxt = vars_ctxt |> ProofContext.fix_i vars;

    (*obtain asms*)
    val (asms_ctxt, proppss) = prep_propp (fix_ctxt, map snd raw_asms);
    val asm_props = flat (map (map fst) proppss);
    val asms = map fst raw_asms ~~ proppss;

    val _ = ProofContext.warn_extra_tfrees fix_ctxt asms_ctxt;

    (*that_prop*)
    val thesisN = Term.variant xs AutoBind.thesisN;
    val bound_thesis =
      ProofContext.bind_skolem fix_ctxt [thesisN] (ObjectLogic.fixed_judgment sign thesisN);

    fun occs_var x = Library.get_first (fn t =>
      ProofContext.find_free t (ProofContext.get_skolem fix_ctxt x)) asm_props;
    val raw_parms = map occs_var xs;
    val parms = mapfilter I raw_parms;
    val parm_names =
      mapfilter (fn (Some (Free a), x) => Some (a, x) | _ => None) (raw_parms ~~ xs);

    val that_prop =
      Term.list_all_free (map #1 parm_names, Logic.list_implies (asm_props, bound_thesis))
      |> Library.curry Logic.list_rename_params (map #2 parm_names);

    fun after_qed st = st
      |> Proof.end_block
      |> Seq.map (fn st' => st'
        |> Proof.fix_i vars
        |> Proof.assm_i (export_obtain state parms (Proof.the_fact st')) asms);
  in
    state
    |> Proof.enter_forward
    |> Proof.begin_block
    |> Proof.fix_i [([thesisN], None)]
    |> Proof.assume_i [((thatN, [Method.intro_local]), [(that_prop, ([], []))])]
    |> (fn state' =>
      state'
      |> Proof.from_facts chain_facts
      |> Proof.have_i after_qed [(("", []), [(bound_thesis, ([], []))])]
      |> Method.refine (Method.Basic (K (Method.insert (Proof.the_facts state')))))
  end;

val obtain = gen_obtain ProofContext.read_vars ProofContext.read_propp;
val obtain_i = gen_obtain ProofContext.cert_vars ProofContext.cert_propp;


end;
