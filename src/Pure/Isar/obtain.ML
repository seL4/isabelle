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
    assume that: "!!x. P x ==> thesis"
    <chain_facts> have thesis <proof (insert that)>
  }
  fix x assm (obtained) "P x"

*)

signature OBTAIN =
sig
  val obtain: ((string list * string option) * Comment.text) list
    * ((string * Args.src list * (string * (string list * string list)) list)
      * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val obtain_i: ((string list * typ option) * Comment.text) list
    * ((string * Proof.context attribute list * (term * (term list * term list)) list)
      * Comment.text) list -> ProofHistory.T -> ProofHistory.T
end;

structure Obtain: OBTAIN =
struct


(** disch_obtained **)

fun disch_obtained state parms rule cprops thm =
  let
    val {sign, prop, maxidx, ...} = Thm.rep_thm thm;
    val cparms = map (Thm.cterm_of sign) parms;

    val thm' = thm
      |> Drule.implies_intr_list cprops
      |> Drule.forall_intr_list cparms
      |> Drule.forall_elim_vars (maxidx + 1);
    val elim_tacs = replicate (length cprops) Proof.hard_asm_tac;

    val concl = Logic.strip_assums_concl prop;
    val bads = parms inter (Term.term_frees concl);
  in
    if not (null bads) then
      raise Proof.STATE ("Conclusion contains obtained parameters: " ^
        space_implode " " (map (Sign.string_of_term sign) bads), state)
    else if not (AutoBind.is_judgment (Logic.strip_assums_concl prop)) then
      raise Proof.STATE ("Conclusions of 'obtain' context must be object-logic judgments", state)
    else (Tactic.rtac thm' THEN' RANGE elim_tacs) 1 rule
  end;



(** obtain(_i) **)

val thatN = "that";

fun gen_obtain prep_vars prep_propp prep_att (raw_vars, raw_asms) state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val chain_facts = if Proof.is_chain state then Proof.the_facts state else [];

    (*obtain vars*)
    val (vars_ctxt, vars) =
      foldl_map prep_vars (Proof.context_of state, map Comment.ignore raw_vars);
    val xs = flat (map fst vars);
    val thesisN = Term.variant xs AutoBind.thesisN;

    val bind_skolem = ProofContext.bind_skolem vars_ctxt (xs @ [thesisN]);
    fun bind_propp (prop, (pats1, pats2)) =
      (bind_skolem prop, (map bind_skolem pats1, map bind_skolem pats2));

    (*obtain asms*)
    fun prep_asm (ctxt, (name, src, raw_propps)) =
      let
        val atts = map (prep_att (ProofContext.theory_of ctxt)) src;
        val (ctxt', propps) = foldl_map prep_propp (ctxt, raw_propps);
      in (ctxt', ((name, atts, map bind_propp propps), map #1 propps)) end;

    val (asms_ctxt, asms_result) = foldl_map prep_asm (vars_ctxt, map Comment.ignore raw_asms);
    val (asms, asm_propss) = Library.split_list asms_result;
    val asm_props = flat asm_propss;
    val _ = ProofContext.warn_extra_tfrees vars_ctxt asms_ctxt;

    (*that_prop*)
    fun find_free x t =
      (case ProofContext.find_free t x of Some (Free a) => Some a | _ => None);
    fun occs_var x = Library.get_first (find_free x) asm_props;
    val xs' = mapfilter occs_var xs;
    val parms = map (bind_skolem o Free) xs';

    val bound_thesis = bind_skolem (AutoBind.atomic_judgment (Proof.theory_of state) thesisN);
    val that_prop = Term.list_all_free (xs', Logic.list_implies (asm_props, bound_thesis));

    fun export_obtained rule =
      (disch_obtained state parms rule, fn _ => fn _ => []);

    fun after_qed st = st
      |> Proof.end_block
      |> Seq.map (fn st' => st'
        |> Proof.fix_i vars
        |> Proof.assm_i (export_obtained (Proof.the_fact st')) asms);
  in
    state
    |> Proof.enter_forward
    |> Proof.begin_block
    |> Proof.fix_i [([thesisN], None)]
    |> Proof.assume_i [(thatN, [Method.intro_local], [(that_prop, ([], []))])]
    |> (fn state' =>
      state'
      |> Proof.from_facts chain_facts
      |> Proof.have_i after_qed "" [] (bound_thesis, ([], []))
      |> Method.refine (Method.Basic (K (Method.insert (Proof.the_facts state')))))
  end;


val obtain = ProofHistory.applys o
  (gen_obtain ProofContext.read_vars ProofContext.read_propp Attrib.local_attribute);

val obtain_i = ProofHistory.applys o
  (gen_obtain ProofContext.cert_vars ProofContext.cert_propp (K I));



(** outer syntax **)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val obtainP =
  OuterSyntax.command "obtain" "generalized existence"
    K.prf_asm_goal
    (Scan.optional
      (P.and_list1 (Scan.repeat1 P.name -- Scan.option (P.$$$ "::" |-- P.typ) -- P.marg_comment)
        --| P.$$$ "where") [] --
      P.and_list1 ((P.opt_thm_name ":" -- Scan.repeat1 P.propp >> P.triple1) -- P.marg_comment)
    >> (Toplevel.print oo (Toplevel.proof o obtain)));

val _ = OuterSyntax.add_keywords ["where"];
val _ = OuterSyntax.add_parsers [obtainP];

end;

end;
