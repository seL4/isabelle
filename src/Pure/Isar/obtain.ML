(*  Title:      Pure/Isar/obtain.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The 'obtain' language element -- eliminated existential quantification
at the level of proof texts.

The common case:

    <goal_facts>
    have/show C
      obtain a in P[a] <proof>          ==

    <goal_facts>
    have/show C
    proof succeed
      def thesis == C
      presume that: !!a. P a ==> thesis
      from goal_facts show thesis <proof>
    next
      fix a
      assume P a

The general case:

    <goal_facts>
    have/show !!x. G x ==> C x
      obtain a in P[a] <proof>          ==

    <goal_facts>
    have/show !!x. G x ==> C x
    proof succeed
      fix x
      assume antecedent: G x
      def thesis == C x
      presume that: !!a. P a ==> thesis
      from goal_facts show thesis <proof>
    next
      fix a
      assume P a

TODO:
  - bind terms for goal as well (done?);
  - improve block structure (admit subsequent occurences of 'next') (no?);
  - handle general case (easy??);
*)

signature OBTAIN_DATA =
sig
  val that_atts: Proof.context attribute list
end;

signature OBTAIN =
sig
  val obtain: ((string list * string option) * Comment.text) list
    * ((string * Args.src list * (string * (string list * string list)) list)
      * Comment.text) list -> ProofHistory.T -> ProofHistory.T
  val obtain_i: ((string list * typ option) * Comment.text) list
    * ((string * Proof.context attribute list * (term * (term list * term list)) list)
      * Comment.text) list -> ProofHistory.T -> ProofHistory.T
end;

functor ObtainFun(Data: OBTAIN_DATA): OBTAIN =
struct


(** obtain(_i) **)

val thatN = "that";

fun gen_obtain prep_vars prep_propp prep_att (raw_vars, raw_asms) state =
  let
    (*thesis*)
    val (prop, (goal_facts, goal)) = Proof.get_goal (Proof.assert_backward state);

    val parms = Logic.strip_params prop;        (* FIXME unused *)
    val _ =
      if null parms then () else raise Proof.STATE ("Cannot handle params in goal (yet)", state);
    val hyps = Logic.strip_assums_hyp prop;     (* FIXME unused *)
    val concl = Logic.strip_assums_concl prop;
    val ((thesis_name, thesis_term), atomic_thesis) = AutoBind.atomic_thesis concl;

    (*vars*)
    val (vars_ctxt, vars) =
      foldl_map prep_vars (Proof.context_of state, map Comment.ignore raw_vars);
    val xs = flat (map fst vars);

    (*asms*)
    fun prep_asm (ctxt, (name, src, raw_propps)) =
      let
        val atts = map (prep_att (ProofContext.theory_of ctxt)) src;
        val (ctxt', propps) = foldl_map prep_propp (ctxt, raw_propps);
      in (ctxt', (name, atts, propps)) end;

    val (asms_ctxt, asms) = foldl_map prep_asm (vars_ctxt, map Comment.ignore raw_asms);
    val asm_props = flat (map (map fst o #3) asms);
    val _ = ProofContext.warn_extra_tfrees vars_ctxt asms_ctxt;

    (*that_prop*)
    fun find_free x t =
      (case Proof.find_free t x of Some (Free a) => Some a | _ => None);
    fun occs_var x = Library.get_first (find_free x) asm_props;
    val that_prop =
      Term.list_all_free (mapfilter occs_var xs, Logic.list_implies (asm_props, atomic_thesis));

    fun after_qed st =
      st
      |> Proof.next_block
      |> Proof.fix_i vars
      |> Proof.assume_i asms
      |> Seq.single;
  in
    state
    |> Method.proof (Some (Method.Basic (K Method.succeed)))
    |> Seq.map (fn st => st
      |> LocalDefs.def_i "" [] ((thesis_name, None), (thesis_term, []))
      |> Proof.presume_i [(thatN, Data.that_atts, [(that_prop, ([], []))])]
      |> Proof.from_facts goal_facts
      |> Proof.show_i after_qed "" [] (atomic_thesis, ([], [])))
  end;


val obtain = ProofHistory.applys o
  (gen_obtain ProofContext.read_vars ProofContext.read_propp Attrib.local_attribute);

val obtain_i = ProofHistory.applys o
  (gen_obtain ProofContext.cert_vars ProofContext.cert_propp (K I));



(** outer syntax **)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val obtainP =
  OuterSyntax.command "obtain" "proof text-level existential quantifier"
    K.prf_asm_goal
    (Scan.optional
      (P.and_list1 (Scan.repeat1 P.name -- Scan.option (P.$$$ "::" |-- P.typ) -- P.marg_comment)
        --| P.$$$ "in") [] --
      P.and_list1 ((P.opt_thm_name ":" -- Scan.repeat1 P.propp >> P.triple1) -- P.marg_comment)
    >> (Toplevel.print oo (Toplevel.proof o obtain)));

val _ = OuterSyntax.add_parsers [obtainP];

end;


end;
