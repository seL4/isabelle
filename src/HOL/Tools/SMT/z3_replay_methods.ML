(*  Title:      HOL/Tools/SMT/z3_replay_methods.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Proof methods for replaying Z3 proofs.
*)

signature Z3_REPLAY_METHODS =
sig

  (*methods for Z3 proof rules*)
  type z3_method = Proof.context -> thm list -> term -> thm
  val true_axiom: z3_method
  val mp: z3_method
  val refl: z3_method
  val symm: z3_method
  val trans: z3_method
  val cong: z3_method
  val quant_intro: z3_method
  val distrib: z3_method
  val and_elim: z3_method
  val not_or_elim: z3_method
  val rewrite: z3_method
  val rewrite_star: z3_method
  val pull_quant: z3_method
  val push_quant: z3_method
  val elim_unused: z3_method
  val dest_eq_res: z3_method
  val quant_inst: z3_method
  val lemma: z3_method
  val unit_res: z3_method
  val iff_true: z3_method
  val iff_false: z3_method
  val comm: z3_method
  val def_axiom: z3_method
  val apply_def: z3_method
  val iff_oeq: z3_method
  val nnf_pos: z3_method
  val nnf_neg: z3_method
  val mp_oeq: z3_method
  val arith_th_lemma: z3_method
  val th_lemma: string -> z3_method
  val method_for: Z3_Proof.z3_rule -> z3_method
end;

structure Z3_Replay_Methods: Z3_REPLAY_METHODS =
struct

type z3_method = Proof.context -> thm list -> term -> thm


(* utility functions *)

fun replay_error ctxt msg rule thms t =
  SMT_Replay_Methods.replay_error ctxt msg (Z3_Proof.string_of_rule rule) thms t

fun replay_rule_error ctxt rule thms t =
  SMT_Replay_Methods.replay_rule_error "Z3" ctxt (Z3_Proof.string_of_rule rule) thms t

fun trace_goal ctxt rule thms t =
  SMT_Replay_Methods.trace_goal ctxt (Z3_Proof.string_of_rule rule) thms t

fun dest_prop (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = t
  | dest_prop t = t

fun dest_thm thm = dest_prop (Thm.concl_of thm)

val try_provers = SMT_Replay_Methods.try_provers "Z3"

fun prop_tac ctxt prems =
  Method.insert_tac ctxt prems
  THEN' SUBGOAL (fn (prop, i) =>
    if Term.size_of_term prop > 100 then SAT.satx_tac ctxt i
    else (Classical.fast_tac ctxt ORELSE' Clasimp.force_tac ctxt) i)

fun quant_tac ctxt = Blast.blast_tac ctxt


fun apply_rule ctxt t =
  (case Z3_Replay_Rules.apply ctxt (SMT_Replay_Methods.certify_prop ctxt t) of
    SOME thm => thm
  | NONE => raise Fail "apply_rule")


(*theory-lemma*)

fun arith_th_lemma_tac ctxt prems =
  Method.insert_tac ctxt prems
  THEN' SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms z3div_def z3mod_def})
  THEN' Arith_Data.arith_tac ctxt

fun arith_th_lemma ctxt thms t =
  SMT_Replay_Methods.prove_abstract ctxt thms t arith_th_lemma_tac (
    fold_map (SMT_Replay_Methods.abstract_arith ctxt o dest_thm) thms ##>>
    SMT_Replay_Methods.abstract_arith ctxt (dest_prop t))

fun th_lemma name ctxt thms =
  (case Symtab.lookup (SMT_Replay_Methods.get_th_lemma_method ctxt) name of
    SOME method => method ctxt thms
  | NONE => replay_error ctxt "Bad theory" (Z3_Proof.Th_Lemma name) thms)


(* truth axiom *)

fun true_axiom _ _ _ = @{thm TrueI}


(* modus ponens *)

fun mp _ [p, p_eq_q] _ = SMT_Replay_Methods.discharge 1 [p_eq_q, p] iffD1
  | mp ctxt thms t = replay_rule_error ctxt Z3_Proof.Modus_Ponens thms t

val mp_oeq = mp


(* reflexivity *)

fun refl ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t @{thm refl}


(* symmetry *)

fun symm _ [thm] _ = thm RS @{thm sym}
  | symm ctxt thms t = replay_rule_error ctxt Z3_Proof.Reflexivity thms t


(* transitivity *)

fun trans _ [thm1, thm2] _ = thm1 RSN (1, thm2 RSN (2, @{thm trans}))
  | trans ctxt thms t = replay_rule_error ctxt Z3_Proof.Transitivity thms t


(* congruence *)

fun cong ctxt thms = try_provers ctxt
    (Z3_Proof.string_of_rule Z3_Proof.Monotonicity) [
  ("basic", SMT_Replay_Methods.cong_basic ctxt thms),
  ("full", SMT_Replay_Methods.cong_full ctxt thms)] thms


(* quantifier introduction *)

val quant_intro_rules = @{lemma
  "(\<And>x. P x = Q x) ==> (\<forall>x. P x) = (\<forall>x. Q x)"
  "(\<And>x. P x = Q x) ==> (\<exists>x. P x) = (\<exists>x. Q x)"
  "(!!x. (\<not> P x) = Q x) \<Longrightarrow> (\<not>(\<exists>x. P x)) = (\<forall>x. Q x)"
  "(\<And>x. (\<not> P x) = Q x) ==> (\<not>(\<forall>x. P x)) = (\<exists>x. Q x)"
  by fast+}

fun quant_intro ctxt [thm] t =
    SMT_Replay_Methods.prove ctxt t (K (REPEAT_ALL_NEW (resolve_tac ctxt (thm :: quant_intro_rules))))
  | quant_intro ctxt thms t = replay_rule_error ctxt Z3_Proof.Quant_Intro thms t


(* distributivity of conjunctions and disjunctions *)

(* TODO: there are no tests with this proof rule *)
fun distrib ctxt _ t =
  SMT_Replay_Methods.prove_abstract' ctxt t prop_tac
    (SMT_Replay_Methods.abstract_prop (dest_prop t))


(* elimination of conjunctions *)

fun and_elim ctxt [thm] t =
      SMT_Replay_Methods.prove_abstract ctxt [thm] t prop_tac (
        SMT_Replay_Methods.abstract_lit (dest_prop t) ##>>
        SMT_Replay_Methods.abstract_conj (dest_thm thm) #>>
        apfst single o swap)
  | and_elim ctxt thms t = replay_rule_error ctxt Z3_Proof.And_Elim thms t


(* elimination of negated disjunctions *)

fun not_or_elim ctxt [thm] t =
      SMT_Replay_Methods.prove_abstract ctxt [thm] t prop_tac (
        SMT_Replay_Methods.abstract_lit (dest_prop t) ##>>
        SMT_Replay_Methods.abstract_not SMT_Replay_Methods.abstract_disj (dest_thm thm) #>>
        apfst single o swap)
  | not_or_elim ctxt thms t =
      replay_rule_error ctxt Z3_Proof.Not_Or_Elim thms t


(* rewriting *)

local

fun dest_all (Const (\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, T, t)) nctxt =
      let
        val (n, nctxt') = Name.variant "" nctxt
        val f = Free (n, T)
        val t' = Term.subst_bound (f, t)
      in dest_all t' nctxt' |>> cons f end
  | dest_all t _ = ([], t)

fun dest_alls t =
  let
    val nctxt = Name.make_context (Term.add_free_names t [])
    val (lhs, rhs) = HOLogic.dest_eq (dest_prop t)
    val (ls, lhs') = dest_all lhs nctxt
    val (rs, rhs') = dest_all rhs nctxt
  in
    if eq_list (op aconv) (ls, rs) then SOME (ls, (HOLogic.mk_eq (lhs', rhs')))
    else NONE
  end

fun forall_intr ctxt t thm =
  let val ct = Thm.cterm_of ctxt t
  in Thm.forall_intr ct thm COMP_INCR @{thm iff_allI} end

in

fun focus_eq f ctxt t =
  (case dest_alls t of
    NONE => f ctxt t
  | SOME (vs, t') => fold (forall_intr ctxt) vs (f ctxt t'))

end

fun abstract_eq f (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2) =
      f t1 ##>> f t2 #>> HOLogic.mk_eq
  | abstract_eq _ t = SMT_Replay_Methods.abstract_term t

fun prove_prop_rewrite ctxt t =
  SMT_Replay_Methods.prove_abstract' ctxt t prop_tac (
    abstract_eq SMT_Replay_Methods.abstract_prop (dest_prop t))

fun arith_rewrite_tac ctxt _ =
  let val backup_tac = Arith_Data.arith_tac ctxt ORELSE' Clasimp.force_tac ctxt in
    (TRY o Simplifier.simp_tac ctxt) THEN_ALL_NEW backup_tac
    ORELSE' backup_tac
  end

fun prove_arith_rewrite ctxt t =
  SMT_Replay_Methods.prove_abstract' ctxt t arith_rewrite_tac (
    abstract_eq (SMT_Replay_Methods.abstract_arith ctxt) (dest_prop t))

val lift_ite_thm = @{thm HOL.if_distrib} RS @{thm eq_reflection}

fun ternary_conv cv = Conv.combination_conv (Conv.binop_conv cv) cv

fun if_context_conv ctxt ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>HOL.If\<close>, _) $ _ $ _ $ _ =>
      ternary_conv (if_context_conv ctxt)
  | _ $ (Const (\<^const_name>\<open>HOL.If\<close>, _) $ _ $ _ $ _) =>
      Conv.rewr_conv lift_ite_thm then_conv ternary_conv (if_context_conv ctxt)
  | _ => Conv.sub_conv (Conv.top_sweep_conv if_context_conv) ctxt) ct

fun lift_ite_rewrite ctxt t =
  SMT_Replay_Methods.prove ctxt t (fn ctxt =>
    CONVERSION (HOLogic.Trueprop_conv (Conv.binop_conv (if_context_conv ctxt)))
    THEN' resolve_tac ctxt @{thms refl})

fun prove_conj_disj_perm ctxt t = SMT_Replay_Methods.prove ctxt t Conj_Disj_Perm.conj_disj_perm_tac

fun rewrite ctxt _ = try_provers ctxt
    (Z3_Proof.string_of_rule Z3_Proof.Rewrite) [
  ("rules", apply_rule ctxt),
  ("conj_disj_perm", prove_conj_disj_perm ctxt),
  ("prop_rewrite", prove_prop_rewrite ctxt),
  ("arith_rewrite", focus_eq prove_arith_rewrite ctxt),
  ("if_rewrite", lift_ite_rewrite ctxt)] []

fun rewrite_star ctxt = rewrite ctxt


(* pulling quantifiers *)

fun pull_quant ctxt _ t = SMT_Replay_Methods.prove ctxt t quant_tac


(* pushing quantifiers *)

fun push_quant _ _ _ = raise Fail "unsupported" (* FIXME *)


(* elimination of unused bound variables *)

val elim_all = @{lemma "P = Q \<Longrightarrow> (\<forall>x. P) = Q" by fast}
val elim_ex = @{lemma "P = Q \<Longrightarrow> (\<exists>x. P) = Q" by fast}

fun elim_unused_tac ctxt i st = (
  match_tac ctxt [@{thm refl}]
  ORELSE' (match_tac ctxt [elim_all, elim_ex] THEN' elim_unused_tac ctxt)
  ORELSE' (
    match_tac ctxt [@{thm iff_allI}, @{thm iff_exI}]
    THEN' elim_unused_tac ctxt)) i st

fun elim_unused ctxt _ t = SMT_Replay_Methods.prove ctxt t elim_unused_tac


(* destructive equality resolution *)

fun dest_eq_res _ _ _ = raise Fail "dest_eq_res" (* FIXME *)


(* quantifier instantiation *)

val quant_inst_rule = @{lemma "\<not>P x \<or> Q ==> \<not>(\<forall>x. P x) \<or> Q" by fast}

fun quant_inst ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  REPEAT_ALL_NEW (resolve_tac ctxt [quant_inst_rule])
  THEN' resolve_tac ctxt @{thms excluded_middle})


(* propositional lemma *)

exception LEMMA of unit

val intro_hyp_rule1 = @{lemma "(\<not>P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q" by fast}
val intro_hyp_rule2 = @{lemma "(P \<Longrightarrow> Q) \<Longrightarrow> \<not>P \<or> Q" by fast}

fun norm_lemma thm =
  (thm COMP_INCR intro_hyp_rule1)
  handle THM _ => thm COMP_INCR intro_hyp_rule2

fun negated_prop \<^Const_>\<open>Not for t\<close> = HOLogic.mk_Trueprop t
  | negated_prop t = HOLogic.mk_Trueprop (HOLogic.mk_not t)

fun intro_hyps tab (t as \<^Const_>\<open>HOL.disj\<close> $ t1 $ t2) cx =
      lookup_intro_hyps tab t (fold (intro_hyps tab) [t1, t2]) cx
  | intro_hyps tab t cx =
      lookup_intro_hyps tab t (fn _ => raise LEMMA ()) cx

and lookup_intro_hyps tab t f (cx as (thm, terms)) =
  (case Termtab.lookup tab (negated_prop t) of
    NONE => f cx
  | SOME hyp => (norm_lemma (Thm.implies_intr hyp thm), t :: terms))

fun lemma ctxt (thms as [thm]) t =
    (let
       val tab = Termtab.make (map (`Thm.term_of) (Thm.chyps_of thm))
       val (thm', terms) = intro_hyps tab (dest_prop t) (thm, [])
     in
       SMT_Replay_Methods.prove_abstract ctxt [thm'] t prop_tac (
         fold (snd oo SMT_Replay_Methods.abstract_lit) terms #>
         SMT_Replay_Methods.abstract_disj (dest_thm thm') #>> single ##>>
         SMT_Replay_Methods.abstract_disj (dest_prop t))
     end
     handle LEMMA () => replay_error ctxt "Bad proof state" Z3_Proof.Lemma thms t)
  | lemma ctxt thms t = replay_rule_error ctxt Z3_Proof.Lemma thms t


(* unit resolution *)

fun unit_res ctxt thms t =
  SMT_Replay_Methods.prove_abstract ctxt thms t prop_tac (
    fold_map (SMT_Replay_Methods.abstract_unit o dest_thm) thms ##>>
    SMT_Replay_Methods.abstract_unit (dest_prop t) #>>
    (fn (prems, concl) => (prems, concl)))


(* iff-true *)

val iff_true_rule = @{lemma "P ==> P = True" by fast}

fun iff_true _ [thm] _ = thm RS iff_true_rule
  | iff_true ctxt thms t = replay_rule_error ctxt Z3_Proof.Iff_True thms t


(* iff-false *)

val iff_false_rule = @{lemma "\<not>P \<Longrightarrow> P = False" by fast}

fun iff_false _ [thm] _ = thm RS iff_false_rule
  | iff_false ctxt thms t = replay_rule_error ctxt Z3_Proof.Iff_False thms t


(* commutativity *)

fun comm ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t @{thm eq_commute}


(* definitional axioms *)

fun def_axiom_disj ctxt t =
  (case dest_prop t of
    \<^Const_>\<open>disj for u1 u2\<close> =>
      SMT_Replay_Methods.prove_abstract' ctxt t prop_tac (
         SMT_Replay_Methods.abstract_prop u2 ##>>  SMT_Replay_Methods.abstract_prop u1 #>>
         HOLogic.mk_disj o swap)
  | u => SMT_Replay_Methods.prove_abstract' ctxt t prop_tac (SMT_Replay_Methods.abstract_prop u))

fun def_axiom ctxt _ = try_provers ctxt
    (Z3_Proof.string_of_rule Z3_Proof.Def_Axiom) [
  ("rules", apply_rule ctxt),
  ("disj", def_axiom_disj ctxt)] []


(* application of definitions *)

fun apply_def _ [thm] _ = thm (* TODO: cover also the missing cases *)
  | apply_def ctxt thms t = replay_rule_error ctxt Z3_Proof.Apply_Def thms t


(* iff-oeq *)

fun iff_oeq _ _ _ = raise Fail "iff_oeq" (* FIXME *)


(* negation normal form *)

fun nnf_prop ctxt thms t =
  SMT_Replay_Methods.prove_abstract ctxt thms t prop_tac (
    fold_map (SMT_Replay_Methods.abstract_prop o dest_thm) thms ##>>
    SMT_Replay_Methods.abstract_prop (dest_prop t))

fun nnf ctxt rule thms = try_provers ctxt (Z3_Proof.string_of_rule rule) [
  ("prop", nnf_prop ctxt thms),
  ("quant", quant_intro ctxt [hd thms])] thms

fun nnf_pos ctxt = nnf ctxt Z3_Proof.Nnf_Pos
fun nnf_neg ctxt = nnf ctxt Z3_Proof.Nnf_Neg


(* mapping of rules to methods *)

fun unsupported rule ctxt = replay_error ctxt "Unsupported" rule
fun assumed rule ctxt = replay_error ctxt "Assumed" rule

fun choose Z3_Proof.True_Axiom = true_axiom
  | choose (r as Z3_Proof.Asserted) = assumed r
  | choose (r as Z3_Proof.Goal) = assumed r
  | choose Z3_Proof.Modus_Ponens = mp
  | choose Z3_Proof.Reflexivity = refl
  | choose Z3_Proof.Symmetry = symm
  | choose Z3_Proof.Transitivity = trans
  | choose (r as Z3_Proof.Transitivity_Star) = unsupported r
  | choose Z3_Proof.Monotonicity = cong
  | choose Z3_Proof.Quant_Intro = quant_intro
  | choose Z3_Proof.Distributivity = distrib
  | choose Z3_Proof.And_Elim = and_elim
  | choose Z3_Proof.Not_Or_Elim = not_or_elim
  | choose Z3_Proof.Rewrite = rewrite
  | choose Z3_Proof.Rewrite_Star = rewrite_star
  | choose Z3_Proof.Pull_Quant = pull_quant
  | choose (r as Z3_Proof.Pull_Quant_Star) = unsupported r
  | choose Z3_Proof.Push_Quant = push_quant
  | choose Z3_Proof.Elim_Unused_Vars = elim_unused
  | choose Z3_Proof.Dest_Eq_Res = dest_eq_res
  | choose Z3_Proof.Quant_Inst = quant_inst
  | choose (r as Z3_Proof.Hypothesis) = assumed r
  | choose Z3_Proof.Lemma = lemma
  | choose Z3_Proof.Unit_Resolution = unit_res
  | choose Z3_Proof.Iff_True = iff_true
  | choose Z3_Proof.Iff_False = iff_false
  | choose Z3_Proof.Commutativity = comm
  | choose Z3_Proof.Def_Axiom = def_axiom
  | choose (r as Z3_Proof.Intro_Def) = assumed r
  | choose Z3_Proof.Apply_Def = apply_def
  | choose Z3_Proof.Iff_Oeq = iff_oeq
  | choose Z3_Proof.Nnf_Pos = nnf_pos
  | choose Z3_Proof.Nnf_Neg = nnf_neg
  | choose (r as Z3_Proof.Nnf_Star) = unsupported r
  | choose (r as Z3_Proof.Cnf_Star) = unsupported r
  | choose (r as Z3_Proof.Skolemize) = assumed r
  | choose Z3_Proof.Modus_Ponens_Oeq = mp_oeq
  | choose (Z3_Proof.Th_Lemma name) = th_lemma name

fun with_tracing rule method ctxt thms t =
  let val _ = trace_goal ctxt rule thms t
  in method ctxt thms t end

fun method_for rule = with_tracing rule (choose rule)

end;
