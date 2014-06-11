(*  Title:      HOL/Tools/SMT2/z3_new_replay_methods.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Proof methods for replaying Z3 proofs.
*)

signature Z3_NEW_REPLAY_METHODS =
sig
  (*abstraction*)
  type abs_context = int * term Termtab.table
  type 'a abstracter = term -> abs_context -> 'a * abs_context
  val add_arith_abstracter: (term abstracter -> term option abstracter) ->
    Context.generic -> Context.generic

  (*theory lemma methods*)
  type th_lemma_method = Proof.context -> thm list -> term -> thm
  val add_th_lemma_method: string * th_lemma_method -> Context.generic ->
    Context.generic

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
  val th_lemma: string -> z3_method
  val method_for: Z3_New_Proof.z3_rule -> z3_method
end;

structure Z3_New_Replay_Methods: Z3_NEW_REPLAY_METHODS =
struct

type z3_method = Proof.context -> thm list -> term -> thm


(* utility functions *)

fun trace ctxt f = SMT2_Config.trace_msg ctxt f ()

fun pretty_thm ctxt thm = Syntax.pretty_term ctxt (Thm.concl_of thm)

fun pretty_goal ctxt msg rule thms t =
  let
    val full_msg = msg ^ ": " ^ quote (Z3_New_Proof.string_of_rule rule)
    val assms =
      if null thms then []
      else [Pretty.big_list "assumptions:" (map (pretty_thm ctxt) thms)]
    val concl = Pretty.big_list "proposition:" [Syntax.pretty_term ctxt t]
  in Pretty.big_list full_msg (assms @ [concl]) end

fun replay_error ctxt msg rule thms t = error (Pretty.string_of (pretty_goal ctxt msg rule thms t))

fun replay_rule_error ctxt = replay_error ctxt "Failed to replay Z3 proof step"

fun trace_goal ctxt rule thms t =
  trace ctxt (fn () => Pretty.string_of (pretty_goal ctxt "Goal" rule thms t))

fun as_prop (t as Const (@{const_name Trueprop}, _) $ _) = t
  | as_prop t = HOLogic.mk_Trueprop t

fun dest_prop (Const (@{const_name Trueprop}, _) $ t) = t
  | dest_prop t = t

fun dest_thm thm = dest_prop (Thm.concl_of thm)

fun certify_prop ctxt t = SMT2_Util.certify ctxt (as_prop t)

fun try_provers ctxt rule [] thms t = replay_rule_error ctxt rule thms t
  | try_provers ctxt rule ((name, prover) :: named_provers) thms t =
      (case (trace ctxt (K ("Trying prover " ^ quote name)); try prover t) of
        SOME thm => thm
      | NONE => try_provers ctxt rule named_provers thms t)

fun match ctxt pat t =
  (Vartab.empty, Vartab.empty)
  |> Pattern.first_order_match (Proof_Context.theory_of ctxt) (pat, t)

fun gen_certify_inst sel mk cert ctxt thm t =
  let
    val inst = match ctxt (dest_thm thm) (dest_prop t)
    fun cert_inst (ix, (a, b)) = (cert (mk (ix, a)), cert b)
  in Vartab.fold (cons o cert_inst) (sel inst) [] end

fun match_instantiateT ctxt t thm =
  if Term.exists_type (Term.exists_subtype Term.is_TVar) (dest_thm thm) then
    let val certT = Thm.ctyp_of (Proof_Context.theory_of ctxt)
    in Thm.instantiate (gen_certify_inst fst TVar certT ctxt thm t, []) thm end
  else thm

fun match_instantiate ctxt t thm =
  let
    val cert = SMT2_Util.certify ctxt
    val thm' = match_instantiateT ctxt t thm
  in Thm.instantiate ([], gen_certify_inst snd Var cert ctxt thm' t) thm' end

fun apply_rule ctxt t =
  (case Z3_New_Replay_Rules.apply ctxt (certify_prop ctxt t) of
    SOME thm => thm
  | NONE => raise Fail "apply_rule")

fun discharge _ [] thm = thm
  | discharge i (rule :: rules) thm = discharge (i + Thm.nprems_of rule) rules (rule RSN (i, thm))

fun by_tac ctxt thms ns ts t tac =
  Goal.prove ctxt [] (map as_prop ts) (as_prop t)
    (fn {context, prems} => HEADGOAL (tac context prems))
  |> Drule.generalize ([], ns)
  |> discharge 1 thms

fun prove ctxt t tac = by_tac ctxt [] [] [] t (K o tac)

fun prop_tac ctxt prems =
  Method.insert_tac prems
  THEN' SUBGOAL (fn (prop, i) =>
    if Term.size_of_term prop > 100 then SAT.satx_tac ctxt i
    else (Classical.fast_tac ctxt ORELSE' Clasimp.force_tac ctxt) i)

fun quant_tac ctxt = Blast.blast_tac ctxt


(* plug-ins *)

type abs_context = int * term Termtab.table

type 'a abstracter = term -> abs_context -> 'a * abs_context

type th_lemma_method = Proof.context -> thm list -> term -> thm

fun id_ord ((id1, _), (id2, _)) = int_ord (id1, id2)

structure Plugins = Generic_Data
(
  type T =
    (int * (term abstracter -> term option abstracter)) list *
    th_lemma_method Symtab.table
  val empty = ([], Symtab.empty)
  val extend = I
  fun merge ((abss1, ths1), (abss2, ths2)) = (
    Ord_List.merge id_ord (abss1, abss2),
    Symtab.merge (K true) (ths1, ths2))
)

fun add_arith_abstracter abs = Plugins.map (apfst (Ord_List.insert id_ord (serial (), abs)))
fun get_arith_abstracters ctxt = map snd (fst (Plugins.get (Context.Proof ctxt)))

fun add_th_lemma_method method = Plugins.map (apsnd (Symtab.update_new method))
fun get_th_lemma_method ctxt = snd (Plugins.get (Context.Proof ctxt))


(* abstraction *)

fun prove_abstract ctxt thms t tac f =
  let
    val ((prems, concl), (_, ts)) = f (1, Termtab.empty)
    val ns = Termtab.fold (fn (_, v) => cons (fst (Term.dest_Free v))) ts []
  in
    by_tac ctxt [] ns prems concl tac
    |> match_instantiate ctxt t
    |> discharge 1 thms
  end

fun prove_abstract' ctxt t tac f =
  prove_abstract ctxt [] t tac (f #>> pair [])

fun lookup_term (_, terms) t = Termtab.lookup terms t

fun abstract_sub t f cx =
  (case lookup_term cx t of
    SOME v => (v, cx)
  | NONE => f cx)

fun mk_fresh_free t (i, terms) =
  let val v = Free ("t" ^ string_of_int i, fastype_of t)
  in (v, (i + 1, Termtab.update (t, v) terms)) end

fun apply_abstracters _ [] _ cx = (NONE, cx)
  | apply_abstracters abs (abstracter :: abstracters) t cx =
      (case abstracter abs t cx of
        (NONE, _) => apply_abstracters abs abstracters t cx
      | x as (SOME _, _) => x)

fun abstract_term (t as _ $ _) = abstract_sub t (mk_fresh_free t)
  | abstract_term (t as Abs _) = abstract_sub t (mk_fresh_free t)
  | abstract_term t = pair t

fun abstract_bin abs f t t1 t2 = abstract_sub t (abs t1 ##>> abs t2 #>> f)

fun abstract_ter abs f t t1 t2 t3 =
  abstract_sub t (abs t1 ##>> abs t2 ##>> abs t3 #>> (Parse.triple1 #> f))

fun abstract_lit (@{const HOL.Not} $ t) = abstract_term t #>> HOLogic.mk_not
  | abstract_lit t = abstract_term t

fun abstract_not abs (t as @{const HOL.Not} $ t1) =
      abstract_sub t (abs t1 #>> HOLogic.mk_not)
  | abstract_not _ t = abstract_lit t

fun abstract_conj (t as @{const HOL.conj} $ t1 $ t2) =
      abstract_bin abstract_conj HOLogic.mk_conj t t1 t2
  | abstract_conj t = abstract_lit t

fun abstract_disj (t as @{const HOL.disj} $ t1 $ t2) =
      abstract_bin abstract_disj HOLogic.mk_disj t t1 t2
  | abstract_disj t = abstract_lit t

fun abstract_prop (t as (c as @{const If (bool)}) $ t1 $ t2 $ t3) =
      abstract_ter abstract_prop (fn (t1, t2, t3) => c $ t1 $ t2 $ t3) t t1 t2 t3
  | abstract_prop (t as @{const HOL.disj} $ t1 $ t2) =
      abstract_bin abstract_prop HOLogic.mk_disj t t1 t2
  | abstract_prop (t as @{const HOL.conj} $ t1 $ t2) =
      abstract_bin abstract_prop HOLogic.mk_conj t t1 t2
  | abstract_prop (t as @{const HOL.implies} $ t1 $ t2) =
      abstract_bin abstract_prop HOLogic.mk_imp t t1 t2
  | abstract_prop (t as @{term "HOL.eq :: bool => _"} $ t1 $ t2) =
      abstract_bin abstract_prop HOLogic.mk_eq t t1 t2
  | abstract_prop t = abstract_not abstract_prop t

fun abstract_arith ctxt u =
  let
    fun abs (t as (c as Const _) $ Abs (s, T, t')) =
          abstract_sub t (abs t' #>> (fn u' => c $ Abs (s, T, u')))
      | abs (t as (c as Const (@{const_name If}, _)) $ t1 $ t2 $ t3) =
          abstract_ter abs (fn (t1, t2, t3) => c $ t1 $ t2 $ t3) t t1 t2 t3
      | abs (t as @{const HOL.Not} $ t1) = abstract_sub t (abs t1 #>> HOLogic.mk_not)
      | abs (t as @{const HOL.disj} $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> HOLogic.mk_disj)
      | abs (t as (c as Const (@{const_name uminus_class.uminus}, _)) $ t1) =
          abstract_sub t (abs t1 #>> (fn u => c $ u))
      | abs (t as (c as Const (@{const_name plus_class.plus}, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (@{const_name minus_class.minus}, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (@{const_name times_class.times}, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (@{const_name z3div}, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (@{const_name z3mod}, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (@{const_name HOL.eq}, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (@{const_name ord_class.less}, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (@{const_name ord_class.less_eq}, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs t = abstract_sub t (fn cx =>
          if can HOLogic.dest_number t then (t, cx)
          else
            (case apply_abstracters abs (get_arith_abstracters ctxt) t cx of
              (SOME u, cx') => (u, cx')
            | (NONE, _) => abstract_term t cx))
  in abs u end


(* truth axiom *)

fun true_axiom _ _ _ = @{thm TrueI}


(* modus ponens *)

fun mp _ [p, p_eq_q] _ = discharge 1 [p_eq_q, p] iffD1
  | mp ctxt thms t = replay_rule_error ctxt Z3_New_Proof.Modus_Ponens thms t

val mp_oeq = mp


(* reflexivity *)

fun refl ctxt _ t = match_instantiate ctxt t @{thm refl}


(* symmetry *)

fun symm _ [thm] _ = thm RS @{thm sym}
  | symm ctxt thms t = replay_rule_error ctxt Z3_New_Proof.Reflexivity thms t


(* transitivity *)

fun trans _ [thm1, thm2] _ = thm1 RSN (1, thm2 RSN (2, @{thm trans}))
  | trans ctxt thms t = replay_rule_error ctxt Z3_New_Proof.Transitivity thms t


(* congruence *)

fun ctac prems i st = st |> (
  resolve_tac (@{thm refl} :: prems) i
  ORELSE (cong_tac i THEN ctac prems (i + 1) THEN ctac prems i))

fun cong_basic ctxt thms t =
  let val st = Thm.trivial (certify_prop ctxt t)
  in
    (case Seq.pull (ctac thms 1 st) of
      SOME (thm, _) => thm
    | NONE => raise THM ("cong", 0, thms @ [st]))
  end

val cong_dest_rules = @{lemma
  "(~ P | Q) & (P | ~ Q) ==> P = Q"
  "(P | ~ Q) & (~ P | Q) ==> P = Q"
  by fast+}

fun cong_full ctxt thms t = prove ctxt t (fn ctxt' =>
  Method.insert_tac thms
  THEN' (Classical.fast_tac ctxt'
    ORELSE' dresolve_tac cong_dest_rules
    THEN' Classical.fast_tac ctxt'))

fun cong ctxt thms = try_provers ctxt Z3_New_Proof.Monotonicity [
  ("basic", cong_basic ctxt thms),
  ("full", cong_full ctxt thms)] thms


(* quantifier introduction *)

val quant_intro_rules = @{lemma
  "(!!x. P x = Q x) ==> (ALL x. P x) = (ALL x. Q x)"
  "(!!x. P x = Q x) ==> (EX x. P x) = (EX x. Q x)"
  "(!!x. (~ P x) = Q x) ==> (~ (EX x. P x)) = (ALL x. Q x)"
  "(!!x. (~ P x) = Q x) ==> (~ (ALL x. P x)) = (EX x. Q x)"
  by fast+}

fun quant_intro ctxt [thm] t =
    prove ctxt t (K (REPEAT_ALL_NEW (resolve_tac (thm :: quant_intro_rules))))
  | quant_intro ctxt thms t = replay_rule_error ctxt Z3_New_Proof.Quant_Intro thms t


(* distributivity of conjunctions and disjunctions *)

(* TODO: there are no tests with this proof rule *)
fun distrib ctxt _ t =
  prove_abstract' ctxt t prop_tac (abstract_prop (dest_prop t))


(* elimination of conjunctions *)

fun and_elim ctxt [thm] t =
      prove_abstract ctxt [thm] t prop_tac (
        abstract_lit (dest_prop t) ##>>
        abstract_conj (dest_thm thm) #>>
        apfst single o swap)
  | and_elim ctxt thms t = replay_rule_error ctxt Z3_New_Proof.And_Elim thms t


(* elimination of negated disjunctions *)

fun not_or_elim ctxt [thm] t =
      prove_abstract ctxt [thm] t prop_tac (
        abstract_lit (dest_prop t) ##>>
        abstract_not abstract_disj (dest_thm thm) #>>
        apfst single o swap)
  | not_or_elim ctxt thms t =
      replay_rule_error ctxt Z3_New_Proof.Not_Or_Elim thms t


(* rewriting *)

local

fun dest_all (Const (@{const_name HOL.All}, _) $ Abs (_, T, t)) nctxt =
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
  let val ct = Thm.cterm_of (Proof_Context.theory_of ctxt) t
  in Thm.forall_intr ct thm COMP_INCR @{thm iff_allI} end

in

fun focus_eq f ctxt t =
  (case dest_alls t of
    NONE => f ctxt t
  | SOME (vs, t') => fold (forall_intr ctxt) vs (f ctxt t'))

end

fun abstract_eq f (Const (@{const_name HOL.eq}, _) $ t1 $ t2) =
      f t1 ##>> f t2 #>> HOLogic.mk_eq
  | abstract_eq _ t = abstract_term t

fun prove_prop_rewrite ctxt t =
  prove_abstract' ctxt t prop_tac (
    abstract_eq abstract_prop (dest_prop t))

fun arith_rewrite_tac ctxt _ =
  TRY o Simplifier.simp_tac ctxt
  THEN_ALL_NEW (Arith_Data.arith_tac ctxt ORELSE' Clasimp.force_tac ctxt)

fun prove_arith_rewrite ctxt t =
  prove_abstract' ctxt t arith_rewrite_tac (
    abstract_eq (abstract_arith ctxt) (dest_prop t))

fun rewrite ctxt _ = try_provers ctxt Z3_New_Proof.Rewrite [
  ("rules", apply_rule ctxt),
  ("prop_rewrite", prove_prop_rewrite ctxt),
  ("arith_rewrite", focus_eq prove_arith_rewrite ctxt)] []

fun rewrite_star ctxt = rewrite ctxt


(* pulling quantifiers *)

fun pull_quant ctxt _ t = prove ctxt t quant_tac


(* pushing quantifiers *)

fun push_quant _ _ _ = raise Fail "unsupported" (* FIXME *)


(* elimination of unused bound variables *)

val elim_all = @{lemma "P = Q ==> (ALL x. P) = Q" by fast}
val elim_ex = @{lemma "P = Q ==> (EX x. P) = Q" by fast}

fun elim_unused_tac i st = (
  match_tac [@{thm refl}]
  ORELSE' (match_tac [elim_all, elim_ex] THEN' elim_unused_tac)
  ORELSE' (
    match_tac [@{thm iff_allI}, @{thm iff_exI}]
    THEN' elim_unused_tac)) i st

fun elim_unused ctxt _ t = prove ctxt t (fn _ => elim_unused_tac)


(* destructive equality resolution *)

fun dest_eq_res _ _ _ = raise Fail "dest_eq_res" (* FIXME *)


(* quantifier instantiation *)

val quant_inst_rule = @{lemma "~P x | Q ==> ~(ALL x. P x) | Q" by fast}

fun quant_inst ctxt _ t = prove ctxt t (fn _ =>
  REPEAT_ALL_NEW (rtac quant_inst_rule)
  THEN' rtac @{thm excluded_middle})


(* propositional lemma *)

exception LEMMA of unit

val intro_hyp_rule1 = @{lemma "(~P ==> Q) ==> P | Q" by fast}
val intro_hyp_rule2 = @{lemma "(P ==> Q) ==> ~P | Q" by fast}

fun norm_lemma thm =
  (thm COMP_INCR intro_hyp_rule1)
  handle THM _ => thm COMP_INCR intro_hyp_rule2

fun negated_prop (@{const HOL.Not} $ t) = HOLogic.mk_Trueprop t
  | negated_prop t = HOLogic.mk_Trueprop (HOLogic.mk_not t)

fun intro_hyps tab (t as @{const HOL.disj} $ t1 $ t2) cx =
      lookup_intro_hyps tab t (fold (intro_hyps tab) [t1, t2]) cx
  | intro_hyps tab t cx =
      lookup_intro_hyps tab t (fn _ => raise LEMMA ()) cx

and lookup_intro_hyps tab t f (cx as (thm, terms)) =
  (case Termtab.lookup tab (negated_prop t) of
    NONE => f cx
  | SOME hyp => (norm_lemma (Thm.implies_intr hyp thm), t :: terms))

fun lemma ctxt (thms as [thm]) t =
    (let
       val tab = Termtab.make (map (`Thm.term_of) (#hyps (Thm.crep_thm thm)))
       val (thm', terms) = intro_hyps tab (dest_prop t) (thm, [])
     in
       prove_abstract ctxt [thm'] t prop_tac (
         fold (snd oo abstract_lit) terms #>
         abstract_disj (dest_thm thm') #>> single ##>>
         abstract_disj (dest_prop t))
     end
     handle LEMMA () => replay_error ctxt "Bad proof state" Z3_New_Proof.Lemma thms t)
  | lemma ctxt thms t = replay_rule_error ctxt Z3_New_Proof.Lemma thms t


(* unit resolution *)

fun abstract_unit (t as (@{const HOL.Not} $ (@{const HOL.disj} $ t1 $ t2))) =
      abstract_sub t (abstract_unit t1 ##>> abstract_unit t2 #>>
        HOLogic.mk_not o HOLogic.mk_disj)
  | abstract_unit (t as (@{const HOL.disj} $ t1 $ t2)) =
      abstract_sub t (abstract_unit t1 ##>> abstract_unit t2 #>>
        HOLogic.mk_disj)
  | abstract_unit t = abstract_lit t

fun unit_res ctxt thms t =
  prove_abstract ctxt thms t prop_tac (
    fold_map (abstract_unit o dest_thm) thms ##>>
    abstract_unit (dest_prop t) #>>
    (fn (prems, concl) => (prems, concl)))


(* iff-true *)

val iff_true_rule = @{lemma "P ==> P = True" by fast}

fun iff_true _ [thm] _ = thm RS iff_true_rule
  | iff_true ctxt thms t = replay_rule_error ctxt Z3_New_Proof.Iff_True thms t


(* iff-false *)

val iff_false_rule = @{lemma "~P ==> P = False" by fast}

fun iff_false _ [thm] _ = thm RS iff_false_rule
  | iff_false ctxt thms t = replay_rule_error ctxt Z3_New_Proof.Iff_False thms t


(* commutativity *)

fun comm ctxt _ t = match_instantiate ctxt t @{thm eq_commute}


(* definitional axioms *)

fun def_axiom_disj ctxt t =
  (case dest_prop t of
    @{const HOL.disj} $ u1 $ u2 =>
      prove_abstract' ctxt t prop_tac (
        abstract_prop u2 ##>> abstract_prop u1 #>> HOLogic.mk_disj o swap)
  | u => prove_abstract' ctxt t prop_tac (abstract_prop u))

fun def_axiom ctxt _ = try_provers ctxt Z3_New_Proof.Def_Axiom [
  ("rules", apply_rule ctxt),
  ("disj", def_axiom_disj ctxt)] []


(* application of definitions *)

fun apply_def _ [thm] _ = thm (* TODO: cover also the missing cases *)
  | apply_def ctxt thms t = replay_rule_error ctxt Z3_New_Proof.Apply_Def thms t


(* iff-oeq *)

fun iff_oeq _ _ _ = raise Fail "iff_oeq" (* FIXME *)


(* negation normal form *)

fun nnf_prop ctxt thms t =
  prove_abstract ctxt thms t prop_tac (
    fold_map (abstract_prop o dest_thm) thms ##>>
    abstract_prop (dest_prop t))

fun nnf ctxt rule thms = try_provers ctxt rule [
  ("prop", nnf_prop ctxt thms),
  ("quant", quant_intro ctxt [hd thms])] thms

fun nnf_pos ctxt = nnf ctxt Z3_New_Proof.Nnf_Pos
fun nnf_neg ctxt = nnf ctxt Z3_New_Proof.Nnf_Neg


(* theory lemmas *)

fun arith_th_lemma_tac ctxt prems =
  Method.insert_tac prems
  THEN' SELECT_GOAL (Local_Defs.unfold_tac ctxt @{thms z3div_def z3mod_def})
  THEN' Arith_Data.arith_tac ctxt

fun arith_th_lemma ctxt thms t =
  prove_abstract ctxt thms t arith_th_lemma_tac (
    fold_map (abstract_arith ctxt o dest_thm) thms ##>>
    abstract_arith ctxt (dest_prop t))

val _ = Theory.setup (Context.theory_map (add_th_lemma_method ("arith", arith_th_lemma)))

fun th_lemma name ctxt thms =
  (case Symtab.lookup (get_th_lemma_method ctxt) name of
    SOME method => method ctxt thms
  | NONE => replay_error ctxt "Bad theory" (Z3_New_Proof.Th_Lemma name) thms)


(* mapping of rules to methods *)

fun unsupported rule ctxt = replay_error ctxt "Unsupported" rule
fun assumed rule ctxt = replay_error ctxt "Assumed" rule

fun choose Z3_New_Proof.True_Axiom = true_axiom
  | choose (r as Z3_New_Proof.Asserted) = assumed r
  | choose (r as Z3_New_Proof.Goal) = assumed r
  | choose Z3_New_Proof.Modus_Ponens = mp
  | choose Z3_New_Proof.Reflexivity = refl
  | choose Z3_New_Proof.Symmetry = symm
  | choose Z3_New_Proof.Transitivity = trans
  | choose (r as Z3_New_Proof.Transitivity_Star) = unsupported r
  | choose Z3_New_Proof.Monotonicity = cong
  | choose Z3_New_Proof.Quant_Intro = quant_intro
  | choose Z3_New_Proof.Distributivity = distrib
  | choose Z3_New_Proof.And_Elim = and_elim
  | choose Z3_New_Proof.Not_Or_Elim = not_or_elim
  | choose Z3_New_Proof.Rewrite = rewrite
  | choose Z3_New_Proof.Rewrite_Star = rewrite_star
  | choose Z3_New_Proof.Pull_Quant = pull_quant
  | choose (r as Z3_New_Proof.Pull_Quant_Star) = unsupported r
  | choose Z3_New_Proof.Push_Quant = push_quant
  | choose Z3_New_Proof.Elim_Unused_Vars = elim_unused
  | choose Z3_New_Proof.Dest_Eq_Res = dest_eq_res
  | choose Z3_New_Proof.Quant_Inst = quant_inst
  | choose (r as Z3_New_Proof.Hypothesis) = assumed r
  | choose Z3_New_Proof.Lemma = lemma
  | choose Z3_New_Proof.Unit_Resolution = unit_res
  | choose Z3_New_Proof.Iff_True = iff_true
  | choose Z3_New_Proof.Iff_False = iff_false
  | choose Z3_New_Proof.Commutativity = comm
  | choose Z3_New_Proof.Def_Axiom = def_axiom
  | choose (r as Z3_New_Proof.Intro_Def) = assumed r
  | choose Z3_New_Proof.Apply_Def = apply_def
  | choose Z3_New_Proof.Iff_Oeq = iff_oeq
  | choose Z3_New_Proof.Nnf_Pos = nnf_pos
  | choose Z3_New_Proof.Nnf_Neg = nnf_neg
  | choose (r as Z3_New_Proof.Nnf_Star) = unsupported r
  | choose (r as Z3_New_Proof.Cnf_Star) = unsupported r
  | choose (r as Z3_New_Proof.Skolemize) = assumed r
  | choose Z3_New_Proof.Modus_Ponens_Oeq = mp_oeq
  | choose (Z3_New_Proof.Th_Lemma name) = th_lemma name

fun with_tracing rule method ctxt thms t =
  let val _ = trace_goal ctxt rule thms t
  in method ctxt thms t end

fun method_for rule = with_tracing rule (choose rule)

end;
