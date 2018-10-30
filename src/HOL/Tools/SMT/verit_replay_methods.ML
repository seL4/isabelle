(*  Title:      HOL/Tools/SMT/verit_replay_methods.ML
    Author:     Mathias Fleury, MPII

Proof methods for replaying veriT proofs.
*)

signature VERIT_REPLAY_METHODS =
sig

  val is_skolemisation: string -> bool
  val is_skolemisation_step: VeriT_Proof.veriT_replay_node -> bool

  (* methods for veriT proof rules *)
  val method_for: string -> Proof.context -> thm list -> term list -> term ->
     thm

  val veriT_step_requires_subproof_assms : string -> bool
  val eq_congruent_pred: Proof.context -> 'a -> term -> thm
end;


structure Verit_Replay_Methods: VERIT_REPLAY_METHODS =
struct

(*Some general comments on the proof format:
  1. Double negations are not always removed. This means for example that the equivalence rules
     cannot assume that the double negations have already been removed. Therefore, we match the
     term, instantiate the theorem, then use simp (to remove double negations), and finally use
     assumption.
  2. The reconstruction for rule forall_inst is buggy and tends to be very fragile, because the rule
     is doing much more that is supposed to do. Moreover types can make trivial goals (for the
     boolean structure) impossible to prove.
  3. Duplicate literals are sometimes removed, mostly by the SAT solver. We currently do not care
     about it, since in all cases we have met, a rule like tmp_AC_simp is called to do the
     simplification.

  Rules unsupported on purpose:
    * Distinct_Elim, XOR, let (we don't need them).
    * tmp_skolemize (because it is not clear if veriT still generates using it).
*)

datatype verit_rule =
   False | True |

   (* input: a repeated (normalized) assumption of  assumption of in a subproof *)
   Normalized_Input | Local_Input |
   (* Subproof: *)
   Subproof |
   (* Conjunction: *)
   And | Not_And | And_Pos | And_Neg |
   (* Disjunction"" *)
   Or | Or_Pos | Not_Or | Or_Neg |
   (* Disjunction: *)
   Implies | Implies_Neg1 | Implies_Neg2 | Implies_Pos | Not_Implies1 | Not_Implies2 |
   (* Equivalence: *)
   Equiv_neg1 | Equiv_pos1 | Equiv_pos2 | Equiv_neg2 | Not_Equiv1 | Not_Equiv2 | Equiv1 | Equiv2 |
   (* If-then-else: *)
   ITE_Pos1 | ITE_Pos2 | ITE_Neg1 | ITE_Neg2 | Not_ITE1 | Not_ITE2 | ITE_Intro | ITE1 | ITE2 |
   (* Equality: *)
   Eq_Congruent | Eq_Reflexive | Eq_Transitive | Eq_Congruent_Pred | Trans |  Refl |  Cong |
   (* Arithmetics: *)
   LA_Disequality | LA_Generic | LA_Tautology |  LIA_Generic | LA_Totality | LA_RW_Eq |
   NLA_Generic |
   (* Quantifiers: *)
   Forall_Inst | Qnt_Rm_Unused | Qnt_Join | Qnt_Simplify | Bind | Skolem_Forall | Skolem_Ex |
   (* Resolution: *)
   Theory_Resolution | Resolution |
   (* Various transformation: *)
   Connective_Equiv |
   (* Temporary rules, that the veriT developpers want to remove: *)
   Tmp_AC_Simp |
   Tmp_Bfun_Elim |
   (* Unsupported rule *)
   Unsupported

val is_skolemisation = member (op =) ["sko_forall", "sko_ex"]
fun is_skolemisation_step (VeriT_Proof.VeriT_Replay_Node {id, ...}) = is_skolemisation id

fun verit_rule_of "bind" = Bind
  | verit_rule_of "cong" = Cong
  | verit_rule_of "refl" = Refl
  | verit_rule_of "equiv1" = Equiv1
  | verit_rule_of "equiv2" = Equiv2
  | verit_rule_of "equiv_pos1" = Equiv_pos1
  | verit_rule_of "equiv_pos2" = Equiv_pos2
  | verit_rule_of "equiv_neg1" = Equiv_neg1
  | verit_rule_of "equiv_neg2" = Equiv_neg2
  | verit_rule_of "sko_forall" = Skolem_Forall
  | verit_rule_of "sko_ex" = Skolem_Ex
  | verit_rule_of "eq_reflexive" = Eq_Reflexive
  | verit_rule_of "th_resolution" = Theory_Resolution
  | verit_rule_of "forall_inst" = Forall_Inst
  | verit_rule_of "implies_pos" = Implies_Pos
  | verit_rule_of "or" = Or
  | verit_rule_of "not_or" = Not_Or
  | verit_rule_of "resolution" = Resolution
  | verit_rule_of "eq_congruent" = Eq_Congruent
  | verit_rule_of "connective_equiv" = Connective_Equiv
  | verit_rule_of "trans" = Trans
  | verit_rule_of "false" = False
  | verit_rule_of "tmp_AC_simp" = Tmp_AC_Simp
  | verit_rule_of "and" = And
  | verit_rule_of "not_and" = Not_And
  | verit_rule_of "and_pos" = And_Pos
  | verit_rule_of "and_neg" = And_Neg
  | verit_rule_of "or_pos" = Or_Pos
  | verit_rule_of "or_neg" = Or_Neg
  | verit_rule_of "not_equiv1" = Not_Equiv1
  | verit_rule_of "not_equiv2" = Not_Equiv2
  | verit_rule_of "not_implies1" = Not_Implies1
  | verit_rule_of "not_implies2" = Not_Implies2
  | verit_rule_of "implies_neg1" = Implies_Neg1
  | verit_rule_of "implies_neg2" = Implies_Neg2
  | verit_rule_of "implies" = Implies
  | verit_rule_of "tmp_bfun_elim" = Tmp_Bfun_Elim
  | verit_rule_of "ite1" = ITE1
  | verit_rule_of "ite2" = ITE2
  | verit_rule_of "not_ite1" = Not_ITE1
  | verit_rule_of "not_ite2" = Not_ITE2
  | verit_rule_of "ite_pos1" = ITE_Pos1
  | verit_rule_of "ite_pos2" = ITE_Pos2
  | verit_rule_of "ite_neg1" = ITE_Neg1
  | verit_rule_of "ite_neg2" = ITE_Neg2
  | verit_rule_of "ite_intro" = ITE_Intro
  | verit_rule_of "la_disequality" = LA_Disequality
  | verit_rule_of "lia_generic" = LIA_Generic
  | verit_rule_of "la_generic" = LA_Generic
  | verit_rule_of "la_tautology" = LA_Tautology
  | verit_rule_of "la_totality" = LA_Totality
  | verit_rule_of "la_rw_eq"= LA_RW_Eq
  | verit_rule_of "nla_generic"= NLA_Generic
  | verit_rule_of "eq_transitive" = Eq_Transitive
  | verit_rule_of "qnt_rm_unused" = Qnt_Rm_Unused
  | verit_rule_of "qnt_simplify" = Qnt_Simplify
  | verit_rule_of "qnt_join" = Qnt_Join
  | verit_rule_of "eq_congruent_pred" = Eq_Congruent_Pred
  | verit_rule_of "subproof" = Subproof
  | verit_rule_of r =
     if r = VeriT_Proof.veriT_normalized_input_rule then Normalized_Input
     else if r = VeriT_Proof.veriT_local_input_rule then Local_Input
     else Unsupported

fun string_of_verit_rule Bind = "Bind"
  | string_of_verit_rule Cong = "Cong"
  | string_of_verit_rule Refl = "Refl"
  | string_of_verit_rule Equiv1 = "Equiv1"
  | string_of_verit_rule Equiv2 = "Equiv2"
  | string_of_verit_rule Equiv_pos1 = "Equiv_pos1"
  | string_of_verit_rule Equiv_pos2 = "Equiv_pos2"
  | string_of_verit_rule Equiv_neg1 = "Equiv_neg1"
  | string_of_verit_rule Equiv_neg2 = "Equiv_neg2"
  | string_of_verit_rule Skolem_Forall = "Skolem_Forall"
  | string_of_verit_rule Skolem_Ex = "Skolem_Ex"
  | string_of_verit_rule Eq_Reflexive = "Eq_Reflexive"
  | string_of_verit_rule Theory_Resolution = "Theory_Resolution"
  | string_of_verit_rule Forall_Inst = "forall_inst"
  | string_of_verit_rule Or = "Or"
  | string_of_verit_rule Not_Or = "Not_Or"
  | string_of_verit_rule Resolution = "Resolution"
  | string_of_verit_rule Eq_Congruent = "eq_congruent"
  | string_of_verit_rule Connective_Equiv = "connective_equiv"
  | string_of_verit_rule Trans = "trans"
  | string_of_verit_rule False = "false"
  | string_of_verit_rule And = "and"
  | string_of_verit_rule And_Pos = "and_pos"
  | string_of_verit_rule Not_And = "not_and"
  | string_of_verit_rule And_Neg = "and_neg"
  | string_of_verit_rule Or_Pos = "or_pos"
  | string_of_verit_rule Or_Neg = "or_neg"
  | string_of_verit_rule Tmp_AC_Simp = "tmp_AC_simp"
  | string_of_verit_rule Not_Equiv1 = "not_equiv1"
  | string_of_verit_rule Not_Equiv2 = "not_equiv2"
  | string_of_verit_rule Not_Implies1 = "not_implies1"
  | string_of_verit_rule Not_Implies2 = "not_implies2"
  | string_of_verit_rule Implies_Neg1 = "implies_neg1"
  | string_of_verit_rule Implies_Neg2 = "implies_neg2"
  | string_of_verit_rule Implies = "implies"
  | string_of_verit_rule Tmp_Bfun_Elim = "tmp_bfun_elim"
  | string_of_verit_rule ITE1 = "ite1"
  | string_of_verit_rule ITE2 = "ite2"
  | string_of_verit_rule Not_ITE1 = "not_ite1"
  | string_of_verit_rule Not_ITE2 = "not_ite2"
  | string_of_verit_rule ITE_Pos1 = "ite_pos1"
  | string_of_verit_rule ITE_Pos2 = "ite_pos2"
  | string_of_verit_rule ITE_Neg1 = "ite_neg1"
  | string_of_verit_rule ITE_Neg2 = "ite_neg2"
  | string_of_verit_rule ITE_Intro = "ite_intro"
  | string_of_verit_rule LA_Disequality = "la_disequality"
  | string_of_verit_rule LA_Generic = "la_generic"
  | string_of_verit_rule LIA_Generic = "lia_generic"
  | string_of_verit_rule LA_Tautology = "la_tautology"
  | string_of_verit_rule LA_RW_Eq = "la_rw_eq"
  | string_of_verit_rule LA_Totality = "LA_Totality"
  | string_of_verit_rule NLA_Generic = "nla_generic"
  | string_of_verit_rule Eq_Transitive = "eq_transitive"
  | string_of_verit_rule Qnt_Rm_Unused = "qnt_remove_unused"
  | string_of_verit_rule Qnt_Simplify = "qnt_simplify"
  | string_of_verit_rule Qnt_Join = "qnt_join"
  | string_of_verit_rule Eq_Congruent_Pred = "eq_congruent_pred"
  | string_of_verit_rule Normalized_Input = VeriT_Proof.veriT_normalized_input_rule
  | string_of_verit_rule Local_Input = VeriT_Proof.veriT_normalized_input_rule
  | string_of_verit_rule Subproof = "subproof"
  | string_of_verit_rule r = "Unsupported rule: " ^ @{make_string} r

(*** Methods to Replay Normal steps ***)
(* sko_forall requires the assumptions to be able to SMT_Replay_Methods.prove the equivalence in case of double
skolemization. See comment below. *)
fun veriT_step_requires_subproof_assms t =
  member (op =) ["refl", "cong", VeriT_Proof.veriT_local_input_rule, "sko_forall",
    "sko_ex"] t

fun simplify_tac ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms not_not eq_commute} addsimps thms)
  |> Simplifier.full_simp_tac

val bind_thms =
  [@{lemma "(\<And>x x'. P x = Q x) \<Longrightarrow> (\<forall>x. P x) = (\<forall>y. Q y)"
      by blast},
   @{lemma "(\<And>x x'.  P x = Q x) \<Longrightarrow> (\<exists>x. P x) = (\<exists>y. Q y)"
      by blast},
   @{lemma "(\<And>x x'.  P x = Q x) \<Longrightarrow> (\<exists>x. P x = Q x)"
      by blast},
   @{lemma "(\<And>x x'.  P x = Q x) \<Longrightarrow> (\<forall>x. P x = Q x)"
      by blast}]

fun TRY' tac = fn i => TRY (tac i)
fun REPEAT' tac = fn i => REPEAT (tac i)
fun REPEAT_CHANGED tac = fn i => REPEAT (CHANGED (tac i))

fun bind ctxt [prems] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
    REPEAT' (resolve_tac ctxt bind_thms)
    THEN' match_tac ctxt [prems]
    THEN' simplify_tac ctxt []
    THEN' REPEAT' (match_tac ctxt [@{thm refl}]))


fun refl ctxt thm t =
  (case find_first (fn thm => t = Thm.full_prop_of thm) thm of
      SOME thm => thm
    | NONE =>
        (case try (Z3_Replay_Methods.refl ctxt thm) t of
          NONE =>
          ( Z3_Replay_Methods.cong ctxt thm t)
        | SOME thm => thm))

local
  fun equiv_pos_neg_term ctxt thm (@{term Trueprop} $
         (@{term HOL.disj} $ (_) $
            ((@{term HOL.disj} $ a $ b)))) =
     Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm

  fun prove_equiv_pos_neg thm ctxt _ t =
    let val thm = equiv_pos_neg_term ctxt thm t
    in
      SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [thm]
        THEN' simplify_tac ctxt [])
    end
in

val equiv_pos1_thm =
  @{lemma "\<not>(a \<longleftrightarrow> ~b) \<or> a \<or> b"
      by blast+}

val equiv_pos1 = prove_equiv_pos_neg equiv_pos1_thm

val equiv_pos2_thm =
  @{lemma  "\<And>a b. ((\<not>a) \<noteq> b) \<or> a \<or> b"
      by blast+}

val equiv_pos2 = prove_equiv_pos_neg equiv_pos2_thm

val equiv_neg1_thm =
  @{lemma "(~a \<longleftrightarrow> ~b) \<or> a \<or> b"
      by blast}

val equiv_neg1 = prove_equiv_pos_neg equiv_neg1_thm

val equiv_neg2_thm =
  @{lemma "(a \<longleftrightarrow> b) \<or> a \<or> b"
      by blast}

val equiv_neg2 = prove_equiv_pos_neg equiv_neg2_thm

end

(* Most of the code below is due to the proof output of veriT: The description of the rule is wrong
(and according to Pascal Fontaine, it is a bug). Anyway, currently, forall_inst does:
  1. swapping out the forall quantifiers
  2. instantiation
  3. boolean.

However, types can mess-up things:
  lemma  \<open>(0 < degree a) = (0 \<noteq> degree a) \<Longrightarrow> 0 = degree a \<or> 0 < degree a\<close>
    by fast
works unlike
  lemma  \<open>((0::nat) < degree a) = (0 \<noteq> degree a) \<Longrightarrow> 0 = degree a \<or> 0 < degree a\<close>
    by fast.
Therefore, we use fast and auto as fall-back.
*)
fun forall_inst ctxt _ args t =
  let
    val instantiate =
       fold (fn inst => fn tac =>
         let val thm = Drule.infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt inst)] @{thm spec}
         in tac THEN' dmatch_tac ctxt [thm]end)
         args
         (K all_tac)
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}]]
      THEN' TRY' (Raw_Simplifier.rewrite_goal_tac ctxt @{thms all_simps[symmetric] not_all})
      THEN' TRY' instantiate
      THEN' TRY' (simplify_tac ctxt [])
      THEN' TRY' (SOLVED' (fn _ => HEADGOAL ( (assume_tac ctxt)
         ORELSE'
            TRY' (dresolve_tac ctxt @{thms conjE}
              THEN_ALL_NEW assume_tac ctxt)
         ORELSE'
            TRY' (dresolve_tac ctxt @{thms verit_forall_inst}
              THEN_ALL_NEW assume_tac ctxt))))
      THEN' (TRY' (Classical.fast_tac ctxt))
      THEN' (TRY' (K (Clasimp.auto_tac ctxt))))
    end

fun or _ [thm] _ = thm

val implies_pos_thm =
  [@{lemma "\<not>(A \<longrightarrow> B) \<or> \<not>A \<or> B"
      by blast},
  @{lemma "\<not>(\<not>A \<longrightarrow> B) \<or> A \<or> B"
      by blast}]

fun implies_pos ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt implies_pos_thm)

fun extract_rewrite_rule_assumption thms =
  let
    fun is_rewrite_rule thm =
      (case Thm.prop_of thm of
        @{term Trueprop} $ (Const(@{const_name HOL.eq}, _) $ Free(_, _) $ _) => true
      | _ => false)
  in
    thms
    |> filter is_rewrite_rule
    |> map (fn thm => thm COMP @{thm eq_reflection})
  end

(* We need to unfold the assumptions if we are in a subproof: For multiple skolemization, the context
contains a mapping "verit_vrX \<leadsto> Eps f". The variable "verit_vrX" must be unfolded to "Eps f".
Otherwise, the proof cannot be done. *)
fun skolem_forall ctxt (thms) t  =
  let
    val ts = extract_rewrite_rule_assumption thms
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      REPEAT_CHANGED (resolve_tac ctxt @{thms verit_sko_forall'})
      THEN' TRY' (simplify_tac ctxt ts)
      THEN' TRY'(resolve_tac ctxt thms THEN_ALL_NEW resolve_tac ctxt @{thms refl})
      THEN' TRY' (resolve_tac ctxt @{thms refl}))
  end

fun skolem_ex ctxt (thms) t  =
  let
    val ts = extract_rewrite_rule_assumption thms
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      Raw_Simplifier.rewrite_goal_tac ctxt ts
      THEN' REPEAT_CHANGED (resolve_tac ctxt @{thms verit_sko_ex'})
      THEN' REPEAT_CHANGED (resolve_tac ctxt thms THEN_ALL_NEW resolve_tac ctxt @{thms refl})
      THEN' TRY' (resolve_tac ctxt @{thms refl}))
  end

fun eq_reflexive ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [@{thm refl}])

fun connective_equiv ctxt thms t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt thms
  THEN' K (Clasimp.auto_tac ctxt))


fun normalized_input ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt prems
  THEN' TRY' (simplify_tac ctxt [])
  THEN' TRY' (K (Clasimp.auto_tac ctxt)))

val false_rule_thm = @{lemma "\<not>False" by blast}

fun false_rule ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [false_rule_thm])


(* transitivity *)

val trans_bool_thm =
  @{lemma "P = Q \<Longrightarrow> Q \<Longrightarrow> P" by blast}
fun trans _ [thm1, thm2] _ =
      (case (Thm.full_prop_of thm1, Thm.full_prop_of thm2) of
        (@{term Trueprop} $ (Const(@{const_name HOL.eq}, _) $ _ $ t2),
         @{term Trueprop} $ (Const(@{const_name HOL.eq}, _) $ t3 $ _)) =>
        if t2 = t3 then thm1 RSN (1, thm2 RSN (2, @{thm trans}))
        else thm1 RSN (1, (thm2 RS sym) RSN (2, @{thm trans}))
      | _ => trans_bool_thm OF [thm1, thm2])
  | trans ctxt (thm1 :: thm2 :: thms) t =
      trans ctxt (trans ctxt [thm1, thm2] t :: thms) t

fun tmp_AC_rule ctxt _ t =
 let
   val simplify =
     ctxt
     |> empty_simpset
     |> put_simpset HOL_basic_ss
     |> (fn ctxt => ctxt addsimps @{thms ac_simps conj_ac})
     |> Simplifier.full_simp_tac
 in SMT_Replay_Methods.prove ctxt t (fn _ =>
   REPEAT_ALL_NEW (simplify_tac ctxt []
     THEN' TRY' simplify
     THEN' TRY' (Classical.fast_tac ctxt))) end

fun and_rule ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
   Method.insert_tac ctxt prems
   THEN' (fn i => REPEAT (dresolve_tac ctxt @{thms conjE} i THEN assume_tac ctxt (i+1)))
   THEN' TRY' (assume_tac ctxt)
   THEN' TRY' (simplify_tac ctxt []))

fun not_and_rule ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
   Method.insert_tac ctxt prems THEN'
   Classical.fast_tac ctxt ORELSE' Clasimp.force_tac ctxt)

fun not_or_rule ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
   Method.insert_tac ctxt prems THEN'
   Classical.fast_tac ctxt ORELSE' Clasimp.force_tac ctxt)

local
  fun simplify_and_pos ctxt =
    ctxt
    |> empty_simpset
    |> put_simpset HOL_basic_ss
    |> (fn ctxt => ctxt addsimps @{thms eq_commute verit_ite_intro_simp if_cancel}
         addsimps @{thms simp_thms de_Morgan_conj})
    |> Simplifier.full_simp_tac
in

fun and_pos ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  REPEAT_CHANGED (resolve_tac ctxt @{thms verit_and_pos})
  THEN' TRY' (simplify_and_pos ctxt)
  THEN' TRY' (assume_tac ctxt)
  THEN' TRY' (Classical.fast_tac ctxt))

end

fun and_neg_rule ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  REPEAT_CHANGED (resolve_tac ctxt @{thms verit_and_neg})
  THEN' simplify_tac ctxt @{thms de_Morgan_conj[symmetric] excluded_middle
    excluded_middle[of \<open>\<not>_\<close>, unfolded not_not]})

fun or_pos_rule ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  simplify_tac ctxt @{thms simp_thms})

fun or_neg_rule ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt @{thms verit_or_neg}
  THEN' (fn i => dresolve_tac ctxt @{thms verit_subst_bool} i
     THEN assume_tac ctxt (i+1))
  THEN' simplify_tac ctxt @{thms simp_thms})

val not_equiv1_thm =
  @{lemma "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> A \<or> B"
      by blast}

fun not_equiv1 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [not_equiv1_thm OF [thm]]
  THEN' simplify_tac ctxt [])

val not_equiv2_thm =
  @{lemma "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<or> \<not>B"
      by blast}

fun not_equiv2 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [not_equiv2_thm OF [thm]]
  THEN' simplify_tac ctxt [])

val equiv1_thm =
  @{lemma "(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<or> B"
      by blast}

fun equiv1 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [equiv1_thm OF [thm]]
  THEN' simplify_tac ctxt [])

val equiv2_thm =
  @{lemma "(A \<longleftrightarrow> B) \<Longrightarrow> A \<or> \<not>B"
      by blast}

fun equiv2 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [equiv2_thm OF [thm]]
  THEN' simplify_tac ctxt [])


val not_implies1_thm =
  @{lemma "\<not>(A \<longrightarrow> B) \<Longrightarrow> A"
      by blast}

fun not_implies1 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [not_implies1_thm OF [thm]]
  THEN' simplify_tac ctxt [])

val not_implies2_thm =
  @{lemma "\<not>(A \<longrightarrow>B) \<Longrightarrow> \<not>B"
      by blast}

fun not_implies2 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [not_implies2_thm OF [thm]]
  THEN' simplify_tac ctxt [])


local
  fun implies_pos_neg_term ctxt thm (@{term Trueprop} $
         (@{term HOL.disj} $ (@{term HOL.implies} $ a $ b) $ _)) =
     Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm

  fun prove_implies_pos_neg thm ctxt _ t =
    let val thm = implies_pos_neg_term ctxt thm t
    in
      SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [thm]
        THEN' simplify_tac ctxt [])
    end
in

val implies_neg1_thm =
  @{lemma "(a \<longrightarrow> b) \<or> a"
      by blast}

val implies_neg1  = prove_implies_pos_neg implies_neg1_thm

val implies_neg2_thm =
  @{lemma "(a \<longrightarrow> b) \<or> \<not>b" by blast}

val implies_neg2 = prove_implies_pos_neg implies_neg2_thm

end

val implies_thm =
  @{lemma "(~a \<longrightarrow> b) \<Longrightarrow> a \<or> b"
       "(a \<longrightarrow> b) \<Longrightarrow> \<not>a \<or> b"
     by blast+}

fun implies_rules ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt prems
  THEN' resolve_tac ctxt implies_thm
  THEN' assume_tac ctxt)


(*
Here is a case where force_tac fails, but auto_tac succeeds:
   Ex (P x) \<noteq> P x c \<Longrightarrow>
   (\<exists>v0. if x then P True v0 else P False v0) \<noteq> (if x then P True c else P False c)

(this was before we added the eqsubst_tac). Therefore, to be safe, we add the fast, auto, and force.
*)
fun tmp_bfun_elim ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt prems
  THEN' REPEAT_CHANGED (EqSubst.eqsubst_tac ctxt [0] @{thms verit_tmp_bfun_elim})
  THEN' TRY' (simplify_tac ctxt [])
  THEN' (Classical.fast_tac ctxt
    ORELSE' K (Clasimp.auto_tac ctxt)
    ORELSE' Clasimp.force_tac ctxt))

val ite_pos1_thm =
  @{lemma "\<not>(if x then P else Q) \<or> x \<or> Q"
      by auto}

fun ite_pos1 ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [ite_pos1_thm])

val ite_pos2_thms =
  @{lemma "\<not>(if x then P else Q) \<or> \<not>x \<or> P" "\<not>(if \<not>x then P else Q) \<or> x \<or> P"
      by auto}

fun ite_pos2 ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt ite_pos2_thms)

val ite_neg1_thms =
  @{lemma "(if x then P else Q) \<or> x \<or> \<not>Q" "(if x then P else \<not>Q) \<or> x \<or> Q"
      by auto}

fun ite_neg1 ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt ite_neg1_thms)

val ite_neg2_thms =
  @{lemma "(if x then P else Q) \<or> \<not>x \<or> \<not>P" "(if \<not>x then P else Q) \<or> x \<or> \<not>P"
          "(if x then \<not>P else Q) \<or> \<not>x \<or> P" "(if \<not>x then \<not>P else Q) \<or> x \<or> P"
      by auto}

fun ite_neg2 ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt ite_neg2_thms)

val ite1_thm =
  @{lemma "(if x then P else Q) \<Longrightarrow> x \<or> Q"
      by (auto split: if_splits) }

fun ite1 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [ite1_thm OF [thm]])

val ite2_thm =
  @{lemma "(if x then P else Q) \<Longrightarrow> \<not>x \<or> P"
      by (auto split: if_splits) }

fun ite2 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [ite2_thm OF [thm]])


val not_ite1_thm =
  @{lemma "\<not>(if x then P else Q) \<Longrightarrow> x \<or> \<not>Q"
      by (auto split: if_splits) }

fun not_ite1 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [not_ite1_thm OF [thm]])

val not_ite2_thm =
  @{lemma "\<not>(if x then P else Q) \<Longrightarrow> \<not>x \<or> \<not>P"
      by (auto split: if_splits) }

fun not_ite2 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [not_ite2_thm OF [thm]])


fun unit_res ctxt thms t =
  let
    val thms = map (Conv.fconv_rule Thm.eta_long_conversion) thms
    val t' = Thm.eta_long_conversion (Object_Logic.dest_judgment ctxt (Thm.cterm_of ctxt t))
    val (_, t2) = Logic.dest_equals (Thm.prop_of t')
    val thm = Z3_Replay_Methods.unit_res ctxt thms t2
  in
    @{thm verit_Pure_trans} OF [t', thm]
  end

fun ite_intro ctxt _ t =
  let
    fun simplify_ite ctxt =
      ctxt
      |> empty_simpset
      |> put_simpset HOL_basic_ss
      |> (fn ctxt => ctxt addsimps @{thms eq_commute verit_ite_intro_simp if_cancel}
           addsimps @{thms simp_thms})
      |> Simplifier.full_simp_tac
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
     (simplify_ite ctxt
     THEN' TRY' (Blast.blast_tac ctxt
       ORELSE' K (Clasimp.auto_tac ctxt)
       ORELSE' Clasimp.force_tac ctxt)))
  end


(* Quantifiers *)

fun qnt_rm_unused ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Classical.fast_tac ctxt)

fun qnt_simplify ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Classical.fast_tac ctxt)

fun qnt_join ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Classical.fast_tac ctxt)


(* Equality *)

fun eq_transitive ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn  _ =>
  REPEAT_CHANGED (resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF @{thms impI}])
  THEN' REPEAT' (resolve_tac ctxt @{thms impI})
  THEN' REPEAT' (eresolve_tac ctxt @{thms conjI})
  THEN' REPEAT' (fn i => dresolve_tac ctxt @{thms verit_eq_transitive} i THEN assume_tac ctxt (i+1))
  THEN' resolve_tac ctxt @{thms refl})

local

  (* Rewrite might apply below choice. As we do not want to change them (it can break other
  rewriting steps), we cannot use Term.lambda *)
  fun abstract_over_no_choice (v, body) =
    let
      fun abs lev tm =
        if v aconv tm then Bound lev
        else
          (case tm of
            Abs (a, T, t) => Abs (a, T, abs (lev + 1) t)
          | t as (Const (\<^const_name>\<open>Hilbert_Choice.Eps\<close>, _) $ _) => t
          | t $ u =>
              (abs lev t $ (abs lev u handle Same.SAME => u)
                handle Same.SAME => t $ abs lev u)
          | _ => raise Same.SAME);
    in abs 0 body handle Same.SAME => body end;

  fun lambda_name (x, v) t =
    Abs (if x = "" then Term.term_name v else x, fastype_of v, abstract_over_no_choice (v, t));

  fun lambda v t = lambda_name ("", v) t;

  fun extract_equal_terms (Const(\<^const_name>\<open>Trueprop\<close>, _) $ t) =
    let fun ext (Const(\<^const_name>\<open>HOL.disj\<close>, _) $ (Const(\<^const_name>\<open>HOL.Not\<close>, _) $
             (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2)) $ t) =
           apfst (curry (op ::) (t1, t2)) (ext t)
          | ext t = ([], t)
    in ext t end
  fun eq_congruent_tac ctxt t =
    let
       val (eqs, g) = extract_equal_terms t
       fun replace1 (t1, t2) (g, tac) =
         let
           val abs_t1 = lambda t2 g
           val subst = Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [t1, t2, abs_t1])
                @{thm subst}
         in (Term.betapply (abs_t1, t1),
             tac THEN' resolve_tac ctxt [subst]
                 THEN' TRY' (assume_tac ctxt)) end
       val (_, tac) = fold replace1 eqs (g, K all_tac)
    in
       tac
    end
in

fun eq_congruent_pred ctxt _ t =
   SMT_Replay_Methods.prove ctxt t (fn _ =>
   REPEAT' (resolve_tac ctxt [@{thm disj_not1[of \<open>_ = _\<close>]} RSN (1, @{thm iffD2}) OF @{thms impI}])
   THEN' REPEAT' (eresolve_tac ctxt @{thms conjI})
   THEN' eq_congruent_tac ctxt t
   THEN' resolve_tac ctxt @{thms refl excluded_middle
     excluded_middle[of \<open>\<not>_\<close>, unfolded not_not]})

end


(* subproof *)

fun subproof ctxt [prem] t =
 SMT_Replay_Methods.prove ctxt t (fn _ =>
   (resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}],
        @{thm disj_not1[of \<open>\<not>_\<close>, unfolded not_not]} RSN (1, @{thm iffD2}) OF [@{thm impI}]]
     THEN' resolve_tac ctxt [prem]
     THEN_ALL_NEW assume_tac ctxt
     THEN' TRY' (assume_tac ctxt))
   ORELSE' TRY' (Method.insert_tac ctxt [prem] THEN' Blast.blast_tac ctxt))


(* la_rw_eq *)

val la_rw_eq_thm = @{lemma \<open>(a :: nat) = b \<or> (a \<le> b) \<or> (a \<ge> b)\<close>
  by auto}

fun la_rw_eq ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [la_rw_eq_thm])

(* congruence *)
fun cong ctxt thms = SMT_Replay_Methods.try_provers ctxt
    (string_of_verit_rule Cong) [
  ("basic", SMT_Replay_Methods.cong_basic ctxt thms),
  ("full", SMT_Replay_Methods.cong_full ctxt thms),
  ("unfolding then auto", SMT_Replay_Methods.cong_unfolding_first ctxt thms)] thms


fun unsupported rule ctxt thms _ t = SMT_Replay_Methods.replay_error ctxt "Unsupported verit rule"
  rule thms t

fun ignore_args f ctxt thm _ t = f ctxt thm t

fun choose Bind = ignore_args bind
  | choose Refl = ignore_args refl
  | choose And_Pos = ignore_args and_pos
  | choose And_Neg = ignore_args and_neg_rule
  | choose Cong = ignore_args cong
  | choose Equiv_pos1 = ignore_args equiv_pos1
  | choose Equiv_pos2 = ignore_args equiv_pos2
  | choose Equiv_neg1 = ignore_args equiv_neg1
  | choose Equiv_neg2 = ignore_args equiv_neg2
  | choose Equiv1 = ignore_args equiv1
  | choose Equiv2 = ignore_args equiv2
  | choose Not_Equiv1 = ignore_args not_equiv1
  | choose Not_Equiv2 = ignore_args not_equiv2
  | choose Not_Implies1 = ignore_args not_implies1
  | choose Not_Implies2 = ignore_args not_implies2
  | choose Implies_Neg1 = ignore_args implies_neg1
  | choose Implies_Neg2 = ignore_args implies_neg2
  | choose Implies_Pos = ignore_args implies_pos
  | choose Implies = ignore_args implies_rules
  | choose Forall_Inst = forall_inst
  | choose Skolem_Forall = ignore_args skolem_forall
  | choose Skolem_Ex = ignore_args skolem_ex
  | choose Or = ignore_args or
  | choose Theory_Resolution = ignore_args unit_res
  | choose Resolution = ignore_args unit_res
  | choose Eq_Reflexive = ignore_args eq_reflexive
  | choose Connective_Equiv = ignore_args connective_equiv
  | choose Trans = ignore_args trans
  | choose False = ignore_args false_rule
  | choose Tmp_AC_Simp = ignore_args tmp_AC_rule
  | choose And = ignore_args and_rule
  | choose Not_And = ignore_args not_and_rule
  | choose Not_Or = ignore_args not_or_rule
  | choose Or_Pos = ignore_args or_pos_rule
  | choose Or_Neg = ignore_args or_neg_rule
  | choose Tmp_Bfun_Elim = ignore_args tmp_bfun_elim
  | choose ITE1 = ignore_args ite1
  | choose ITE2 = ignore_args ite2
  | choose Not_ITE1 = ignore_args not_ite1
  | choose Not_ITE2 = ignore_args not_ite2
  | choose ITE_Pos1 = ignore_args ite_pos1
  | choose ITE_Pos2 = ignore_args ite_pos2
  | choose ITE_Neg1 = ignore_args ite_neg1
  | choose ITE_Neg2 = ignore_args ite_neg2
  | choose ITE_Intro = ignore_args ite_intro
  | choose LA_Disequality = ignore_args Z3_Replay_Methods.arith_th_lemma
  | choose LIA_Generic = ignore_args Z3_Replay_Methods.arith_th_lemma
  | choose LA_Generic = ignore_args Z3_Replay_Methods.arith_th_lemma
  | choose LA_Totality = ignore_args Z3_Replay_Methods.arith_th_lemma
  | choose LA_Tautology = ignore_args Z3_Replay_Methods.arith_th_lemma
  | choose LA_RW_Eq = ignore_args la_rw_eq
  | choose NLA_Generic = ignore_args Z3_Replay_Methods.arith_th_lemma
  | choose Normalized_Input = ignore_args normalized_input
  | choose Qnt_Rm_Unused = ignore_args qnt_rm_unused
  | choose Qnt_Simplify = ignore_args qnt_simplify
  | choose Qnt_Join = ignore_args qnt_join
  | choose Eq_Congruent_Pred = ignore_args eq_congruent_pred
  | choose Eq_Congruent = ignore_args eq_congruent_pred
  | choose Eq_Transitive = ignore_args eq_transitive
  | choose Local_Input = ignore_args refl
  | choose Subproof = ignore_args subproof
  | choose r = unsupported (string_of_verit_rule r)

type Verit_method = Proof.context -> thm list -> term -> thm
type abs_context = int * term Termtab.table

fun with_tracing rule method ctxt thms args t =
  let val _ = SMT_Replay_Methods.trace_goal ctxt rule thms t
  in method ctxt thms args t end

fun method_for rule = with_tracing rule (choose (verit_rule_of rule))

end;
