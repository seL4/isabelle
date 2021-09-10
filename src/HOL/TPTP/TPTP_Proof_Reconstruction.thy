(*  Title:      HOL/TPTP/TPTP_Proof_Reconstruction.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Proof reconstruction for Leo-II.

USAGE:
* Simple call the "reconstruct_leo2" function.
* For more advanced use, you could use the component functions used in
  "reconstruct_leo2" -- see TPTP_Proof_Reconstruction_Test.thy for
  examples of this.

This file contains definitions describing how to interpret LEO-II's
calculus in Isabelle/HOL, as well as more general proof-handling
functions. The definitions in this file serve to build an intermediate
proof script which is then evaluated into a tactic -- both these steps
are independent of LEO-II, and are defined in the TPTP_Reconstruct SML
module.

CONFIG:
The following attributes are mainly useful for debugging:
  tptp_unexceptional_reconstruction |
  unexceptional_reconstruction      |-- when these are true, a low-level exception
                                        is allowed to float to the top (instead of
                                        triggering a higher-level exception, or
                                        simply indicating that the reconstruction failed).
  tptp_max_term_size                --- fail of a term exceeds this size. "0" is taken
                                        to mean infinity.
  tptp_informative_failure          |
  informative_failure               |-- produce more output during reconstruction.
  tptp_trace_reconstruction         |

There are also two attributes, independent of the code here, that
influence the success of reconstruction: blast_depth_limit and
unify_search_bound. These are documented in their respective modules,
but in summary, if unify_search_bound is increased then we can
handle larger terms (at the cost of performance), since the unification
engine takes longer to give up the search; blast_depth_limit is
a limit on proof search performed by Blast. Blast is used for
the limited proof search that needs to be done to interpret
instances of LEO-II's inference rules.

TODO:
  use RemoveRedundantQuantifications instead of the ad hoc use of
   remove_redundant_quantification_in_lit and remove_redundant_quantification
*)

theory TPTP_Proof_Reconstruction
imports TPTP_Parser TPTP_Interpret
(* keywords "import_leo2_proof" :: thy_decl *) (*FIXME currently unused*)
begin


section "Setup"

ML \<open>
  val tptp_unexceptional_reconstruction = Attrib.setup_config_bool \<^binding>\<open>tptp_unexceptional_reconstruction\<close> (K false)
  fun unexceptional_reconstruction ctxt = Config.get ctxt tptp_unexceptional_reconstruction
  val tptp_informative_failure = Attrib.setup_config_bool \<^binding>\<open>tptp_informative_failure\<close> (K false)
  fun informative_failure ctxt = Config.get ctxt tptp_informative_failure
  val tptp_trace_reconstruction = Attrib.setup_config_bool \<^binding>\<open>tptp_trace_reconstruction\<close> (K false)
  val tptp_max_term_size = Attrib.setup_config_int \<^binding>\<open>tptp_max_term_size\<close> (K 0) (*0=infinity*)

  fun exceeds_tptp_max_term_size ctxt size =
    let
      val max = Config.get ctxt tptp_max_term_size
    in
      if max = 0 then false
      else size > max
    end
\<close>

(*FIXME move to TPTP_Proof_Reconstruction_Test_Units*)
declare [[
  tptp_unexceptional_reconstruction = false, (*NOTE should be "false" while testing*)
  tptp_informative_failure = true
]]

ML_file \<open>TPTP_Parser/tptp_reconstruct_library.ML\<close>
ML "open TPTP_Reconstruct_Library"
ML_file \<open>TPTP_Parser/tptp_reconstruct.ML\<close>

(*FIXME fudge*)
declare [[
  blast_depth_limit = 10,
  unify_search_bound = 5
]]


section "Proof reconstruction"
text \<open>There are two parts to proof reconstruction:
\begin{itemize}
  \item interpreting the inferences
  \item building the skeleton, which indicates how to compose
    individual inferences into subproofs, and then compose the
    subproofs to give the proof).
\end{itemize}

One step detects unsound inferences, and the other step detects
unsound composition of inferences.  The two parts can be weakly
coupled. They rely on a "proof index" which maps nodes to the
inference information. This information consists of the (usually
prover-specific) name of the inference step, and the Isabelle
formalisation of the inference as a term. The inference interpretation
then maps these terms into meta-theorems, and the skeleton is used to
compose the inference-level steps into a proof.

Leo2 operates on conjunctions of clauses. Each Leo2 inference has the
following form, where Cx are clauses:

           C1 && ... && Cn
          -----------------
          C'1 && ... && C'n

Clauses consist of disjunctions of literals (shown as Px below), and might
have a prefix of !-bound variables, as shown below.

  ! X... { P1 || ... || Pn}

Literals are usually assigned a polarity, but this isn't always the
case; you can come across inferences looking like this (where A is an
object-level formula):

             F
          --------
          F = true

The symbol "||" represents literal-level disjunction and "&&" is
clause-level conjunction. Rules will typically lift formula-level
conjunctions; for instance the following rule lifts object-level
disjunction:

          {    (A | B) = true    || ... } && ...
          --------------------------------------
          { A = true || B = true || ... } && ...


Using this setup, efficiency might be gained by only interpreting
inferences once, merging identical inference steps, and merging
identical subproofs into single inferences thus avoiding some effort.
We can also attempt to minimising proof search when interpreting
inferences.

It is hoped that this setup can target other provers by modifying the
clause representation to fit them, and adapting the inference
interpretation to handle the rules used by the prover. It should also
facilitate composing together proofs found by different provers.
\<close>


subsection "Instantiation"

lemma polar_allE [rule_format]:
  "\<lbrakk>(\<forall>x. P x) = True; (P x) = True \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>(\<exists>x. P x) = False; (P x) = False \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by auto

lemma polar_exE [rule_format]:
  "\<lbrakk>(\<exists>x. P x) = True; \<And>x. (P x) = True \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>(\<forall>x. P x) = False; \<And>x. (P x) = False \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by auto

ML \<open>
(*This carries out an allE-like rule but on (polarised) literals.
 Instead of yielding a free variable (which is a hell for the
 matcher) it seeks to use one of the subgoals' parameters.
 This ought to be sufficient for emulating extcnf_combined,
 but note that the complexity of the problem can be enormous.*)
fun inst_parametermatch_tac ctxt thms i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst

    val parameters =
      if null gls then []
      else
        rpair (i - 1) gls
        |> uncurry nth
        |> strip_top_all_vars []
        |> fst
        |> map fst (*just get the parameter names*)
  in
    if null parameters then no_tac st
    else
      let
        fun instantiate param =
          (map (Rule_Insts.eres_inst_tac ctxt [((("x", 0), Position.none), param)] []) thms
                   |> FIRST')
        val attempts = map instantiate parameters
      in
        (fold (curry (op APPEND')) attempts (K no_tac)) i st
      end
  end

(*Attempts to use the polar_allE theorems on a specific subgoal.*)
fun forall_pos_tac ctxt = inst_parametermatch_tac ctxt @{thms polar_allE}
\<close>

ML \<open>
(*This is similar to inst_parametermatch_tac, but prefers to
  match variables having identical names. Logically, this is
  a hack. But it reduces the complexity of the problem.*)
fun nominal_inst_parametermatch_tac ctxt thm i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst

    val parameters =
      if null gls then []
      else
        rpair (i - 1) gls
        |> uncurry nth
        |> strip_top_all_vars []
        |> fst
        |> map fst (*just get the parameter names*)
  in
    if null parameters then no_tac st
    else
      let
        fun instantiates param =
          Rule_Insts.eres_inst_tac ctxt [((("x", 0), Position.none), param)] [] thm

        val quantified_var = head_quantified_variable ctxt i st
      in
        if is_none quantified_var then no_tac st
        else
          if member (op =) parameters (the quantified_var |> fst) then
            instantiates (the quantified_var |> fst) i st
          else
            K no_tac i st
      end
  end
\<close>


subsection "Prefix massaging"

ML \<open>
exception NO_GOALS

(*Get quantifier prefix of the hypothesis and conclusion, reorder
  the hypothesis' quantifiers to have the ones appearing in the
  conclusion first.*)
fun canonicalise_qtfr_order ctxt i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst
  in
    if null gls then raise NO_GOALS
    else
      let
        val (params, (hyp_clause, conc_clause)) =
          rpair (i - 1) gls
          |> uncurry nth
          |> strip_top_all_vars []
          |> apsnd Logic.dest_implies

        val (hyp_quants, hyp_body) =
          HOLogic.dest_Trueprop hyp_clause
          |> strip_top_All_vars
          |> apfst rev

        val conc_quants =
          HOLogic.dest_Trueprop conc_clause
          |> strip_top_All_vars
          |> fst

        val new_hyp =
          (* fold absfree new_hyp_prefix hyp_body *)
          (*HOLogic.list_all*)
          fold_rev (fn (v, ty) => fn t => HOLogic.mk_all (v, ty, t))
           (prefix_intersection_list
             hyp_quants conc_quants)
           hyp_body
          |> HOLogic.mk_Trueprop

         val thm = Goal.prove ctxt [] []
           (Logic.mk_implies (hyp_clause, new_hyp))
           (fn _ =>
              (REPEAT_DETERM (HEADGOAL (resolve_tac ctxt @{thms allI})))
              THEN (REPEAT_DETERM
                    (HEADGOAL
                     (nominal_inst_parametermatch_tac ctxt @{thm allE})))
              THEN HEADGOAL (assume_tac ctxt))
      in
        dresolve_tac ctxt [thm] i st
      end
    end
\<close>


subsection "Some general rules and congruences"

(*this isn't an actual rule used in Leo2, but it seems to be
  applied implicitly during some Leo2 inferences.*)
lemma polarise: "P ==> P = True" by auto

ML \<open>
fun is_polarised t =
  (TPTP_Reconstruct.remove_polarity true t; true)
  handle TPTP_Reconstruct.UNPOLARISED _ => false

fun polarise_subgoal_hyps ctxt =
  COND' (SOME #> TERMPRED is_polarised (fn _ => true)) (K no_tac) (dresolve_tac ctxt @{thms polarise})
\<close>

lemma simp_meta [rule_format]:
  "(A --> B) == (~A | B)"
  "(A | B) | C == A | B | C"
  "(A & B) & C == A & B & C"
  "(~ (~ A)) == A"
  (* "(A & B) == (~ (~A | ~B))" *)
  "~ (A & B) == (~A | ~B)"
  "~(A | B) == (~A) & (~B)"
by auto


subsection "Emulation of Leo2's inference rules"

(*this is not included in simp_meta since it would make a mess of the polarities*)
lemma expand_iff [rule_format]:
 "((A :: bool) = B) \<equiv> (~ A | B) & (~ B | A)"
by (rule eq_reflection, auto)

lemma polarity_switch [rule_format]:
  "(\<not> P) = True \<Longrightarrow> P = False"
  "(\<not> P) = False \<Longrightarrow> P = True"
  "P = False \<Longrightarrow> (\<not> P) = True"
  "P = True \<Longrightarrow> (\<not> P) = False"
by auto

lemma solved_all_splits: "False = True \<Longrightarrow> False" by simp
ML \<open>
fun solved_all_splits_tac ctxt =
  TRY (eresolve_tac ctxt @{thms conjE} 1)
  THEN resolve_tac ctxt @{thms solved_all_splits} 1
  THEN assume_tac ctxt 1
\<close>

lemma lots_of_logic_expansions_meta [rule_format]:
  "(((A :: bool) = B) = True) == (((A \<longrightarrow> B) = True) & ((B \<longrightarrow> A) = True))"
  "((A :: bool) = B) = False == (((~A) | B) = False) | (((~B) | A) = False)"

  "((F = G) = True) == (\<forall>x. (F x = G x)) = True"
  "((F = G) = False) == (\<forall>x. (F x = G x)) = False"

  "(A | B) = True == (A = True) | (B = True)"
  "(A & B) = False == (A = False) | (B = False)"
  "(A | B) = False == (A = False) & (B = False)"
  "(A & B) = True == (A = True) & (B = True)"
  "(~ A) = True == A = False"
  "(~ A) = False == A = True"
  "~ (A = True) == A = False"
  "~ (A = False) == A = True"
by (rule eq_reflection, auto)+

(*this is used in extcnf_combined handler*)
lemma eq_neg_bool: "((A :: bool) = B) = False ==> ((~ (A | B)) | ~ ((~ A) | (~ B))) = False"
by auto

lemma eq_pos_bool:
  "((A :: bool) = B) = True ==> ((~ (A | B)) | ~ (~ A | ~ B)) = True"
  "(A = B) = True \<Longrightarrow> A = True \<or> B = False"
  "(A = B) = True \<Longrightarrow> A = False \<or> B = True"
by auto

(*next formula is more versatile than
    "(F = G) = True \<Longrightarrow> \<forall>x. ((F x = G x) = True)"
  since it doesn't assume that clause is singleton. After splitqtfr,
  and after applying allI exhaustively to the conclusion, we can
  use the existing functions to find the "(F x = G x) = True"
  disjunct in the conclusion*)
lemma eq_pos_func: "\<And> x. (F = G) = True \<Longrightarrow> (F x = G x) = True"
by auto

(*make sure the conclusion consists of just "False"*)
lemma flip:
  "((A = True) ==> False) ==> A = False"
  "((A = False) ==> False) ==> A = True"
by auto

(*FIXME try to use Drule.equal_elim_rule1 directly for this*)
lemma equal_elim_rule1: "(A \<equiv> B) \<Longrightarrow> A \<Longrightarrow> B" by auto
lemmas leo2_rules =
 lots_of_logic_expansions_meta[THEN equal_elim_rule1]

(*FIXME is there any overlap with lots_of_logic_expansions_meta or leo2_rules?*)
lemma extuni_bool2 [rule_format]: "(A = B) = False \<Longrightarrow> (A = True) | (B = True)" by auto
lemma extuni_bool1 [rule_format]: "(A = B) = False \<Longrightarrow> (A = False) | (B = False)" by auto
lemma extuni_triv [rule_format]: "(A = A) = False \<Longrightarrow> R" by auto

(*Order (of A, B, C, D) matters*)
lemma dec_commut_eq [rule_format]:
  "((A = B) = (C = D)) = False \<Longrightarrow> (B = C) = False | (A = D) = False"
  "((A = B) = (C = D)) = False \<Longrightarrow> (B = D) = False | (A = C) = False"
by auto
lemma dec_commut_disj [rule_format]:
  "((A \<or> B) = (C \<or> D)) = False \<Longrightarrow> (B = C) = False \<or> (A = D) = False"
by auto

lemma extuni_func [rule_format]: "(F = G) = False \<Longrightarrow> (\<forall>X. (F X = G X)) = False" by auto


subsection "Emulation: tactics"

ML \<open>
(*Instantiate a variable according to the info given in the
  proof annotation. Through this we avoid having to come up
  with instantiations during reconstruction.*)
fun bind_tac ctxt prob_name ordered_binds =
  let
    val thy = Proof_Context.theory_of ctxt
    fun term_to_string t =
        Print_Mode.with_modes [""]
          (fn () => Output.output (Syntax.string_of_term ctxt t)) ()
    val ordered_instances =
      TPTP_Reconstruct.interpret_bindings prob_name thy ordered_binds []
      |> map (snd #> term_to_string)
      |> permute

    (*instantiate a list of variables, order matters*)
    fun instantiate_vars ctxt vars : tactic =
      map (fn var =>
            Rule_Insts.eres_inst_tac ctxt
             [((("x", 0), Position.none), var)] [] @{thm allE} 1)
          vars
      |> EVERY

    fun instantiate_tac vars =
      instantiate_vars ctxt vars
      THEN (HEADGOAL (assume_tac ctxt))
  in
    HEADGOAL (canonicalise_qtfr_order ctxt)
    THEN (REPEAT_DETERM (HEADGOAL (resolve_tac ctxt @{thms allI})))
    THEN REPEAT_DETERM (HEADGOAL (nominal_inst_parametermatch_tac ctxt @{thm allE}))
    (*now only the variable to instantiate should be left*)
    THEN FIRST (map instantiate_tac ordered_instances)
  end
\<close>

ML \<open>
(*Simplification tactics*)
local
  fun rew_goal_tac thms ctxt i =
    rewrite_goal_tac ctxt thms i
    |> CHANGED
in
  val expander_animal =
    rew_goal_tac (@{thms simp_meta} @ @{thms lots_of_logic_expansions_meta})

  val simper_animal =
    rew_goal_tac @{thms simp_meta}
end
\<close>

lemma prop_normalise [rule_format]:
  "(A | B) | C == A | B | C"
  "(A & B) & C == A & B & C"
  "A | B == ~(~A & ~B)"
  "~~ A == A"
by auto
ML \<open>
(*i.e., break_conclusion*)
fun flip_conclusion_tac ctxt =
  let
    val default_tac =
      (TRY o CHANGED o (rewrite_goal_tac ctxt @{thms prop_normalise}))
      THEN' resolve_tac ctxt @{thms notI}
      THEN' (REPEAT_DETERM o eresolve_tac ctxt @{thms conjE})
      THEN' (TRY o (expander_animal ctxt))
  in
    default_tac ORELSE' resolve_tac ctxt @{thms flip}
  end
\<close>


subsection "Skolemisation"

lemma skolemise [rule_format]:
  "\<forall> P. (\<not> (\<forall>x. P x)) \<longrightarrow> \<not> (P (SOME x. ~ P x))"
proof -
  have "\<And> P. (\<not> (\<forall>x. P x)) \<Longrightarrow> \<not> (P (SOME x. ~ P x))"
  proof -
    fix P
    assume ption: "\<not> (\<forall>x. P x)"
    hence a: "\<exists>x. \<not> P x" by force

    have hilbert : "\<And>P. (\<exists>x. P x) \<Longrightarrow> (P (SOME x. P x))"
    proof -
      fix P
      assume "(\<exists>x. P x)"
      thus "(P (SOME x. P x))"
        apply auto
        apply (rule someI)
        apply auto
        done
    qed

    from a show "\<not> P (SOME x. \<not> P x)"
    proof -
      assume "\<exists>x. \<not> P x"
      hence "\<not> P (SOME x. \<not> P x)" by (rule hilbert)
      thus ?thesis .
    qed
  qed
  thus ?thesis by blast
qed

lemma polar_skolemise [rule_format]:
  "\<forall>P. (\<forall>x. P x) = False \<longrightarrow> (P (SOME x. \<not> P x)) = False"
proof -
  have "\<And>P. (\<forall>x. P x) = False \<Longrightarrow> (P (SOME x. \<not> P x)) = False"
  proof -
    fix P
    assume ption: "(\<forall>x. P x) = False"
    hence "\<not> (\<forall>x. P x)" by force
    hence "\<not> All P" by force
    hence "\<not> (P (SOME x. \<not> P x))" by (rule skolemise)
    thus "(P (SOME x. \<not> P x)) = False" by force
  qed
  thus ?thesis by blast
qed

lemma leo2_skolemise [rule_format]:
  "\<forall>P sk. (\<forall>x. P x) = False \<longrightarrow> (sk = (SOME x. \<not> P x)) \<longrightarrow> (P sk) = False"
by (clarify, rule polar_skolemise)

lemma lift_forall [rule_format]:
  "\<And>x. (\<forall>x. A x) = True \<Longrightarrow> (A x) = True"
  "\<And>x. (\<exists>x. A x) = False \<Longrightarrow> (A x) = False"
by auto
lemma lift_exists [rule_format]:
  "\<lbrakk>(All P) = False; sk = (SOME x. \<not> P x)\<rbrakk> \<Longrightarrow> P sk = False"
  "\<lbrakk>(Ex P) = True; sk = (SOME x. P x)\<rbrakk> \<Longrightarrow> P sk = True"
apply (drule polar_skolemise, simp)
apply (simp, drule someI_ex, simp)
done

ML \<open>
(*FIXME LHS should be constant. Currently allow variables for testing. Probably should still allow Vars (but not Frees) since they'll act as intermediate values*)
fun conc_is_skolem_def t =
  case t of
      Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t' $ (Const (\<^const_name>\<open>Hilbert_Choice.Eps\<close>, _) $ _) =>
      let
        val (h, args) =
          strip_comb t'
          |> apfst (strip_abs #> snd #> strip_comb #> fst)
        val get_const_name = dest_Const #> fst
        val h_property =
          is_Free h orelse
          is_Var h orelse
          (is_Const h
           andalso (get_const_name h <> get_const_name \<^term>\<open>HOL.Ex\<close>)
           andalso (get_const_name h <> get_const_name \<^term>\<open>HOL.All\<close>)
           andalso (h <> \<^term>\<open>Hilbert_Choice.Eps\<close>)
           andalso (h <> \<^term>\<open>HOL.conj\<close>)
           andalso (h <> \<^term>\<open>HOL.disj\<close>)
           andalso (h <> \<^term>\<open>HOL.eq\<close>)
           andalso (h <> \<^term>\<open>HOL.implies\<close>)
           andalso (h <> \<^term>\<open>HOL.The\<close>)
           andalso (h <> \<^term>\<open>HOL.Ex1\<close>)
           andalso (h <> \<^term>\<open>HOL.Not\<close>)
           andalso (h <> \<^term>\<open>HOL.iff\<close>)
           andalso (h <> \<^term>\<open>HOL.not_equal\<close>))
        val args_property =
          fold (fn t => fn b =>
           b andalso is_Free t) args true
      in
        h_property andalso args_property
      end
    | _ => false
\<close>

ML \<open>
(*Hack used to detect if a Skolem definition, with an LHS Var, has had the LHS instantiated into an unacceptable term.*)
fun conc_is_bad_skolem_def t =
  case t of
      Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t' $ (Const (\<^const_name>\<open>Hilbert_Choice.Eps\<close>, _) $ _) =>
      let
        val (h, args) = strip_comb t'
        val get_const_name = dest_Const #> fst
        val const_h_test =
          if is_Const h then
            (get_const_name h = get_const_name \<^term>\<open>HOL.Ex\<close>)
             orelse (get_const_name h = get_const_name \<^term>\<open>HOL.All\<close>)
             orelse (h = \<^term>\<open>Hilbert_Choice.Eps\<close>)
             orelse (h = \<^term>\<open>HOL.conj\<close>)
             orelse (h = \<^term>\<open>HOL.disj\<close>)
             orelse (h = \<^term>\<open>HOL.eq\<close>)
             orelse (h = \<^term>\<open>HOL.implies\<close>)
             orelse (h = \<^term>\<open>HOL.The\<close>)
             orelse (h = \<^term>\<open>HOL.Ex1\<close>)
             orelse (h = \<^term>\<open>HOL.Not\<close>)
             orelse (h = \<^term>\<open>HOL.iff\<close>)
             orelse (h = \<^term>\<open>HOL.not_equal\<close>)
          else true
        val h_property =
          not (is_Free h) andalso
          not (is_Var h) andalso
          const_h_test
        val args_property =
          fold (fn t => fn b =>
           b andalso is_Free t) args true
      in
        h_property andalso args_property
      end
    | _ => false
\<close>

ML \<open>
fun get_skolem_conc t =
  let
    val t' =
      strip_top_all_vars [] t
      |> snd
      |> try_dest_Trueprop
  in
    case t' of
        Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t' $ (Const (\<^const_name>\<open>Hilbert_Choice.Eps\<close>, _) $ _) => SOME t'
      | _ => NONE
  end

fun get_skolem_conc_const t =
  lift_option
   (fn t' =>
     head_of t'
     |> strip_abs_body
     |> head_of
     |> dest_Const)
   (get_skolem_conc t)
\<close>

(*
Technique for handling quantifiers:
  Principles:
  * allE should always match with a !!
  * exE should match with a constant,
     or bind a fresh !! -- currently not doing the latter since it never seems to arised in normal Leo2 proofs.
*)

ML \<open>
fun forall_neg_tac candidate_consts ctxt i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst

    val parameters =
      if null gls then ""
      else
        rpair (i - 1) gls
        |> uncurry nth
        |> strip_top_all_vars []
        |> fst
        |> map fst (*just get the parameter names*)
        |> (fn l =>
              if null l then ""
              else
                space_implode " " l
                |> pair " "
                |> (op ^))

  in
    if null gls orelse null candidate_consts then no_tac st
    else
      let
        fun instantiate const_name =
          Rule_Insts.dres_inst_tac ctxt [((("sk", 0), Position.none), const_name ^ parameters)] []
            @{thm leo2_skolemise}
        val attempts = map instantiate candidate_consts
      in
        (fold (curry (op APPEND')) attempts (K no_tac)) i st
      end
  end
\<close>

ML \<open>
exception SKOLEM_DEF of term (*The tactic wasn't pointed at a skolem definition*)
exception NO_SKOLEM_DEF of (*skolem const name*)string * Binding.binding * term (*The tactic could not find a skolem definition in the theory*)
fun absorb_skolem_def ctxt prob_name_opt i = fn st =>
  let
    val thy = Proof_Context.theory_of ctxt

    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst

    val conclusion =
      if null gls then
        (*this should never be thrown*)
        raise NO_GOALS
      else
        rpair (i - 1) gls
        |> uncurry nth
        |> strip_top_all_vars []
        |> snd
        |> Logic.strip_horn
        |> snd

    fun skolem_const_info_of t =
      case t of
          Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t' $ (Const (\<^const_name>\<open>Hilbert_Choice.Eps\<close>, _) $ _)) =>
          head_of t'
          |> strip_abs_body (*since in general might have a skolem term, so we want to rip out the prefixing lambdas to get to the constant (which should be at head position)*)
          |> head_of
          |> dest_Const
        | _ => raise SKOLEM_DEF t

    val const_name =
      skolem_const_info_of conclusion
      |> fst

    val def_name = const_name ^ "_def"

    val bnd_def = (*FIXME consts*)
      const_name
      |> Long_Name.implode o tl o Long_Name.explode (*FIXME hack to drop theory-name prefix*)
      |> Binding.qualified_name
      |> Binding.suffix_name "_def"

    val bnd_name =
      case prob_name_opt of
          NONE => bnd_def
        | SOME prob_name =>
(*            Binding.qualify false
             (TPTP_Problem_Name.mangle_problem_name prob_name)
*)
             bnd_def

    val thm =
      (case try (Thm.axiom thy) def_name of
        SOME thm => thm
      | NONE =>
          if is_none prob_name_opt then
            (*This mode is for testing, so we can be a bit
              looser with theories*)
            (* FIXME bad theory context!? *)
            Thm.add_axiom_global (bnd_name, conclusion) thy
            |> fst |> snd
          else
            raise (NO_SKOLEM_DEF (def_name, bnd_name, conclusion)))
  in
    resolve_tac ctxt [Drule.export_without_context thm] i st
  end
  handle SKOLEM_DEF _ => no_tac st
\<close>

ML \<open>
(*
In current system, there should only be 2 subgoals: the one where
the skolem definition is being built (with a Var in the LHS), and the other subgoal using Var.
*)
(*arity must be greater than 0. if arity=0 then
  there's no need to use this expensive matching.*)
fun find_skolem_term ctxt consts_candidate arity = fn st =>
  let
    val _ = \<^assert> (arity > 0)

    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst

    (*extract the conclusion of each subgoal*)
    val conclusions =
      if null gls then
        raise NO_GOALS
      else
        map (strip_top_all_vars [] #> snd #> Logic.strip_horn #> snd) gls
        (*Remove skolem-definition conclusion, to avoid wasting time analysing it*)
        |> filter (try_dest_Trueprop #> conc_is_skolem_def #> not)
        (*There should only be a single goal*) (*FIXME this might not always be the case, in practice*)
        (* |> tap (fn x => @{assert} (is_some (try the_single x))) *)

    (*look for subterms headed by a skolem constant, and whose
      arguments are all parameter Vars*)
    fun get_skolem_terms args (acc : term list) t =
      case t of
          (c as Const _) $ (v as Free _) =>
            if c = consts_candidate andalso
             arity = length args + 1 then
              (list_comb (c, v :: args)) :: acc
            else acc
        | t1 $ (v as Free _) =>
            get_skolem_terms (v :: args) acc t1 @
             get_skolem_terms [] acc t1
        | t1 $ t2 =>
            get_skolem_terms [] acc t1 @
             get_skolem_terms [] acc t2
        | Abs (_, _, t') => get_skolem_terms [] acc t'
        | _ => acc
  in
    map (strip_top_All_vars #> snd) conclusions
    |> maps (get_skolem_terms [] [])
    |> distinct (op =)
  end
\<close>

ML \<open>
fun instantiate_skols ctxt consts_candidates i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst

    val (params, conclusion) =
      if null gls then
        raise NO_GOALS
      else
        rpair (i - 1) gls
        |> uncurry nth
        |> strip_top_all_vars []
        |> apsnd (Logic.strip_horn #> snd)

    fun skolem_const_info_of t =
      case t of
          Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ (Const (\<^const_name>\<open>Hilbert_Choice.Eps\<close>, _) $ rhs)) =>
          let
            (*the parameters we will concern ourselves with*)
            val params' =
              Term.add_frees lhs []
              |> distinct (op =)
            (*check to make sure that params' <= params*)
            val _ = \<^assert> (forall (member (op =) params) params')
            val skolem_const_ty =
              let
                val (skolem_const_prety, no_params) =
                  Term.strip_comb lhs
                  |> apfst (dest_Var #> snd) (*head of lhs consists of a logical variable. we just want its type.*)
                  |> apsnd length

                val _ = \<^assert> (length params = no_params)

                (*get value type of a function type after n arguments have been supplied*)
                fun get_val_ty n ty =
                  if n = 0 then ty
                  else get_val_ty (n - 1) (dest_funT ty |> snd)
              in
                get_val_ty no_params skolem_const_prety
              end

          in
            (skolem_const_ty, params')
          end
        | _ => raise (SKOLEM_DEF t)

(*
find skolem const candidates which, after applying distinct members of params' we end up with, give us something of type skolem_const_ty.

given a candidate's type, skolem_const_ty, and params', we get some pemutations of params' (i.e. the order in which they can be given to the candidate in order to get skolem_const_ty). If the list of permutations is empty, then we cannot use that candidate.
*)
(*
only returns a single matching -- since terms are linear, and variable arguments are Vars, order shouldn't matter, so we can ignore permutations.
doesn't work with polymorphism (for which we'd need to use type unification) -- this is OK since no terms should be polymorphic, since Leo2 proofs aren't.
*)
    fun use_candidate target_ty params acc cur_ty =
      if null params then
        if cur_ty = target_ty then
          SOME (rev acc)
        else NONE
      else
        let
          val (arg_ty, val_ty) = Term.dest_funT cur_ty
          (*now find a param of type arg_ty*)
          val (candidate_param, params') =
            find_and_remove (snd #> pair arg_ty #> (op =)) params
        in
          use_candidate target_ty params' (candidate_param :: acc) val_ty
        end
        handle TYPE ("dest_funT", _, _) => NONE  (* FIXME fragile *)
             | _ => NONE  (* FIXME avoid catch-all handler *)

    val (skolem_const_ty, params') = skolem_const_info_of conclusion

(*
For each candidate, build a term and pass it to Thm.instantiate, whic in turn is chained with PRIMITIVE to give us this_tactic.

Big picture:
  we run the following:
    drule leo2_skolemise THEN' this_tactic

NOTE: remember to APPEND' instead of ORELSE' the two tactics relating to skolemisation
*)

    val filtered_candidates =
      map (dest_Const
           #> snd
           #> use_candidate skolem_const_ty params' [])
       consts_candidates (* prefiltered_candidates *)
      |> pair consts_candidates (* prefiltered_candidates *)
      |> ListPair.zip
      |> filter (snd #> is_none #> not)
      |> map (apsnd the)

    val skolem_terms =
      let
        fun make_result_t (t, args) =
          (* list_comb (t, map Free args) *)
          if length args > 0 then
            hd (find_skolem_term ctxt t (length args) st)
          else t
      in
        map make_result_t filtered_candidates
      end

    (*prefix a skolem term with bindings for the parameters*)
    (* val contextualise = fold absdummy (map snd params) *)
    val contextualise = fold absfree params

    val skolem_cts = map (contextualise #> Thm.cterm_of ctxt) skolem_terms


(*now the instantiation code*)

    (*there should only be one Var -- that is from the previous application of drule leo2_skolemise. We look for it at the head position in some equation at a conclusion of a subgoal.*)
    val var_opt =
      let
        val pre_var =
          gls
          |> map
              (strip_top_all_vars [] #> snd #>
               Logic.strip_horn #> snd #>
               get_skolem_conc)
          |> switch (fold (fn x => fn l => if is_some x then the x :: l else l)) []
          |> maps (switch Term.add_vars [])

        fun make_var pre_var =
          the_single pre_var
          |> Var
          |> Thm.cterm_of ctxt
          |> SOME
      in
        if null pre_var then NONE
        else make_var pre_var
     end

    fun instantiate_tac from to =
      PRIMITIVE (Thm.instantiate (TVars.empty, Vars.make [(from, to)]))

    val tactic =
      if is_none var_opt then no_tac
      else
        fold (curry (op APPEND))
          (map (instantiate_tac (dest_Var (Thm.term_of (the var_opt)))) skolem_cts) no_tac
  in
    tactic st
  end
\<close>

ML \<open>
fun new_skolem_tac ctxt consts_candidates =
  let
    fun tac thm =
      dresolve_tac ctxt [thm]
      THEN' instantiate_skols ctxt consts_candidates
  in
    if null consts_candidates then K no_tac
    else FIRST' (map tac @{thms lift_exists})
  end
\<close>

(*
need a tactic to expand "? x . P" to "~ ! x. ~ P"
*)
ML \<open>
fun ex_expander_tac ctxt i =
   let
     val simpset =
       empty_simpset ctxt (*NOTE for some reason, Bind exception gets raised if ctxt's simpset isn't emptied*)
       |> Simplifier.add_simp @{lemma "Ex P == (\<not> (\<forall>x. \<not> P x))" by auto}
   in
     CHANGED (asm_full_simp_tac simpset i)
   end
\<close>


subsubsection "extuni_dec"

ML \<open>
(*n-ary decomposition. Code is based on the n-ary arg_cong generator*)
fun extuni_dec_n ctxt arity =
  let
    val _ = \<^assert> (arity > 0)
    val is =
      1 upto arity
      |> map Int.toString
    val arg_tys = map (fn i => TFree ("arg" ^ i ^ "_ty", \<^sort>\<open>type\<close>)) is
    val res_ty = TFree ("res" ^ "_ty", \<^sort>\<open>type\<close>)
    val f_ty = arg_tys ---> res_ty
    val f = Free ("f", f_ty)
    val xs = map (fn i =>
      Free ("x" ^ i, TFree ("arg" ^ i ^ "_ty", \<^sort>\<open>type\<close>))) is
    (*FIXME DRY principle*)
    val ys = map (fn i =>
      Free ("y" ^ i, TFree ("arg" ^ i ^ "_ty", \<^sort>\<open>type\<close>))) is

    val hyp_lhs = list_comb (f, xs)
    val hyp_rhs = list_comb (f, ys)
    val hyp_eq =
      HOLogic.eq_const res_ty $ hyp_lhs $ hyp_rhs
    val hyp =
      HOLogic.eq_const HOLogic.boolT $ hyp_eq $ \<^term>\<open>False\<close>
      |> HOLogic.mk_Trueprop
    fun conc_eq i =
      let
        val ty = TFree ("arg" ^ i ^ "_ty", \<^sort>\<open>type\<close>)
        val x = Free ("x" ^ i, ty)
        val y = Free ("y" ^ i, ty)
        val eq = HOLogic.eq_const ty $ x $ y
      in
        HOLogic.eq_const HOLogic.boolT $ eq $ \<^term>\<open>False\<close>
      end

    val conc_disjs = map conc_eq is

    val conc =
      if length conc_disjs = 1 then
        the_single conc_disjs
      else
        fold
         (fn t => fn t_conc => HOLogic.mk_disj (t_conc, t))
         (tl conc_disjs) (hd conc_disjs)

    val t =
      Logic.mk_implies (hyp, HOLogic.mk_Trueprop conc)
  in
    Goal.prove ctxt [] [] t (fn _ => auto_tac ctxt)
    |> Drule.export_without_context
  end
\<close>

ML \<open>
(*Determine the arity of a function which the "dec"
  unification rule is about to be applied.
  NOTE:
    * Assumes that there is a single hypothesis
*)
fun find_dec_arity i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst
  in
    if null gls then raise NO_GOALS
    else
      let
        val (params, (literal, conc_clause)) =
          rpair (i - 1) gls
          |> uncurry nth
          |> strip_top_all_vars []
          |> apsnd Logic.strip_horn
          |> apsnd (apfst the_single)

        val get_ty =
          HOLogic.dest_Trueprop
          #> strip_top_All_vars
          #> snd
          #> HOLogic.dest_eq (*polarity's "="*)
          #> fst
          #> HOLogic.dest_eq (*the unification constraint's "="*)
          #> fst
          #> head_of
          #> dest_Const
          #> snd

       fun arity_of ty =
         let
           val (_, res_ty) = dest_funT ty

         in
           1 + arity_of res_ty
         end
         handle (TYPE ("dest_funT", _, _)) => 0

      in
        arity_of (get_ty literal)
      end
  end

(*given an inference, it returns the parameters (i.e., we've already matched the leading & shared quantification in the hypothesis & conclusion clauses), and the "raw" inference*)
fun breakdown_inference i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst
  in
    if null gls then raise NO_GOALS
    else
      rpair (i - 1) gls
      |> uncurry nth
      |> strip_top_all_vars []
  end

(*build a custom elimination rule for extuni_dec, and instantiate it to match a specific subgoal*)
fun extuni_dec_elim_rule ctxt arity i = fn st =>
  let
    val rule = extuni_dec_n ctxt arity

    val rule_hyp =
      Thm.prop_of rule
      |> Logic.dest_implies
      |> fst (*assuming that rule has single hypothesis*)

    (*having run break_hypothesis earlier, we know that the hypothesis
      now consists of a single literal. We can (and should)
      disregard the conclusion, since it hasn't been "broken",
      and it might include some unwanted literals -- the latter
      could cause "diff" to fail (since they won't agree with the
      rule we have generated.*)

    val inference_hyp =
      snd (breakdown_inference i st)
      |> Logic.dest_implies
      |> fst (*assuming that inference has single hypothesis,
               as explained above.*)
  in
    TPTP_Reconstruct_Library.diff_and_instantiate ctxt rule rule_hyp inference_hyp
  end

fun extuni_dec_tac ctxt i = fn st =>
  let
    val arity = find_dec_arity i st

    fun elim_tac i st =
      let
        val rule =
          extuni_dec_elim_rule ctxt arity i st
          (*in case we itroduced free variables during
            instantiation, we generalise the rule to make
            those free variables into logical variables.*)
          |> Thm.forall_intr_frees
          |> Drule.export_without_context
      in dresolve_tac ctxt [rule] i st end
      handle NO_GOALS => no_tac st

    fun closure tac =
     (*batter fails if there's no toplevel disjunction in the
       hypothesis, so we also try atac*)
      SOLVE o (tac THEN' (batter_tac ctxt ORELSE' assume_tac ctxt))
    val search_tac =
      ASAP
        (resolve_tac ctxt @{thms disjI1} APPEND' resolve_tac ctxt @{thms disjI2})
        (FIRST' (map closure
                  [dresolve_tac ctxt @{thms dec_commut_eq},
                   dresolve_tac ctxt @{thms dec_commut_disj},
                   elim_tac]))
  in
    (CHANGED o search_tac) i st
  end
\<close>


subsubsection "standard_cnf"
(*Given a standard_cnf inference, normalise it
     e.g. ((A & B) & C \<longrightarrow> D & E \<longrightarrow> F \<longrightarrow> G) = False
     is changed to
          (A & B & C & D & E & F \<longrightarrow> G) = False
 then custom-build a metatheorem which validates this:
          (A & B & C & D & E & F \<longrightarrow> G) = False
       -------------------------------------------
          (A = True) & (B = True) & (C = True) &
          (D = True) & (E = True) & (F = True) & (G = False)
 and apply this metatheorem.

There aren't any "positive" standard_cnfs in Leo2's calculus:
  e.g.,  "(A \<longrightarrow> B) = True \<Longrightarrow> A = False | (A = True & B = True)"
since "standard_cnf" seems to be applied at the preprocessing
stage, together with splitting.
*)

ML \<open>
(*Conjunctive counterparts to Term.disjuncts_aux and Term.disjuncts*)
fun conjuncts_aux (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ t $ t') conjs =
     conjuncts_aux t (conjuncts_aux t' conjs)
  | conjuncts_aux t conjs = t :: conjs

fun conjuncts t = conjuncts_aux t []

(*HOL equivalent of Logic.strip_horn*)
local
  fun imp_strip_horn' acc (Const (\<^const_name>\<open>HOL.implies\<close>, _) $ A $ B) =
        imp_strip_horn' (A :: acc) B
    | imp_strip_horn' acc t = (acc, t)
in
  fun imp_strip_horn t =
    imp_strip_horn' [] t
    |> apfst rev
end
\<close>

ML \<open>
(*Returns whether the antecedents are separated by conjunctions
  or implications; the number of antecedents; and the polarity
  of the original clause -- I think this will always be "false".*)
fun standard_cnf_type ctxt i : thm -> (TPTP_Reconstruct.formula_kind * int * bool) option = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst

    val hypos =
      if null gls then raise NO_GOALS
      else
        rpair (i - 1) gls
        |> uncurry nth
        |> TPTP_Reconstruct.strip_top_all_vars []
        |> snd
        |> Logic.strip_horn
        |> fst

    (*hypothesis clause should be singleton*)
    val _ = \<^assert> (length hypos = 1)

    val (t, pol) = the_single hypos
      |> try_dest_Trueprop
      |> TPTP_Reconstruct.strip_top_All_vars
      |> snd
      |> TPTP_Reconstruct.remove_polarity true

    (*literal is negative*)
    val _ = \<^assert> (not pol)

    val (antes, conc) = imp_strip_horn t

    val (ante_type, antes') =
      if length antes = 1 then
        let
          val conjunctive_antes =
            the_single antes
            |> conjuncts
        in
          if length conjunctive_antes > 1 then
            (TPTP_Reconstruct.Conjunctive NONE,
             conjunctive_antes)
          else
            (TPTP_Reconstruct.Implicational NONE,
             antes)
        end
      else
        (TPTP_Reconstruct.Implicational NONE,
         antes)
  in
    if null antes then NONE
    else SOME (ante_type, length antes', pol)
  end
\<close>

ML \<open>
(*Given a certain standard_cnf type, build a metatheorem that would
  validate it*)
fun mk_standard_cnf ctxt kind arity =
  let
    val _ = \<^assert> (arity > 0)
    val vars =
      1 upto (arity + 1)
      |> map (fn i => Free ("x" ^ Int.toString i, HOLogic.boolT))

    val consequent = hd vars
    val antecedents = tl vars

    val conc =
      fold
       (curry HOLogic.mk_conj)
       (map (fn var => HOLogic.mk_eq (var, \<^term>\<open>True\<close>)) antecedents)
       (HOLogic.mk_eq (consequent, \<^term>\<open>False\<close>))

    val pre_hyp =
      case kind of
          TPTP_Reconstruct.Conjunctive NONE =>
            curry HOLogic.mk_imp
             (if length antecedents = 1 then the_single antecedents
              else
                fold (curry HOLogic.mk_conj) (tl antecedents) (hd antecedents))
             (hd vars)
        | TPTP_Reconstruct.Implicational NONE =>
            fold (curry HOLogic.mk_imp) antecedents consequent

    val hyp = HOLogic.mk_eq (pre_hyp, \<^term>\<open>False\<close>)

    val t =
      Logic.mk_implies (HOLogic.mk_Trueprop  hyp, HOLogic.mk_Trueprop conc)
  in
    Goal.prove ctxt [] [] t (fn _ => HEADGOAL (blast_tac ctxt))
    |> Drule.export_without_context
  end
\<close>

ML \<open>
(*Applies a d-tactic, then breaks it up conjunctively.
  This can be used to transform subgoals as follows:
     (A \<longrightarrow> B) = False  \<Longrightarrow> R
              |
              v
  \<lbrakk>A = True; B = False\<rbrakk> \<Longrightarrow> R
*)
fun weak_conj_tac ctxt drule =
  dresolve_tac ctxt [drule] THEN'
  (REPEAT_DETERM o eresolve_tac ctxt @{thms conjE})
\<close>

ML \<open>
fun uncurry_lit_neg_tac ctxt =
  REPEAT_DETERM o
    dresolve_tac ctxt [@{lemma "(A \<longrightarrow> B \<longrightarrow> C) = False \<Longrightarrow> (A & B \<longrightarrow> C) = False" by auto}]
\<close>

ML \<open>
fun standard_cnf_tac ctxt i = fn st =>
  let
    fun core_tactic i = fn st =>
      case standard_cnf_type ctxt i st of
          NONE => no_tac st
        | SOME (kind, arity, _) =>
            let
              val rule = mk_standard_cnf ctxt kind arity;
            in
              (weak_conj_tac ctxt rule THEN' assume_tac ctxt) i st
            end
  in
    (uncurry_lit_neg_tac ctxt
     THEN' TPTP_Reconstruct_Library.reassociate_conjs_tac ctxt
     THEN' core_tactic) i st
  end
\<close>


subsubsection "Emulator prep"

ML \<open>
datatype cleanup_feature =
    RemoveHypothesesFromSkolemDefs
  | RemoveDuplicates

datatype loop_feature =
    Close_Branch
  | ConjI
  | King_Cong
  | Break_Hypotheses
  | Donkey_Cong (*simper_animal + ex_expander_tac*)
  | RemoveRedundantQuantifications
  | Assumption

  (*Closely based on Leo2 calculus*)
  | Existential_Free
  | Existential_Var
  | Universal
  | Not_pos
  | Not_neg
  | Or_pos
  | Or_neg
  | Equal_pos
  | Equal_neg
  | Extuni_Bool2
  | Extuni_Bool1
  | Extuni_Dec
  | Extuni_Bind
  | Extuni_Triv
  | Extuni_FlexRigid
  | Extuni_Func
  | Polarity_switch
  | Forall_special_pos

datatype feature =
    ConstsDiff
  | StripQuantifiers
  | Flip_Conclusion
  | Loop of loop_feature list
  | LoopOnce of loop_feature list
  | InnerLoopOnce of loop_feature list
  | CleanUp of cleanup_feature list
  | AbsorbSkolemDefs
\<close>

ML \<open>
fun can_feature x l =
  let
    fun sublist_of_clean_up el =
      case el of
          CleanUp l'' => SOME l''
        | _ => NONE
    fun sublist_of_loop el =
      case el of
          Loop l'' => SOME l''
        | _ => NONE
    fun sublist_of_loop_once el =
      case el of
          LoopOnce l'' => SOME l''
        | _ => NONE
    fun sublist_of_inner_loop_once el =
      case el of
          InnerLoopOnce l'' => SOME l''
        | _ => NONE

    fun check_sublist sought_sublist opt_list =
      if forall is_none opt_list then false
      else
        fold_options opt_list
        |> flat
        |> pair sought_sublist
        |> subset (op =)
  in
    case x of
        CleanUp l' =>
          map sublist_of_clean_up l
          |> check_sublist l'
      | Loop l' =>
          map sublist_of_loop l
          |> check_sublist l'
      | LoopOnce l' =>
          map sublist_of_loop_once l
          |> check_sublist l'
      | InnerLoopOnce l' =>
          map sublist_of_inner_loop_once l
          |> check_sublist l'
      | _ => exists (curry (op =) x) l
  end;

fun loop_can_feature loop_feats l =
  can_feature (Loop loop_feats) l orelse
  can_feature (LoopOnce loop_feats) l orelse
  can_feature (InnerLoopOnce loop_feats) l;

\<^assert> (can_feature ConstsDiff [StripQuantifiers, ConstsDiff]);

\<^assert>
  (can_feature (CleanUp [RemoveHypothesesFromSkolemDefs])
    [CleanUp [RemoveHypothesesFromSkolemDefs, RemoveDuplicates]]);

\<^assert>
  (can_feature (Loop []) [Loop [Existential_Var]]);

\<^assert>
  (not (can_feature (Loop []) [InnerLoopOnce [Existential_Var]]));
\<close>

ML \<open>
exception NO_LOOP_FEATS
fun get_loop_feats (feats : feature list) =
  let
    val loop_find =
      fold (fn x => fn loop_feats_acc =>
        if is_some loop_feats_acc then loop_feats_acc
        else
          case x of
              Loop loop_feats => SOME loop_feats
            | LoopOnce loop_feats => SOME loop_feats
            | InnerLoopOnce loop_feats => SOME loop_feats
            | _ => NONE)
       feats
       NONE
  in
    if is_some loop_find then the loop_find
    else raise NO_LOOP_FEATS
  end;

\<^assert>
  (get_loop_feats [Loop [King_Cong, Break_Hypotheses, Existential_Free, Existential_Var, Universal]] =
   [King_Cong, Break_Hypotheses, Existential_Free, Existential_Var, Universal])
\<close>

(*use as elim rule to remove premises*)
lemma insa_prems: "\<lbrakk>Q; P\<rbrakk> \<Longrightarrow> P" by auto
ML \<open>
fun cleanup_skolem_defs ctxt feats =
  let
    (*remove hypotheses from skolem defs,
     after testing that they look like skolem defs*)
    val dehypothesise_skolem_defs =
      COND' (SOME #> TERMPRED (fn _ => true) conc_is_skolem_def)
        (REPEAT_DETERM o eresolve_tac ctxt @{thms insa_prems})
        (K no_tac)
  in
    if can_feature (CleanUp [RemoveHypothesesFromSkolemDefs]) feats then
      ALLGOALS (TRY o dehypothesise_skolem_defs)
    else all_tac
  end
\<close>

ML \<open>
fun remove_duplicates_tac feats =
  (if can_feature (CleanUp [RemoveDuplicates]) feats then
     distinct_subgoals_tac
   else all_tac)
\<close>

ML \<open>
(*given a goal state, indicates the skolem constants committed-to in it (i.e. appearing in LHS of a skolem definition)*)
fun which_skolem_concs_used ctxt = fn st =>
  let
    val feats = [CleanUp [RemoveHypothesesFromSkolemDefs, RemoveDuplicates]]
    val scrubup_tac =
      cleanup_skolem_defs ctxt feats
      THEN remove_duplicates_tac feats
  in
    scrubup_tac st
    |> break_seq
    |> tap (fn (_, rest) => \<^assert> (null (Seq.list_of rest)))
    |> fst
    |> TERMFUN (snd (*discard hypotheses*)
                 #> get_skolem_conc_const) NONE
    |> switch (fold (fn x => fn l => if is_some x then the x :: l else l)) []
    |> map Const
  end
\<close>

ML \<open>
fun exists_tac ctxt feats consts_diff =
  let
    val ex_var =
      if loop_can_feature [Existential_Var] feats andalso consts_diff <> [] then
        new_skolem_tac ctxt consts_diff
        (*We're making sure that each skolem constant is used once in instantiations.*)
      else K no_tac

    val ex_free =
      if loop_can_feature [Existential_Free] feats andalso consts_diff = [] then
        eresolve_tac ctxt @{thms polar_exE}
      else K no_tac
  in
    ex_var APPEND' ex_free
  end

fun forall_tac ctxt feats =
  if loop_can_feature [Universal] feats then
    forall_pos_tac ctxt
  else K no_tac
\<close>


subsubsection "Finite types"
(*lift quantification from a singleton literal to a singleton clause*)
lemma forall_pos_lift:
"\<lbrakk>(\<forall>X. P X) = True; \<forall>X. (P X = True) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" by auto

(*predicate over the type of the leading quantified variable*)

ML \<open>
fun extcnf_forall_special_pos_tac ctxt =
  let
    val bool =
      ["True", "False"]

    val bool_to_bool =
      ["% _ . True", "% _ . False", "% x . x", "Not"]

    val tacs =
      map (fn t_s =>  (* FIXME proper context!? *)
       Rule_Insts.eres_inst_tac \<^context> [((("x", 0), Position.none), t_s)] [] @{thm allE}
       THEN' assume_tac ctxt)
  in
    (TRY o eresolve_tac ctxt @{thms forall_pos_lift})
    THEN' (assume_tac ctxt
           ORELSE' FIRST'
            (*FIXME could check the type of the leading quantified variable, instead of trying everything*)
            (tacs (bool @ bool_to_bool)))
  end
\<close>


subsubsection "Emulator"

lemma efq: "[|A = True; A = False|] ==> R" by auto
ML \<open>
fun efq_tac ctxt =
  (eresolve_tac ctxt @{thms efq} THEN' assume_tac ctxt)
  ORELSE' assume_tac ctxt
\<close>

ML \<open>
(*This is applied to all subgoals, repeatedly*)
fun extcnf_combined_main ctxt feats consts_diff =
  let
    (*This is applied to subgoals which don't have a conclusion
      consisting of a Skolem definition*)
    fun extcnf_combined_tac' ctxt i = fn st =>
      let
        val skolem_consts_used_so_far = which_skolem_concs_used ctxt st
        val consts_diff' = subtract (op =) skolem_consts_used_so_far consts_diff

        fun feat_to_tac feat =
          case feat of
              Close_Branch => trace_tac' ctxt "mark: closer" (efq_tac ctxt)
            | ConjI => trace_tac' ctxt "mark: conjI" (resolve_tac ctxt @{thms conjI})
            | King_Cong => trace_tac' ctxt "mark: expander_animal" (expander_animal ctxt)
            | Break_Hypotheses => trace_tac' ctxt "mark: break_hypotheses" (break_hypotheses_tac ctxt)
            | RemoveRedundantQuantifications => K all_tac
(*
FIXME Building this into the loop instead.. maybe not the ideal choice
            | RemoveRedundantQuantifications =>
                trace_tac' ctxt "mark: strip_unused_variable_hyp"
                 (REPEAT_DETERM o remove_redundant_quantification_in_lit)
*)

            | Assumption => assume_tac ctxt
(*FIXME both Existential_Free and Existential_Var run same code*)
            | Existential_Free => trace_tac' ctxt "mark: forall_neg" (exists_tac ctxt feats consts_diff')
            | Existential_Var => trace_tac' ctxt "mark: forall_neg" (exists_tac ctxt feats consts_diff')
            | Universal => trace_tac' ctxt "mark: forall_pos" (forall_tac ctxt feats)
            | Not_pos => trace_tac' ctxt "mark: not_pos" (dresolve_tac ctxt @{thms leo2_rules(9)})
            | Not_neg => trace_tac' ctxt "mark: not_neg" (dresolve_tac ctxt @{thms leo2_rules(10)})
            | Or_pos => trace_tac' ctxt "mark: or_pos" (dresolve_tac ctxt @{thms leo2_rules(5)}) (*could add (6) for negated conjunction*)
            | Or_neg => trace_tac' ctxt "mark: or_neg" (dresolve_tac ctxt @{thms leo2_rules(7)})
            | Equal_pos => trace_tac' ctxt "mark: equal_pos" (dresolve_tac ctxt (@{thms eq_pos_bool} @ [@{thm leo2_rules(3)}, @{thm eq_pos_func}]))
            | Equal_neg => trace_tac' ctxt "mark: equal_neg" (dresolve_tac ctxt [@{thm eq_neg_bool}, @{thm leo2_rules(4)}])
            | Donkey_Cong => trace_tac' ctxt "mark: donkey_cong" (simper_animal ctxt THEN' ex_expander_tac ctxt)

            | Extuni_Bool2 => trace_tac' ctxt "mark: extuni_bool2" (dresolve_tac ctxt @{thms extuni_bool2})
            | Extuni_Bool1 => trace_tac' ctxt "mark: extuni_bool1" (dresolve_tac ctxt @{thms extuni_bool1})
            | Extuni_Bind => trace_tac' ctxt "mark: extuni_triv" (eresolve_tac ctxt @{thms extuni_triv})
            | Extuni_Triv => trace_tac' ctxt "mark: extuni_triv" (eresolve_tac ctxt @{thms extuni_triv})
            | Extuni_Dec => trace_tac' ctxt "mark: extuni_dec_tac" (extuni_dec_tac ctxt)
            | Extuni_FlexRigid => trace_tac' ctxt "mark: extuni_flex_rigid" (assume_tac ctxt ORELSE' asm_full_simp_tac ctxt)
            | Extuni_Func => trace_tac' ctxt "mark: extuni_func" (dresolve_tac ctxt @{thms extuni_func})
            | Polarity_switch => trace_tac' ctxt "mark: polarity_switch" (eresolve_tac ctxt @{thms polarity_switch})
            | Forall_special_pos => trace_tac' ctxt "mark: dorall_special_pos" (extcnf_forall_special_pos_tac ctxt)

        val core_tac =
          get_loop_feats feats
          |> map feat_to_tac
          |> FIRST'
      in
        core_tac i st
      end

    (*This is applied to all subgoals, repeatedly*)
    fun extcnf_combined_tac ctxt i =
      COND (TERMPRED (fn _ => true) conc_is_skolem_def (SOME i))
        no_tac
        (extcnf_combined_tac' ctxt i)

    val core_tac = CHANGED (ALLGOALS (IF_UNSOLVED o TRY o extcnf_combined_tac ctxt))

    val full_tac = REPEAT core_tac

  in
    CHANGED
      (if can_feature (InnerLoopOnce []) feats then
         core_tac
       else full_tac)
  end

val interpreted_consts =
  [\<^const_name>\<open>HOL.All\<close>, \<^const_name>\<open>HOL.Ex\<close>,
   \<^const_name>\<open>Hilbert_Choice.Eps\<close>,
   \<^const_name>\<open>HOL.conj\<close>,
   \<^const_name>\<open>HOL.disj\<close>,
   \<^const_name>\<open>HOL.eq\<close>,
   \<^const_name>\<open>HOL.implies\<close>,
   \<^const_name>\<open>HOL.The\<close>,
   \<^const_name>\<open>HOL.Ex1\<close>,
   \<^const_name>\<open>HOL.Not\<close>,
   (* @{const_name HOL.iff}, *) (*FIXME do these exist?*)
   (* @{const_name HOL.not_equal}, *)
   \<^const_name>\<open>HOL.False\<close>,
   \<^const_name>\<open>HOL.True\<close>,
   \<^const_name>\<open>Pure.imp\<close>]

fun strip_qtfrs_tac ctxt =
  REPEAT_DETERM (HEADGOAL (resolve_tac ctxt @{thms allI}))
  THEN REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt @{thms exE}))
  THEN HEADGOAL (canonicalise_qtfr_order ctxt)
  THEN
    ((REPEAT (HEADGOAL (nominal_inst_parametermatch_tac ctxt @{thm allE})))
     APPEND (REPEAT (HEADGOAL (inst_parametermatch_tac ctxt [@{thm allE}]))))
  (*FIXME need to handle "@{thm exI}"?*)

(*difference in constants between the hypothesis clause and the conclusion clause*)
fun clause_consts_diff thm =
  let
    val t =
      Thm.prop_of thm
      |> Logic.dest_implies
      |> fst

      (*This bit should not be needed, since Leo2 inferences don't have parameters*)
      |> TPTP_Reconstruct.strip_top_all_vars []
      |> snd

    val do_diff =
      Logic.dest_implies
      #> uncurry TPTP_Reconstruct.new_consts_between
      #> filter
           (fn Const (n, _) =>
             not (member (op =) interpreted_consts n))
  in
    if head_of t = Logic.implies then do_diff t
    else []
  end
\<close>

ML \<open>
(*remove quantification in hypothesis clause (! X. t), if
  X not free in t*)
fun remove_redundant_quantification ctxt i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst
  in
    if null gls then raise NO_GOALS
    else
      let
        val (params, (hyp_clauses, conc_clause)) =
          rpair (i - 1) gls
          |> uncurry nth
          |> TPTP_Reconstruct.strip_top_all_vars []
          |> apsnd Logic.strip_horn
      in
        (*this is to fail gracefully in case this tactic is applied to a goal which doesn't have a single hypothesis*)
        if length hyp_clauses > 1 then no_tac st
        else
          let
            val hyp_clause = the_single hyp_clauses
            val sep_prefix =
              HOLogic.dest_Trueprop
              #> TPTP_Reconstruct.strip_top_All_vars
              #> apfst rev
            val (hyp_prefix, hyp_body) = sep_prefix hyp_clause
            val (conc_prefix, conc_body) = sep_prefix conc_clause
          in
            if null hyp_prefix orelse
              member (op =) conc_prefix (hd hyp_prefix) orelse
              member (op =)  (Term.add_frees hyp_body []) (hd hyp_prefix) then
              no_tac st
            else
              Rule_Insts.eres_inst_tac ctxt [((("x", 0), Position.none), "(@X. False)")] []
                @{thm allE} i st
          end
     end
  end
\<close>

ML \<open>
fun remove_redundant_quantification_ignore_skolems ctxt i =
  COND (TERMPRED (fn _ => true) conc_is_skolem_def (SOME i))
    no_tac
    (remove_redundant_quantification ctxt i)
\<close>

lemma drop_redundant_literal_qtfr:
  "(\<forall>X. P) = True \<Longrightarrow> P = True"
  "(\<exists>X. P) = True \<Longrightarrow> P = True"
  "(\<forall>X. P) = False \<Longrightarrow> P = False"
  "(\<exists>X. P) = False \<Longrightarrow> P = False"
by auto

ML \<open>
(*remove quantification in the literal "(! X. t) = True/False"
  in the singleton hypothesis clause, if X not free in t*)
fun remove_redundant_quantification_in_lit ctxt i = fn st =>
  let
    val gls =
      Thm.prop_of st
      |> Logic.strip_horn
      |> fst
  in
    if null gls then raise NO_GOALS
    else
      let
        val (params, (hyp_clauses, conc_clause)) =
          rpair (i - 1) gls
          |> uncurry nth
          |> TPTP_Reconstruct.strip_top_all_vars []
          |> apsnd Logic.strip_horn
      in
        (*this is to fail gracefully in case this tactic is applied to a goal which doesn't have a single hypothesis*)
        if length hyp_clauses > 1 then no_tac st
        else
          let
            fun literal_content (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ (rhs as \<^term>\<open>True\<close>)) = SOME (lhs, rhs)
              | literal_content (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ (rhs as \<^term>\<open>False\<close>)) = SOME (lhs, rhs)
              | literal_content t = NONE

            val hyp_clause =
              the_single hyp_clauses
              |> HOLogic.dest_Trueprop
              |> literal_content

          in
            if is_none hyp_clause then
              no_tac st
            else
              let
                val (hyp_lit_prefix, hyp_lit_body) =
                  the hyp_clause
                  |> (fn (t, polarity) =>
                       TPTP_Reconstruct.strip_top_All_vars t
                       |> apfst rev)
              in
                if null hyp_lit_prefix orelse
                  member (op =)  (Term.add_frees hyp_lit_body []) (hd hyp_lit_prefix) then
                  no_tac st
                else
                  dresolve_tac ctxt @{thms drop_redundant_literal_qtfr} i st
              end
          end
     end
  end
\<close>

ML \<open>
fun remove_redundant_quantification_in_lit_ignore_skolems ctxt i =
  COND (TERMPRED (fn _ => true) conc_is_skolem_def (SOME i))
    no_tac
    (remove_redundant_quantification_in_lit ctxt i)
\<close>

ML \<open>
fun extcnf_combined_tac ctxt prob_name_opt feats skolem_consts = fn st =>
  let
    val thy = Proof_Context.theory_of ctxt

    (*Initially, st consists of a single goal, showing the
      hypothesis clause implying the conclusion clause.
      There are no parameters.*)
    val consts_diff =
      union (=) skolem_consts
       (if can_feature ConstsDiff feats then
          clause_consts_diff st
        else [])

    val main_tac =
      if can_feature (LoopOnce []) feats orelse can_feature (InnerLoopOnce []) feats then
        extcnf_combined_main ctxt feats consts_diff
      else if can_feature (Loop []) feats then
        BEST_FIRST (TERMPRED (fn _ => true) conc_is_skolem_def NONE, size_of_thm)
(*FIXME maybe need to weaken predicate to include "solved form"?*)
         (extcnf_combined_main ctxt feats consts_diff)
      else all_tac (*to allow us to use the cleaning features*)

    (*Remove hypotheses from Skolem definitions,
      then remove duplicate subgoals,
      then we should be left with skolem definitions:
        absorb them as axioms into the theory.*)
    val cleanup =
      cleanup_skolem_defs ctxt feats
      THEN remove_duplicates_tac feats
      THEN (if can_feature AbsorbSkolemDefs feats then
              ALLGOALS (absorb_skolem_def ctxt prob_name_opt)
            else all_tac)

    val have_loop_feats =
      (get_loop_feats feats; true)
      handle NO_LOOP_FEATS => false

    val tec =
      (if can_feature StripQuantifiers feats then
         (REPEAT (CHANGED (strip_qtfrs_tac ctxt)))
       else all_tac)
      THEN (if can_feature Flip_Conclusion feats then
             HEADGOAL (flip_conclusion_tac ctxt)
           else all_tac)

      (*after stripping the quantifiers any remaining quantifiers
        can be simply eliminated -- they're redundant*)
      (*FIXME instead of just using allE, instantiate to a silly
         term, to remove opportunities for unification.*)
      THEN (REPEAT_DETERM (eresolve_tac ctxt @{thms allE} 1))

      THEN (REPEAT_DETERM (resolve_tac ctxt @{thms allI} 1))

      THEN (if have_loop_feats then
              REPEAT (CHANGED
              ((ALLGOALS (TRY o clause_breaker_tac ctxt)) (*brush away literals which don't change*)
               THEN
                (*FIXME move this to a different level?*)
                (if loop_can_feature [Polarity_switch] feats then
                   all_tac
                 else
                   (TRY (IF_UNSOLVED (HEADGOAL (remove_redundant_quantification_ignore_skolems ctxt))))
                   THEN (TRY (IF_UNSOLVED (HEADGOAL (remove_redundant_quantification_in_lit_ignore_skolems ctxt)))))
               THEN (TRY main_tac)))
            else
              all_tac)
      THEN IF_UNSOLVED cleanup

  in
    DEPTH_SOLVE (CHANGED tec) st
  end
\<close>


subsubsection "unfold_def"

(*this is used when handling unfold_tac, because the skeleton includes the definitions conjoined with the goal. it turns out that, for my tactic, the definitions are harmful. instead of modifying the skeleton (which may be nontrivial) i'm just dropping the information using this lemma. obviously, and from the name, order matters here.*)
lemma drop_first_hypothesis [rule_format]: "\<lbrakk>A; B\<rbrakk> \<Longrightarrow> B" by auto

(*Unfold_def works by reducing the goal to a meta equation,
  then working on it until it can be discharged by atac,
  or reflexive, or else turned back into an object equation
  and broken down further.*)
lemma un_meta_polarise: "(X \<equiv> True) \<Longrightarrow> X" by auto
lemma meta_polarise: "X \<Longrightarrow> X \<equiv> True" by auto

ML \<open>
fun unfold_def_tac ctxt depends_on_defs = fn st =>
  let
    (*This is used when we end up with something like
        (A & B) \<equiv> True \<Longrightarrow> (B & A) \<equiv> True.
      It breaks down this subgoal until it can be trivially
      discharged.
     *)
    val kill_meta_eqs_tac =
      dresolve_tac ctxt @{thms un_meta_polarise}
      THEN' resolve_tac ctxt @{thms meta_polarise}
      THEN' (REPEAT_DETERM o (eresolve_tac ctxt @{thms conjE}))
      THEN' (REPEAT_DETERM o (resolve_tac ctxt @{thms conjI} ORELSE' assume_tac ctxt))

    val continue_reducing_tac =
      resolve_tac ctxt @{thms meta_eq_to_obj_eq} 1
      THEN (REPEAT_DETERM (ex_expander_tac ctxt 1))
      THEN TRY (polarise_subgoal_hyps ctxt 1) (*no need to REPEAT_DETERM here, since there should only be one hypothesis*)
      THEN TRY (dresolve_tac ctxt @{thms eq_reflection} 1)
      THEN (TRY ((CHANGED o rewrite_goal_tac ctxt
              (@{thm expand_iff} :: @{thms simp_meta})) 1))
      THEN HEADGOAL (resolve_tac ctxt @{thms reflexive}
                     ORELSE' assume_tac ctxt
                     ORELSE' kill_meta_eqs_tac)

    val tactic =
      (resolve_tac ctxt @{thms polarise} 1 THEN assume_tac ctxt 1)
      ORELSE
        (REPEAT_DETERM (eresolve_tac ctxt @{thms conjE} 1 THEN
          eresolve_tac ctxt @{thms drop_first_hypothesis} 1)
         THEN PRIMITIVE (Conv.fconv_rule Thm.eta_long_conversion)
         THEN (REPEAT_DETERM (ex_expander_tac ctxt 1))
         THEN (TRY ((CHANGED o rewrite_goal_tac ctxt @{thms simp_meta}) 1))
         THEN PRIMITIVE (Conv.fconv_rule Thm.eta_long_conversion)
         THEN
           (HEADGOAL (assume_tac ctxt)
           ORELSE
            (unfold_tac ctxt depends_on_defs
             THEN IF_UNSOLVED continue_reducing_tac)))
  in
    tactic st
  end
\<close>


subsection "Handling split 'preprocessing'"

lemma split_tranfs:
  "\<forall>x. P x \<and> Q x \<equiv> (\<forall>x. P x) \<and> (\<forall>x. Q x)"
  "\<not> (\<not> A) \<equiv> A"
  "\<exists>x. A \<equiv> A"
  "(A \<and> B) \<and> C \<equiv> A \<and> B \<and> C"
  "A = B \<equiv> (A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
by (rule eq_reflection, auto)+

(*Same idiom as ex_expander_tac*)
ML \<open>
fun split_simp_tac (ctxt : Proof.context) i =
   let
     val simpset =
       fold Simplifier.add_simp @{thms split_tranfs} (empty_simpset ctxt)
   in
     CHANGED (asm_full_simp_tac simpset i)
   end
\<close>


subsection "Alternative reconstruction tactics"
ML \<open>
(*An "auto"-based proof reconstruction, where we attempt to reconstruct each inference
  using auto_tac. A realistic tactic would inspect the inference name and act
  accordingly.*)
fun auto_based_reconstruction_tac ctxt prob_name n =
  let
    val thy = Proof_Context.theory_of ctxt
    val pannot = TPTP_Reconstruct.get_pannot_of_prob thy prob_name
  in
    TPTP_Reconstruct.inference_at_node
     thy
     prob_name (#meta pannot) n
      |> the
      |> (fn {inference_fmla, ...} =>
          Goal.prove ctxt [] [] inference_fmla
           (fn pdata => auto_tac (#context pdata)))
  end
\<close>

(*An oracle-based reconstruction, which is only used to test the shunting part of the system*)
oracle oracle_iinterp = "fn t => t"
ML \<open>
fun oracle_based_reconstruction_tac ctxt prob_name n =
  let
    val thy = Proof_Context.theory_of ctxt
    val pannot = TPTP_Reconstruct.get_pannot_of_prob thy prob_name
  in
    TPTP_Reconstruct.inference_at_node
     thy
     prob_name (#meta pannot) n
      |> the
      |> (fn {inference_fmla, ...} => Thm.cterm_of ctxt inference_fmla)
      |> oracle_iinterp
  end
\<close>


subsection "Leo2 reconstruction tactic"

ML \<open>
exception UNSUPPORTED_ROLE
exception INTERPRET_INFERENCE

(*Failure reports can be adjusted to avoid interrupting
  an overall reconstruction process*)
fun fail ctxt x =
  if unexceptional_reconstruction ctxt then
    (warning x; raise INTERPRET_INFERENCE)
  else error x

fun interpret_leo2_inference_tac ctxt prob_name node =
  let
    val thy = Proof_Context.theory_of ctxt

    val _ =
      if Config.get ctxt tptp_trace_reconstruction then
        tracing ("interpret_inference reconstructing node" ^ node ^ " of " ^ TPTP_Problem_Name.mangle_problem_name prob_name)
      else ()

    val pannot = TPTP_Reconstruct.get_pannot_of_prob thy prob_name

    fun nonfull_extcnf_combined_tac feats =
      extcnf_combined_tac ctxt (SOME prob_name)
       [ConstsDiff,
        StripQuantifiers,
        InnerLoopOnce (Break_Hypotheses :: (*FIXME RemoveRedundantQuantifications :: *) feats),
        AbsorbSkolemDefs]
       []

    val source_inf_opt =
      AList.lookup (op =) (#meta pannot)
      #> the
      #> #source_inf_opt

    (*FIXME integrate this with other lookup code, or in the early analysis*)
    local
      fun node_is_of_role role node =
        AList.lookup (op =) (#meta pannot) node |> the
        |> #role
        |> (fn role' => role = role')

      fun roled_dependencies_names role =
        let
          fun values () =
            case role of
                TPTP_Syntax.Role_Definition =>
                  map (apsnd Binding.name_of) (#defs pannot)
              | TPTP_Syntax.Role_Axiom =>
                  map (apsnd Binding.name_of) (#axs pannot)
              | _ => raise UNSUPPORTED_ROLE
          in
            if is_none (source_inf_opt node) then []
            else
              case the (source_inf_opt node) of
                  TPTP_Proof.Inference (_, _, parent_inf) =>
                    map TPTP_Proof.parent_name parent_inf
                    |> filter (node_is_of_role role)
                    |> (*FIXME currently definitions are not
                         included in the proof annotations, so
                         i'm using all the definitions available
                         in the proof. ideally i should only
                         use the ones in the proof annotation.*)
                       (fn x =>
                         if role = TPTP_Syntax.Role_Definition then
                           let fun values () = map (apsnd Binding.name_of) (#defs pannot)
                           in
                             map snd (values ())
                           end
                         else
                         map (fn node => AList.lookup (op =) (values ()) node |> the) x)
                | _ => []
         end

      val roled_dependencies =
        roled_dependencies_names
        #> map (Global_Theory.get_thm thy)
    in
      val depends_on_defs = roled_dependencies TPTP_Syntax.Role_Definition
      val depends_on_axs = roled_dependencies TPTP_Syntax.Role_Axiom
      val depends_on_defs_names = roled_dependencies_names TPTP_Syntax.Role_Definition
    end

    fun get_binds source_inf_opt =
      case the source_inf_opt of
          TPTP_Proof.Inference (_, _, parent_inf) =>
            maps
              (fn TPTP_Proof.Parent _ => []
                | TPTP_Proof.ParentWithDetails (_, parent_details) => parent_details)
              parent_inf
        | _ => []

    val inference_name =
      case TPTP_Reconstruct.inference_at_node thy prob_name (#meta pannot) node of
          NONE => fail ctxt "Cannot reconstruct rule: no information"
        | SOME {inference_name, ...} => inference_name
    val default_tac = HEADGOAL (blast_tac ctxt)
  in
    case inference_name of
      "fo_atp_e" =>
        HEADGOAL (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combs_or_liftingN ctxt [])
        (*NOTE To treat E as an oracle use the following line:
        HEADGOAL (etac (oracle_based_reconstruction_tac ctxt prob_name node))
        *)
    | "copy" =>
         HEADGOAL
          (assume_tac ctxt
           ORELSE'
              (resolve_tac ctxt @{thms polarise}
               THEN' assume_tac ctxt))
    | "polarity_switch" => nonfull_extcnf_combined_tac [Polarity_switch]
    | "solved_all_splits" => solved_all_splits_tac ctxt
    | "extcnf_not_pos" => nonfull_extcnf_combined_tac [Not_pos]
    | "extcnf_forall_pos" => nonfull_extcnf_combined_tac [Universal]
    | "negate_conjecture" => fail ctxt "Should not handle negate_conjecture here"
    | "unfold_def" => unfold_def_tac ctxt depends_on_defs
    | "extcnf_not_neg" => nonfull_extcnf_combined_tac [Not_neg]
    | "extcnf_or_neg" => nonfull_extcnf_combined_tac [Or_neg]
    | "extcnf_equal_pos" => nonfull_extcnf_combined_tac [Equal_pos]
    | "extcnf_equal_neg" => nonfull_extcnf_combined_tac [Equal_neg]
    | "extcnf_forall_special_pos" =>
         nonfull_extcnf_combined_tac [Forall_special_pos]
         ORELSE HEADGOAL (blast_tac ctxt)
    | "extcnf_or_pos" => nonfull_extcnf_combined_tac [Or_pos]
    | "extuni_bool2" => nonfull_extcnf_combined_tac [Extuni_Bool2]
    | "extuni_bool1" => nonfull_extcnf_combined_tac [Extuni_Bool1]
    | "extuni_dec" =>
        HEADGOAL (assume_tac ctxt)
        ORELSE nonfull_extcnf_combined_tac [Extuni_Dec]
    | "extuni_bind" => nonfull_extcnf_combined_tac [Extuni_Bind]
    | "extuni_triv" => nonfull_extcnf_combined_tac [Extuni_Triv]
    | "extuni_flex_rigid" => nonfull_extcnf_combined_tac [Extuni_FlexRigid]
    | "prim_subst" => nonfull_extcnf_combined_tac [Assumption]
    | "bind" =>
        let
          val ordered_binds = get_binds (source_inf_opt node)
        in
          bind_tac ctxt prob_name ordered_binds
        end
    | "standard_cnf" => HEADGOAL (standard_cnf_tac ctxt)
    | "extcnf_forall_neg" =>
        nonfull_extcnf_combined_tac
         [Existential_Var(* , RemoveRedundantQuantifications *)] (*FIXME RemoveRedundantQuantifications*)
    | "extuni_func" =>
        nonfull_extcnf_combined_tac [Extuni_Func, Existential_Var]
    | "replace_leibnizEQ" => nonfull_extcnf_combined_tac [Assumption]
    | "replace_andrewsEQ" => nonfull_extcnf_combined_tac [Assumption]
    | "split_preprocessing" =>
         (REPEAT (HEADGOAL (split_simp_tac ctxt)))
         THEN TRY (PRIMITIVE (Conv.fconv_rule Thm.eta_long_conversion))
         THEN HEADGOAL (assume_tac ctxt)

    (*FIXME some of these could eventually be handled specially*)
    | "fac_restr" => default_tac
    | "sim" => default_tac
    | "res" => default_tac
    | "rename" => default_tac
    | "flexflex" => default_tac
    | other => fail ctxt ("Unknown inference rule: " ^ other)
  end
\<close>

ML \<open>
fun interpret_leo2_inference ctxt prob_name node =
  let
    val thy = Proof_Context.theory_of ctxt
    val pannot = TPTP_Reconstruct.get_pannot_of_prob thy prob_name

    val (inference_name, inference_fmla) =
      case TPTP_Reconstruct.inference_at_node thy prob_name (#meta pannot) node of
          NONE => fail ctxt "Cannot reconstruct rule: no information"
        | SOME {inference_name, inference_fmla, ...} =>
            (inference_name, inference_fmla)

    val proof_outcome =
      let
        fun prove () =
          Goal.prove ctxt [] [] inference_fmla
           (fn pdata => interpret_leo2_inference_tac
            (#context pdata) prob_name node)
      in
        if informative_failure ctxt then SOME (prove ())
        else try prove ()
      end

  in case proof_outcome of
      NONE => fail ctxt (Pretty.string_of
        (Pretty.block
          [Pretty.str ("Failed inference reconstruction for '" ^
            inference_name ^ "' at node " ^ node ^ ":\n"),
           Syntax.pretty_term ctxt inference_fmla]))
    | SOME thm => thm
  end
\<close>

ML \<open>
(*filter a set of nodes based on which inference rule was used to
  derive a node*)
fun nodes_by_inference (fms : TPTP_Reconstruct.formula_meaning list) inference_rule =
  let
    fun fold_fun n l =
      case TPTP_Reconstruct.node_info fms #source_inf_opt n of
          NONE => l
        | SOME (TPTP_Proof.File _) => l
        | SOME (TPTP_Proof.Inference (rule_name, _, _)) =>
            if rule_name = inference_rule then n :: l
            else l
  in
    fold fold_fun (map fst fms) []
  end
\<close>


section "Importing proofs and reconstructing theorems"

ML \<open>
(*Preprocessing carried out on a LEO-II proof.*)
fun leo2_on_load (pannot : TPTP_Reconstruct.proof_annotation) thy =
  let
    val ctxt = Proof_Context.init_global thy
    val dud = ("", Binding.empty, \<^term>\<open>False\<close>)
    val pre_skolem_defs =
      nodes_by_inference (#meta pannot) "extcnf_forall_neg" @
       nodes_by_inference (#meta pannot) "extuni_func"
      |> map (fn x =>
              (interpret_leo2_inference ctxt (#problem_name pannot) x; dud)
               handle NO_SKOLEM_DEF (s, bnd, t) => (s, bnd, t))
      |> filter (fn (x, _, _) => x <> "") (*In case no skolem constants were introduced in that inference*)
    val skolem_defs = map (fn (x, y, _) => (x, y)) pre_skolem_defs
    val thy' =
      fold (fn skolem_def => fn thy =>
             let
               val ((s, thm), thy') = Thm.add_axiom_global skolem_def thy
               (* val _ = warning ("Added skolem definition " ^ s ^ ": " ^  @{make_string thm}) *) (*FIXME use of make_string*)
             in thy' end)
       (map (fn (_, y, z) => (y, z)) pre_skolem_defs)
       thy
  in
    ({problem_name = #problem_name pannot,
      skolem_defs = skolem_defs,
      defs = #defs pannot,
      axs = #axs pannot,
      meta = #meta pannot},
     thy')
  end
\<close>

ML \<open>
(*Imports and reconstructs a LEO-II proof.*)
fun reconstruct_leo2 path thy =
  let
    val prob_file = Path.base path
    val dir = Path.dir path
    val thy' = TPTP_Reconstruct.import_thm true [dir, prob_file] path leo2_on_load thy
    val ctxt =
      Context.Theory thy'
      |> Context.proof_of
    val prob_name =
      Path.implode prob_file
      |> TPTP_Problem_Name.parse_problem_name
    val theorem =
      TPTP_Reconstruct.reconstruct ctxt
       (TPTP_Reconstruct.naive_reconstruct_tac ctxt interpret_leo2_inference)
       prob_name
  in
    (*NOTE we could return the theorem value alone, since
       users could get the thy value from the thm value.*)
    (thy', theorem)
  end
\<close>

end
