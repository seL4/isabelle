(*  Title:      HOL/HOLCF/IOA/CompoScheds.thy
    Author:     Olaf Müller
*)

section \<open>Compositionality on Schedule level\<close>

theory CompoScheds
imports CompoExecs
begin

definition mkex2 :: "('a, 's) ioa \<Rightarrow> ('a, 't) ioa \<Rightarrow> 'a Seq \<rightarrow>
  ('a, 's) pairs \<rightarrow> ('a, 't) pairs \<rightarrow> ('s \<Rightarrow> 't \<Rightarrow> ('a, 's \<times> 't) pairs)"
  where "mkex2 A B =
    (fix $
      (LAM h sch exA exB.
        (\<lambda>s t.
          case sch of
            nil \<Rightarrow> nil
        | x ## xs \<Rightarrow>
            (case x of
              UU \<Rightarrow> UU
            | Def y \<Rightarrow>
               (if y \<in> act A then
                 (if y \<in> act B then
                    (case HD $ exA of
                      UU \<Rightarrow> UU
                    | Def a \<Rightarrow>
                        (case HD $ exB of
                          UU \<Rightarrow> UU
                        | Def b \<Rightarrow>
                           (y, (snd a, snd b)) \<leadsto>
                            (h $ xs $ (TL $ exA) $ (TL $ exB)) (snd a) (snd b)))
                  else
                    (case HD $ exA of
                      UU \<Rightarrow> UU
                    | Def a \<Rightarrow> (y, (snd a, t)) \<leadsto> (h $ xs $ (TL $ exA) $ exB) (snd a) t))
                else
                  (if y \<in> act B then
                    (case HD $ exB of
                      UU \<Rightarrow> UU
                    | Def b \<Rightarrow> (y, (s, snd b)) \<leadsto> (h $ xs $ exA $ (TL $ exB)) s (snd b))
                   else UU))))))"

definition mkex :: "('a, 's) ioa \<Rightarrow> ('a, 't) ioa \<Rightarrow> 'a Seq \<Rightarrow>
    ('a, 's) execution \<Rightarrow> ('a, 't) execution \<Rightarrow> ('a, 's \<times> 't) execution"
  where "mkex A B sch exA exB =
    ((fst exA, fst exB), (mkex2 A B $ sch $ (snd exA) $ (snd exB)) (fst exA) (fst exB))"

definition par_scheds :: "'a schedule_module \<Rightarrow> 'a schedule_module \<Rightarrow> 'a schedule_module"
  where "par_scheds SchedsA SchedsB =
    (let
      schA = fst SchedsA; sigA = snd SchedsA;
      schB = fst SchedsB; sigB = snd SchedsB
     in
      ({sch. Filter (%a. a:actions sigA)$sch : schA} \<inter>
       {sch. Filter (%a. a:actions sigB)$sch : schB} \<inter>
       {sch. Forall (%x. x:(actions sigA Un actions sigB)) sch},
        asig_comp sigA sigB))"


subsection \<open>\<open>mkex\<close> rewrite rules\<close>

lemma mkex2_unfold:
  "mkex2 A B =
    (LAM sch exA exB.
      (\<lambda>s t.
        case sch of
          nil \<Rightarrow> nil
        | x ## xs \<Rightarrow>
            (case x of
              UU \<Rightarrow> UU
            | Def y \<Rightarrow>
                (if y \<in> act A then
                  (if y \<in> act B then
                    (case HD $ exA of
                      UU \<Rightarrow> UU
                    | Def a \<Rightarrow>
                        (case HD $ exB of
                          UU \<Rightarrow> UU
                        | Def b \<Rightarrow>
                            (y, (snd a, snd b)) \<leadsto>
                              (mkex2 A B $ xs $ (TL $ exA) $ (TL $ exB)) (snd a) (snd b)))
                   else
                     (case HD $ exA of
                       UU \<Rightarrow> UU
                     | Def a \<Rightarrow> (y, (snd a, t)) \<leadsto> (mkex2 A B $ xs $ (TL $ exA) $ exB) (snd a) t))
                 else
                   (if y \<in> act B then
                     (case HD $ exB of
                       UU \<Rightarrow> UU
                     | Def b \<Rightarrow> (y, (s, snd b)) \<leadsto> (mkex2 A B $ xs $ exA $ (TL $ exB)) s (snd b))
                    else UU)))))"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (simp only: mkex2_def)
  apply (rule beta_cfun)
  apply simp
  done

lemma mkex2_UU: "(mkex2 A B $ UU $ exA $ exB) s t = UU"
  apply (subst mkex2_unfold)
  apply simp
  done

lemma mkex2_nil: "(mkex2 A B $ nil $ exA $ exB) s t = nil"
  apply (subst mkex2_unfold)
  apply simp
  done

lemma mkex2_cons_1:
  "x \<in> act A \<Longrightarrow> x \<notin> act B \<Longrightarrow> HD $ exA = Def a \<Longrightarrow>
    (mkex2 A B $ (x \<leadsto> sch) $ exA $ exB) s t =
      (x, snd a,t) \<leadsto> (mkex2 A B $ sch $ (TL $ exA) $ exB) (snd a) t"
  apply (rule trans)
  apply (subst mkex2_unfold)
  apply (simp add: Consq_def If_and_if)
  apply (simp add: Consq_def)
  done

lemma mkex2_cons_2:
  "x \<notin> act A \<Longrightarrow> x \<in> act B \<Longrightarrow> HD $ exB = Def b \<Longrightarrow>
    (mkex2 A B $ (x \<leadsto> sch) $ exA $ exB) s t =
      (x, s, snd b) \<leadsto> (mkex2 A B $ sch $ exA $ (TL $ exB)) s (snd b)"
  apply (rule trans)
  apply (subst mkex2_unfold)
  apply (simp add: Consq_def If_and_if)
  apply (simp add: Consq_def)
  done

lemma mkex2_cons_3:
  "x \<in> act A \<Longrightarrow> x \<in> act B \<Longrightarrow> HD $ exA = Def a \<Longrightarrow> HD $ exB = Def b \<Longrightarrow>
    (mkex2 A B $ (x \<leadsto> sch) $ exA $ exB) s t =
      (x, snd a,snd b) \<leadsto> (mkex2 A B $ sch $ (TL $ exA) $ (TL $ exB)) (snd a) (snd b)"
  apply (rule trans)
  apply (subst mkex2_unfold)
  apply (simp add: Consq_def If_and_if)
  apply (simp add: Consq_def)
  done

declare mkex2_UU [simp] mkex2_nil [simp] mkex2_cons_1 [simp]
  mkex2_cons_2 [simp] mkex2_cons_3 [simp]


subsection \<open>\<open>mkex\<close>\<close>

lemma mkex_UU: "mkex A B UU  (s,exA) (t,exB) = ((s,t),UU)"
  by (simp add: mkex_def)

lemma mkex_nil: "mkex A B nil (s,exA) (t,exB) = ((s,t),nil)"
  by (simp add: mkex_def)

lemma mkex_cons_1:
  "x \<in> act A \<Longrightarrow> x \<notin> act B \<Longrightarrow>
    mkex A B (x \<leadsto> sch) (s, a \<leadsto> exA) (t, exB) =
      ((s, t), (x, snd a, t) \<leadsto> snd (mkex A B sch (snd a, exA) (t, exB)))"
  apply (unfold mkex_def)
  apply (cut_tac exA = "a \<leadsto> exA" in mkex2_cons_1)
  apply auto
  done

lemma mkex_cons_2:
  "x \<notin> act A \<Longrightarrow> x \<in> act B \<Longrightarrow>
    mkex A B (x \<leadsto> sch) (s, exA) (t, b \<leadsto> exB) =
      ((s, t), (x, s, snd b) \<leadsto> snd (mkex A B sch (s, exA) (snd b, exB)))"
  apply (unfold mkex_def)
  apply (cut_tac exB = "b\<leadsto>exB" in mkex2_cons_2)
  apply auto
  done

lemma mkex_cons_3:
  "x \<in> act A \<Longrightarrow> x \<in> act B \<Longrightarrow>
    mkex A B (x \<leadsto> sch) (s, a \<leadsto> exA) (t, b \<leadsto> exB) =
      ((s, t), (x, snd a, snd b) \<leadsto> snd (mkex A B sch (snd a, exA) (snd b, exB)))"
  apply (unfold mkex_def)
  apply (cut_tac exB = "b\<leadsto>exB" and exA = "a\<leadsto>exA" in mkex2_cons_3)
  apply auto
  done

declare mkex2_UU [simp del] mkex2_nil [simp del]
  mkex2_cons_1 [simp del] mkex2_cons_2 [simp del] mkex2_cons_3 [simp del]

lemmas composch_simps = mkex_UU mkex_nil mkex_cons_1 mkex_cons_2 mkex_cons_3

declare composch_simps [simp]


subsection \<open>Compositionality on schedule level\<close>

subsubsection \<open>Lemmas for \<open>\<Longrightarrow>\<close>\<close>

lemma lemma_2_1a:
  \<comment> \<open>\<open>tfilter ex\<close> and \<open>filter_act\<close> are commutative\<close>
  "filter_act $ (Filter_ex2 (asig_of A) $ xs) =
    Filter (\<lambda>a. a \<in> act A) $ (filter_act $ xs)"
  apply (unfold filter_act_def Filter_ex2_def)
  apply (simp add: MapFilter o_def)
  done

lemma lemma_2_1b:
  \<comment> \<open>State-projections do not affect \<open>filter_act\<close>\<close>
  "filter_act $ (ProjA2 $ xs) = filter_act $ xs \<and>
    filter_act $ (ProjB2 $ xs) = filter_act $ xs"
  by (pair_induct xs)


text \<open>
  Schedules of \<open>A \<parallel> B\<close> have only \<open>A\<close>- or \<open>B\<close>-actions.

  Very similar to \<open>lemma_1_1c\<close>, but it is not checking if every action element
  of an \<open>ex\<close> is in \<open>A\<close> or \<open>B\<close>, but after projecting it onto the action
  schedule. Of course, this is the same proposition, but we cannot change this
  one, when then rather \<open>lemma_1_1c\<close>.
\<close>

lemma sch_actions_in_AorB:
  "\<forall>s. is_exec_frag (A \<parallel> B) (s, xs) \<longrightarrow> Forall (\<lambda>x. x \<in> act (A \<parallel> B)) (filter_act $ xs)"
  apply (pair_induct xs simp: is_exec_frag_def Forall_def sforall_def)
  text \<open>main case\<close>
  apply auto
  apply (simp add: trans_of_defs2 actions_asig_comp asig_of_par)
  done


subsubsection \<open>Lemmas for \<open>\<Longleftarrow>\<close>\<close>

text \<open>
  Filtering actions out of \<open>mkex (sch, exA, exB)\<close> yields the oracle \<open>sch\<close>
  structural induction.
\<close>

lemma Mapfst_mkex_is_sch:
  "\<forall>exA exB s t.
    Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch \<and>
    Filter (\<lambda>a. a \<in> act A) $ sch \<sqsubseteq> filter_act $ exA \<and>
    Filter (\<lambda>a. a \<in> act B) $ sch \<sqsubseteq> filter_act $ exB \<longrightarrow>
    filter_act $ (snd (mkex A B sch (s, exA) (t, exB))) = sch"
  apply (Seq_induct sch simp: Filter_def Forall_def sforall_def mkex_def)

  text \<open>main case: splitting into 4 cases according to \<open>a \<in> A\<close>, \<open>a \<in> B\<close>\<close>
  apply auto

  text \<open>Case \<open>y \<in> A\<close>, \<open>y \<in> B\<close>\<close>
  apply (Seq_case_simp exA)
  text \<open>Case \<open>exA = UU\<close>, Case \<open>exA = nil\<close>\<close>
  text \<open>
    These \<open>UU\<close> and \<open>nil\<close> cases are the only places where the assumption
    \<open>filter A sch \<sqsubseteq> f_act exA\<close> is used!
    \<open>\<longrightarrow>\<close> to generate a contradiction using \<open>\<not> a \<leadsto> ss \<sqsubseteq> UU nil\<close>,
    using theorems \<open>Cons_not_less_UU\<close> and \<open>Cons_not_less_nil\<close>.\<close>
  apply (Seq_case_simp exB)
  text \<open>Case \<open>exA = a \<leadsto> x\<close>, \<open>exB = b \<leadsto> y\<close>\<close>
  text \<open>
    Here it is important that @{method Seq_case_simp} uses no \<open>!full!_simp_tac\<close>
    for the cons case, as otherwise \<open>mkex_cons_3\<close> would not be rewritten
    without use of \<open>rotate_tac\<close>: then tactic would not be generally
    applicable.\<close>
  apply simp

  text \<open>Case \<open>y \<in> A\<close>, \<open>y \<notin> B\<close>\<close>
  apply (Seq_case_simp exA)
  apply simp

  text \<open>Case \<open>y \<notin> A\<close>, \<open>y \<in> B\<close>\<close>
  apply (Seq_case_simp exB)
  apply simp

  text \<open>Case \<open>y \<notin> A\<close>, \<open>y \<notin> B\<close>\<close>
  apply (simp add: asig_of_par actions_asig_comp)
  done


text \<open>Generalizing the proof above to a proof method:\<close>
ML \<open>
fun mkex_induct_tac ctxt sch exA exB =
  EVERY' [
    Seq_induct_tac ctxt sch
      @{thms Filter_def Forall_def sforall_def mkex_def stutter_def},
    asm_full_simp_tac ctxt,
    SELECT_GOAL
      (safe_tac (Context.raw_transfer (Proof_Context.theory_of ctxt) @{theory_context Fun})),
    Seq_case_simp_tac ctxt exA,
    Seq_case_simp_tac ctxt exB,
    asm_full_simp_tac ctxt,
    Seq_case_simp_tac ctxt exA,
    asm_full_simp_tac ctxt,
    Seq_case_simp_tac ctxt exB,
    asm_full_simp_tac ctxt,
    asm_full_simp_tac (ctxt addsimps @{thms asig_of_par actions_asig_comp})]
\<close>

method_setup mkex_induct = \<open>
  Scan.lift (Args.embedded -- Args.embedded -- Args.embedded)
    >> (fn ((sch, exA), exB) => fn ctxt =>
      SIMPLE_METHOD' (mkex_induct_tac ctxt sch exA exB))
\<close>


text \<open>
  Projection of \<open>mkex (sch, exA, exB)\<close> onto \<open>A\<close> stutters on \<open>A\<close>
  structural induction.
\<close>

lemma stutterA_mkex:
  "\<forall>exA exB s t.
    Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch \<and>
    Filter (\<lambda>a. a \<in> act A) $ sch \<sqsubseteq> filter_act $ exA \<and>
    Filter (\<lambda>a. a \<in> act B) $ sch \<sqsubseteq> filter_act $ exB \<longrightarrow>
    stutter (asig_of A) (s, ProjA2 $ (snd (mkex A B sch (s, exA) (t, exB))))"
  by (mkex_induct sch exA exB)

lemma stutter_mkex_on_A:
  "Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch \<Longrightarrow>
    Filter (\<lambda>a. a \<in> act A) $ sch \<sqsubseteq> filter_act $ (snd exA) \<Longrightarrow>
    Filter (\<lambda>a. a \<in> act B) $ sch \<sqsubseteq> filter_act $ (snd exB) \<Longrightarrow>
    stutter (asig_of A) (ProjA (mkex A B sch exA exB))"
  apply (cut_tac stutterA_mkex)
  apply (simp add: stutter_def ProjA_def mkex_def)
  apply (erule allE)+
  apply (drule mp)
  prefer 2 apply (assumption)
  apply simp
  done


text \<open>
  Projection of \<open>mkex (sch, exA, exB)\<close> onto \<open>B\<close> stutters on \<open>B\<close>
  structural induction.
\<close>

lemma stutterB_mkex:
  "\<forall>exA exB s t.
    Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch \<and>
    Filter (\<lambda>a. a \<in> act A) $ sch \<sqsubseteq> filter_act $ exA \<and>
    Filter (\<lambda>a. a \<in> act B) $ sch \<sqsubseteq> filter_act $ exB \<longrightarrow>
    stutter (asig_of B) (t, ProjB2 $ (snd (mkex A B sch (s, exA) (t, exB))))"
  by (mkex_induct sch exA exB)


lemma stutter_mkex_on_B:
  "Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch \<Longrightarrow>
   Filter (\<lambda>a. a \<in> act A) $ sch \<sqsubseteq> filter_act $ (snd exA) \<Longrightarrow>
   Filter (\<lambda>a. a \<in> act B) $ sch \<sqsubseteq> filter_act $ (snd exB) \<Longrightarrow>
   stutter (asig_of B) (ProjB (mkex A B sch exA exB))"
  apply (cut_tac stutterB_mkex)
  apply (simp add: stutter_def ProjB_def mkex_def)
  apply (erule allE)+
  apply (drule mp)
  prefer 2 apply (assumption)
  apply simp
  done


text \<open>
  Filter of \<open>mkex (sch, exA, exB)\<close> to \<open>A\<close> after projection onto \<open>A\<close> is \<open>exA\<close>,
  using \<open>zip $ (proj1 $ exA) $ (proj2 $ exA)\<close> instead of \<open>exA\<close>,
  because of admissibility problems structural induction.
\<close>

lemma filter_mkex_is_exA_tmp:
  "\<forall>exA exB s t.
    Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch \<and>
    Filter (\<lambda>a. a \<in> act A) $ sch \<sqsubseteq> filter_act $ exA \<and>
    Filter (\<lambda>a. a \<in> act B) $ sch \<sqsubseteq> filter_act $ exB \<longrightarrow>
    Filter_ex2 (asig_of A) $ (ProjA2 $ (snd (mkex A B sch (s, exA) (t, exB)))) =
      Zip $ (Filter (\<lambda>a. a \<in> act A) $ sch) $ (Map snd $ exA)"
  by (mkex_induct sch exB exA)

text \<open>
  \<open>zip $ (proj1 $ y) $ (proj2 $ y) = y\<close>  (using the lift operations)
  lemma for admissibility problems
\<close>

lemma Zip_Map_fst_snd: "Zip $ (Map fst $ y) $ (Map snd $ y) = y"
  by (Seq_induct y)


text \<open>
  \<open>filter A $ sch = proj1 $ ex \<longrightarrow> zip $ (filter A $ sch) $ (proj2 $ ex) = ex\<close>
  lemma for eliminating non admissible equations in assumptions
\<close>

lemma trick_against_eq_in_ass:
  "Filter (\<lambda>a. a \<in> act AB) $ sch = filter_act $ ex \<Longrightarrow>
    ex = Zip $ (Filter (\<lambda>a. a \<in> act AB) $ sch) $ (Map snd $ ex)"
  apply (simp add: filter_act_def)
  apply (rule Zip_Map_fst_snd [symmetric])
  done

text \<open>
  Filter of \<open>mkex (sch, exA, exB)\<close> to \<open>A\<close> after projection onto \<open>A\<close> is \<open>exA\<close>
  using the above trick.
\<close>

lemma filter_mkex_is_exA:
  "Forall (\<lambda>a. a \<in> act (A \<parallel> B)) sch \<Longrightarrow>
    Filter (\<lambda>a. a \<in> act A) $ sch = filter_act $ (snd exA) \<Longrightarrow>
    Filter (\<lambda>a. a \<in> act B) $ sch = filter_act $ (snd exB) \<Longrightarrow>
  Filter_ex (asig_of A) (ProjA (mkex A B sch exA exB)) = exA"
  apply (simp add: ProjA_def Filter_ex_def)
  apply (pair exA)
  apply (pair exB)
  apply (rule conjI)
  apply (simp (no_asm) add: mkex_def)
  apply (simplesubst trick_against_eq_in_ass)
  back
  apply assumption
  apply (simp add: filter_mkex_is_exA_tmp)
  done

text \<open>
  Filter of \<open>mkex (sch, exA, exB)\<close> to \<open>B\<close> after projection onto \<open>B\<close> is \<open>exB\<close>
  using \<open>zip $ (proj1 $ exB) $ (proj2 $ exB)\<close> instead of \<open>exB\<close>
  because of admissibility problems structural induction.
\<close>

lemma filter_mkex_is_exB_tmp:
  "\<forall>exA exB s t.
    Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch \<and>
    Filter (\<lambda>a. a \<in> act A) $ sch \<sqsubseteq> filter_act $ exA \<and>
    Filter (\<lambda>a. a \<in> act B) $ sch \<sqsubseteq> filter_act $ exB \<longrightarrow>
    Filter_ex2 (asig_of B) $ (ProjB2 $ (snd (mkex A B sch (s, exA) (t, exB)))) =
      Zip $ (Filter (\<lambda>a. a \<in> act B) $ sch) $ (Map snd $ exB)"
  (*notice necessary change of arguments exA and exB*)
  by (mkex_induct sch exA exB)

text \<open>
  Filter of \<open>mkex (sch, exA, exB)\<close> to \<open>A\<close> after projection onto \<open>B\<close> is \<open>exB\<close>
  using the above trick.
\<close>

lemma filter_mkex_is_exB:
  "Forall (\<lambda>a. a \<in> act (A \<parallel> B)) sch \<Longrightarrow>
    Filter (\<lambda>a. a \<in> act A) $ sch = filter_act $ (snd exA) \<Longrightarrow>
    Filter (\<lambda>a. a \<in> act B) $ sch = filter_act $ (snd exB) \<Longrightarrow>
    Filter_ex (asig_of B) (ProjB (mkex A B sch exA exB)) = exB"
  apply (simp add: ProjB_def Filter_ex_def)
  apply (pair exA)
  apply (pair exB)
  apply (rule conjI)
  apply (simp add: mkex_def)
  apply (simplesubst trick_against_eq_in_ass)
  back
  apply assumption
  apply (simp add: filter_mkex_is_exB_tmp)
  done

lemma mkex_actions_in_AorB:
  \<comment> \<open>\<open>mkex\<close> has only \<open>A\<close>- or \<open>B\<close>-actions\<close>
  "\<forall>s t exA exB.
    Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch &
    Filter (\<lambda>a. a \<in> act A) $ sch \<sqsubseteq> filter_act $ exA \<and>
    Filter (\<lambda>a. a \<in> act B) $ sch \<sqsubseteq> filter_act $ exB \<longrightarrow>
    Forall (\<lambda>x. fst x \<in> act (A \<parallel> B)) (snd (mkex A B sch (s, exA) (t, exB)))"
  by (mkex_induct sch exA exB)


theorem compositionality_sch:
  "sch \<in> schedules (A \<parallel> B) \<longleftrightarrow>
    Filter (\<lambda>a. a \<in> act A) $ sch \<in> schedules A \<and>
    Filter (\<lambda>a. a \<in> act B) $ sch \<in> schedules B \<and>
    Forall (\<lambda>x. x \<in> act (A \<parallel> B)) sch"
  apply (simp add: schedules_def has_schedule_def)
  apply auto
  text \<open>\<open>\<Longrightarrow>\<close>\<close>
  apply (rule_tac x = "Filter_ex (asig_of A) (ProjA ex)" in bexI)
  prefer 2
  apply (simp add: compositionality_ex)
  apply (simp (no_asm) add: Filter_ex_def ProjA_def lemma_2_1a lemma_2_1b)
  apply (rule_tac x = "Filter_ex (asig_of B) (ProjB ex)" in bexI)
  prefer 2
  apply (simp add: compositionality_ex)
  apply (simp add: Filter_ex_def ProjB_def lemma_2_1a lemma_2_1b)
  apply (simp add: executions_def)
  apply (pair ex)
  apply (erule conjE)
  apply (simp add: sch_actions_in_AorB)
  text \<open>\<open>\<Longleftarrow>\<close>\<close>
  text \<open>\<open>mkex\<close> is exactly the construction of \<open>exA\<parallel>B\<close> out of \<open>exA\<close>, \<open>exB\<close>,
    and the oracle \<open>sch\<close>, we need here\<close>
  apply (rename_tac exA exB)
  apply (rule_tac x = "mkex A B sch exA exB" in bexI)
  text \<open>\<open>mkex\<close> actions are just the oracle\<close>
  apply (pair exA)
  apply (pair exB)
  apply (simp add: Mapfst_mkex_is_sch)
  text \<open>\<open>mkex\<close> is an execution -- use compositionality on ex-level\<close>
  apply (simp add: compositionality_ex)
  apply (simp add: stutter_mkex_on_A stutter_mkex_on_B filter_mkex_is_exB filter_mkex_is_exA)
  apply (pair exA)
  apply (pair exB)
  apply (simp add: mkex_actions_in_AorB)
  done

theorem compositionality_sch_modules:
  "Scheds (A \<parallel> B) = par_scheds (Scheds A) (Scheds B)"
  apply (unfold Scheds_def par_scheds_def)
  apply (simp add: asig_of_par)
  apply (rule set_eqI)
  apply (simp add: compositionality_sch actions_of_par)
  done

declare compoex_simps [simp del]
declare composch_simps [simp del]

end
