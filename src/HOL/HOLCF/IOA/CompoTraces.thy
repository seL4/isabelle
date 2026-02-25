(*  Title:      HOL/HOLCF/IOA/CompoTraces.thy
    Author:     Olaf Müller
*)

section \<open>Compositionality on Trace level\<close>

theory CompoTraces
imports CompoScheds ShortExecutions
begin

definition mksch ::
    "('a, 's) ioa \<Rightarrow> ('a, 't) ioa \<Rightarrow> 'a Seq \<rightarrow> 'a Seq \<rightarrow> 'a Seq \<rightarrow> 'a Seq"
  where "mksch A B =
    (fix \<cdot>
      (LAM h tr schA schB.
        case tr of
          nil \<Rightarrow> nil
        | x ## xs \<Rightarrow>
            (case x of
              UU \<Rightarrow> UU
            | Def y \<Rightarrow>
                (if y \<in> act A then
                  (if y \<in> act B then
                    ((Takewhile (\<lambda>a. a \<in> int A) \<cdot> schA) @@
                     (Takewhile (\<lambda>a. a \<in> int B) \<cdot> schB) @@
                     (y \<leadsto> (h \<cdot> xs \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int A) \<cdot> schA))
                                   \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int B) \<cdot> schB)))))
                   else
                    ((Takewhile (\<lambda>a. a \<in> int A) \<cdot> schA) @@
                     (y \<leadsto> (h \<cdot> xs \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int A) \<cdot> schA)) \<cdot> schB))))
                 else
                  (if y \<in> act B then
                    ((Takewhile (\<lambda>a. a \<in> int B) \<cdot> schB) @@
                     (y \<leadsto> (h \<cdot> xs \<cdot> schA \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int B) \<cdot> schB)))))
                   else UU)))))"

definition par_traces :: "'a trace_module \<Rightarrow> 'a trace_module \<Rightarrow> 'a trace_module"
  where "par_traces TracesA TracesB =
    (let
      trA = fst TracesA; sigA = snd TracesA;
      trB = fst TracesB; sigB = snd TracesB
     in
       ({tr. Filter (\<lambda>a. a \<in> actions sigA) \<cdot> tr \<in> trA} \<inter>
        {tr. Filter (\<lambda>a. a \<in> actions sigB) \<cdot> tr \<in> trB} \<inter>
        {tr. Forall (\<lambda>x. x \<in> externals sigA \<union> externals sigB) tr},
        asig_comp sigA sigB))"

axiomatization where
  finiteR_mksch: "Finite (mksch A B \<cdot> tr \<cdot> x \<cdot> y) \<Longrightarrow> Finite tr"

lemma finiteR_mksch': "\<not> Finite tr \<Longrightarrow> \<not> Finite (mksch A B \<cdot> tr \<cdot> x \<cdot> y)"
  by (blast intro: finiteR_mksch)


declaration \<open>K (Simplifier.map_simpset (Simplifier.set_mksym (K (K NONE))))\<close>


subsection "mksch rewrite rules"

lemma mksch_unfold:
  "mksch A B =
    (LAM tr schA schB.
      case tr of
        nil \<Rightarrow> nil
      | x ## xs \<Rightarrow>
          (case x of
            UU \<Rightarrow> UU
          | Def y \<Rightarrow>
              (if y \<in> act A then
                (if y \<in> act B then
                  ((Takewhile (\<lambda>a. a \<in> int A) \<cdot> schA) @@
                   (Takewhile (\<lambda>a. a \<in> int B) \<cdot> schB) @@
                   (y \<leadsto> (mksch A B \<cdot> xs \<cdot>(TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int A) \<cdot> schA))
                                         \<cdot>(TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int B) \<cdot> schB)))))
                 else
                  ((Takewhile (\<lambda>a. a \<in> int A) \<cdot> schA) @@
                   (y \<leadsto> (mksch A B \<cdot> xs \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int A) \<cdot> schA)) \<cdot> schB))))
               else
                (if y \<in> act B then
                  ((Takewhile (\<lambda>a. a \<in> int B) \<cdot> schB) @@
                   (y \<leadsto> (mksch A B \<cdot> xs \<cdot> schA \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int B) \<cdot> schB)))))
                 else UU))))"
  apply (rule trans)
  apply (rule fix_eq4)
  apply (rule mksch_def)
  apply (rule beta_cfun)
  apply simp
  done

lemma mksch_UU: "mksch A B \<cdot> UU \<cdot> schA \<cdot> schB = UU"
  apply (subst mksch_unfold)
  apply simp
  done

lemma mksch_nil: "mksch A B \<cdot> nil \<cdot> schA \<cdot> schB = nil"
  apply (subst mksch_unfold)
  apply simp
  done

lemma mksch_cons1:
  "x \<in> act A \<Longrightarrow> x \<notin> act B \<Longrightarrow>
    mksch A B \<cdot> (x \<leadsto> tr) \<cdot> schA \<cdot> schB =
      (Takewhile (\<lambda>a. a \<in> int A) \<cdot> schA) @@
      (x \<leadsto> (mksch A B \<cdot> tr \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int A) \<cdot> schA)) \<cdot> schB))"
  apply (rule trans)
  apply (subst mksch_unfold)
  apply (simp add: Consq_def If_and_if)
  apply (simp add: Consq_def)
  done

lemma mksch_cons2:
  "x \<notin> act A \<Longrightarrow> x \<in> act B \<Longrightarrow>
    mksch A B \<cdot> (x \<leadsto> tr) \<cdot> schA \<cdot> schB =
      (Takewhile (\<lambda>a. a \<in> int B) \<cdot> schB) @@
      (x \<leadsto> (mksch A B \<cdot> tr \<cdot> schA \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int B) \<cdot> schB))))"
  apply (rule trans)
  apply (subst mksch_unfold)
  apply (simp add: Consq_def If_and_if)
  apply (simp add: Consq_def)
  done

lemma mksch_cons3:
  "x \<in> act A \<Longrightarrow> x \<in> act B \<Longrightarrow>
    mksch A B \<cdot> (x \<leadsto> tr) \<cdot> schA \<cdot> schB =
      (Takewhile (\<lambda>a. a \<in> int A) \<cdot> schA) @@
      ((Takewhile (\<lambda>a. a \<in> int B) \<cdot> schB) @@
      (x \<leadsto> (mksch A B \<cdot> tr \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int A) \<cdot> schA))
                            \<cdot> (TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int B) \<cdot> schB)))))"
  apply (rule trans)
  apply (subst mksch_unfold)
  apply (simp add: Consq_def If_and_if)
  apply (simp add: Consq_def)
  done

lemmas compotr_simps = mksch_UU mksch_nil mksch_cons1 mksch_cons2 mksch_cons3

declare compotr_simps [simp]


subsection \<open>COMPOSITIONALITY on TRACE Level\<close>

subsubsection "Lemmata for \<open>\<Longrightarrow>\<close>"

text \<open>
  Consequence out of \<open>ext1_ext2_is_not_act1(2)\<close>, which in turn are
  consequences out of the compatibility of IOA, in particular out of the
  condition that internals are really hidden.
\<close>

lemma compatibility_consequence1: "(eB \<and> \<not> eA \<longrightarrow> \<not> A) \<longrightarrow> A \<and> (eA \<or> eB) \<longleftrightarrow> eA \<and> A"
  by fast


(* very similar to above, only the commutativity of | is used to make a slight change *)
lemma compatibility_consequence2: "(eB \<and> \<not> eA \<longrightarrow> \<not> A) \<longrightarrow> A \<and> (eB \<or> eA) \<longleftrightarrow> eA \<and> A"
  by fast


subsubsection \<open>Lemmata for \<open>\<Longleftarrow>\<close>\<close>

(* Lemma for substitution of looping assumption in another specific assumption *)
lemma subst_lemma1: "f \<sqsubseteq> g x \<Longrightarrow> x = h x \<Longrightarrow> f \<sqsubseteq> g (h x)"
  by (erule subst)

(* Lemma for substitution of looping assumption in another specific assumption *)
lemma subst_lemma2: "(f x) = y \<leadsto> g \<Longrightarrow> x = h x \<Longrightarrow> f (h x) = y \<leadsto> g"
  by (erule subst)

lemma ForallAorB_mksch [rule_format]:
  "compatible A B \<Longrightarrow>
    \<forall>schA schB. Forall (\<lambda>x. x \<in> act (A \<parallel> B)) tr \<longrightarrow>
      Forall (\<lambda>x. x \<in> act (A \<parallel> B)) (mksch A B \<cdot> tr \<cdot> schA \<cdot> schB)"
  apply (Seq_induct tr simp: Forall_def sforall_def mksch_def)
  apply auto
  apply (simp add: actions_of_par)
  apply (case_tac "a \<in> act A")
  apply (case_tac "a \<in> act B")
  text \<open>\<open>a \<in> A\<close>, \<open>a \<in> B\<close>\<close>
  apply simp
  apply (rule Forall_Conc_impl [THEN mp])
  apply (simp add: intA_is_not_actB int_is_act)
  apply (rule Forall_Conc_impl [THEN mp])
  apply (simp add: intA_is_not_actB int_is_act)
  text \<open>\<open>a \<in> A\<close>, \<open>a \<notin> B\<close>\<close>
  apply simp
  apply (rule Forall_Conc_impl [THEN mp])
  apply (simp add: intA_is_not_actB int_is_act)
  apply (case_tac "a\<in>act B")
  text \<open>\<open>a \<notin> A\<close>, \<open>a \<in> B\<close>\<close>
  apply simp
  apply (rule Forall_Conc_impl [THEN mp])
  apply (simp add: intA_is_not_actB int_is_act)
  text \<open>\<open>a \<notin> A\<close>, \<open>a \<notin> B\<close>\<close>
  apply auto
  done

lemma ForallBnAmksch [rule_format]:
  "compatible B A \<Longrightarrow>
    \<forall>schA schB. Forall (\<lambda>x. x \<in> act B \<and> x \<notin> act A) tr \<longrightarrow>
      Forall (\<lambda>x. x \<in> act B \<and> x \<notin> act A) (mksch A B \<cdot> tr \<cdot> schA \<cdot> schB)"
  apply (Seq_induct tr simp: Forall_def sforall_def mksch_def)
  apply auto
  apply (rule Forall_Conc_impl [THEN mp])
  apply (simp add: intA_is_not_actB int_is_act)
  done

lemma ForallAnBmksch [rule_format]:
  "compatible A B \<Longrightarrow>
    \<forall>schA schB. Forall (\<lambda>x. x \<in> act A \<and> x \<notin> act B) tr \<longrightarrow>
      Forall (\<lambda>x. x \<in> act A \<and> x \<notin> act B) (mksch A B \<cdot> tr \<cdot> schA \<cdot> schB)"
  apply (Seq_induct tr simp: Forall_def sforall_def mksch_def)
  apply auto
  apply (rule Forall_Conc_impl [THEN mp])
  apply (simp add: intA_is_not_actB int_is_act)
  done

(* safe_tac makes too many case distinctions with this lemma in the next proof *)
declare FiniteConc [simp del]

lemma FiniteL_mksch [rule_format]:
  "Finite tr \<Longrightarrow> is_asig (asig_of A) \<Longrightarrow> is_asig (asig_of B) \<Longrightarrow>
    \<forall>x y.
      Forall (\<lambda>x. x \<in> act A) x \<and> Forall (\<lambda>x. x \<in> act B) y \<and>
      Filter (\<lambda>a. a \<in> ext A) \<cdot> x = Filter (\<lambda>a. a \<in> act A) \<cdot> tr \<and>
      Filter (\<lambda>a. a \<in> ext B) \<cdot> y = Filter (\<lambda>a. a \<in> act B) \<cdot> tr \<and>
      Forall (\<lambda>x. x \<in> ext (A \<parallel> B)) tr \<longrightarrow> Finite (mksch A B \<cdot> tr \<cdot> x \<cdot> y)"
  apply (erule Seq_Finite_ind)
  apply simp
  text \<open>main case\<close>
  apply simp
  apply auto

  text \<open>\<open>a \<in> act A\<close>; \<open>a \<in> act B\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
  back
  apply (erule conjE)+
  text \<open>\<open>Finite (tw iA x)\<close> and \<open>Finite (tw iB y)\<close>\<close>
  apply (simp add: not_ext_is_int_or_not_act FiniteConc)
  text \<open>now for conclusion IH applicable, but assumptions have to be transformed\<close>
  apply (drule_tac x = "x" and g = "Filter (\<lambda>a. a \<in> act A) \<cdot> s" in subst_lemma2)
  apply assumption
  apply (drule_tac x = "y" and g = "Filter (\<lambda>a. a \<in> act B) \<cdot> s" in subst_lemma2)
  apply assumption
  text \<open>IH\<close>
  apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

  text \<open>\<open>a \<in> act B\<close>; \<open>a \<notin> act A\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])

  apply (erule conjE)+
  text \<open>\<open>Finite (tw iB y)\<close>\<close>
  apply (simp add: not_ext_is_int_or_not_act FiniteConc)
  text \<open>now for conclusion IH applicable, but assumptions have to be transformed\<close>
  apply (drule_tac x = "y" and g = "Filter (\<lambda>a. a \<in> act B) \<cdot> s" in subst_lemma2)
  apply assumption
  text \<open>IH\<close>
  apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

  text \<open>\<open>a \<notin> act B\<close>; \<open>a \<in> act A\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])

  apply (erule conjE)+
  text \<open>\<open>Finite (tw iA x)\<close>\<close>
  apply (simp add: not_ext_is_int_or_not_act FiniteConc)
  text \<open>now for conclusion IH applicable, but assumptions have to be transformed\<close>
  apply (drule_tac x = "x" and g = "Filter (\<lambda>a. a \<in> act A) \<cdot> s" in subst_lemma2)
  apply assumption
  text \<open>IH\<close>
  apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

  text \<open>\<open>a \<notin> act B\<close>; \<open>a \<notin> act A\<close>\<close>
  apply (fastforce intro!: ext_is_act simp: externals_of_par)
  done

declare FiniteConc [simp]

declare FilterConc [simp del]

lemma reduceA_mksch1 [rule_format]:
  "Finite bs \<Longrightarrow> is_asig (asig_of A) \<Longrightarrow> is_asig (asig_of B) \<Longrightarrow> compatible A B \<Longrightarrow>
    \<forall>y. Forall (\<lambda>x. x \<in> act B) y \<and> Forall (\<lambda>x. x \<in> act B \<and> x \<notin> act A) bs \<and>
      Filter (\<lambda>a. a \<in> ext B) \<cdot> y = Filter (\<lambda>a. a \<in> act B) \<cdot> (bs @@ z) \<longrightarrow>
      (\<exists>y1 y2.
        (mksch A B \<cdot> (bs @@ z) \<cdot> x \<cdot> y) = (y1 @@ (mksch A B \<cdot> z \<cdot> x \<cdot> y2)) \<and>
        Forall (\<lambda>x. x \<in> act B \<and> x \<notin> act A) y1 \<and>
        Finite y1 \<and> y = (y1 @@ y2) \<and>
        Filter (\<lambda>a. a \<in> ext B) \<cdot> y1 = bs)"
  apply (frule_tac A1 = "A" in compat_commute [THEN iffD1])
  apply (erule Seq_Finite_ind)
  apply (rule allI)+
  apply (rule impI)
  apply (rule_tac x = "nil" in exI)
  apply (rule_tac x = "y" in exI)
  apply simp
  text \<open>main case\<close>
  apply (rule allI)+
  apply (rule impI)
  apply simp
  apply (erule conjE)+
  apply simp
  text \<open>\<open>divide_Seq\<close> on \<open>s\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
  apply (erule conjE)+
  text \<open>transform assumption \<open>f eB y = f B (s @ z)\<close>\<close>
  apply (drule_tac x = "y" and g = "Filter (\<lambda>a. a \<in> act B) \<cdot> (s @@ z) " in subst_lemma2)
  apply assumption
  apply (simp add: not_ext_is_int_or_not_act FilterConc)
  text \<open>apply IH\<close>
  apply (erule_tac x = "TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int B) \<cdot> y)" in allE)
  apply (simp add: ForallTL ForallDropwhile FilterConc)
  apply (erule exE)+
  apply (erule conjE)+
  apply (simp add: FilterConc)
  text \<open>for replacing IH in conclusion\<close>
  apply (rotate_tac -2)
  text \<open>instantiate \<open>y1a\<close> and \<open>y2a\<close>\<close>
  apply (rule_tac x = "Takewhile (\<lambda>a. a \<in> int B) \<cdot> y @@ a \<leadsto> y1" in exI)
  apply (rule_tac x = "y2" in exI)
  text \<open>elminate all obligations up to two depending on \<open>Conc_assoc\<close>\<close>
  apply (simp add: intA_is_not_actB int_is_act int_is_not_ext FilterConc)
  apply (simp add: Conc_assoc FilterConc)
  done

lemmas reduceA_mksch = conjI [THEN [6] conjI [THEN [5] reduceA_mksch1]]

lemma reduceB_mksch1 [rule_format]:
  "Finite a_s \<Longrightarrow> is_asig (asig_of A) \<Longrightarrow> is_asig (asig_of B) \<Longrightarrow> compatible A B \<Longrightarrow>
    \<forall>x. Forall (\<lambda>x. x \<in> act A) x \<and> Forall (\<lambda>x. x \<in> act A \<and> x \<notin> act B) a_s \<and>
      Filter (\<lambda>a. a \<in> ext A) \<cdot> x = Filter (\<lambda>a. a \<in> act A) \<cdot> (a_s @@ z) \<longrightarrow>
      (\<exists>x1 x2.
        (mksch A B \<cdot> (a_s @@ z) \<cdot> x \<cdot> y) = (x1 @@ (mksch A B \<cdot> z \<cdot> x2 \<cdot> y)) \<and>
        Forall (\<lambda>x. x \<in> act A \<and> x \<notin> act B) x1 \<and>
        Finite x1 \<and> x = (x1 @@ x2) \<and>
        Filter (\<lambda>a. a \<in> ext A) \<cdot> x1 = a_s)"
  apply (frule_tac A1 = "A" in compat_commute [THEN iffD1])
  apply (erule Seq_Finite_ind)
  apply (rule allI)+
  apply (rule impI)
  apply (rule_tac x = "nil" in exI)
  apply (rule_tac x = "x" in exI)
  apply simp
  text \<open>main case\<close>
  apply (rule allI)+
  apply (rule impI)
  apply simp
  apply (erule conjE)+
  apply simp
  text \<open>\<open>divide_Seq\<close> on \<open>s\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
  apply (erule conjE)+
  text \<open>transform assumption \<open>f eA x = f A (s @ z)\<close>\<close>
  apply (drule_tac x = "x" and g = "Filter (\<lambda>a. a \<in> act A) \<cdot> (s @@ z)" in subst_lemma2)
  apply assumption
  apply (simp add: not_ext_is_int_or_not_act FilterConc)
  text \<open>apply IH\<close>
  apply (erule_tac x = "TL \<cdot> (Dropwhile (\<lambda>a. a \<in> int A) \<cdot> x)" in allE)
  apply (simp add: ForallTL ForallDropwhile FilterConc)
  apply (erule exE)+
  apply (erule conjE)+
  apply (simp add: FilterConc)
  text \<open>for replacing IH in conclusion\<close>
  apply (rotate_tac -2)
  text \<open>instantiate \<open>y1a\<close> and \<open>y2a\<close>\<close>
  apply (rule_tac x = "Takewhile (\<lambda>a. a \<in> int A) \<cdot> x @@ a \<leadsto> x1" in exI)
  apply (rule_tac x = "x2" in exI)
  text \<open>eliminate all obligations up to two depending on \<open>Conc_assoc\<close>\<close>
  apply (simp add: intA_is_not_actB int_is_act int_is_not_ext FilterConc)
  apply (simp add: Conc_assoc FilterConc)
  done

lemmas reduceB_mksch = conjI [THEN [6] conjI [THEN [5] reduceB_mksch1]]

declare FilterConc [simp]


subsection \<open>Filtering external actions out of \<open>mksch (tr, schA, schB)\<close> yields the oracle \<open>tr\<close>\<close>

lemma FilterA_mksch_is_tr:
  "compatible A B \<Longrightarrow> compatible B A \<Longrightarrow> is_asig (asig_of A) \<Longrightarrow> is_asig (asig_of B) \<Longrightarrow>
    \<forall>schA schB.
      Forall (\<lambda>x. x \<in> act A) schA \<and>
      Forall (\<lambda>x. x \<in> act B) schB \<and>
      Forall (\<lambda>x. x \<in> ext (A \<parallel> B)) tr \<and>
      Filter (\<lambda>a. a \<in> act A) \<cdot> tr \<sqsubseteq> Filter (\<lambda>a. a \<in> ext A) \<cdot> schA \<and>
      Filter (\<lambda>a. a \<in> act B) \<cdot> tr \<sqsubseteq> Filter (\<lambda>a. a \<in> ext B) \<cdot> schB
      \<longrightarrow> Filter (\<lambda>a. a \<in> ext (A \<parallel> B)) \<cdot> (mksch A B \<cdot> tr \<cdot> schA \<cdot> schB) = tr"
  apply (Seq_induct tr simp: Forall_def sforall_def mksch_def)
  text \<open>main case\<close>
  text \<open>splitting into 4 cases according to \<open>a \<in> A\<close>, \<open>a \<in> B\<close>\<close>
  apply auto

  text \<open>Case \<open>a \<in> A\<close>, \<open>a \<in> B\<close>\<close>
  apply (frule divide_Seq)
  apply (frule divide_Seq)
  back
  apply (erule conjE)+
  text \<open>filtering internals of \<open>A\<close> in \<open>schA\<close> and of \<open>B\<close> in \<open>schB\<close> is \<open>nil\<close>\<close>
  apply (simp add: not_ext_is_int_or_not_act externals_of_par intA_is_not_extB int_is_not_ext)
  text \<open>conclusion of IH ok, but assumptions of IH have to be transformed\<close>
  apply (drule_tac x = "schA" in subst_lemma1)
  apply assumption
  apply (drule_tac x = "schB" in subst_lemma1)
  apply assumption
  text \<open>IH\<close>
  apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

  text \<open>Case \<open>a \<in> A\<close>, \<open>a \<notin> B\<close>\<close>
  apply (frule divide_Seq)
  apply (erule conjE)+
  text \<open>filtering internals of \<open>A\<close> is \<open>nil\<close>\<close>
  apply (simp add: not_ext_is_int_or_not_act externals_of_par intA_is_not_extB int_is_not_ext)
  apply (drule_tac x = "schA" in subst_lemma1)
  apply assumption
  apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

  text \<open>Case \<open>a \<in> B\<close>, \<open>a \<notin> A\<close>\<close>
  apply (frule divide_Seq)
  apply (erule conjE)+
  text \<open>filtering internals of \<open>A\<close> is \<open>nil\<close>\<close>
  apply (simp add: not_ext_is_int_or_not_act externals_of_par intA_is_not_extB int_is_not_ext)
  apply (drule_tac x = "schB" in subst_lemma1)
  back
  apply assumption
  apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

  text \<open>Case \<open>a \<notin> A\<close>, \<open>a \<notin> B\<close>\<close>
  apply (fastforce intro!: ext_is_act simp: externals_of_par)
  done


subsection" Filter of mksch(tr,schA,schB) to A is schA -- take lemma proof"

lemma FilterAmksch_is_schA:
  "compatible A B \<Longrightarrow> compatible B A \<Longrightarrow> is_asig (asig_of A) \<Longrightarrow> is_asig (asig_of B) \<Longrightarrow>
    Forall (\<lambda>x. x \<in> ext (A \<parallel> B)) tr \<and>
    Forall (\<lambda>x. x \<in> act A) schA \<and>
    Forall (\<lambda>x. x \<in> act B) schB \<and>
    Filter (\<lambda>a. a \<in> ext A) \<cdot> schA = Filter (\<lambda>a. a \<in> act A) \<cdot> tr \<and>
    Filter (\<lambda>a. a \<in> ext B) \<cdot> schB = Filter (\<lambda>a. a \<in> act B) \<cdot> tr \<and>
    LastActExtsch A schA \<and> LastActExtsch B schB
    \<longrightarrow> Filter (\<lambda>a. a \<in> act A) \<cdot> (mksch A B \<cdot> tr \<cdot> schA \<cdot> schB) = schA"
  apply (intro strip)
  apply (rule seq.take_lemma)
  apply (rule mp)
  prefer 2 apply assumption
  back back back back
  apply (rule_tac x = "schA" in spec)
  apply (rule_tac x = "schB" in spec)
  apply (rule_tac x = "tr" in spec)
  apply (tactic "thin_tac' \<^context> 5 1")
  apply (rule nat_less_induct)
  apply (rule allI)+
  apply (rename_tac tr schB schA)
  apply (intro strip)
  apply (erule conjE)+

  apply (case_tac "Forall (\<lambda>x. x \<in> act B \<and> x \<notin> act A) tr")

  apply (rule seq_take_lemma [THEN iffD2, THEN spec])
  apply (tactic "thin_tac' \<^context> 5 1")


  apply (case_tac "Finite tr")

  text \<open>both sides of this equation are \<open>nil\<close>\<close>
  apply (subgoal_tac "schA = nil")
  apply simp
  text \<open>first side: \<open>mksch = nil\<close>\<close>
  apply (auto intro!: ForallQFilterPnil ForallBnAmksch FiniteL_mksch)[1]
  text \<open>second side: \<open>schA = nil\<close>\<close>
  apply (erule_tac A = "A" in LastActExtimplnil)
  apply simp
  apply (erule_tac Q = "\<lambda>x. x \<in> act B \<and> x \<notin> act A" in ForallQFilterPnil)
  apply assumption
  apply fast

  text \<open>case \<open>\<not> Finite s\<close>\<close>

  text \<open>both sides of this equation are \<open>UU\<close>\<close>
  apply (subgoal_tac "schA = UU")
  apply simp
  text \<open>first side: \<open>mksch = UU\<close>\<close>
  apply (auto intro!: ForallQFilterPUU finiteR_mksch' ForallBnAmksch)[1]
  text \<open>\<open>schA = UU\<close>\<close>
  apply (erule_tac A = "A" in LastActExtimplUU)
  apply simp
  apply (erule_tac Q = "\<lambda>x. x \<in> act B \<and> x \<notin> act A" in ForallQFilterPUU)
  apply assumption
  apply fast

  text \<open>case \<open>\<not> Forall (\<lambda>x. x \<in> act B \<and> x \<notin> act A) s\<close>\<close>

  apply (drule divide_Seq3)

  apply (erule exE)+
  apply (erule conjE)+
  apply hypsubst

  text \<open>bring in lemma \<open>reduceA_mksch\<close>\<close>
  apply (frule_tac x = "schA" and y = "schB" and A = "A" and B = "B" in reduceA_mksch)
  apply assumption+
  apply (erule exE)+
  apply (erule conjE)+

  text \<open>use \<open>reduceA_mksch\<close> to rewrite conclusion\<close>
  apply hypsubst
  apply simp

  text \<open>eliminate the \<open>B\<close>-only prefix\<close>

  apply (subgoal_tac "(Filter (\<lambda>a. a \<in> act A) \<cdot> y1) = nil")
  apply (erule_tac [2] ForallQFilterPnil)
  prefer 2 apply assumption
  prefer 2 apply fast

  text \<open>Now real recursive step follows (in \<open>y\<close>)\<close>

  apply simp
  apply (case_tac "x \<in> act A")
  apply (case_tac "x \<notin> act B")
  apply (rotate_tac -2)
  apply simp

  apply (subgoal_tac "Filter (\<lambda>a. a \<in> act A \<and> a \<in> ext B) \<cdot> y1 = nil")
  apply (rotate_tac -1)
  apply simp
  text \<open>eliminate introduced subgoal 2\<close>
  apply (erule_tac [2] ForallQFilterPnil)
  prefer 2 apply assumption
  prefer 2 apply fast

  text \<open>bring in \<open>divide_Seq\<close> for \<open>s\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
  apply (erule conjE)+

  text \<open>subst \<open>divide_Seq\<close> in conclusion, but only at the rightest occurrence\<close>
  apply (rule_tac t = "schA" in ssubst)
  back
  back
  back
  apply assumption

  text \<open>reduce trace_takes from \<open>n\<close> to strictly smaller \<open>k\<close>\<close>
  apply (rule take_reduction)

  text \<open>\<open>f A (tw iA) = tw \<not> eA\<close>\<close>
  apply (simp add: int_is_act not_ext_is_int_or_not_act)
  apply (rule refl)
  apply (simp add: int_is_act not_ext_is_int_or_not_act)
  apply (rotate_tac -11)

  text \<open>now conclusion fulfills induction hypothesis, but assumptions are not ready\<close>

  text \<open>assumption \<open>Forall tr\<close>\<close>
  text \<open>assumption \<open>schB\<close>\<close>
  apply (simp add: ext_and_act)
  text \<open>assumption \<open>schA\<close>\<close>
  apply (drule_tac x = "schA" and g = "Filter (\<lambda>a. a \<in> act A) \<cdot> rs" in subst_lemma2)
  apply assumption
  apply (simp add: int_is_not_ext)
  text \<open>assumptions concerning \<open>LastActExtsch\<close>, cannot be rewritten, as \<open>LastActExtsmalli\<close> are looping\<close>
  apply (drule_tac sch = "schA" and P = "\<lambda>a. a \<in> int A" in LastActExtsmall1)
  apply (frule_tac ?sch1.0 = "y1" in LastActExtsmall2)
  apply assumption

  text \<open>assumption \<open>Forall schA\<close>\<close>
  apply (drule_tac s = "schA" and P = "Forall (\<lambda>x. x \<in> act A) " in subst)
  apply assumption
  apply (simp add: int_is_act)

  text \<open>case \<open>x \<in> actions (asig_of A) \<and> x \<in> actions (asig_of B)\<close>\<close>

  apply (rotate_tac -2)
  apply simp

  apply (subgoal_tac "Filter (\<lambda>a. a \<in> act A \<and> a \<in> ext B) \<cdot> y1 = nil")
  apply (rotate_tac -1)
  apply simp
  text \<open>eliminate introduced subgoal 2\<close>
  apply (erule_tac [2] ForallQFilterPnil)
  prefer 2 apply assumption
  prefer 2 apply fast

  text \<open>bring in \<open>divide_Seq\<close> for \<open>s\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
  apply (erule conjE)+

  text \<open>subst \<open>divide_Seq\<close> in conclusion, but only at the rightmost occurrence\<close>
  apply (rule_tac t = "schA" in ssubst)
  back
  back
  back
  apply assumption

  text \<open>\<open>f A (tw iA) = tw \<not> eA\<close>\<close>
  apply (simp add: int_is_act not_ext_is_int_or_not_act)

  text \<open>rewrite assumption forall and \<open>schB\<close>\<close>
  apply (rotate_tac 13)
  apply (simp add: ext_and_act)

  text \<open>\<open>divide_Seq\<close> for \<open>schB2\<close>\<close>
  apply (frule_tac y = "y2" in sym [THEN eq_imp_below, THEN divide_Seq])
  apply (erule conjE)+
  text \<open>assumption \<open>schA\<close>\<close>
  apply (drule_tac x = "schA" and g = "Filter (\<lambda>a. a\<in>act A) \<cdot>rs" in subst_lemma2)
  apply assumption
  apply (simp add: int_is_not_ext)

  text \<open>\<open>f A (tw iB schB2) = nil\<close>\<close>
  apply (simp add: int_is_not_ext not_ext_is_int_or_not_act intA_is_not_actB)


  text \<open>reduce trace_takes from \<open>n\<close> to strictly smaller \<open>k\<close>\<close>
  apply (rule take_reduction)
  apply (rule refl)
  apply (rule refl)

  text \<open>now conclusion fulfills induction hypothesis, but assumptions are not all ready\<close>

  text \<open>assumption \<open>schB\<close>\<close>
  apply (drule_tac x = "y2" and g = "Filter (\<lambda>a. a \<in> act B) \<cdot> rs" in subst_lemma2)
  apply assumption
  apply (simp add: intA_is_not_actB int_is_not_ext)

  text \<open>conclusions concerning \<open>LastActExtsch\<close>, cannot be rewritten, as \<open>LastActExtsmalli\<close> are looping\<close>
  apply (drule_tac sch = "schA" and P = "\<lambda>a. a \<in> int A" in LastActExtsmall1)
  apply (frule_tac ?sch1.0 = "y1" in LastActExtsmall2)
  apply assumption
  apply (drule_tac sch = "y2" and P = "\<lambda>a. a \<in> int B" in LastActExtsmall1)

  text \<open>assumption \<open>Forall schA\<close>, and \<open>Forall schA\<close> are performed by \<open>ForallTL\<close>, \<open>ForallDropwhile\<close>\<close>
  apply (simp add: ForallTL ForallDropwhile)

  text \<open>case \<open>x \<notin> A \<and> x \<in> B\<close>\<close>
  text \<open>cannot occur, as just this case has been scheduled out before as the \<open>B\<close>-only prefix\<close>
  apply (case_tac "x \<in> act B")
  apply fast

  text \<open>case \<open>x \<notin> A \<and> x \<notin> B\<close>\<close>
  text \<open>cannot occur because of assumption: \<open>Forall (a \<in> ext A \<or> a \<in> ext B)\<close>\<close>
  apply (rotate_tac -9)
  text \<open>reduce forall assumption from \<open>tr\<close> to \<open>x \<leadsto> rs\<close>\<close>
  apply (simp add: externals_of_par)
  apply (fast intro!: ext_is_act)
  done


subsection \<open>Filter of \<open>mksch (tr, schA, schB)\<close> to \<open>B\<close> is \<open>schB\<close> -- take lemma proof\<close>

lemma FilterBmksch_is_schB:
  "compatible A B \<Longrightarrow> compatible B A \<Longrightarrow> is_asig (asig_of A) \<Longrightarrow> is_asig (asig_of B) \<Longrightarrow>
    Forall (\<lambda>x. x \<in> ext (A \<parallel> B)) tr \<and>
    Forall (\<lambda>x. x \<in> act A) schA \<and>
    Forall (\<lambda>x. x \<in> act B) schB \<and>
    Filter (\<lambda>a. a \<in> ext A) \<cdot> schA = Filter (\<lambda>a. a \<in> act A) \<cdot> tr \<and>
    Filter (\<lambda>a. a \<in> ext B) \<cdot> schB = Filter (\<lambda>a. a \<in> act B) \<cdot> tr \<and>
    LastActExtsch A schA \<and> LastActExtsch B schB
    \<longrightarrow> Filter (\<lambda>a. a \<in> act B) \<cdot> (mksch A B \<cdot> tr \<cdot> schA \<cdot> schB) = schB"
  apply (intro strip)
  apply (rule seq.take_lemma)
  apply (rule mp)
  prefer 2 apply assumption
  back back back back
  apply (rule_tac x = "schA" in spec)
  apply (rule_tac x = "schB" in spec)
  apply (rule_tac x = "tr" in spec)
  apply (tactic "thin_tac' \<^context> 5 1")
  apply (rule nat_less_induct)
  apply (rule allI)+
  apply (rename_tac tr schB schA)
  apply (intro strip)
  apply (erule conjE)+

  apply (case_tac "Forall (\<lambda>x. x \<in> act A \<and> x \<notin> act B) tr")

  apply (rule seq_take_lemma [THEN iffD2, THEN spec])
  apply (tactic "thin_tac' \<^context> 5 1")

  apply (case_tac "Finite tr")

  text \<open>both sides of this equation are \<open>nil\<close>\<close>
  apply (subgoal_tac "schB = nil")
  apply simp
  text \<open>first side: \<open>mksch = nil\<close>\<close>
  apply (auto intro!: ForallQFilterPnil ForallAnBmksch FiniteL_mksch)[1]
  text \<open>second side: \<open>schA = nil\<close>\<close>
  apply (erule_tac A = "B" in LastActExtimplnil)
  apply (simp (no_asm_simp))
  apply (erule_tac Q = "\<lambda>x. x \<in> act A \<and> x \<notin> act B" in ForallQFilterPnil)
  apply assumption
  apply fast

  text \<open>case \<open>\<not> Finite tr\<close>\<close>

  text \<open>both sides of this equation are \<open>UU\<close>\<close>
  apply (subgoal_tac "schB = UU")
  apply simp
  text \<open>first side: \<open>mksch = UU\<close>\<close>
  apply (force intro!: ForallQFilterPUU finiteR_mksch' ForallAnBmksch)
  text \<open>\<open>schA = UU\<close>\<close>
  apply (erule_tac A = "B" in LastActExtimplUU)
  apply simp
  apply (erule_tac Q = "\<lambda>x. x \<in> act A \<and> x \<notin> act B" in ForallQFilterPUU)
  apply assumption
  apply fast

  text \<open>case \<open>\<not> Forall (\<lambda>x. x \<in> act B \<and> x \<notin> act A) s\<close>\<close>

  apply (drule divide_Seq3)

  apply (erule exE)+
  apply (erule conjE)+
  apply hypsubst

  text \<open>bring in lemma \<open>reduceB_mksch\<close>\<close>
  apply (frule_tac y = "schB" and x = "schA" and A = "A" and B = "B" in reduceB_mksch)
  apply assumption+
  apply (erule exE)+
  apply (erule conjE)+

  text \<open>use \<open>reduceB_mksch\<close> to rewrite conclusion\<close>
  apply hypsubst
  apply simp

  text \<open>eliminate the \<open>A\<close>-only prefix\<close>

  apply (subgoal_tac "(Filter (\<lambda>a. a \<in> act B) \<cdot> x1) = nil")
  apply (erule_tac [2] ForallQFilterPnil)
  prefer 2 apply (assumption)
  prefer 2 apply (fast)

  text \<open>Now real recursive step follows (in \<open>x\<close>)\<close>

  apply simp
  apply (case_tac "x \<in> act B")
  apply (case_tac "x \<notin> act A")
  apply (rotate_tac -2)
  apply simp

  apply (subgoal_tac "Filter (\<lambda>a. a \<in> act B \<and> a \<in> ext A) \<cdot> x1 = nil")
  apply (rotate_tac -1)
  apply simp
  text \<open>eliminate introduced subgoal 2\<close>
  apply (erule_tac [2] ForallQFilterPnil)
  prefer 2 apply assumption
  prefer 2 apply fast

  text \<open>bring in \<open>divide_Seq\<close> for \<open>s\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
  apply (erule conjE)+

  text \<open>subst \<open>divide_Seq\<close> in conclusion, but only at the rightmost occurrence\<close>
  apply (rule_tac t = "schB" in ssubst)
  back
  back
  back
  apply assumption

  text \<open>reduce \<open>trace_takes\<close> from \<open>n\<close> to strictly smaller \<open>k\<close>\<close>
  apply (rule take_reduction)

  text \<open>\<open>f B (tw iB) = tw \<not> eB\<close>\<close>
  apply (simp add: int_is_act not_ext_is_int_or_not_act)
  apply (rule refl)
  apply (simp add: int_is_act not_ext_is_int_or_not_act)
  apply (rotate_tac -11)

  text \<open>now conclusion fulfills induction hypothesis, but assumptions are not ready\<close>

  text \<open>assumption \<open>schA\<close>\<close>
  apply (simp add: ext_and_act)
  text \<open>assumption \<open>schB\<close>\<close>
  apply (drule_tac x = "schB" and g = "Filter (\<lambda>a. a \<in> act B) \<cdot> rs" in subst_lemma2)
  apply assumption
  apply (simp add: int_is_not_ext)
  text \<open>assumptions concerning \<open>LastActExtsch\<close>, cannot be rewritten, as \<open>LastActExtsmalli\<close> are looping\<close>
  apply (drule_tac sch = "schB" and P = "\<lambda>a. a \<in> int B" in LastActExtsmall1)
  apply (frule_tac ?sch1.0 = "x1" in LastActExtsmall2)
  apply assumption

  text \<open>assumption \<open>Forall schB\<close>\<close>
  apply (drule_tac s = "schB" and P = "Forall (\<lambda>x. x \<in> act B)" in subst)
  apply assumption
  apply (simp add: int_is_act)

  text \<open>case \<open>x \<in> actions (asig_of A) \<and> x \<in> actions (asig_of B)\<close>\<close>

  apply (rotate_tac -2)
  apply simp

  apply (subgoal_tac "Filter (\<lambda>a. a \<in> act B \<and> a \<in> ext A) \<cdot> x1 = nil")
  apply (rotate_tac -1)
  apply simp
  text \<open>eliminate introduced subgoal 2\<close>
  apply (erule_tac [2] ForallQFilterPnil)
  prefer 2 apply assumption
  prefer 2 apply fast

  text \<open>bring in \<open>divide_Seq\<close> for \<open>s\<close>\<close>
  apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
  apply (erule conjE)+

  text \<open>subst \<open>divide_Seq\<close> in conclusion, but only at the rightmost occurrence\<close>
  apply (rule_tac t = "schB" in ssubst)
  back
  back
  back
  apply assumption

  text \<open>\<open>f B (tw iB) = tw \<not> eB\<close>\<close>
  apply (simp add: int_is_act not_ext_is_int_or_not_act)

  text \<open>rewrite assumption forall and \<open>schB\<close>\<close>
  apply (rotate_tac 13)
  apply (simp add: ext_and_act)

  text \<open>\<open>divide_Seq\<close> for \<open>schB2\<close>\<close>
  apply (frule_tac y = "x2" in sym [THEN eq_imp_below, THEN divide_Seq])
  apply (erule conjE)+
  text \<open>assumption \<open>schA\<close>\<close>
  apply (drule_tac x = "schB" and g = "Filter (\<lambda>a. a \<in> act B) \<cdot> rs" in subst_lemma2)
  apply assumption
  apply (simp add: int_is_not_ext)

  text \<open>\<open>f B (tw iA schA2) = nil\<close>\<close>
  apply (simp add: int_is_not_ext not_ext_is_int_or_not_act intA_is_not_actB)


  text \<open>reduce \<open>trace_takes from \<open>n\<close> to strictly smaller \<open>k\<close>\<close>\<close>
  apply (rule take_reduction)
  apply (rule refl)
  apply (rule refl)

  text \<open>now conclusion fulfills induction hypothesis, but assumptions are not all ready\<close>

  text \<open>assumption \<open>schA\<close>\<close>
  apply (drule_tac x = "x2" and g = "Filter (\<lambda>a. a \<in> act A) \<cdot> rs" in subst_lemma2)
  apply assumption
  apply (simp add: intA_is_not_actB int_is_not_ext)

  text \<open>conclusions concerning \<open>LastActExtsch\<close>, cannot be rewritten, as \<open>LastActExtsmalli\<close> are looping\<close>
  apply (drule_tac sch = "schB" and P = "\<lambda>a. a\<in>int B" in LastActExtsmall1)
  apply (frule_tac ?sch1.0 = "x1" in LastActExtsmall2)
  apply assumption
  apply (drule_tac sch = "x2" and P = "\<lambda>a. a\<in>int A" in LastActExtsmall1)

  text \<open>assumption \<open>Forall schA\<close>, and \<open>Forall schA\<close> are performed by \<open>ForallTL\<close>, \<open>ForallDropwhile\<close>\<close>
  apply (simp add: ForallTL ForallDropwhile)

  text \<open>case \<open>x \<notin> B \<and> x \<in> A\<close>\<close>
  text \<open>cannot occur, as just this case has been scheduled out before as the \<open>B\<close>-only prefix\<close>
  apply (case_tac "x \<in> act A")
  apply fast

  text \<open>case \<open>x \<notin> B \<and> x \<notin> A\<close>\<close>
  text \<open>cannot occur because of assumption: \<open>Forall (a \<in> ext A \<or> a \<in> ext B)\<close>\<close>
  apply (rotate_tac -9)
  text \<open>reduce forall assumption from \<open>tr\<close> to \<open>x \<leadsto> rs\<close>\<close>
  apply (simp add: externals_of_par)
  apply (fast intro!: ext_is_act)
  done


subsection "COMPOSITIONALITY on TRACE Level -- Main Theorem"

theorem compositionality_tr:
  "is_trans_of A \<Longrightarrow> is_trans_of B \<Longrightarrow> compatible A B \<Longrightarrow> compatible B A \<Longrightarrow>
    is_asig (asig_of A) \<Longrightarrow> is_asig (asig_of B) \<Longrightarrow>
    tr \<in> traces (A \<parallel> B) \<longleftrightarrow>
      Filter (\<lambda>a. a \<in> act A) \<cdot> tr \<in> traces A \<and>
      Filter (\<lambda>a. a \<in> act B) \<cdot> tr \<in> traces B \<and>
      Forall (\<lambda>x. x \<in> ext(A \<parallel> B)) tr"
  apply (simp add: traces_def has_trace_def)
  apply auto

  text \<open>\<open>\<Longrightarrow>\<close>\<close>
  text \<open>There is a schedule of \<open>A\<close>\<close>
  apply (rule_tac x = "Filter (\<lambda>a. a \<in> act A) \<cdot> sch" in bexI)
  prefer 2
  apply (simp add: compositionality_sch)
  apply (simp add: compatibility_consequence1 externals_of_par ext1_ext2_is_not_act1)
  text \<open>There is a schedule of \<open>B\<close>\<close>
  apply (rule_tac x = "Filter (\<lambda>a. a \<in> act B) \<cdot> sch" in bexI)
  prefer 2
  apply (simp add: compositionality_sch)
  apply (simp add: compatibility_consequence2 externals_of_par ext1_ext2_is_not_act2)
  text \<open>Traces of \<open>A \<parallel> B\<close> have only external actions from \<open>A\<close> or \<open>B\<close>\<close>
  apply (rule ForallPFilterP)

  text \<open>\<open>\<Longleftarrow>\<close>\<close>

  text \<open>replace \<open>schA\<close> and \<open>schB\<close> by \<open>Cut schA\<close> and \<open>Cut schB\<close>\<close>
  apply (drule exists_LastActExtsch)
  apply assumption
  apply (drule exists_LastActExtsch)
  apply assumption
  apply (erule exE)+
  apply (erule conjE)+
  text \<open>Schedules of A(B) have only actions of A(B)\<close>
  apply (drule scheds_in_sig)
  apply assumption
  apply (drule scheds_in_sig)
  apply assumption

  apply (rename_tac h1 h2 schA schB)
  text \<open>\<open>mksch\<close> is exactly the construction of \<open>trA\<parallel>B\<close> out of \<open>schA\<close>, \<open>schB\<close>, and the oracle \<open>tr\<close>,
     we need here\<close>
  apply (rule_tac x = "mksch A B \<cdot> tr \<cdot> schA \<cdot> schB" in bexI)

  text \<open>External actions of mksch are just the oracle\<close>
  apply (simp add: FilterA_mksch_is_tr)

  text \<open>\<open>mksch\<close> is a schedule -- use compositionality on sch-level\<close>
  apply (simp add: compositionality_sch)
  apply (simp add: FilterAmksch_is_schA FilterBmksch_is_schB)
  apply (erule ForallAorB_mksch)
  apply (erule ForallPForallQ)
  apply (erule ext_is_act)
  done



subsection \<open>COMPOSITIONALITY on TRACE Level -- for Modules\<close>

lemma compositionality_tr_modules:
  "is_trans_of A \<Longrightarrow> is_trans_of B \<Longrightarrow> compatible A B \<Longrightarrow> compatible B A \<Longrightarrow>
    is_asig(asig_of A) \<Longrightarrow> is_asig(asig_of B) \<Longrightarrow>
    Traces (A\<parallel>B) = par_traces (Traces A) (Traces B)"
  apply (unfold Traces_def par_traces_def)
  apply (simp add: asig_of_par)
  apply (rule set_eqI)
  apply (simp add: compositionality_tr externals_of_par)
  done


declaration \<open>K (Simplifier.map_simpset (Simplifier.set_mksym Simplifier.default_mk_sym))\<close>

end
