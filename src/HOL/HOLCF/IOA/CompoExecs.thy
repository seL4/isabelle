(*  Title:      HOL/HOLCF/IOA/CompoExecs.thy
    Author:     Olaf Müller
*)

section \<open>Compositionality on Execution level\<close>

theory CompoExecs
imports Traces
begin

definition ProjA2 :: "('a, 's \<times> 't) pairs \<rightarrow> ('a, 's) pairs"
  where "ProjA2 = Map (\<lambda>x. (fst x, fst (snd x)))"

definition ProjA :: "('a, 's \<times> 't) execution \<Rightarrow> ('a, 's) execution"
  where "ProjA ex = (fst (fst ex), ProjA2 \<cdot> (snd ex))"

definition ProjB2 :: "('a, 's \<times> 't) pairs \<rightarrow> ('a, 't) pairs"
  where "ProjB2 = Map (\<lambda>x. (fst x, snd (snd x)))"

definition ProjB :: "('a, 's \<times> 't) execution \<Rightarrow> ('a, 't) execution"
  where "ProjB ex = (snd (fst ex), ProjB2 \<cdot> (snd ex))"

definition Filter_ex2 :: "'a signature \<Rightarrow> ('a, 's) pairs \<rightarrow> ('a, 's) pairs"
  where "Filter_ex2 sig = Filter (\<lambda>x. fst x \<in> actions sig)"

definition Filter_ex :: "'a signature \<Rightarrow> ('a, 's) execution \<Rightarrow> ('a, 's) execution"
  where "Filter_ex sig ex = (fst ex, Filter_ex2 sig \<cdot> (snd ex))"

definition stutter2 :: "'a signature \<Rightarrow> ('a, 's) pairs \<rightarrow> ('s \<Rightarrow> tr)"
  where "stutter2 sig =
    (fix \<cdot>
      (LAM h ex.
        (\<lambda>s.
          case ex of
            nil \<Rightarrow> TT
          | x ## xs \<Rightarrow>
              (flift1
                (\<lambda>p.
                  (If Def (fst p \<notin> actions sig) then Def (s = snd p) else TT)
                  andalso (h\<cdot>xs) (snd p)) \<cdot> x))))"

definition stutter :: "'a signature \<Rightarrow> ('a, 's) execution \<Rightarrow> bool"
  where "stutter sig ex \<longleftrightarrow> (stutter2 sig \<cdot> (snd ex)) (fst ex) \<noteq> FF"

definition par_execs ::
  "('a, 's) execution_module \<Rightarrow> ('a, 't) execution_module \<Rightarrow> ('a, 's \<times> 't) execution_module"
  where "par_execs ExecsA ExecsB =
    (let
      exA = fst ExecsA; sigA = snd ExecsA;
      exB = fst ExecsB; sigB = snd ExecsB
     in
       ({ex. Filter_ex sigA (ProjA ex) \<in> exA} \<inter>
        {ex. Filter_ex sigB (ProjB ex) \<in> exB} \<inter>
        {ex. stutter sigA (ProjA ex)} \<inter>
        {ex. stutter sigB (ProjB ex)} \<inter>
        {ex. Forall (\<lambda>x. fst x \<in> actions sigA \<union> actions sigB) (snd ex)},
        asig_comp sigA sigB))"


lemmas [simp del] = split_paired_All


section \<open>Recursive equations of operators\<close>

subsection \<open>\<open>ProjA2\<close>\<close>

lemma ProjA2_UU: "ProjA2 \<cdot> UU = UU"
  by (simp add: ProjA2_def)

lemma ProjA2_nil: "ProjA2 \<cdot> nil = nil"
  by (simp add: ProjA2_def)

lemma ProjA2_cons: "ProjA2 \<cdot> ((a, t) \<leadsto> xs) = (a, fst t) \<leadsto> ProjA2 \<cdot> xs"
  by (simp add: ProjA2_def)


subsection \<open>\<open>ProjB2\<close>\<close>

lemma ProjB2_UU: "ProjB2 \<cdot> UU = UU"
  by (simp add: ProjB2_def)

lemma ProjB2_nil: "ProjB2 \<cdot> nil = nil"
  by (simp add: ProjB2_def)

lemma ProjB2_cons: "ProjB2 \<cdot> ((a, t) \<leadsto> xs) = (a, snd t) \<leadsto> ProjB2 \<cdot> xs"
  by (simp add: ProjB2_def)


subsection \<open>\<open>Filter_ex2\<close>\<close>

lemma Filter_ex2_UU: "Filter_ex2 sig \<cdot> UU = UU"
  by (simp add: Filter_ex2_def)

lemma Filter_ex2_nil: "Filter_ex2 sig \<cdot> nil = nil"
  by (simp add: Filter_ex2_def)

lemma Filter_ex2_cons:
  "Filter_ex2 sig \<cdot> (at \<leadsto> xs) =
    (if fst at \<in> actions sig
     then at \<leadsto> (Filter_ex2 sig \<cdot> xs)
     else Filter_ex2 sig \<cdot> xs)"
  by (simp add: Filter_ex2_def)


subsection \<open>\<open>stutter2\<close>\<close>

lemma stutter2_unfold:
  "stutter2 sig =
    (LAM ex.
      (\<lambda>s.
        case ex of
          nil \<Rightarrow> TT
        | x ## xs \<Rightarrow>
            (flift1
              (\<lambda>p.
                (If Def (fst p \<notin> actions sig) then Def (s= snd p) else TT)
                andalso (stutter2 sig\<cdot>xs) (snd p)) \<cdot> x)))"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (simp only: stutter2_def)
  apply (rule beta_cfun)
  apply (simp add: flift1_def)
  done

lemma stutter2_UU: "(stutter2 sig \<cdot> UU) s = UU"
  apply (subst stutter2_unfold)
  apply simp
  done

lemma stutter2_nil: "(stutter2 sig \<cdot> nil) s = TT"
  apply (subst stutter2_unfold)
  apply simp
  done

lemma stutter2_cons:
  "(stutter2 sig \<cdot> (at \<leadsto> xs)) s =
    ((if fst at \<notin> actions sig then Def (s = snd at) else TT)
      andalso (stutter2 sig \<cdot> xs) (snd at))"
  apply (rule trans)
  apply (subst stutter2_unfold)
  apply (simp add: Consq_def flift1_def If_and_if)
  apply simp
  done

declare stutter2_UU [simp] stutter2_nil [simp] stutter2_cons [simp]


subsection \<open>\<open>stutter\<close>\<close>

lemma stutter_UU: "stutter sig (s, UU)"
  by (simp add: stutter_def)

lemma stutter_nil: "stutter sig (s, nil)"
  by (simp add: stutter_def)

lemma stutter_cons:
  "stutter sig (s, (a, t) \<leadsto> ex) \<longleftrightarrow> (a \<notin> actions sig \<longrightarrow> (s = t)) \<and> stutter sig (t, ex)"
  by (simp add: stutter_def)

declare stutter2_UU [simp del] stutter2_nil [simp del] stutter2_cons [simp del]

lemmas compoex_simps = ProjA2_UU ProjA2_nil ProjA2_cons
  ProjB2_UU ProjB2_nil ProjB2_cons
  Filter_ex2_UU Filter_ex2_nil Filter_ex2_cons
  stutter_UU stutter_nil stutter_cons

declare compoex_simps [simp]


section \<open>Compositionality on execution level\<close>

lemma lemma_1_1a:
  \<comment> \<open>\<open>is_ex_fr\<close> propagates from \<open>A \<parallel> B\<close> to projections \<open>A\<close> and \<open>B\<close>\<close>
  "\<forall>s. is_exec_frag (A \<parallel> B) (s, xs) \<longrightarrow>
    is_exec_frag A (fst s, Filter_ex2 (asig_of A) \<cdot> (ProjA2 \<cdot> xs)) \<and>
    is_exec_frag B (snd s, Filter_ex2 (asig_of B) \<cdot> (ProjB2 \<cdot> xs))"
  apply (pair_induct xs simp: is_exec_frag_def)
  text \<open>main case\<close>
  apply (auto simp add: trans_of_defs2)
  done

lemma lemma_1_1b:
  \<comment> \<open>\<open>is_ex_fr (A \<parallel> B)\<close> implies stuttering on projections\<close>
  "\<forall>s. is_exec_frag (A \<parallel> B) (s, xs) \<longrightarrow>
    stutter (asig_of A) (fst s, ProjA2 \<cdot> xs) \<and>
    stutter (asig_of B) (snd s, ProjB2 \<cdot> xs)"
  apply (pair_induct xs simp: stutter_def is_exec_frag_def)
  text \<open>main case\<close>
  apply (auto simp add: trans_of_defs2)
  done

lemma lemma_1_1c:
  \<comment> \<open>Executions of \<open>A \<parallel> B\<close> have only \<open>A\<close>- or \<open>B\<close>-actions\<close>
  "\<forall>s. is_exec_frag (A \<parallel> B) (s, xs) \<longrightarrow> Forall (\<lambda>x. fst x \<in> act (A \<parallel> B)) xs"
  apply (pair_induct xs simp: Forall_def sforall_def is_exec_frag_def)
  text \<open>main case\<close>
  apply auto
  apply (simp add: trans_of_defs2 actions_asig_comp asig_of_par)
  done

lemma lemma_1_2:
  \<comment> \<open>\<open>ex A\<close>, \<open>exB\<close>, stuttering and forall \<open>a \<in> A \<parallel> B\<close> implies \<open>ex (A \<parallel> B)\<close>\<close>
  "\<forall>s.
    is_exec_frag A (fst s, Filter_ex2 (asig_of A) \<cdot> (ProjA2 \<cdot> xs)) \<and>
    is_exec_frag B (snd s, Filter_ex2 (asig_of B) \<cdot> (ProjB2 \<cdot> xs)) \<and>
    stutter (asig_of A) (fst s, ProjA2 \<cdot> xs) \<and>
    stutter (asig_of B) (snd s, ProjB2 \<cdot> xs) \<and>
    Forall (\<lambda>x. fst x \<in> act (A \<parallel> B)) xs \<longrightarrow>
    is_exec_frag (A \<parallel> B) (s, xs)"
  apply (pair_induct xs simp: Forall_def sforall_def is_exec_frag_def stutter_def)
  apply (auto simp add: trans_of_defs1 actions_asig_comp asig_of_par)
  done

theorem compositionality_ex:
  "ex \<in> executions (A \<parallel> B) \<longleftrightarrow>
    Filter_ex (asig_of A) (ProjA ex) \<in> executions A \<and>
    Filter_ex (asig_of B) (ProjB ex) \<in> executions B \<and>
    stutter (asig_of A) (ProjA ex) \<and>
    stutter (asig_of B) (ProjB ex) \<and>
    Forall (\<lambda>x. fst x \<in> act (A \<parallel> B)) (snd ex)"
  apply (simp add: executions_def ProjB_def Filter_ex_def ProjA_def starts_of_par)
  apply (pair ex)
  apply (rule iffI)
  text \<open>\<open>\<Longrightarrow>\<close>\<close>
  apply (erule conjE)+
  apply (simp add: lemma_1_1a lemma_1_1b lemma_1_1c)
  text \<open>\<open>\<Longleftarrow>\<close>\<close>
  apply (erule conjE)+
  apply (simp add: lemma_1_2)
  done

theorem compositionality_ex_modules: "Execs (A \<parallel> B) = par_execs (Execs A) (Execs B)"
  apply (unfold Execs_def par_execs_def)
  apply (simp add: asig_of_par)
  apply (rule set_eqI)
  apply (simp add: compositionality_ex actions_of_par)
  done

end
