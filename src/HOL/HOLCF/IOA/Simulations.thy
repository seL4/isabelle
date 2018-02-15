(*  Title:      HOL/HOLCF/IOA/Simulations.thy
    Author:     Olaf Müller
*)

section \<open>Simulations in HOLCF/IOA\<close>

theory Simulations
imports RefCorrectness
begin

default_sort type

definition is_simulation :: "('s1 \<times> 's2) set \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_simulation R C A \<longleftrightarrow>
    (\<forall>s \<in> starts_of C. R``{s} \<inter> starts_of A \<noteq> {}) \<and>
    (\<forall>s s' t a. reachable C s \<and> s \<midarrow>a\<midarrow>C\<rightarrow> t \<and> (s, s') \<in> R
      \<longrightarrow> (\<exists>t' ex. (t, t') \<in> R \<and> move A ex s' a t'))"

definition is_backward_simulation :: "('s1 \<times> 's2) set \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_backward_simulation R C A \<longleftrightarrow>
    (\<forall>s \<in> starts_of C. R``{s} \<subseteq> starts_of A) \<and>
    (\<forall>s t t' a. reachable C s \<and> s \<midarrow>a\<midarrow>C\<rightarrow> t \<and> (t, t') \<in> R
      \<longrightarrow> (\<exists>ex s'. (s,s') \<in> R \<and> move A ex s' a t'))"

definition is_forw_back_simulation ::
    "('s1 \<times> 's2 set) set \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_forw_back_simulation R C A \<longleftrightarrow>
    (\<forall>s \<in> starts_of C. \<exists>S'. (s, S') \<in> R \<and> S' \<subseteq> starts_of A) \<and>
    (\<forall>s S' t a. reachable C s \<and> s \<midarrow>a\<midarrow>C\<rightarrow> t \<and> (s, S') \<in> R
      \<longrightarrow> (\<exists>T'. (t, T') \<in> R \<and> (\<forall>t' \<in> T'. \<exists>s' \<in> S'. \<exists>ex. move A ex s' a t')))"

definition is_back_forw_simulation ::
    "('s1 \<times> 's2 set) set \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_back_forw_simulation R C A \<longleftrightarrow>
    ((\<forall>s \<in> starts_of C. \<forall>S'. (s, S') \<in> R \<longrightarrow> S' \<inter> starts_of A \<noteq> {}) \<and>
    (\<forall>s t T' a. reachable C s \<and> s \<midarrow>a\<midarrow>C\<rightarrow> t \<and> (t, T') \<in> R
      \<longrightarrow> (\<exists>S'. (s, S') \<in> R \<and> (\<forall>s' \<in> S'. \<exists>t' \<in> T'. \<exists>ex. move A ex s' a t'))))"

definition is_history_relation :: "('s1 \<times> 's2) set \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_history_relation R C A \<longleftrightarrow>
    is_simulation R C A \<and> is_ref_map (\<lambda>x. (SOME y. (x, y) \<in> R\<inverse>)) A C"

definition is_prophecy_relation :: "('s1 \<times> 's2) set \<Rightarrow> ('a, 's1) ioa \<Rightarrow> ('a, 's2) ioa \<Rightarrow> bool"
  where "is_prophecy_relation R C A \<longleftrightarrow>
    is_backward_simulation R C A \<and> is_ref_map (\<lambda>x. (SOME y. (x, y) \<in> R\<inverse>)) A C"


lemma set_non_empty: "A \<noteq> {} \<longleftrightarrow> (\<exists>x. x \<in> A)"
  by auto

lemma Int_non_empty: "A \<inter> B \<noteq> {} \<longleftrightarrow> (\<exists>x. x \<in> A \<and> x \<in> B)"
  by (simp add: set_non_empty)

lemma Sim_start_convert [simp]: "R``{x} \<inter> S \<noteq> {} \<longleftrightarrow> (\<exists>y. (x, y) \<in> R \<and> y \<in> S)"
  by (simp add: Image_def Int_non_empty)

lemma ref_map_is_simulation: "is_ref_map f C A \<Longrightarrow> is_simulation {p. snd p = f (fst p)} C A"
  by (simp add: is_ref_map_def is_simulation_def)

end
