(*  Title:      HOL/Isar_Examples/Schroeder_Bernstein.thy
    Author:     Makarius
*)

section \<open>Schröder-Bernstein Theorem\<close>

theory Schroeder_Bernstein
imports Main
begin

text \<open>
  See also:
  \<^item> @{file "$ISABELLE_HOME/src/HOL/ex/Set_Theory.thy"}
  \<^item> @{url "http://planetmath.org/proofofschroederbernsteintheoremusingtarskiknastertheorem"}
  \<^item> Springer LNCS 828 (cover page)
\<close>

theorem Schroeder_Bernstein:
  fixes f :: "'a \<Rightarrow> 'b"
    and g :: "'b \<Rightarrow> 'a"
  assumes "inj f" and "inj g"
  shows "\<exists>h :: 'a \<Rightarrow> 'b. inj h \<and> surj h"
proof
  def A \<equiv> "lfp (\<lambda>X. - (g ` (- (f ` X))))"
  def g' \<equiv> "inv g"
  let ?h = "\<lambda>z. if z \<in> A then f z else g' z"

  have "A = - (g ` (- (f ` A)))"
    unfolding A_def by (rule lfp_unfold) (blast intro: monoI)
  then have A_compl: "- A = g ` (- (f ` A))" by blast
  then have *: "g' ` (- A) = - (f ` A)"
    using g'_def \<open>inj g\<close> by auto

  show "inj ?h \<and> surj ?h"
  proof
    from * show "surj ?h" by auto
    have "inj_on f A"
      using \<open>inj f\<close> by (rule subset_inj_on) blast
    moreover
    have "inj_on g' (- A)"
      unfolding g'_def
    proof (rule inj_on_inv_into)
      have "g ` (- (f ` A)) \<subseteq> range g" by blast
      then show "- A \<subseteq> range g" by (simp only: A_compl)
    qed
    moreover
    have False if eq: "f a = g' b" and a: "a \<in> A" and b: "b \<in> - A" for a b
    proof -
      from a have fa: "f a \<in> f ` A" by (rule imageI)
      from b have "g' b \<in> g' ` (- A)" by (rule imageI)
      with * have "g' b \<in> - (f ` A)" by simp
      with eq fa show False by simp
    qed
    ultimately show "inj ?h"
      unfolding inj_on_def by (metis ComplI)
  qed
qed

end
