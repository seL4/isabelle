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

theorem Schroeder_Bernstein: \<open>\<exists>h :: 'a \<Rightarrow> 'b. inj h \<and> surj h\<close> if \<open>inj f\<close> and \<open>inj g\<close>
  for f :: \<open>'a \<Rightarrow> 'b\<close> and g :: \<open>'b \<Rightarrow> 'a\<close>
proof
  define A where \<open>A = lfp (\<lambda>X. - (g ` (- (f ` X))))\<close>
  define g' where \<open>g' = inv g\<close>
  let \<open>?h\<close> = \<open>\<lambda>z. if z \<in> A then f z else g' z\<close>

  have \<open>A = - (g ` (- (f ` A)))\<close>
    unfolding A_def by (rule lfp_unfold) (blast intro: monoI)
  then have A_compl: \<open>- A = g ` (- (f ` A))\<close> by blast
  then have *: \<open>g' ` (- A) = - (f ` A)\<close>
    using g'_def \<open>inj g\<close> by auto

  show \<open>inj ?h \<and> surj ?h\<close>
  proof
    from * show \<open>surj ?h\<close> by auto
    have \<open>inj_on f A\<close>
      using \<open>inj f\<close> by (rule subset_inj_on) blast
    moreover
    have \<open>inj_on g' (- A)\<close>
      unfolding g'_def
    proof (rule inj_on_inv_into)
      have \<open>g ` (- (f ` A)) \<subseteq> range g\<close> by blast
      then show \<open>- A \<subseteq> range g\<close> by (simp only: A_compl)
    qed
    moreover
    have \<open>False\<close> if eq: \<open>f a = g' b\<close> and a: \<open>a \<in> A\<close> and b: \<open>b \<in> - A\<close> for a b
    proof -
      from a have fa: \<open>f a \<in> f ` A\<close> by (rule imageI)
      from b have \<open>g' b \<in> g' ` (- A)\<close> by (rule imageI)
      with * have \<open>g' b \<in> - (f ` A)\<close> by simp
      with eq fa show \<open>False\<close> by simp
    qed
    ultimately show \<open>inj ?h\<close>
      unfolding inj_on_def by (metis ComplI)
  qed
qed

end
