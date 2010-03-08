(*  Title:      HOLCF/Domain_Aux.thy
    Author:     Brian Huffman
*)

header {* Domain package support *}

theory Domain_Aux
imports Ssum Sprod Fixrec
uses
  ("Tools/Domain/domain_take_proofs.ML")
begin

subsection {* Proofs about take functions *}

text {*
  This section contains lemmas that are used in a module that supports
  the domain isomorphism package; the module contains proofs related
  to take functions and the finiteness predicate.
*}

lemma deflation_abs_rep:
  fixes abs and rep and d
  assumes abs_iso: "\<And>x. rep\<cdot>(abs\<cdot>x) = x"
  assumes rep_iso: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
  shows "deflation d \<Longrightarrow> deflation (abs oo d oo rep)"
by (rule ep_pair.deflation_e_d_p) (simp add: ep_pair.intro assms)

lemma deflation_chain_min:
  assumes chain: "chain d"
  assumes defl: "\<And>n. deflation (d n)"
  shows "d m\<cdot>(d n\<cdot>x) = d (min m n)\<cdot>x"
proof (rule linorder_le_cases)
  assume "m \<le> n"
  with chain have "d m \<sqsubseteq> d n" by (rule chain_mono)
  then have "d m\<cdot>(d n\<cdot>x) = d m\<cdot>x"
    by (rule deflation_below_comp1 [OF defl defl])
  moreover from `m \<le> n` have "min m n = m" by simp
  ultimately show ?thesis by simp
next
  assume "n \<le> m"
  with chain have "d n \<sqsubseteq> d m" by (rule chain_mono)
  then have "d m\<cdot>(d n\<cdot>x) = d n\<cdot>x"
    by (rule deflation_below_comp2 [OF defl defl])
  moreover from `n \<le> m` have "min m n = n" by simp
  ultimately show ?thesis by simp
qed

use "Tools/Domain/domain_take_proofs.ML"

end
