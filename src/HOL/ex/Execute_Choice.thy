(* Author: Florian Haftmann, TU Muenchen *)

header {* A simple cookbook example how to eliminate choice in programs. *}

theory Execute_Choice
imports Main AssocList
begin

definition valuesum :: "('a, 'b :: comm_monoid_add) mapping \<Rightarrow> 'b" where
  "valuesum m = (\<Sum>k \<in> Mapping.keys m. the (Mapping.lookup m k))"

lemma valuesum_rec:
  assumes fin: "finite (dom (Mapping.lookup m))"
  shows "valuesum m = (if Mapping.is_empty m then 0 else
    let l = (SOME l. l \<in> Mapping.keys m) in the (Mapping.lookup m l) + valuesum (Mapping.delete l m))"
proof (cases "Mapping.is_empty m")
  case True then show ?thesis by (simp add: is_empty_def keys_def valuesum_def)
next
  case False
  then have l: "\<exists>l. l \<in> dom (Mapping.lookup m)" by (auto simp add: is_empty_def expand_fun_eq mem_def)
  then have "(let l = SOME l. l \<in> dom (Mapping.lookup m) in
     the (Mapping.lookup m l) + (\<Sum>k \<in> dom (Mapping.lookup m) - {l}. the (Mapping.lookup m k))) =
       (\<Sum>k \<in> dom (Mapping.lookup m). the (Mapping.lookup m k))"
  proof (rule someI2_ex)
    fix l
    note fin
    moreover assume "l \<in> dom (Mapping.lookup m)"
    moreover obtain A where "A = dom (Mapping.lookup m) - {l}" by simp
    ultimately have "dom (Mapping.lookup m) = insert l A" and "finite A" and "l \<notin> A" by auto
    then show "(let l = l
        in the (Mapping.lookup m l) + (\<Sum>k \<in> dom (Mapping.lookup m) - {l}. the (Mapping.lookup m k))) =
        (\<Sum>k \<in> dom (Mapping.lookup m). the (Mapping.lookup m k))"
      by simp
   qed
  then show ?thesis by (simp add: keys_def valuesum_def is_empty_def)
qed

lemma valuesum_rec_AList:
  "valuesum (AList []) = 0"
  "valuesum (AList (x # xs)) = (let l = (SOME l. l \<in> Mapping.keys (AList (x # xs))) in
    the (Mapping.lookup (AList (x # xs)) l) + valuesum (Mapping.delete l (AList (x # xs))))"
  by (simp_all add: valuesum_rec finite_dom_map_of is_empty_AList)

axioms
  FIXME: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> C x = C y"

lemma aux: "(SOME l. l \<in> Mapping.keys (AList (x # xs))) = fst (hd (x # xs))"
proof (rule FIXME)
  show "fst (hd (x # xs)) \<in> Mapping.keys (AList (x # xs))"
    by (simp add: keys_AList)
  show "(SOME l. l \<in> Mapping.keys (AList (x # xs))) \<in> Mapping.keys (AList (x # xs))"
    apply (rule someI) apply (simp add: keys_AList) apply auto
    done
qed

lemma valuesum_rec_exec [code]:
  "valuesum (AList []) = 0"
  "valuesum (AList (x # xs)) = (let l = fst (hd (x # xs)) in
    the (Mapping.lookup (AList (x # xs)) l) + valuesum (Mapping.delete l (AList (x # xs))))"
  by (simp_all add: valuesum_rec_AList aux)

value "valuesum (AList [(''abc'', (42::nat)), (''def'', 1705)])"

end
