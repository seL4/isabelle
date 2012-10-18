(* Author: Florian Haftmann, TU Muenchen *)

header {* A simple cookbook example how to eliminate choice in programs. *}

theory Execute_Choice
imports Main "~~/src/HOL/Library/AList_Mapping"
begin

text {*
  A trivial example:
*}

definition valuesum :: "('a, 'b :: ab_group_add) mapping \<Rightarrow> 'b" where
  "valuesum m = (\<Sum>k \<in> Mapping.keys m. the (Mapping.lookup m k))"

text {*
  Not that instead of defining @{term valuesum} with choice, we define it
  directly and derive a description involving choice afterwards:
*}

lemma valuesum_rec:
  assumes fin: "finite (dom (Mapping.lookup m))"
  shows "valuesum m = (if Mapping.is_empty m then 0 else
    let l = (SOME l. l \<in> Mapping.keys m) in the (Mapping.lookup m l) + valuesum (Mapping.delete l m))"
proof (cases "Mapping.is_empty m")
  case True then show ?thesis by (simp add: is_empty_def keys_def valuesum_def)
next
  case False
  then have l: "\<exists>l. l \<in> dom (Mapping.lookup m)" unfolding is_empty_def by transfer auto
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
  then show ?thesis unfolding is_empty_def valuesum_def by transfer simp
qed

text {*
  In the context of the else-branch we can show that the exact choice is
  irrelvant; in practice, finding this point where choice becomes irrelevant is the
  most difficult thing!
*}

lemma valuesum_choice:
  "finite (Mapping.keys M) \<Longrightarrow> x \<in> Mapping.keys M \<Longrightarrow> y \<in> Mapping.keys M \<Longrightarrow>
    the (Mapping.lookup M x) + valuesum (Mapping.delete x M) =
    the (Mapping.lookup M y) + valuesum (Mapping.delete y M)"
  unfolding valuesum_def  by transfer (simp add: setsum_diff)

text {*
  Given @{text valuesum_rec} as initial description, we stepwise refine it to something executable;
  first, we formally insert the constructor @{term Mapping} and split the one equation into two,
  where the second one provides the necessary context:
*}

lemma valuesum_rec_Mapping:
  shows [code]: "valuesum (Mapping []) = 0"
  and "valuesum (Mapping (x # xs)) = (let l = (SOME l. l \<in> Mapping.keys (Mapping (x # xs))) in
    the (Mapping.lookup (Mapping (x # xs)) l) + valuesum (Mapping.delete l (Mapping (x # xs))))"
  by (simp_all add: valuesum_rec finite_dom_map_of is_empty_Mapping null_def)

text {*
  As a side effect the precondition disappears (but note this has nothing to do with choice!).
  The first equation deals with the uncritical empty case and can already be used for code generation.

  Using @{text valuesum_choice}, we are able to prove an executable version of @{term valuesum}:
*}

lemma valuesum_rec_exec [code]:
  "valuesum (Mapping (x # xs)) = (let l = fst (hd (x # xs)) in
    the (Mapping.lookup (Mapping (x # xs)) l) + valuesum (Mapping.delete l (Mapping (x # xs))))"
proof -
  let ?M = "Mapping (x # xs)"
  let ?l1 = "(SOME l. l \<in> Mapping.keys ?M)"
  let ?l2 = "fst (hd (x # xs))"
  have "finite (Mapping.keys ?M)" by (simp add: keys_Mapping)
  moreover have "?l1 \<in> Mapping.keys ?M"
    by (rule someI) (auto simp add: keys_Mapping)
  moreover have "?l2 \<in> Mapping.keys ?M"
    by (simp add: keys_Mapping)
  ultimately have "the (Mapping.lookup ?M ?l1) + valuesum (Mapping.delete ?l1 ?M) =
    the (Mapping.lookup ?M ?l2) + valuesum (Mapping.delete ?l2 ?M)"
    by (rule valuesum_choice)
  then show ?thesis by (simp add: valuesum_rec_Mapping)
qed
  
text {*
  See how it works:
*}

value "valuesum (Mapping [(''abc'', (42::int)), (''def'', 1705)])"

end
