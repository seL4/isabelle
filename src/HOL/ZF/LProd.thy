(*  Title:      HOL/ZF/LProd.thy
    ID:         $Id$
    Author:     Steven Obua

    Introduces the lprod relation.
    See "Partizan Games in Isabelle/HOLZF", available from http://www4.in.tum.de/~obua/partizan
*)

theory LProd 
imports Multiset
begin

inductive2
  lprod :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  lprod_single[intro!]: "R a b \<Longrightarrow> lprod R [a] [b]"
| lprod_list[intro!]: "lprod R (ah@at) (bh@bt) \<Longrightarrow> R a b \<or> a = b \<Longrightarrow> lprod R (ah@a#at) (bh@b#bt)"

lemma "lprod R as bs \<Longrightarrow> length as = length bs"
  apply (induct as bs rule: lprod.induct)
  apply auto
  done

lemma "lprod R as bs \<Longrightarrow> 1 \<le> length as \<and> 1 \<le> length bs"
  apply (induct as bs rule: lprod.induct)
  apply auto
  done

lemma lprod_subset_elem: "lprod S as bs \<Longrightarrow> S \<le> R \<Longrightarrow> lprod R as bs"
  apply (induct as bs rule: lprod.induct)
  apply (auto)
  done

lemma lprod_subset: "S \<le> R \<Longrightarrow> lprod S \<le> lprod R"
  by (auto intro: lprod_subset_elem)

lemma lprod_implies_mult: "lprod R as bs \<Longrightarrow> transP R \<Longrightarrow> mult R (multiset_of as) (multiset_of bs)"
proof (induct as bs rule: lprod.induct)
  case (lprod_single a b)
  note step = one_step_implies_mult[
    where r=R and I="{#}" and K="{#a#}" and J="{#b#}", simplified]    
  show ?case by (auto intro: lprod_single step)
next
  case (lprod_list ah at bh bt a b) 
  from prems have transR: "transP R" by auto
  have as: "multiset_of (ah @ a # at) = multiset_of (ah @ at) + {#a#}" (is "_ = ?ma + _")
    by (simp add: ring_eq_simps)
  have bs: "multiset_of (bh @ b # bt) = multiset_of (bh @ bt) + {#b#}" (is "_ = ?mb + _")
    by (simp add: ring_eq_simps)
  from prems have "mult R ?ma ?mb"
    by auto
  with mult_implies_one_step[OF transR] have 
    "\<exists>I J K. ?mb = I + J \<and> ?ma = I + K \<and> J \<noteq> {#} \<and> (\<forall>k\<in>set_of K. \<exists>j\<in>set_of J. R k j)"
    by blast
  then obtain I J K where 
    decomposed: "?mb = I + J \<and> ?ma = I + K \<and> J \<noteq> {#} \<and> (\<forall>k\<in>set_of K. \<exists>j\<in>set_of J. R k j)"
    by blast   
  show ?case
  proof (cases "a = b")
    case True    
    have "mult R ((I + {#b#}) + K) ((I + {#b#}) + J)"
      apply (rule one_step_implies_mult)
      apply (auto simp add: decomposed)
      done
    then show ?thesis
      apply (simp only: as bs)
      apply (simp only: decomposed True)
      apply (simp add: ring_eq_simps)
      done
  next
    case False
    from False lprod_list have False: "R a b" by blast
    have "mult R (I + (K + {#a#})) (I + (J + {#b#}))"
      apply (rule one_step_implies_mult)
      apply (auto simp add: False decomposed)
      done
    then show ?thesis
      apply (simp only: as bs)
      apply (simp only: decomposed)
      apply (simp add: ring_eq_simps)
      done
  qed
qed

lemma wf_lprod[recdef_wf,simp,intro]:
  assumes wf_R: "wfP R"
  shows "wfP (lprod R)"
proof -
  have subset: "lprod (R^++) \<le> inv_imagep (mult (R^++)) multiset_of"
    by (auto simp add: lprod_implies_mult trans_trancl[to_pred])
  note lprodtrancl = wfP_subset[OF wf_inv_image[to_pred, where r="mult (R^++)" and f="multiset_of", 
    OF wf_mult[OF wfP_trancl[OF wf_R]]], OF subset]
  note lprod = wfP_subset[OF lprodtrancl, where p="lprod R", OF lprod_subset, simplified]
  show ?thesis by (auto intro: lprod)
qed

constdefs
  gprod_2_2 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a * 'a) \<Rightarrow> ('a * 'a) \<Rightarrow> bool"
  "gprod_2_2 R \<equiv> \<lambda>(a,b) (c,d). (a = c \<and> R b d) \<or> (b = d \<and> R a c)"
  gprod_2_1 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a * 'a) \<Rightarrow> ('a * 'a) \<Rightarrow> bool"
  "gprod_2_1 R \<equiv> \<lambda>(a,b) (c,d). (a = d \<and> R b c) \<or> (b = c \<and> R a d)"

lemma lprod_2_3: "R a b \<Longrightarrow> lprod R [a, c] [b, c]"
  by (auto intro: lprod_list[where a=c and b=c and 
    ah = "[a]" and at = "[]" and bh="[b]" and bt="[]", simplified]) 

lemma lprod_2_4: "R a b \<Longrightarrow> lprod R [c, a] [c, b]"
  by (auto intro: lprod_list[where a=c and b=c and 
    ah = "[]" and at = "[a]" and bh="[]" and bt="[b]", simplified])

lemma lprod_2_1: "R a b \<Longrightarrow> lprod R [c, a] [b, c]"
  by (auto intro: lprod_list[where a=c and b=c and 
    ah = "[]" and at = "[a]" and bh="[b]" and bt="[]", simplified]) 

lemma lprod_2_2: "R a b \<Longrightarrow> lprod R [a, c] [c, b]"
  by (auto intro: lprod_list[where a=c and b=c and 
    ah = "[a]" and at = "[]" and bh="[]" and bt="[b]", simplified])

lemma [recdef_wf, simp, intro]: 
  assumes wfR: "wfP R" shows "wfP (gprod_2_1 R)"
proof -
  have "gprod_2_1 R \<le> inv_imagep (lprod R) (\<lambda> (a,b). [a,b])"
    by (auto simp add: gprod_2_1_def lprod_2_1 lprod_2_2)
  with wfR show ?thesis
    by (rule_tac wfP_subset, auto intro!: wf_inv_image[to_pred])
qed

lemma [recdef_wf, simp, intro]: 
  assumes wfR: "wfP R" shows "wfP (gprod_2_2 R)"
proof -
  have "gprod_2_2 R \<le> inv_imagep (lprod R) (\<lambda> (a,b). [a,b])"
    by (auto simp add: gprod_2_2_def lprod_2_3 lprod_2_4)
  with wfR show ?thesis
    by (rule_tac wfP_subset, auto intro!: wf_inv_image[to_pred])
qed

lemma lprod_3_1: assumes "R x' x" shows "lprod R [y, z, x'] [x, y, z]"
  apply (rule lprod_list[where a="y" and b="y" and ah="[]" and at="[z,x']" and bh="[x]" and bt="[z]", simplified])
  apply (auto simp add: lprod_2_1 prems)
  done

lemma lprod_3_2: assumes "R z' z" shows "lprod R [z', x, y] [x,y,z]"
  apply (rule lprod_list[where a="y" and b="y" and ah="[z',x]" and at="[]" and bh="[x]" and bt="[z]", simplified])
  apply (auto simp add: lprod_2_2 prems)
  done

lemma lprod_3_3: assumes xr: "R xr x" shows "lprod R [xr, y, z] [x, y, z]"
  apply (rule lprod_list[where a="y" and b="y" and ah="[xr]" and at="[z]" and bh="[x]" and bt="[z]", simplified])
  apply (simp add: xr lprod_2_3)
  done

lemma lprod_3_4: assumes yr: "R yr y" shows "lprod R [x, yr, z] [x, y, z]"
  apply (rule lprod_list[where a="x" and b="x" and ah="[]" and at="[yr,z]" and bh="[]" and bt="[y,z]", simplified])
  apply (simp add: yr lprod_2_3)
  done

lemma lprod_3_5: assumes zr: "R zr z" shows "lprod R [x, y, zr] [x, y, z]"
  apply (rule lprod_list[where a="x" and b="x" and ah="[]" and at="[y,zr]" and bh="[]" and bt="[y,z]", simplified])
  apply (simp add: zr lprod_2_4)
  done

lemma lprod_3_6: assumes y': "R y' y" shows "lprod R [x, z, y'] [x, y, z]"
  apply (rule lprod_list[where a="z" and b="z" and ah="[x]" and at="[y']" and bh="[x,y]" and bt="[]", simplified])
  apply (simp add: y' lprod_2_4)
  done

lemma lprod_3_7: assumes z': "R z' z" shows "lprod R [x, z', y] [x, y, z]"
  apply (rule lprod_list[where a="y" and b="y" and ah="[x, z']" and at="[]" and bh="[x]" and bt="[z]", simplified])
  apply (simp add: z' lprod_2_4)
  done

constdefs
   perm :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool"
   "perm f A \<equiv> inj_on f A \<and> f ` A = A"

lemma "lprod R as bs = 
  (\<exists> f. perm f {0 ..< (length as)} \<and> 
  (\<forall> j. j < length as \<longrightarrow> (R (nth as j) (nth bs (f j)) \<or> (nth as j = nth bs (f j)))) \<and> 
  (\<exists> i. i < length as \<and> R (nth as i) (nth bs (f i))))"
oops

lemma "transP R \<Longrightarrow> lprod R (ah@a#at) (bh@b#bt) \<Longrightarrow> R b a \<or> a = b \<Longrightarrow> lprod R (ah@at) (bh@bt)" 
oops



end