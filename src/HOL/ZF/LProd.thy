(*  Title:      HOL/ZF/LProd.thy
    ID:         $Id$
    Author:     Steven Obua

    Introduces the lprod relation.
    See "Partizan Games in Isabelle/HOLZF", available from http://www4.in.tum.de/~obua/partizan
*)

theory LProd 
imports Multiset
begin

consts
  lprod :: "('a * 'a) set \<Rightarrow> ('a list * 'a list) set"

inductive "lprod R"
intros
  lprod_single[intro!]: "(a, b) \<in> R \<Longrightarrow> ([a], [b]) \<in> lprod R"
  lprod_list[intro!]: "(ah@at, bh@bt) \<in> lprod R \<Longrightarrow> (a,b) \<in> R \<or> a = b \<Longrightarrow> (ah@a#at, bh@b#bt) \<in> lprod R"

lemma "(as,bs) \<in> lprod R \<Longrightarrow> length as = length bs"
  apply (induct as bs rule: lprod.induct)
  apply auto
  done

lemma "(as, bs) \<in> lprod R \<Longrightarrow> 1 \<le> length as \<and> 1 \<le> length bs"
  apply (induct as bs rule: lprod.induct)
  apply auto
  done

lemma lprod_subset_elem: "(as, bs) \<in> lprod S \<Longrightarrow> S \<subseteq> R \<Longrightarrow> (as, bs) \<in> lprod R"
  apply (induct as bs rule: lprod.induct)
  apply (auto)
  done

lemma lprod_subset: "S \<subseteq> R \<Longrightarrow> lprod S \<subseteq> lprod R"
  by (auto intro: lprod_subset_elem)

lemma lprod_implies_mult: "(as, bs) \<in> lprod R \<Longrightarrow> trans R \<Longrightarrow> (multiset_of as, multiset_of bs) \<in> mult R"
proof (induct as bs rule: lprod.induct)
  case (lprod_single a b)
  note step = one_step_implies_mult[
    where r=R and I="{#}" and K="{#a#}" and J="{#b#}", simplified]    
  show ?case by (auto intro: lprod_single step)
next
  case (lprod_list a ah at b bh bt) 
  from prems have transR: "trans R" by auto
  have as: "multiset_of (ah @ a # at) = multiset_of (ah @ at) + {#a#}" (is "_ = ?ma + _")
    by (simp add: ring_eq_simps)
  have bs: "multiset_of (bh @ b # bt) = multiset_of (bh @ bt) + {#b#}" (is "_ = ?mb + _")
    by (simp add: ring_eq_simps)
  from prems have "(?ma, ?mb) \<in> mult R"
    by auto
  with mult_implies_one_step[OF transR] have 
    "\<exists>I J K. ?mb = I + J \<and> ?ma = I + K \<and> J \<noteq> {#} \<and> (\<forall>k\<in>set_of K. \<exists>j\<in>set_of J. (k, j) \<in> R)"
    by blast
  then obtain I J K where 
    decomposed: "?mb = I + J \<and> ?ma = I + K \<and> J \<noteq> {#} \<and> (\<forall>k\<in>set_of K. \<exists>j\<in>set_of J. (k, j) \<in> R)"
    by blast   
  show ?case
  proof (cases "a = b")
    case True    
    have "((I + {#b#}) + K, (I + {#b#}) + J) \<in> mult R"
      apply (rule one_step_implies_mult[OF transR])
      apply (auto simp add: decomposed)
      done
    then show ?thesis
      apply (simp only: as bs)
      apply (simp only: decomposed True)
      apply (simp add: ring_eq_simps)
      done
  next
    case False
    from False lprod_list have False: "(a, b) \<in> R" by blast
    have "(I + (K + {#a#}), I + (J + {#b#})) \<in> mult R"
      apply (rule one_step_implies_mult[OF transR])
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
  assumes wf_R: "wf R"
  shows "wf (lprod R)"
proof -
  have subset: "lprod (R^+) \<subseteq> inv_image (mult (R^+)) multiset_of"
    by (auto simp add: inv_image_def lprod_implies_mult trans_trancl)
  note lprodtrancl = wf_subset[OF wf_inv_image[where r="mult (R^+)" and f="multiset_of", 
    OF wf_mult[OF wf_trancl[OF wf_R]]], OF subset]
  note lprod = wf_subset[OF lprodtrancl, where p="lprod R", OF lprod_subset, simplified]
  show ?thesis by (auto intro: lprod)
qed

constdefs
  gprod_2_2 :: "('a * 'a) set \<Rightarrow> (('a * 'a) * ('a * 'a)) set"
  "gprod_2_2 R \<equiv> { ((a,b), (c,d)) . (a = c \<and> (b,d) \<in> R) \<or> (b = d \<and> (a,c) \<in> R) }"
  gprod_2_1 :: "('a * 'a) set \<Rightarrow> (('a * 'a) * ('a * 'a)) set"
  "gprod_2_1 R \<equiv>  { ((a,b), (c,d)) . (a = d \<and> (b,c) \<in> R) \<or> (b = c \<and> (a,d) \<in> R) }"

lemma lprod_2_3: "(a, b) \<in> R \<Longrightarrow> ([a, c], [b, c]) \<in> lprod R"
  by (auto intro: lprod_list[where a=c and b=c and 
    ah = "[a]" and at = "[]" and bh="[b]" and bt="[]", simplified]) 

lemma lprod_2_4: "(a, b) \<in> R \<Longrightarrow> ([c, a], [c, b]) \<in> lprod R"
  by (auto intro: lprod_list[where a=c and b=c and 
    ah = "[]" and at = "[a]" and bh="[]" and bt="[b]", simplified])

lemma lprod_2_1: "(a, b) \<in> R \<Longrightarrow> ([c, a], [b, c]) \<in> lprod R"
  by (auto intro: lprod_list[where a=c and b=c and 
    ah = "[]" and at = "[a]" and bh="[b]" and bt="[]", simplified]) 

lemma lprod_2_2: "(a, b) \<in> R \<Longrightarrow> ([a, c], [c, b]) \<in> lprod R"
  by (auto intro: lprod_list[where a=c and b=c and 
    ah = "[a]" and at = "[]" and bh="[]" and bt="[b]", simplified])

lemma [recdef_wf, simp, intro]: 
  assumes wfR: "wf R" shows "wf (gprod_2_1 R)"
proof -
  have "gprod_2_1 R \<subseteq> inv_image (lprod R) (\<lambda> (a,b). [a,b])"
    by (auto simp add: inv_image_def gprod_2_1_def lprod_2_1 lprod_2_2)
  with wfR show ?thesis
    by (rule_tac wf_subset, auto)
qed

lemma [recdef_wf, simp, intro]: 
  assumes wfR: "wf R" shows "wf (gprod_2_2 R)"
proof -
  have "gprod_2_2 R \<subseteq> inv_image (lprod R) (\<lambda> (a,b). [a,b])"
    by (auto simp add: inv_image_def gprod_2_2_def lprod_2_3 lprod_2_4)
  with wfR show ?thesis
    by (rule_tac wf_subset, auto)
qed

lemma lprod_3_1: assumes "(x', x) \<in> R" shows "([y, z, x'], [x, y, z]) \<in> lprod R"
  apply (rule lprod_list[where a="y" and b="y" and ah="[]" and at="[z,x']" and bh="[x]" and bt="[z]", simplified])
  apply (auto simp add: lprod_2_1 prems)
  done

lemma lprod_3_2: assumes "(z',z) \<in> R" shows "([z', x, y], [x,y,z]) \<in> lprod R"
  apply (rule lprod_list[where a="y" and b="y" and ah="[z',x]" and at="[]" and bh="[x]" and bt="[z]", simplified])
  apply (auto simp add: lprod_2_2 prems)
  done

lemma lprod_3_3: assumes xr: "(xr, x) \<in> R" shows "([xr, y, z], [x, y, z]) \<in> lprod R"
  apply (rule lprod_list[where a="y" and b="y" and ah="[xr]" and at="[z]" and bh="[x]" and bt="[z]", simplified])
  apply (simp add: xr lprod_2_3)
  done

lemma lprod_3_4: assumes yr: "(yr, y) \<in> R" shows "([x, yr, z], [x, y, z]) \<in> lprod R"
  apply (rule lprod_list[where a="x" and b="x" and ah="[]" and at="[yr,z]" and bh="[]" and bt="[y,z]", simplified])
  apply (simp add: yr lprod_2_3)
  done

lemma lprod_3_5: assumes zr: "(zr, z) \<in> R" shows "([x, y, zr], [x, y, z]) \<in> lprod R"
  apply (rule lprod_list[where a="x" and b="x" and ah="[]" and at="[y,zr]" and bh="[]" and bt="[y,z]", simplified])
  apply (simp add: zr lprod_2_4)
  done

lemma lprod_3_6: assumes y': "(y', y) \<in> R" shows "([x, z, y'], [x, y, z]) \<in> lprod R"
  apply (rule lprod_list[where a="z" and b="z" and ah="[x]" and at="[y']" and bh="[x,y]" and bt="[]", simplified])
  apply (simp add: y' lprod_2_4)
  done

lemma lprod_3_7: assumes z': "(z',z) \<in> R" shows "([x, z', y], [x, y, z]) \<in> lprod R"
  apply (rule lprod_list[where a="y" and b="y" and ah="[x, z']" and at="[]" and bh="[x]" and bt="[z]", simplified])
  apply (simp add: z' lprod_2_4)
  done

constdefs
   perm :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool"
   "perm f A \<equiv> inj_on f A \<and> f ` A = A"

lemma "((as,bs) \<in> lprod R) = 
  (\<exists> f. perm f {0 ..< (length as)} \<and> 
  (\<forall> j. j < length as \<longrightarrow> ((nth as j, nth bs (f j)) \<in> R \<or> (nth as j = nth bs (f j)))) \<and> 
  (\<exists> i. i < length as \<and> (nth as i, nth bs (f i)) \<in> R))"
oops

lemma "trans R \<Longrightarrow> (ah@a#at, bh@b#bt) \<in> lprod R \<Longrightarrow> (b, a) \<in> R \<or> a = b \<Longrightarrow> (ah@at, bh@bt) \<in> lprod R" 
oops



end