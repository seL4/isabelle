(*  Title:      HOL/Library/SCT_Interpretation.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Applying SCT to function definitions *}

theory Interpretation
imports Main Misc_Tools Criterion
begin

definition
  "idseq R s x = (s 0 = x \<and> (\<forall>i. R (s (Suc i)) (s i)))"

lemma not_acc_smaller:
  assumes notacc: "\<not> accp R x"
  shows "\<exists>y. R y x \<and> \<not> accp R y"
proof (rule classical)
  assume "\<not> ?thesis"
  hence "\<And>y. R y x \<Longrightarrow> accp R y" by blast
  with accp.accI have "accp R x" .
  with notacc show ?thesis by contradiction
qed

lemma non_acc_has_idseq:
  assumes "\<not> accp R x"
  shows "\<exists>s. idseq R s x"
proof -
  
  have	"\<exists>f. \<forall>x. \<not>accp R x \<longrightarrow> R (f x) x \<and> \<not>accp R (f x)"
	by (rule choice, auto simp:not_acc_smaller)
  
  then obtain f where
	in_R: "\<And>x. \<not>accp R x \<Longrightarrow> R (f x) x"
	and nia: "\<And>x. \<not>accp R x \<Longrightarrow> \<not>accp R (f x)"
	by blast
  
  let ?s = "\<lambda>i. (f ^^ i) x"
  
  {
	fix i
	have "\<not>accp R (?s i)"
	  by (induct i) (auto simp:nia `\<not>accp R x`)
	hence "R (f (?s i)) (?s i)"
	  by (rule in_R)
  }
  
  hence "idseq R ?s x"
	unfolding idseq_def
	by auto
  
  thus ?thesis by auto
qed





types ('a, 'q) cdesc =
  "('q \<Rightarrow> bool) \<times> ('q \<Rightarrow> 'a) \<times>('q \<Rightarrow> 'a)"


fun in_cdesc :: "('a, 'q) cdesc \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "in_cdesc (\<Gamma>, r, l) x y = (\<exists>q. x = r q \<and> y = l q \<and> \<Gamma> q)"

primrec mk_rel :: "('a, 'q) cdesc list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "mk_rel [] x y = False"
| "mk_rel (c#cs) x y =
  (in_cdesc c x y \<or> mk_rel cs x y)"


lemma some_rd:
  assumes "mk_rel rds x y"
  shows "\<exists>rd\<in>set rds. in_cdesc rd x y"
  using assms
  by (induct rds) (auto simp:in_cdesc_def)

(* from a value sequence, get a sequence of rds *)

lemma ex_cs:
  assumes idseq: "idseq (mk_rel rds) s x"
  shows "\<exists>cs. \<forall>i. cs i \<in> set rds \<and> in_cdesc (cs i) (s (Suc i)) (s i)"
proof -
  from idseq
  have a: "\<forall>i. \<exists>rd \<in> set rds. in_cdesc rd (s (Suc i)) (s i)"
	by (auto simp:idseq_def intro:some_rd)
  
  show ?thesis
	by (rule choice) (insert a, blast)
qed


types 'a measures = "nat \<Rightarrow> 'a \<Rightarrow> nat"

fun stepP :: "('a, 'q) cdesc \<Rightarrow> ('a, 'q) cdesc \<Rightarrow> 
  ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool"
where
  "stepP (\<Gamma>1,r1,l1) (\<Gamma>2,r2,l2) m1 m2 R
  = (\<forall>q\<^isub>1 q\<^isub>2. \<Gamma>1 q\<^isub>1 \<and> \<Gamma>2 q\<^isub>2 \<and> r1 q\<^isub>1 = l2 q\<^isub>2 
  \<longrightarrow> R (m2 (l2 q\<^isub>2)) ((m1 (l1 q\<^isub>1))))"


definition
  decr :: "('a, 'q) cdesc \<Rightarrow> ('a, 'q) cdesc \<Rightarrow> 
  ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool"
where
  "decr c1 c2 m1 m2 = stepP c1 c2 m1 m2 (op <)"

definition
  decreq :: "('a, 'q) cdesc \<Rightarrow> ('a, 'q) cdesc \<Rightarrow> 
  ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool"
where
  "decreq c1 c2 m1 m2 = stepP c1 c2 m1 m2 (op \<le>)"

definition
  no_step :: "('a, 'q) cdesc \<Rightarrow> ('a, 'q) cdesc \<Rightarrow> bool"
where
  "no_step c1 c2 = stepP c1 c2 (\<lambda>x. 0) (\<lambda>x. 0) (\<lambda>x y. False)"



lemma decr_in_cdesc:
  assumes "in_cdesc RD1 y x"
  assumes "in_cdesc RD2 z y"
  assumes "decr RD1 RD2 m1 m2"
  shows "m2 y < m1 x"
  using assms
  by (cases RD1, cases RD2, auto simp:decr_def)

lemma decreq_in_cdesc:
  assumes "in_cdesc RD1 y x"
  assumes "in_cdesc RD2 z y"
  assumes "decreq RD1 RD2 m1 m2"
  shows "m2 y \<le> m1 x"
  using assms
  by (cases RD1, cases RD2, auto simp:decreq_def)


lemma no_inf_desc_nat_sequence:
  fixes s :: "nat \<Rightarrow> nat"
  assumes leq: "\<And>i. n \<le> i \<Longrightarrow> s (Suc i) \<le> s i"
  assumes less: "\<exists>\<^sub>\<infinity>i. s (Suc i) < s i"
  shows False
proof -
  {
	fix i j:: nat 
	assume "n \<le> i"
	assume "i \<le> j"
	{
	  fix k 
	  have "s (i + k) \<le> s i"
	  proof (induct k)
		case 0 thus ?case by simp
	  next
		case (Suc k)
		with leq[of "i + k"] `n \<le> i`
		show ?case by simp
	  qed
	}
	from this[of "j - i"] `n \<le> i` `i \<le> j`
	have "s j \<le> s i" by auto
  }
  note decr = this
  
  let ?min = "LEAST x. x \<in> range (\<lambda>i. s (n + i))"
  have "?min \<in> range (\<lambda>i. s (n + i))"
	by (rule LeastI) auto
  then obtain k where min: "?min = s (n + k)" by auto
  
  from less 
  obtain k' where "n + k < k'"
	and "s (Suc k') < s k'"
	unfolding INFM_nat by auto
  
  with decr[of "n + k" k'] min
  have "s (Suc k') < ?min" by auto
  moreover from `n + k < k'`
  have "s (Suc k') = s (n + (Suc k' - n))" by simp
  ultimately
  show False using not_less_Least by blast
qed



definition
  approx :: "nat scg \<Rightarrow> ('a, 'q) cdesc \<Rightarrow> ('a, 'q) cdesc 
  \<Rightarrow> 'a measures \<Rightarrow> 'a measures \<Rightarrow> bool"
  where
  "approx G C C' M M'
  = (\<forall>i j. (dsc G i j \<longrightarrow> decr C C' (M i) (M' j))
  \<and>(eqp G i j \<longrightarrow> decreq C C' (M i) (M' j)))"




(* Unfolding "approx" for finite graphs *)

lemma approx_empty: 
  "approx (Graph {}) c1 c2 ms1 ms2"
  unfolding approx_def has_edge_def dest_graph.simps by simp

lemma approx_less:
  assumes "stepP c1 c2 (ms1 i) (ms2 j) (op <)"
  assumes "approx (Graph Es) c1 c2 ms1 ms2"
  shows "approx (Graph (insert (i, \<down>, j) Es)) c1 c2 ms1 ms2"
  using assms
  unfolding approx_def has_edge_def dest_graph.simps decr_def
  by auto

lemma approx_leq:
  assumes "stepP c1 c2 (ms1 i) (ms2 j) (op \<le>)"
  assumes "approx (Graph Es) c1 c2 ms1 ms2"
  shows "approx (Graph (insert (i, \<Down>, j) Es)) c1 c2 ms1 ms2"
  using assms
  unfolding approx_def has_edge_def dest_graph.simps decreq_def
  by auto


lemma "approx (Graph {(1, \<down>, 2),(2, \<Down>, 3)}) c1 c2 ms1 ms2"
  apply (intro approx_less approx_leq approx_empty) 
  oops


(*
fun
  no_step :: "('a, 'q) cdesc \<Rightarrow> ('a, 'q) cdesc \<Rightarrow> bool"
where
  "no_step (\<Gamma>1, r1, l1) (\<Gamma>2, r2, l2) =
  (\<forall>q\<^isub>1 q\<^isub>2. \<Gamma>1 q\<^isub>1 \<and> \<Gamma>2 q\<^isub>2 \<and> r1 q\<^isub>1 = l2 q\<^isub>2 \<longrightarrow> False)"
*)

lemma no_stepI:
  "stepP c1 c2 m1 m2 (\<lambda>x y. False)
  \<Longrightarrow> no_step c1 c2"
by (cases c1, cases c2) (auto simp: no_step_def)

definition
  sound_int :: "nat acg \<Rightarrow> ('a, 'q) cdesc list 
  \<Rightarrow> 'a measures list \<Rightarrow> bool"
where
  "sound_int \<A> RDs M =
  (\<forall>n<length RDs. \<forall>m<length RDs.
  no_step (RDs ! n) (RDs ! m) \<or>
  (\<exists>G. (\<A> \<turnstile> n \<leadsto>\<^bsup>G\<^esup> m) \<and> approx G (RDs ! n) (RDs ! m) (M ! n) (M ! m)))"


(* The following are uses by the tactics *)
lemma length_simps: "length [] = 0" "length (x#xs) = Suc (length xs)"
  by auto

lemma all_less_zero: "\<forall>n<(0::nat). P n"
  by simp

lemma all_less_Suc:
  assumes Pk: "P k"
  assumes Pn: "\<forall>n<k. P n"
  shows "\<forall>n<Suc k. P n"
proof (intro allI impI)
  fix n assume "n < Suc k"
  show "P n"
  proof (cases "n < k")
    case True with Pn show ?thesis by simp
  next
    case False with `n < Suc k` have "n = k" by simp
    with Pk show ?thesis by simp
  qed
qed


lemma step_witness:
  assumes "in_cdesc RD1 y x"
  assumes "in_cdesc RD2 z y"
  shows "\<not> no_step RD1 RD2"
  using assms
  by (cases RD1, cases RD2) (auto simp:no_step_def)


theorem SCT_on_relations:
  assumes R: "R = mk_rel RDs"
  assumes sound: "sound_int \<A> RDs M"
  assumes "SCT \<A>"
  shows "\<forall>x. accp R x"
proof (rule, rule classical)
  fix x
  assume "\<not> accp R x"
  with non_acc_has_idseq	
  have "\<exists>s. idseq R s x" .
  then obtain s where "idseq R s x" ..
  hence "\<exists>cs. \<forall>i. cs i \<in> set RDs \<and>
	in_cdesc (cs i) (s (Suc i)) (s i)"
	unfolding R by (rule ex_cs) 
  then obtain cs where
	[simp]: "\<And>i. cs i \<in> set RDs"
	  and ird[simp]: "\<And>i. in_cdesc (cs i) (s (Suc i)) (s i)"
	by blast
  
  let ?cis = "\<lambda>i. index_of RDs (cs i)"
  have "\<forall>i. \<exists>G. (\<A> \<turnstile> ?cis i \<leadsto>\<^bsup>G\<^esup> (?cis (Suc i)))
	\<and> approx G (RDs ! ?cis i) (RDs ! ?cis (Suc i)) 
	(M ! ?cis i) (M ! ?cis (Suc i))" (is "\<forall>i. \<exists>G. ?P i G")
  proof
	fix i
	let ?n = "?cis i" and ?n' = "?cis (Suc i)"
    
	have "in_cdesc (RDs ! ?n) (s (Suc i)) (s i)"
	  "in_cdesc (RDs ! ?n') (s (Suc (Suc i))) (s (Suc i))"
	  by (simp_all add:index_of_member)
	with step_witness
 	have "\<not> no_step (RDs ! ?n) (RDs ! ?n')" .
	moreover have
	  "?n < length RDs" 
	  "?n' < length RDs"
	  by (simp_all add:index_of_length[symmetric])
	ultimately
	obtain G
	  where "\<A> \<turnstile> ?n \<leadsto>\<^bsup>G\<^esup> ?n'"
	  and "approx G (RDs ! ?n) (RDs ! ?n') (M ! ?n) (M ! ?n')"
	  using sound
	  unfolding sound_int_def by auto
    
	thus "\<exists>G. ?P i G" by blast
  qed
  with choice
  have "\<exists>Gs. \<forall>i. ?P i (Gs i)" .
  then obtain Gs where 
	A: "\<And>i. \<A> \<turnstile> ?cis i \<leadsto>\<^bsup>(Gs i)\<^esup> (?cis (Suc i))" 
	and B: "\<And>i. approx (Gs i) (RDs ! ?cis i) (RDs ! ?cis (Suc i)) 
	(M ! ?cis i) (M ! ?cis (Suc i))"
	by blast
  
  let ?p = "\<lambda>i. (?cis i, Gs i)"
  
  from A have "has_ipath \<A> ?p"
	unfolding has_ipath_def
	by auto
  
  with `SCT \<A>` SCT_def 
  obtain th where "is_desc_thread th ?p"
	by auto
  
  then obtain n
	where fr: "\<forall>i\<ge>n. eqlat ?p th i"
	and inf: "\<exists>\<^sub>\<infinity>i. descat ?p th i"
	unfolding is_desc_thread_def by auto
  
  from B
  have approx:
	"\<And>i. approx (Gs i) (cs i) (cs (Suc i)) 
	(M ! ?cis i) (M ! ?cis (Suc i))"
	by (simp add:index_of_member)
  
  let ?seq = "\<lambda>i. (M ! ?cis i) (th i) (s i)"
  
  have "\<And>i. n < i \<Longrightarrow> ?seq (Suc i) \<le> ?seq i"
  proof -
	fix i 
	let ?q1 = "th i" and ?q2 = "th (Suc i)"
	assume "n < i"
	
	with fr	have "eqlat ?p th i" by simp 
	hence "dsc (Gs i) ?q1 ?q2 \<or> eqp (Gs i) ?q1 ?q2" 
      by simp
	thus "?seq (Suc i) \<le> ?seq i"
	proof
	  assume "dsc (Gs i) ?q1 ?q2"
	  
	  with approx
	  have a:"decr (cs i) (cs (Suc i)) 
		((M ! ?cis i) ?q1) ((M ! ?cis (Suc i)) ?q2)" 
		unfolding approx_def by auto
      
	  show ?thesis
		apply (rule less_imp_le)
		apply (rule decr_in_cdesc[of _ "s (Suc i)" "s i"])
		by (rule ird a)+
	next
	  assume "eqp (Gs i) ?q1 ?q2"
	  
	  with approx
	  have a:"decreq (cs i) (cs (Suc i)) 
		((M ! ?cis i) ?q1) ((M ! ?cis (Suc i)) ?q2)" 
		unfolding approx_def by auto
      
	  show ?thesis
		apply (rule decreq_in_cdesc[of _ "s (Suc i)" "s i"])
		by (rule ird a)+
	qed
  qed
  moreover have "\<exists>\<^sub>\<infinity>i. ?seq (Suc i) < ?seq i" unfolding INFM_nat
  proof 
	fix i 
	from inf obtain j where "i < j" and d: "descat ?p th j"
	  unfolding INFM_nat by auto
	let ?q1 = "th j" and ?q2 = "th (Suc j)"
	from d have "dsc (Gs j) ?q1 ?q2" by auto
	
	with approx
	have a:"decr (cs j) (cs (Suc j)) 
	  ((M ! ?cis j) ?q1) ((M ! ?cis (Suc j)) ?q2)" 
	  unfolding approx_def by auto
    
	have "?seq (Suc j) < ?seq j"
	  apply (rule decr_in_cdesc[of _ "s (Suc j)" "s j"])
	  by (rule ird a)+
	with `i < j` 
	show "\<exists>j. i < j \<and> ?seq (Suc j) < ?seq j" by auto
  qed
  ultimately have False
    by (rule no_inf_desc_nat_sequence[of "Suc n"]) simp
  thus "accp R x" ..
qed

end
