
header {* \chapter{Case Study: Single and Multi-Mutator Garbage Collection Algorithms}

\section {Formalization of the Memory} *}

theory Graph = Main:

datatype node = Black | White

types 
  nodes = "node list"
  edge  = "nat \<times> nat"
  edges = "edge list"

consts Roots :: "nat set"

constdefs
  Proper_Roots :: "nodes \<Rightarrow> bool"
  "Proper_Roots M \<equiv> Roots\<noteq>{} \<and> Roots \<subseteq> {i. i<length M}"

  Proper_Edges :: "(nodes \<times> edges) \<Rightarrow> bool"
  "Proper_Edges \<equiv> (\<lambda>(M,E). \<forall>i<length E. fst(E!i)<length M \<and> snd(E!i)<length M)"

  BtoW :: "(edge \<times> nodes) \<Rightarrow> bool"
  "BtoW \<equiv> (\<lambda>(e,M). (M!fst e)=Black \<and> (M!snd e)\<noteq>Black)"

  Blacks :: "nodes \<Rightarrow> nat set"
  "Blacks M \<equiv> {i. i<length M \<and> M!i=Black}"

  Reach :: "edges \<Rightarrow> nat set"
  "Reach E \<equiv> {x. (\<exists>path. 1<length path \<and> path!(length path - 1)\<in>Roots \<and> x=path!0
              \<and> (\<forall>i<length path - 1. (\<exists>j<length E. E!j=(path!(i+1), path!i))))
	      \<or> x\<in>Roots}"

text{* Reach: the set of reachable nodes is the set of Roots together with the
nodes reachable from some Root by a path represented by a list of
  nodes (at least two since we traverse at least one edge), where two
consecutive nodes correspond to an edge in E. *}

subsection {* Proofs about Graphs *}

lemmas Graph_defs= Blacks_def Proper_Roots_def Proper_Edges_def BtoW_def
declare Graph_defs [simp]

subsubsection{* Graph 1 *}

lemma Graph1_aux [rule_format]: 
  "\<lbrakk> Roots\<subseteq>Blacks M; \<forall>i<length E. \<not>BtoW(E!i,M)\<rbrakk>
  \<Longrightarrow> 1< length path \<longrightarrow> (path!(length path - 1))\<in>Roots \<longrightarrow>  
  (\<forall>i<length path - 1. (\<exists>j. j < length E \<and> E!j=(path!(Suc i), path!i))) 
  \<longrightarrow> M!(path!0) = Black"
apply(induct_tac "path")
 apply force
apply clarify
apply simp
apply(case_tac "list")
 apply force
apply simp
apply(rotate_tac -2)
apply(erule_tac x = "0" in all_dupE)
apply simp
apply clarify
apply(erule allE , erule (1) notE impE)
apply simp
apply(erule mp)
apply(case_tac "lista")
 apply force
apply simp
apply(erule mp)
apply clarify
apply(erule_tac x = "Suc i" in allE)
apply force
done

lemma Graph1: 
  "\<lbrakk>Roots\<subseteq>Blacks M; Proper_Edges(M, E); \<forall>i<length E. \<not>BtoW(E!i,M) \<rbrakk> 
  \<Longrightarrow> Reach E\<subseteq>Blacks M"
apply (unfold Reach_def)
apply simp
apply clarify
apply(erule disjE)
 apply clarify
 apply(rule conjI)
  apply(subgoal_tac "0< length path - Suc 0")
   apply(erule allE , erule (1) notE impE)
   apply force
  apply simp
 apply(rule Graph1_aux)
apply auto
done

subsubsection{* Graph 2 *}

lemma Ex_first_occurrence [rule_format]: 
  "P (n::nat) \<longrightarrow> (\<exists>m. P m \<and> (\<forall>i. i<m \<longrightarrow> \<not> P i))";
apply(rule nat_less_induct)
apply clarify
apply(case_tac "\<forall>m. m<n \<longrightarrow> \<not> P m")
apply auto
done

lemma Compl_lemma: "(n::nat)\<le>l \<Longrightarrow> (\<exists>m. m\<le>l \<and> n=l - m)"
apply(rule_tac x = "l - n" in exI)
apply arith
done

lemma Ex_last_occurrence: 
  "\<lbrakk>P (n::nat); n\<le>l\<rbrakk> \<Longrightarrow> (\<exists>m. P (l - m) \<and> (\<forall>i. i<m \<longrightarrow> \<not>P (l - i)))"
apply(drule Compl_lemma)
apply clarify
apply(erule Ex_first_occurrence)
done

lemma Graph2: 
  "\<lbrakk>T \<in> Reach E; R<length E\<rbrakk> \<Longrightarrow> T \<in> Reach (E[R:=(fst(E!R), T)])"
apply (unfold Reach_def)
apply clarify
apply simp
apply(case_tac "\<forall>z<length path. fst(E!R)\<noteq>path!z")
 apply(rule_tac x = "path" in exI)
 apply simp
 apply clarify
 apply(erule allE , erule (1) notE impE)
 apply clarify
 apply(rule_tac x = "j" in exI)
 apply(case_tac "j=R")
  apply(erule_tac x = "Suc i" in allE)
  apply simp
  apply arith
 apply (force simp add:nth_list_update)
apply simp
apply(erule exE)
apply(subgoal_tac "z \<le> length path - Suc 0")
 prefer 2 apply arith
apply(drule_tac P = "\<lambda>m. m<length path \<and> fst(E!R)=path!m" in Ex_last_occurrence)
 apply assumption
apply clarify
apply simp
apply(rule_tac x = "(path!0)#(drop (length path - Suc m) path)" in exI)
apply simp
apply(case_tac "length path - (length path - Suc m)")
 apply arith
apply simp
apply(subgoal_tac "(length path - Suc m) + nat \<le> length path")
 prefer 2 apply arith
apply(drule nth_drop)
apply simp
apply(subgoal_tac "length path - Suc m + nat = length path - Suc 0")
 prefer 2 apply arith 
apply simp
apply clarify
apply(case_tac "i")
 apply(force simp add: nth_list_update)
apply simp
apply(subgoal_tac "(length path - Suc m) + nata \<le> length path")
 prefer 2 apply arith
apply simp
apply(subgoal_tac "(length path - Suc m) + (Suc nata) \<le> length path")
 prefer 2 apply arith
apply simp
apply(erule_tac x = "length path - Suc m + nata" in allE)
apply simp
apply clarify
apply(rule_tac x = "j" in exI)
apply(case_tac "R=j")
 prefer 2 apply force
apply simp
apply(drule_tac t = "path ! (length path - Suc m)" in sym)
apply simp
apply(case_tac " length path - Suc 0 < m")
 apply(subgoal_tac "(length path - Suc m)=0")
  prefer 2 apply arith
 apply(simp del: diff_is_0_eq)
 apply(subgoal_tac "Suc nata\<le>nat")
 prefer 2 apply arith
 apply(drule_tac n = "Suc nata" in Compl_lemma)
 apply clarify
 apply force
apply(drule leI)
apply(subgoal_tac "Suc (length path - Suc m + nata)=(length path - Suc 0) - (m - Suc nata)")
 apply(erule_tac x = "m - (Suc nata)" in allE)
 apply(case_tac "m")
  apply simp
 apply simp
 apply(subgoal_tac "natb - nata < Suc natb")
  prefer 2 apply(erule thin_rl)+ apply arith
 apply simp
 apply(case_tac "length path")
  apply force
apply (erule_tac V = "Suc natb \<le> length path - Suc 0" in thin_rl)
apply simp
apply(frule_tac i1 = "length path" and j1 = "length path - Suc 0" and k1 = "m" in diff_diff_right [THEN mp])
apply(erule_tac V = "length path - Suc m + nat = length path - Suc 0" in thin_rl)
apply simp
apply arith
done


subsubsection{* Graph 3 *}

lemma Graph3: 
  "\<lbrakk> T\<in>Reach E; R<length E \<rbrakk> \<Longrightarrow> Reach(E[R:=(fst(E!R),T)]) \<subseteq> Reach E"
apply (unfold Reach_def)
apply clarify
apply simp
apply(case_tac "\<exists>i<length path - 1. (fst(E!R),T)=(path!(Suc i),path!i)")
--{* the changed edge is part of the path *}
 apply(erule exE)
 apply(drule_tac P = "\<lambda>i. i<length path - 1 \<and> (fst(E!R),T)=(path!Suc i,path!i)" in Ex_first_occurrence)
 apply clarify
 apply(erule disjE)
--{* T is NOT a root *}
  apply clarify
  apply(rule_tac x = "(take m path)@patha" in exI)
  apply(subgoal_tac "\<not>(length path\<le>m)")
   prefer 2 apply arith
  apply(simp add: min_def)
  apply(rule conjI)
   apply(subgoal_tac "\<not>(m + length patha - 1 < m)")
    prefer 2 apply arith
   apply(simp add: nth_append min_def)
  apply(rule conjI)
   apply(case_tac "m")
    apply force
   apply(case_tac "path")
    apply force
   apply force
  apply clarify
  apply(case_tac "Suc i\<le>m")
   apply(erule_tac x = "i" in allE)
   apply simp
   apply clarify
   apply(rule_tac x = "j" in exI)
   apply(case_tac "Suc i<m")
    apply(simp add: nth_append min_def)
    apply(case_tac "R=j")
     apply(simp add: nth_list_update)
     apply(case_tac "i=m")
      apply force
     apply(erule_tac x = "i" in allE)
     apply force
    apply(force simp add: nth_list_update)
   apply(simp add: nth_append min_def)
   apply(subgoal_tac "i=m - 1")
    prefer 2 apply arith
   apply(case_tac "R=j")
    apply(erule_tac x = "m - 1" in allE)
    apply(simp add: nth_list_update)
   apply(force simp add: nth_list_update)
  apply(simp add: nth_append min_def)
  apply(rotate_tac -4)
  apply(erule_tac x = "i - m" in allE)
  apply(subgoal_tac "Suc (i - m)=(Suc i - m)" )
    prefer 2 apply arith
   apply simp
  apply(erule mp)
  apply arith
--{* T is a root *}
 apply(case_tac "m=0")
  apply force
 apply(rule_tac x = "take (Suc m) path" in exI)
 apply(subgoal_tac "\<not>(length path\<le>Suc m)" )
  prefer 2 apply arith
 apply(simp add: min_def)
 apply clarify
 apply(erule_tac x = "i" in allE)
 apply simp
 apply clarify
 apply(case_tac "R=j")
  apply(force simp add: nth_list_update)
 apply(force simp add: nth_list_update)
--{* the changed edge is not part of the path *}
apply(rule_tac x = "path" in exI)
apply simp
apply clarify
apply(erule_tac x = "i" in allE)
apply clarify
apply(case_tac "R=j")
 apply(erule_tac x = "i" in allE)
 apply simp
apply(force simp add: nth_list_update)
done

subsubsection{* Graph 4 *}

lemma Graph4: 
  "\<lbrakk>T \<in> Reach E; Roots\<subseteq>Blacks M; I\<le>length E; T<length M; R<length E; 
  \<forall>i<I. \<not>BtoW(E!i,M); R<I; M!fst(E!R)=Black; M!T\<noteq>Black\<rbrakk> \<Longrightarrow> 
  (\<exists>r. I\<le>r \<and> r<length E \<and> BtoW(E[R:=(fst(E!R),T)]!r,M))"
apply (unfold Reach_def)
apply simp
apply(erule disjE)
 prefer 2 apply force
apply clarify
--{* there exist a black node in the path to T *}
apply(case_tac "\<exists>m<length path. M!(path!m)=Black")
 apply(erule exE)
 apply(drule_tac P = "\<lambda>m. m<length path \<and> M!(path!m)=Black" in Ex_first_occurrence)
 apply clarify
 apply(case_tac "ma")
  apply force
 apply simp
 apply(case_tac "length path")
  apply force
 apply simp
 apply(erule_tac P = "\<lambda>i. i < nata \<longrightarrow> ?P i" and x = "nat" in allE)
 apply simp
 apply clarify
 apply(erule_tac P = "\<lambda>i. i < Suc nat \<longrightarrow> ?P i" and x = "nat" in allE)
 apply simp
 apply(case_tac "j<I")
  apply(erule_tac x = "j" in allE)
  apply force
 apply(rule_tac x = "j" in exI)
 apply(force  simp add: nth_list_update)
apply simp
apply(rotate_tac -1)
apply(erule_tac x = "length path - 1" in allE)
apply(case_tac "length path")
 apply force
apply force
done

subsubsection {* Graph 5 *}

lemma Graph5: 
  "\<lbrakk> T \<in> Reach E ; Roots \<subseteq> Blacks M; \<forall>i<R. \<not>BtoW(E!i,M); T<length M; 
    R<length E; M!fst(E!R)=Black; M!snd(E!R)=Black; M!T \<noteq> Black\<rbrakk> 
   \<Longrightarrow> (\<exists>r. R<r \<and> r<length E \<and> BtoW(E[R:=(fst(E!R),T)]!r,M))"
apply (unfold Reach_def)
apply simp
apply(erule disjE)
 prefer 2 apply force
apply clarify
--{* there exist a black node in the path to T*}
apply(case_tac "\<exists>m<length path. M!(path!m)=Black")
 apply(erule exE)
 apply(drule_tac P = "\<lambda>m. m<length path \<and> M!(path!m)=Black" in Ex_first_occurrence)
 apply clarify
 apply(case_tac "ma")
  apply force
 apply simp
 apply(case_tac "length path")
  apply force
 apply simp
 apply(erule_tac P = "\<lambda>i. i < nata \<longrightarrow> ?P i" and x = "nat" in allE)
 apply simp
 apply clarify
 apply(erule_tac P = "\<lambda>i. i < Suc nat \<longrightarrow> ?P i" and x = "nat" in allE)
 apply simp
 apply(case_tac "j\<le>R")
  apply(drule le_imp_less_or_eq)
  apply(erule disjE)
   apply(erule allE , erule (1) notE impE)
   apply force
  apply force
 apply(rule_tac x = "j" in exI)
 apply(force  simp add: nth_list_update)
apply simp
apply(rotate_tac -1)
apply(erule_tac x = "length path - 1" in allE)
apply(case_tac "length path")
 apply force
apply force
done

subsubsection {* Other lemmas about graphs *}

lemma Graph6: 
 "\<lbrakk>Proper_Edges(M,E); R<length E ; T<length M\<rbrakk> \<Longrightarrow> Proper_Edges(M,E[R:=(fst(E!R),T)])"
apply (unfold Proper_Edges_def)
 apply(force  simp add: nth_list_update)
done

lemma Graph7: 
 "\<lbrakk>Proper_Edges(M,E)\<rbrakk> \<Longrightarrow> Proper_Edges(M[T:=a],E)"
apply (unfold Proper_Edges_def)
apply force
done

lemma Graph8: 
 "\<lbrakk>Proper_Roots(M)\<rbrakk> \<Longrightarrow> Proper_Roots(M[T:=a])"
apply (unfold Proper_Roots_def)
apply force
done

text{* Some specific lemmata for the verification of garbage collection algorithms. *}

lemma Graph9: "j<length M \<Longrightarrow> Blacks M\<subseteq>Blacks (M[j := Black])"
apply (unfold Blacks_def)
 apply(force simp add: nth_list_update)
done

lemma Graph10 [rule_format (no_asm)]: "\<forall>i. M!i=a \<longrightarrow>M[i:=a]=M"
apply(induct_tac "M")
apply auto
apply(case_tac "i")
apply auto
done

lemma Graph11 [rule_format (no_asm)]: 
  "\<lbrakk> M!j\<noteq>Black;j<length M\<rbrakk> \<Longrightarrow> Blacks M \<subset> Blacks (M[j := Black])"
apply (unfold Blacks_def)
apply(rule psubsetI)
 apply(force simp add: nth_list_update)
apply safe
apply(erule_tac c = "j" in equalityCE)
apply auto
done

lemma Graph12: "\<lbrakk>a\<subseteq>Blacks M;j<length M\<rbrakk> \<Longrightarrow> a\<subseteq>Blacks (M[j := Black])"
apply (unfold Blacks_def)
apply(force simp add: nth_list_update)
done

lemma Graph13: "\<lbrakk>a\<subset> Blacks M;j<length M\<rbrakk> \<Longrightarrow> a \<subset> Blacks (M[j := Black])"
apply (unfold Blacks_def)
apply(erule psubset_subset_trans)
apply(force simp add: nth_list_update)
done

declare Graph_defs [simp del]

end
