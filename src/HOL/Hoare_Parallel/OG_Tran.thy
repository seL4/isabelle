
header {* \section{Operational Semantics} *}

theory OG_Tran imports OG_Com begin

type_synonym 'a ann_com_op = "('a ann_com) option"
type_synonym 'a ann_triple_op = "('a ann_com_op \<times> 'a assn)"
  
primrec com :: "'a ann_triple_op \<Rightarrow> 'a ann_com_op" where
  "com (c, q) = c"

primrec post :: "'a ann_triple_op \<Rightarrow> 'a assn" where
  "post (c, q) = q"

definition All_None :: "'a ann_triple_op list \<Rightarrow> bool" where
  "All_None Ts \<equiv> \<forall>(c, q) \<in> set Ts. c = None"

subsection {* The Transition Relation *}

inductive_set
  ann_transition :: "(('a ann_com_op \<times> 'a) \<times> ('a ann_com_op \<times> 'a)) set"        
  and transition :: "(('a com \<times> 'a) \<times> ('a com \<times> 'a)) set"
  and ann_transition' :: "('a ann_com_op \<times> 'a) \<Rightarrow> ('a ann_com_op \<times> 'a) \<Rightarrow> bool"
    ("_ -1\<rightarrow> _"[81,81] 100)
  and transition' :: "('a com \<times> 'a) \<Rightarrow> ('a com \<times> 'a) \<Rightarrow> bool"
    ("_ -P1\<rightarrow> _"[81,81] 100)
  and transitions :: "('a com \<times> 'a) \<Rightarrow> ('a com \<times> 'a) \<Rightarrow> bool"
    ("_ -P*\<rightarrow> _"[81,81] 100)
where
  "con_0 -1\<rightarrow> con_1 \<equiv> (con_0, con_1) \<in> ann_transition"
| "con_0 -P1\<rightarrow> con_1 \<equiv> (con_0, con_1) \<in> transition"
| "con_0 -P*\<rightarrow> con_1 \<equiv> (con_0, con_1) \<in> transition\<^sup>*"

| AnnBasic:  "(Some (AnnBasic r f), s) -1\<rightarrow> (None, f s)"

| AnnSeq1: "(Some c0, s) -1\<rightarrow> (None, t) \<Longrightarrow> 
               (Some (AnnSeq c0 c1), s) -1\<rightarrow> (Some c1, t)"
| AnnSeq2: "(Some c0, s) -1\<rightarrow> (Some c2, t) \<Longrightarrow> 
               (Some (AnnSeq c0 c1), s) -1\<rightarrow> (Some (AnnSeq c2 c1), t)"

| AnnCond1T: "s \<in> b  \<Longrightarrow> (Some (AnnCond1 r b c1 c2), s) -1\<rightarrow> (Some c1, s)"
| AnnCond1F: "s \<notin> b \<Longrightarrow> (Some (AnnCond1 r b c1 c2), s) -1\<rightarrow> (Some c2, s)"

| AnnCond2T: "s \<in> b  \<Longrightarrow> (Some (AnnCond2 r b c), s) -1\<rightarrow> (Some c, s)"
| AnnCond2F: "s \<notin> b \<Longrightarrow> (Some (AnnCond2 r b c), s) -1\<rightarrow> (None, s)"

| AnnWhileF: "s \<notin> b \<Longrightarrow> (Some (AnnWhile r b i c), s) -1\<rightarrow> (None, s)"
| AnnWhileT: "s \<in> b  \<Longrightarrow> (Some (AnnWhile r b i c), s) -1\<rightarrow> 
                         (Some (AnnSeq c (AnnWhile i b i c)), s)"

| AnnAwait: "\<lbrakk> s \<in> b; atom_com c; (c, s) -P*\<rightarrow> (Parallel [], t) \<rbrakk> \<Longrightarrow>
                   (Some (AnnAwait r b c), s) -1\<rightarrow> (None, t)" 

| Parallel: "\<lbrakk> i<length Ts; Ts!i = (Some c, q); (Some c, s) -1\<rightarrow> (r, t) \<rbrakk>
              \<Longrightarrow> (Parallel Ts, s) -P1\<rightarrow> (Parallel (Ts [i:=(r, q)]), t)"

| Basic:  "(Basic f, s) -P1\<rightarrow> (Parallel [], f s)"

| Seq1:   "All_None Ts \<Longrightarrow> (Seq (Parallel Ts) c, s) -P1\<rightarrow> (c, s)"
| Seq2:   "(c0, s) -P1\<rightarrow> (c2, t) \<Longrightarrow> (Seq c0 c1, s) -P1\<rightarrow> (Seq c2 c1, t)"

| CondT: "s \<in> b \<Longrightarrow> (Cond b c1 c2, s) -P1\<rightarrow> (c1, s)"
| CondF: "s \<notin> b \<Longrightarrow> (Cond b c1 c2, s) -P1\<rightarrow> (c2, s)"

| WhileF: "s \<notin> b \<Longrightarrow> (While b i c, s) -P1\<rightarrow> (Parallel [], s)"
| WhileT: "s \<in> b \<Longrightarrow> (While b i c, s) -P1\<rightarrow> (Seq c (While b i c), s)"

monos "rtrancl_mono"

text {* The corresponding abbreviations are: *}

abbreviation
  ann_transition_n :: "('a ann_com_op \<times> 'a) \<Rightarrow> nat \<Rightarrow> ('a ann_com_op \<times> 'a) 
                           \<Rightarrow> bool"  ("_ -_\<rightarrow> _"[81,81] 100)  where
  "con_0 -n\<rightarrow> con_1 \<equiv> (con_0, con_1) \<in> ann_transition ^^ n"

abbreviation
  ann_transitions :: "('a ann_com_op \<times> 'a) \<Rightarrow> ('a ann_com_op \<times> 'a) \<Rightarrow> bool"
                           ("_ -*\<rightarrow> _"[81,81] 100)  where
  "con_0 -*\<rightarrow> con_1 \<equiv> (con_0, con_1) \<in> ann_transition\<^sup>*"

abbreviation
  transition_n :: "('a com \<times> 'a) \<Rightarrow> nat \<Rightarrow> ('a com \<times> 'a) \<Rightarrow> bool"  
                          ("_ -P_\<rightarrow> _"[81,81,81] 100)  where
  "con_0 -Pn\<rightarrow> con_1 \<equiv> (con_0, con_1) \<in> transition ^^ n"

subsection {* Definition of Semantics *}

definition ann_sem :: "'a ann_com \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "ann_sem c \<equiv> \<lambda>s. {t. (Some c, s) -*\<rightarrow> (None, t)}"

definition ann_SEM :: "'a ann_com \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "ann_SEM c S \<equiv> \<Union>ann_sem c ` S"  

definition sem :: "'a com \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "sem c \<equiv> \<lambda>s. {t. \<exists>Ts. (c, s) -P*\<rightarrow> (Parallel Ts, t) \<and> All_None Ts}"

definition SEM :: "'a com \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "SEM c S \<equiv> \<Union>sem c ` S "

abbreviation Omega :: "'a com"    ("\<Omega>" 63)
  where "\<Omega> \<equiv> While UNIV UNIV (Basic id)"

primrec fwhile :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> nat \<Rightarrow> 'a com" where
    "fwhile b c 0 = \<Omega>"
  | "fwhile b c (Suc n) = Cond b (Seq c (fwhile b c n)) (Basic id)"

subsubsection {* Proofs *}

declare ann_transition_transition.intros [intro]
inductive_cases transition_cases: 
    "(Parallel T,s) -P1\<rightarrow> t"  
    "(Basic f, s) -P1\<rightarrow> t"
    "(Seq c1 c2, s) -P1\<rightarrow> t" 
    "(Cond b c1 c2, s) -P1\<rightarrow> t"
    "(While b i c, s) -P1\<rightarrow> t"

lemma Parallel_empty_lemma [rule_format (no_asm)]: 
  "(Parallel [],s) -Pn\<rightarrow> (Parallel Ts,t) \<longrightarrow> Ts=[] \<and> n=0 \<and> s=t"
apply(induct n)
 apply(simp (no_asm))
apply clarify
apply(drule relpow_Suc_D2)
apply(force elim:transition_cases)
done

lemma Parallel_AllNone_lemma [rule_format (no_asm)]: 
 "All_None Ss \<longrightarrow> (Parallel Ss,s) -Pn\<rightarrow> (Parallel Ts,t) \<longrightarrow> Ts=Ss \<and> n=0 \<and> s=t"
apply(induct "n")
 apply(simp (no_asm))
apply clarify
apply(drule relpow_Suc_D2)
apply clarify
apply(erule transition_cases,simp_all)
apply(force dest:nth_mem simp add:All_None_def)
done

lemma Parallel_AllNone: "All_None Ts \<Longrightarrow> (SEM (Parallel Ts) X) = X"
apply (unfold SEM_def sem_def)
apply auto
apply(drule rtrancl_imp_UN_relpow)
apply clarify
apply(drule Parallel_AllNone_lemma)
apply auto
done

lemma Parallel_empty: "Ts=[] \<Longrightarrow> (SEM (Parallel Ts) X) = X"
apply(rule Parallel_AllNone)
apply(simp add:All_None_def)
done

text {* Set of lemmas from Apt and Olderog "Verification of sequential
and concurrent programs", page 63. *}

lemma L3_5i: "X\<subseteq>Y \<Longrightarrow> SEM c X \<subseteq> SEM c Y" 
apply (unfold SEM_def)
apply force
done

lemma L3_5ii_lemma1: 
 "\<lbrakk> (c1, s1) -P*\<rightarrow> (Parallel Ts, s2); All_None Ts;  
  (c2, s2) -P*\<rightarrow> (Parallel Ss, s3); All_None Ss \<rbrakk> 
 \<Longrightarrow> (Seq c1 c2, s1) -P*\<rightarrow> (Parallel Ss, s3)"
apply(erule converse_rtrancl_induct2)
apply(force intro:converse_rtrancl_into_rtrancl)+
done

lemma L3_5ii_lemma2 [rule_format (no_asm)]: 
 "\<forall>c1 c2 s t. (Seq c1 c2, s) -Pn\<rightarrow> (Parallel Ts, t) \<longrightarrow>  
  (All_None Ts) \<longrightarrow> (\<exists>y m Rs. (c1,s) -P*\<rightarrow> (Parallel Rs, y) \<and> 
  (All_None Rs) \<and> (c2, y) -Pm\<rightarrow> (Parallel Ts, t) \<and>  m \<le> n)"
apply(induct "n")
 apply(force)
apply(safe dest!: relpow_Suc_D2)
apply(erule transition_cases,simp_all)
 apply (fast intro!: le_SucI)
apply (fast intro!: le_SucI elim!: relpow_imp_rtrancl converse_rtrancl_into_rtrancl)
done

lemma L3_5ii_lemma3: 
 "\<lbrakk>(Seq c1 c2,s) -P*\<rightarrow> (Parallel Ts,t); All_None Ts\<rbrakk> \<Longrightarrow> 
    (\<exists>y Rs. (c1,s) -P*\<rightarrow> (Parallel Rs,y) \<and> All_None Rs 
   \<and> (c2,y) -P*\<rightarrow> (Parallel Ts,t))"
apply(drule rtrancl_imp_UN_relpow)
apply(fast dest: L3_5ii_lemma2 relpow_imp_rtrancl)
done

lemma L3_5ii: "SEM (Seq c1 c2) X = SEM c2 (SEM c1 X)"
apply (unfold SEM_def sem_def)
apply auto
 apply(fast dest: L3_5ii_lemma3)
apply(fast elim: L3_5ii_lemma1)
done

lemma L3_5iii: "SEM (Seq (Seq c1 c2) c3) X = SEM (Seq c1 (Seq c2 c3)) X"
apply (simp (no_asm) add: L3_5ii)
done

lemma L3_5iv:
 "SEM (Cond b c1 c2) X = (SEM c1 (X \<inter> b)) Un (SEM c2 (X \<inter> (-b)))"
apply (unfold SEM_def sem_def)
apply auto
apply(erule converse_rtranclE)
 prefer 2
 apply (erule transition_cases,simp_all)
  apply(fast intro: converse_rtrancl_into_rtrancl elim: transition_cases)+
done


lemma  L3_5v_lemma1[rule_format]: 
 "(S,s) -Pn\<rightarrow> (T,t) \<longrightarrow> S=\<Omega> \<longrightarrow> (\<not>(\<exists>Rs. T=(Parallel Rs) \<and> All_None Rs))"
apply (unfold UNIV_def)
apply(rule nat_less_induct)
apply safe
apply(erule relpow_E2)
 apply simp_all
apply(erule transition_cases)
 apply simp_all
apply(erule relpow_E2)
 apply(simp add: Id_def)
apply(erule transition_cases,simp_all)
apply clarify
apply(erule transition_cases,simp_all)
apply(erule relpow_E2,simp)
apply clarify
apply(erule transition_cases)
 apply simp+
    apply clarify
    apply(erule transition_cases)
apply simp_all
done

lemma L3_5v_lemma2: "\<lbrakk>(\<Omega>, s) -P*\<rightarrow> (Parallel Ts, t); All_None Ts \<rbrakk> \<Longrightarrow> False"
apply(fast dest: rtrancl_imp_UN_relpow L3_5v_lemma1)
done

lemma L3_5v_lemma3: "SEM (\<Omega>) S = {}"
apply (unfold SEM_def sem_def)
apply(fast dest: L3_5v_lemma2)
done

lemma L3_5v_lemma4 [rule_format]: 
 "\<forall>s. (While b i c, s) -Pn\<rightarrow> (Parallel Ts, t) \<longrightarrow> All_None Ts \<longrightarrow>  
  (\<exists>k. (fwhile b c k, s) -P*\<rightarrow> (Parallel Ts, t))"
apply(rule nat_less_induct)
apply safe
apply(erule relpow_E2)
 apply safe
apply(erule transition_cases,simp_all)
 apply (rule_tac x = "1" in exI)
 apply(force dest: Parallel_empty_lemma intro: converse_rtrancl_into_rtrancl simp add: Id_def)
apply safe
apply(drule L3_5ii_lemma2)
 apply safe
apply(drule le_imp_less_Suc)
apply (erule allE , erule impE,assumption)
apply (erule allE , erule impE, assumption)
apply safe
apply (rule_tac x = "k+1" in exI)
apply(simp (no_asm))
apply(rule converse_rtrancl_into_rtrancl)
 apply fast
apply(fast elim: L3_5ii_lemma1)
done

lemma L3_5v_lemma5 [rule_format]: 
 "\<forall>s. (fwhile b c k, s) -P*\<rightarrow> (Parallel Ts, t) \<longrightarrow> All_None Ts \<longrightarrow>  
  (While b i c, s) -P*\<rightarrow> (Parallel Ts,t)"
apply(induct "k")
 apply(force dest: L3_5v_lemma2)
apply safe
apply(erule converse_rtranclE)
 apply simp_all
apply(erule transition_cases,simp_all)
 apply(rule converse_rtrancl_into_rtrancl)
  apply(fast)
 apply(fast elim!: L3_5ii_lemma1 dest: L3_5ii_lemma3)
apply(drule rtrancl_imp_UN_relpow)
apply clarify
apply(erule relpow_E2)
 apply simp_all
apply(erule transition_cases,simp_all)
apply(fast dest: Parallel_empty_lemma)
done

lemma L3_5v: "SEM (While b i c) = (\<lambda>x. (\<Union>k. SEM (fwhile b c k) x))"
apply(rule ext)
apply (simp add: SEM_def sem_def)
apply safe
 apply(drule rtrancl_imp_UN_relpow,simp)
 apply clarify
 apply(fast dest:L3_5v_lemma4)
apply(fast intro: L3_5v_lemma5)
done

section {* Validity of Correctness Formulas *}

definition com_validity :: "'a assn \<Rightarrow> 'a com \<Rightarrow> 'a assn \<Rightarrow> bool" ("(3\<parallel>= _// _//_)" [90,55,90] 50) where
  "\<parallel>= p c q \<equiv> SEM c p \<subseteq> q"

definition ann_com_validity :: "'a ann_com \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile> _ _" [60,90] 45) where
  "\<Turnstile> c q \<equiv> ann_SEM c (pre c) \<subseteq> q"

end