
header {* \section{The Proof System} *}

theory OG_Hoare = OG_Tran:

consts assertions :: "'a ann_com \<Rightarrow> ('a assn) set"
primrec
  "assertions (AnnBasic r f) = {r}"
  "assertions (AnnSeq c1 c2) = assertions c1 \<union> assertions c2"
  "assertions (AnnCond1 r b c1 c2) = {r} \<union> assertions c1 \<union> assertions c2"
  "assertions (AnnCond2 r b c) = {r} \<union> assertions c"
  "assertions (AnnWhile r b i c) = {r, i} \<union> assertions c"
  "assertions (AnnAwait r b c) = {r}" 

consts atomics :: "'a ann_com \<Rightarrow> ('a assn \<times> 'a com) set"       
primrec
  "atomics (AnnBasic r f) = {(r, Basic f)}"
  "atomics (AnnSeq c1 c2) = atomics c1 \<union> atomics c2"
  "atomics (AnnCond1 r b c1 c2) = atomics c1 \<union> atomics c2"
  "atomics (AnnCond2 r b c) = atomics c"
  "atomics (AnnWhile r b i c) = atomics c" 
  "atomics (AnnAwait r b c) = {(r \<inter> b, c)}"

consts com :: "'a ann_triple_op \<Rightarrow> 'a ann_com_op"
primrec "com (c, q) = c"

consts post :: "'a ann_triple_op \<Rightarrow> 'a assn"
primrec "post (c, q) = q"

constdefs  interfree_aux :: "('a ann_com_op \<times> 'a assn \<times> 'a ann_com_op) \<Rightarrow> bool"
  "interfree_aux \<equiv> \<lambda>(co, q, co'). co'= None \<or>  
                    (\<forall>(r,a) \<in> atomics (the co'). \<parallel>= (q \<inter> r) a q \<and>
                    (co = None \<or> (\<forall>p \<in> assertions (the co). \<parallel>= (p \<inter> r) a p)))"

constdefs interfree :: "(('a ann_triple_op) list) \<Rightarrow> bool" 
  "interfree Ts \<equiv> \<forall>i j. i < length Ts \<and> j < length Ts \<and> i \<noteq> j \<longrightarrow> 
                         interfree_aux (com (Ts!i), post (Ts!i), com (Ts!j)) "

consts ann_hoare :: "('a ann_com \<times> 'a assn) set" 
syntax "_ann_hoare" :: "'a ann_com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(2\<turnstile> _// _)" [60,90] 45)
translations "\<turnstile> c q" \<rightleftharpoons> "(c, q) \<in> ann_hoare"

consts oghoare :: "('a assn \<times> 'a com \<times> 'a assn) set"
syntax "_oghoare" :: "'a assn \<Rightarrow> 'a com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(3\<parallel>- _//_//_)" [90,55,90] 50)
translations "\<parallel>- p c q" \<rightleftharpoons> "(p, c, q) \<in> oghoare"

inductive oghoare ann_hoare
intros
  AnnBasic: "r \<subseteq> {s. f s \<in> q} \<Longrightarrow> \<turnstile> (AnnBasic r f) q"

  AnnSeq:   "\<lbrakk> \<turnstile> c0 pre c1; \<turnstile> c1 q \<rbrakk> \<Longrightarrow> \<turnstile> (AnnSeq c0 c1) q"
  
  AnnCond1: "\<lbrakk> r \<inter> b \<subseteq> pre c1; \<turnstile> c1 q; r \<inter> -b \<subseteq> pre c2; \<turnstile> c2 q\<rbrakk> 
              \<Longrightarrow> \<turnstile> (AnnCond1 r b c1 c2) q"
  AnnCond2: "\<lbrakk> r \<inter> b \<subseteq> pre c; \<turnstile> c q; r \<inter> -b \<subseteq> q \<rbrakk> \<Longrightarrow> \<turnstile> (AnnCond2 r b c) q"
  
  AnnWhile: "\<lbrakk> r \<subseteq> i; i \<inter> b \<subseteq> pre c; \<turnstile> c i; i \<inter> -b \<subseteq> q \<rbrakk> 
              \<Longrightarrow> \<turnstile> (AnnWhile r b i c) q"
  
  AnnAwait:  "\<lbrakk> atom_com c; \<parallel>- (r \<inter> b) c q \<rbrakk> \<Longrightarrow> \<turnstile> (AnnAwait r b c) q"
  
  AnnConseq: "\<lbrakk>\<turnstile> c q; q \<subseteq> q' \<rbrakk> \<Longrightarrow> \<turnstile> c q'"


  Parallel: "\<lbrakk> \<forall>i<length Ts. \<exists>c q. Ts!i = (Some c, q) \<and> \<turnstile> c q; interfree Ts \<rbrakk>
	   \<Longrightarrow> \<parallel>- (\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts!i)))) 
                     Parallel Ts 
                  (\<Inter>i\<in>{i. i<length Ts}. post(Ts!i))"

  Basic:   "\<parallel>- {s. f s \<in>q} (Basic f) q"
  
  Seq:    "\<lbrakk> \<parallel>- p c1 r; \<parallel>- r c2 q \<rbrakk> \<Longrightarrow> \<parallel>- p (Seq c1 c2) q "

  Cond:   "\<lbrakk> \<parallel>- (p \<inter> b) c1 q; \<parallel>- (p \<inter> -b) c2 q \<rbrakk> \<Longrightarrow> \<parallel>- p (Cond b c1 c2) q"

  While:  "\<lbrakk> \<parallel>- (p \<inter> b) c p \<rbrakk> \<Longrightarrow> \<parallel>- p (While b i c) (p \<inter> -b)"

  Conseq: "\<lbrakk> p' \<subseteq> p; \<parallel>- p c q ; q \<subseteq> q' \<rbrakk> \<Longrightarrow> \<parallel>- p' c q'"
					    
section {* Soundness *}
(* In the version Isabelle-10-Sep-1999: HOL: The THEN and ELSE
parts of conditional expressions (if P then x else y) are no longer
simplified.  (This allows the simplifier to unfold recursive
functional programs.)  To restore the old behaviour, we declare
@{text "lemmas [cong del] = if_weak_cong"}. *)

lemmas [cong del] = if_weak_cong

lemmas ann_hoare_induct = oghoare_ann_hoare.induct [THEN conjunct2]
lemmas oghoare_induct = oghoare_ann_hoare.induct [THEN conjunct1]

lemmas AnnBasic = oghoare_ann_hoare.AnnBasic
lemmas AnnSeq = oghoare_ann_hoare.AnnSeq
lemmas AnnCond1 = oghoare_ann_hoare.AnnCond1
lemmas AnnCond2 = oghoare_ann_hoare.AnnCond2
lemmas AnnWhile = oghoare_ann_hoare.AnnWhile
lemmas AnnAwait = oghoare_ann_hoare.AnnAwait
lemmas AnnConseq = oghoare_ann_hoare.AnnConseq

lemmas Parallel = oghoare_ann_hoare.Parallel
lemmas Basic = oghoare_ann_hoare.Basic
lemmas Seq = oghoare_ann_hoare.Seq
lemmas Cond = oghoare_ann_hoare.Cond
lemmas While = oghoare_ann_hoare.While
lemmas Conseq = oghoare_ann_hoare.Conseq

subsection {* Soundness of the System for Atomic Programs *}

lemma Basic_ntran [rule_format]: 
 "(Basic f, s) -Pn\<rightarrow> (Parallel Ts, t) \<longrightarrow> All_None Ts \<longrightarrow> t = f s"
apply(induct "n")
 apply(simp (no_asm))
apply(fast dest: rel_pow_Suc_D2 Parallel_empty_lemma elim: transition_cases)
done

lemma SEM_fwhile: "SEM S (p \<inter> b) \<subseteq> p \<Longrightarrow> SEM (fwhile b S k) p \<subseteq> (p \<inter> -b)"
apply (induct "k")
 apply(simp (no_asm) add: L3_5v_lemma3)
apply(simp (no_asm) add: L3_5iv L3_5ii Parallel_empty)
apply(rule Un_least)
 apply(rule subset_trans)
  prefer 2 apply simp
 apply(erule L3_5i)
apply(simp add: SEM_def sem_def id_def)
apply clarify
apply(drule rtrancl_imp_UN_rel_pow)
apply clarify
apply(drule Basic_ntran)
 apply fast+
done

lemma atom_hoare_sound [rule_format (no_asm)]: 
 " \<parallel>- p c q \<longrightarrow> atom_com(c) \<longrightarrow> \<parallel>= p c q"
apply (unfold com_validity_def)
apply(rule oghoare_induct)
apply simp_all
--{*Basic*}
    apply(simp add: SEM_def sem_def)
    apply(fast dest: rtrancl_imp_UN_rel_pow Basic_ntran)
--{* Seq *}
   apply(rule impI)
   apply(rule subset_trans)
    prefer 2 apply simp
   apply(simp add: L3_5ii L3_5i)
--{* Cond *}
  apply(rule impI)
  apply(simp add: L3_5iv)
  apply(erule Un_least)
  apply assumption
--{* While *}
 apply(rule impI)
 apply(simp add: L3_5v)
 apply(rule UN_least)
 apply(drule SEM_fwhile)
 apply assumption
--{* Conseq *}
apply(simp add: SEM_def sem_def)
apply force
done
    
subsection {* Soundness of the System for Component Programs *}

inductive_cases ann_transition_cases:
    "(None,s) -1\<rightarrow> t"
    "(Some (AnnBasic r f),s) -1\<rightarrow> t"
    "(Some (AnnSeq c1 c2), s) -1\<rightarrow> t" 
    "(Some (AnnCond1 r b c1 c2), s) -1\<rightarrow> t"
    "(Some (AnnCond2 r b c), s) -1\<rightarrow> t"
    "(Some (AnnWhile r b I c), s) -1\<rightarrow> t"
    "(Some (AnnAwait r b c),s) -1\<rightarrow> t"

text {* Strong Soundness for Component Programs:*}

lemma ann_hoare_case_analysis [rule_format]: "\<turnstile> C q' \<longrightarrow>  
  ((\<forall>r f. C = AnnBasic r f \<longrightarrow> (\<exists>q. r \<subseteq> {s. f s \<in> q} \<and> q \<subseteq> q')) \<and>  
  (\<forall>c0 c1. C = AnnSeq c0 c1 \<longrightarrow> (\<exists>q. q \<subseteq> q' \<and> \<turnstile> c0 pre c1 \<and> \<turnstile> c1 q)) \<and>  
  (\<forall>r b c1 c2. C = AnnCond1 r b c1 c2 \<longrightarrow> (\<exists>q. q \<subseteq> q' \<and>  
  r \<inter> b \<subseteq> pre c1 \<and> \<turnstile> c1 q \<and> r \<inter> -b \<subseteq> pre c2 \<and> \<turnstile> c2 q)) \<and>  
  (\<forall>r b c. C = AnnCond2 r b c \<longrightarrow> 
  (\<exists>q. q \<subseteq> q' \<and> r \<inter> b \<subseteq> pre c  \<and> \<turnstile> c q \<and> r \<inter> -b \<subseteq> q)) \<and>  
  (\<forall>r i b c. C = AnnWhile r b i c \<longrightarrow>  
  (\<exists>q. q \<subseteq> q' \<and> r \<subseteq> i \<and> i \<inter> b \<subseteq> pre c \<and> \<turnstile> c i \<and> i \<inter> -b \<subseteq> q)) \<and>  
  (\<forall>r b c. C = AnnAwait r b c \<longrightarrow> (\<exists>q. q \<subseteq> q' \<and> \<parallel>- (r \<inter> b) c q)))"
apply(rule ann_hoare_induct)
apply simp_all
 apply(rule_tac x=q in exI,simp)+
apply(rule conjI,clarify,simp,clarify,rule_tac x=qa in exI,fast)+
apply(clarify,simp,clarify,rule_tac x=qa in exI,fast)
done

lemma Help: "(transition \<inter> {(v,v,u). True}) = (transition)"
apply force
done

lemma Strong_Soundness_aux_aux [rule_format]: 
 "(co, s) -1\<rightarrow> (co', t) \<longrightarrow> (\<forall>c. co = Some c \<longrightarrow> s\<in> pre c \<longrightarrow> 
 (\<forall>q. \<turnstile> c q \<longrightarrow> (if co' = None then t\<in>q else t \<in> pre(the co') \<and> \<turnstile> (the co') q )))"
apply(rule ann_transition_transition.induct [THEN conjunct1])
apply simp_all 
--{* Basic *}
         apply clarify
         apply(frule ann_hoare_case_analysis)
         apply force
--{* Seq *}
        apply clarify
        apply(frule ann_hoare_case_analysis,simp)
        apply(fast intro: AnnConseq)
       apply clarify
       apply(frule ann_hoare_case_analysis,simp)
       apply clarify
       apply(rule conjI)
        apply force
       apply(rule AnnSeq,simp)
       apply(fast intro: AnnConseq)
--{* Cond1 *}
      apply clarify
      apply(frule ann_hoare_case_analysis,simp)
      apply(fast intro: AnnConseq)
     apply clarify
     apply(frule ann_hoare_case_analysis,simp)
     apply(fast intro: AnnConseq)
--{* Cond2 *}
    apply clarify
    apply(frule ann_hoare_case_analysis,simp)
    apply(fast intro: AnnConseq)
   apply clarify
   apply(frule ann_hoare_case_analysis,simp)
   apply(fast intro: AnnConseq)
--{* While *}
  apply clarify
  apply(frule ann_hoare_case_analysis,simp)
  apply force
 apply clarify
 apply(frule ann_hoare_case_analysis,simp)
 apply auto
 apply(rule AnnSeq)
  apply simp
 apply(rule AnnWhile)
  apply simp_all
 apply(fast)
--{* Await *}
apply(frule ann_hoare_case_analysis,simp)
apply clarify
apply(drule atom_hoare_sound)
 apply simp 
apply(simp add: com_validity_def SEM_def sem_def)
apply(simp add: Help All_None_def)
apply force
done

lemma Strong_Soundness_aux: "\<lbrakk> (Some c, s) -*\<rightarrow> (co, t); s \<in> pre c; \<turnstile> c q \<rbrakk>  
  \<Longrightarrow> if co = None then t \<in> q else t \<in> pre (the co) \<and> \<turnstile> (the co) q"
apply(erule rtrancl_induct2)
 apply simp
apply(case_tac "a")
 apply(fast elim: ann_transition_cases)
apply(erule Strong_Soundness_aux_aux)
 apply simp
apply simp_all
done

lemma Strong_Soundness: "\<lbrakk> (Some c, s)-*\<rightarrow>(co, t); s \<in> pre c; \<turnstile> c q \<rbrakk>  
  \<Longrightarrow> if co = None then t\<in>q else t \<in> pre (the co)"
apply(force dest:Strong_Soundness_aux)
done

lemma ann_hoare_sound: "\<turnstile> c q  \<Longrightarrow> \<Turnstile> c q"
apply (unfold ann_com_validity_def ann_SEM_def ann_sem_def)
apply clarify
apply(drule Strong_Soundness)
apply simp_all
done

subsection {* Soundness of the System for Parallel Programs *}

lemma Parallel_length_post_P1: "(Parallel Ts,s) -P1\<rightarrow> (R', t) \<Longrightarrow>  
  (\<exists>Rs. R' = (Parallel Rs) \<and> (length Rs) = (length Ts) \<and>
  (\<forall>i. i<length Ts \<longrightarrow> post(Rs ! i) = post(Ts ! i)))"
apply(erule transition_cases)
apply simp
apply clarify
apply(case_tac "i=ia")
apply simp+
done

lemma Parallel_length_post_PStar: "(Parallel Ts,s) -P*\<rightarrow> (R',t) \<Longrightarrow>   
  (\<exists>Rs. R' = (Parallel Rs) \<and> (length Rs) = (length Ts) \<and>  
  (\<forall>i. i<length Ts \<longrightarrow> post(Ts ! i) = post(Rs ! i)))"
apply(erule rtrancl_induct2)
 apply(simp_all)
apply clarify
apply simp
apply(drule Parallel_length_post_P1)
apply auto
done

lemma assertions_lemma: "pre c \<in> assertions c"
apply(rule ann_com_com.induct [THEN conjunct1])
apply auto
done

lemma interfree_aux1 [rule_format]: 
  "(c,s) -1\<rightarrow> (r,t)  \<longrightarrow> (interfree_aux(c1, q1, c) \<longrightarrow> interfree_aux(c1, q1, r))"
apply (rule ann_transition_transition.induct [THEN conjunct1])
apply(safe)
prefer 13
apply (rule TrueI)
apply (simp_all add:interfree_aux_def)
apply force+
done

lemma interfree_aux2 [rule_format]: 
  "(c,s) -1\<rightarrow> (r,t) \<longrightarrow> (interfree_aux(c, q, a)  \<longrightarrow> interfree_aux(r, q, a) )"
apply (rule ann_transition_transition.induct [THEN conjunct1])
apply(force simp add:interfree_aux_def)+
done

lemma interfree_lemma: "\<lbrakk> (Some c, s) -1\<rightarrow> (r, t);interfree Ts ; i<length Ts;  
           Ts!i = (Some c, q) \<rbrakk> \<Longrightarrow> interfree (Ts[i:= (r, q)])"
apply(simp add: interfree_def)
apply clarify
apply(case_tac "i=j")
 apply(drule_tac t = "ia" in not_sym)
 apply simp_all
apply(force elim: interfree_aux1)
apply(force elim: interfree_aux2 simp add:nth_list_update)
done

text {* Strong Soundness Theorem for Parallel Programs:*}

lemma Parallel_Strong_Soundness_Seq_aux: 
  "\<lbrakk>interfree Ts; i<length Ts; com(Ts ! i) = Some(AnnSeq c0 c1) \<rbrakk> 
  \<Longrightarrow>  interfree (Ts[i:=(Some c0, pre c1)])"
apply(simp add: interfree_def)
apply clarify
apply(case_tac "i=j")
 apply(force simp add: nth_list_update interfree_aux_def)
apply(case_tac "i=ia")
 apply(erule_tac x=ia in allE)
 apply(force simp add:interfree_aux_def assertions_lemma)
apply simp
done

lemma Parallel_Strong_Soundness_Seq [rule_format (no_asm)]: 
 "\<lbrakk> \<forall>i<length Ts. (if com(Ts!i) = None then b \<in> post(Ts!i) 
  else b \<in> pre(the(com(Ts!i))) \<and> \<turnstile> the(com(Ts!i)) post(Ts!i));  
  com(Ts ! i) = Some(AnnSeq c0 c1); i<length Ts; interfree Ts \<rbrakk> \<Longrightarrow> 
 (\<forall>ia<length Ts. (if com(Ts[i:=(Some c0, pre c1)]! ia) = None  
  then b \<in> post(Ts[i:=(Some c0, pre c1)]! ia) 
 else b \<in> pre(the(com(Ts[i:=(Some c0, pre c1)]! ia))) \<and>  
 \<turnstile> the(com(Ts[i:=(Some c0, pre c1)]! ia)) post(Ts[i:=(Some c0, pre c1)]! ia))) 
  \<and> interfree (Ts[i:= (Some c0, pre c1)])"
apply(rule conjI)
 apply safe
 apply(case_tac "i=ia")
  apply simp
  apply(force dest: ann_hoare_case_analysis)
 apply simp
apply(fast elim: Parallel_Strong_Soundness_Seq_aux)
done

lemma Parallel_Strong_Soundness_aux_aux [rule_format]: 
 "(Some c, b) -1\<rightarrow> (co, t) \<longrightarrow>  
  (\<forall>Ts. i<length Ts \<longrightarrow> com(Ts ! i) = Some c \<longrightarrow>  
  (\<forall>i<length Ts. (if com(Ts ! i) = None then b\<in>post(Ts!i)  
  else b\<in>pre(the(com(Ts!i))) \<and> \<turnstile> the(com(Ts!i)) post(Ts!i))) \<longrightarrow>  
 interfree Ts \<longrightarrow>  
  (\<forall>j. j<length Ts \<and> i\<noteq>j \<longrightarrow> (if com(Ts!j) = None then t\<in>post(Ts!j)  
  else t\<in>pre(the(com(Ts!j))) \<and> \<turnstile> the(com(Ts!j)) post(Ts!j))) )"
apply(rule ann_transition_transition.induct [THEN conjunct1])
apply safe
prefer 11
apply(rule TrueI)
apply simp_all
--{* Basic *}
   apply(erule_tac x = "i" in all_dupE, erule (1) notE impE)
   apply(erule_tac x = "j" in allE , erule (1) notE impE)
   apply(simp add: interfree_def)
   apply(erule_tac x = "j" in allE,simp)
   apply(erule_tac x = "i" in allE,simp)
   apply(drule_tac t = "i" in not_sym)
   apply(case_tac "com(Ts ! j)=None")
    apply(force intro: converse_rtrancl_into_rtrancl
          simp add: interfree_aux_def com_validity_def SEM_def sem_def All_None_def)
   apply(simp add:interfree_aux_def)
   apply clarify
   apply simp
   apply(erule_tac x="pre y" in ballE)
    apply(force intro: converse_rtrancl_into_rtrancl 
          simp add: com_validity_def SEM_def sem_def All_None_def)
   apply(simp add:assertions_lemma)
--{* Seqs *}
  apply(erule_tac x = "Ts[i:=(Some c0, pre c1)]" in allE)
  apply(drule  Parallel_Strong_Soundness_Seq,simp+)
 apply(erule_tac x = "Ts[i:=(Some c0, pre c1)]" in allE)
 apply(drule  Parallel_Strong_Soundness_Seq,simp+)
--{* Await *}
apply(rule_tac x = "i" in allE , assumption , erule (1) notE impE)
apply(erule_tac x = "j" in allE , erule (1) notE impE)
apply(simp add: interfree_def)
apply(erule_tac x = "j" in allE,simp)
apply(erule_tac x = "i" in allE,simp)
apply(drule_tac t = "i" in not_sym)
apply(case_tac "com(Ts ! j)=None")
 apply(force intro: converse_rtrancl_into_rtrancl simp add: interfree_aux_def 
        com_validity_def SEM_def sem_def All_None_def Help)
apply(simp add:interfree_aux_def)
apply clarify
apply simp
apply(erule_tac x="pre y" in ballE)
 apply(force intro: converse_rtrancl_into_rtrancl 
       simp add: com_validity_def SEM_def sem_def All_None_def Help)
apply(simp add:assertions_lemma)
done

lemma Parallel_Strong_Soundness_aux [rule_format]: 
 "\<lbrakk>(Ts',s) -P*\<rightarrow> (Rs',t);  Ts' = (Parallel Ts); interfree Ts;
 \<forall>i. i<length Ts \<longrightarrow> (\<exists>c q. (Ts ! i) = (Some c, q) \<and> s\<in>(pre c) \<and> \<turnstile> c q ) \<rbrakk> \<Longrightarrow>  
  \<forall>Rs. Rs' = (Parallel Rs) \<longrightarrow> (\<forall>j. j<length Rs \<longrightarrow> 
  (if com(Rs ! j) = None then t\<in>post(Ts ! j) 
  else t\<in>pre(the(com(Rs ! j))) \<and> \<turnstile> the(com(Rs ! j)) post(Ts ! j))) \<and> interfree Rs"
apply(erule rtrancl_induct2)
 apply clarify
--{* Base *}
 apply force
--{* Induction step *}
apply clarify
apply(drule Parallel_length_post_PStar)
apply clarify
apply (ind_cases "(Parallel Ts, s) -P1\<rightarrow> (Parallel Rs, t)")
apply(rule conjI)
 apply clarify
 apply(case_tac "i=j")
  apply(simp split del:split_if)
  apply(erule Strong_Soundness_aux_aux,simp+)
   apply force
  apply force
 apply(simp split del: split_if)
 apply(erule Parallel_Strong_Soundness_aux_aux)
 apply(simp_all add: split del:split_if)
 apply force
apply(rule interfree_lemma)
apply simp_all
done

lemma Parallel_Strong_Soundness: 
 "\<lbrakk>(Parallel Ts, s) -P*\<rightarrow> (Parallel Rs, t); interfree Ts; j<length Rs; 
  \<forall>i. i<length Ts \<longrightarrow> (\<exists>c q. Ts ! i = (Some c, q) \<and> s\<in>pre c \<and> \<turnstile> c q) \<rbrakk> \<Longrightarrow>  
  if com(Rs ! j) = None then t\<in>post(Ts ! j) else t\<in>pre (the(com(Rs ! j)))"
apply(drule  Parallel_Strong_Soundness_aux)
apply simp+
done

lemma oghoare_sound [rule_format (no_asm)]: "\<parallel>- p c q \<longrightarrow> \<parallel>= p c q"
apply (unfold com_validity_def)
apply(rule oghoare_induct)
apply(rule TrueI)+
--{* Parallel *}     
      apply(simp add: SEM_def sem_def)
      apply clarify
      apply(frule Parallel_length_post_PStar)
      apply clarify
      apply(drule_tac j=i in Parallel_Strong_Soundness)
         apply clarify
        apply simp
       apply force
      apply simp
      apply(erule_tac V = "\<forall>i. ?P i" in thin_rl)
      apply(drule_tac s = "length Rs" in sym)
      apply(erule allE, erule impE, assumption)
      apply(force dest: nth_mem simp add: All_None_def)
--{* Basic *}
    apply(simp add: SEM_def sem_def)
    apply(force dest: rtrancl_imp_UN_rel_pow Basic_ntran)
--{* Seq *}
   apply(rule subset_trans)
    prefer 2 apply assumption
   apply(simp add: L3_5ii L3_5i)
--{* Cond *}
  apply(simp add: L3_5iv)
  apply(erule Un_least)
  apply assumption
--{* While *}
 apply(simp add: L3_5v)
 apply(rule UN_least)
 apply(drule SEM_fwhile)
 apply assumption
--{* Conseq *}
apply(simp add: SEM_def sem_def)
apply auto
done

end