(*  Title:      HOL/NanoJava/Equivalence.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Equivalence of Operational and Axiomatic Semantics"

theory Equivalence = OpSem + AxSem:

subsection "Validity"

constdefs
  valid   :: "[assn,stmt, assn] => bool"  ("|= {(1_)}/ (_)/ {(1_)}" [3,90,3] 60)
 "|=  {P} c {Q} \<equiv> \<forall>s   t. P s --> (\<exists>n. s -c  -n-> t) --> Q   t"

 evalid   :: "[assn,expr,vassn] => bool" ("|=e {(1_)}/ (_)/ {(1_)}" [3,90,3] 60)
 "|=e {P} e {Q} \<equiv> \<forall>s v t. P s --> (\<exists>n. s -e>v-n-> t) --> Q v t"


 nvalid   :: "[nat, triple    ] => bool" ("|=_: _"  [61,61] 60)
 "|=n:  t \<equiv> let (P,c,Q) = t in \<forall>s   t. s -c  -n-> t --> P s --> Q   t"

envalid   :: "[nat,etriple    ] => bool" ("|=_:e _" [61,61] 60)
 "|=n:e t \<equiv> let (P,e,Q) = t in \<forall>s v t. s -e>v-n-> t --> P s --> Q v t"

  nvalids :: "[nat,       triple set] => bool" ("||=_: _" [61,61] 60)
 "||=n: T \<equiv> \<forall>t\<in>T. |=n: t"

 cnvalids :: "[triple set,triple set] => bool" ("_ ||=/ _"  [61,61] 60)
 "A ||=  C \<equiv> \<forall>n. ||=n: A --> ||=n: C"

cenvalid  :: "[triple set,etriple   ] => bool" ("_ ||=e/ _" [61,61] 60)
 "A ||=e t \<equiv> \<forall>n. ||=n: A --> |=n:e t"

syntax (xsymbols)
   valid  :: "[assn,stmt, assn] => bool" ( "\<Turnstile> {(1_)}/ (_)/ {(1_)}" [3,90,3] 60)
  evalid  :: "[assn,expr,vassn] => bool" ("\<Turnstile>\<^sub>e {(1_)}/ (_)/ {(1_)}" [3,90,3] 60)
  nvalid  :: "[nat, triple          ] => bool" ("\<Turnstile>_: _"  [61,61] 60)
 envalid  :: "[nat,etriple          ] => bool" ("\<Turnstile>_:\<^sub>e _" [61,61] 60)
  nvalids :: "[nat,       triple set] => bool" ("|\<Turnstile>_: _"  [61,61] 60)
 cnvalids :: "[triple set,triple set] => bool" ("_ |\<Turnstile>/ _" [61,61] 60)
cenvalid  :: "[triple set,etriple   ] => bool" ("_ |\<Turnstile>\<^sub>e/ _"[61,61] 60)


lemma nvalid_def2: "\<Turnstile>n: (P,c,Q) \<equiv> \<forall>s t. s -c-n\<rightarrow> t \<longrightarrow> P s \<longrightarrow> Q t"
by (simp add: nvalid_def Let_def)

lemma valid_def2: "\<Turnstile> {P} c {Q} = (\<forall>n. \<Turnstile>n: (P,c,Q))"
apply (simp add: valid_def nvalid_def2)
apply blast
done

lemma envalid_def2: "\<Turnstile>n:\<^sub>e (P,e,Q) \<equiv> \<forall>s v t. s -e\<succ>v-n\<rightarrow> t \<longrightarrow> P s \<longrightarrow> Q v t"
by (simp add: envalid_def Let_def)

lemma evalid_def2: "\<Turnstile>\<^sub>e {P} e {Q} = (\<forall>n. \<Turnstile>n:\<^sub>e (P,e,Q))"
apply (simp add: evalid_def envalid_def2)
apply blast
done

lemma cenvalid_def2: 
  "A|\<Turnstile>\<^sub>e (P,e,Q) = (\<forall>n. |\<Turnstile>n: A \<longrightarrow> (\<forall>s v t. s -e\<succ>v-n\<rightarrow> t \<longrightarrow> P s \<longrightarrow> Q v t))"
by(simp add: cenvalid_def envalid_def2) 


subsection "Soundness"

declare exec_elim_cases [elim!] eval_elim_cases [elim!]

lemma Impl_nvalid_0: "\<Turnstile>0: (P,Impl M,Q)"
by (clarsimp simp add: nvalid_def2)

lemma Impl_nvalid_Suc: "\<Turnstile>n: (P,body M,Q) \<Longrightarrow> \<Turnstile>Suc n: (P,Impl M,Q)"
by (clarsimp simp add: nvalid_def2)

lemma nvalid_SucD: "\<And>t. \<Turnstile>Suc n:t \<Longrightarrow> \<Turnstile>n:t"
by (force simp add: split_paired_all nvalid_def2 intro: exec_mono)

lemma nvalids_SucD: "Ball A (nvalid (Suc n)) \<Longrightarrow>  Ball A (nvalid n)"
by (fast intro: nvalid_SucD)

lemma Loop_sound_lemma [rule_format (no_asm)]: 
"\<forall>s t. s -c-n\<rightarrow> t \<longrightarrow> P s \<and> s<x> \<noteq> Null \<longrightarrow> P t \<Longrightarrow> 
  (s -c0-n0\<rightarrow> t \<longrightarrow> P s \<longrightarrow> c0 = While (x) c \<longrightarrow> n0 = n \<longrightarrow> P t \<and> t<x> = Null)"
apply (rule_tac "P2.1"="%s e v n t. True" in exec_eval.induct [THEN conjunct1])
apply clarsimp+
done

lemma Impl_sound_lemma: 
"\<lbrakk>\<forall>z n. Ball (A \<union> B) (nvalid n) \<longrightarrow> Ball (f z ` Ms) (nvalid n); 
Cm\<in>Ms; Ball A (nvalid na); Ball B (nvalid na)\<rbrakk> \<Longrightarrow> nvalid na (f z Cm)"
by blast

lemma all_conjunct2: "\<forall>l. P' l \<and> P l \<Longrightarrow> \<forall>l. P l"
by fast

lemma all3_conjunct2: 
  "\<forall>a p l. (P' a p l \<and> P a p l) \<Longrightarrow> \<forall>a p l. P a p l"
by fast

lemma cnvalid1_eq: 
  "A |\<Turnstile> {(P,c,Q)} \<equiv> \<forall>n. |\<Turnstile>n: A \<longrightarrow> (\<forall>s t. s -c-n\<rightarrow> t \<longrightarrow> P s \<longrightarrow> Q t)"
by(simp add: cnvalids_def nvalids_def nvalid_def2)

lemma hoare_sound_main:"\<And>t. (A |\<turnstile> C \<longrightarrow> A |\<Turnstile> C) \<and> (A |\<turnstile>\<^sub>e t \<longrightarrow> A |\<Turnstile>\<^sub>e t)"
apply (tactic "split_all_tac 1", rename_tac P e Q)
apply (rule hoare_ehoare.induct)
apply (tactic {* ALLGOALS (REPEAT o dresolve_tac [thm "all_conjunct2", thm "all3_conjunct2"]) *})
apply (tactic {* ALLGOALS (REPEAT o thin_tac "?x :  hoare") *})
apply (tactic {* ALLGOALS (REPEAT o thin_tac "?x : ehoare") *})
apply (simp_all only: cnvalid1_eq cenvalid_def2)
apply fast
apply fast
apply fast
apply (clarify,tactic "smp_tac 1 1",erule(2) Loop_sound_lemma,(rule HOL.refl)+)
apply fast
apply fast
apply fast
apply fast
apply fast
apply fast
apply (clarsimp del: Meth_elim_cases) (* Call *)
apply (tactic "smp_tac 1 1", tactic "smp_tac 3 1", tactic "smp_tac 0 1")
apply (tactic "smp_tac 2 1", tactic "smp_tac 3 1", tactic "smp_tac 0 1")
apply (tactic "smp_tac 4 1", tactic "smp_tac 2 1", fast)
apply (force del: Impl_elim_cases) (* Meth *)
defer
prefer 4 apply blast (*  Conseq *)
prefer 4 apply blast (* eConseq *)
apply (simp_all (no_asm_use) only: cnvalids_def nvalids_def)
apply blast
apply blast
apply blast
(* Impl *)
apply (rule allI)
apply (rule_tac x=Z in spec)
apply (induct_tac "n")
apply  (clarify intro!: Impl_nvalid_0)
apply (clarify  intro!: Impl_nvalid_Suc)
apply (drule nvalids_SucD)
apply (simp only: all_simps)
apply (erule (1) impE)
apply (drule (2) Impl_sound_lemma)
apply  blast
apply assumption
done

theorem hoare_sound: "{} \<turnstile> {P} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q}"
apply (simp only: valid_def2)
apply (drule hoare_sound_main [THEN conjunct1, rule_format])
apply (unfold cnvalids_def nvalids_def)
apply fast
done

theorem ehoare_sound: "{} \<turnstile>\<^sub>e {P} e {Q} \<Longrightarrow> \<Turnstile>\<^sub>e {P} e {Q}"
apply (simp only: evalid_def2)
apply (drule hoare_sound_main [THEN conjunct2, rule_format])
apply (unfold cenvalid_def nvalids_def)
apply fast
done


subsection "(Relative) Completeness"

constdefs MGT    :: "stmt => state =>  triple"
         "MGT  c Z \<equiv> (\<lambda>s. Z = s, c, \<lambda>  t. \<exists>n. Z -c-  n-> t)"
          MGTe   :: "expr => state => etriple"
         "MGTe e Z \<equiv> (\<lambda>s. Z = s, e, \<lambda>v t. \<exists>n. Z -e>v-n-> t)"
syntax (xsymbols)
         MGTe    :: "expr => state => etriple" ("MGT\<^sub>e")

lemma MGF_implies_complete:
 "\<forall>Z. {} |\<turnstile> { MGT c Z} \<Longrightarrow> \<Turnstile>  {P} c {Q} \<Longrightarrow> {} \<turnstile>  {P} c {Q}"
apply (simp only: valid_def2)
apply (unfold MGT_def)
apply (erule hoare_ehoare.Conseq)
apply (clarsimp simp add: nvalid_def2)
done

lemma eMGF_implies_complete:
 "\<forall>Z. {} |\<turnstile>\<^sub>e MGT\<^sub>e e Z \<Longrightarrow> \<Turnstile>\<^sub>e {P} e {Q} \<Longrightarrow> {} \<turnstile>\<^sub>e {P} e {Q}"
apply (simp only: evalid_def2)
apply (unfold MGTe_def)
apply (erule hoare_ehoare.eConseq)
apply (clarsimp simp add: envalid_def2)
done

declare exec_eval.intros[intro!]

lemma MGF_Loop: "\<forall>Z. A \<turnstile> {op = Z} c {\<lambda>t. \<exists>n. Z -c-n\<rightarrow> t} \<Longrightarrow> 
  A \<turnstile> {op = Z} While (x) c {\<lambda>t. \<exists>n. Z -While (x) c-n\<rightarrow> t}"
apply (rule_tac P' = "\<lambda>Z s. (Z,s) \<in> ({(s,t). \<exists>n. s<x> \<noteq> Null \<and> s -c-n\<rightarrow> t})^*"
       in hoare_ehoare.Conseq)
apply  (rule allI)
apply  (rule hoare_ehoare.Loop)
apply  (erule hoare_ehoare.Conseq)
apply  clarsimp
apply  (blast intro:rtrancl_into_rtrancl)
apply (erule thin_rl)
apply clarsimp
apply (erule_tac x = Z in allE)
apply clarsimp
apply (erule converse_rtrancl_induct)
apply  blast
apply clarsimp
apply (drule (1) exec_exec_max)
apply (blast del: exec_elim_cases)
done

lemma MGF_lemma: "\<forall>M Z. A |\<turnstile> {MGT (Impl M) Z} \<Longrightarrow> 
 (\<forall>Z. A |\<turnstile> {MGT c Z}) \<and> (\<forall>Z. A |\<turnstile>\<^sub>e MGT\<^sub>e e Z)"
apply (simp add: MGT_def MGTe_def)
apply (rule stmt_expr.induct)
apply (rule_tac [!] allI)

apply (rule Conseq1 [OF hoare_ehoare.Skip])
apply blast

apply (rule hoare_ehoare.Comp)
apply  (erule spec)
apply (erule hoare_ehoare.Conseq)
apply clarsimp
apply (drule (1) exec_exec_max)
apply blast

apply (erule thin_rl)
apply (rule hoare_ehoare.Cond)
apply  (erule spec)
apply (rule allI)
apply (simp)
apply (rule conjI)
apply  (rule impI, erule hoare_ehoare.Conseq, clarsimp, drule (1) eval_exec_max,
        erule thin_rl, erule thin_rl, force)+

apply (erule MGF_Loop)

apply (erule hoare_ehoare.eConseq [THEN hoare_ehoare.LAss])
apply fast

apply (erule thin_rl)
apply (rule_tac Q = "\<lambda>a s. \<exists>n. Z -expr1\<succ>Addr a-n\<rightarrow> s" in hoare_ehoare.FAss)
apply  (drule spec)
apply  (erule eConseq2)
apply  fast
apply (rule allI)
apply (erule hoare_ehoare.eConseq)
apply clarsimp
apply (drule (1) eval_eval_max)
apply blast

apply (simp only: split_paired_all)
apply (rule hoare_ehoare.Meth)
apply (rule allI)
apply (drule spec, drule spec, erule hoare_ehoare.Conseq)
apply blast

apply (simp add: split_paired_all)

apply (rule eConseq1 [OF hoare_ehoare.NewC])
apply blast

apply (erule hoare_ehoare.eConseq [THEN hoare_ehoare.Cast])
apply fast

apply (rule eConseq1 [OF hoare_ehoare.LAcc])
apply blast

apply (erule hoare_ehoare.eConseq [THEN hoare_ehoare.FAcc])
apply fast

apply (rule_tac R = "\<lambda>a v s. \<exists>n1 n2 t. Z -expr1\<succ>a-n1\<rightarrow> t \<and> t -expr2\<succ>v-n2\<rightarrow> s" in
                hoare_ehoare.Call)
apply   (erule spec)
apply  (rule allI)
apply  (erule hoare_ehoare.eConseq)
apply  clarsimp
apply  blast
apply (rule allI)+
apply (rule hoare_ehoare.Meth)
apply (rule allI)
apply (drule spec, drule spec, erule hoare_ehoare.Conseq)
apply (erule thin_rl, erule thin_rl)
apply (clarsimp del: Impl_elim_cases)
apply (drule (2) eval_eval_exec_max)
apply (force del: Impl_elim_cases)
done

lemma MGF_Impl: "{} |\<turnstile> {MGT (Impl M) Z}"
apply (unfold MGT_def)
apply (rule_tac 'a = state in Impl1')
apply  (rule_tac [2] UNIV_I)
apply clarsimp
apply (rule hoare_ehoare.ConjI)
apply clarsimp
apply (rule ssubst [OF Impl_body_eq])
apply (fold MGT_def)
apply (rule MGF_lemma [THEN conjunct1, rule_format])
apply (rule hoare_ehoare.Asm)
apply force
done

theorem hoare_relative_complete: "\<Turnstile> {P} c {Q} \<Longrightarrow> {} \<turnstile> {P} c {Q}"
apply (rule MGF_implies_complete)
apply  (erule_tac [2] asm_rl)
apply (rule allI)
apply (rule MGF_lemma [THEN conjunct1, rule_format])
apply (rule MGF_Impl)
done

theorem ehoare_relative_complete: "\<Turnstile>\<^sub>e {P} e {Q} \<Longrightarrow> {} \<turnstile>\<^sub>e {P} e {Q}"
apply (rule eMGF_implies_complete)
apply  (erule_tac [2] asm_rl)
apply (rule allI)
apply (rule MGF_lemma [THEN conjunct2, rule_format])
apply (rule MGF_Impl)
done

lemma cFalse: "A \<turnstile> {\<lambda>s. False} c {Q}"
apply (rule cThin)
apply (rule hoare_relative_complete)
apply (auto simp add: valid_def)
done

lemma eFalse: "A \<turnstile>\<^sub>e {\<lambda>s. False} e {Q}"
apply (rule eThin)
apply (rule ehoare_relative_complete)
apply (auto simp add: evalid_def)
done

end
