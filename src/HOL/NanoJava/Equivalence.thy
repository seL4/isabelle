(*  Title:      HOL/NanoJava/Equivalence.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Equivalence of Operational and Axiomatic Semantics"

theory Equivalence = OpSem + AxSem:

subsection "Validity"

constdefs
  valid   :: "[assn,stmt,assn] => bool" ("|= {(1_)}/ (_)/ {(1_)}" [3,90,3] 60)
 "|= {P} c {Q} \<equiv> \<forall>s t. P s --> (\<exists>n. s -c-n-> t) --> Q t"

 nvalid   :: "[nat,       triple    ] => bool" ("|=_: _"  [61,61] 60)
 "|=n: t \<equiv> let (P,c,Q) = t in \<forall>s t. s -c-n-> t --> P s --> Q t"

 nvalids  :: "[nat,       triple set] => bool" ("||=_: _" [61,61] 60)
 "||=n: T \<equiv> \<forall>t\<in>T. |=n: t"

 cnvalids :: "[triple set,triple set] => bool" ("_ ||=/ _"[61,61] 60)
 "A ||= C \<equiv> \<forall>n. ||=n: A --> ||=n: C"

syntax (xsymbols)
  valid   :: "[assn,stmt,assn] => bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" [3,90,3] 60)
 nvalid   :: "[nat,       triple    ] => bool" ("\<Turnstile>_: _"   [61,61] 60)
 nvalids  :: "[nat,       triple set] => bool" ("|\<Turnstile>_: _"  [61,61] 60)
 cnvalids :: "[triple set,triple set] => bool" ("_ |\<Turnstile>/ _" [61,61] 60)

syntax
  nvalid1::"[nat,        assn,stmt,assn] => bool" ( "|=_:.{(1_)}/ (_)/ {(1_)}"
                                                         [61,3,90,3] 60)
 cnvalid1::"[triple set, assn,stmt,assn] => bool" ("_ ||=.{(1_)}/ (_)/ {(1_)}"
                                                         [61,3,90,3] 60)
syntax (xsymbols)
  nvalid1::"[nat,        assn,stmt,assn] => bool" (  "\<Turnstile>_:.{(1_)}/ (_)/ {(1_)}"
                                                         [61,3,90,3] 60)
 cnvalid1::"[triple set, assn,stmt,assn] => bool" ( "_ |\<Turnstile>.{(1_)}/ (_)/ {(1_)}"
                                                         [61,3,90,3] 60)
translations
 " \<Turnstile>n:.{P} c {Q}" \<rightleftharpoons> " \<Turnstile>n:  (P,c,Q)"
 "A |\<Turnstile>.{P} c {Q}" \<rightleftharpoons> "A |\<Turnstile> {(P,c,Q)}"

lemma nvalid1_def2: "\<Turnstile>n:.{P} c {Q} \<equiv> \<forall>s t. s -c-n\<rightarrow> t \<longrightarrow> P s \<longrightarrow> Q t"
by (simp add: nvalid_def Let_def)

lemma cnvalid1_def2: 
  "A |\<Turnstile>.{P} c {Q} \<equiv> \<forall>n. |\<Turnstile>n: A \<longrightarrow> (\<forall>s t. s -c-n\<rightarrow> t \<longrightarrow> P s \<longrightarrow> Q t)"
by(simp add: nvalid1_def2 nvalids_def cnvalids_def)

lemma valid_def2: "\<Turnstile> {P} c {Q} = (\<forall>n. \<Turnstile>n:.{P} c {Q})"
apply (simp add: valid_def nvalid1_def2)
apply blast
done


subsection "Soundness"

declare exec_elim_cases [elim!]

lemma Impl_nvalid_0: "\<Turnstile>0:.{P} Impl C m {Q}"
by (clarsimp simp add: nvalid1_def2)

lemma Impl_nvalid_Suc: "\<Turnstile>n:.{P} body C m {Q} \<Longrightarrow> \<Turnstile>Suc n:.{P} Impl C m {Q}"
by (clarsimp simp add: nvalid1_def2)

lemma nvalid_SucD: "\<And>t. \<Turnstile>Suc n:t \<Longrightarrow> \<Turnstile>n:t"
by (force simp add: split_paired_all nvalid1_def2 intro: exec_mono)

lemma nvalids_SucD: "Ball A (nvalid (Suc n)) \<Longrightarrow>  Ball A (nvalid n)"
by (fast intro: nvalid_SucD)

lemma Loop_sound_lemma [rule_format (no_asm)]: 
"\<lbrakk>\<forall>s t. s -c-n\<rightarrow> t \<longrightarrow> P s \<and> s<e> \<noteq> Null \<longrightarrow> P t; s -c0-n0\<rightarrow> t\<rbrakk> \<Longrightarrow> 
  P s \<longrightarrow> c0 = While (e) c \<longrightarrow> n0 = n \<longrightarrow> P t \<and> t<e> = Null"
apply (erule exec.induct)
apply clarsimp+
done

lemma Impl_sound_lemma: 
"\<lbrakk>\<forall>n. Ball (A \<union> B) (nvalid n) \<longrightarrow> Ball (\<Union>z. split (f z) ` ms) (nvalid n);
          (C, m) \<in> ms; Ball A (nvalid na); Ball B (nvalid na)\<rbrakk> \<Longrightarrow> nvalid na (f z C m)"
by blast

lemma hoare_sound_main: "A |\<turnstile> C \<Longrightarrow> A |\<Turnstile> C"
apply (erule hoare.induct)
apply (simp_all only: cnvalid1_def2)
apply clarsimp
apply clarsimp
apply (clarsimp split add: split_if_asm)
apply (clarsimp,tactic "smp_tac 1 1",erule(2) Loop_sound_lemma,(rule HOL.refl)+)
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp
apply (clarsimp del: Meth_elim_cases) (* Call *)
apply (clarsimp del: Impl_elim_cases) (* Meth *)
defer
apply blast (* Conseq *)
apply (simp_all (no_asm_use) only: cnvalids_def nvalids_def)
apply blast
apply blast
apply blast
(* Impl *)
apply (erule thin_rl)
apply (rule allI)
apply (induct_tac "n")
apply  (clarify intro!: Impl_nvalid_0)
apply (clarify  intro!: Impl_nvalid_Suc)
apply (drule nvalids_SucD)
apply (erule (1) impE)
apply (drule (4) Impl_sound_lemma)
done

theorem hoare_sound: "{} \<turnstile> {P} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q}"
apply (simp only: valid_def2)
apply (drule hoare_sound_main)
apply (unfold cnvalids_def nvalids_def)
apply fast
done


subsection "(Relative) Completeness"

constdefs MGT    :: "stmt => state => triple"
         "MGT c z \<equiv> (\<lambda> s. z = s, c, %t. \<exists>n. z -c-n-> t)"

lemma MGF_implies_complete:
 "\<forall>z. {} |\<turnstile> {MGT c z} \<Longrightarrow> \<Turnstile> {P} c {Q} \<Longrightarrow> {} \<turnstile> {P} c {Q}"
apply (simp only: valid_def2)
apply (unfold MGT_def)
apply (erule hoare.Conseq)
apply (clarsimp simp add: nvalid1_def2)
done


declare exec.intros[intro!]

lemma MGF_Loop: "\<forall>z. A \<turnstile> {op = z} c {\<lambda>t. \<exists>n. z -c-n\<rightarrow> t} \<Longrightarrow> 
  A \<turnstile> {op = z} While (e) c {\<lambda>t. \<exists>n. z -While (e) c-n\<rightarrow> t}"
apply (rule_tac P' = "\<lambda>z s. (z,s) \<in> ({(s,t). \<exists>n. s<e> \<noteq> Null \<and> s -c-n\<rightarrow> t})^*"
       in hoare.Conseq)
apply  (rule allI)
apply  (rule hoare.Loop)
apply  (erule hoare.Conseq)
apply  clarsimp
apply  (blast intro:rtrancl_into_rtrancl)
apply (erule thin_rl)
apply clarsimp
apply (erule_tac x = z in allE)
apply clarsimp
apply (erule converse_rtrancl_induct)
apply  blast
apply clarsimp
apply (drule (1) exec_max2)
apply (blast del: exec_elim_cases)
done

lemma MGF_lemma[rule_format]:
 "(\<forall>C m z. A |\<turnstile> {MGT (Impl C m) z}) \<longrightarrow> (\<forall>z. A |\<turnstile> {MGT c z})"
apply (simp add: MGT_def)
apply (induct_tac c)
apply (tactic "ALLGOALS Clarify_tac")

apply (rule Conseq1 [OF hoare.Skip])
apply blast

apply (rule hoare.Comp)
apply  (erule spec)
apply (erule hoare.Conseq)
apply (erule thin_rl, erule thin_rl)
apply clarsimp
apply (drule (1) exec_max2)
apply blast

apply (rule hoare.Cond)
apply  (erule hoare.Conseq)
apply  (erule thin_rl, erule thin_rl)
apply  force
apply (erule hoare.Conseq)
apply (erule thin_rl, erule thin_rl)
apply force

apply (erule MGF_Loop)

apply (rule Conseq1 [OF hoare.NewC])
apply blast

apply (rule Conseq1 [OF hoare.Cast])
apply blast

apply (rule Conseq1 [OF hoare.FAcc])
apply blast

apply (rule Conseq1 [OF hoare.FAss])
apply blast

apply (rule hoare.Call)
apply (rule allI)
apply (rule hoare.Meth)
apply (rule allI)
apply (drule spec, drule spec, erule hoare.Conseq)
apply blast

apply (rule hoare.Meth)
apply (rule allI)
apply (drule spec, drule spec, erule hoare.Conseq)
apply blast

apply blast
done

lemma MGF_Impl: "{} |\<turnstile> {MGT (Impl C m) z}"
apply (unfold MGT_def)
apply (rule Impl1)
apply  (rule_tac [2] UNIV_I)
apply clarsimp
apply (rule hoare.ConjI)
apply clarsimp
apply (rule ssubst [OF Impl_body_eq])
apply (fold MGT_def)
apply (rule MGF_lemma)
apply (rule hoare.Asm)
apply force
done

theorem hoare_relative_complete: "\<Turnstile> {P} c {Q} \<Longrightarrow> {} \<turnstile> {P} c {Q}"
apply (rule MGF_implies_complete)
apply  (erule_tac [2] asm_rl)
apply (rule allI)
apply (rule MGF_lemma)
apply (rule MGF_Impl)
done

end
