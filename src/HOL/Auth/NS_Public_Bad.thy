(*  Title:      HOL/Auth/NS_Public_Bad.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

section\<open>The Needham-Schroeder Public-Key Protocol (Flawed)\<close>

text \<open>Flawed version, vulnerable to Lowe's attack.
From Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989), p. 260\<close>

theory NS_Public_Bad imports Public begin

inductive_set ns_public :: "event list set"
  where
   Nil:  "[] \<in> ns_public" 
   \<comment> \<open>Initial trace is empty\<close>
 | Fake: "\<lbrakk>evsf \<in> ns_public;  X \<in> synth (analz (spies evsf))\<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> ns_public"
   \<comment> \<open>The spy can say almost anything.\<close>
 | NS1:  "\<lbrakk>evs1 \<in> ns_public;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>)
                # evs1  \<in>  ns_public"
   \<comment> \<open>Alice initiates a protocol run, sending a nonce to Bob\<close>
 | NS2:  "\<lbrakk>evs2 \<in> ns_public;  Nonce NB \<notin> used evs2;
           Says A' B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>)
                # evs2  \<in>  ns_public"
   \<comment> \<open>Bob responds to Alice's message with a further nonce\<close>
 | NS3:  "\<lbrakk>evs3 \<in> ns_public;
           Says A  B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
           Says B' A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) (Nonce NB)) # evs3 \<in> ns_public"
   \<comment> \<open>Alice proves her existence by sending @{term NB} back to Bob.\<close>

declare knows_Spy_partsEs [elim]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

text \<open>A "possibility property": there are traces that reach the end\<close>
lemma "\<exists>NB. \<exists>evs \<in> ns_public. Says A B (Crypt (pubEK B) (Nonce NB)) \<in> set evs"
  apply (intro exI bexI)
   apply (rule_tac [2] ns_public.Nil [THEN ns_public.NS1, THEN ns_public.NS2, THEN ns_public.NS3])
  by possibility


subsection \<open>Inductive proofs about @{term ns_public}\<close>

(** Theorems of the form X \<notin> parts (spies evs) imply that NOBODY
    sends messages containing X! **)

text \<open>Spy never sees another agent's private key! (unless it's bad at start)\<close>
lemma Spy_see_priEK [simp]: 
  "evs \<in> ns_public \<Longrightarrow> (Key (priEK A) \<in> parts (spies evs)) = (A \<in> bad)"
  by (erule ns_public.induct, auto)

lemma Spy_analz_priEK [simp]: 
  "evs \<in> ns_public \<Longrightarrow> (Key (priEK A) \<in> analz (spies evs)) = (A \<in> bad)"
  by auto


subsection \<open>Authenticity properties obtained from {term NS1}\<close>

text \<open>It is impossible to re-use a nonce in both {term NS1} and {term NS2}, provided the nonce
  is secret.  (Honest users generate fresh nonces.)\<close>
lemma no_nonce_NS1_NS2 [rule_format]: 
      "evs \<in> ns_public 
       \<Longrightarrow> Crypt (pubEK C) \<lbrace>NA', Nonce NA\<rbrace> \<in> parts (spies evs) \<longrightarrow>
           Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies evs) \<longrightarrow>  
           Nonce NA \<in> analz (spies evs)"
  by (induct rule: ns_public.induct) (auto intro: analz_insertI)


text \<open>Unicity for {term NS1}: nonce {term NA} identifies agents {term A} and {term B}\<close>
lemma unique_NA: 
  assumes NA: "Crypt(pubEK B)  \<lbrace>Nonce NA, Agent A \<rbrace> \<in> parts(spies evs)"
              "Crypt(pubEK B') \<lbrace>Nonce NA, Agent A'\<rbrace> \<in> parts(spies evs)"
              "Nonce NA \<notin> analz (spies evs)"
    and evs: "evs \<in> ns_public"
  shows "A=A' \<and> B=B'"
  using evs NA
  by (induction rule: ns_public.induct) (auto intro!: analz_insertI split: if_split_asm)


text \<open>Secrecy: Spy does not see the nonce sent in msg {term NS1} if {term A} and {term B} are secure
  The major premise "Says A B ..." makes it a dest-rule, hence the given assumption order. \<close>
theorem Spy_not_see_NA: 
  assumes NA: "Says A B (Crypt(pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs"
              "A \<notin> bad" "B \<notin> bad"
    and evs: "evs \<in> ns_public"
  shows "Nonce NA \<notin> analz (spies evs)"
  using evs NA
proof (induction rule: ns_public.induct)
  case (Fake evsf X B)
  then show ?case
    by spy_analz
next
  case (NS2 evs2 NB A' B NA A)
  then show ?case
    by simp (metis Says_imp_analz_Spy analz_into_parts parts.simps unique_NA usedI)
next
  case (NS3 evs3 A B NA B' NB)
  then show ?case
    by simp (meson Says_imp_analz_Spy analz_into_parts no_nonce_NS1_NS2)
qed auto


text \<open>Authentication for {term A}: if she receives message 2 and has used {term NA}
  to start a run, then {term B} has sent message 2.\<close>
lemma A_trusts_NS2_lemma [rule_format]: 
   "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
    \<Longrightarrow> Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts (spies evs) \<longrightarrow>
        Says A B (Crypt(pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs \<longrightarrow>
        Says B A (Crypt(pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs"
  by (erule ns_public.induct) (auto dest: Spy_not_see_NA unique_NA)

theorem A_trusts_NS2: 
     "\<lbrakk>Says A  B (Crypt(pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs;   
       Says B' A (Crypt(pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
      \<Longrightarrow> Says B A (Crypt(pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs"
  by (blast intro: A_trusts_NS2_lemma)


text \<open>If the encrypted message appears then it originated with Alice in {term NS1}\<close>
lemma B_trusts_NS1 [rule_format]:
     "evs \<in> ns_public                                         
      \<Longrightarrow> Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies evs) \<longrightarrow>
          Nonce NA \<notin> analz (spies evs) \<longrightarrow>
          Says A B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs"
  by (induction evs rule: ns_public.induct) (use analz_insertI in auto)


subsection \<open>Authenticity properties obtained from {term NS2}\<close>

text \<open>Unicity for {term NS2}: nonce {term NB} identifies nonce {term NA} and agent {term A} 
  [proof closely follows that for @{thm [source] unique_NA}]\<close>

lemma unique_NB [dest]: 
  assumes NB: "Crypt(pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts(spies evs)"
              "Crypt(pubEK A') \<lbrace>Nonce NA', Nonce NB\<rbrace> \<in> parts(spies evs)"
              "Nonce NB \<notin> analz (spies evs)"
    and evs: "evs \<in> ns_public"
  shows "A=A' \<and> NA=NA'"
  using evs NB 
  by (induction rule: ns_public.induct) (auto intro!: analz_insertI split: if_split_asm)


text \<open>{term NB} remains secret \emph{provided} Alice never responds with round 3\<close>
theorem Spy_not_see_NB [dest]:
  assumes NB: "Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs"
              "\<forall>C. Says A C (Crypt (pubEK C) (Nonce NB)) \<notin> set evs"
              "A \<notin> bad" "B \<notin> bad"
    and evs: "evs \<in> ns_public"
  shows "Nonce NB \<notin> analz (spies evs)"
  using evs NB evs
proof (induction rule: ns_public.induct)
  case Fake
  then show ?case by spy_analz
next
  case NS2
  then show ?case
    by (auto intro!: no_nonce_NS1_NS2)
qed auto


text \<open>Authentication for {term B}: if he receives message 3 and has used {term NB}
  in message 2, then {term A} has sent message 3 (to somebody) \<close>
lemma B_trusts_NS3_lemma [rule_format]:
     "\<lbrakk>evs \<in> ns_public; 
       Crypt (pubEK B) (Nonce NB) \<in> parts (spies evs); 
       Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs; 
       A \<notin> bad;  B \<notin> bad\<rbrakk>                    
      \<Longrightarrow> \<exists>C. Says A C (Crypt (pubEK C) (Nonce NB)) \<in> set evs"
proof (induction rule: ns_public.induct)
  case (NS3 evs3 A B NA B' NB)
  then show ?case
    by simp (blast intro: no_nonce_NS1_NS2)
qed auto

theorem B_trusts_NS3:
     "\<lbrakk>Says B A  (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;
       Says A' B (Crypt (pubEK B) (Nonce NB)) \<in> set evs;             
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                    
      \<Longrightarrow> \<exists>C. Says A C (Crypt (pubEK C) (Nonce NB)) \<in> set evs"
  by (blast intro: B_trusts_NS3_lemma)


text \<open>Can we strengthen the secrecy theorem @{thm[source]Spy_not_see_NB}?  NO\<close>
lemma "\<lbrakk>evs \<in> ns_public; 
        Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs; 
        A \<notin> bad; B \<notin> bad\<rbrakk>            
       \<Longrightarrow> Nonce NB \<notin> analz (spies evs)"
apply (induction rule: ns_public.induct, simp_all, spy_analz)
(*{term NS1}: by freshness*)
apply blast
(*{term NS2}: by freshness and unicity of {term NB}*)
apply (blast intro: no_nonce_NS1_NS2)
(*{term NS3}: unicity of {term NB} identifies {term A} and {term NA}, but not {term B}*)
apply clarify
apply (frule_tac A' = A in 
       Says_imp_knows_Spy [THEN parts.Inj, THEN unique_NB], auto)
apply (rename_tac evs3 B' C)
txt\<open>This is the attack!
@{subgoals[display,indent=0,margin=65]}
\<close>
oops

(*
THIS IS THE ATTACK!
Level 8
!!evs. \<lbrakk>A \<notin> bad; B \<notin> bad; evs \<in> ns_public\<rbrakk>
       \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs \<longrightarrow>
           Nonce NB \<notin> analz (spies evs)
 1. !!C B' evs3.
       \<lbrakk>A \<notin> bad; B \<notin> bad; evs3 \<in> ns_public
        Says A C (Crypt (pubEK C) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
        Says B' A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3; 
        C \<in> bad;
        Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3;
        Nonce NB \<notin> analz (spies evs3)\<rbrakk>
       \<Longrightarrow> False
*)

end
