theory Needham_Schroeder_Guided_Attacker_Example
imports Needham_Schroeder_Base
begin

inductive_set ns_public :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> ns_public"

 | Fake_NS1:  "\<lbrakk>evs1 \<in> ns_public; Nonce NA \<in> analz (spies evs1) \<rbrakk>
          \<Longrightarrow> Says Spy B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>)
                # evs1  \<in> ns_public"
 | Fake_NS2:  "\<lbrakk>evs1 \<in> ns_public; Nonce NA \<in> analz (spies evs1); Nonce NB \<in> analz (spies evs1) \<rbrakk>
          \<Longrightarrow> Says Spy A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>)
                # evs1  \<in> ns_public"

         (*Alice initiates a protocol run, sending a nonce to Bob*)
 | NS1:  "\<lbrakk>evs1 \<in> ns_public;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>)
                # evs1  \<in>  ns_public"
         (*Bob responds to Alice's message with a further nonce*)
 | NS2:  "\<lbrakk>evs2 \<in> ns_public;  Nonce NB \<notin> used evs2;
           Says A' B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>)
                # evs2  \<in>  ns_public"

         (*Alice proves her existence by sending NB back to Bob.*)
 | NS3:  "\<lbrakk>evs3 \<in> ns_public;
           Says A  B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
           Says B' A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) (Nonce NB)) # evs3 \<in> ns_public"

declare ListMem_iff[symmetric, code_pred_inline]

lemmas [code_pred_intro] = ns_publicp.intros[folded synth'_def]

code_pred [skip_proof] ns_publicp unfolding synth'_def by (rule ns_publicp.cases) fastforce+
thm ns_publicp.equation

code_pred [generator_cps] ns_publicp .
thm ns_publicp.generator_cps_equation


lemma "ns_publicp evs ==> \<not> (Says Alice Bob (Crypt (pubEK Bob) (Nonce NB))) : set evs"
quickcheck[smart_exhaustive, depth = 5, timeout = 100, expect = counterexample]
(*quickcheck[narrowing, size = 6, timeout = 200, verbose, expect = no_counterexample]*)
oops

lemma
  "\<lbrakk>ns_publicp evs\<rbrakk>            
       \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) : set evs
       \<Longrightarrow> A \<noteq> Spy \<Longrightarrow> B \<noteq> Spy \<Longrightarrow> A \<noteq> B 
           \<Longrightarrow> Nonce NB \<notin> analz (spies evs)"
(*quickcheck[smart_exhaustive, depth = 6, timeout = 100, expect = counterexample]
quickcheck[narrowing, size = 7, timeout = 200, expect = no_counterexample]*)
oops

section {* Proving the counterexample trace for validation *}

lemma
  assumes "A = Alice" "B = Bob" "C = Spy" "NA = 0" "NB = 1"
  assumes "evs = 
  [Says Alice Spy (Crypt (pubEK Spy) (Nonce 1)),
   Says Bob Alice (Crypt (pubEK Alice) {|Nonce 0, Nonce 1|}),
   Says Spy Bob (Crypt (pubEK Bob) {|Nonce 0, Agent Alice|}),
   Says Alice Spy (Crypt (pubEK Spy) {|Nonce 0, Agent Alice|})]" (is "_ = [?e3, ?e2, ?e1, ?e0]")
  shows "A \<noteq> Spy" "B \<noteq> Spy" "evs : ns_public" "Nonce NB : analz (knows Spy evs)"
proof -
  from assms show "A \<noteq> Spy" by auto
  from assms show "B \<noteq> Spy" by auto
  have "[] : ns_public" by (rule Nil)
  then have first_step: "[?e0] : ns_public"
  proof (rule NS1)
    show "Nonce 0 ~: used []" by eval
  qed
  then have "[?e1, ?e0] : ns_public"
  proof (rule Fake_NS1)
    show "Nonce 0 : analz (knows Spy [?e0])" by eval
  qed
  then have "[?e2, ?e1, ?e0] : ns_public"
  proof (rule NS2)
    show "Says Spy Bob (Crypt (pubEK Bob) {|Nonce 0, Agent Alice|}) \<in> set [?e1, ?e0]" by simp
    show " Nonce 1 ~: used [?e1, ?e0]" by eval
  qed
  then show "evs : ns_public"
  unfolding assms
  proof (rule NS3)
    show "  Says Alice Spy (Crypt (pubEK Spy) {|Nonce 0, Agent Alice|}) \<in> set [?e2, ?e1, ?e0]" by simp
    show "Says Bob Alice (Crypt (pubEK Alice) {|Nonce 0, Nonce 1|})
    : set [?e2, ?e1, ?e0]" by simp
  qed
  from assms show "Nonce NB : analz (knows Spy evs)"
    apply simp
    apply (rule analz.intros(4))
    apply (rule analz.intros(1))
    apply (auto simp add: bad_def)
    done
qed

end