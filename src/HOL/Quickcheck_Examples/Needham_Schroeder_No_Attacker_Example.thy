theory Needham_Schroeder_No_Attacker_Example
imports Main "~~/src/HOL/Library/Predicate_Compile_Quickcheck"
begin

inductive_set ns_public :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> ns_public"
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

code_pred [skip_proof] ns_publicp .
thm ns_publicp.equation

code_pred [generator_cps] ns_publicp .
thm ns_publicp.generator_cps_equation

lemma "ns_publicp evs ==> \<not> (Says Alice Bob (Crypt (pubEK Bob) (Nonce NB))) : set evs"
(*quickcheck[random, iterations = 1000000, size = 20, timeout = 3600, verbose]
quickcheck[exhaustive, size = 8, timeout = 3600, verbose]
quickcheck[narrowing, size = 7, timeout = 3600, verbose]*)
quickcheck[smart_exhaustive, depth = 5, timeout = 30, expect = counterexample]
oops

lemma
  "\<lbrakk>ns_publicp evs\<rbrakk>            
       \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) : set evs
       \<Longrightarrow> A \<noteq> Spy \<Longrightarrow> B \<noteq> Spy \<Longrightarrow> A \<noteq> B 
           \<Longrightarrow> Nonce NB \<notin> analz (spies evs)"
quickcheck[smart_exhaustive, depth = 6, timeout = 30]
quickcheck[narrowing, size = 6, timeout = 30, verbose]
oops

end