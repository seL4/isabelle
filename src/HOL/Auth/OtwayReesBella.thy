(*  Title:      HOL/Auth/OtwayReesBella.thy
    Author:     Giampaolo Bella, Catania University
*)

header{*Bella's version of the Otway-Rees protocol*}


theory OtwayReesBella imports Public begin

text{*Bella's modifications to a version of the Otway-Rees protocol taken from
the BAN paper only concern message 7. The updated protocol makes the goal of
key distribution of the session key available to A. Investigating the
principle of Goal Availability undermines the BAN claim about the original
protocol, that "this protocol does not make use of Kab as an encryption key,
so neither principal can know whether the key is known to the other". The
updated protocol makes no use of the session key to encrypt but informs A that
B knows it.*}

inductive_set orb :: "event list set"
 where

  Nil:  "[]\<in> orb"

| Fake: "\<lbrakk>evsa\<in> orb;  X\<in> synth (analz (knows Spy evsa))\<rbrakk>
         \<Longrightarrow> Says Spy B X  # evsa \<in> orb"

| Reception: "\<lbrakk>evsr\<in> orb;  Says A B X \<in> set evsr\<rbrakk>
              \<Longrightarrow> Gets B X # evsr \<in> orb"

| OR1:  "\<lbrakk>evs1\<in> orb;  Nonce NA \<notin> used evs1\<rbrakk>
         \<Longrightarrow> Says A B \<lbrace>Nonce M, Agent A, Agent B, 
                   Crypt (shrK A) \<lbrace>Nonce NA, Nonce M, Agent A, Agent B\<rbrace>\<rbrace> 
               # evs1 \<in> orb"

| OR2:  "\<lbrakk>evs2\<in> orb;  Nonce NB \<notin> used evs2;
           Gets B \<lbrace>Nonce M, Agent A, Agent B, X\<rbrace> \<in> set evs2\<rbrakk>
        \<Longrightarrow> Says B Server 
                \<lbrace>Nonce M, Agent A, Agent B, X, 
           Crypt (shrK B) \<lbrace>Nonce NB, Nonce M, Nonce M, Agent A, Agent B\<rbrace>\<rbrace>
               # evs2 \<in> orb"

| OR3:  "\<lbrakk>evs3\<in> orb;  Key KAB \<notin> used evs3;
          Gets Server 
             \<lbrace>Nonce M, Agent A, Agent B, 
               Crypt (shrK A) \<lbrace>Nonce NA, Nonce M, Agent A, Agent B\<rbrace>, 
               Crypt (shrK B) \<lbrace>Nonce NB, Nonce M, Nonce M, Agent A, Agent B\<rbrace>\<rbrace>
          \<in> set evs3\<rbrakk>
        \<Longrightarrow> Says Server B \<lbrace>Nonce M,
                    Crypt (shrK B) \<lbrace>Crypt (shrK A) \<lbrace>Nonce NA, Key KAB\<rbrace>,
                                      Nonce NB, Key KAB\<rbrace>\<rbrace>
               # evs3 \<in> orb"

  (*B can only check that the message he is bouncing is a ciphertext*)
  (*Sending M back is omitted*)   
| OR4:  "\<lbrakk>evs4\<in> orb; B \<noteq> Server; \<forall> p q. X \<noteq> \<lbrace>p, q\<rbrace>; 
          Says B Server \<lbrace>Nonce M, Agent A, Agent B, X', 
                Crypt (shrK B) \<lbrace>Nonce NB, Nonce M, Nonce M, Agent A, Agent B\<rbrace>\<rbrace>
            \<in> set evs4;
          Gets B \<lbrace>Nonce M, Crypt (shrK B) \<lbrace>X, Nonce NB, Key KAB\<rbrace>\<rbrace>
            \<in> set evs4\<rbrakk>
        \<Longrightarrow> Says B A \<lbrace>Nonce M, X\<rbrace> # evs4 \<in> orb"


| Oops: "\<lbrakk>evso\<in> orb;  
           Says Server B \<lbrace>Nonce M,
                    Crypt (shrK B) \<lbrace>Crypt (shrK A) \<lbrace>Nonce NA, Key KAB\<rbrace>,
                                      Nonce NB, Key KAB\<rbrace>\<rbrace> 
             \<in> set evso\<rbrakk>
 \<Longrightarrow> Notes Spy \<lbrace>Agent A, Agent B, Nonce NA, Nonce NB, Key KAB\<rbrace> # evso 
     \<in> orb"



declare knows_Spy_partsEs [elim]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]


text{*Fragile proof, with backtracking in the possibility call.*}
lemma possibility_thm: "\<lbrakk>A \<noteq> Server; B \<noteq> Server; Key K \<notin> used[]\<rbrakk>    
      \<Longrightarrow>   \<exists> evs \<in> orb.           
     Says B A \<lbrace>Nonce M, Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>\<rbrace> \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] orb.Nil
                    [THEN orb.OR1, THEN orb.Reception,
                     THEN orb.OR2, THEN orb.Reception,
                     THEN orb.OR3, THEN orb.Reception, THEN orb.OR4]) 
apply (possibility, simp add: used_Cons)  
done


lemma Gets_imp_Says :
     "\<lbrakk>Gets B X \<in> set evs; evs \<in> orb\<rbrakk> \<Longrightarrow> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule orb.induct)
apply auto
done

lemma Gets_imp_knows_Spy: 
     "\<lbrakk>Gets B X \<in> set evs; evs \<in> orb\<rbrakk>  \<Longrightarrow> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)

declare Gets_imp_knows_Spy [THEN parts.Inj, dest]

lemma Gets_imp_knows:
     "\<lbrakk>Gets B X \<in> set evs; evs \<in> orb\<rbrakk>  \<Longrightarrow> X \<in> knows B evs"
by (metis Gets_imp_knows_Spy Gets_imp_knows_agents)

lemma OR2_analz_knows_Spy: 
   "\<lbrakk>Gets B \<lbrace>Nonce M, Agent A, Agent B, X\<rbrace> \<in> set evs; evs \<in> orb\<rbrakk>   
    \<Longrightarrow> X \<in> analz (knows Spy evs)"
by (blast dest!: Gets_imp_knows_Spy [THEN analz.Inj])

lemma OR4_parts_knows_Spy: 
   "\<lbrakk>Gets B \<lbrace>Nonce M, Crypt (shrK B) \<lbrace>X, Nonce Nb, Key Kab\<rbrace>\<rbrace>  \<in> set evs; 
      evs \<in> orb\<rbrakk>   \<Longrightarrow> X \<in> parts (knows Spy evs)"
by blast

lemma Oops_parts_knows_Spy: 
    "Says Server B \<lbrace>Nonce M, Crypt K' \<lbrace>X, Nonce Nb, K\<rbrace>\<rbrace> \<in> set evs  
     \<Longrightarrow> K \<in> parts (knows Spy evs)"
by blast

lemmas OR2_parts_knows_Spy =
    OR2_analz_knows_Spy [THEN analz_into_parts]

ML
{*
fun parts_explicit_tac i = 
    forward_tac [@{thm Oops_parts_knows_Spy}] (i+7) THEN
    forward_tac [@{thm OR4_parts_knows_Spy}]  (i+6) THEN
    forward_tac [@{thm OR2_parts_knows_Spy}]  (i+4)
*}
 
method_setup parts_explicit = {*
    Scan.succeed (K (SIMPLE_METHOD' parts_explicit_tac)) *}
  "to explicitly state that some message components belong to parts knows Spy"


lemma Spy_see_shrK [simp]: 
    "evs \<in> orb \<Longrightarrow> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
by (erule orb.induct, parts_explicit, simp_all, blast+)

lemma Spy_analz_shrK [simp]: 
"evs \<in> orb \<Longrightarrow> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[|Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> orb|] ==> A \<in> bad"
by (blast dest: Spy_see_shrK)

lemma new_keys_not_used [simp]:
   "\<lbrakk>Key K \<notin> used evs; K \<in> symKeys; evs \<in> orb\<rbrakk>  \<Longrightarrow> K \<notin> keysFor (parts (knows Spy evs))"
apply (erule rev_mp)
apply (erule orb.induct, parts_explicit, simp_all)
apply (force dest!: keysFor_parts_insert)
apply (blast+)
done



subsection{* Proofs involving analz *}

text{*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*}
lemma Says_Server_message_form: 
"\<lbrakk>Says Server B  \<lbrace>Nonce M, Crypt (shrK B) \<lbrace>X, Nonce Nb, Key K\<rbrace>\<rbrace> \<in> set evs;  
     evs \<in> orb\<rbrakk>                                            
 \<Longrightarrow> K \<notin> range shrK & (\<exists> A Na. X=(Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>))"
by (erule rev_mp, erule orb.induct, simp_all)

lemma Says_Server_imp_Gets: 
 "\<lbrakk>Says Server B \<lbrace>Nonce M, Crypt (shrK B) \<lbrace>Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>,
                                             Nonce Nb, Key K\<rbrace>\<rbrace> \<in> set evs;
    evs \<in> orb\<rbrakk>
  \<Longrightarrow>  Gets Server \<lbrace>Nonce M, Agent A, Agent B, 
                   Crypt (shrK A) \<lbrace>Nonce Na, Nonce M, Agent A, Agent B\<rbrace>, 
               Crypt (shrK B) \<lbrace>Nonce Nb, Nonce M, Nonce M, Agent A, Agent B\<rbrace>\<rbrace>
         \<in> set evs"
by (erule rev_mp, erule orb.induct, simp_all)


lemma A_trusts_OR1: 
"\<lbrakk>Crypt (shrK A) \<lbrace>Nonce Na, Nonce M, Agent A, Agent B\<rbrace> \<in> parts (knows Spy evs);  
    A \<notin> bad; evs \<in> orb\<rbrakk>                   
 \<Longrightarrow> Says A B \<lbrace>Nonce M, Agent A, Agent B, Crypt (shrK A) \<lbrace>Nonce Na, Nonce M, Agent A, Agent B\<rbrace>\<rbrace> \<in> set evs"
apply (erule rev_mp, erule orb.induct, parts_explicit, simp_all)
apply (blast)
done


lemma B_trusts_OR2:
 "\<lbrakk>Crypt (shrK B) \<lbrace>Nonce Nb, Nonce M, Nonce M, Agent A, Agent B\<rbrace>  
      \<in> parts (knows Spy evs);  B \<notin> bad; evs \<in> orb\<rbrakk>                   
  \<Longrightarrow> (\<exists> X. Says B Server \<lbrace>Nonce M, Agent A, Agent B, X,  
              Crypt (shrK B) \<lbrace>Nonce Nb, Nonce M, Nonce M, Agent A, Agent B\<rbrace>\<rbrace> 
          \<in> set evs)"
apply (erule rev_mp, erule orb.induct, parts_explicit, simp_all)
apply (blast+)
done


lemma B_trusts_OR3: 
"\<lbrakk>Crypt (shrK B) \<lbrace>X, Nonce Nb, Key K\<rbrace> \<in> parts (knows Spy evs);  
   B \<notin> bad; evs \<in> orb\<rbrakk>                   
\<Longrightarrow> \<exists> M. Says Server B \<lbrace>Nonce M, Crypt (shrK B) \<lbrace>X, Nonce Nb, Key K\<rbrace>\<rbrace> 
         \<in> set evs"
apply (erule rev_mp, erule orb.induct, parts_explicit, simp_all)
apply (blast+)
done

lemma Gets_Server_message_form: 
"\<lbrakk>Gets B \<lbrace>Nonce M, Crypt (shrK B) \<lbrace>X, Nonce Nb, Key K\<rbrace>\<rbrace> \<in> set evs;  
    evs \<in> orb\<rbrakk>                                              
 \<Longrightarrow> (K \<notin> range shrK & (\<exists> A Na. X = (Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>)))    
             | X \<in> analz (knows Spy evs)"
by (metis B_trusts_OR3 Crypt_Spy_analz_bad Gets_imp_Says MPair_analz MPair_parts
          Says_Server_message_form Says_imp_analz_Spy Says_imp_parts_knows_Spy)

lemma unique_Na: "\<lbrakk>Says A B  \<lbrace>Nonce M, Agent A, Agent B, Crypt (shrK A) \<lbrace>Nonce Na, Nonce M, Agent A, Agent B\<rbrace>\<rbrace> \<in> set evs;   
         Says A B' \<lbrace>Nonce M', Agent A, Agent B', Crypt (shrK A) \<lbrace>Nonce Na, Nonce M', Agent A, Agent B'\<rbrace>\<rbrace> \<in> set evs;  
    A \<notin> bad; evs \<in> orb\<rbrakk> \<Longrightarrow> B=B' & M=M'"
by (erule rev_mp, erule rev_mp, erule orb.induct, simp_all, blast+)

lemma unique_Nb: "\<lbrakk>Says B Server \<lbrace>Nonce M, Agent A, Agent B, X, Crypt (shrK B) \<lbrace>Nonce Nb, Nonce M, Nonce M, Agent A, Agent B\<rbrace>\<rbrace> \<in> set evs;   
         Says B Server \<lbrace>Nonce M', Agent A', Agent B, X', Crypt (shrK B) \<lbrace>Nonce Nb,Nonce M', Nonce M', Agent A', Agent B\<rbrace>\<rbrace> \<in> set evs;   
    B \<notin> bad; evs \<in> orb\<rbrakk> \<Longrightarrow>   M=M' & A=A' & X=X'"
by (erule rev_mp, erule rev_mp, erule orb.induct, simp_all, blast+)

lemma analz_image_freshCryptK_lemma:
"(Crypt K X \<in> analz (Key`nE \<union> H)) \<longrightarrow> (Crypt K X \<in> analz H) \<Longrightarrow>  
        (Crypt K X \<in> analz (Key`nE \<union> H)) = (Crypt K X \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

ML
{*
structure OtwayReesBella =
struct

val analz_image_freshK_ss = 
  @{simpset} delsimps [image_insert, image_Un]
      delsimps [@{thm imp_disjL}]    (*reduces blow-up*)
      addsimps @{thms analz_image_freshK_simps}

end
*}

method_setup analz_freshCryptK = {*
    Scan.succeed (fn ctxt =>
     (SIMPLE_METHOD
      (EVERY [REPEAT_FIRST (resolve_tac [allI, ballI, impI]),
          REPEAT_FIRST (rtac @{thm analz_image_freshCryptK_lemma}),
          ALLGOALS (asm_simp_tac
            (Simplifier.context ctxt OtwayReesBella.analz_image_freshK_ss))]))) *}
  "for proving useful rewrite rule"


method_setup disentangle = {*
    Scan.succeed
     (K (SIMPLE_METHOD
      (REPEAT_FIRST (eresolve_tac [asm_rl, conjE, disjE] 
                   ORELSE' hyp_subst_tac)))) *}
  "for eliminating conjunctions, disjunctions and the like"



lemma analz_image_freshCryptK [rule_format]: 
"evs \<in> orb \<Longrightarrow>                              
     Key K \<notin> analz (knows Spy evs) \<longrightarrow>  
       (\<forall> KK. KK \<subseteq> - (range shrK) \<longrightarrow>                  
             (Crypt K X \<in> analz (Key`KK \<union> (knows Spy evs))) =   
             (Crypt K X \<in> analz (knows Spy evs)))"
apply (erule orb.induct)
apply (analz_mono_contra)
apply (frule_tac [7] Gets_Server_message_form)
apply (frule_tac [9] Says_Server_message_form)
apply disentangle
apply (drule_tac [5] Gets_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd, THEN analz.Snd, THEN  analz.Snd])
prefer 8 apply clarify
apply (analz_freshCryptK, spy_analz, fastforce)
done



lemma analz_insert_freshCryptK: 
"\<lbrakk>evs \<in> orb;  Key K \<notin> analz (knows Spy evs);  
         Seskey \<notin> range shrK\<rbrakk> \<Longrightarrow>   
         (Crypt K X \<in> analz (insert (Key Seskey) (knows Spy evs))) =  
         (Crypt K X \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshCryptK analz_image_freshK_simps)


lemma analz_hard: 
"\<lbrakk>Says A B \<lbrace>Nonce M, Agent A, Agent B,  
             Crypt (shrK A) \<lbrace>Nonce Na, Nonce M, Agent A, Agent B\<rbrace>\<rbrace> \<in>set evs; 
   Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace> \<in> analz (knows Spy evs);  
   A \<notin> bad; B \<notin> bad; evs \<in> orb\<rbrakk>                   
 \<Longrightarrow>  Says B A \<lbrace>Nonce M, Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule orb.induct)
apply (frule_tac [7] Gets_Server_message_form)
apply (frule_tac [9] Says_Server_message_form)
apply disentangle
txt{*letting the simplifier solve OR2*}
apply (drule_tac [5] Gets_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd, THEN analz.Snd, THEN analz.Snd])
apply (simp_all (no_asm_simp) add: analz_insert_eq pushes split_ifs)
apply (spy_analz)
txt{*OR1*}
apply blast
txt{*Oops*}
prefer 4 apply (blast dest: analz_insert_freshCryptK)
txt{*OR4 - ii*}
prefer 3 apply (blast)
txt{*OR3*}
(*adding Gets_imp_ and Says_imp_ for efficiency*)
apply (blast dest: 
       A_trusts_OR1 unique_Na Key_not_used analz_insert_freshCryptK)
txt{*OR4 - i *}
apply clarify
apply (simp add: pushes split_ifs)
apply (case_tac "Aaa\<in>bad")
apply (blast dest: analz_insert_freshCryptK)
apply clarify
apply simp
apply (case_tac "Ba\<in>bad")
apply (frule Gets_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd, THEN analz.Decrypt, THEN analz.Fst] , assumption)
apply (simp (no_asm_simp))
apply clarify
apply (frule Gets_imp_knows_Spy 
             [THEN parts.Inj, THEN parts.Snd, THEN B_trusts_OR3],  
       assumption, assumption, assumption, erule exE)
apply (frule Says_Server_imp_Gets 
            [THEN Gets_imp_knows_Spy, THEN parts.Inj, THEN parts.Snd, 
            THEN parts.Snd, THEN parts.Snd, THEN parts.Fst, THEN A_trusts_OR1],
       assumption, assumption, assumption, assumption)
apply (blast dest: Says_Server_imp_Gets B_trusts_OR2 unique_Na unique_Nb)
done


lemma Gets_Server_message_form': 
"\<lbrakk>Gets B \<lbrace>Nonce M, Crypt (shrK B) \<lbrace>X, Nonce Nb, Key K\<rbrace>\<rbrace>  \<in> set evs;  
   B \<notin> bad; evs \<in> orb\<rbrakk>                              
  \<Longrightarrow> K \<notin> range shrK & (\<exists> A Na. X = (Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>))"
by (blast dest!: B_trusts_OR3 Says_Server_message_form)


lemma OR4_imp_Gets: 
"\<lbrakk>Says B A \<lbrace>Nonce M, Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>\<rbrace> \<in> set evs;   
   B \<notin> bad; evs \<in> orb\<rbrakk>  
 \<Longrightarrow> (\<exists> Nb. Gets B \<lbrace>Nonce M, Crypt (shrK B) \<lbrace>Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>,
                                             Nonce Nb, Key K\<rbrace>\<rbrace> \<in> set evs)"
apply (erule rev_mp, erule orb.induct, parts_explicit, simp_all)
prefer 3 apply (blast dest: Gets_Server_message_form')
apply blast+
done


lemma A_keydist_to_B: 
"\<lbrakk>Says A B \<lbrace>Nonce M, Agent A, Agent B,  
            Crypt (shrK A) \<lbrace>Nonce Na, Nonce M, Agent A, Agent B\<rbrace>\<rbrace> \<in>set evs; 
   Gets A \<lbrace>Nonce M, Crypt (shrK A) \<lbrace>Nonce Na, Key K\<rbrace>\<rbrace> \<in> set evs;    
   A \<notin> bad; B \<notin> bad; evs \<in> orb\<rbrakk>  
  \<Longrightarrow> Key K \<in> analz (knows B evs)"
apply (drule Gets_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd], assumption)
apply (drule analz_hard, assumption, assumption, assumption, assumption)
apply (drule OR4_imp_Gets, assumption, assumption)
apply (fastforce dest!: Gets_imp_knows [THEN analz.Inj] analz.Decrypt)
done


text{*Other properties as for the original protocol*}


end
