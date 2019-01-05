(*  Title:      HOL/Auth/ZhouGollmann.thy
    Author:     Giampaolo Bella and L C Paulson, Cambridge Univ Computer Lab
    Copyright   2003  University of Cambridge

The protocol of
  Jianying Zhou and Dieter Gollmann,
  A Fair Non-Repudiation Protocol,
  Security and Privacy 1996 (Oakland)
  55-61
*)

theory ZhouGollmann imports Public begin

abbreviation
  TTP :: agent where "TTP == Server"

abbreviation f_sub :: nat where "f_sub == 5"
abbreviation f_nro :: nat where "f_nro == 2"
abbreviation f_nrr :: nat where "f_nrr == 3"
abbreviation f_con :: nat where "f_con == 4"


definition broken :: "agent set" where    
    \<comment> \<open>the compromised honest agents; TTP is included as it's not allowed to
        use the protocol\<close>
   "broken == bad - {Spy}"

declare broken_def [simp]

inductive_set zg :: "event list set"
  where

  Nil:  "[] \<in> zg"

| Fake: "[| evsf \<in> zg;  X \<in> synth (analz (spies evsf)) |]
         ==> Says Spy B X  # evsf \<in> zg"

| Reception:  "[| evsr \<in> zg; Says A B X \<in> set evsr |] ==> Gets B X # evsr \<in> zg"

  (*L is fresh for honest agents.
    We don't require K to be fresh because we don't bother to prove secrecy!
    We just assume that the protocol's objective is to deliver K fairly,
    rather than to keep M secret.*)
| ZG1: "[| evs1 \<in> zg;  Nonce L \<notin> used evs1; C = Crypt K (Number m);
           K \<in> symKeys;
           NRO = Crypt (priK A) \<lbrace>Number f_nro, Agent B, Nonce L, C\<rbrace>|]
       ==> Says A B \<lbrace>Number f_nro, Agent B, Nonce L, C, NRO\<rbrace> # evs1 \<in> zg"

  (*B must check that NRO is A's signature to learn the sender's name*)
| ZG2: "[| evs2 \<in> zg;
           Gets B \<lbrace>Number f_nro, Agent B, Nonce L, C, NRO\<rbrace> \<in> set evs2;
           NRO = Crypt (priK A) \<lbrace>Number f_nro, Agent B, Nonce L, C\<rbrace>;
           NRR = Crypt (priK B) \<lbrace>Number f_nrr, Agent A, Nonce L, C\<rbrace>|]
       ==> Says B A \<lbrace>Number f_nrr, Agent A, Nonce L, NRR\<rbrace> # evs2  \<in>  zg"

  (*A must check that NRR is B's signature to learn the sender's name;
    without spy, the matching label would be enough*)
| ZG3: "[| evs3 \<in> zg; C = Crypt K M; K \<in> symKeys;
           Says A B \<lbrace>Number f_nro, Agent B, Nonce L, C, NRO\<rbrace> \<in> set evs3;
           Gets A \<lbrace>Number f_nrr, Agent A, Nonce L, NRR\<rbrace> \<in> set evs3;
           NRR = Crypt (priK B) \<lbrace>Number f_nrr, Agent A, Nonce L, C\<rbrace>;
           sub_K = Crypt (priK A) \<lbrace>Number f_sub, Agent B, Nonce L, Key K\<rbrace>|]
       ==> Says A TTP \<lbrace>Number f_sub, Agent B, Nonce L, Key K, sub_K\<rbrace>
             # evs3 \<in> zg"

 (*TTP checks that sub_K is A's signature to learn who issued K, then
   gives credentials to A and B.  The Notes event models the availability of
   the credentials, but the act of fetching them is not modelled.  We also
   give con_K to the Spy. This makes the threat model more dangerous, while 
   also allowing lemma @{text Crypt_used_imp_spies} to omit the condition
   @{term "K \<noteq> priK TTP"}. *)
| ZG4: "[| evs4 \<in> zg; K \<in> symKeys;
           Gets TTP \<lbrace>Number f_sub, Agent B, Nonce L, Key K, sub_K\<rbrace>
             \<in> set evs4;
           sub_K = Crypt (priK A) \<lbrace>Number f_sub, Agent B, Nonce L, Key K\<rbrace>;
           con_K = Crypt (priK TTP) \<lbrace>Number f_con, Agent A, Agent B,
                                      Nonce L, Key K\<rbrace>|]
       ==> Says TTP Spy con_K
           #
           Notes TTP \<lbrace>Number f_con, Agent A, Agent B, Nonce L, Key K, con_K\<rbrace>
           # evs4 \<in> zg"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]

declare symKey_neq_priEK [simp]
declare symKey_neq_priEK [THEN not_sym, simp]


text\<open>A "possibility property": there are traces that reach the end\<close>
lemma "[|A \<noteq> B; TTP \<noteq> A; TTP \<noteq> B; K \<in> symKeys|] ==>
     \<exists>L. \<exists>evs \<in> zg.
           Notes TTP \<lbrace>Number f_con, Agent A, Agent B, Nonce L, Key K,
               Crypt (priK TTP) \<lbrace>Number f_con, Agent A, Agent B, Nonce L, Key K\<rbrace>\<rbrace>
               \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] zg.Nil
                    [THEN zg.ZG1, THEN zg.Reception [of _ A B],
                     THEN zg.ZG2, THEN zg.Reception [of _ B A],
                     THEN zg.ZG3, THEN zg.Reception [of _ A TTP], 
                     THEN zg.ZG4])
apply (basic_possibility, auto)
done

subsection \<open>Basic Lemmas\<close>

lemma Gets_imp_Says:
     "[| Gets B X \<in> set evs; evs \<in> zg |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule zg.induct, auto)
done

lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> zg |]  ==> X \<in> spies evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)


text\<open>Lets us replace proofs about \<^term>\<open>used evs\<close> by simpler proofs 
about \<^term>\<open>parts (spies evs)\<close>.\<close>
lemma Crypt_used_imp_spies:
     "[| Crypt K X \<in> used evs; evs \<in> zg |]
      ==> Crypt K X \<in> parts (spies evs)"
apply (erule rev_mp)
apply (erule zg.induct)
apply (simp_all add: parts_insert_knows_A) 
done

lemma Notes_TTP_imp_Gets:
     "[|Notes TTP \<lbrace>Number f_con, Agent A, Agent B, Nonce L, Key K, con_K\<rbrace>
           \<in> set evs;
        sub_K = Crypt (priK A) \<lbrace>Number f_sub, Agent B, Nonce L, Key K\<rbrace>;
        evs \<in> zg|]
    ==> Gets TTP \<lbrace>Number f_sub, Agent B, Nonce L, Key K, sub_K\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule zg.induct, auto)
done

text\<open>For reasoning about C, which is encrypted in message ZG2\<close>
lemma ZG2_msg_in_parts_spies:
     "[|Gets B \<lbrace>F, B', L, C, X\<rbrace> \<in> set evs; evs \<in> zg|]
      ==> C \<in> parts (spies evs)"
by (blast dest: Gets_imp_Says)

(*classical regularity lemma on priK*)
lemma Spy_see_priK [simp]:
     "evs \<in> zg ==> (Key (priK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, auto)
done

text\<open>So that blast can use it too\<close>
declare  Spy_see_priK [THEN [2] rev_iffD1, dest!]

lemma Spy_analz_priK [simp]:
     "evs \<in> zg ==> (Key (priK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto 


subsection\<open>About NRO: Validity for \<^term>\<open>B\<close>\<close>

text\<open>Below we prove that if \<^term>\<open>NRO\<close> exists then \<^term>\<open>A\<close> definitely
sent it, provided \<^term>\<open>A\<close> is not broken.\<close>

text\<open>Strong conclusion for a good agent\<close>
lemma NRO_validity_good:
     "[|NRO = Crypt (priK A) \<lbrace>Number f_nro, Agent B, Nonce L, C\<rbrace>;
        NRO \<in> parts (spies evs);
        A \<notin> bad;  evs \<in> zg |]
     ==> Says A B \<lbrace>Number f_nro, Agent B, Nonce L, C, NRO\<rbrace> \<in> set evs"
apply clarify
apply (erule rev_mp)
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, auto)  
done

lemma NRO_sender:
     "[|Says A' B \<lbrace>n, b, l, C, Crypt (priK A) X\<rbrace> \<in> set evs; evs \<in> zg|]
    ==> A' \<in> {A,Spy}"
apply (erule rev_mp)  
apply (erule zg.induct, simp_all)
done

text\<open>Holds also for \<^term>\<open>A = Spy\<close>!\<close>
theorem NRO_validity:
     "[|Gets B \<lbrace>Number f_nro, Agent B, Nonce L, C, NRO\<rbrace> \<in> set evs;
        NRO = Crypt (priK A) \<lbrace>Number f_nro, Agent B, Nonce L, C\<rbrace>;
        A \<notin> broken;  evs \<in> zg |]
     ==> Says A B \<lbrace>Number f_nro, Agent B, Nonce L, C, NRO\<rbrace> \<in> set evs"
apply (drule Gets_imp_Says, assumption) 
apply clarify 
apply (frule NRO_sender, auto)
txt\<open>We are left with the case where the sender is \<^term>\<open>Spy\<close> and not
  equal to \<^term>\<open>A\<close>, because \<^term>\<open>A \<notin> bad\<close>. 
  Thus theorem \<open>NRO_validity_good\<close> applies.\<close>
apply (blast dest: NRO_validity_good [OF refl])
done


subsection\<open>About NRR: Validity for \<^term>\<open>A\<close>\<close>

text\<open>Below we prove that if \<^term>\<open>NRR\<close> exists then \<^term>\<open>B\<close> definitely
sent it, provided \<^term>\<open>B\<close> is not broken.\<close>

text\<open>Strong conclusion for a good agent\<close>
lemma NRR_validity_good:
     "[|NRR = Crypt (priK B) \<lbrace>Number f_nrr, Agent A, Nonce L, C\<rbrace>;
        NRR \<in> parts (spies evs);
        B \<notin> bad;  evs \<in> zg |]
     ==> Says B A \<lbrace>Number f_nrr, Agent A, Nonce L, NRR\<rbrace> \<in> set evs"
apply clarify
apply (erule rev_mp)
apply (erule zg.induct) 
apply (frule_tac [5] ZG2_msg_in_parts_spies, auto)  
done

lemma NRR_sender:
     "[|Says B' A \<lbrace>n, a, l, Crypt (priK B) X\<rbrace> \<in> set evs; evs \<in> zg|]
    ==> B' \<in> {B,Spy}"
apply (erule rev_mp)  
apply (erule zg.induct, simp_all)
done

text\<open>Holds also for \<^term>\<open>B = Spy\<close>!\<close>
theorem NRR_validity:
     "[|Says B' A \<lbrace>Number f_nrr, Agent A, Nonce L, NRR\<rbrace> \<in> set evs;
        NRR = Crypt (priK B) \<lbrace>Number f_nrr, Agent A, Nonce L, C\<rbrace>;
        B \<notin> broken; evs \<in> zg|]
    ==> Says B A \<lbrace>Number f_nrr, Agent A, Nonce L, NRR\<rbrace> \<in> set evs"
apply clarify 
apply (frule NRR_sender, auto)
txt\<open>We are left with the case where \<^term>\<open>B' = Spy\<close> and  \<^term>\<open>B' \<noteq> B\<close>,
  i.e. \<^term>\<open>B \<notin> bad\<close>, when we can apply \<open>NRR_validity_good\<close>.\<close>
 apply (blast dest: NRR_validity_good [OF refl])
done


subsection\<open>Proofs About \<^term>\<open>sub_K\<close>\<close>

text\<open>Below we prove that if \<^term>\<open>sub_K\<close> exists then \<^term>\<open>A\<close> definitely
sent it, provided \<^term>\<open>A\<close> is not broken.\<close>

text\<open>Strong conclusion for a good agent\<close>
lemma sub_K_validity_good:
     "[|sub_K = Crypt (priK A) \<lbrace>Number f_sub, Agent B, Nonce L, Key K\<rbrace>;
        sub_K \<in> parts (spies evs);
        A \<notin> bad;  evs \<in> zg |]
     ==> Says A TTP \<lbrace>Number f_sub, Agent B, Nonce L, Key K, sub_K\<rbrace> \<in> set evs"
apply clarify
apply (erule rev_mp)
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, simp_all)
txt\<open>Fake\<close> 
apply (blast dest!: Fake_parts_sing_imp_Un)
done

lemma sub_K_sender:
     "[|Says A' TTP \<lbrace>n, b, l, k, Crypt (priK A) X\<rbrace> \<in> set evs;  evs \<in> zg|]
    ==> A' \<in> {A,Spy}"
apply (erule rev_mp)  
apply (erule zg.induct, simp_all)
done

text\<open>Holds also for \<^term>\<open>A = Spy\<close>!\<close>
theorem sub_K_validity:
     "[|Gets TTP \<lbrace>Number f_sub, Agent B, Nonce L, Key K, sub_K\<rbrace> \<in> set evs;
        sub_K = Crypt (priK A) \<lbrace>Number f_sub, Agent B, Nonce L, Key K\<rbrace>;
        A \<notin> broken;  evs \<in> zg |]
     ==> Says A TTP \<lbrace>Number f_sub, Agent B, Nonce L, Key K, sub_K\<rbrace> \<in> set evs"
apply (drule Gets_imp_Says, assumption) 
apply clarify 
apply (frule sub_K_sender, auto)
txt\<open>We are left with the case where the sender is \<^term>\<open>Spy\<close> and not
  equal to \<^term>\<open>A\<close>, because \<^term>\<open>A \<notin> bad\<close>. 
  Thus theorem \<open>sub_K_validity_good\<close> applies.\<close>
apply (blast dest: sub_K_validity_good [OF refl])
done



subsection\<open>Proofs About \<^term>\<open>con_K\<close>\<close>

text\<open>Below we prove that if \<^term>\<open>con_K\<close> exists, then \<^term>\<open>TTP\<close> has it,
and therefore \<^term>\<open>A\<close> and \<^term>\<open>B\<close>) can get it too.  Moreover, we know
that \<^term>\<open>A\<close> sent \<^term>\<open>sub_K\<close>\<close>

lemma con_K_validity:
     "[|con_K \<in> used evs;
        con_K = Crypt (priK TTP)
                  \<lbrace>Number f_con, Agent A, Agent B, Nonce L, Key K\<rbrace>;
        evs \<in> zg |]
    ==> Notes TTP \<lbrace>Number f_con, Agent A, Agent B, Nonce L, Key K, con_K\<rbrace>
          \<in> set evs"
apply clarify
apply (erule rev_mp)
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, simp_all)
txt\<open>Fake\<close>
apply (blast dest!: Fake_parts_sing_imp_Un)
txt\<open>ZG2\<close> 
apply (blast dest: parts_cut)
done

text\<open>If \<^term>\<open>TTP\<close> holds \<^term>\<open>con_K\<close> then \<^term>\<open>A\<close> sent
 \<^term>\<open>sub_K\<close>.  We assume that \<^term>\<open>A\<close> is not broken.  Importantly, nothing
  needs to be assumed about the form of \<^term>\<open>con_K\<close>!\<close>
lemma Notes_TTP_imp_Says_A:
     "[|Notes TTP \<lbrace>Number f_con, Agent A, Agent B, Nonce L, Key K, con_K\<rbrace>
           \<in> set evs;
        sub_K = Crypt (priK A) \<lbrace>Number f_sub, Agent B, Nonce L, Key K\<rbrace>;
        A \<notin> broken; evs \<in> zg|]
     ==> Says A TTP \<lbrace>Number f_sub, Agent B, Nonce L, Key K, sub_K\<rbrace> \<in> set evs"
apply clarify
apply (erule rev_mp)
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, simp_all)
txt\<open>ZG4\<close>
apply clarify 
apply (rule sub_K_validity, auto) 
done

text\<open>If \<^term>\<open>con_K\<close> exists, then \<^term>\<open>A\<close> sent \<^term>\<open>sub_K\<close>.  We again
   assume that \<^term>\<open>A\<close> is not broken.\<close>
theorem B_sub_K_validity:
     "[|con_K \<in> used evs;
        con_K = Crypt (priK TTP) \<lbrace>Number f_con, Agent A, Agent B,
                                   Nonce L, Key K\<rbrace>;
        sub_K = Crypt (priK A) \<lbrace>Number f_sub, Agent B, Nonce L, Key K\<rbrace>;
        A \<notin> broken; evs \<in> zg|]
     ==> Says A TTP \<lbrace>Number f_sub, Agent B, Nonce L, Key K, sub_K\<rbrace> \<in> set evs"
by (blast dest: con_K_validity Notes_TTP_imp_Says_A)


subsection\<open>Proving fairness\<close>

text\<open>Cannot prove that, if \<^term>\<open>B\<close> has NRO, then  \<^term>\<open>A\<close> has her NRR.
It would appear that \<^term>\<open>B\<close> has a small advantage, though it is
useless to win disputes: \<^term>\<open>B\<close> needs to present \<^term>\<open>con_K\<close> as well.\<close>

text\<open>Strange: unicity of the label protects \<^term>\<open>A\<close>?\<close>
lemma A_unicity: 
     "[|NRO = Crypt (priK A) \<lbrace>Number f_nro, Agent B, Nonce L, Crypt K M\<rbrace>;
        NRO \<in> parts (spies evs);
        Says A B \<lbrace>Number f_nro, Agent B, Nonce L, Crypt K M', NRO'\<rbrace>
          \<in> set evs;
        A \<notin> bad; evs \<in> zg |]
     ==> M'=M"
apply clarify
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, auto) 
txt\<open>ZG1: freshness\<close>
apply (blast dest: parts.Body) 
done


text\<open>Fairness lemma: if \<^term>\<open>sub_K\<close> exists, then \<^term>\<open>A\<close> holds 
NRR.  Relies on unicity of labels.\<close>
lemma sub_K_implies_NRR:
     "[| NRO = Crypt (priK A) \<lbrace>Number f_nro, Agent B, Nonce L, Crypt K M\<rbrace>;
         NRR = Crypt (priK B) \<lbrace>Number f_nrr, Agent A, Nonce L, Crypt K M\<rbrace>;
         sub_K \<in> parts (spies evs);
         NRO \<in> parts (spies evs);
         sub_K = Crypt (priK A) \<lbrace>Number f_sub, Agent B, Nonce L, Key K\<rbrace>;
         A \<notin> bad;  evs \<in> zg |]
     ==> Gets A \<lbrace>Number f_nrr, Agent A, Nonce L, NRR\<rbrace> \<in> set evs"
apply clarify
apply hypsubst_thin
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, simp_all)
txt\<open>Fake\<close>
apply blast 
txt\<open>ZG1: freshness\<close>
apply (blast dest: parts.Body) 
txt\<open>ZG3\<close> 
apply (blast dest: A_unicity [OF refl]) 
done


lemma Crypt_used_imp_L_used:
     "[| Crypt (priK TTP) \<lbrace>F, A, B, L, K\<rbrace> \<in> used evs; evs \<in> zg |]
      ==> L \<in> used evs"
apply (erule rev_mp)
apply (erule zg.induct, auto)
txt\<open>Fake\<close>
apply (blast dest!: Fake_parts_sing_imp_Un)
txt\<open>ZG2: freshness\<close>
apply (blast dest: parts.Body) 
done


text\<open>Fairness for \<^term>\<open>A\<close>: if \<^term>\<open>con_K\<close> and \<^term>\<open>NRO\<close> exist, 
then \<^term>\<open>A\<close> holds NRR.  \<^term>\<open>A\<close> must be uncompromised, but there is no
assumption about \<^term>\<open>B\<close>.\<close>
theorem A_fairness_NRO:
     "[|con_K \<in> used evs;
        NRO \<in> parts (spies evs);
        con_K = Crypt (priK TTP)
                      \<lbrace>Number f_con, Agent A, Agent B, Nonce L, Key K\<rbrace>;
        NRO = Crypt (priK A) \<lbrace>Number f_nro, Agent B, Nonce L, Crypt K M\<rbrace>;
        NRR = Crypt (priK B) \<lbrace>Number f_nrr, Agent A, Nonce L, Crypt K M\<rbrace>;
        A \<notin> bad;  evs \<in> zg |]
    ==> Gets A \<lbrace>Number f_nrr, Agent A, Nonce L, NRR\<rbrace> \<in> set evs"
apply clarify
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, simp_all)
   txt\<open>Fake\<close>
   apply (simp add: parts_insert_knows_A) 
   apply (blast dest: Fake_parts_sing_imp_Un) 
  txt\<open>ZG1\<close>
  apply (blast dest: Crypt_used_imp_L_used) 
 txt\<open>ZG2\<close>
 apply (blast dest: parts_cut)
txt\<open>ZG4\<close> 
apply (blast intro: sub_K_implies_NRR [OF refl] 
             dest: Gets_imp_knows_Spy [THEN parts.Inj])
done

text\<open>Fairness for \<^term>\<open>B\<close>: NRR exists at all, then \<^term>\<open>B\<close> holds NRO.
\<^term>\<open>B\<close> must be uncompromised, but there is no assumption about \<^term>\<open>A\<close>.\<close>
theorem B_fairness_NRR:
     "[|NRR \<in> used evs;
        NRR = Crypt (priK B) \<lbrace>Number f_nrr, Agent A, Nonce L, C\<rbrace>;
        NRO = Crypt (priK A) \<lbrace>Number f_nro, Agent B, Nonce L, C\<rbrace>;
        B \<notin> bad; evs \<in> zg |]
    ==> Gets B \<lbrace>Number f_nro, Agent B, Nonce L, C, NRO\<rbrace> \<in> set evs"
apply clarify
apply (erule rev_mp)
apply (erule zg.induct)
apply (frule_tac [5] ZG2_msg_in_parts_spies, simp_all)
txt\<open>Fake\<close>
apply (blast dest!: Fake_parts_sing_imp_Un)
txt\<open>ZG2\<close>
apply (blast dest: parts_cut)
done


text\<open>If \<^term>\<open>con_K\<close> exists at all, then \<^term>\<open>B\<close> can get it, by \<open>con_K_validity\<close>.  Cannot conclude that also NRO is available to \<^term>\<open>B\<close>,
because if \<^term>\<open>A\<close> were unfair, \<^term>\<open>A\<close> could build message 3 without
building message 1, which contains NRO.\<close>

end
