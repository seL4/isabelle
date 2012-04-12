(*  Author:     Giampaolo Bella, Catania University
*)

header{*Original Shoup-Rubin protocol*}

theory ShoupRubin imports Smartcard begin

axiomatization sesK :: "nat*key => key"
where
   (*sesK is injective on each component*) 
   inj_sesK [iff]: "(sesK(m,k) = sesK(m',k')) = (m = m' \<and> k = k')" and
   (*all long-term keys differ from sesK*)
   shrK_disj_sesK [iff]: "shrK A \<noteq> sesK(m,pk)" and
   crdK_disj_sesK [iff]: "crdK C \<noteq> sesK(m,pk)" and
   pin_disj_sesK  [iff]: "pin P \<noteq> sesK(m,pk)" and
   pairK_disj_sesK[iff]:"pairK(A,B) \<noteq> sesK(m,pk)" and

   (*needed for base case in analz_image_freshK*)
   Atomic_distrib [iff]: "Atomic`(KEY`K \<union> NONCE`N) =
                   Atomic`(KEY`K) \<union> Atomic`(NONCE`N)" and

  (*this protocol makes the assumption of secure means
    between each agent and his smartcard*)
   shouprubin_assumes_securemeans [iff]: "evs \<in> sr \<Longrightarrow> secureM"

definition Unique :: "[event, event list] => bool" ("Unique _ on _") where
   "Unique ev on evs == 
      ev \<notin> set (tl (dropWhile (% z. z \<noteq> ev) evs))"


inductive_set sr :: "event list set"
  where

    Nil:  "[]\<in> sr"



  | Fake: "\<lbrakk> evsF\<in> sr;  X\<in> synth (analz (knows Spy evsF)); 
             illegalUse(Card B) \<rbrakk>
          \<Longrightarrow> Says Spy A X # 
              Inputs Spy (Card B) X # evsF \<in> sr"

(*In general this rule causes the assumption Card B \<notin> cloned
  in most guarantees for B - starting with confidentiality -
  otherwise pairK_confidential could not apply*)
  | Forge:
         "\<lbrakk> evsFo \<in> sr; Nonce Nb \<in> analz (knows Spy evsFo);
             Key (pairK(A,B)) \<in> knows Spy evsFo \<rbrakk>
          \<Longrightarrow> Notes Spy (Key (sesK(Nb,pairK(A,B)))) # evsFo \<in> sr"



  | Reception: "\<lbrakk> evsR\<in> sr; Says A B X \<in> set evsR \<rbrakk>
              \<Longrightarrow> Gets B X # evsR \<in> sr"



(*A AND THE SERVER *)
  | SR1:  "\<lbrakk> evs1\<in> sr; A \<noteq> Server\<rbrakk>
          \<Longrightarrow> Says A Server \<lbrace>Agent A, Agent B\<rbrace> 
                # evs1 \<in> sr"

  | SR2:  "\<lbrakk> evs2\<in> sr; 
             Gets Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs2 \<rbrakk>
          \<Longrightarrow> Says Server A \<lbrace>Nonce (Pairkey(A,B)), 
                           Crypt (shrK A) \<lbrace>Nonce (Pairkey(A,B)), Agent B\<rbrace>
                  \<rbrace>
                # evs2 \<in> sr"




(*A AND HER CARD*)
(*A cannot decrypt the verifier for she dosn't know shrK A,
  but the pairkey is recognisable*)
  | SR3:  "\<lbrakk> evs3\<in> sr; legalUse(Card A);
             Says A Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs3;
             Gets A \<lbrace>Nonce Pk, Certificate\<rbrace> \<in> set evs3 \<rbrakk>
          \<Longrightarrow> Inputs A (Card A) (Agent A)
                # evs3 \<in> sr"   (*however A only queries her card 
if she has previously contacted the server to initiate with some B. 
Otherwise she would do so even if the Server had not been active. 
Still, this doesn't and can't mean that the pairkey originated with 
the server*)
 
(*The card outputs the nonce Na to A*)               
  | SR4:  "\<lbrakk> evs4\<in> sr;  A \<noteq> Server; 
             Nonce Na \<notin> used evs4; legalUse(Card A);
             Inputs A (Card A) (Agent A) \<in> set evs4 \<rbrakk> 
       \<Longrightarrow> Outpts (Card A) A \<lbrace>Nonce Na, Crypt (crdK (Card A)) (Nonce Na)\<rbrace>
              # evs4 \<in> sr"

(*The card can be exploited by the spy*)
(*because of the assumptions on the card, A is certainly not server nor spy*)
  | SR4Fake: "\<lbrakk> evs4F\<in> sr; Nonce Na \<notin> used evs4F; 
                illegalUse(Card A);
                Inputs Spy (Card A) (Agent A) \<in> set evs4F \<rbrakk> 
      \<Longrightarrow> Outpts (Card A) Spy \<lbrace>Nonce Na, Crypt (crdK (Card A)) (Nonce Na)\<rbrace>
            # evs4F \<in> sr"




(*A TOWARDS B*)
  | SR5:  "\<lbrakk> evs5\<in> sr; 
             Outpts (Card A) A \<lbrace>Nonce Na, Certificate\<rbrace> \<in> set evs5;
             \<forall> p q. Certificate \<noteq> \<lbrace>p, q\<rbrace> \<rbrakk>
          \<Longrightarrow> Says A B \<lbrace>Agent A, Nonce Na\<rbrace> # evs5 \<in> sr"
(*A must check that the verifier is not a compound message, 
  otherwise this would also fire after SR7 *)




(*B AND HIS CARD*)
  | SR6:  "\<lbrakk> evs6\<in> sr; legalUse(Card B);
             Gets B \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs6 \<rbrakk>
          \<Longrightarrow> Inputs B (Card B) \<lbrace>Agent A, Nonce Na\<rbrace> 
                # evs6 \<in> sr"

(*B gets back from the card the session key and various verifiers*)
  | SR7:  "\<lbrakk> evs7\<in> sr; 
             Nonce Nb \<notin> used evs7; legalUse(Card B); B \<noteq> Server;
             K = sesK(Nb,pairK(A,B));
             Key K \<notin> used evs7;
             Inputs B (Card B) \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs7\<rbrakk>
    \<Longrightarrow> Outpts (Card B) B \<lbrace>Nonce Nb, Key K,
                            Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                            Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> 
                # evs7 \<in> sr"

 (*The card can be exploited by the spy*)
(*because of the assumptions on the card, A is certainly not server nor spy*)
  | SR7Fake:  "\<lbrakk> evs7F\<in> sr; Nonce Nb \<notin> used evs7F; 
                 illegalUse(Card B);
                 K = sesK(Nb,pairK(A,B));
                 Key K \<notin> used evs7F;
                 Inputs Spy (Card B) \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs7F \<rbrakk>
          \<Longrightarrow> Outpts (Card B) Spy \<lbrace>Nonce Nb, Key K,
                            Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                            Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> 
                # evs7F \<in> sr"




(*B TOWARDS A*)
(*having sent an input that mentions A is the only memory B relies on,
  since the output doesn't mention A - lack of explicitness*) 
  | SR8:  "\<lbrakk> evs8\<in> sr;  
             Inputs B (Card B) \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs8;
             Outpts (Card B) B \<lbrace>Nonce Nb, Key K, 
                                 Cert1, Cert2\<rbrace> \<in> set evs8 \<rbrakk>
          \<Longrightarrow> Says B A \<lbrace>Nonce Nb, Cert1\<rbrace> # evs8 \<in> sr"
  



(*A AND HER CARD*)
(*A cannot check the form of the verifiers - although I can prove the form of
  Cert2 - and just feeds her card with what she's got*)
  | SR9:  "\<lbrakk> evs9\<in> sr; legalUse(Card A);
             Gets A \<lbrace>Nonce Pk, Cert1\<rbrace> \<in> set evs9;
             Outpts (Card A) A \<lbrace>Nonce Na, Cert2\<rbrace> \<in> set evs9; 
             Gets A \<lbrace>Nonce Nb, Cert3\<rbrace> \<in> set evs9;
             \<forall> p q. Cert2 \<noteq> \<lbrace>p, q\<rbrace> \<rbrakk>
          \<Longrightarrow> Inputs A (Card A) 
                 \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce Pk,
                  Cert1, Cert3, Cert2\<rbrace> 
                # evs9 \<in> sr"

(*But the card will only give outputs to the inputs of the correct form*)
  | SR10: "\<lbrakk> evs10\<in> sr; legalUse(Card A); A \<noteq> Server;
             K = sesK(Nb,pairK(A,B));
             Inputs A (Card A) \<lbrace>Agent B, Nonce Na, Nonce Nb, 
                                 Nonce (Pairkey(A,B)),
                                 Crypt (shrK A) \<lbrace>Nonce (Pairkey(A,B)), 
                                                   Agent B\<rbrace>,
                                 Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                                 Crypt (crdK (Card A)) (Nonce Na)\<rbrace>
               \<in> set evs10 \<rbrakk>
          \<Longrightarrow> Outpts (Card A) A \<lbrace>Key K, Crypt (pairK(A,B)) (Nonce Nb)\<rbrace>
                 # evs10 \<in> sr"

(*The card can be exploited by the spy*)
(*because of the assumptions on the card, A is certainly not server nor spy*)
  | SR10Fake: "\<lbrakk> evs10F\<in> sr; 
                 illegalUse(Card A);
                 K = sesK(Nb,pairK(A,B));
                 Inputs Spy (Card A) \<lbrace>Agent B, Nonce Na, Nonce Nb, 
                                       Nonce (Pairkey(A,B)),
                                       Crypt (shrK A) \<lbrace>Nonce (Pairkey(A,B)), 
                                                        Agent B\<rbrace>,
                                       Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                                       Crypt (crdK (Card A)) (Nonce Na)\<rbrace>
                   \<in> set evs10F \<rbrakk>
          \<Longrightarrow> Outpts (Card A) Spy \<lbrace>Key K, Crypt (pairK(A,B)) (Nonce Nb)\<rbrace>
                 # evs10F \<in> sr"




(*A TOWARDS B*)
(*having initiated with B is the only memory A relies on,
  since the output doesn't mention B - lack of explicitness*) 
  | SR11: "\<lbrakk> evs11\<in> sr;
             Says A Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs11;
             Outpts (Card A) A \<lbrace>Key K, Certificate\<rbrace> \<in> set evs11 \<rbrakk>
          \<Longrightarrow> Says A B (Certificate) 
                 # evs11 \<in> sr"



    (*Both peers may leak by accident the session keys obtained from their
      cards*)
  | Oops1:
     "\<lbrakk> evsO1 \<in> sr;
         Outpts (Card B) B \<lbrace>Nonce Nb, Key K, Certificate, 
                             Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evsO1 \<rbrakk>
     \<Longrightarrow> Notes Spy \<lbrace>Key K, Nonce Nb, Agent A, Agent B\<rbrace> # evsO1 \<in> sr"

  | Oops2:
     "\<lbrakk> evsO2 \<in> sr;
         Outpts (Card A) A \<lbrace>Key K, Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> 
           \<in> set evsO2 \<rbrakk>
    \<Longrightarrow> Notes Spy \<lbrace>Key K, Nonce Nb, Agent A, Agent B\<rbrace> # evsO2 \<in> sr"






(*To solve Fake case when it doesn't involve analz - used to be condensed
  into Fake_parts_insert_tac*)
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]
(*declare parts_insertI [intro]*)



(*General facts about message reception*)
lemma Gets_imp_Says: 
       "\<lbrakk> Gets B X \<in> set evs; evs \<in> sr \<rbrakk> \<Longrightarrow> \<exists> A. Says A B X \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Gets_imp_knows_Spy: 
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> sr \<rbrakk>  \<Longrightarrow> X \<in> knows Spy evs"
apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
done

lemma Gets_imp_knows_Spy_parts_Snd: 
     "\<lbrakk> Gets B \<lbrace>X, Y\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  \<Longrightarrow> Y \<in> parts (knows Spy evs)"
apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy parts.Inj parts.Snd)
done

lemma Gets_imp_knows_Spy_analz_Snd: 
     "\<lbrakk> Gets B \<lbrace>X, Y\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  \<Longrightarrow> Y \<in> analz (knows Spy evs)"
apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy analz.Inj analz.Snd)
done

(*end general facts*)



(*Begin lemmas on secure means, from Event.thy, proved for shouprubin. They help
  the simplifier, especially in analz_image_freshK*)


lemma Inputs_imp_knows_Spy_secureM_sr: 
      "\<lbrakk> Inputs Spy C X \<in> set evs; evs \<in> sr \<rbrakk> \<Longrightarrow> X \<in> knows Spy evs"
apply (simp (no_asm_simp) add: Inputs_imp_knows_Spy_secureM)
done

lemma knows_Spy_Inputs_secureM_sr_Spy: 
      "evs \<in>sr \<Longrightarrow> knows Spy (Inputs Spy C X # evs) = insert X (knows Spy evs)"
apply (simp (no_asm_simp))
done

lemma knows_Spy_Inputs_secureM_sr: 
    "\<lbrakk> A \<noteq> Spy; evs \<in>sr \<rbrakk> \<Longrightarrow> knows Spy (Inputs A C X # evs) =  knows Spy evs"
apply (simp (no_asm_simp))
done

lemma knows_Spy_Outpts_secureM_sr_Spy: 
      "evs \<in>sr \<Longrightarrow> knows Spy (Outpts C Spy X # evs) = insert X (knows Spy evs)"
apply (simp (no_asm_simp))
done

lemma knows_Spy_Outpts_secureM_sr: 
     "\<lbrakk> A \<noteq> Spy; evs \<in>sr \<rbrakk> \<Longrightarrow> knows Spy (Outpts C A X # evs) =  knows Spy evs"
apply (simp (no_asm_simp))
done

(*End lemmas on secure means for shouprubin*)




(*BEGIN technical lemmas - evolution of forwarding lemmas*)

(*If an honest agent uses a smart card, then the card is his/her own, is
  not stolen, and the agent has received suitable data to feed the card. 
  In other words, these are guarantees that an honest agent can only use 
  his/her own card, and must use it correctly.
  On the contrary, the spy can "Inputs" any cloned cards also by the Fake rule.

  Instead of Auto_tac, proofs here used to asm-simplify and then force-tac.
*)
lemma Inputs_A_Card_3: 
    "\<lbrakk> Inputs A C (Agent A) \<in> set evs; A \<noteq> Spy; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> legalUse(C) \<and> C = (Card A) \<and>  
      (\<exists> Pk Certificate. Gets A \<lbrace>Pk, Certificate\<rbrace> \<in> set evs)"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Inputs_B_Card_6: 
     "\<lbrakk> Inputs B C \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs; B \<noteq> Spy; evs \<in> sr \<rbrakk>  
      \<Longrightarrow> legalUse(C) \<and> C = (Card B) \<and> Gets B \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Inputs_A_Card_9: 
     "\<lbrakk> Inputs A C \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce Pk,   
                                           Cert1, Cert2, Cert3\<rbrace> \<in> set evs; 
         A \<noteq> Spy; evs \<in> sr \<rbrakk>  
  \<Longrightarrow> legalUse(C) \<and> C = (Card A) \<and>  
      Gets A \<lbrace>Nonce Pk, Cert1\<rbrace> \<in> set evs     \<and>  
      Outpts (Card A) A \<lbrace>Nonce Na, Cert3\<rbrace> \<in> set evs        \<and>   
      Gets A \<lbrace>Nonce Nb, Cert2\<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply auto
done


(*The two occurrences of A in the Outpts event don't match SR4Fake, where
  A cannot be the Spy. Hence the card is legally usable by rule SR4*)
lemma Outpts_A_Card_4: 
     "\<lbrakk> Outpts C A \<lbrace>Nonce Na, (Crypt (crdK (Card A)) (Nonce Na))\<rbrace> \<in> set evs;  
         evs \<in> sr \<rbrakk>  
     \<Longrightarrow> legalUse(C) \<and> C = (Card A) \<and>  
         Inputs A (Card A) (Agent A) \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply auto
done


(*First certificate is made explicit so that a comment similar to the previous
  applies. This also provides Na to the Inputs event in the conclusion*)
lemma Outpts_B_Card_7: 
      "\<lbrakk> Outpts C B \<lbrace>Nonce Nb, Key K,  
                      Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>,  
                      Cert2\<rbrace> \<in> set evs;  
         evs \<in> sr \<rbrakk>  
     \<Longrightarrow> legalUse(C) \<and> C = (Card B) \<and>  
         Inputs B (Card B) \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Outpts_A_Card_10: 
     "\<lbrakk> Outpts C A \<lbrace>Key K, (Crypt (pairK(A,B)) (Nonce Nb))\<rbrace> \<in> set evs; 
         evs \<in> sr \<rbrakk>  
     \<Longrightarrow> legalUse(C) \<and> C = (Card A) \<and>  
         (\<exists> Na Ver1 Ver2 Ver3.  
       Inputs A (Card A) \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce (Pairkey(A,B)),  
                              Ver1, Ver2, Ver3\<rbrace> \<in> set evs)"
apply (erule rev_mp, erule sr.induct)
apply auto
done



(*
A can't check the form of the certificate, and so cannot associate the sesion 
key to the other peer! This already shows that the protocol fails to satisfy 
the principle of goal availability for the goal of key association.
Similar reasoning below for the goal of confidentiality will be even more
accessible.
*)
lemma Outpts_A_Card_10_imp_Inputs: 
     "\<lbrakk> Outpts (Card A) A \<lbrace>Key K, Certificate\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> (\<exists> B Na Nb Ver1 Ver2 Ver3.  
       Inputs A (Card A) \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce (Pairkey(A,B)),  
                              Ver1, Ver2, Ver3\<rbrace> \<in> set evs)"
apply (erule rev_mp, erule sr.induct)
apply simp_all
apply blast+
done




(*Weaker version: if the agent can't check the forms of the verifiers, then
  the agent must not be the spy so as to solve SR4Fake. The verifier must be
  recognised as some cyphertex in order to distinguish from case SR7, 
  concerning B's output, which also begins with a nonce.
*)
lemma Outpts_honest_A_Card_4: 
     "\<lbrakk> Outpts C A \<lbrace>Nonce Na, Crypt K X\<rbrace> \<in>set evs; 
         A \<noteq> Spy;  evs \<in> sr \<rbrakk>  
     \<Longrightarrow> legalUse(C) \<and> C = (Card A) \<and>  
         Inputs A (Card A) (Agent A) \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply auto
done

(*alternative formulation of same theorem
Goal "\<lbrakk> Outpts C A \<lbrace>Nonce Na, Certificate\<rbrace> \<in> set evs;  
         \<forall> p q. Certificate \<noteq> \<lbrace>p, q\<rbrace>;    
         A \<noteq> Spy; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> legalUse(C) \<and> C = (Card A) \<and>  
         Inputs A (Card A) (Agent A) \<in> set evs"
same proof
*)


lemma Outpts_honest_B_Card_7: 
     "\<lbrakk> Outpts C B \<lbrace>Nonce Nb, Key K, Cert1, Cert2\<rbrace> \<in> set evs;  
         B \<noteq> Spy; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> legalUse(C) \<and> C = (Card B) \<and>  
         (\<exists> A Na. Inputs B (Card B) \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs)"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Outpts_honest_A_Card_10: 
     "\<lbrakk> Outpts C A \<lbrace>Key K, Certificate\<rbrace> \<in> set evs;  
         A \<noteq> Spy; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> legalUse (C) \<and> C = (Card A) \<and>  
         (\<exists> B Na Nb Pk Ver1 Ver2 Ver3.  
          Inputs A (Card A) \<lbrace>Agent B, Nonce Na, Nonce Nb, Pk,  
                              Ver1, Ver2, Ver3\<rbrace> \<in> set evs)"
apply (erule rev_mp, erule sr.induct)
apply simp_all
apply blast+
done
(*-END-*)


(*Even weaker versions: if the agent can't check the forms of the verifiers
  and the agent may be the spy, then we must know what card the agent
  is getting the output from. 
*)
lemma Outpts_which_Card_4: 
    "\<lbrakk> Outpts (Card A) A \<lbrace>Nonce Na, Crypt K X\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  
    \<Longrightarrow> Inputs A (Card A) (Agent A) \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply (simp_all (no_asm_simp))
apply clarify
done

lemma Outpts_which_Card_7: 
  "\<lbrakk> Outpts (Card B) B \<lbrace>Nonce Nb, Key K, Cert1, Cert2\<rbrace> \<in> set evs;  
         evs \<in> sr \<rbrakk>  
     \<Longrightarrow> \<exists> A Na. Inputs B (Card B) \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Outpts_which_Card_10: 
     "\<lbrakk> Outpts (Card A) A \<lbrace>Key (sesK(Nb,pairK(A,B))),  
                             Crypt (pairK(A,B)) (Nonce Nb) \<rbrace> \<in> set evs;  
         evs \<in> sr \<rbrakk>  
    \<Longrightarrow> \<exists> Na. Inputs A (Card A) \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce (Pairkey(A,B)), 
                            Crypt (shrK A) \<lbrace>Nonce (Pairkey(A,B)), Agent B\<rbrace>,  
                            Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>,  
                            Crypt (crdK (Card A)) (Nonce Na) \<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply auto
done


(*Lemmas on the form of outputs*)


(*A needs to check that the verifier is a cipher for it to come from SR4
  otherwise it could come from SR7 *)
lemma Outpts_A_Card_form_4: 
  "\<lbrakk> Outpts (Card A) A \<lbrace>Nonce Na, Certificate\<rbrace> \<in> set evs;  
         \<forall> p q. Certificate \<noteq> \<lbrace>p, q\<rbrace>; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> Certificate = (Crypt (crdK (Card A)) (Nonce Na))"
apply (erule rev_mp, erule sr.induct)
apply (simp_all (no_asm_simp))
done

lemma Outpts_B_Card_form_7: 
   "\<lbrakk> Outpts (Card B) B \<lbrace>Nonce Nb, Key K, Cert1, Cert2\<rbrace> \<in> set evs; 
         evs \<in> sr \<rbrakk>          
      \<Longrightarrow> \<exists> A Na.    
          K = sesK(Nb,pairK(A,B)) \<and>                       
          Cert1 = (Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>) \<and>  
          Cert2 = (Crypt (pairK(A,B)) (Nonce Nb))"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Outpts_A_Card_form_10: 
   "\<lbrakk> Outpts (Card A) A \<lbrace>Key K, Certificate\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  
      \<Longrightarrow> \<exists> B Nb.  
          K = sesK(Nb,pairK(A,B)) \<and>  
          Certificate = (Crypt (pairK(A,B)) (Nonce Nb))"
apply (erule rev_mp, erule sr.induct)
apply (simp_all (no_asm_simp))
done

lemma Outpts_A_Card_form_bis: 
  "\<lbrakk> Outpts (Card A') A' \<lbrace>Key (sesK(Nb,pairK(A,B))), Certificate\<rbrace> \<in> set evs; 
         evs \<in> sr \<rbrakk>  
      \<Longrightarrow> A' = A \<and>  
          Certificate = (Crypt (pairK(A,B)) (Nonce Nb))"
apply (erule rev_mp, erule sr.induct)
apply (simp_all (no_asm_simp))
done

(*\<dots> and Inputs *)

lemma Inputs_A_Card_form_9: 
     "\<lbrakk> Inputs A (Card A) \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce Pk,   
                             Cert1, Cert2, Cert3\<rbrace> \<in> set evs; 
         evs \<in> sr \<rbrakk>  
  \<Longrightarrow>    Cert3 = Crypt (crdK (Card A)) (Nonce Na)"
apply (erule rev_mp)
apply (erule sr.induct)
apply (simp_all (no_asm_simp))
(*Fake*)
apply force
(*SR9*)
apply (blast dest!: Outpts_A_Card_form_4)
done
(* Pk, Cert1, Cert2 cannot be made explicit because they traversed the network in the clear *)

(*General guarantees on Inputs and Outpts*)

(*for any agents*)


lemma Inputs_Card_legalUse: 
  "\<lbrakk> Inputs A (Card A) X \<in> set evs; evs \<in> sr \<rbrakk> \<Longrightarrow> legalUse(Card A)"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Outpts_Card_legalUse: 
  "\<lbrakk> Outpts (Card A) A X \<in> set evs; evs \<in> sr \<rbrakk> \<Longrightarrow> legalUse(Card A)"
apply (erule rev_mp, erule sr.induct)
apply auto
done

(*for honest agents*)

lemma Inputs_Card: "\<lbrakk> Inputs A C X \<in> set evs; A \<noteq> Spy; evs \<in> sr \<rbrakk>  
      \<Longrightarrow> C = (Card A) \<and> legalUse(C)"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Outpts_Card: "\<lbrakk> Outpts C A X \<in> set evs; A \<noteq> Spy; evs \<in> sr \<rbrakk>  
      \<Longrightarrow> C = (Card A) \<and> legalUse(C)"
apply (erule rev_mp, erule sr.induct)
apply auto
done

lemma Inputs_Outpts_Card: 
     "\<lbrakk> Inputs A C X \<in> set evs \<or> Outpts C A Y \<in> set evs;  
         A \<noteq> Spy; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> C = (Card A) \<and> legalUse(Card A)"
apply (blast dest: Inputs_Card Outpts_Card)
done


(*for the spy - they stress that the model behaves as it is meant to*) 

(*The or version can be also proved directly.
  It stresses that the spy may use either her own legally usable card or
  all the illegally usable cards.
*)
lemma Inputs_Card_Spy: 
  "\<lbrakk> Inputs Spy C X \<in> set evs \<or> Outpts C Spy X \<in> set evs; evs \<in> sr \<rbrakk>  
      \<Longrightarrow> C = (Card Spy) \<and> legalUse(Card Spy) \<or>  
          (\<exists> A. C = (Card A) \<and> illegalUse(Card A))"
apply (erule rev_mp, erule sr.induct)
apply auto
done


(*END technical lemmas*)






(*BEGIN unicity theorems: certain items uniquely identify a smart card's
                          output*)

(*A's card's first output: the nonce uniquely identifies the rest*)
lemma Outpts_A_Card_unique_nonce:
     "\<lbrakk> Outpts (Card A) A \<lbrace>Nonce Na, Crypt (crdK (Card A)) (Nonce Na)\<rbrace>  
           \<in> set evs;   
         Outpts (Card A') A' \<lbrace>Nonce Na, Crypt (crdK (Card A')) (Nonce Na)\<rbrace> 
           \<in> set evs;   
         evs \<in> sr \<rbrakk> \<Longrightarrow> A=A'"
apply (erule rev_mp, erule rev_mp, erule sr.induct, simp_all)
apply (fastforce dest: Outpts_parts_used)
apply blast
done

(*B's card's output: the NONCE uniquely identifies the rest*)
lemma Outpts_B_Card_unique_nonce: 
     "\<lbrakk> Outpts (Card B) B \<lbrace>Nonce Nb, Key SK, Cert1, Cert2\<rbrace> \<in> set evs;   
         Outpts (Card B') B' \<lbrace>Nonce Nb, Key SK', Cert1', Cert2'\<rbrace> \<in> set evs;   
         evs \<in> sr \<rbrakk> \<Longrightarrow> B=B' \<and> SK=SK' \<and> Cert1=Cert1' \<and> Cert2=Cert2'"
apply (erule rev_mp, erule rev_mp, erule sr.induct, simp_all)
apply (fastforce dest: Outpts_parts_used)
apply blast
done


(*B's card's output: the SESKEY uniquely identifies the rest*)
lemma Outpts_B_Card_unique_key: 
     "\<lbrakk> Outpts (Card B) B \<lbrace>Nonce Nb, Key SK, Cert1, Cert2\<rbrace> \<in> set evs;   
         Outpts (Card B') B' \<lbrace>Nonce Nb', Key SK, Cert1', Cert2'\<rbrace> \<in> set evs;   
         evs \<in> sr \<rbrakk> \<Longrightarrow> B=B' \<and> Nb=Nb' \<and> Cert1=Cert1' \<and> Cert2=Cert2'"
apply (erule rev_mp, erule rev_mp, erule sr.induct, simp_all)
apply (fastforce dest: Outpts_parts_used)
apply blast
done

lemma Outpts_A_Card_unique_key: "\<lbrakk> Outpts (Card A) A \<lbrace>Key K, V\<rbrace> \<in> set evs;   
         Outpts (Card A') A' \<lbrace>Key K, V'\<rbrace> \<in> set evs;   
         evs \<in> sr \<rbrakk> \<Longrightarrow> A=A' \<and> V=V'"
apply (erule rev_mp, erule rev_mp, erule sr.induct, simp_all)
apply (blast dest: Outpts_A_Card_form_bis)
apply blast
done


(*Revised unicity theorems - applies to both steps 4 and 7*)
lemma Outpts_A_Card_Unique: 
  "\<lbrakk> Outpts (Card A) A \<lbrace>Nonce Na, rest\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> Unique (Outpts (Card A) A \<lbrace>Nonce Na, rest\<rbrace>) on evs"
apply (erule rev_mp, erule sr.induct, simp_all add: Unique_def)
apply (fastforce dest: Outpts_parts_used)
apply blast
apply (fastforce dest: Outpts_parts_used)
apply blast
done

(*can't prove the same on evs10 for it doesn't have a freshness assumption!*)


(*END unicity theorems*)


(*BEGIN counterguarantees about spy's knowledge*)

(*on nonces*)

lemma Spy_knows_Na: 
      "\<lbrakk> Says A B \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  
      \<Longrightarrow> Nonce Na \<in> analz (knows Spy evs)"
apply (blast dest!: Says_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd])
done

lemma Spy_knows_Nb: 
      "\<lbrakk> Says B A \<lbrace>Nonce Nb, Certificate\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  
      \<Longrightarrow> Nonce Nb \<in> analz (knows Spy evs)"
apply (blast dest!: Says_imp_knows_Spy [THEN analz.Inj, THEN analz.Fst])
done


(*on Pairkey*)

lemma Pairkey_Gets_analz_knows_Spy: 
      "\<lbrakk> Gets A \<lbrace>Nonce (Pairkey(A,B)), Certificate\<rbrace> \<in> set evs; evs \<in> sr \<rbrakk>  
      \<Longrightarrow> Nonce (Pairkey(A,B)) \<in> analz (knows Spy evs)"
apply (blast dest!: Gets_imp_knows_Spy [THEN analz.Inj])
done

lemma Pairkey_Inputs_imp_Gets: 
     "\<lbrakk> Inputs A (Card A)             
           \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce (Pairkey(A,B)),     
             Cert1, Cert3, Cert2\<rbrace> \<in> set evs;           
         A \<noteq> Spy; evs \<in> sr \<rbrakk>     
      \<Longrightarrow> Gets A \<lbrace>Nonce (Pairkey(A,B)), Cert1\<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply (simp_all (no_asm_simp))
apply force
done

lemma Pairkey_Inputs_analz_knows_Spy: 
     "\<lbrakk> Inputs A (Card A)             
           \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce (Pairkey(A,B)),     
             Cert1, Cert3, Cert2\<rbrace> \<in> set evs;           
         evs \<in> sr \<rbrakk>     
     \<Longrightarrow> Nonce (Pairkey(A,B)) \<in> analz (knows Spy evs)"
apply (case_tac "A = Spy")
apply (fastforce dest!: Inputs_imp_knows_Spy_secureM [THEN analz.Inj])
apply (blast dest!: Pairkey_Inputs_imp_Gets [THEN Pairkey_Gets_analz_knows_Spy])
done

(* This fails on base case because of XOR properties.
lemma Pairkey_authentic:
  "\<lbrakk> Nonce (Pairkey(A,B)) \<in> parts (knows Spy evs);
     Card A \<notin> cloned; evs \<in> sr \<rbrakk>
 \<Longrightarrow> \<exists> cert. Says Server A \<lbrace>Nonce (Pairkey(A,B)), Cert\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule sr.induct, simp_all)
apply clarify
oops

 1. \<And>x a b.
       \<lbrakk>Card A \<notin> cloned; Pairkey (A, B) = Pairkey (a, b); Card a \<in> cloned;
        Card b \<in> cloned\<rbrakk>
       \<Longrightarrow> False
*)

(*END counterguarantees on spy's knowledge*)


(*BEGIN rewrite rules for parts operator*)


declare shrK_disj_sesK [THEN not_sym, iff] 
declare pin_disj_sesK [THEN not_sym, iff]
declare crdK_disj_sesK [THEN not_sym, iff]
declare pairK_disj_sesK [THEN not_sym, iff]


ML
{*
structure ShoupRubin =
struct

val prepare_tac = 
 (*SR8*)   forward_tac [@{thm Outpts_B_Card_form_7}] 14 THEN
           eresolve_tac [exE] 15 THEN eresolve_tac [exE] 15 THEN 
 (*SR9*)   forward_tac [@{thm Outpts_A_Card_form_4}] 16 THEN 
 (*SR11*)  forward_tac [@{thm Outpts_A_Card_form_10}] 21 THEN
           eresolve_tac [exE] 22 THEN eresolve_tac [exE] 22

fun parts_prepare_tac ctxt = 
           prepare_tac THEN
 (*SR9*)   dresolve_tac [@{thm Gets_imp_knows_Spy_parts_Snd}] 18 THEN 
 (*SR9*)   dresolve_tac [@{thm Gets_imp_knows_Spy_parts_Snd}] 19 THEN 
 (*Oops1*) dresolve_tac [@{thm Outpts_B_Card_form_7}] 25    THEN               
 (*Oops2*) dresolve_tac [@{thm Outpts_A_Card_form_10}] 27 THEN                
 (*Base*)  (force_tac ctxt) 1

val analz_prepare_tac = 
         prepare_tac THEN
         dtac @{thm Gets_imp_knows_Spy_analz_Snd} 18 THEN 
 (*SR9*) dtac @{thm Gets_imp_knows_Spy_analz_Snd} 19 THEN 
         REPEAT_FIRST (eresolve_tac [asm_rl, conjE] ORELSE' hyp_subst_tac)

end
*}

method_setup prepare = {*
    Scan.succeed (K (SIMPLE_METHOD ShoupRubin.prepare_tac)) *}
  "to launch a few simple facts that will help the simplifier"

method_setup parts_prepare = {*
    Scan.succeed (fn ctxt => SIMPLE_METHOD (ShoupRubin.parts_prepare_tac ctxt)) *}
  "additional facts to reason about parts"

method_setup analz_prepare = {*
    Scan.succeed (K (SIMPLE_METHOD ShoupRubin.analz_prepare_tac)) *}
  "additional facts to reason about analz"


(*Treatment of pins is here for completeness. This protocol doesn't use pins*)
lemma Spy_parts_keys [simp]: "evs \<in> sr \<Longrightarrow>  
  (Key (shrK P) \<in> parts (knows Spy evs)) = (Card P \<in> cloned) \<and>  
  (Key (pin P) \<in> parts (knows Spy evs)) = (P \<in> bad \<or> Card P \<in> cloned) \<and>  
  (Key (crdK C) \<in> parts (knows Spy evs)) = (C \<in> cloned) \<and>  
  (Key (pairK(A,B)) \<in> parts (knows Spy evs)) = (Card B \<in> cloned)"
apply (erule sr.induct)
apply parts_prepare
apply simp_all
apply (blast intro: parts_insertI)
done


(*END rewrite rules for parts operator*)

(*BEGIN rewrite rules for analz operator*)

lemma Spy_analz_shrK[simp]: "evs \<in> sr \<Longrightarrow>  
  (Key (shrK P) \<in> analz (knows Spy evs)) = (Card P \<in> cloned)" 
apply (auto dest!: Spy_knows_cloned)
done

lemma Spy_analz_crdK[simp]: "evs \<in> sr \<Longrightarrow>  
  (Key (crdK C) \<in> analz (knows Spy evs)) = (C \<in> cloned)"
apply (auto dest!: Spy_knows_cloned)
done

lemma Spy_analz_pairK[simp]: "evs \<in> sr \<Longrightarrow>  
  (Key (pairK(A,B)) \<in> analz (knows Spy evs)) = (Card B \<in> cloned)"
apply (auto dest!: Spy_knows_cloned)
done



(*Because initState contains a set of nonces, this is needed for base case of
  analz_image_freshK*)
lemma analz_image_Key_Un_Nonce: "analz (Key`K \<union> Nonce`N) = Key`K \<union> Nonce`N"
apply auto
done

method_setup sc_analz_freshK = {*
    Scan.succeed (fn ctxt =>
     (SIMPLE_METHOD
      (EVERY [REPEAT_FIRST
       (resolve_tac [allI, ballI, impI]),
        REPEAT_FIRST (rtac @{thm analz_image_freshK_lemma}),
        ALLGOALS (asm_simp_tac (Simplifier.context ctxt Smartcard.analz_image_freshK_ss
          addsimps [@{thm knows_Spy_Inputs_secureM_sr_Spy},
                    @{thm knows_Spy_Outpts_secureM_sr_Spy},
                    @{thm shouprubin_assumes_securemeans}, 
                    @{thm analz_image_Key_Un_Nonce}]))]))) *}
    "for proving the Session Key Compromise theorem for smartcard protocols"


lemma analz_image_freshK [rule_format]: 
     "evs \<in> sr \<Longrightarrow>      \<forall> K KK.  
          (Key K \<in> analz (Key`KK \<union> (knows Spy evs))) =  
          (K \<in> KK \<or> Key K \<in> analz (knows Spy evs))"
apply (erule sr.induct)
apply analz_prepare
apply sc_analz_freshK
apply spy_analz
done


lemma analz_insert_freshK: "evs \<in> sr \<Longrightarrow>   
         Key K \<in> analz (insert (Key K') (knows Spy evs)) =  
         (K = K' \<or> Key K \<in> analz (knows Spy evs))"
apply (simp only: analz_image_freshK_simps analz_image_freshK)
done

(*END rewrite rules for analz operator*)

(*BEGIN authenticity theorems*)




(*Card B \<notin> cloned needed for Fake
  B \<notin> bad needed for SR7Fake; equivalent to Card B \<notin> stolen
*)

lemma Na_Nb_certificate_authentic: 
     "\<lbrakk> Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace> \<in> parts (knows Spy evs);  
         \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>           
     \<Longrightarrow> Outpts (Card B) B \<lbrace>Nonce Nb, Key (sesK(Nb,pairK(A,B))),   
                Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply parts_prepare
apply simp_all
(*Fake*)
apply spy_analz
(*SR7F*)
apply clarify
done

(* Card B \<notin> cloned needed for Fake and SR7F
   B \<noteq> Spy needed for SR7
   B \<notin> bad - or Card B \<notin> stolen - needed for SR7F
   Card A \<notin> cloned needed for SR10F
   A \<notin> bad - or Card A \<notin> stolen - needed for SR10F

   Non-trivial case done by the simplifier.*)
lemma Nb_certificate_authentic: 
      "\<lbrakk> Crypt (pairK(A,B)) (Nonce Nb) \<in> parts (knows Spy evs);  
         B \<noteq> Spy; \<not>illegalUse(Card A); \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>    
     \<Longrightarrow> Outpts (Card A) A \<lbrace>Key (sesK(Nb,pairK(A,B))),  
                             Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply parts_prepare
apply (case_tac [17] "Aa = Spy")
apply simp_all
(*Fake*)
apply spy_analz
(*SR7F, SR10F*)
apply clarify+
done



(*Discovering the very origin of the Nb certificate... non needed!*)
(*lemma*)
lemma Outpts_A_Card_imp_pairK_parts: 
     "\<lbrakk> Outpts (Card A) A            
         \<lbrace>Key K, Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs;  
         evs \<in> sr \<rbrakk>   
     \<Longrightarrow> \<exists> Na. Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace> \<in> parts (knows Spy evs)"
apply (erule rev_mp, erule sr.induct)
apply parts_prepare
apply simp_all
(*Fake*)
apply (blast dest: parts_insertI)
(*SR7*)
apply force
(*SR7F*)
apply force
(*SR8*)
apply blast
(*SR10*)
apply (blast dest: Inputs_imp_knows_Spy_secureM_sr parts.Inj Inputs_A_Card_9 Gets_imp_knows_Spy elim: knows_Spy_partsEs)
(*SR10F*)
apply (blast dest: Inputs_imp_knows_Spy_secureM_sr [THEN parts.Inj] 
                   Inputs_A_Card_9 Gets_imp_knows_Spy 
             elim: knows_Spy_partsEs)
done



lemma Nb_certificate_authentic_bis: 
     "\<lbrakk> Crypt (pairK(A,B)) (Nonce Nb) \<in> parts (knows Spy evs);  
         B \<noteq> Spy; \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>    
     \<Longrightarrow> \<exists> Na. Outpts (Card B) B \<lbrace>Nonce Nb, Key (sesK(Nb,pairK(A,B))),   
                   Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                   Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply parts_prepare
apply (simp_all (no_asm_simp))
(*Fake*)
apply spy_analz
(*SR7*)
apply blast
(*SR7F*)
apply blast
(*SR10*)
apply (blast dest: Na_Nb_certificate_authentic Inputs_imp_knows_Spy_secureM_sr [THEN parts.Inj] elim: knows_Spy_partsEs)
(*SR10F*)
apply (blast dest: Na_Nb_certificate_authentic Inputs_imp_knows_Spy_secureM_sr [THEN parts.Inj] elim: knows_Spy_partsEs)
(*SR11*)
apply (blast dest: Na_Nb_certificate_authentic Outpts_A_Card_imp_pairK_parts)
done


lemma Pairkey_certificate_authentic: 
    "\<lbrakk> Crypt (shrK A) \<lbrace>Nonce Pk, Agent B\<rbrace> \<in> parts (knows Spy evs);    
         Card A \<notin> cloned; evs \<in> sr \<rbrakk>        
     \<Longrightarrow> Pk = Pairkey(A,B) \<and>              
         Says Server A \<lbrace>Nonce Pk,  
                        Crypt (shrK A) \<lbrace>Nonce Pk, Agent B\<rbrace>\<rbrace> 
           \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply parts_prepare
apply (simp_all (no_asm_simp))
(*Fake*)
apply spy_analz
done


(*Alternatively:  A \<notin> bad; Card A \<notin> cloned; B \<notin> bad; Card B \<notin> cloned;*)
lemma sesK_authentic: 
     "\<lbrakk> Key (sesK(Nb,pairK(A,B))) \<in> parts (knows Spy evs);  
         A \<noteq> Spy; B \<noteq> Spy; \<not>illegalUse(Card A); \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>           
      \<Longrightarrow> Notes Spy \<lbrace>Key (sesK(Nb,pairK(A,B))), Nonce Nb, Agent A, Agent B\<rbrace>  
           \<in> set evs"
apply (erule rev_mp, erule sr.induct)
apply parts_prepare
apply (simp_all (no_asm_simp))
(*fake*)
apply spy_analz
(*forge*)
apply (fastforce dest: analz.Inj)
(*SR7: used B\<noteq>Spy*)
(*SR7F*)
apply clarify
(*SR10: used A\<noteq>Spy*)
(*SR10F*)
apply clarify
(*Oops*)
apply simp_all
done


(*END authenticity theorems*)


(*BEGIN confidentiality theorems*)

(*If B were bad and his card stolen, they spy could use B's card but would 
  not obtain this K because B's card only issues new session keys out
  of new nonces. 
  If A were bad, then her card could be stolen, hence the spy could feed it
  with Nb and get this K. Thus, A\<notin>bad can be replaced by Card A \<notin> stolen
  Hence these are the minimal assumptions:
        A \<notin> bad; B \<noteq> Spy; Card A \<notin> cloned; Card B \<notin> cloned; 
         A \<noteq> Spy; B \<noteq> Spy; \<not>illegalUse(Card A); Card B \<notin> cloned;
*)

lemma Confidentiality: 
     "\<lbrakk> Notes Spy \<lbrace>Key (sesK(Nb,pairK(A,B))), Nonce Nb, Agent A, Agent B\<rbrace>  
           \<notin> set evs; 
        A \<noteq> Spy; B \<noteq> Spy; \<not>illegalUse(Card A); \<not>illegalUse(Card B); 
        evs \<in> sr \<rbrakk>           
      \<Longrightarrow> Key (sesK(Nb,pairK(A,B))) \<notin> analz (knows Spy evs)"
apply (blast intro: sesK_authentic)
done

lemma Confidentiality_B: 
     "\<lbrakk> Outpts (Card B) B \<lbrace>Nonce Nb, Key K, Certificate,          
                             Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs;  
         Notes Spy \<lbrace>Key K, Nonce Nb, Agent A, Agent B\<rbrace> \<notin> set evs;  
         A \<noteq> Spy; B \<noteq> Spy; \<not>illegalUse(Card A); Card B \<notin> cloned; 
         evs \<in> sr \<rbrakk>  
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
apply (erule rev_mp, erule rev_mp, erule sr.induct)
apply analz_prepare
apply (simp_all add: analz_insert_eq analz_insert_freshK pushes split_ifs)
(*Fake*)
apply spy_analz
(*Forge*)
apply (rotate_tac 7)
apply (drule parts.Inj)
apply (fastforce dest: Outpts_B_Card_form_7)
(*SR7*)
apply (blast dest!: Outpts_B_Card_form_7)
(*SR7F*)
apply clarify
apply (drule Outpts_parts_used)
apply simp
(*faster than
  apply (fastforce dest: Outpts_parts_used)
*)
(*SR10*)
apply (fastforce dest: Outpts_B_Card_form_7)
(*SR10F - uses assumption Card A not cloned*)
apply clarify
apply (drule Outpts_B_Card_form_7, assumption)
apply simp
(*Oops1*)
apply (blast dest!: Outpts_B_Card_form_7)
(*Oops2*)
apply (blast dest!: Outpts_B_Card_form_7 Outpts_A_Card_form_10)
done

(*Confidentiality_A can be is faster to prove in forward style, using
the authentication theorems. So it is moved below*)


(*END confidentiality theorems*)



(*BEGIN authentication theorems*)

lemma A_authenticates_B: 
     "\<lbrakk> Outpts (Card A) A \<lbrace>Key K, Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs;  
         \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>           
     \<Longrightarrow> \<exists> Na. 
            Outpts (Card B) B \<lbrace>Nonce Nb, Key K,   
                Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs"
apply (blast dest: Na_Nb_certificate_authentic Outpts_A_Card_form_10 Outpts_A_Card_imp_pairK_parts)
done

lemma A_authenticates_B_Gets: 
     "\<lbrakk> Gets A \<lbrace>Nonce Nb, Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>\<rbrace>  
           \<in> set evs;  
         \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>           
     \<Longrightarrow> Outpts (Card B) B \<lbrace>Nonce Nb, Key (sesK(Nb, pairK (A, B))),   
                             Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                             Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs"
apply (blast dest: Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Snd, THEN Na_Nb_certificate_authentic])
done




lemma B_authenticates_A: 
     "\<lbrakk> Gets B (Crypt (pairK(A,B)) (Nonce Nb)) \<in> set evs;  
         B \<noteq> Spy; \<not>illegalUse(Card A); \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>  
      \<Longrightarrow> Outpts (Card A) A            
       \<lbrace>Key (sesK(Nb,pairK(A,B))), Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule sr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest: Says_imp_knows_Spy [THEN parts.Inj] Nb_certificate_authentic)
done


(*END authentication theorems*)

lemma Confidentiality_A: "\<lbrakk> Outpts (Card A) A            
           \<lbrace>Key K, Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs;  
         Notes Spy \<lbrace>Key K, Nonce Nb, Agent A, Agent B\<rbrace> \<notin> set evs;  
         A \<noteq> Spy; B \<noteq> Spy; \<not>illegalUse(Card A); \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>           
     \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
apply (drule A_authenticates_B)
prefer 3
apply (erule exE)
apply (drule Confidentiality_B)
apply auto
done

lemma Outpts_imp_knows_agents_secureM_sr: 
   "\<lbrakk> Outpts (Card A) A X \<in> set evs; evs \<in> sr \<rbrakk> \<Longrightarrow> X \<in> knows A evs"
apply (simp (no_asm_simp) add: Outpts_imp_knows_agents_secureM)
done


(*BEGIN key distribution theorems*)


(*Alternatively: B \<notin> bad; Card B \<notin> cloned;*)
lemma A_keydist_to_B: 
     "\<lbrakk> Outpts (Card A) A            
           \<lbrace>Key K, Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs;  
         \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>           
     \<Longrightarrow> Key K \<in> analz (knows B evs)"
apply (drule A_authenticates_B)
prefer 3
apply (erule exE)
apply (rule Outpts_imp_knows_agents_secureM_sr [THEN analz.Inj, THEN analz.Snd, THEN analz.Fst])
apply assumption+
done


(*Alternatively: A \<notin> bad; B \<notin> bad; Card A \<notin> cloned; Card B \<notin> cloned;*)
lemma B_keydist_to_A: 
     "\<lbrakk> Outpts (Card B) B \<lbrace>Nonce Nb, Key K, Certificate,          
                             (Crypt (pairK(A,B)) (Nonce Nb))\<rbrace> \<in> set evs;  
         Gets B (Crypt (pairK(A,B)) (Nonce Nb)) \<in> set evs;  
         B \<noteq> Spy; \<not>illegalUse(Card A); \<not>illegalUse(Card B); 
         evs \<in> sr \<rbrakk>  
     \<Longrightarrow> Key K \<in> analz (knows A evs)"
apply (frule B_authenticates_A)
apply (drule_tac [5] Outpts_B_Card_form_7)
apply (rule_tac [6] Outpts_imp_knows_agents_secureM_sr [THEN analz.Inj, THEN analz.Fst])
prefer 6 apply force
apply assumption+
done

(*END key distribution theorems*)








(*BEGIN further theorems about authenticity of verifiers
  (useful to agents and cards).                          *)

(*MSG11
If B receives the verifier of msg11, then the verifier originated with msg7.
Alternatively: A \<notin> bad; B \<notin> bad; Card A \<notin> cloned; Card B \<notin> cloned;
*)
lemma Nb_certificate_authentic_B: 
     "\<lbrakk> Gets B (Crypt (pairK(A,B)) (Nonce Nb)) \<in> set evs;  
        B \<noteq> Spy; \<not>illegalUse(Card B); 
        evs \<in> sr \<rbrakk>  
    \<Longrightarrow> \<exists> Na. 
            Outpts (Card B) B \<lbrace>Nonce Nb, Key (sesK(Nb,pairK(A,B))),   
                Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, 
                Crypt (pairK(A,B)) (Nonce Nb)\<rbrace> \<in> set evs"
apply (blast dest: Gets_imp_knows_Spy [THEN parts.Inj, THEN Nb_certificate_authentic_bis])
done
(*Useless to B: B can't check the form of the verifier because he doesn't know
  pairK(A,B) *)

(*MSG10
If A obtains the verifier of msg10, then the verifier originated with msg7:
A_authenticates_B. It is useful to A, who can check the form of the 
verifier by application of Outpts_A_Card_form_10.
*)

(*MSG9
The first verifier verifies the Pairkey to the card: since it's encrypted
under Ka, it must come from the server (if A's card is not cloned).
The second verifier verifies both nonces, since it's encrypted under the
pairK, it must originate with B's card  (if A and B's cards not cloned).
The third verifier verifies Na: since it's encrytped under the card's key,
it originated with the card; so the card does not need to save Na
in the first place and do a comparison now: it just verifies Na through the
verifier. Three theorems related to these three statements.

Recall that a card can check the form of the verifiers (can decrypt them),
while an agent in general cannot, if not provided with a suitable theorem.
*)

(*Card A can't reckon the pairkey - we need to guarantee its integrity!*)
lemma Pairkey_certificate_authentic_A_Card: 
     "\<lbrakk> Inputs A (Card A)   
             \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce Pk, 
               Crypt (shrK A) \<lbrace>Nonce Pk, Agent B\<rbrace>,  
               Cert2, Cert3\<rbrace> \<in> set evs; 
         A \<noteq> Spy; Card A \<notin> cloned; evs \<in> sr \<rbrakk>   
     \<Longrightarrow> Pk = Pairkey(A,B) \<and>  
         Says Server A \<lbrace>Nonce (Pairkey(A,B)),  
                  Crypt (shrK A) \<lbrace>Nonce (Pairkey(A,B)), Agent B\<rbrace>\<rbrace>   
           \<in> set evs "
apply (blast dest: Inputs_A_Card_9 Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Snd] Pairkey_certificate_authentic)
done
(*the second conjunct of the thesis might be regarded as a form of integrity 
  in the sense of Neuman-Ts'o*)

lemma Na_Nb_certificate_authentic_A_Card: 
      "\<lbrakk> Inputs A (Card A)   
             \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce Pk, 
               Cert1,  
               Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, Cert3\<rbrace> \<in> set evs; 
      A \<noteq> Spy; \<not>illegalUse(Card B); evs \<in> sr \<rbrakk> 
     \<Longrightarrow> Outpts (Card B) B \<lbrace>Nonce Nb, Key (sesK(Nb, pairK (A, B))),    
                             Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>,  
                             Crypt (pairK(A,B)) (Nonce Nb)\<rbrace>  
           \<in> set evs "
apply (blast dest: Inputs_A_Card_9 Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Snd, THEN Na_Nb_certificate_authentic])
done

lemma Na_authentic_A_Card: 
     "\<lbrakk> Inputs A (Card A)   
             \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce Pk, 
                Cert1, Cert2, Cert3\<rbrace> \<in> set evs; 
         A \<noteq> Spy; evs \<in> sr \<rbrakk>   
     \<Longrightarrow> Outpts (Card A) A \<lbrace>Nonce Na, Cert3\<rbrace>  
           \<in> set evs"
apply (blast dest: Inputs_A_Card_9)
done

(* The last three theorems for Card A can be put togheter trivially.
They are separated to highlight the different requirements on agents
and their cards.*)


(*Alternatively:
  A \<noteq> Spy; B \<notin> bad; Card A \<notin> cloned; Card B \<notin> cloned; evs \<in> sr \<rbrakk> *)
lemma Inputs_A_Card_9_authentic: 
  "\<lbrakk> Inputs A (Card A)   
             \<lbrace>Agent B, Nonce Na, Nonce Nb, Nonce Pk, 
               Crypt (shrK A) \<lbrace>Nonce Pk, Agent B\<rbrace>,  
               Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>, Cert3\<rbrace> \<in> set evs; 
    A \<noteq> Spy; Card A \<notin> cloned;\<not>illegalUse(Card B); evs \<in> sr \<rbrakk>   
    \<Longrightarrow>  Says Server A \<lbrace>Nonce Pk, Crypt (shrK A) \<lbrace>Nonce Pk, Agent B\<rbrace>\<rbrace>   
           \<in> set evs  \<and> 
         Outpts (Card B) B \<lbrace>Nonce Nb, Key (sesK(Nb, pairK (A, B))),    
                             Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>,  
                             Crypt (pairK(A,B)) (Nonce Nb)\<rbrace>  
           \<in> set evs  \<and> 
         Outpts (Card A) A \<lbrace>Nonce Na, Cert3\<rbrace>  
           \<in> set evs"
apply (blast dest: Inputs_A_Card_9 Na_Nb_certificate_authentic Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Snd] Pairkey_certificate_authentic)
done

(*MSG8
Nothing to prove because the message is a cleartext that comes from the 
network*)

(*Other messages: nothing to prove because the verifiers involved are new*)


(*END further theorems about authenticity of verifiers*)



(* BEGIN trivial guarantees on outputs for agents *)

(*MSG4*)
lemma SR4_imp: 
     "\<lbrakk> Outpts (Card A) A \<lbrace>Nonce Na, Crypt (crdK (Card A)) (Nonce Na)\<rbrace> 
           \<in> set evs;  
         A \<noteq> Spy; evs \<in> sr \<rbrakk>                 
     \<Longrightarrow> \<exists> Pk V. Gets A \<lbrace>Pk, V\<rbrace> \<in> set evs"
apply (blast dest: Outpts_A_Card_4 Inputs_A_Card_3)
done
(*weak: could strengthen the model adding verifier for the Pairkey to msg3*)


(*MSG7*)
lemma SR7_imp: 
     "\<lbrakk> Outpts (Card B) B \<lbrace>Nonce Nb, Key K,  
                      Crypt (pairK(A,B)) \<lbrace>Nonce Na, Nonce Nb\<rbrace>,  
                      Cert2\<rbrace> \<in> set evs;  
         B \<noteq> Spy; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> Gets B \<lbrace>Agent A, Nonce Na\<rbrace> \<in> set evs"
apply (blast dest: Outpts_B_Card_7 Inputs_B_Card_6)
done

(*MSG10*)
lemma SR10_imp: 
     "\<lbrakk> Outpts (Card A) A \<lbrace>Key K, Crypt (pairK(A,B)) (Nonce Nb)\<rbrace>  
           \<in> set evs;  
         A \<noteq> Spy; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> \<exists> Cert1 Cert2.  
                   Gets A \<lbrace>Nonce (Pairkey (A, B)), Cert1\<rbrace> \<in> set evs \<and>  
                   Gets A \<lbrace>Nonce Nb, Cert2\<rbrace> \<in> set evs"
apply (blast dest: Outpts_A_Card_10 Inputs_A_Card_9)
done


(*END trivial guarantees on outputs for agents*)



(*INTEGRITY*)
lemma Outpts_Server_not_evs: "evs \<in> sr \<Longrightarrow> Outpts (Card Server) P X \<notin> set evs"
apply (erule sr.induct)
apply auto
done

text{*@{term step2_integrity} also is a reliability theorem*}
lemma Says_Server_message_form: 
     "\<lbrakk> Says Server A \<lbrace>Pk, Certificate\<rbrace> \<in> set evs;  
         evs \<in> sr \<rbrakk>                   
     \<Longrightarrow> \<exists> B. Pk = Nonce (Pairkey(A,B)) \<and>  
         Certificate = Crypt (shrK A) \<lbrace>Nonce (Pairkey(A,B)), Agent B\<rbrace>"
apply (erule rev_mp)
apply (erule sr.induct)
apply auto
apply (blast dest!: Outpts_Server_not_evs)+
done
(*cannot be made useful to A in form of a Gets event*)

text{*
  step4integrity is @{term Outpts_A_Card_form_4}

  step7integrity is @{term Outpts_B_Card_form_7}
*}

lemma step8_integrity: 
     "\<lbrakk> Says B A \<lbrace>Nonce Nb, Certificate\<rbrace> \<in> set evs;  
         B \<noteq> Server; B \<noteq> Spy; evs \<in> sr \<rbrakk>                   
     \<Longrightarrow> \<exists> Cert2 K.   
          Outpts (Card B) B \<lbrace>Nonce Nb, Key K, Certificate, Cert2\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule sr.induct)
prefer 18 apply (fastforce dest: Outpts_A_Card_form_10)
apply auto
done


text{*  step9integrity is @{term Inputs_A_Card_form_9}

        step10integrity is @{term Outpts_A_Card_form_10}.
*}

lemma step11_integrity: 
     "\<lbrakk> Says A B (Certificate) \<in> set evs; 
         \<forall> p q. Certificate \<noteq> \<lbrace>p, q\<rbrace>;  
         A \<noteq> Spy; evs \<in> sr \<rbrakk>  
     \<Longrightarrow> \<exists> K.  
            Outpts (Card A) A \<lbrace>Key K, Certificate\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule sr.induct)
apply auto
done

end
