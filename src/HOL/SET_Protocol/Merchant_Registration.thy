(*  Title:      HOL/SET_Protocol/Merchant_Registration.thy
    Author:     Giampaolo Bella
    Author:     Fabio Massacci
    Author:     Lawrence C Paulson
*)

section\<open>The SET Merchant Registration Protocol\<close>

theory Merchant_Registration
imports Public_SET
begin

text\<open>Copmpared with Cardholder Reigstration, \<open>KeyCryptKey\<close> is not
  needed: no session key encrypts another.  Instead we
  prove the "key compromise" theorems for sets KK that contain no private
  encryption keys (@{term "priEK C"}).\<close>


inductive_set
  set_mr :: "event list set"
where

  Nil:    \<comment> \<open>Initial trace is empty\<close>
           "[] \<in> set_mr"


| Fake:    \<comment> \<open>The spy MAY say anything he CAN say.\<close>
           "[| evsf \<in> set_mr; X \<in> synth (analz (knows Spy evsf)) |]
            ==> Says Spy B X  # evsf \<in> set_mr"
        

| Reception: \<comment> \<open>If A sends a message X to B, then B might receive it\<close>
             "[| evsr \<in> set_mr; Says A B X \<in> set evsr |]
              ==> Gets B X  # evsr \<in> set_mr"


| SET_MR1: \<comment> \<open>RegFormReq: M requires a registration form to a CA\<close>
           "[| evs1 \<in> set_mr; M = Merchant k; Nonce NM1 \<notin> used evs1 |]
            ==> Says M (CA i) \<lbrace>Agent M, Nonce NM1\<rbrace> # evs1 \<in> set_mr"


| SET_MR2: \<comment> \<open>RegFormRes: CA replies with the registration form and the 
               certificates for her keys\<close>
  "[| evs2 \<in> set_mr; Nonce NCA \<notin> used evs2;
      Gets (CA i) \<lbrace>Agent M, Nonce NM1\<rbrace> \<in> set evs2 |]
   ==> Says (CA i) M \<lbrace>sign (priSK (CA i)) \<lbrace>Agent M, Nonce NM1, Nonce NCA\<rbrace>,
                       cert (CA i) (pubEK (CA i)) onlyEnc (priSK RCA),
                       cert (CA i) (pubSK (CA i)) onlySig (priSK RCA) \<rbrace>
         # evs2 \<in> set_mr"

| SET_MR3:
         \<comment> \<open>CertReq: M submits the key pair to be certified.  The Notes
             event allows KM1 to be lost if M is compromised. Piero remarks
             that the agent mentioned inside the signature is not verified to
             correspond to M.  As in CR, each Merchant has fixed key pairs.  M
             is only optionally required to send NCA back, so M doesn't do so
             in the model\<close>
  "[| evs3 \<in> set_mr; M = Merchant k; Nonce NM2 \<notin> used evs3;
      Key KM1 \<notin> used evs3;  KM1 \<in> symKeys;
      Gets M \<lbrace>sign (invKey SKi) \<lbrace>Agent X, Nonce NM1, Nonce NCA\<rbrace>,
               cert (CA i) EKi onlyEnc (priSK RCA),
               cert (CA i) SKi onlySig (priSK RCA) \<rbrace>
        \<in> set evs3;
      Says M (CA i) \<lbrace>Agent M, Nonce NM1\<rbrace> \<in> set evs3 |]
   ==> Says M (CA i)
            \<lbrace>Crypt KM1 (sign (priSK M) \<lbrace>Agent M, Nonce NM2,
                                          Key (pubSK M), Key (pubEK M)\<rbrace>),
              Crypt EKi (Key KM1)\<rbrace>
         # Notes M \<lbrace>Key KM1, Agent (CA i)\<rbrace>
         # evs3 \<in> set_mr"

| SET_MR4:
         \<comment> \<open>CertRes: CA issues the certificates for merSK and merEK,
             while checking never to have certified the m even
             separately. NOTE: In Cardholder Registration the
             corresponding rule (6) doesn't use the "sign" primitive. "The
             CertRes shall be signed but not encrypted if the EE is a Merchant
             or Payment Gateway."-- Programmer's Guide, page 191.\<close>
    "[| evs4 \<in> set_mr; M = Merchant k;
        merSK \<notin> symKeys;  merEK \<notin> symKeys;
        Notes (CA i) (Key merSK) \<notin> set evs4;
        Notes (CA i) (Key merEK) \<notin> set evs4;
        Gets (CA i) \<lbrace>Crypt KM1 (sign (invKey merSK)
                                 \<lbrace>Agent M, Nonce NM2, Key merSK, Key merEK\<rbrace>),
                      Crypt (pubEK (CA i)) (Key KM1) \<rbrace>
          \<in> set evs4 |]
    ==> Says (CA i) M \<lbrace>sign (priSK(CA i)) \<lbrace>Agent M, Nonce NM2, Agent(CA i)\<rbrace>,
                        cert  M      merSK    onlySig (priSK (CA i)),
                        cert  M      merEK    onlyEnc (priSK (CA i)),
                        cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace>
          # Notes (CA i) (Key merSK)
          # Notes (CA i) (Key merEK)
          # evs4 \<in> set_mr"


text\<open>Note possibility proofs are missing.\<close>

declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

text\<open>General facts about message reception\<close>
lemma Gets_imp_Says:
     "[| Gets B X \<in> set evs; evs \<in> set_mr |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule set_mr.induct, auto)
done

lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> set_mr |]  ==> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)


declare Gets_imp_knows_Spy [THEN parts.Inj, dest]

subsubsection\<open>Proofs on keys\<close>

text\<open>Spy never sees an agent's private keys! (unless it's bad at start)\<close>
lemma Spy_see_private_Key [simp]:
     "evs \<in> set_mr
      ==> (Key(invKey (publicKey b A)) \<in> parts(knows Spy evs)) = (A \<in> bad)"
apply (erule set_mr.induct)
apply (auto dest!: Gets_imp_knows_Spy [THEN parts.Inj])
done

lemma Spy_analz_private_Key [simp]:
     "evs \<in> set_mr ==>
     (Key(invKey (publicKey b A)) \<in> analz(knows Spy evs)) = (A \<in> bad)"
by auto

declare Spy_see_private_Key [THEN [2] rev_iffD1, dest!]
declare Spy_analz_private_Key [THEN [2] rev_iffD1, dest!]

(*This is to state that the signed keys received in step 4
  are into parts - rather than installing sign_def each time.
  Needed in Spy_see_priSK_RCA, Spy_see_priEK and in Spy_see_priSK
Goal "[|Gets C \<lbrace>Crypt KM1
                (sign K \<lbrace>Agent M, Nonce NM2, Key merSK, Key merEK\<rbrace>), X\<rbrace>
          \<in> set evs;  evs \<in> set_mr |]
    ==> Key merSK \<in> parts (knows Spy evs) \<and>
        Key merEK \<in> parts (knows Spy evs)"
by (fast_tac (claset() addss (simpset())) 1);
qed "signed_keys_in_parts";
???*)

text\<open>Proofs on certificates -
  they hold, as in CR, because RCA's keys are secure\<close>

lemma Crypt_valid_pubEK:
     "[| Crypt (priSK RCA) \<lbrace>Agent (CA i), Key EKi, onlyEnc\<rbrace>
           \<in> parts (knows Spy evs);
         evs \<in> set_mr |] ==> EKi = pubEK (CA i)"
apply (erule rev_mp)
apply (erule set_mr.induct, auto)
done

lemma certificate_valid_pubEK:
    "[| cert (CA i) EKi onlyEnc (priSK RCA) \<in> parts (knows Spy evs);
        evs \<in> set_mr |]
     ==> EKi = pubEK (CA i)"
apply (unfold cert_def signCert_def)
apply (blast dest!: Crypt_valid_pubEK)
done

lemma Crypt_valid_pubSK:
     "[| Crypt (priSK RCA) \<lbrace>Agent (CA i), Key SKi, onlySig\<rbrace>
           \<in> parts (knows Spy evs);
         evs \<in> set_mr |] ==> SKi = pubSK (CA i)"
apply (erule rev_mp)
apply (erule set_mr.induct, auto)
done

lemma certificate_valid_pubSK:
    "[| cert (CA i) SKi onlySig (priSK RCA) \<in> parts (knows Spy evs);
        evs \<in> set_mr |] ==> SKi = pubSK (CA i)"
apply (unfold cert_def signCert_def)
apply (blast dest!: Crypt_valid_pubSK)
done

lemma Gets_certificate_valid:
     "[| Gets A \<lbrace> X, cert (CA i) EKi onlyEnc (priSK RCA),
                      cert (CA i) SKi onlySig (priSK RCA)\<rbrace> \<in> set evs;
         evs \<in> set_mr |]
      ==> EKi = pubEK (CA i) \<and> SKi = pubSK (CA i)"
by (blast dest: certificate_valid_pubEK certificate_valid_pubSK)


text\<open>Nobody can have used non-existent keys!\<close>
lemma new_keys_not_used [rule_format,simp]:
     "evs \<in> set_mr
      ==> Key K \<notin> used evs \<longrightarrow> K \<in> symKeys \<longrightarrow>
          K \<notin> keysFor (parts (knows Spy evs))"
apply (erule set_mr.induct, simp_all)
apply (force dest!: usedI keysFor_parts_insert)  \<comment> \<open>Fake\<close>
apply force  \<comment> \<open>Message 2\<close>
apply (blast dest: Gets_certificate_valid)  \<comment> \<open>Message 3\<close>
apply force  \<comment> \<open>Message 4\<close>
done


subsubsection\<open>New Versions: As Above, but Generalized with the Kk Argument\<close>

lemma gen_new_keys_not_used [rule_format]:
     "evs \<in> set_mr
      ==> Key K \<notin> used evs \<longrightarrow> K \<in> symKeys \<longrightarrow>
          K \<notin> keysFor (parts (Key`KK \<union> knows Spy evs))"
by auto

lemma gen_new_keys_not_analzd:
     "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> set_mr |]
      ==> K \<notin> keysFor (analz (Key`KK \<union> knows Spy evs))"
by (blast intro: keysFor_mono [THEN [2] rev_subsetD]
          dest: gen_new_keys_not_used)

lemma analz_Key_image_insert_eq:
     "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> set_mr |]
      ==> analz (Key ` (insert K KK) \<union> knows Spy evs) =
          insert (Key K) (analz (Key ` KK \<union> knows Spy evs))"
by (simp add: gen_new_keys_not_analzd)


lemma Crypt_parts_imp_used:
     "[|Crypt K X \<in> parts (knows Spy evs);
        K \<in> symKeys; evs \<in> set_mr |] ==> Key K \<in> used evs"
apply (rule ccontr)
apply (force dest: new_keys_not_used Crypt_imp_invKey_keysFor)
done

lemma Crypt_analz_imp_used:
     "[|Crypt K X \<in> analz (knows Spy evs);
        K \<in> symKeys; evs \<in> set_mr |] ==> Key K \<in> used evs"
by (blast intro: Crypt_parts_imp_used)

text\<open>Rewriting rule for private encryption keys.  Analogous rewriting rules
for other keys aren't needed.\<close>

lemma parts_image_priEK:
     "[|Key (priEK (CA i)) \<in> parts (Key`KK \<union> (knows Spy evs));
        evs \<in> set_mr|] ==> priEK (CA i) \<in> KK | CA i \<in> bad"
by auto

text\<open>trivial proof because (priEK (CA i)) never appears even in (parts evs)\<close>
lemma analz_image_priEK:
     "evs \<in> set_mr ==>
          (Key (priEK (CA i)) \<in> analz (Key`KK \<union> (knows Spy evs))) =
          (priEK (CA i) \<in> KK | CA i \<in> bad)"
by (blast dest!: parts_image_priEK intro: analz_mono [THEN [2] rev_subsetD])


subsection\<open>Secrecy of Session Keys\<close>

text\<open>This holds because if (priEK (CA i)) appears in any traffic then it must
  be known to the Spy, by \<open>Spy_see_private_Key\<close>\<close>
lemma merK_neq_priEK:
     "[|Key merK \<notin> analz (knows Spy evs);
        Key merK \<in> parts (knows Spy evs);
        evs \<in> set_mr|] ==> merK \<noteq> priEK C"
by blast

text\<open>Lemma for message 4: either merK is compromised (when we don't care)
  or else merK hasn't been used to encrypt K.\<close>
lemma msg4_priEK_disj:
     "[|Gets B \<lbrace>Crypt KM1
                       (sign K \<lbrace>Agent M, Nonce NM2, Key merSK, Key merEK\<rbrace>),
                 Y\<rbrace> \<in> set evs;
        evs \<in> set_mr|]
  ==> (Key merSK \<in> analz (knows Spy evs) | merSK \<notin> range(\<lambda>C. priEK C))
   \<and>  (Key merEK \<in> analz (knows Spy evs) | merEK \<notin> range(\<lambda>C. priEK C))"
apply (unfold sign_def)
apply (blast dest: merK_neq_priEK)
done


lemma Key_analz_image_Key_lemma:
     "P \<longrightarrow> (Key K \<in> analz (Key`KK \<union> H)) \<longrightarrow> (K\<in>KK | Key K \<in> analz H)
      ==>
      P \<longrightarrow> (Key K \<in> analz (Key`KK \<union> H)) = (K\<in>KK | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

lemma symKey_compromise:
     "evs \<in> set_mr ==>
      (\<forall>SK KK. SK \<in> symKeys \<longrightarrow> (\<forall>K \<in> KK. K \<notin> range(\<lambda>C. priEK C)) \<longrightarrow>
               (Key SK \<in> analz (Key`KK \<union> (knows Spy evs))) =
               (SK \<in> KK | Key SK \<in> analz (knows Spy evs)))"
apply (erule set_mr.induct)
apply (safe del: impI intro!: Key_analz_image_Key_lemma [THEN impI])
apply (drule_tac [7] msg4_priEK_disj)
apply (frule_tac [6] Gets_certificate_valid)
apply (safe del: impI)
apply (simp_all del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps abbrev_simps analz_knows_absorb
              analz_knows_absorb2 analz_Key_image_insert_eq notin_image_iff
              Spy_analz_private_Key analz_image_priEK)
  \<comment> \<open>5 seconds on a 1.6GHz machine\<close>
apply spy_analz  \<comment> \<open>Fake\<close>
apply auto  \<comment> \<open>Message 3\<close>
done

lemma symKey_secrecy [rule_format]:
     "[|CA i \<notin> bad; K \<in> symKeys;  evs \<in> set_mr|]
      ==> \<forall>X m. Says (Merchant m) (CA i) X \<in> set evs \<longrightarrow>
                Key K \<in> parts{X} \<longrightarrow>
                Merchant m \<notin> bad \<longrightarrow>
                Key K \<notin> analz (knows Spy evs)"
apply (erule set_mr.induct)
apply (drule_tac [7] msg4_priEK_disj)
apply (frule_tac [6] Gets_certificate_valid)
apply (safe del: impI)
apply (simp_all del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps abbrev_simps analz_knows_absorb
              analz_knows_absorb2 analz_Key_image_insert_eq
              symKey_compromise notin_image_iff Spy_analz_private_Key
              analz_image_priEK)
apply spy_analz  \<comment> \<open>Fake\<close>
apply force  \<comment> \<open>Message 1\<close>
apply (auto intro: analz_into_parts [THEN usedI] in_parts_Says_imp_used)  \<comment> \<open>Message 3\<close>
done

subsection\<open>Unicity\<close>

lemma msg4_Says_imp_Notes:
 "[|Says (CA i) M \<lbrace>sign (priSK (CA i)) \<lbrace>Agent M, Nonce NM2, Agent (CA i)\<rbrace>,
                    cert  M      merSK    onlySig (priSK (CA i)),
                    cert  M      merEK    onlyEnc (priSK (CA i)),
                    cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace> \<in> set evs;
    evs \<in> set_mr |]
  ==> Notes (CA i) (Key merSK) \<in> set evs
   \<and>  Notes (CA i) (Key merEK) \<in> set evs"
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
done

text\<open>Unicity of merSK wrt a given CA:
  merSK uniquely identifies the other components, including merEK\<close>
lemma merSK_unicity:
 "[|Says (CA i) M \<lbrace>sign (priSK(CA i)) \<lbrace>Agent M, Nonce NM2, Agent (CA i)\<rbrace>,
                    cert  M      merSK    onlySig (priSK (CA i)),
                    cert  M      merEK    onlyEnc (priSK (CA i)),
                    cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace> \<in> set evs;
    Says (CA i) M' \<lbrace>sign (priSK(CA i)) \<lbrace>Agent M', Nonce NM2', Agent (CA i)\<rbrace>,
                    cert  M'      merSK    onlySig (priSK (CA i)),
                    cert  M'      merEK'    onlyEnc (priSK (CA i)),
                    cert (CA i) (pubSK(CA i)) onlySig (priSK RCA)\<rbrace> \<in> set evs;
    evs \<in> set_mr |] ==> M=M' \<and> NM2=NM2' \<and> merEK=merEK'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest!: msg4_Says_imp_Notes)
done

text\<open>Unicity of merEK wrt a given CA:
  merEK uniquely identifies the other components, including merSK\<close>
lemma merEK_unicity:
 "[|Says (CA i) M \<lbrace>sign (priSK(CA i)) \<lbrace>Agent M, Nonce NM2, Agent (CA i)\<rbrace>,
                    cert  M      merSK    onlySig (priSK (CA i)),
                    cert  M      merEK    onlyEnc (priSK (CA i)),
                    cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace> \<in> set evs;
    Says (CA i) M' \<lbrace>sign (priSK(CA i)) \<lbrace>Agent M', Nonce NM2', Agent (CA i)\<rbrace>,
                     cert  M'      merSK'    onlySig (priSK (CA i)),
                     cert  M'      merEK    onlyEnc (priSK (CA i)),
                     cert (CA i) (pubSK(CA i)) onlySig (priSK RCA)\<rbrace> \<in> set evs;
    evs \<in> set_mr |] 
  ==> M=M' \<and> NM2=NM2' \<and> merSK=merSK'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest!: msg4_Says_imp_Notes)
done


text\<open>-No interest on secrecy of nonces: they appear to be used
    only for freshness.
   -No interest on secrecy of merSK or merEK, as in CR.
   -There's no equivalent of the PAN\<close>


subsection\<open>Primary Goals of Merchant Registration\<close>

subsubsection\<open>The merchant's certificates really were created by the CA,
provided the CA is uncompromised\<close>

text\<open>The assumption @{term "CA i \<noteq> RCA"} is required: step 2 uses 
  certificates of the same form.\<close>
lemma certificate_merSK_valid_lemma [intro]:
     "[|Crypt (priSK (CA i)) \<lbrace>Agent M, Key merSK, onlySig\<rbrace>
          \<in> parts (knows Spy evs);
        CA i \<notin> bad;  CA i \<noteq> RCA;  evs \<in> set_mr|]
 ==> \<exists>X Y Z. Says (CA i) M
                  \<lbrace>X, cert M merSK onlySig (priSK (CA i)), Y, Z\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
apply auto
done

lemma certificate_merSK_valid:
     "[| cert M merSK onlySig (priSK (CA i)) \<in> parts (knows Spy evs);
         CA i \<notin> bad;  CA i \<noteq> RCA;  evs \<in> set_mr|]
 ==> \<exists>X Y Z. Says (CA i) M
                  \<lbrace>X, cert M merSK onlySig (priSK (CA i)), Y, Z\<rbrace> \<in> set evs"
by auto

lemma certificate_merEK_valid_lemma [intro]:
     "[|Crypt (priSK (CA i)) \<lbrace>Agent M, Key merEK, onlyEnc\<rbrace>
          \<in> parts (knows Spy evs);
        CA i \<notin> bad;  CA i \<noteq> RCA;  evs \<in> set_mr|]
 ==> \<exists>X Y Z. Says (CA i) M
                  \<lbrace>X, Y, cert M merEK onlyEnc (priSK (CA i)), Z\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
apply auto
done

lemma certificate_merEK_valid:
     "[| cert M merEK onlyEnc (priSK (CA i)) \<in> parts (knows Spy evs);
         CA i \<notin> bad;  CA i \<noteq> RCA;  evs \<in> set_mr|]
 ==> \<exists>X Y Z. Says (CA i) M
                  \<lbrace>X, Y, cert M merEK onlyEnc (priSK (CA i)), Z\<rbrace> \<in> set evs"
by auto

text\<open>The two certificates - for merSK and for merEK - cannot be proved to
  have originated together\<close>

end
