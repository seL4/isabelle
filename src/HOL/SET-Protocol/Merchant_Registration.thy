(*  Title:      HOL/Auth/SET/Merchant_Registration
    ID:         $Id$
    Authors:    Giampaolo Bella, Fabio Massacci, Lawrence C Paulson
*)

header{*The SET Merchant Registration Protocol*}

theory Merchant_Registration = PublicSET:

text{*Copmpared with Cardholder Reigstration, @{text KeyCryptKey} is not
  needed: no session key encrypts another.  Instead we
  prove the "key compromise" theorems for sets KK that contain no private
  encryption keys (@{term "priEK C"}). *}


consts  set_mr  :: "event list set"
inductive set_mr
 intros

  Nil:    --{*Initial trace is empty*}
	   "[] \<in> set_mr"


  Fake:    --{*The spy MAY say anything he CAN say.*}
	   "[| evsf \<in> set_mr; X \<in> synth (analz (knows Spy evsf)) |]
	    ==> Says Spy B X  # evsf \<in> set_mr"
	

  Reception: --{*If A sends a message X to B, then B might receive it*}
	     "[| evsr \<in> set_mr; Says A B X \<in> set evsr |]
              ==> Gets B X  # evsr \<in> set_mr"


  SET_MR1: --{*RegFormReq: M requires a registration form to a CA*}
 	   "[| evs1 \<in> set_mr; M = Merchant k; Nonce NM1 \<notin> used evs1 |]
            ==> Says M (CA i) {|Agent M, Nonce NM1|} # evs1 \<in> set_mr"


  SET_MR2: --{*RegFormRes: CA replies with the registration form and the 
               certificates for her keys*}
  "[| evs2 \<in> set_mr; Nonce NCA \<notin> used evs2;
      Gets (CA i) {|Agent M, Nonce NM1|} \<in> set evs2 |]
   ==> Says (CA i) M {|sign (priSK (CA i)) {|Agent M, Nonce NM1, Nonce NCA|},
	               cert (CA i) (pubEK (CA i)) onlyEnc (priSK RCA),
                       cert (CA i) (pubSK (CA i)) onlySig (priSK RCA) |}
	 # evs2 \<in> set_mr"

  SET_MR3:
         --{*CertReq: M submits the key pair to be certified.  The Notes
             event allows KM1 to be lost if M is compromised. Piero remarks
             that the agent mentioned inside the signature is not verified to
             correspond to M.  As in CR, each Merchant has fixed key pairs.  M
             is only optionally required to send NCA back, so M doesn't do so
             in the model*}
  "[| evs3 \<in> set_mr; M = Merchant k; Nonce NM2 \<notin> used evs3;
      Key KM1 \<notin> used evs3;  KM1 \<in> symKeys;
      Gets M {|sign (invKey SKi) {|Agent X, Nonce NM1, Nonce NCA|},
	       cert (CA i) EKi onlyEnc (priSK RCA),
	       cert (CA i) SKi onlySig (priSK RCA) |}
	\<in> set evs3;
      Says M (CA i) {|Agent M, Nonce NM1|} \<in> set evs3 |]
   ==> Says M (CA i)
	    {|Crypt KM1 (sign (priSK M) {|Agent M, Nonce NM2,
					  Key (pubSK M), Key (pubEK M)|}),
	      Crypt EKi (Key KM1)|}
	 # Notes M {|Key KM1, Agent (CA i)|}
	 # evs3 \<in> set_mr"

  SET_MR4:
         --{*CertRes: CA issues the certificates for merSK and merEK,
             while checking never to have certified the m even
             separately. NOTE: In Cardholder Registration the
             corresponding rule (6) doesn't use the "sign" primitive. "The
             CertRes shall be signed but not encrypted if the EE is a Merchant
             or Payment Gateway."-- Programmer's Guide, page 191.*}
    "[| evs4 \<in> set_mr; M = Merchant k;
	merSK \<notin> symKeys;  merEK \<notin> symKeys;
	Notes (CA i) (Key merSK) \<notin> set evs4;
	Notes (CA i) (Key merEK) \<notin> set evs4;
	Gets (CA i) {|Crypt KM1 (sign (invKey merSK)
				 {|Agent M, Nonce NM2, Key merSK, Key merEK|}),
		      Crypt (pubEK (CA i)) (Key KM1) |}
	  \<in> set evs4 |]
    ==> Says (CA i) M {|sign (priSK(CA i)) {|Agent M, Nonce NM2, Agent(CA i)|},
			cert  M      merSK    onlySig (priSK (CA i)),
			cert  M      merEK    onlyEnc (priSK (CA i)),
			cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|}
	  # Notes (CA i) (Key merSK)
	  # Notes (CA i) (Key merEK)
	  # evs4 \<in> set_mr"


text{*Note possibility proofs are missing.*}

declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

text{*General facts about message reception*}
lemma Gets_imp_Says:
     "[| Gets B X \<in> set evs; evs \<in> set_mr |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule set_mr.induct, auto)
done

lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> set_mr |]  ==> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)


declare Gets_imp_knows_Spy [THEN parts.Inj, dest]

subsubsection{*Proofs on keys *}

text{*Spy never sees an agent's private keys! (unless it's bad at start)*}
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

text{*Proofs on certificates -
  they hold, as in CR, because RCA's keys are secure*}

lemma Crypt_valid_pubEK:
     "[| Crypt (priSK RCA) {|Agent (CA i), Key EKi, onlyEnc|}
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
     "[| Crypt (priSK RCA) {|Agent (CA i), Key SKi, onlySig|}
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
     "[| Gets A {| X, cert (CA i) EKi onlyEnc (priSK RCA),
                      cert (CA i) SKi onlySig (priSK RCA)|} \<in> set evs;
         evs \<in> set_mr |]
      ==> EKi = pubEK (CA i) & SKi = pubSK (CA i)"
by (blast dest: certificate_valid_pubEK certificate_valid_pubSK)


text{*Nobody can have used non-existent keys!*}
lemma new_keys_not_used [rule_format,simp]:
     "evs \<in> set_mr
      ==> Key K \<notin> used evs --> K \<in> symKeys -->
          K \<notin> keysFor (parts (knows Spy evs))"
apply (erule set_mr.induct, simp_all)
apply (force dest!: usedI keysFor_parts_insert)  --{*Fake*}
apply force  --{*Message 2*}
apply (blast dest: Gets_certificate_valid)  --{*Message 3*}
apply force  --{*Message 4*}
done


subsubsection{*New Versions: As Above, but Generalized with the Kk Argument*}

lemma gen_new_keys_not_used [rule_format]:
     "evs \<in> set_mr
      ==> Key K \<notin> used evs --> K \<in> symKeys -->
          K \<notin> keysFor (parts (Key`KK Un knows Spy evs))"
by auto

lemma gen_new_keys_not_analzd:
     "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> set_mr |]
      ==> K \<notin> keysFor (analz (Key`KK Un knows Spy evs))"
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

text{*Rewriting rule for private encryption keys.  Analogous rewriting rules
for other keys aren't needed.*}

lemma parts_image_priEK:
     "[|Key (priEK (CA i)) \<in> parts (Key`KK Un (knows Spy evs));
        evs \<in> set_mr|] ==> priEK (CA i) \<in> KK | CA i \<in> bad"
by auto

text{*trivial proof because (priEK (CA i)) never appears even in (parts evs)*}
lemma analz_image_priEK:
     "evs \<in> set_mr ==>
          (Key (priEK (CA i)) \<in> analz (Key`KK Un (knows Spy evs))) =
          (priEK (CA i) \<in> KK | CA i \<in> bad)"
by (blast dest!: parts_image_priEK intro: analz_mono [THEN [2] rev_subsetD])


subsection{*Secrecy of Session Keys*}

text{*This holds because if (priEK (CA i)) appears in any traffic then it must
  be known to the Spy, by @{text Spy_see_private_Key}*}
lemma merK_neq_priEK:
     "[|Key merK \<notin> analz (knows Spy evs);
        Key merK \<in> parts (knows Spy evs);
        evs \<in> set_mr|] ==> merK \<noteq> priEK C"
by blast

text{*Lemma for message 4: either merK is compromised (when we don't care)
  or else merK hasn't been used to encrypt K.*}
lemma msg4_priEK_disj:
     "[|Gets B {|Crypt KM1
                       (sign K {|Agent M, Nonce NM2, Key merSK, Key merEK|}),
                 Y|} \<in> set evs;
        evs \<in> set_mr|]
  ==> (Key merSK \<in> analz (knows Spy evs) | merSK \<notin> range(\<lambda>C. priEK C))
   &  (Key merEK \<in> analz (knows Spy evs) | merEK \<notin> range(\<lambda>C. priEK C))"
apply (unfold sign_def)
apply (blast dest: merK_neq_priEK)
done


lemma Key_analz_image_Key_lemma:
     "P --> (Key K \<in> analz (Key`KK Un H)) --> (K\<in>KK | Key K \<in> analz H)
      ==>
      P --> (Key K \<in> analz (Key`KK Un H)) = (K\<in>KK | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

lemma symKey_compromise:
     "evs \<in> set_mr ==>
      (\<forall>SK KK. SK \<in> symKeys \<longrightarrow> (\<forall>K \<in> KK. K \<notin> range(\<lambda>C. priEK C)) -->
               (Key SK \<in> analz (Key`KK Un (knows Spy evs))) =
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
  --{*23 seconds on a 1.8GHz machine*}
apply spy_analz  --{*Fake*}
apply auto  --{*Message 3*}
done

lemma symKey_secrecy [rule_format]:
     "[|CA i \<notin> bad; K \<in> symKeys;  evs \<in> set_mr|]
      ==> \<forall>X m. Says (Merchant m) (CA i) X \<in> set evs -->
                Key K \<in> parts{X} -->
                Merchant m \<notin> bad -->
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
apply spy_analz  --{*Fake*}
apply force  --{*Message 1*}
apply (auto intro: analz_into_parts [THEN usedI] in_parts_Says_imp_used)  --{*Message 3*}
done

subsection{*Unicity *}

lemma msg4_Says_imp_Notes:
 "[|Says (CA i) M {|sign (priSK (CA i)) {|Agent M, Nonce NM2, Agent (CA i)|},
		    cert  M      merSK    onlySig (priSK (CA i)),
		    cert  M      merEK    onlyEnc (priSK (CA i)),
		    cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|} \<in> set evs;
    evs \<in> set_mr |]
  ==> Notes (CA i) (Key merSK) \<in> set evs
   &  Notes (CA i) (Key merEK) \<in> set evs"
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
done

text{*Unicity of merSK wrt a given CA:
  merSK uniquely identifies the other components, including merEK*}
lemma merSK_unicity:
 "[|Says (CA i) M {|sign (priSK(CA i)) {|Agent M, Nonce NM2, Agent (CA i)|},
		    cert  M      merSK    onlySig (priSK (CA i)),
		    cert  M      merEK    onlyEnc (priSK (CA i)),
		    cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|} \<in> set evs;
    Says (CA i) M' {|sign (priSK(CA i)) {|Agent M', Nonce NM2', Agent (CA i)|},
		    cert  M'      merSK    onlySig (priSK (CA i)),
		    cert  M'      merEK'    onlyEnc (priSK (CA i)),
		    cert (CA i) (pubSK(CA i)) onlySig (priSK RCA)|} \<in> set evs;
    evs \<in> set_mr |] ==> M=M' & NM2=NM2' & merEK=merEK'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest!: msg4_Says_imp_Notes)
done

text{*Unicity of merEK wrt a given CA:
  merEK uniquely identifies the other components, including merSK*}
lemma merEK_unicity:
 "[|Says (CA i) M {|sign (priSK(CA i)) {|Agent M, Nonce NM2, Agent (CA i)|},
		    cert  M      merSK    onlySig (priSK (CA i)),
		    cert  M      merEK    onlyEnc (priSK (CA i)),
		    cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|} \<in> set evs;
    Says (CA i) M' {|sign (priSK(CA i)) {|Agent M', Nonce NM2', Agent (CA i)|},
		     cert  M'      merSK'    onlySig (priSK (CA i)),
		     cert  M'      merEK    onlyEnc (priSK (CA i)),
		     cert (CA i) (pubSK(CA i)) onlySig (priSK RCA)|} \<in> set evs;
    evs \<in> set_mr |] 
  ==> M=M' & NM2=NM2' & merSK=merSK'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest!: msg4_Says_imp_Notes)
done


text{* -No interest on secrecy of nonces: they appear to be used
    only for freshness.
   -No interest on secrecy of merSK or merEK, as in CR.
   -There's no equivalent of the PAN*}


subsection{*Primary Goals of Merchant Registration *}

subsubsection{*The merchant's certificates really were created by the CA,
provided the CA is uncompromised *}

text{*The assumption @{term "CA i \<noteq> RCA"} is required: step 2 uses 
  certificates of the same form.*}
lemma certificate_merSK_valid_lemma [intro]:
     "[|Crypt (priSK (CA i)) {|Agent M, Key merSK, onlySig|}
          \<in> parts (knows Spy evs);
        CA i \<notin> bad;  CA i \<noteq> RCA;  evs \<in> set_mr|]
 ==> \<exists>X Y Z. Says (CA i) M
                  {|X, cert M merSK onlySig (priSK (CA i)), Y, Z|} \<in> set evs"
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
apply auto
done

lemma certificate_merSK_valid:
     "[| cert M merSK onlySig (priSK (CA i)) \<in> parts (knows Spy evs);
         CA i \<notin> bad;  CA i \<noteq> RCA;  evs \<in> set_mr|]
 ==> \<exists>X Y Z. Says (CA i) M
                  {|X, cert M merSK onlySig (priSK (CA i)), Y, Z|} \<in> set evs"
by auto

lemma certificate_merEK_valid_lemma [intro]:
     "[|Crypt (priSK (CA i)) {|Agent M, Key merEK, onlyEnc|}
          \<in> parts (knows Spy evs);
        CA i \<notin> bad;  CA i \<noteq> RCA;  evs \<in> set_mr|]
 ==> \<exists>X Y Z. Says (CA i) M
                  {|X, Y, cert M merEK onlyEnc (priSK (CA i)), Z|} \<in> set evs"
apply (erule rev_mp)
apply (erule set_mr.induct)
apply (simp_all (no_asm_simp))
apply auto
done

lemma certificate_merEK_valid:
     "[| cert M merEK onlyEnc (priSK (CA i)) \<in> parts (knows Spy evs);
         CA i \<notin> bad;  CA i \<noteq> RCA;  evs \<in> set_mr|]
 ==> \<exists>X Y Z. Says (CA i) M
                  {|X, Y, cert M merEK onlyEnc (priSK (CA i)), Z|} \<in> set evs"
by auto

text{*The two certificates - for merSK and for merEK - cannot be proved to
  have originated together*}

end
