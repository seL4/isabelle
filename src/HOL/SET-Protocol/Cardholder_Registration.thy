(*  Title:      HOL/Auth/SET/Cardholder_Registration
    ID:         $Id$
    Authors:    Giampaolo Bella, Fabio Massacci, Lawrence C Paulson,
                Piero Tramontano
*)

header{*The SET Cardholder Registration Protocol*}

theory Cardholder_Registration = PublicSET:

text{*Note: nonces seem to consist of 20 bytes.  That includes both freshness
challenges (Chall-EE, etc.) and important secrets (CardSecret, PANsecret)
*}

text{*Simplifications involving @{text analz_image_keys_simps} appear to
have become much slower. The cause is unclear. However, there is a big blow-up
and the rewriting is very sensitive to the set of rewrite rules given.*}

subsection{*Predicate Formalizing the Encryption Association between Keys *}

consts
  KeyCryptKey :: "[key, key, event list] => bool"

primrec

KeyCryptKey_Nil:
  "KeyCryptKey DK K [] = False"

KeyCryptKey_Cons:
      --{*Says is the only important case.
	1st case: CR5, where KC3 encrypts KC2.
	2nd case: any use of priEK C.
	Revision 1.12 has a more complicated version with separate treatment of
	  the dependency of KC1, KC2 and KC3 on priEK (CA i.)  Not needed since
	  priEK C is never sent (and so can't be lost except at the start). *}
  "KeyCryptKey DK K (ev # evs) =
   (KeyCryptKey DK K evs |
    (case ev of
      Says A B Z =>
       ((\<exists>N X Y. A \<noteq> Spy &
	         DK \<in> symKeys &
		 Z = {|Crypt DK {|Agent A, Nonce N, Key K, X|}, Y|}) |
	(\<exists>C. DK = priEK C))
    | Gets A' X => False
    | Notes A' X => False))"


subsection{*Predicate formalizing the association between keys and nonces *}

consts
  KeyCryptNonce :: "[key, key, event list] => bool"

primrec

KeyCryptNonce_Nil:
  "KeyCryptNonce EK K [] = False"

KeyCryptNonce_Cons:
  --{*Says is the only important case.
    1st case: CR3, where KC1 encrypts NC2 (distinct from CR5 due to EXH);
    2nd case: CR5, where KC3 encrypts NC3;
    3rd case: CR6, where KC2 encrypts NC3;
    4th case: CR6, where KC2 encrypts NonceCCA;
    5th case: any use of @{term "priEK C"} (including CardSecret).
    NB the only Nonces we need to keep secret are CardSecret and NonceCCA.
    But we can't prove @{text Nonce_compromise} unless the relation covers ALL
	nonces that the protocol keeps secret.
  *}
  "KeyCryptNonce DK N (ev # evs) =
   (KeyCryptNonce DK N evs |
    (case ev of
      Says A B Z =>
       A \<noteq> Spy &
       ((\<exists>X Y. DK \<in> symKeys &
	       Z = (EXHcrypt DK X {|Agent A, Nonce N|} Y)) |
	(\<exists>X Y. DK \<in> symKeys &
	       Z = {|Crypt DK {|Agent A, Nonce N, X|}, Y|}) |
	(\<exists>K i X Y.
	  K \<in> symKeys &
          Z = Crypt K {|sign (priSK (CA i)) {|Agent B, Nonce N, X|}, Y|} &
	  (DK=K | KeyCryptKey DK K evs)) |
	(\<exists>K C NC3 Y.
	  K \<in> symKeys &
          Z = Crypt K
 	        {|sign (priSK C) {|Agent B, Nonce NC3, Agent C, Nonce N|},
                  Y|} &
	  (DK=K | KeyCryptKey DK K evs)) |
	(\<exists>C. DK = priEK C))
    | Gets A' X => False
    | Notes A' X => False))"


subsection{*Formal protocol definition *}

consts  set_cr  :: "event list set"
inductive set_cr
 intros

  Nil:    --{*Initial trace is empty*}
	  "[] \<in> set_cr"

  Fake:    --{*The spy MAY say anything he CAN say.*}
	   "[| evsf \<in> set_cr; X \<in> synth (analz (knows Spy evsf)) |]
	    ==> Says Spy B X  # evsf \<in> set_cr"

  Reception: --{*If A sends a message X to B, then B might receive it*}
	     "[| evsr \<in> set_cr; Says A B X \<in> set evsr |]
              ==> Gets B X  # evsr \<in> set_cr"

  SET_CR1: --{*CardCInitReq: C initiates a run, sending a nonce to CCA*}
	     "[| evs1 \<in> set_cr;  C = Cardholder k;  Nonce NC1 \<notin> used evs1 |]
	      ==> Says C (CA i) {|Agent C, Nonce NC1|} # evs1 \<in> set_cr"

  SET_CR2: --{*CardCInitRes: CA responds sending NC1 and its certificates*}
	     "[| evs2 \<in> set_cr;
		 Gets (CA i) {|Agent C, Nonce NC1|} \<in> set evs2 |]
	      ==> Says (CA i) C
		       {|sign (priSK (CA i)) {|Agent C, Nonce NC1|},
			 cert (CA i) (pubEK (CA i)) onlyEnc (priSK RCA),
			 cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|}
		    # evs2 \<in> set_cr"

  SET_CR3:
   --{*RegFormReq: C sends his PAN and a new nonce to CA.
   C verifies that
    - nonce received is the same as that sent;
    - certificates are signed by RCA;
    - certificates are an encryption certificate (flag is onlyEnc) and a
      signature certificate (flag is onlySig);
    - certificates pertain to the CA that C contacted (this is done by
      checking the signature).
   C generates a fresh symmetric key KC1.
   The point of encrypting @{term "{|Agent C, Nonce NC2, Hash (Pan(pan C))|}"}
   is not clear. *}
"[| evs3 \<in> set_cr;  C = Cardholder k;
    Nonce NC2 \<notin> used evs3;
    Key KC1 \<notin> used evs3; KC1 \<in> symKeys;
    Gets C {|sign (invKey SKi) {|Agent X, Nonce NC1|},
	     cert (CA i) EKi onlyEnc (priSK RCA),
	     cert (CA i) SKi onlySig (priSK RCA)|}
       \<in> set evs3;
    Says C (CA i) {|Agent C, Nonce NC1|} \<in> set evs3|]
 ==> Says C (CA i) (EXHcrypt KC1 EKi {|Agent C, Nonce NC2|} (Pan(pan C)))
       # Notes C {|Key KC1, Agent (CA i)|}
       # evs3 \<in> set_cr"

  SET_CR4:
    --{*RegFormRes:
    CA responds sending NC2 back with a new nonce NCA, after checking that
     - the digital envelope is correctly encrypted by @{term "pubEK (CA i)"}
     - the entire message is encrypted with the same key found inside the
       envelope (here, KC1) *}
"[| evs4 \<in> set_cr;
    Nonce NCA \<notin> used evs4;  KC1 \<in> symKeys;
    Gets (CA i) (EXHcrypt KC1 EKi {|Agent C, Nonce NC2|} (Pan(pan X)))
       \<in> set evs4 |]
  ==> Says (CA i) C
	  {|sign (priSK (CA i)) {|Agent C, Nonce NC2, Nonce NCA|},
	    cert (CA i) (pubEK (CA i)) onlyEnc (priSK RCA),
	    cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|}
       # evs4 \<in> set_cr"

  SET_CR5:
   --{*CertReq: C sends his PAN, a new nonce, its proposed public signature key
       and its half of the secret value to CA.
       We now assume that C has a fixed key pair, and he submits (pubSK C).
       The protocol does not require this key to be fresh.
       The encryption below is actually EncX.*}
"[| evs5 \<in> set_cr;  C = Cardholder k;
    Nonce NC3 \<notin> used evs5;  Nonce CardSecret \<notin> used evs5; NC3\<noteq>CardSecret;
    Key KC2 \<notin> used evs5; KC2 \<in> symKeys;
    Key KC3 \<notin> used evs5; KC3 \<in> symKeys; KC2\<noteq>KC3;
    Gets C {|sign (invKey SKi) {|Agent C, Nonce NC2, Nonce NCA|},
             cert (CA i) EKi onlyEnc (priSK RCA),
             cert (CA i) SKi onlySig (priSK RCA) |}
        \<in> set evs5;
    Says C (CA i) (EXHcrypt KC1 EKi {|Agent C, Nonce NC2|} (Pan(pan C)))
         \<in> set evs5 |]
==> Says C (CA i)
         {|Crypt KC3
	     {|Agent C, Nonce NC3, Key KC2, Key (pubSK C),
	       Crypt (priSK C)
	         (Hash {|Agent C, Nonce NC3, Key KC2,
			 Key (pubSK C), Pan (pan C), Nonce CardSecret|})|},
           Crypt EKi {|Key KC3, Pan (pan C), Nonce CardSecret|} |}
    # Notes C {|Key KC2, Agent (CA i)|}
    # Notes C {|Key KC3, Agent (CA i)|}
    # evs5 \<in> set_cr"


  --{* CertRes: CA responds sending NC3 back with its half of the secret value,
   its signature certificate and the new cardholder signature
   certificate.  CA checks to have never certified the key proposed by C.
   NOTE: In Merchant Registration, the corresponding rule (4)
   uses the "sign" primitive. The encryption below is actually @{term EncK}, 
   which is just @{term "Crypt K (sign SK X)"}.
*}

SET_CR6:
"[| evs6 \<in> set_cr;
    Nonce NonceCCA \<notin> used evs6;
    KC2 \<in> symKeys;  KC3 \<in> symKeys;  cardSK \<notin> symKeys;
    Notes (CA i) (Key cardSK) \<notin> set evs6;
    Gets (CA i)
      {|Crypt KC3 {|Agent C, Nonce NC3, Key KC2, Key cardSK,
                    Crypt (invKey cardSK)
                      (Hash {|Agent C, Nonce NC3, Key KC2,
			      Key cardSK, Pan (pan C), Nonce CardSecret|})|},
        Crypt (pubEK (CA i)) {|Key KC3, Pan (pan C), Nonce CardSecret|} |}
      \<in> set evs6 |]
==> Says (CA i) C
         (Crypt KC2
	  {|sign (priSK (CA i))
	         {|Agent C, Nonce NC3, Agent(CA i), Nonce NonceCCA|},
	    certC (pan C) cardSK (XOR(CardSecret,NonceCCA)) onlySig (priSK (CA i)),
	    cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|})
      # Notes (CA i) (Key cardSK)
      # evs6 \<in> set_cr"


declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

text{*A "possibility property": there are traces that reach the end.
      An unconstrained proof with many subgoals.*}

lemma Says_to_Gets:
     "Says A B X # evs \<in> set_cr ==> Gets B X # Says A B X # evs \<in> set_cr"
by (rule set_cr.Reception, auto)

text{*The many nonces and keys generated, some simultaneously, force us to
  introduce them explicitly as shown below.*}
lemma possibility_CR6:
     "[|NC1 < (NC2::nat);  NC2 < NC3;  NC3 < NCA ;
        NCA < NonceCCA;  NonceCCA < CardSecret;
        KC1 < (KC2::key);  KC2 < KC3;
        KC1 \<in> symKeys;  Key KC1 \<notin> used [];
        KC2 \<in> symKeys;  Key KC2 \<notin> used [];
        KC3 \<in> symKeys;  Key KC3 \<notin> used [];
        C = Cardholder k|]
   ==> \<exists>evs \<in> set_cr.
       Says (CA i) C
            (Crypt KC2
             {|sign (priSK (CA i))
                    {|Agent C, Nonce NC3, Agent(CA i), Nonce NonceCCA|},
               certC (pan C) (pubSK (Cardholder k)) (XOR(CardSecret,NonceCCA))
                     onlySig (priSK (CA i)),
               cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|})
          \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] 
       set_cr.Nil 
        [THEN set_cr.SET_CR1 [of concl: C i NC1], 
         THEN Says_to_Gets, 
	 THEN set_cr.SET_CR2 [of concl: i C NC1], 
	 THEN Says_to_Gets,  
	 THEN set_cr.SET_CR3 [of concl: C i KC1 _ NC2], 
	 THEN Says_to_Gets,  
	 THEN set_cr.SET_CR4 [of concl: i C NC2 NCA], 
	 THEN Says_to_Gets,  
	 THEN set_cr.SET_CR5 [of concl: C i KC3 NC3 KC2 CardSecret],
	 THEN Says_to_Gets,  
	 THEN set_cr.SET_CR6 [of concl: i C KC2]])
apply (tactic "basic_possibility_tac")
apply (simp_all (no_asm_simp) add: symKeys_neq_imp_neq)
done

text{*General facts about message reception*}
lemma Gets_imp_Says:
     "[| Gets B X \<in> set evs; evs \<in> set_cr |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> set_cr |]  ==> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
declare Gets_imp_knows_Spy [THEN parts.Inj, dest]


subsection{*Proofs on keys *}

text{*Spy never sees an agent's private keys! (unless it's bad at start)*}

lemma Spy_see_private_Key [simp]:
     "evs \<in> set_cr
      ==> (Key(invKey (publicKey b A)) \<in> parts(knows Spy evs)) = (A \<in> bad)"
by (erule set_cr.induct, auto)

lemma Spy_analz_private_Key [simp]:
     "evs \<in> set_cr ==>
     (Key(invKey (publicKey b A)) \<in> analz(knows Spy evs)) = (A \<in> bad)"
by auto

declare Spy_see_private_Key [THEN [2] rev_iffD1, dest!]
declare Spy_analz_private_Key [THEN [2] rev_iffD1, dest!]


subsection{*Begin Piero's Theorems on Certificates*}
text{*Trivial in the current model, where certificates by RCA are secure *}

lemma Crypt_valid_pubEK:
     "[| Crypt (priSK RCA) {|Agent C, Key EKi, onlyEnc|}
           \<in> parts (knows Spy evs);
         evs \<in> set_cr |] ==> EKi = pubEK C"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

lemma certificate_valid_pubEK:
    "[| cert C EKi onlyEnc (priSK RCA) \<in> parts (knows Spy evs);
        evs \<in> set_cr |]
     ==> EKi = pubEK C"
apply (unfold cert_def signCert_def)
apply (blast dest!: Crypt_valid_pubEK)
done

lemma Crypt_valid_pubSK:
     "[| Crypt (priSK RCA) {|Agent C, Key SKi, onlySig|}
           \<in> parts (knows Spy evs);
         evs \<in> set_cr |] ==> SKi = pubSK C"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

lemma certificate_valid_pubSK:
    "[| cert C SKi onlySig (priSK RCA) \<in> parts (knows Spy evs);
        evs \<in> set_cr |] ==> SKi = pubSK C"
apply (unfold cert_def signCert_def)
apply (blast dest!: Crypt_valid_pubSK)
done

lemma Gets_certificate_valid:
     "[| Gets A {| X, cert C EKi onlyEnc (priSK RCA),
                      cert C SKi onlySig (priSK RCA)|} \<in> set evs;
         evs \<in> set_cr |]
      ==> EKi = pubEK C & SKi = pubSK C"
by (blast dest: certificate_valid_pubEK certificate_valid_pubSK)

text{*Nobody can have used non-existent keys!*}
lemma new_keys_not_used:
     "[|K \<in> symKeys; Key K \<notin> used evs; evs \<in> set_cr|]
      ==> K \<notin> keysFor (parts (knows Spy evs))"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (frule_tac [8] Gets_certificate_valid)
apply (frule_tac [6] Gets_certificate_valid, simp_all)
apply (force dest!: usedI keysFor_parts_insert) --{*Fake*}
apply (blast,auto)  --{*Others*}
done


subsection{*New versions: as above, but generalized to have the KK argument *}

lemma gen_new_keys_not_used:
     "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> set_cr |]
      ==> Key K \<notin> used evs --> K \<in> symKeys -->
          K \<notin> keysFor (parts (Key`KK Un knows Spy evs))"
by (auto simp add: new_keys_not_used)

lemma gen_new_keys_not_analzd:
     "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> set_cr |]
      ==> K \<notin> keysFor (analz (Key`KK Un knows Spy evs))"
by (blast intro: keysFor_mono [THEN [2] rev_subsetD]
          dest: gen_new_keys_not_used)

lemma analz_Key_image_insert_eq:
     "[|K \<in> symKeys; Key K \<notin> used evs; evs \<in> set_cr |]
      ==> analz (Key ` (insert K KK) \<union> knows Spy evs) =
          insert (Key K) (analz (Key ` KK \<union> knows Spy evs))"
by (simp add: gen_new_keys_not_analzd)

lemma Crypt_parts_imp_used:
     "[|Crypt K X \<in> parts (knows Spy evs);
        K \<in> symKeys; evs \<in> set_cr |] ==> Key K \<in> used evs"
apply (rule ccontr)
apply (force dest: new_keys_not_used Crypt_imp_invKey_keysFor)
done

lemma Crypt_analz_imp_used:
     "[|Crypt K X \<in> analz (knows Spy evs);
        K \<in> symKeys; evs \<in> set_cr |] ==> Key K \<in> used evs"
by (blast intro: Crypt_parts_imp_used)


(*<*) 
subsection{*Messages signed by CA*}

text{*Message @{text SET_CR2}: C can check CA's signature if he has received
     CA's certificate.*}
lemma CA_Says_2_lemma:
     "[| Crypt (priSK (CA i)) (Hash{|Agent C, Nonce NC1|})
           \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
     ==> \<exists>Y. Says (CA i) C {|sign (priSK (CA i)) {|Agent C, Nonce NC1|}, Y|}
                 \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

text{*Ever used?*}
lemma CA_Says_2:
     "[| Crypt (invKey SK) (Hash{|Agent C, Nonce NC1|})
           \<in> parts (knows Spy evs);
         cert (CA i) SK onlySig (priSK RCA) \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y. Says (CA i) C {|sign (priSK (CA i)) {|Agent C, Nonce NC1|}, Y|}
                  \<in> set evs"
by (blast dest!: certificate_valid_pubSK intro!: CA_Says_2_lemma)


text{*Message @{text SET_CR4}: C can check CA's signature if he has received
      CA's certificate.*}
lemma CA_Says_4_lemma:
     "[| Crypt (priSK (CA i)) (Hash{|Agent C, Nonce NC2, Nonce NCA|})
           \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y. Says (CA i) C {|sign (priSK (CA i))
                     {|Agent C, Nonce NC2, Nonce NCA|}, Y|} \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

text{*NEVER USED*}
lemma CA_Says_4:
     "[| Crypt (invKey SK) (Hash{|Agent C, Nonce NC2, Nonce NCA|})
           \<in> parts (knows Spy evs);
         cert (CA i) SK onlySig (priSK RCA) \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y. Says (CA i) C {|sign (priSK (CA i))
                   {|Agent C, Nonce NC2, Nonce NCA|}, Y|} \<in> set evs"
by (blast dest!: certificate_valid_pubSK intro!: CA_Says_4_lemma)


text{*Message @{text SET_CR6}: C can check CA's signature if he has
      received CA's certificate.*}
lemma CA_Says_6_lemma:
     "[| Crypt (priSK (CA i)) 
               (Hash{|Agent C, Nonce NC3, Agent (CA i), Nonce NonceCCA|})
           \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y K. Says (CA i) C (Crypt K {|sign (priSK (CA i))
      {|Agent C, Nonce NC3, Agent (CA i), Nonce NonceCCA|}, Y|}) \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

text{*NEVER USED*}
lemma CA_Says_6:
     "[| Crypt (invKey SK) (Hash{|Agent C, Nonce NC3, Agent (CA i), Nonce NonceCCA|})
           \<in> parts (knows Spy evs);
         cert (CA i) SK onlySig (priSK RCA) \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y K. Says (CA i) C (Crypt K {|sign (priSK (CA i))
                    {|Agent C, Nonce NC3, Agent (CA i), Nonce NonceCCA|}, Y|}) \<in> set evs"
by (blast dest!: certificate_valid_pubSK intro!: CA_Says_6_lemma)
(*>*)


subsection{*Useful lemmas *}

text{*Rewriting rule for private encryption keys.  Analogous rewriting rules
for other keys aren't needed.*}

lemma parts_image_priEK:
     "[|Key (priEK C) \<in> parts (Key`KK Un (knows Spy evs));
        evs \<in> set_cr|] ==> priEK C \<in> KK | C \<in> bad"
by auto

text{*trivial proof because (priEK C) never appears even in (parts evs)*}
lemma analz_image_priEK:
     "evs \<in> set_cr ==>
          (Key (priEK C) \<in> analz (Key`KK Un (knows Spy evs))) =
          (priEK C \<in> KK | C \<in> bad)"
by (blast dest!: parts_image_priEK intro: analz_mono [THEN [2] rev_subsetD])


subsection{*Secrecy of Session Keys *}

subsubsection{*Lemmas about the predicate KeyCryptKey *}

text{*A fresh DK cannot be associated with any other
  (with respect to a given trace). *}
lemma DK_fresh_not_KeyCryptKey:
     "[| Key DK \<notin> used evs; evs \<in> set_cr |] ==> ~ KeyCryptKey DK K evs"
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest: Crypt_analz_imp_used)+
done

text{*A fresh K cannot be associated with any other.  The assumption that
  DK isn't a private encryption key may be an artifact of the particular
  definition of KeyCryptKey.*}
lemma K_fresh_not_KeyCryptKey:
     "[|\<forall>C. DK \<noteq> priEK C; Key K \<notin> used evs|] ==> ~ KeyCryptKey DK K evs"
apply (induct evs)
apply (auto simp add: parts_insert2 split add: event.split)
done


text{*This holds because if (priEK (CA i)) appears in any traffic then it must
  be known to the Spy, by @{term Spy_see_private_Key}*}
lemma cardSK_neq_priEK:
     "[|Key cardSK \<notin> analz (knows Spy evs);
        Key cardSK : parts (knows Spy evs);
        evs \<in> set_cr|] ==> cardSK \<noteq> priEK C"
by blast

lemma not_KeyCryptKey_cardSK [rule_format (no_asm)]:
     "[|cardSK \<notin> symKeys;  \<forall>C. cardSK \<noteq> priEK C;  evs \<in> set_cr|] ==>
      Key cardSK \<notin> analz (knows Spy evs) --> ~ KeyCryptKey cardSK K evs"
by (erule set_cr.induct, analz_mono_contra, auto)

text{*Lemma for message 5: pubSK C is never used to encrypt Keys.*}
lemma pubSK_not_KeyCryptKey [simp]: "~ KeyCryptKey (pubSK C) K evs"
apply (induct_tac "evs")
apply (auto simp add: parts_insert2 split add: event.split)
done

text{*Lemma for message 6: either cardSK is compromised (when we don't care)
  or else cardSK hasn't been used to encrypt K.  Previously we treated
  message 5 in the same way, but the current model assumes that rule
  @{text SET_CR5} is executed only by honest agents.*}
lemma msg6_KeyCryptKey_disj:
     "[|Gets B {|Crypt KC3 {|Agent C, Nonce N, Key KC2, Key cardSK, X|}, Y|}
          \<in> set evs;
        cardSK \<notin> symKeys;  evs \<in> set_cr|]
      ==> Key cardSK \<in> analz (knows Spy evs) |
          (\<forall>K. ~ KeyCryptKey cardSK K evs)"
by (blast dest: not_KeyCryptKey_cardSK intro: cardSK_neq_priEK)

text{*As usual: we express the property as a logical equivalence*}
lemma Key_analz_image_Key_lemma:
     "P --> (Key K \<in> analz (Key`KK Un H)) --> (K \<in> KK | Key K \<in> analz H)
      ==>
      P --> (Key K \<in> analz (Key`KK Un H)) = (K \<in> KK | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

ML
{*
val Gets_certificate_valid = thm "Gets_certificate_valid";

fun valid_certificate_tac i =
    EVERY [ftac Gets_certificate_valid i,
           assume_tac i,
           etac conjE i, REPEAT (hyp_subst_tac i)];
*}

text{*The @{text "(no_asm)"} attribute is essential, since it retains
  the quantifier and allows the simprule's condition to itself be simplified.*}
lemma symKey_compromise [rule_format (no_asm)]:
     "evs \<in> set_cr ==>
      (\<forall>SK KK. SK \<in> symKeys \<longrightarrow> (\<forall>K \<in> KK. ~ KeyCryptKey K SK evs)   -->
               (Key SK \<in> analz (Key`KK Un (knows Spy evs))) =
               (SK \<in> KK | Key SK \<in> analz (knows Spy evs)))"
apply (erule set_cr.induct)
apply (rule_tac [!] allI) +
apply (rule_tac [!] impI [THEN Key_analz_image_Key_lemma, THEN impI])+
apply (tactic{*valid_certificate_tac 8*}) --{*for message 5*}
apply (tactic{*valid_certificate_tac 6*}) --{*for message 5*}
apply (erule_tac [9] msg6_KeyCryptKey_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps analz_knows_absorb
              analz_Key_image_insert_eq notin_image_iff
              K_fresh_not_KeyCryptKey
              DK_fresh_not_KeyCryptKey ball_conj_distrib
              analz_image_priEK disj_simps)
  --{*46 seconds on a 1.8GHz machine*}
apply spy_analz
apply blast  --{*3*}
apply blast  --{*5*}
done

text{*The remaining quantifiers seem to be essential.
  NO NEED to assume the cardholder's OK: bad cardholders don't do anything
  wrong!!*}
lemma symKey_secrecy [rule_format]:
     "[|CA i \<notin> bad;  K \<in> symKeys;  evs \<in> set_cr|]
      ==> \<forall>X c. Says (Cardholder c) (CA i) X \<in> set evs -->
                Key K \<in> parts{X} -->
                Cardholder c \<notin> bad -->
                Key K \<notin> analz (knows Spy evs)"
apply (erule set_cr.induct)
apply (frule_tac [8] Gets_certificate_valid) --{*for message 5*}
apply (frule_tac [6] Gets_certificate_valid) --{*for message 3*}
apply (erule_tac [11] msg6_KeyCryptKey_disj [THEN disjE])
apply (simp_all del: image_insert image_Un imp_disjL
         add: symKey_compromise fresh_notin_analz_knows_Spy
              analz_image_keys_simps analz_knows_absorb
              analz_Key_image_insert_eq notin_image_iff
              K_fresh_not_KeyCryptKey
              DK_fresh_not_KeyCryptKey
              analz_image_priEK)
  --{*13 seconds on a 1.8GHz machine*}
apply spy_analz  --{*Fake*}
apply (auto intro: analz_into_parts [THEN usedI] in_parts_Says_imp_used)
done


subsection{*Primary Goals of Cardholder Registration *}

text{*The cardholder's certificate really was created by the CA, provided the
    CA is uncompromised *}

text{*Lemma concerning the actual signed message digest*}
lemma cert_valid_lemma:
     "[|Crypt (priSK (CA i)) {|Hash {|Nonce N, Pan(pan C)|}, Key cardSK, N1|}
          \<in> parts (knows Spy evs);
        CA i \<notin> bad; evs \<in> set_cr|]
  ==> \<exists>KC2 X Y. Says (CA i) C
                     (Crypt KC2 
                       {|X, certC (pan C) cardSK N onlySig (priSK (CA i)), Y|})
                  \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
apply auto
done

text{*Pre-packaged version for cardholder.  We don't try to confirm the values
  of KC2, X and Y, since they are not important.*}
lemma certificate_valid_cardSK:
    "[|Gets C (Crypt KC2 {|X, certC (pan C) cardSK N onlySig (invKey SKi),
                              cert (CA i) SKi onlySig (priSK RCA)|}) \<in> set evs;
        CA i \<notin> bad; evs \<in> set_cr|]
  ==> \<exists>KC2 X Y. Says (CA i) C
                     (Crypt KC2 
                       {|X, certC (pan C) cardSK N onlySig (priSK (CA i)), Y|})
                   \<in> set evs"
by (force dest!: Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Body]
                    certificate_valid_pubSK cert_valid_lemma)


lemma Hash_imp_parts [rule_format]:
     "evs \<in> set_cr
      ==> Hash{|X, Nonce N|} \<in> parts (knows Spy evs) -->
          Nonce N \<in> parts (knows Spy evs)"
apply (erule set_cr.induct, force)
apply (simp_all (no_asm_simp))
apply (blast intro: parts_mono [THEN [2] rev_subsetD])
done

lemma Hash_imp_parts2 [rule_format]:
     "evs \<in> set_cr
      ==> Hash{|X, Nonce M, Y, Nonce N|} \<in> parts (knows Spy evs) -->
          Nonce M \<in> parts (knows Spy evs) & Nonce N \<in> parts (knows Spy evs)"
apply (erule set_cr.induct, force)
apply (simp_all (no_asm_simp))
apply (blast intro: parts_mono [THEN [2] rev_subsetD])
done


subsection{*Secrecy of Nonces*}

subsubsection{*Lemmas about the predicate KeyCryptNonce *}

text{*A fresh DK cannot be associated with any other
  (with respect to a given trace). *}
lemma DK_fresh_not_KeyCryptNonce:
     "[| DK \<in> symKeys; Key DK \<notin> used evs; evs \<in> set_cr |]
      ==> ~ KeyCryptNonce DK K evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
apply blast
apply blast
apply (auto simp add: DK_fresh_not_KeyCryptKey)
done

text{*A fresh N cannot be associated with any other
      (with respect to a given trace). *}
lemma N_fresh_not_KeyCryptNonce:
     "\<forall>C. DK \<noteq> priEK C ==> Nonce N \<notin> used evs --> ~ KeyCryptNonce DK N evs"
apply (induct_tac "evs")
apply (case_tac [2] "a")
apply (auto simp add: parts_insert2)
done

lemma not_KeyCryptNonce_cardSK [rule_format (no_asm)]:
     "[|cardSK \<notin> symKeys;  \<forall>C. cardSK \<noteq> priEK C;  evs \<in> set_cr|] ==>
      Key cardSK \<notin> analz (knows Spy evs) --> ~ KeyCryptNonce cardSK N evs"
apply (erule set_cr.induct, analz_mono_contra, simp_all)
apply (blast dest: not_KeyCryptKey_cardSK)  --{*6*}
done

subsubsection{*Lemmas for message 5 and 6:
  either cardSK is compromised (when we don't care)
  or else cardSK hasn't been used to encrypt K. *}

text{*Lemma for message 5: pubSK C is never used to encrypt Nonces.*}
lemma pubSK_not_KeyCryptNonce [simp]: "~ KeyCryptNonce (pubSK C) N evs"
apply (induct_tac "evs")
apply (auto simp add: parts_insert2 split add: event.split)
done

text{*Lemma for message 6: either cardSK is compromised (when we don't care)
  or else cardSK hasn't been used to encrypt K.*}
lemma msg6_KeyCryptNonce_disj:
     "[|Gets B {|Crypt KC3 {|Agent C, Nonce N, Key KC2, Key cardSK, X|}, Y|}
          \<in> set evs;
        cardSK \<notin> symKeys;  evs \<in> set_cr|]
      ==> Key cardSK \<in> analz (knows Spy evs) |
          ((\<forall>K. ~ KeyCryptKey cardSK K evs) &
           (\<forall>N. ~ KeyCryptNonce cardSK N evs))"
by (blast dest: not_KeyCryptKey_cardSK not_KeyCryptNonce_cardSK
          intro: cardSK_neq_priEK)


text{*As usual: we express the property as a logical equivalence*}
lemma Nonce_analz_image_Key_lemma:
     "P --> (Nonce N \<in> analz (Key`KK Un H)) --> (Nonce N \<in> analz H)
      ==> P --> (Nonce N \<in> analz (Key`KK Un H)) = (Nonce N \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

text{*The @{text "(no_asm)"} attribute is essential, since it retains
  the quantifier and allows the simprule's condition to itself be simplified.*}
lemma Nonce_compromise [rule_format (no_asm)]:
     "evs \<in> set_cr ==>
      (\<forall>N KK. (\<forall>K \<in> KK. ~ KeyCryptNonce K N evs)   -->
               (Nonce N \<in> analz (Key`KK Un (knows Spy evs))) =
               (Nonce N \<in> analz (knows Spy evs)))"
apply (erule set_cr.induct)
apply (rule_tac [!] allI)+
apply (rule_tac [!] impI [THEN Nonce_analz_image_Key_lemma])+
apply (frule_tac [8] Gets_certificate_valid) --{*for message 5*}
apply (frule_tac [6] Gets_certificate_valid) --{*for message 3*}
apply (frule_tac [11] msg6_KeyCryptNonce_disj)
apply (erule_tac [13] disjE)
apply (simp_all del: image_insert image_Un
         add: symKey_compromise
              analz_image_keys_simps analz_knows_absorb
              analz_Key_image_insert_eq notin_image_iff
              N_fresh_not_KeyCryptNonce
              DK_fresh_not_KeyCryptNonce K_fresh_not_KeyCryptKey
              ball_conj_distrib analz_image_priEK)
  --{*71 seconds on a 1.8GHz machine*}
apply spy_analz  --{*Fake*}
apply blast  --{*3*}
apply blast  --{*5*}
txt{*Message 6*}
apply (force del: allE ballE impCE simp add: symKey_compromise)
  --{*cardSK compromised*}
txt{*Simplify again--necessary because the previous simplification introduces
  some logical connectives*}
apply (force del: allE ballE impCE
          simp del: image_insert image_Un imp_disjL
          simp add: analz_image_keys_simps symKey_compromise)
done


subsection{*Secrecy of CardSecret: the Cardholder's secret*}

lemma NC2_not_CardSecret:
     "[|Crypt EKj {|Key K, Pan p, Hash {|Agent D, Nonce N|}|}
          \<in> parts (knows Spy evs);
        Key K \<notin> analz (knows Spy evs);
        Nonce N \<notin> analz (knows Spy evs);
       evs \<in> set_cr|]
      ==> Crypt EKi {|Key K', Pan p', Nonce N|} \<notin> parts (knows Spy evs)"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct, analz_mono_contra, simp_all)
apply (blast dest: Hash_imp_parts)+
done

lemma KC2_secure_lemma [rule_format]:
     "[|U = Crypt KC3 {|Agent C, Nonce N, Key KC2, X|};
        U \<in> parts (knows Spy evs);
        evs \<in> set_cr|]
  ==> Nonce N \<notin> analz (knows Spy evs) -->
      (\<exists>k i W. Says (Cardholder k) (CA i) {|U,W|} \<in> set evs & 
               Cardholder k \<notin> bad & CA i \<notin> bad)"
apply (erule_tac P = "U \<in> ?H" in rev_mp)
apply (erule set_cr.induct)
apply (tactic{*valid_certificate_tac 8*})  --{*for message 5*}
apply (simp_all del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps analz_knows_absorb
              analz_knows_absorb2 notin_image_iff)
  --{*19 seconds on a 1.8GHz machine*}
apply (simp_all (no_asm_simp)) --{*leaves 4 subgoals*}
apply (blast intro!: analz_insertI)+
done

lemma KC2_secrecy:
     "[|Gets B {|Crypt K {|Agent C, Nonce N, Key KC2, X|}, Y|} \<in> set evs;
        Nonce N \<notin> analz (knows Spy evs);  KC2 \<in> symKeys;
        evs \<in> set_cr|]
       ==> Key KC2 \<notin> analz (knows Spy evs)"
by (force dest!: refl [THEN KC2_secure_lemma] symKey_secrecy)


text{*Inductive version*}
lemma CardSecret_secrecy_lemma [rule_format]:
     "[|CA i \<notin> bad;  evs \<in> set_cr|]
      ==> Key K \<notin> analz (knows Spy evs) -->
          Crypt (pubEK (CA i)) {|Key K, Pan p, Nonce CardSecret|}
             \<in> parts (knows Spy evs) -->
          Nonce CardSecret \<notin> analz (knows Spy evs)"
apply (erule set_cr.induct, analz_mono_contra)
apply (tactic{*valid_certificate_tac 8*}) --{*for message 5*}
apply (tactic{*valid_certificate_tac 6*}) --{*for message 5*}
apply (frule_tac [9] msg6_KeyCryptNonce_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps analz_knows_absorb
              analz_Key_image_insert_eq notin_image_iff
              EXHcrypt_def Crypt_notin_image_Key
              N_fresh_not_KeyCryptNonce DK_fresh_not_KeyCryptNonce
              ball_conj_distrib Nonce_compromise symKey_compromise
              analz_image_priEK)
  --{*12 seconds on a 1.8GHz machine*}
apply spy_analz  --{*Fake*}
apply (simp_all (no_asm_simp))
apply blast  --{*1*}
apply (blast dest!: Gets_imp_knows_Spy [THEN analz.Inj])  --{*2*}
apply blast  --{*3*}
apply (blast dest: NC2_not_CardSecret Gets_imp_knows_Spy [THEN analz.Inj] analz_symKeys_Decrypt)  --{*4*}
apply blast  --{*5*}
apply (blast dest: KC2_secrecy)+  --{*Message 6: two cases*}
done


text{*Packaged version for cardholder*}
lemma CardSecret_secrecy:
     "[|Cardholder k \<notin> bad;  CA i \<notin> bad;
        Says (Cardholder k) (CA i)
           {|X, Crypt EKi {|Key KC3, Pan p, Nonce CardSecret|}|} \<in> set evs;
        Gets A {|Z, cert (CA i) EKi onlyEnc (priSK RCA),
                    cert (CA i) SKi onlySig (priSK RCA)|} \<in> set evs;
        KC3 \<in> symKeys;  evs \<in> set_cr|]
      ==> Nonce CardSecret \<notin> analz (knows Spy evs)"
apply (frule Gets_certificate_valid, assumption)
apply (subgoal_tac "Key KC3 \<notin> analz (knows Spy evs) ")
apply (blast dest: CardSecret_secrecy_lemma)
apply (rule symKey_secrecy)
apply (auto simp add: parts_insert2)
done


subsection{*Secrecy of NonceCCA [the CA's secret] *}

lemma NC2_not_NonceCCA:
     "[|Hash {|Agent C', Nonce N', Agent C, Nonce N|}
          \<in> parts (knows Spy evs);
        Nonce N \<notin> analz (knows Spy evs);
       evs \<in> set_cr|]
      ==> Crypt KC1 {|{|Agent B, Nonce N|}, Hash p|} \<notin> parts (knows Spy evs)"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct, analz_mono_contra, simp_all)
apply (blast dest: Hash_imp_parts2)+
done


text{*Inductive version*}
lemma NonceCCA_secrecy_lemma [rule_format]:
     "[|CA i \<notin> bad;  evs \<in> set_cr|]
      ==> Key K \<notin> analz (knows Spy evs) -->
          Crypt K
            {|sign (priSK (CA i))
                   {|Agent C, Nonce N, Agent(CA i), Nonce NonceCCA|},
              X, Y|}
             \<in> parts (knows Spy evs) -->
          Nonce NonceCCA \<notin> analz (knows Spy evs)"
apply (erule set_cr.induct, analz_mono_contra)
apply (tactic{*valid_certificate_tac 8*}) --{*for message 5*}
apply (tactic{*valid_certificate_tac 6*}) --{*for message 5*}
apply (frule_tac [9] msg6_KeyCryptNonce_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps analz_knows_absorb sign_def
              analz_Key_image_insert_eq notin_image_iff
              EXHcrypt_def Crypt_notin_image_Key
              N_fresh_not_KeyCryptNonce DK_fresh_not_KeyCryptNonce
              ball_conj_distrib Nonce_compromise symKey_compromise
              analz_image_priEK)
  --{*15 seconds on a 1.8GHz machine*}
apply spy_analz  --{*Fake*}
apply blast  --{*1*}
apply (blast dest!: Gets_imp_knows_Spy [THEN analz.Inj])  --{*2*}
apply blast  --{*3*}
apply (blast dest: NC2_not_NonceCCA)  --{*4*}
apply blast  --{*5*}
apply (blast dest: KC2_secrecy)+  --{*Message 6: two cases*}
done


text{*Packaged version for cardholder*}
lemma NonceCCA_secrecy:
     "[|Cardholder k \<notin> bad;  CA i \<notin> bad;
        Gets (Cardholder k)
           (Crypt KC2
            {|sign (priSK (CA i)) {|Agent C, Nonce N, Agent(CA i), Nonce NonceCCA|},
              X, Y|}) \<in> set evs;
        Says (Cardholder k) (CA i)
           {|Crypt KC3 {|Agent C, Nonce NC3, Key KC2, X'|}, Y'|} \<in> set evs;
        Gets A {|Z, cert (CA i) EKi onlyEnc (priSK RCA),
                    cert (CA i) SKi onlySig (priSK RCA)|} \<in> set evs;
        KC2 \<in> symKeys;  evs \<in> set_cr|]
      ==> Nonce NonceCCA \<notin> analz (knows Spy evs)"
apply (frule Gets_certificate_valid, assumption)
apply (subgoal_tac "Key KC2 \<notin> analz (knows Spy evs) ")
apply (blast dest: NonceCCA_secrecy_lemma)
apply (rule symKey_secrecy)
apply (auto simp add: parts_insert2)
done

text{*We don't bother to prove guarantees for the CA.  He doesn't care about
  the PANSecret: it isn't his credit card!*}


subsection{*Rewriting Rule for PANs*}

text{*Lemma for message 6: either cardSK isn't a CA's private encryption key,
  or if it is then (because it appears in traffic) that CA is bad,
  and so the Spy knows that key already.  Either way, we can simplify
  the expression @{term "analz (insert (Key cardSK) X)"}.*}
lemma msg6_cardSK_disj:
     "[|Gets A {|Crypt K {|c, n, k', Key cardSK, X|}, Y|}
          \<in> set evs;  evs \<in> set_cr |]
      ==> cardSK \<notin> range(invKey o pubEK o CA) | Key cardSK \<in> knows Spy evs"
by auto

lemma analz_image_pan_lemma:
     "(Pan P \<in> analz (Key`nE Un H)) --> (Pan P \<in> analz H)  ==>
      (Pan P \<in> analz (Key`nE Un H)) =   (Pan P \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

lemma analz_image_pan [rule_format]:
     "evs \<in> set_cr ==>
       \<forall>KK. KK <= - invKey ` pubEK ` range CA -->
            (Pan P \<in> analz (Key`KK Un (knows Spy evs))) =
            (Pan P \<in> analz (knows Spy evs))"
apply (erule set_cr.induct)
apply (rule_tac [!] allI impI)+
apply (rule_tac [!] analz_image_pan_lemma)
apply (tactic{*valid_certificate_tac 8*}) --{*for message 5*}
apply (tactic{*valid_certificate_tac 6*}) --{*for message 5*}
apply (erule_tac [9] msg6_cardSK_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un
         add: analz_image_keys_simps disjoint_image_iff
              notin_image_iff analz_image_priEK)
  --{*33 seconds on a 1.8GHz machine*}
apply spy_analz
apply (simp add: insert_absorb)  --{*6*}
done

lemma analz_insert_pan:
     "[| evs \<in> set_cr;  K \<notin> invKey ` pubEK ` range CA |] ==>
          (Pan P \<in> analz (insert (Key K) (knows Spy evs))) =
          (Pan P \<in> analz (knows Spy evs))"
by (simp del: image_insert image_Un
         add: analz_image_keys_simps analz_image_pan)


text{*Confidentiality of the PAN\@.  Maybe we could combine the statements of
  this theorem with @{term analz_image_pan}, requiring a single induction but
  a much more difficult proof.*}
lemma pan_confidentiality:
     "[| Pan (pan C) \<in> analz(knows Spy evs); C \<noteq>Spy; evs :set_cr|]
    ==> \<exists>i X K HN.
        Says C (CA i) {|X, Crypt (pubEK (CA i)) {|Key K, Pan (pan C), HN|} |}
           \<in> set evs
      & (CA i) \<in> bad"
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (tactic{*valid_certificate_tac 8*}) --{*for message 5*}
apply (tactic{*valid_certificate_tac 6*}) --{*for message 5*}
apply (erule_tac [9] msg6_cardSK_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un
         add: analz_image_keys_simps analz_insert_pan analz_image_pan
              notin_image_iff analz_image_priEK)
  --{*18 seconds on a 1.8GHz machine*}
apply spy_analz  --{*fake*}
apply blast  --{*3*}
apply blast  --{*5*}
apply (simp (no_asm_simp) add: insert_absorb)  --{*6*}
done


subsection{*Unicity*}

lemma CR6_Says_imp_Notes:
     "[|Says (CA i) C (Crypt KC2
          {|sign (priSK (CA i)) {|Agent C, Nonce NC3, Agent (CA i), Nonce Y|},
            certC (pan C) cardSK X onlySig (priSK (CA i)),
            cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|})  \<in> set evs;
        evs \<in> set_cr |]
      ==> Notes (CA i) (Key cardSK) \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
done

text{*Unicity of cardSK: it uniquely identifies the other components.  
      This holds because a CA accepts a cardSK at most once.*}
lemma cardholder_key_unicity:
     "[|Says (CA i) C (Crypt KC2
          {|sign (priSK (CA i)) {|Agent C, Nonce NC3, Agent (CA i), Nonce Y|},
            certC (pan C) cardSK X onlySig (priSK (CA i)),
            cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|})
          \<in> set evs;
        Says (CA i) C' (Crypt KC2'
          {|sign (priSK (CA i)) {|Agent C', Nonce NC3', Agent (CA i), Nonce Y'|},
            certC (pan C') cardSK X' onlySig (priSK (CA i)),
            cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)|})
          \<in> set evs;
        evs \<in> set_cr |] ==> C=C' & NC3=NC3' & X=X' & KC2=KC2' & Y=Y'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest!: CR6_Says_imp_Notes)
done


(*<*)
text{*UNUSED unicity result*}
lemma unique_KC1:
     "[|Says C B {|Crypt KC1 X, Crypt EK {|Key KC1, Y|}|}
          \<in> set evs;
        Says C B' {|Crypt KC1 X', Crypt EK' {|Key KC1, Y'|}|}
          \<in> set evs;
        C \<notin> bad;  evs \<in> set_cr|] ==> B'=B & Y'=Y"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

text{*UNUSED unicity result*}
lemma unique_KC2:
     "[|Says C B {|Crypt K {|Agent C, nn, Key KC2, X|}, Y|} \<in> set evs;
        Says C B' {|Crypt K' {|Agent C, nn', Key KC2, X'|}, Y'|} \<in> set evs;
        C \<notin> bad;  evs \<in> set_cr|] ==> B'=B & X'=X"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done
(*>*)


text{*Cannot show cardSK to be secret because it isn't assumed to be fresh
  it could be a previously compromised cardSK [e.g. involving a bad CA]*}


end
