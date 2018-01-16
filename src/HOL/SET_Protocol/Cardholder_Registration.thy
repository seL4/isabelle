(*  Title:      HOL/SET_Protocol/Cardholder_Registration.thy
    Author:     Giampaolo Bella
    Author:     Fabio Massacci
    Author:     Lawrence C Paulson
    Author:     Piero Tramontano
*)

section\<open>The SET Cardholder Registration Protocol\<close>

theory Cardholder_Registration
imports Public_SET
begin

text\<open>Note: nonces seem to consist of 20 bytes.  That includes both freshness
challenges (Chall-EE, etc.) and important secrets (CardSecret, PANsecret)
\<close>

text\<open>Simplifications involving \<open>analz_image_keys_simps\<close> appear to
have become much slower. The cause is unclear. However, there is a big blow-up
and the rewriting is very sensitive to the set of rewrite rules given.\<close>

subsection\<open>Predicate Formalizing the Encryption Association between Keys\<close>

primrec KeyCryptKey :: "[key, key, event list] => bool"
where
  KeyCryptKey_Nil:
    "KeyCryptKey DK K [] = False"
| KeyCryptKey_Cons:
      \<comment> \<open>Says is the only important case.
        1st case: CR5, where KC3 encrypts KC2.
        2nd case: any use of priEK C.
        Revision 1.12 has a more complicated version with separate treatment of
          the dependency of KC1, KC2 and KC3 on priEK (CA i.)  Not needed since
          priEK C is never sent (and so can't be lost except at the start).\<close>
    "KeyCryptKey DK K (ev # evs) =
     (KeyCryptKey DK K evs |
      (case ev of
        Says A B Z =>
         ((\<exists>N X Y. A \<noteq> Spy &
                 DK \<in> symKeys &
                 Z = \<lbrace>Crypt DK \<lbrace>Agent A, Nonce N, Key K, X\<rbrace>, Y\<rbrace>) |
          (\<exists>C. DK = priEK C))
      | Gets A' X => False
      | Notes A' X => False))"


subsection\<open>Predicate formalizing the association between keys and nonces\<close>

primrec KeyCryptNonce :: "[key, key, event list] => bool"
where
  KeyCryptNonce_Nil:
    "KeyCryptNonce EK K [] = False"
| KeyCryptNonce_Cons:
  \<comment> \<open>Says is the only important case.
    1st case: CR3, where KC1 encrypts NC2 (distinct from CR5 due to EXH);
    2nd case: CR5, where KC3 encrypts NC3;
    3rd case: CR6, where KC2 encrypts NC3;
    4th case: CR6, where KC2 encrypts NonceCCA;
    5th case: any use of @{term "priEK C"} (including CardSecret).
    NB the only Nonces we need to keep secret are CardSecret and NonceCCA.
    But we can't prove \<open>Nonce_compromise\<close> unless the relation covers ALL
        nonces that the protocol keeps secret.\<close>
  "KeyCryptNonce DK N (ev # evs) =
   (KeyCryptNonce DK N evs |
    (case ev of
      Says A B Z =>
       A \<noteq> Spy &
       ((\<exists>X Y. DK \<in> symKeys &
               Z = (EXHcrypt DK X \<lbrace>Agent A, Nonce N\<rbrace> Y)) |
        (\<exists>X Y. DK \<in> symKeys &
               Z = \<lbrace>Crypt DK \<lbrace>Agent A, Nonce N, X\<rbrace>, Y\<rbrace>) |
        (\<exists>K i X Y.
          K \<in> symKeys &
          Z = Crypt K \<lbrace>sign (priSK (CA i)) \<lbrace>Agent B, Nonce N, X\<rbrace>, Y\<rbrace> &
          (DK=K | KeyCryptKey DK K evs)) |
        (\<exists>K C NC3 Y.
          K \<in> symKeys &
          Z = Crypt K
                \<lbrace>sign (priSK C) \<lbrace>Agent B, Nonce NC3, Agent C, Nonce N\<rbrace>,
                  Y\<rbrace> &
          (DK=K | KeyCryptKey DK K evs)) |
        (\<exists>C. DK = priEK C))
    | Gets A' X => False
    | Notes A' X => False))"


subsection\<open>Formal protocol definition\<close>

inductive_set
  set_cr :: "event list set"
where

  Nil:    \<comment> \<open>Initial trace is empty\<close>
          "[] \<in> set_cr"

| Fake:    \<comment> \<open>The spy MAY say anything he CAN say.\<close>
           "[| evsf \<in> set_cr; X \<in> synth (analz (knows Spy evsf)) |]
            ==> Says Spy B X  # evsf \<in> set_cr"

| Reception: \<comment> \<open>If A sends a message X to B, then B might receive it\<close>
             "[| evsr \<in> set_cr; Says A B X \<in> set evsr |]
              ==> Gets B X  # evsr \<in> set_cr"

| SET_CR1: \<comment> \<open>CardCInitReq: C initiates a run, sending a nonce to CCA\<close>
             "[| evs1 \<in> set_cr;  C = Cardholder k;  Nonce NC1 \<notin> used evs1 |]
              ==> Says C (CA i) \<lbrace>Agent C, Nonce NC1\<rbrace> # evs1 \<in> set_cr"

| SET_CR2: \<comment> \<open>CardCInitRes: CA responds sending NC1 and its certificates\<close>
             "[| evs2 \<in> set_cr;
                 Gets (CA i) \<lbrace>Agent C, Nonce NC1\<rbrace> \<in> set evs2 |]
              ==> Says (CA i) C
                       \<lbrace>sign (priSK (CA i)) \<lbrace>Agent C, Nonce NC1\<rbrace>,
                         cert (CA i) (pubEK (CA i)) onlyEnc (priSK RCA),
                         cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace>
                    # evs2 \<in> set_cr"

| SET_CR3:
   \<comment> \<open>RegFormReq: C sends his PAN and a new nonce to CA.
   C verifies that
    - nonce received is the same as that sent;
    - certificates are signed by RCA;
    - certificates are an encryption certificate (flag is onlyEnc) and a
      signature certificate (flag is onlySig);
    - certificates pertain to the CA that C contacted (this is done by
      checking the signature).
   C generates a fresh symmetric key KC1.
   The point of encrypting @{term "\<lbrace>Agent C, Nonce NC2, Hash (Pan(pan C))\<rbrace>"}
   is not clear.\<close>
"[| evs3 \<in> set_cr;  C = Cardholder k;
    Nonce NC2 \<notin> used evs3;
    Key KC1 \<notin> used evs3; KC1 \<in> symKeys;
    Gets C \<lbrace>sign (invKey SKi) \<lbrace>Agent X, Nonce NC1\<rbrace>,
             cert (CA i) EKi onlyEnc (priSK RCA),
             cert (CA i) SKi onlySig (priSK RCA)\<rbrace>
       \<in> set evs3;
    Says C (CA i) \<lbrace>Agent C, Nonce NC1\<rbrace> \<in> set evs3|]
 ==> Says C (CA i) (EXHcrypt KC1 EKi \<lbrace>Agent C, Nonce NC2\<rbrace> (Pan(pan C)))
       # Notes C \<lbrace>Key KC1, Agent (CA i)\<rbrace>
       # evs3 \<in> set_cr"

| SET_CR4:
    \<comment> \<open>RegFormRes:
    CA responds sending NC2 back with a new nonce NCA, after checking that
     - the digital envelope is correctly encrypted by @{term "pubEK (CA i)"}
     - the entire message is encrypted with the same key found inside the
       envelope (here, KC1)\<close>
"[| evs4 \<in> set_cr;
    Nonce NCA \<notin> used evs4;  KC1 \<in> symKeys;
    Gets (CA i) (EXHcrypt KC1 EKi \<lbrace>Agent C, Nonce NC2\<rbrace> (Pan(pan X)))
       \<in> set evs4 |]
  ==> Says (CA i) C
          \<lbrace>sign (priSK (CA i)) \<lbrace>Agent C, Nonce NC2, Nonce NCA\<rbrace>,
            cert (CA i) (pubEK (CA i)) onlyEnc (priSK RCA),
            cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace>
       # evs4 \<in> set_cr"

| SET_CR5:
   \<comment> \<open>CertReq: C sends his PAN, a new nonce, its proposed public signature key
       and its half of the secret value to CA.
       We now assume that C has a fixed key pair, and he submits (pubSK C).
       The protocol does not require this key to be fresh.
       The encryption below is actually EncX.\<close>
"[| evs5 \<in> set_cr;  C = Cardholder k;
    Nonce NC3 \<notin> used evs5;  Nonce CardSecret \<notin> used evs5; NC3\<noteq>CardSecret;
    Key KC2 \<notin> used evs5; KC2 \<in> symKeys;
    Key KC3 \<notin> used evs5; KC3 \<in> symKeys; KC2\<noteq>KC3;
    Gets C \<lbrace>sign (invKey SKi) \<lbrace>Agent C, Nonce NC2, Nonce NCA\<rbrace>,
             cert (CA i) EKi onlyEnc (priSK RCA),
             cert (CA i) SKi onlySig (priSK RCA) \<rbrace>
        \<in> set evs5;
    Says C (CA i) (EXHcrypt KC1 EKi \<lbrace>Agent C, Nonce NC2\<rbrace> (Pan(pan C)))
         \<in> set evs5 |]
==> Says C (CA i)
         \<lbrace>Crypt KC3
             \<lbrace>Agent C, Nonce NC3, Key KC2, Key (pubSK C),
               Crypt (priSK C)
                 (Hash \<lbrace>Agent C, Nonce NC3, Key KC2,
                         Key (pubSK C), Pan (pan C), Nonce CardSecret\<rbrace>)\<rbrace>,
           Crypt EKi \<lbrace>Key KC3, Pan (pan C), Nonce CardSecret\<rbrace> \<rbrace>
    # Notes C \<lbrace>Key KC2, Agent (CA i)\<rbrace>
    # Notes C \<lbrace>Key KC3, Agent (CA i)\<rbrace>
    # evs5 \<in> set_cr"


  \<comment> \<open>CertRes: CA responds sending NC3 back with its half of the secret value,
   its signature certificate and the new cardholder signature
   certificate.  CA checks to have never certified the key proposed by C.
   NOTE: In Merchant Registration, the corresponding rule (4)
   uses the "sign" primitive. The encryption below is actually @{term EncK}, 
   which is just @{term "Crypt K (sign SK X)"}.\<close>

| SET_CR6:
"[| evs6 \<in> set_cr;
    Nonce NonceCCA \<notin> used evs6;
    KC2 \<in> symKeys;  KC3 \<in> symKeys;  cardSK \<notin> symKeys;
    Notes (CA i) (Key cardSK) \<notin> set evs6;
    Gets (CA i)
      \<lbrace>Crypt KC3 \<lbrace>Agent C, Nonce NC3, Key KC2, Key cardSK,
                    Crypt (invKey cardSK)
                      (Hash \<lbrace>Agent C, Nonce NC3, Key KC2,
                              Key cardSK, Pan (pan C), Nonce CardSecret\<rbrace>)\<rbrace>,
        Crypt (pubEK (CA i)) \<lbrace>Key KC3, Pan (pan C), Nonce CardSecret\<rbrace> \<rbrace>
      \<in> set evs6 |]
==> Says (CA i) C
         (Crypt KC2
          \<lbrace>sign (priSK (CA i))
                 \<lbrace>Agent C, Nonce NC3, Agent(CA i), Nonce NonceCCA\<rbrace>,
            certC (pan C) cardSK (XOR(CardSecret,NonceCCA)) onlySig (priSK (CA i)),
            cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace>)
      # Notes (CA i) (Key cardSK)
      # evs6 \<in> set_cr"


declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

text\<open>A "possibility property": there are traces that reach the end.
      An unconstrained proof with many subgoals.\<close>

lemma Says_to_Gets:
     "Says A B X # evs \<in> set_cr ==> Gets B X # Says A B X # evs \<in> set_cr"
by (rule set_cr.Reception, auto)

text\<open>The many nonces and keys generated, some simultaneously, force us to
  introduce them explicitly as shown below.\<close>
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
             \<lbrace>sign (priSK (CA i))
                    \<lbrace>Agent C, Nonce NC3, Agent(CA i), Nonce NonceCCA\<rbrace>,
               certC (pan C) (pubSK (Cardholder k)) (XOR(CardSecret,NonceCCA))
                     onlySig (priSK (CA i)),
               cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace>)
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
apply basic_possibility
apply (simp_all (no_asm_simp) add: symKeys_neq_imp_neq)
done

text\<open>General facts about message reception\<close>
lemma Gets_imp_Says:
     "[| Gets B X \<in> set evs; evs \<in> set_cr |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> set_cr |]  ==> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
declare Gets_imp_knows_Spy [THEN parts.Inj, dest]


subsection\<open>Proofs on keys\<close>

text\<open>Spy never sees an agent's private keys! (unless it's bad at start)\<close>

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


subsection\<open>Begin Piero's Theorems on Certificates\<close>
text\<open>Trivial in the current model, where certificates by RCA are secure\<close>

lemma Crypt_valid_pubEK:
     "[| Crypt (priSK RCA) \<lbrace>Agent C, Key EKi, onlyEnc\<rbrace>
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
     "[| Crypt (priSK RCA) \<lbrace>Agent C, Key SKi, onlySig\<rbrace>
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
     "[| Gets A \<lbrace> X, cert C EKi onlyEnc (priSK RCA),
                      cert C SKi onlySig (priSK RCA)\<rbrace> \<in> set evs;
         evs \<in> set_cr |]
      ==> EKi = pubEK C & SKi = pubSK C"
by (blast dest: certificate_valid_pubEK certificate_valid_pubSK)

text\<open>Nobody can have used non-existent keys!\<close>
lemma new_keys_not_used:
     "[|K \<in> symKeys; Key K \<notin> used evs; evs \<in> set_cr|]
      ==> K \<notin> keysFor (parts (knows Spy evs))"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (frule_tac [8] Gets_certificate_valid)
apply (frule_tac [6] Gets_certificate_valid, simp_all)
apply (force dest!: usedI keysFor_parts_insert) \<comment> \<open>Fake\<close>
apply (blast,auto)  \<comment> \<open>Others\<close>
done


subsection\<open>New versions: as above, but generalized to have the KK argument\<close>

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
subsection\<open>Messages signed by CA\<close>

text\<open>Message \<open>SET_CR2\<close>: C can check CA's signature if he has received
     CA's certificate.\<close>
lemma CA_Says_2_lemma:
     "[| Crypt (priSK (CA i)) (Hash\<lbrace>Agent C, Nonce NC1\<rbrace>)
           \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
     ==> \<exists>Y. Says (CA i) C \<lbrace>sign (priSK (CA i)) \<lbrace>Agent C, Nonce NC1\<rbrace>, Y\<rbrace>
                 \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

text\<open>Ever used?\<close>
lemma CA_Says_2:
     "[| Crypt (invKey SK) (Hash\<lbrace>Agent C, Nonce NC1\<rbrace>)
           \<in> parts (knows Spy evs);
         cert (CA i) SK onlySig (priSK RCA) \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y. Says (CA i) C \<lbrace>sign (priSK (CA i)) \<lbrace>Agent C, Nonce NC1\<rbrace>, Y\<rbrace>
                  \<in> set evs"
by (blast dest!: certificate_valid_pubSK intro!: CA_Says_2_lemma)


text\<open>Message \<open>SET_CR4\<close>: C can check CA's signature if he has received
      CA's certificate.\<close>
lemma CA_Says_4_lemma:
     "[| Crypt (priSK (CA i)) (Hash\<lbrace>Agent C, Nonce NC2, Nonce NCA\<rbrace>)
           \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y. Says (CA i) C \<lbrace>sign (priSK (CA i))
                     \<lbrace>Agent C, Nonce NC2, Nonce NCA\<rbrace>, Y\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

text\<open>NEVER USED\<close>
lemma CA_Says_4:
     "[| Crypt (invKey SK) (Hash\<lbrace>Agent C, Nonce NC2, Nonce NCA\<rbrace>)
           \<in> parts (knows Spy evs);
         cert (CA i) SK onlySig (priSK RCA) \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y. Says (CA i) C \<lbrace>sign (priSK (CA i))
                   \<lbrace>Agent C, Nonce NC2, Nonce NCA\<rbrace>, Y\<rbrace> \<in> set evs"
by (blast dest!: certificate_valid_pubSK intro!: CA_Says_4_lemma)


text\<open>Message \<open>SET_CR6\<close>: C can check CA's signature if he has
      received CA's certificate.\<close>
lemma CA_Says_6_lemma:
     "[| Crypt (priSK (CA i)) 
               (Hash\<lbrace>Agent C, Nonce NC3, Agent (CA i), Nonce NonceCCA\<rbrace>)
           \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y K. Says (CA i) C (Crypt K \<lbrace>sign (priSK (CA i))
      \<lbrace>Agent C, Nonce NC3, Agent (CA i), Nonce NonceCCA\<rbrace>, Y\<rbrace>) \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

text\<open>NEVER USED\<close>
lemma CA_Says_6:
     "[| Crypt (invKey SK) (Hash\<lbrace>Agent C, Nonce NC3, Agent (CA i), Nonce NonceCCA\<rbrace>)
           \<in> parts (knows Spy evs);
         cert (CA i) SK onlySig (priSK RCA) \<in> parts (knows Spy evs);
         evs \<in> set_cr; (CA i) \<notin> bad |]
      ==> \<exists>Y K. Says (CA i) C (Crypt K \<lbrace>sign (priSK (CA i))
                    \<lbrace>Agent C, Nonce NC3, Agent (CA i), Nonce NonceCCA\<rbrace>, Y\<rbrace>) \<in> set evs"
by (blast dest!: certificate_valid_pubSK intro!: CA_Says_6_lemma)
(*>*)


subsection\<open>Useful lemmas\<close>

text\<open>Rewriting rule for private encryption keys.  Analogous rewriting rules
for other keys aren't needed.\<close>

lemma parts_image_priEK:
     "[|Key (priEK C) \<in> parts (Key`KK Un (knows Spy evs));
        evs \<in> set_cr|] ==> priEK C \<in> KK | C \<in> bad"
by auto

text\<open>trivial proof because (priEK C) never appears even in (parts evs)\<close>
lemma analz_image_priEK:
     "evs \<in> set_cr ==>
          (Key (priEK C) \<in> analz (Key`KK Un (knows Spy evs))) =
          (priEK C \<in> KK | C \<in> bad)"
by (blast dest!: parts_image_priEK intro: analz_mono [THEN [2] rev_subsetD])


subsection\<open>Secrecy of Session Keys\<close>

subsubsection\<open>Lemmas about the predicate KeyCryptKey\<close>

text\<open>A fresh DK cannot be associated with any other
  (with respect to a given trace).\<close>
lemma DK_fresh_not_KeyCryptKey:
     "[| Key DK \<notin> used evs; evs \<in> set_cr |] ==> ~ KeyCryptKey DK K evs"
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest: Crypt_analz_imp_used)+
done

text\<open>A fresh K cannot be associated with any other.  The assumption that
  DK isn't a private encryption key may be an artifact of the particular
  definition of KeyCryptKey.\<close>
lemma K_fresh_not_KeyCryptKey:
     "[|\<forall>C. DK \<noteq> priEK C; Key K \<notin> used evs|] ==> ~ KeyCryptKey DK K evs"
apply (induct evs)
apply (auto simp add: parts_insert2 split: event.split)
done


text\<open>This holds because if (priEK (CA i)) appears in any traffic then it must
  be known to the Spy, by @{term Spy_see_private_Key}\<close>
lemma cardSK_neq_priEK:
     "[|Key cardSK \<notin> analz (knows Spy evs);
        Key cardSK : parts (knows Spy evs);
        evs \<in> set_cr|] ==> cardSK \<noteq> priEK C"
by blast

lemma not_KeyCryptKey_cardSK [rule_format (no_asm)]:
     "[|cardSK \<notin> symKeys;  \<forall>C. cardSK \<noteq> priEK C;  evs \<in> set_cr|] ==>
      Key cardSK \<notin> analz (knows Spy evs) --> ~ KeyCryptKey cardSK K evs"
by (erule set_cr.induct, analz_mono_contra, auto)

text\<open>Lemma for message 5: pubSK C is never used to encrypt Keys.\<close>
lemma pubSK_not_KeyCryptKey [simp]: "~ KeyCryptKey (pubSK C) K evs"
apply (induct_tac "evs")
apply (auto simp add: parts_insert2 split: event.split)
done

text\<open>Lemma for message 6: either cardSK is compromised (when we don't care)
  or else cardSK hasn't been used to encrypt K.  Previously we treated
  message 5 in the same way, but the current model assumes that rule
  \<open>SET_CR5\<close> is executed only by honest agents.\<close>
lemma msg6_KeyCryptKey_disj:
     "[|Gets B \<lbrace>Crypt KC3 \<lbrace>Agent C, Nonce N, Key KC2, Key cardSK, X\<rbrace>, Y\<rbrace>
          \<in> set evs;
        cardSK \<notin> symKeys;  evs \<in> set_cr|]
      ==> Key cardSK \<in> analz (knows Spy evs) |
          (\<forall>K. ~ KeyCryptKey cardSK K evs)"
by (blast dest: not_KeyCryptKey_cardSK intro: cardSK_neq_priEK)

text\<open>As usual: we express the property as a logical equivalence\<close>
lemma Key_analz_image_Key_lemma:
     "P --> (Key K \<in> analz (Key`KK Un H)) --> (K \<in> KK | Key K \<in> analz H)
      ==>
      P --> (Key K \<in> analz (Key`KK Un H)) = (K \<in> KK | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

method_setup valid_certificate_tac = \<open>
  Args.goal_spec >> (fn quant => fn ctxt => SIMPLE_METHOD'' quant
    (fn i =>
      EVERY [forward_tac ctxt @{thms Gets_certificate_valid} i,
             assume_tac ctxt i,
             eresolve_tac ctxt [conjE] i, REPEAT (hyp_subst_tac ctxt i)]))
\<close>

text\<open>The \<open>(no_asm)\<close> attribute is essential, since it retains
  the quantifier and allows the simprule's condition to itself be simplified.\<close>
lemma symKey_compromise [rule_format (no_asm)]:
     "evs \<in> set_cr ==>
      (\<forall>SK KK. SK \<in> symKeys \<longrightarrow> (\<forall>K \<in> KK. ~ KeyCryptKey K SK evs)   -->
               (Key SK \<in> analz (Key`KK Un (knows Spy evs))) =
               (SK \<in> KK | Key SK \<in> analz (knows Spy evs)))"
apply (erule set_cr.induct)
apply (rule_tac [!] allI) +
apply (rule_tac [!] impI [THEN Key_analz_image_Key_lemma, THEN impI])+
apply (valid_certificate_tac [8]) \<comment> \<open>for message 5\<close>
apply (valid_certificate_tac [6]) \<comment> \<open>for message 5\<close>
apply (erule_tac [9] msg6_KeyCryptKey_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps analz_knows_absorb
              analz_Key_image_insert_eq notin_image_iff
              K_fresh_not_KeyCryptKey
              DK_fresh_not_KeyCryptKey ball_conj_distrib
              analz_image_priEK disj_simps)
  \<comment> \<open>9 seconds on a 1.6GHz machine\<close>
apply spy_analz
apply blast  \<comment> \<open>3\<close>
apply blast  \<comment> \<open>5\<close>
done

text\<open>The remaining quantifiers seem to be essential.
  NO NEED to assume the cardholder's OK: bad cardholders don't do anything
  wrong!!\<close>
lemma symKey_secrecy [rule_format]:
     "[|CA i \<notin> bad;  K \<in> symKeys;  evs \<in> set_cr|]
      ==> \<forall>X c. Says (Cardholder c) (CA i) X \<in> set evs -->
                Key K \<in> parts{X} -->
                Cardholder c \<notin> bad -->
                Key K \<notin> analz (knows Spy evs)"
apply (erule set_cr.induct)
apply (frule_tac [8] Gets_certificate_valid) \<comment> \<open>for message 5\<close>
apply (frule_tac [6] Gets_certificate_valid) \<comment> \<open>for message 3\<close>
apply (erule_tac [11] msg6_KeyCryptKey_disj [THEN disjE])
apply (simp_all del: image_insert image_Un imp_disjL
         add: symKey_compromise fresh_notin_analz_knows_Spy
              analz_image_keys_simps analz_knows_absorb
              analz_Key_image_insert_eq notin_image_iff
              K_fresh_not_KeyCryptKey
              DK_fresh_not_KeyCryptKey
              analz_image_priEK)
  \<comment> \<open>2.5 seconds on a 1.6GHz machine\<close>
apply spy_analz  \<comment> \<open>Fake\<close>
apply (auto intro: analz_into_parts [THEN usedI] in_parts_Says_imp_used)
done


subsection\<open>Primary Goals of Cardholder Registration\<close>

text\<open>The cardholder's certificate really was created by the CA, provided the
    CA is uncompromised\<close>

text\<open>Lemma concerning the actual signed message digest\<close>
lemma cert_valid_lemma:
     "[|Crypt (priSK (CA i)) \<lbrace>Hash \<lbrace>Nonce N, Pan(pan C)\<rbrace>, Key cardSK, N1\<rbrace>
          \<in> parts (knows Spy evs);
        CA i \<notin> bad; evs \<in> set_cr|]
  ==> \<exists>KC2 X Y. Says (CA i) C
                     (Crypt KC2 
                       \<lbrace>X, certC (pan C) cardSK N onlySig (priSK (CA i)), Y\<rbrace>)
                  \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
apply auto
done

text\<open>Pre-packaged version for cardholder.  We don't try to confirm the values
  of KC2, X and Y, since they are not important.\<close>
lemma certificate_valid_cardSK:
    "[|Gets C (Crypt KC2 \<lbrace>X, certC (pan C) cardSK N onlySig (invKey SKi),
                              cert (CA i) SKi onlySig (priSK RCA)\<rbrace>) \<in> set evs;
        CA i \<notin> bad; evs \<in> set_cr|]
  ==> \<exists>KC2 X Y. Says (CA i) C
                     (Crypt KC2 
                       \<lbrace>X, certC (pan C) cardSK N onlySig (priSK (CA i)), Y\<rbrace>)
                   \<in> set evs"
by (force dest!: Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Body]
                    certificate_valid_pubSK cert_valid_lemma)


lemma Hash_imp_parts [rule_format]:
     "evs \<in> set_cr
      ==> Hash\<lbrace>X, Nonce N\<rbrace> \<in> parts (knows Spy evs) -->
          Nonce N \<in> parts (knows Spy evs)"
apply (erule set_cr.induct, force)
apply (simp_all (no_asm_simp))
apply (blast intro: parts_mono [THEN [2] rev_subsetD])
done

lemma Hash_imp_parts2 [rule_format]:
     "evs \<in> set_cr
      ==> Hash\<lbrace>X, Nonce M, Y, Nonce N\<rbrace> \<in> parts (knows Spy evs) -->
          Nonce M \<in> parts (knows Spy evs) & Nonce N \<in> parts (knows Spy evs)"
apply (erule set_cr.induct, force)
apply (simp_all (no_asm_simp))
apply (blast intro: parts_mono [THEN [2] rev_subsetD])
done


subsection\<open>Secrecy of Nonces\<close>

subsubsection\<open>Lemmas about the predicate KeyCryptNonce\<close>

text\<open>A fresh DK cannot be associated with any other
  (with respect to a given trace).\<close>
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

text\<open>A fresh N cannot be associated with any other
      (with respect to a given trace).\<close>
lemma N_fresh_not_KeyCryptNonce:
     "\<forall>C. DK \<noteq> priEK C ==> Nonce N \<notin> used evs --> ~ KeyCryptNonce DK N evs"
apply (induct_tac "evs")
apply (rename_tac [2] a evs')
apply (case_tac [2] "a")
apply (auto simp add: parts_insert2)
done

lemma not_KeyCryptNonce_cardSK [rule_format (no_asm)]:
     "[|cardSK \<notin> symKeys;  \<forall>C. cardSK \<noteq> priEK C;  evs \<in> set_cr|] ==>
      Key cardSK \<notin> analz (knows Spy evs) --> ~ KeyCryptNonce cardSK N evs"
apply (erule set_cr.induct, analz_mono_contra, simp_all)
apply (blast dest: not_KeyCryptKey_cardSK)  \<comment> \<open>6\<close>
done

subsubsection\<open>Lemmas for message 5 and 6:
  either cardSK is compromised (when we don't care)
  or else cardSK hasn't been used to encrypt K.\<close>

text\<open>Lemma for message 5: pubSK C is never used to encrypt Nonces.\<close>
lemma pubSK_not_KeyCryptNonce [simp]: "~ KeyCryptNonce (pubSK C) N evs"
apply (induct_tac "evs")
apply (auto simp add: parts_insert2 split: event.split)
done

text\<open>Lemma for message 6: either cardSK is compromised (when we don't care)
  or else cardSK hasn't been used to encrypt K.\<close>
lemma msg6_KeyCryptNonce_disj:
     "[|Gets B \<lbrace>Crypt KC3 \<lbrace>Agent C, Nonce N, Key KC2, Key cardSK, X\<rbrace>, Y\<rbrace>
          \<in> set evs;
        cardSK \<notin> symKeys;  evs \<in> set_cr|]
      ==> Key cardSK \<in> analz (knows Spy evs) |
          ((\<forall>K. ~ KeyCryptKey cardSK K evs) &
           (\<forall>N. ~ KeyCryptNonce cardSK N evs))"
by (blast dest: not_KeyCryptKey_cardSK not_KeyCryptNonce_cardSK
          intro: cardSK_neq_priEK)


text\<open>As usual: we express the property as a logical equivalence\<close>
lemma Nonce_analz_image_Key_lemma:
     "P --> (Nonce N \<in> analz (Key`KK Un H)) --> (Nonce N \<in> analz H)
      ==> P --> (Nonce N \<in> analz (Key`KK Un H)) = (Nonce N \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])


text\<open>The \<open>(no_asm)\<close> attribute is essential, since it retains
  the quantifier and allows the simprule's condition to itself be simplified.\<close>
lemma Nonce_compromise [rule_format (no_asm)]:
     "evs \<in> set_cr ==>
      (\<forall>N KK. (\<forall>K \<in> KK. ~ KeyCryptNonce K N evs)   -->
               (Nonce N \<in> analz (Key`KK Un (knows Spy evs))) =
               (Nonce N \<in> analz (knows Spy evs)))"
apply (erule set_cr.induct)
apply (rule_tac [!] allI)+
apply (rule_tac [!] impI [THEN Nonce_analz_image_Key_lemma])+
apply (frule_tac [8] Gets_certificate_valid) \<comment> \<open>for message 5\<close>
apply (frule_tac [6] Gets_certificate_valid) \<comment> \<open>for message 3\<close>
apply (frule_tac [11] msg6_KeyCryptNonce_disj)
apply (erule_tac [13] disjE)
apply (simp_all del: image_insert image_Un
         add: symKey_compromise
              analz_image_keys_simps analz_knows_absorb
              analz_Key_image_insert_eq notin_image_iff
              N_fresh_not_KeyCryptNonce
              DK_fresh_not_KeyCryptNonce K_fresh_not_KeyCryptKey
              ball_conj_distrib analz_image_priEK)
  \<comment> \<open>14 seconds on a 1.6GHz machine\<close>
apply spy_analz  \<comment> \<open>Fake\<close>
apply blast  \<comment> \<open>3\<close>
apply blast  \<comment> \<open>5\<close>
txt\<open>Message 6\<close>
apply (metis symKey_compromise)
  \<comment> \<open>cardSK compromised\<close>
txt\<open>Simplify again--necessary because the previous simplification introduces
  some logical connectives\<close> 
apply (force simp del: image_insert image_Un imp_disjL
          simp add: analz_image_keys_simps symKey_compromise)
done


subsection\<open>Secrecy of CardSecret: the Cardholder's secret\<close>

lemma NC2_not_CardSecret:
     "[|Crypt EKj \<lbrace>Key K, Pan p, Hash \<lbrace>Agent D, Nonce N\<rbrace>\<rbrace>
          \<in> parts (knows Spy evs);
        Key K \<notin> analz (knows Spy evs);
        Nonce N \<notin> analz (knows Spy evs);
       evs \<in> set_cr|]
      ==> Crypt EKi \<lbrace>Key K', Pan p', Nonce N\<rbrace> \<notin> parts (knows Spy evs)"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct, analz_mono_contra, simp_all)
apply (blast dest: Hash_imp_parts)+
done

lemma KC2_secure_lemma [rule_format]:
     "[|U = Crypt KC3 \<lbrace>Agent C, Nonce N, Key KC2, X\<rbrace>;
        U \<in> parts (knows Spy evs);
        evs \<in> set_cr|]
  ==> Nonce N \<notin> analz (knows Spy evs) -->
      (\<exists>k i W. Says (Cardholder k) (CA i) \<lbrace>U,W\<rbrace> \<in> set evs & 
               Cardholder k \<notin> bad & CA i \<notin> bad)"
apply (erule_tac P = "U \<in> H" for H in rev_mp)
apply (erule set_cr.induct)
apply (valid_certificate_tac [8])  \<comment> \<open>for message 5\<close>
apply (simp_all del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps analz_knows_absorb
              analz_knows_absorb2 notin_image_iff)
  \<comment> \<open>4 seconds on a 1.6GHz machine\<close>
apply (simp_all (no_asm_simp)) \<comment> \<open>leaves 4 subgoals\<close>
apply (blast intro!: analz_insertI)+
done

lemma KC2_secrecy:
     "[|Gets B \<lbrace>Crypt K \<lbrace>Agent C, Nonce N, Key KC2, X\<rbrace>, Y\<rbrace> \<in> set evs;
        Nonce N \<notin> analz (knows Spy evs);  KC2 \<in> symKeys;
        evs \<in> set_cr|]
       ==> Key KC2 \<notin> analz (knows Spy evs)"
by (force dest!: refl [THEN KC2_secure_lemma] symKey_secrecy)


text\<open>Inductive version\<close>
lemma CardSecret_secrecy_lemma [rule_format]:
     "[|CA i \<notin> bad;  evs \<in> set_cr|]
      ==> Key K \<notin> analz (knows Spy evs) -->
          Crypt (pubEK (CA i)) \<lbrace>Key K, Pan p, Nonce CardSecret\<rbrace>
             \<in> parts (knows Spy evs) -->
          Nonce CardSecret \<notin> analz (knows Spy evs)"
apply (erule set_cr.induct, analz_mono_contra)
apply (valid_certificate_tac [8]) \<comment> \<open>for message 5\<close>
apply (valid_certificate_tac [6]) \<comment> \<open>for message 5\<close>
apply (frule_tac [9] msg6_KeyCryptNonce_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps analz_knows_absorb
              analz_Key_image_insert_eq notin_image_iff
              EXHcrypt_def Crypt_notin_image_Key
              N_fresh_not_KeyCryptNonce DK_fresh_not_KeyCryptNonce
              ball_conj_distrib Nonce_compromise symKey_compromise
              analz_image_priEK)
  \<comment> \<open>2.5 seconds on a 1.6GHz machine\<close>
apply spy_analz  \<comment> \<open>Fake\<close>
apply (simp_all (no_asm_simp))
apply blast  \<comment> \<open>1\<close>
apply (blast dest!: Gets_imp_knows_Spy [THEN analz.Inj])  \<comment> \<open>2\<close>
apply blast  \<comment> \<open>3\<close>
apply (blast dest: NC2_not_CardSecret Gets_imp_knows_Spy [THEN analz.Inj] analz_symKeys_Decrypt)  \<comment> \<open>4\<close>
apply blast  \<comment> \<open>5\<close>
apply (blast dest: KC2_secrecy)+  \<comment> \<open>Message 6: two cases\<close>
done


text\<open>Packaged version for cardholder\<close>
lemma CardSecret_secrecy:
     "[|Cardholder k \<notin> bad;  CA i \<notin> bad;
        Says (Cardholder k) (CA i)
           \<lbrace>X, Crypt EKi \<lbrace>Key KC3, Pan p, Nonce CardSecret\<rbrace>\<rbrace> \<in> set evs;
        Gets A \<lbrace>Z, cert (CA i) EKi onlyEnc (priSK RCA),
                    cert (CA i) SKi onlySig (priSK RCA)\<rbrace> \<in> set evs;
        KC3 \<in> symKeys;  evs \<in> set_cr|]
      ==> Nonce CardSecret \<notin> analz (knows Spy evs)"
apply (frule Gets_certificate_valid, assumption)
apply (subgoal_tac "Key KC3 \<notin> analz (knows Spy evs) ")
apply (blast dest: CardSecret_secrecy_lemma)
apply (rule symKey_secrecy)
apply (auto simp add: parts_insert2)
done


subsection\<open>Secrecy of NonceCCA [the CA's secret]\<close>

lemma NC2_not_NonceCCA:
     "[|Hash \<lbrace>Agent C', Nonce N', Agent C, Nonce N\<rbrace>
          \<in> parts (knows Spy evs);
        Nonce N \<notin> analz (knows Spy evs);
       evs \<in> set_cr|]
      ==> Crypt KC1 \<lbrace>\<lbrace>Agent B, Nonce N\<rbrace>, Hash p\<rbrace> \<notin> parts (knows Spy evs)"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct, analz_mono_contra, simp_all)
apply (blast dest: Hash_imp_parts2)+
done


text\<open>Inductive version\<close>
lemma NonceCCA_secrecy_lemma [rule_format]:
     "[|CA i \<notin> bad;  evs \<in> set_cr|]
      ==> Key K \<notin> analz (knows Spy evs) -->
          Crypt K
            \<lbrace>sign (priSK (CA i))
                   \<lbrace>Agent C, Nonce N, Agent(CA i), Nonce NonceCCA\<rbrace>,
              X, Y\<rbrace>
             \<in> parts (knows Spy evs) -->
          Nonce NonceCCA \<notin> analz (knows Spy evs)"
apply (erule set_cr.induct, analz_mono_contra)
apply (valid_certificate_tac [8]) \<comment> \<open>for message 5\<close>
apply (valid_certificate_tac [6]) \<comment> \<open>for message 5\<close>
apply (frule_tac [9] msg6_KeyCryptNonce_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un imp_disjL
         add: analz_image_keys_simps analz_knows_absorb sign_def
              analz_Key_image_insert_eq notin_image_iff
              EXHcrypt_def Crypt_notin_image_Key
              N_fresh_not_KeyCryptNonce DK_fresh_not_KeyCryptNonce
              ball_conj_distrib Nonce_compromise symKey_compromise
              analz_image_priEK)
  \<comment> \<open>3 seconds on a 1.6GHz machine\<close>
apply spy_analz  \<comment> \<open>Fake\<close>
apply blast  \<comment> \<open>1\<close>
apply (blast dest!: Gets_imp_knows_Spy [THEN analz.Inj])  \<comment> \<open>2\<close>
apply blast  \<comment> \<open>3\<close>
apply (blast dest: NC2_not_NonceCCA)  \<comment> \<open>4\<close>
apply blast  \<comment> \<open>5\<close>
apply (blast dest: KC2_secrecy)+  \<comment> \<open>Message 6: two cases\<close>
done


text\<open>Packaged version for cardholder\<close>
lemma NonceCCA_secrecy:
     "[|Cardholder k \<notin> bad;  CA i \<notin> bad;
        Gets (Cardholder k)
           (Crypt KC2
            \<lbrace>sign (priSK (CA i)) \<lbrace>Agent C, Nonce N, Agent(CA i), Nonce NonceCCA\<rbrace>,
              X, Y\<rbrace>) \<in> set evs;
        Says (Cardholder k) (CA i)
           \<lbrace>Crypt KC3 \<lbrace>Agent C, Nonce NC3, Key KC2, X'\<rbrace>, Y'\<rbrace> \<in> set evs;
        Gets A \<lbrace>Z, cert (CA i) EKi onlyEnc (priSK RCA),
                    cert (CA i) SKi onlySig (priSK RCA)\<rbrace> \<in> set evs;
        KC2 \<in> symKeys;  evs \<in> set_cr|]
      ==> Nonce NonceCCA \<notin> analz (knows Spy evs)"
apply (frule Gets_certificate_valid, assumption)
apply (subgoal_tac "Key KC2 \<notin> analz (knows Spy evs) ")
apply (blast dest: NonceCCA_secrecy_lemma)
apply (rule symKey_secrecy)
apply (auto simp add: parts_insert2)
done

text\<open>We don't bother to prove guarantees for the CA.  He doesn't care about
  the PANSecret: it isn't his credit card!\<close>


subsection\<open>Rewriting Rule for PANs\<close>

text\<open>Lemma for message 6: either cardSK isn't a CA's private encryption key,
  or if it is then (because it appears in traffic) that CA is bad,
  and so the Spy knows that key already.  Either way, we can simplify
  the expression @{term "analz (insert (Key cardSK) X)"}.\<close>
lemma msg6_cardSK_disj:
     "[|Gets A \<lbrace>Crypt K \<lbrace>c, n, k', Key cardSK, X\<rbrace>, Y\<rbrace>
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
apply (valid_certificate_tac [8]) \<comment> \<open>for message 5\<close>
apply (valid_certificate_tac [6]) \<comment> \<open>for message 5\<close>
apply (erule_tac [9] msg6_cardSK_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un
         add: analz_image_keys_simps disjoint_image_iff
              notin_image_iff analz_image_priEK)
  \<comment> \<open>6 seconds on a 1.6GHz machine\<close>
apply spy_analz
apply (simp add: insert_absorb)  \<comment> \<open>6\<close>
done

lemma analz_insert_pan:
     "[| evs \<in> set_cr;  K \<notin> invKey ` pubEK ` range CA |] ==>
          (Pan P \<in> analz (insert (Key K) (knows Spy evs))) =
          (Pan P \<in> analz (knows Spy evs))"
by (simp del: image_insert image_Un
         add: analz_image_keys_simps analz_image_pan)


text\<open>Confidentiality of the PAN\@.  Maybe we could combine the statements of
  this theorem with @{term analz_image_pan}, requiring a single induction but
  a much more difficult proof.\<close>
lemma pan_confidentiality:
     "[| Pan (pan C) \<in> analz(knows Spy evs); C \<noteq>Spy; evs :set_cr|]
    ==> \<exists>i X K HN.
        Says C (CA i) \<lbrace>X, Crypt (pubEK (CA i)) \<lbrace>Key K, Pan (pan C), HN\<rbrace> \<rbrace>
           \<in> set evs
      & (CA i) \<in> bad"
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (valid_certificate_tac [8]) \<comment> \<open>for message 5\<close>
apply (valid_certificate_tac [6]) \<comment> \<open>for message 5\<close>
apply (erule_tac [9] msg6_cardSK_disj [THEN disjE])
apply (simp_all
         del: image_insert image_Un
         add: analz_image_keys_simps analz_insert_pan analz_image_pan
              notin_image_iff analz_image_priEK)
  \<comment> \<open>3.5 seconds on a 1.6GHz machine\<close>
apply spy_analz  \<comment> \<open>fake\<close>
apply blast  \<comment> \<open>3\<close>
apply blast  \<comment> \<open>5\<close>
apply (simp (no_asm_simp) add: insert_absorb)  \<comment> \<open>6\<close>
done


subsection\<open>Unicity\<close>

lemma CR6_Says_imp_Notes:
     "[|Says (CA i) C (Crypt KC2
          \<lbrace>sign (priSK (CA i)) \<lbrace>Agent C, Nonce NC3, Agent (CA i), Nonce Y\<rbrace>,
            certC (pan C) cardSK X onlySig (priSK (CA i)),
            cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace>)  \<in> set evs;
        evs \<in> set_cr |]
      ==> Notes (CA i) (Key cardSK) \<in> set evs"
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
done

text\<open>Unicity of cardSK: it uniquely identifies the other components.  
      This holds because a CA accepts a cardSK at most once.\<close>
lemma cardholder_key_unicity:
     "[|Says (CA i) C (Crypt KC2
          \<lbrace>sign (priSK (CA i)) \<lbrace>Agent C, Nonce NC3, Agent (CA i), Nonce Y\<rbrace>,
            certC (pan C) cardSK X onlySig (priSK (CA i)),
            cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace>)
          \<in> set evs;
        Says (CA i) C' (Crypt KC2'
          \<lbrace>sign (priSK (CA i)) \<lbrace>Agent C', Nonce NC3', Agent (CA i), Nonce Y'\<rbrace>,
            certC (pan C') cardSK X' onlySig (priSK (CA i)),
            cert (CA i) (pubSK (CA i)) onlySig (priSK RCA)\<rbrace>)
          \<in> set evs;
        evs \<in> set_cr |] ==> C=C' & NC3=NC3' & X=X' & KC2=KC2' & Y=Y'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct)
apply (simp_all (no_asm_simp))
apply (blast dest!: CR6_Says_imp_Notes)
done


(*<*)
text\<open>UNUSED unicity result\<close>
lemma unique_KC1:
     "[|Says C B \<lbrace>Crypt KC1 X, Crypt EK \<lbrace>Key KC1, Y\<rbrace>\<rbrace>
          \<in> set evs;
        Says C B' \<lbrace>Crypt KC1 X', Crypt EK' \<lbrace>Key KC1, Y'\<rbrace>\<rbrace>
          \<in> set evs;
        C \<notin> bad;  evs \<in> set_cr|] ==> B'=B & Y'=Y"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done

text\<open>UNUSED unicity result\<close>
lemma unique_KC2:
     "[|Says C B \<lbrace>Crypt K \<lbrace>Agent C, nn, Key KC2, X\<rbrace>, Y\<rbrace> \<in> set evs;
        Says C B' \<lbrace>Crypt K' \<lbrace>Agent C, nn', Key KC2, X'\<rbrace>, Y'\<rbrace> \<in> set evs;
        C \<notin> bad;  evs \<in> set_cr|] ==> B'=B & X'=X"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule set_cr.induct, auto)
done
(*>*)


text\<open>Cannot show cardSK to be secret because it isn't assumed to be fresh
  it could be a previously compromised cardSK [e.g. involving a bad CA]\<close>


end
