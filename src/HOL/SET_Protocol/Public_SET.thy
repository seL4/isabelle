(*  Title:      HOL/SET_Protocol/Public_SET.thy
    Author:     Giampaolo Bella
    Author:     Fabio Massacci
    Author:     Lawrence C Paulson
*)

section\<open>The Public-Key Theory, Modified for SET\<close>

theory Public_SET
imports Event_SET
begin

subsection\<open>Symmetric and Asymmetric Keys\<close>

text\<open>definitions influenced by the wish to assign asymmetric keys 
  - since the beginning - only to RCA and CAs, namely we need a partial 
  function on type Agent\<close>


text\<open>The SET specs mention two signature keys for CAs - we only have one\<close>

consts
  publicKey :: "[bool, agent] \<Rightarrow> key"
    \<comment> \<open>the boolean is TRUE if a signing key\<close>

abbreviation "pubEK == publicKey False"
abbreviation "pubSK == publicKey True"

(*BEWARE!! priEK, priSK DON'T WORK with inj, range, image, etc.*)
abbreviation "priEK A == invKey (pubEK A)"
abbreviation "priSK A == invKey (pubSK A)"

text\<open>By freeness of agents, no two agents have the same key. Since
 \<^term>\<open>True\<noteq>False\<close>, no agent has the same signing and encryption keys.\<close>

specification (publicKey)
  injective_publicKey:
    "publicKey b A = publicKey c A' \<Longrightarrow> b=c \<and> A=A'"
(*<*)
   apply (rule exI [of _ "%b A. 2 * nat_of_agent A + (if b then 1 else 0)"]) 
   apply (auto simp add: inj_on_def inj_nat_of_agent [THEN inj_eq] split: agent.split) 
   apply (drule_tac f="%x. x mod 2" in arg_cong, simp add: mod_Suc)+
(*or this, but presburger won't abstract out the function applications
   apply presburger+
*)
   done                       
(*>*)

axiomatization where
  (*No private key equals any public key (essential to ensure that private
    keys are private!) *)
  privateKey_neq_publicKey [iff]:
      "invKey (publicKey b A) \<noteq> publicKey b' A'"

declare privateKey_neq_publicKey [THEN not_sym, iff]

  
subsection\<open>Initial Knowledge\<close>

text\<open>This information is not necessary.  Each protocol distributes any needed
certificates, and anyway our proofs require a formalization of the Spy's 
knowledge only.  However, the initial knowledge is as follows:
   All agents know RCA's public keys;
   RCA and CAs know their own respective keys;
   RCA (has already certified and therefore) knows all CAs public keys; 
   Spy knows all keys of all bad agents.\<close>

overloading initState \<equiv> "initState"
begin

primrec initState where
(*<*)
  initState_CA:
    "initState (CA i)  =
       (if i=0 then Key ` ({priEK RCA, priSK RCA} \<union>
                            pubEK ` (range CA) \<union> pubSK ` (range CA))
        else {Key (priEK (CA i)), Key (priSK (CA i)),
              Key (pubEK (CA i)), Key (pubSK (CA i)),
              Key (pubEK RCA), Key (pubSK RCA)})"

| initState_Cardholder:
    "initState (Cardholder i)  =    
       {Key (priEK (Cardholder i)), Key (priSK (Cardholder i)),
        Key (pubEK (Cardholder i)), Key (pubSK (Cardholder i)),
        Key (pubEK RCA), Key (pubSK RCA)}"

| initState_Merchant:
    "initState (Merchant i)  =    
       {Key (priEK (Merchant i)), Key (priSK (Merchant i)),
        Key (pubEK (Merchant i)), Key (pubSK (Merchant i)),
        Key (pubEK RCA), Key (pubSK RCA)}"

| initState_PG:
    "initState (PG i)  = 
       {Key (priEK (PG i)), Key (priSK (PG i)),
        Key (pubEK (PG i)), Key (pubSK (PG i)),
        Key (pubEK RCA), Key (pubSK RCA)}"
(*>*)
| initState_Spy:
    "initState Spy = Key ` (invKey ` pubEK ` bad \<union>
                            invKey ` pubSK ` bad \<union>
                            range pubEK \<union> range pubSK)"

end


text\<open>Injective mapping from agents to PANs: an agent can have only one card\<close>

consts  pan :: "agent \<Rightarrow> nat"

specification (pan)
  inj_pan: "inj pan"
  \<comment> \<open>No two agents have the same PAN\<close>
(*<*)
   apply (rule exI [of _ "nat_of_agent"]) 
   apply (simp add: inj_on_def inj_nat_of_agent [THEN inj_eq]) 
   done
(*>*)

declare inj_pan [THEN inj_eq, iff]

consts
  XOR :: "nat*nat \<Rightarrow> nat"  \<comment> \<open>no properties are assumed of exclusive-or\<close>


subsection\<open>Signature Primitives\<close>

definition
 (* Signature = Message + signed Digest *)
  sign :: "[key, msg]\<Rightarrow>msg"
  where "sign K X = \<lbrace>X, Crypt K (Hash X) \<rbrace>"

definition
 (* Signature Only = signed Digest Only *)
  signOnly :: "[key, msg]\<Rightarrow>msg"
  where "signOnly K X = Crypt K (Hash X)"

definition
 (* Signature for Certificates = Message + signed Message *)
  signCert :: "[key, msg]\<Rightarrow>msg"
  where "signCert K X = \<lbrace>X, Crypt K X \<rbrace>"

definition
 (* Certification Authority's Certificate.
    Contains agent name, a key, a number specifying the key's target use,
              a key to sign the entire certificate.

    Should prove if signK=priSK RCA and C=CA i,
                  then Ka=pubEK i or pubSK i depending on T  ??
 *)
  cert :: "[agent, key, msg, key] \<Rightarrow> msg"
  where "cert A Ka T signK = signCert signK \<lbrace>Agent A, Key Ka, T\<rbrace>"

definition
 (* Cardholder's Certificate.
    Contains a PAN, the certified key Ka, the PANSecret PS,
    a number specifying the target use for Ka, the signing key signK.
 *)
  certC :: "[nat, key, nat, msg, key] \<Rightarrow> msg"
  where "certC PAN Ka PS T signK =
    signCert signK \<lbrace>Hash \<lbrace>Nonce PS, Pan PAN\<rbrace>, Key Ka, T\<rbrace>"

(*cert and certA have no repeated elements, so they could be abbreviations,
  but that's tricky and makes proofs slower*)

abbreviation "onlyEnc == Number 0"
abbreviation "onlySig == Number (Suc 0)"
abbreviation "authCode == Number (Suc (Suc 0))"

subsection\<open>Encryption Primitives\<close>

definition EXcrypt :: "[key,key,msg,msg] \<Rightarrow> msg" where
  \<comment> \<open>Extra Encryption\<close>
    (*K: the symmetric key   EK: the public encryption key*)
    "EXcrypt K EK M m =
       \<lbrace>Crypt K \<lbrace>M, Hash m\<rbrace>, Crypt EK \<lbrace>Key K, m\<rbrace>\<rbrace>"

definition EXHcrypt :: "[key,key,msg,msg] \<Rightarrow> msg" where
  \<comment> \<open>Extra Encryption with Hashing\<close>
    (*K: the symmetric key   EK: the public encryption key*)
    "EXHcrypt K EK M m =
       \<lbrace>Crypt K \<lbrace>M, Hash m\<rbrace>, Crypt EK \<lbrace>Key K, m, Hash M\<rbrace>\<rbrace>"

definition Enc :: "[key,key,key,msg] \<Rightarrow> msg" where
  \<comment> \<open>Simple Encapsulation with SIGNATURE\<close>
    (*SK: the sender's signing key
      K: the symmetric key
      EK: the public encryption key*)
    "Enc SK K EK M =
       \<lbrace>Crypt K (sign SK M), Crypt EK (Key K)\<rbrace>"

definition EncB :: "[key,key,key,msg,msg] \<Rightarrow> msg" where
  \<comment> \<open>Encapsulation with Baggage.  Keys as above, and baggage b.\<close>
    "EncB SK K EK M b =
       \<lbrace>Enc SK K EK \<lbrace>M, Hash b\<rbrace>, b\<rbrace>"


subsection\<open>Basic Properties of pubEK, pubSK, priEK and priSK\<close>

lemma publicKey_eq_iff [iff]:
     "(publicKey b A = publicKey b' A') = (b=b' \<and> A=A')"
by (blast dest: injective_publicKey)

lemma privateKey_eq_iff [iff]:
     "(invKey (publicKey b A) = invKey (publicKey b' A')) = (b=b' \<and> A=A')"
by auto

lemma not_symKeys_publicKey [iff]: "publicKey b A \<notin> symKeys"
by (simp add: symKeys_def)

lemma not_symKeys_privateKey [iff]: "invKey (publicKey b A) \<notin> symKeys"
by (simp add: symKeys_def)

lemma symKeys_invKey_eq [simp]: "K \<in> symKeys \<Longrightarrow> invKey K = K"
by (simp add: symKeys_def)

lemma symKeys_invKey_iff [simp]: "(invKey K \<in> symKeys) = (K \<in> symKeys)"
by (unfold symKeys_def, auto)

text\<open>Can be slow (or even loop) as a simprule\<close>
lemma symKeys_neq_imp_neq: "(K \<in> symKeys) \<noteq> (K' \<in> symKeys) \<Longrightarrow> K \<noteq> K'"
by blast

text\<open>These alternatives to \<open>symKeys_neq_imp_neq\<close> don't seem any better
in practice.\<close>
lemma publicKey_neq_symKey: "K \<in> symKeys \<Longrightarrow> publicKey b A \<noteq> K"
by blast

lemma symKey_neq_publicKey: "K \<in> symKeys \<Longrightarrow> K \<noteq> publicKey b A"
by blast

lemma privateKey_neq_symKey: "K \<in> symKeys \<Longrightarrow> invKey (publicKey b A) \<noteq> K"
by blast

lemma symKey_neq_privateKey: "K \<in> symKeys \<Longrightarrow> K \<noteq> invKey (publicKey b A)"
by blast

lemma analz_symKeys_Decrypt:
     "[| Crypt K X \<in> analz H;  K \<in> symKeys;  Key K \<in> analz H |]  
      ==> X \<in> analz H"
by auto


subsection\<open>"Image" Equations That Hold for Injective Functions\<close>

lemma invKey_image_eq [iff]: "(invKey x \<in> invKey`A) = (x\<in>A)"
by auto

text\<open>holds because invKey is injective\<close>
lemma publicKey_image_eq [iff]:
     "(publicKey b A \<in> publicKey c ` AS) = (b=c \<and> A\<in>AS)"
by auto

lemma privateKey_image_eq [iff]:
     "(invKey (publicKey b A) \<in> invKey ` publicKey c ` AS) = (b=c \<and> A\<in>AS)"
by auto

lemma privateKey_notin_image_publicKey [iff]:
     "invKey (publicKey b A) \<notin> publicKey c ` AS"
by auto

lemma publicKey_notin_image_privateKey [iff]:
     "publicKey b A \<notin> invKey ` publicKey c ` AS"
by auto

lemma keysFor_parts_initState [simp]: "keysFor (parts (initState C)) = {}"
apply (simp add: keysFor_def)
apply (induct_tac "C")
apply (auto intro: range_eqI)
done

text\<open>for proving \<open>new_keys_not_used\<close>\<close>
lemma keysFor_parts_insert:
     "[| K \<in> keysFor (parts (insert X H));  X \<in> synth (analz H) |]  
      ==> K \<in> keysFor (parts H) | Key (invKey K) \<in> parts H"
by (force dest!: 
         parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
         analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD] 
            intro: analz_into_parts)

lemma Crypt_imp_keysFor [intro]:
     "[|K \<in> symKeys; Crypt K X \<in> H|] ==> K \<in> keysFor H"
by (drule Crypt_imp_invKey_keysFor, simp)

text\<open>Agents see their own private keys!\<close>
lemma privateKey_in_initStateCA [iff]:
     "Key (invKey (publicKey b A)) \<in> initState A"
by (case_tac "A", auto)

text\<open>Agents see their own public keys!\<close>
lemma publicKey_in_initStateCA [iff]: "Key (publicKey b A) \<in> initState A"
by (case_tac "A", auto)

text\<open>RCA sees CAs' public keys!\<close>
lemma pubK_CA_in_initState_RCA [iff]:
     "Key (publicKey b (CA i)) \<in> initState RCA"
by auto


text\<open>Spy knows all public keys\<close>
lemma knows_Spy_pubEK_i [iff]: "Key (publicKey b A) \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all add: imageI knows_Cons split: event.split)
done

declare knows_Spy_pubEK_i [THEN analz.Inj, iff]
                            (*needed????*)

text\<open>Spy sees private keys of bad agents! [and obviously public keys too]\<close>
lemma knows_Spy_bad_privateKey [intro!]:
     "A \<in> bad \<Longrightarrow> Key (invKey (publicKey b A)) \<in> knows Spy evs"
by (rule initState_subset_knows [THEN subsetD], simp)


subsection\<open>Fresh Nonces for Possibility Theorems\<close>

lemma Nonce_notin_initState [iff]: "Nonce N \<notin> parts (initState B)"
by (induct_tac "B", auto)

lemma Nonce_notin_used_empty [simp]: "Nonce N \<notin> used []"
by (simp add: used_Nil)

text\<open>In any trace, there is an upper bound N on the greatest nonce in use.\<close>
lemma Nonce_supply_lemma: "\<exists>N. \<forall>n. N\<le>n \<longrightarrow> Nonce n \<notin> used evs"
apply (induct_tac "evs")
apply (rule_tac x = 0 in exI)
apply (simp_all add: used_Cons split: event.split, safe)
apply (rule msg_Nonce_supply [THEN exE], blast elim!: add_leE)+
done

lemma Nonce_supply1: "\<exists>N. Nonce N \<notin> used evs"
by (rule Nonce_supply_lemma [THEN exE], blast)

lemma Nonce_supply: "Nonce (SOME N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply (rule someI, fast)
done


subsection\<open>Specialized Methods for Possibility Theorems\<close>

ML
\<open>
(*Tactic for possibility theorems*)
fun possibility_tac ctxt =
    REPEAT (*omit used_Says so that Nonces start from different traces!*)
    (ALLGOALS (simp_tac (ctxt |> Simplifier.del_simps @{thms used_Says used_Notes}))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac ctxt [refl, conjI, @{thm Nonce_supply}]))

(*For harder protocols (such as SET_CR!), where we have to set up some
  nonces and keys initially*)
fun basic_possibility_tac ctxt =
    REPEAT 
    (ALLGOALS (asm_simp_tac (ctxt |> Simplifier.set_unsafe_solver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac ctxt [refl, conjI]))
\<close>

method_setup possibility = \<open>
    Scan.succeed (SIMPLE_METHOD o possibility_tac)\<close>
    "for proving possibility theorems"

method_setup basic_possibility = \<open>
    Scan.succeed (SIMPLE_METHOD o basic_possibility_tac)\<close>
    "for proving possibility theorems"


subsection\<open>Specialized Rewriting for Theorems About \<^term>\<open>analz\<close> and Image\<close>

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} \<union> H"
by blast

lemma insert_Key_image:
     "insert (Key K) (Key`KK \<union> C) = Key ` (insert K KK) \<union> C"
by blast

text\<open>Needed for \<open>DK_fresh_not_KeyCryptKey\<close>\<close>
lemma publicKey_in_used [iff]: "Key (publicKey b A) \<in> used evs"
by auto

lemma privateKey_in_used [iff]: "Key (invKey (publicKey b A)) \<in> used evs"
by (blast intro!: initState_into_used)

text\<open>Reverse the normal simplification of "image" to build up (not break down)
  the set of keys.  Based on \<open>analz_image_freshK_ss\<close>, but simpler.\<close>
lemmas analz_image_keys_simps =
       simp_thms mem_simps \<comment> \<open>these two allow its use with \<open>only:\<close>\<close>
       image_insert [THEN sym] image_Un [THEN sym] 
       rangeI symKeys_neq_imp_neq
       insert_Key_singleton insert_Key_image Un_assoc [THEN sym]


(*General lemmas proved by Larry*)

subsection\<open>Controlled Unfolding of Abbreviations\<close>

text\<open>A set is expanded only if a relation is applied to it\<close>
lemma def_abbrev_simp_relation:
     "A = B \<Longrightarrow> (A \<in> X) = (B \<in> X) \<and>  
                 (u = A) = (u = B) \<and>  
                 (A = u) = (B = u)"
by auto

text\<open>A set is expanded only if one of the given functions is applied to it\<close>
lemma def_abbrev_simp_function:
     "A = B  
      \<Longrightarrow> parts (insert A X) = parts (insert B X) \<and>  
          analz (insert A X) = analz (insert B X) \<and>  
          keysFor (insert A X) = keysFor (insert B X)"
by auto

subsubsection\<open>Special Simplification Rules for \<^term>\<open>signCert\<close>\<close>

text\<open>Avoids duplicating X and its components!\<close>
lemma parts_insert_signCert:
     "parts (insert (signCert K X) H) =  
      insert \<lbrace>X, Crypt K X\<rbrace> (parts (insert (Crypt K X) H))"
by (simp add: signCert_def insert_commute [of X])

text\<open>Avoids a case split! [X is always available]\<close>
lemma analz_insert_signCert:
     "analz (insert (signCert K X) H) =  
      insert \<lbrace>X, Crypt K X\<rbrace> (insert (Crypt K X) (analz (insert X H)))"
by (simp add: signCert_def insert_commute [of X])

lemma keysFor_insert_signCert: "keysFor (insert (signCert K X) H) = keysFor H"
by (simp add: signCert_def)

text\<open>Controlled rewrite rules for \<^term>\<open>signCert\<close>, just the definitions
  of the others. Encryption primitives are just expanded, despite their huge
  redundancy!\<close>
lemmas abbrev_simps [simp] =
    parts_insert_signCert analz_insert_signCert keysFor_insert_signCert
    sign_def     [THEN def_abbrev_simp_relation]
    sign_def     [THEN def_abbrev_simp_function]
    signCert_def [THEN def_abbrev_simp_relation]
    signCert_def [THEN def_abbrev_simp_function]
    certC_def    [THEN def_abbrev_simp_relation]
    certC_def    [THEN def_abbrev_simp_function]
    cert_def     [THEN def_abbrev_simp_relation]
    cert_def     [THEN def_abbrev_simp_function]
    EXcrypt_def  [THEN def_abbrev_simp_relation]
    EXcrypt_def  [THEN def_abbrev_simp_function]
    EXHcrypt_def [THEN def_abbrev_simp_relation]
    EXHcrypt_def [THEN def_abbrev_simp_function]
    Enc_def      [THEN def_abbrev_simp_relation]
    Enc_def      [THEN def_abbrev_simp_function]
    EncB_def     [THEN def_abbrev_simp_relation]
    EncB_def     [THEN def_abbrev_simp_function]


subsubsection\<open>Elimination Rules for Controlled Rewriting\<close>

lemma Enc_partsE: 
     "!!R. [|Enc SK K EK M \<in> parts H;  
             [|Crypt K (sign SK M) \<in> parts H;  
               Crypt EK (Key K) \<in> parts H|] ==> R|]  
           ==> R"

by (unfold Enc_def, blast)

lemma EncB_partsE: 
     "!!R. [|EncB SK K EK M b \<in> parts H;  
             [|Crypt K (sign SK \<lbrace>M, Hash b\<rbrace>) \<in> parts H;  
               Crypt EK (Key K) \<in> parts H;  
               b \<in> parts H|] ==> R|]  
           ==> R"
by (unfold EncB_def Enc_def, blast)

lemma EXcrypt_partsE: 
     "!!R. [|EXcrypt K EK M m \<in> parts H;  
             [|Crypt K \<lbrace>M, Hash m\<rbrace> \<in> parts H;  
               Crypt EK \<lbrace>Key K, m\<rbrace> \<in> parts H|] ==> R|]  
           ==> R"
by (unfold EXcrypt_def, blast)


subsection\<open>Lemmas to Simplify Expressions Involving \<^term>\<open>analz\<close>\<close>

lemma analz_knows_absorb:
     "Key K \<in> analz (knows Spy evs)  
      ==> analz (Key ` (insert K H) \<union> knows Spy evs) =  
          analz (Key ` H \<union> knows Spy evs)"
by (simp add: analz_insert_eq Un_upper2 [THEN analz_mono, THEN subsetD])

lemma analz_knows_absorb2:
     "Key K \<in> analz (knows Spy evs)  
      ==> analz (Key ` (insert X (insert K H)) \<union> knows Spy evs) =  
          analz (Key ` (insert X H) \<union> knows Spy evs)"
apply (subst insert_commute)
apply (erule analz_knows_absorb)
done

lemma analz_insert_subset_eq:
     "[|X \<in> analz (knows Spy evs);  knows Spy evs \<subseteq> H|]  
      ==> analz (insert X H) = analz H"
apply (rule analz_insert_eq)
apply (blast intro: analz_mono [THEN [2] rev_subsetD])
done

lemmas analz_insert_simps = 
         analz_insert_subset_eq Un_upper2
         subset_insertI [THEN [2] subset_trans] 


subsection\<open>Freshness Lemmas\<close>

lemma in_parts_Says_imp_used:
     "[|Key K \<in> parts {X}; Says A B X \<in> set evs|] ==> Key K \<in> used evs"
by (blast intro: parts_trans dest!: Says_imp_knows_Spy [THEN parts.Inj])

text\<open>A useful rewrite rule with \<^term>\<open>analz_image_keys_simps\<close>\<close>
lemma Crypt_notin_image_Key: "Crypt K X \<notin> Key ` KK"
by auto

lemma fresh_notin_analz_knows_Spy:
     "Key K \<notin> used evs \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (auto dest: analz_into_parts)

end
