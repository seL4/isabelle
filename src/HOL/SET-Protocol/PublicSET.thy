(*  Title:      HOL/Auth/SET/PublicSET
    ID:         $Id$
    Authors:     Giampaolo Bella, Fabio Massacci, Lawrence C Paulson
*)

header{*The Public-Key Theory, Modified for SET*}

theory PublicSET = EventSET:

subsection{*Symmetric and Asymmetric Keys*}

text{*definitions influenced by the wish to assign asymmetric keys 
  - since the beginning - only to RCA and CAs, namely we need a partial 
  function on type Agent*}


text{*The SET specs mention two signature keys for CAs - we only have one*}

consts
  publicKey :: "[bool, agent] => key"
    --{*the boolean is TRUE if a signing key*}

syntax
  pubEK :: "agent => key"
  pubSK :: "agent => key"
  priEK :: "agent => key"
  priSK :: "agent => key"

translations
  "pubEK"  == "publicKey False"
  "pubSK"  == "publicKey True"

  (*BEWARE!! priEK, priSK DON'T WORK with inj, range, image, etc.*)
  "priEK A"  == "invKey (pubEK A)"
  "priSK A"  == "invKey (pubSK A)"

text{*By freeness of agents, no two agents have the same key. Since
 @{term "True\<noteq>False"}, no agent has the same signing and encryption keys.*}

specification (publicKey)
  injective_publicKey:
    "publicKey b A = publicKey c A' ==> b=c & A=A'"
   apply (rule exI [of _ "%b A. 2 * nat_of_agent A + (if b then 1 else 0)"]) 
   apply (auto simp add: inj_on_def inj_nat_of_agent [THEN inj_eq] split: agent.split) 
   apply (drule_tac f="%x. x mod 2" in arg_cong, simp add: mod_Suc)+
(*or this, but presburger won't abstract out the function applications
   apply presburger+
*)
   done                       


axioms
  (*No private key equals any public key (essential to ensure that private
    keys are private!) *)
  privateKey_neq_publicKey [iff]:
      "invKey (publicKey b A) \<noteq> publicKey b' A'"

declare privateKey_neq_publicKey [THEN not_sym, iff]

  
subsection{*Initial Knowledge*}

text{*This information is not necessary.  Each protocol distributes any needed
certificates, and anyway our proofs require a formalization of the Spy's 
knowledge only.  However, the initial knowledge is as follows:
   All agents know RCA's public keys;
   RCA and CAs know their own respective keys;
   RCA (has already certified and therefore) knows all CAs public keys; 
   Spy knows all keys of all bad agents.*}
primrec    

  initState_CA:
    "initState (CA i)  =
       (if i=0 then Key ` ({priEK RCA, priSK RCA} Un
			    pubEK ` (range CA) Un pubSK ` (range CA))
	else {Key (priEK (CA i)), Key (priSK (CA i)),
	      Key (pubEK (CA i)), Key (pubSK (CA i)),
	      Key (pubEK RCA), Key (pubSK RCA)})"

  initState_Cardholder:
    "initState (Cardholder i)  =    
       {Key (priEK (Cardholder i)), Key (priSK (Cardholder i)),
	Key (pubEK (Cardholder i)), Key (pubSK (Cardholder i)),
	Key (pubEK RCA), Key (pubSK RCA)}"

  initState_Merchant:
    "initState (Merchant i)  =    
       {Key (priEK (Merchant i)), Key (priSK (Merchant i)),
	Key (pubEK (Merchant i)), Key (pubSK (Merchant i)),
	Key (pubEK RCA), Key (pubSK RCA)}"

  initState_PG:
    "initState (PG i)  = 
       {Key (priEK (PG i)), Key (priSK (PG i)),
	Key (pubEK (PG i)), Key (pubSK (PG i)),
	Key (pubEK RCA), Key (pubSK RCA)}"

  initState_Spy:
    "initState Spy = Key ` (invKey ` pubEK ` bad Un
			    invKey ` pubSK ` bad Un
			    range pubEK Un range pubSK)"


text{*Injective mapping from agents to PANs: an agent can have only one card*}

consts  pan :: "agent => nat"

specification (pan)
  inj_pan: "inj pan"
  --{*No two agents have the same PAN*}
   apply (rule exI [of _ "nat_of_agent"]) 
   apply (simp add: inj_on_def inj_nat_of_agent [THEN inj_eq]) 
   done

declare inj_pan [THEN inj_eq, iff]

consts
  XOR :: "nat*nat => nat"  --{*no properties are assumed of exclusive-or*}


subsection{*Signature Primitives*}

constdefs 

 (* Signature = Message + signed Digest *)
  sign :: "[key, msg]=>msg"
    "sign K X == {|X, Crypt K (Hash X) |}"

 (* Signature Only = signed Digest Only *)
  signOnly :: "[key, msg]=>msg"
    "signOnly K X == Crypt K (Hash X)"

 (* Signature for Certificates = Message + signed Message *)
  signCert :: "[key, msg]=>msg"
    "signCert K X == {|X, Crypt K X |}"

 (* Certification Authority's Certificate.
    Contains agent name, a key, a number specifying the key's target use,
              a key to sign the entire certificate.

    Should prove if signK=priSK RCA and C=CA i,
                  then Ka=pubEK i or pubSK i depending on T  ??
 *)
  cert :: "[agent, key, msg, key] => msg"
    "cert A Ka T signK == signCert signK {|Agent A, Key Ka, T|}"


 (* Cardholder's Certificate.
    Contains a PAN, the certified key Ka, the PANSecret PS,
    a number specifying the target use for Ka, the signing key signK.
 *)
  certC :: "[nat, key, nat, msg, key] => msg"
    "certC PAN Ka PS T signK ==
     signCert signK {|Hash {|Nonce PS, Pan PAN|}, Key Ka, T|}"

  (*cert and certA have no repeated elements, so they could be translations,
    but that's tricky and makes proofs slower*)

syntax
  "onlyEnc" :: msg      
  "onlySig" :: msg
  "authCode" :: msg

translations
  "onlyEnc"   == "Number 0"
  "onlySig"  == "Number (Suc 0)"
  "authCode" == "Number (Suc (Suc 0))"

subsection{*Encryption Primitives*}

constdefs

  EXcrypt :: "[key,key,msg,msg] => msg"
  --{*Extra Encryption*}
    (*K: the symmetric key   EK: the public encryption key*)
    "EXcrypt K EK M m ==
       {|Crypt K {|M, Hash m|}, Crypt EK {|Key K, m|}|}"

  EXHcrypt :: "[key,key,msg,msg] => msg"
  --{*Extra Encryption with Hashing*}
    (*K: the symmetric key   EK: the public encryption key*)
    "EXHcrypt K EK M m ==
       {|Crypt K {|M, Hash m|}, Crypt EK {|Key K, m, Hash M|}|}"

  Enc :: "[key,key,key,msg] => msg"
  --{*Simple Encapsulation with SIGNATURE*}
    (*SK: the sender's signing key
      K: the symmetric key
      EK: the public encryption key*)
    "Enc SK K EK M ==
       {|Crypt K (sign SK M), Crypt EK (Key K)|}"

  EncB :: "[key,key,key,msg,msg] => msg"
  --{*Encapsulation with Baggage.  Keys as above, and baggage b.*}
    "EncB SK K EK M b == 
       {|Enc SK K EK {|M, Hash b|}, b|}"


subsection{*Basic Properties of pubEK, pubSK, priEK and priSK *}

lemma publicKey_eq_iff [iff]:
     "(publicKey b A = publicKey b' A') = (b=b' & A=A')"
by (blast dest: injective_publicKey)

lemma privateKey_eq_iff [iff]:
     "(invKey (publicKey b A) = invKey (publicKey b' A')) = (b=b' & A=A')"
by auto

lemma not_symKeys_publicKey [iff]: "publicKey b A \<notin> symKeys"
by (simp add: symKeys_def)

lemma not_symKeys_privateKey [iff]: "invKey (publicKey b A) \<notin> symKeys"
by (simp add: symKeys_def)

lemma symKeys_invKey_eq [simp]: "K \<in> symKeys ==> invKey K = K"
by (simp add: symKeys_def)

lemma symKeys_invKey_iff [simp]: "(invKey K \<in> symKeys) = (K \<in> symKeys)"
by (unfold symKeys_def, auto)

text{*Can be slow (or even loop) as a simprule*}
lemma symKeys_neq_imp_neq: "(K \<in> symKeys) \<noteq> (K' \<in> symKeys) ==> K \<noteq> K'"
by blast

text{*These alternatives to @{text symKeys_neq_imp_neq} don't seem any better
in practice.*}
lemma publicKey_neq_symKey: "K \<in> symKeys ==> publicKey b A \<noteq> K"
by blast

lemma symKey_neq_publicKey: "K \<in> symKeys ==> K \<noteq> publicKey b A"
by blast

lemma privateKey_neq_symKey: "K \<in> symKeys ==> invKey (publicKey b A) \<noteq> K"
by blast

lemma symKey_neq_privateKey: "K \<in> symKeys ==> K \<noteq> invKey (publicKey b A)"
by blast

lemma analz_symKeys_Decrypt:
     "[| Crypt K X \<in> analz H;  K \<in> symKeys;  Key K \<in> analz H |]  
      ==> X \<in> analz H"
by auto


subsection{*"Image" Equations That Hold for Injective Functions *}

lemma invKey_image_eq [iff]: "(invKey x \<in> invKey`A) = (x\<in>A)"
by auto

text{*holds because invKey is injective*}
lemma publicKey_image_eq [iff]:
     "(publicKey b A \<in> publicKey c ` AS) = (b=c & A\<in>AS)"
by auto

lemma privateKey_image_eq [iff]:
     "(invKey (publicKey b A) \<in> invKey ` publicKey c ` AS) = (b=c & A\<in>AS)"
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

text{*for proving @{text new_keys_not_used}*}
lemma keysFor_parts_insert:
     "[| K \<in> keysFor (parts (insert X H));  X \<in> synth (analz H) |]  
      ==> K \<in> keysFor (parts H) | Key (invKey K) \<in> parts H"
apply (force dest!: 
         parts_insert_subset_Un [THEN keysFor_mono, THEN [2] rev_subsetD]
         analz_subset_parts [THEN keysFor_mono, THEN [2] rev_subsetD] 
            intro: analz_into_parts)
done

lemma Crypt_imp_keysFor [intro]:
     "[|K \<in> symKeys; Crypt K X \<in> H|] ==> K \<in> keysFor H"
by (drule Crypt_imp_invKey_keysFor, simp)

text{*Agents see their own private keys!*}
lemma privateKey_in_initStateCA [iff]:
     "Key (invKey (publicKey b A)) \<in> initState A"
by (case_tac "A", auto)

text{*Agents see their own public keys!*}
lemma publicKey_in_initStateCA [iff]: "Key (publicKey b A) \<in> initState A"
by (case_tac "A", auto)

text{*RCA sees CAs' public keys! *}
lemma pubK_CA_in_initState_RCA [iff]:
     "Key (publicKey b (CA i)) \<in> initState RCA"
by auto


text{*Spy knows all public keys*}
lemma knows_Spy_pubEK_i [iff]: "Key (publicKey b A) \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all add: imageI knows_Cons split add: event.split)
done

declare knows_Spy_pubEK_i [THEN analz.Inj, iff]
                            (*needed????*)

text{*Spy sees private keys of bad agents! [and obviously public keys too]*}
lemma knows_Spy_bad_privateKey [intro!]:
     "A \<in> bad ==> Key (invKey (publicKey b A)) \<in> knows Spy evs"
by (rule initState_subset_knows [THEN subsetD], simp)


subsection{*Fresh Nonces for Possibility Theorems*}

lemma Nonce_notin_initState [iff]: "Nonce N \<notin> parts (initState B)"
by (induct_tac "B", auto)

lemma Nonce_notin_used_empty [simp]: "Nonce N \<notin> used []"
by (simp add: used_Nil)

text{*In any trace, there is an upper bound N on the greatest nonce in use.*}
lemma Nonce_supply_lemma: "\<exists>N. \<forall>n. N<=n --> Nonce n \<notin> used evs"
apply (induct_tac "evs")
apply (rule_tac x = 0 in exI)
apply (simp_all add: used_Cons split add: event.split, safe)
apply (rule msg_Nonce_supply [THEN exE], blast elim!: add_leE)+
done

lemma Nonce_supply1: "\<exists>N. Nonce N \<notin> used evs"
by (rule Nonce_supply_lemma [THEN exE], blast)

lemma Nonce_supply: "Nonce (@ N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply (rule someI, fast)
done


subsection{*Specialized Methods for Possibility Theorems*}

ML
{*
val Nonce_supply1 = thm "Nonce_supply1";
val Nonce_supply = thm "Nonce_supply";

val used_Says = thm "used_Says";
val used_Notes = thm "used_Notes";

(*Tactic for possibility theorems (Isar interface)*)
fun gen_possibility_tac ss state = state |>
    REPEAT (*omit used_Says so that Nonces start from different traces!*)
    (ALLGOALS (simp_tac (ss delsimps [used_Says,used_Notes]))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, Nonce_supply]))

(*Tactic for possibility theorems (ML script version)*)
fun possibility_tac state = gen_possibility_tac (simpset()) state

(*For harder protocols (such as SET_CR!), where we have to set up some
  nonces and keys initially*)
fun basic_possibility_tac st = st |>
    REPEAT 
    (ALLGOALS (asm_simp_tac (simpset() setSolver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac [refl, conjI]))
*}

method_setup possibility = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            gen_possibility_tac (Simplifier.get_local_simpset ctxt))) *}
    "for proving possibility theorems"



subsection{*Specialized Rewriting for Theorems About @{term analz} and Image*}

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} Un H"
by blast

lemma insert_Key_image:
     "insert (Key K) (Key`KK Un C) = Key ` (insert K KK) Un C"
by blast

text{*Needed for @{text DK_fresh_not_KeyCryptKey}*}
lemma publicKey_in_used [iff]: "Key (publicKey b A) \<in> used evs"
by auto

lemma privateKey_in_used [iff]: "Key (invKey (publicKey b A)) \<in> used evs"
by (blast intro!: initState_into_used)

text{*Reverse the normal simplification of "image" to build up (not break down)
  the set of keys.  Based on @{text analz_image_freshK_ss}, but simpler.*}
lemmas analz_image_keys_simps =
       simp_thms mem_simps --{*these two allow its use with @{text "only:"}*}
       image_insert [THEN sym] image_Un [THEN sym] 
       rangeI symKeys_neq_imp_neq
       insert_Key_singleton insert_Key_image Un_assoc [THEN sym]


(*General lemmas proved by Larry*)

subsection{*Controlled Unfolding of Abbreviations*}

text{*A set is expanded only if a relation is applied to it*}
lemma def_abbrev_simp_relation:
     "A == B ==> (A \<in> X) = (B \<in> X) &  
                 (u = A) = (u = B) &  
                 (A = u) = (B = u)"
by auto

text{*A set is expanded only if one of the given functions is applied to it*}
lemma def_abbrev_simp_function:
     "A == B  
      ==> parts (insert A X) = parts (insert B X) &  
          analz (insert A X) = analz (insert B X) &  
          keysFor (insert A X) = keysFor (insert B X)"
by auto

subsubsection{*Special Simplification Rules for @{term signCert}*}

text{*Avoids duplicating X and its components!*}
lemma parts_insert_signCert:
     "parts (insert (signCert K X) H) =  
      insert {|X, Crypt K X|} (parts (insert (Crypt K X) H))"
by (simp add: signCert_def insert_commute [of X])

text{*Avoids a case split! [X is always available]*}
lemma analz_insert_signCert:
     "analz (insert (signCert K X) H) =  
      insert {|X, Crypt K X|} (insert (Crypt K X) (analz (insert X H)))"
by (simp add: signCert_def insert_commute [of X])

lemma keysFor_insert_signCert: "keysFor (insert (signCert K X) H) = keysFor H"
by (simp add: signCert_def)

text{*Controlled rewrite rules for @{term signCert}, just the definitions
  of the others. Encryption primitives are just expanded, despite their huge
  redundancy!*}
lemmas abbrev_simps [simp] =
    parts_insert_signCert analz_insert_signCert keysFor_insert_signCert
    sign_def	 [THEN def_abbrev_simp_relation]
    sign_def	 [THEN def_abbrev_simp_function]
    signCert_def [THEN def_abbrev_simp_relation]
    signCert_def [THEN def_abbrev_simp_function]
    certC_def	 [THEN def_abbrev_simp_relation]
    certC_def	 [THEN def_abbrev_simp_function]
    cert_def	 [THEN def_abbrev_simp_relation]
    cert_def	 [THEN def_abbrev_simp_function]
    EXcrypt_def	 [THEN def_abbrev_simp_relation]
    EXcrypt_def	 [THEN def_abbrev_simp_function]
    EXHcrypt_def [THEN def_abbrev_simp_relation]
    EXHcrypt_def [THEN def_abbrev_simp_function]
    Enc_def	 [THEN def_abbrev_simp_relation]
    Enc_def	 [THEN def_abbrev_simp_function]
    EncB_def	 [THEN def_abbrev_simp_relation]
    EncB_def	 [THEN def_abbrev_simp_function]


subsubsection{*Elimination Rules for Controlled Rewriting *}

lemma Enc_partsE: 
     "!!R. [|Enc SK K EK M \<in> parts H;  
             [|Crypt K (sign SK M) \<in> parts H;  
               Crypt EK (Key K) \<in> parts H|] ==> R|]  
           ==> R"

by (unfold Enc_def, blast)

lemma EncB_partsE: 
     "!!R. [|EncB SK K EK M b \<in> parts H;  
             [|Crypt K (sign SK {|M, Hash b|}) \<in> parts H;  
               Crypt EK (Key K) \<in> parts H;  
               b \<in> parts H|] ==> R|]  
           ==> R"
by (unfold EncB_def Enc_def, blast)

lemma EXcrypt_partsE: 
     "!!R. [|EXcrypt K EK M m \<in> parts H;  
             [|Crypt K {|M, Hash m|} \<in> parts H;  
               Crypt EK {|Key K, m|} \<in> parts H|] ==> R|]  
           ==> R"
by (unfold EXcrypt_def, blast)


subsection{*Lemmas to Simplify Expressions Involving @{term analz} *}

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


subsection{*Freshness Lemmas*}

lemma in_parts_Says_imp_used:
     "[|Key K \<in> parts {X}; Says A B X \<in> set evs|] ==> Key K \<in> used evs"
by (blast intro: parts_trans dest!: Says_imp_knows_Spy [THEN parts.Inj])

text{*A useful rewrite rule with @{term analz_image_keys_simps}*}
lemma Crypt_notin_image_Key: "Crypt K X \<notin> Key ` KK"
by auto

lemma fresh_notin_analz_knows_Spy:
     "Key K \<notin> used evs ==> Key K \<notin> analz (knows Spy evs)"
by (auto dest: analz_into_parts)

end
