(*  Title:      HOL/Auth/Public.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Public Keys (common to all public-key protocols)

Private and public keys; initial states of agents
*)

theory Public
imports Event
begin

lemma invKey_K: "K \<in> symKeys \<Longrightarrow> invKey K = K"
by (simp add: symKeys_def)

subsection\<open>Asymmetric Keys\<close>

datatype keymode = Signature | Encryption

consts
  publicKey :: "[keymode,agent] \<Rightarrow> key"

abbreviation
  pubEK :: "agent \<Rightarrow> key" where
  "pubEK == publicKey Encryption"

abbreviation
  pubSK :: "agent \<Rightarrow> key" where
  "pubSK == publicKey Signature"

abbreviation
  privateKey :: "[keymode, agent] \<Rightarrow> key" where
  "privateKey b A == invKey (publicKey b A)"

abbreviation
  (*BEWARE!! priEK, priSK DON'T WORK with inj, range, image, etc.*)
  priEK :: "agent \<Rightarrow> key" where
  "priEK A == privateKey Encryption A"

abbreviation
  priSK :: "agent \<Rightarrow> key" where
  "priSK A == privateKey Signature A"


text\<open>These abbreviations give backward compatibility.  They represent the
simple situation where the signature and encryption keys are the same.\<close>

abbreviation (input)
  pubK :: "agent \<Rightarrow> key" where
  "pubK A == pubEK A"

abbreviation (input)
  priK :: "agent \<Rightarrow> key" where
  "priK A == invKey (pubEK A)"


text\<open>By freeness of agents, no two agents have the same key.  Since
  \<^term>\<open>True\<noteq>False\<close>, no agent has identical signing and encryption keys\<close>
specification (publicKey)
  injective_publicKey:
    "publicKey b A = publicKey c A' \<Longrightarrow> b=c \<and> A=A'"
   apply (rule exI [of _ 
       "\<lambda>b A. 2 * case_agent 0 (\<lambda>n. n + 2) 1 A + case_keymode 0 1 b"])
   apply (auto simp add: inj_on_def split: agent.split keymode.split)
   apply presburger
   apply presburger
   done                       


axiomatization where
  (*No private key equals any public key (essential to ensure that private
    keys are private!) *)
  privateKey_neq_publicKey [iff]: "privateKey b A \<noteq> publicKey c A'"

lemmas publicKey_neq_privateKey = privateKey_neq_publicKey [THEN not_sym]
declare publicKey_neq_privateKey [iff]


subsection\<open>Basic properties of \<^term>\<open>pubK\<close> and \<^term>\<open>priK\<close>\<close>

lemma publicKey_inject [iff]: "(publicKey b A = publicKey c A') = (b=c \<and> A=A')"
by (blast dest!: injective_publicKey) 

lemma not_symKeys_pubK [iff]: "publicKey b A \<notin> symKeys"
by (simp add: symKeys_def)

lemma not_symKeys_priK [iff]: "privateKey b A \<notin> symKeys"
by (simp add: symKeys_def)

lemma symKey_neq_priEK: "K \<in> symKeys \<Longrightarrow> K \<noteq> priEK A"
by auto

lemma symKeys_neq_imp_neq: "(K \<in> symKeys) \<noteq> (K' \<in> symKeys) \<Longrightarrow> K \<noteq> K'"
by blast

lemma symKeys_invKey_iff [iff]: "(invKey K \<in> symKeys) = (K \<in> symKeys)"
  unfolding symKeys_def by auto

lemma analz_symKeys_Decrypt:
     "\<lbrakk>Crypt K X \<in> analz H;  K \<in> symKeys;  Key K \<in> analz H\<rbrakk>  
      \<Longrightarrow> X \<in> analz H"
by (auto simp add: symKeys_def)



subsection\<open>"Image" equations that hold for injective functions\<close>

lemma invKey_image_eq [simp]: "(invKey x \<in> invKey`A) = (x \<in> A)"
by auto

(*holds because invKey is injective*)
lemma publicKey_image_eq [simp]:
     "(publicKey b x \<in> publicKey c ` AA) = (b=c \<and> x \<in> AA)"
by auto

lemma privateKey_notin_image_publicKey [simp]: "privateKey b x \<notin> publicKey c ` AA"
by auto

lemma privateKey_image_eq [simp]:
     "(privateKey b A \<in> invKey ` publicKey c ` AS) = (b=c \<and> A\<in>AS)"
by auto

lemma publicKey_notin_image_privateKey [simp]: "publicKey b A \<notin> invKey ` publicKey c ` AS"
by auto


subsection\<open>Symmetric Keys\<close>

text\<open>For some protocols, it is convenient to equip agents with symmetric as
well as asymmetric keys.  The theory \<open>Shared\<close> assumes that all keys
are symmetric.\<close>

consts
  shrK    :: "agent => key"    \<comment> \<open>long-term shared keys\<close>

specification (shrK)
  inj_shrK: "inj shrK"
  \<comment> \<open>No two agents have the same long-term key\<close>
   apply (rule exI [of _ "case_agent 0 (\<lambda>n. n + 2) 1"]) 
   apply (simp add: inj_on_def split: agent.split) 
   done

axiomatization where
  sym_shrK [iff]: "shrK X \<in> symKeys" \<comment> \<open>All shared keys are symmetric\<close>

text\<open>Injectiveness: Agents' long-term keys are distinct.\<close>
lemmas shrK_injective = inj_shrK [THEN inj_eq]
declare shrK_injective [iff]

lemma invKey_shrK [simp]: "invKey (shrK A) = shrK A"
by (simp add: invKey_K) 

lemma analz_shrK_Decrypt:
     "\<lbrakk>Crypt (shrK A) X \<in> analz H; Key(shrK A) \<in> analz H\<rbrakk> \<Longrightarrow> X \<in> analz H"
by auto

lemma analz_Decrypt':
     "\<lbrakk>Crypt K X \<in> analz H; K \<in> symKeys; Key K \<in> analz H\<rbrakk> \<Longrightarrow> X \<in> analz H"
by (auto simp add: invKey_K)

lemma priK_neq_shrK [iff]: "shrK A \<noteq> privateKey b C"
by (simp add: symKeys_neq_imp_neq)

lemmas shrK_neq_priK = priK_neq_shrK [THEN not_sym]
declare shrK_neq_priK [simp]

lemma pubK_neq_shrK [iff]: "shrK A \<noteq> publicKey b C"
by (simp add: symKeys_neq_imp_neq)

lemmas shrK_neq_pubK = pubK_neq_shrK [THEN not_sym]
declare shrK_neq_pubK [simp]

lemma priEK_noteq_shrK [simp]: "priEK A \<noteq> shrK B" 
by auto

lemma publicKey_notin_image_shrK [simp]: "publicKey b x \<notin> shrK ` AA"
by auto

lemma privateKey_notin_image_shrK [simp]: "privateKey b x \<notin> shrK ` AA"
by auto

lemma shrK_notin_image_publicKey [simp]: "shrK x \<notin> publicKey b ` AA"
by auto

lemma shrK_notin_image_privateKey [simp]: "shrK x \<notin> invKey ` publicKey b ` AA" 
by auto

lemma shrK_image_eq [simp]: "(shrK x \<in> shrK ` AA) = (x \<in> AA)"
by auto

text\<open>For some reason, moving this up can make some proofs loop!\<close>
declare invKey_K [simp]


subsection\<open>Initial States of Agents\<close>

text\<open>Note: for all practical purposes, all that matters is the initial
knowledge of the Spy.  All other agents are automata, merely following the
protocol.\<close>

overloading
  initState \<equiv> initState
begin

primrec initState where
        (*Agents know their private key and all public keys*)
  initState_Server:
    "initState Server     =    
       {Key (priEK Server), Key (priSK Server)} \<union> 
       (Key ` range pubEK) \<union> (Key ` range pubSK) \<union> (Key ` range shrK)"

| initState_Friend:
    "initState (Friend i) =    
       {Key (priEK(Friend i)), Key (priSK(Friend i)), Key (shrK(Friend i))} \<union> 
       (Key ` range pubEK) \<union> (Key ` range pubSK)"

| initState_Spy:
    "initState Spy        =    
       (Key ` invKey ` pubEK ` bad) \<union> (Key ` invKey ` pubSK ` bad) \<union> 
       (Key ` shrK ` bad) \<union> 
       (Key ` range pubEK) \<union> (Key ` range pubSK)"

end


text\<open>These lemmas allow reasoning about \<^term>\<open>used evs\<close> rather than
   \<^term>\<open>knows Spy evs\<close>, which is useful when there are private Notes. 
   Because they depend upon the definition of \<^term>\<open>initState\<close>, they cannot
   be moved up.\<close>

lemma used_parts_subset_parts [rule_format]:
     "\<forall>X \<in> used evs. parts {X} \<subseteq> used evs"
apply (induct evs) 
 prefer 2
 apply (simp add: used_Cons split: event.split)
 apply (metis Un_iff empty_subsetI insert_subset le_supI1 le_supI2 parts_subset_iff)
txt\<open>Base case\<close>
apply (auto dest!: parts_cut simp add: used_Nil) 
done

lemma MPair_used_D: "\<lbrace>X,Y\<rbrace> \<in> used H \<Longrightarrow> X \<in> used H \<and> Y \<in> used H"
by (drule used_parts_subset_parts, simp, blast)

text\<open>There was a similar theorem in Event.thy, so perhaps this one can
  be moved up if proved directly by induction.\<close>
lemma MPair_used [elim!]:
     "\<lbrakk>\<lbrace>X,Y\<rbrace> \<in> used H;
         \<lbrakk>X \<in> used H; Y \<in> used H\<rbrakk> \<Longrightarrow> P\<rbrakk> 
      \<Longrightarrow> P"
by (blast dest: MPair_used_D) 


text\<open>Rewrites should not refer to  \<^term>\<open>initState(Friend i)\<close> because
  that expression is not in normal form.\<close>

lemma keysFor_parts_initState [simp]: "keysFor (parts (initState C)) = {}"
unfolding keysFor_def
apply (induct_tac "C")
apply (auto intro: range_eqI)
done

lemma Crypt_notin_initState: "Crypt K X \<notin> parts (initState B)"
by (induct B, auto)

lemma Crypt_notin_used_empty [simp]: "Crypt K X \<notin> used []"
by (simp add: Crypt_notin_initState used_Nil)

(*** Basic properties of shrK ***)

(*Agents see their own shared keys!*)
lemma shrK_in_initState [iff]: "Key (shrK A) \<in> initState A"
by (induct_tac "A", auto)

lemma shrK_in_knows [iff]: "Key (shrK A) \<in> knows A evs"
by (simp add: initState_subset_knows [THEN subsetD])

lemma shrK_in_used [iff]: "Key (shrK A) \<in> used evs"
by (rule initState_into_used, blast)


(** Fresh keys never clash with long-term shared keys **)

(*Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
  from long-term shared keys*)
lemma Key_not_used [simp]: "Key K \<notin> used evs \<Longrightarrow> K \<notin> range shrK"
by blast

lemma shrK_neq: "Key K \<notin> used evs \<Longrightarrow> shrK B \<noteq> K"
by blast

lemmas neq_shrK = shrK_neq [THEN not_sym]
declare neq_shrK [simp]


subsection\<open>Function \<^term>\<open>spies\<close>\<close>

lemma not_SignatureE [elim!]: "b \<noteq> Signature \<Longrightarrow> b = Encryption"
  by (cases b, auto) 

text\<open>Agents see their own private keys!\<close>
lemma priK_in_initState [iff]: "Key (privateKey b A) \<in> initState A"
  by (cases A, auto)

text\<open>Agents see all public keys!\<close>
lemma publicKey_in_initState [iff]: "Key (publicKey b A) \<in> initState B"
  by (cases B, auto) 

text\<open>All public keys are visible\<close>
lemma spies_pubK [iff]: "Key (publicKey b A) \<in> spies evs"
apply (induct_tac "evs")
apply (auto simp add: imageI knows_Cons split: event.split)
done

lemmas analz_spies_pubK = spies_pubK [THEN analz.Inj]
declare analz_spies_pubK [iff]

text\<open>Spy sees private keys of bad agents!\<close>
lemma Spy_spies_bad_privateKey [intro!]:
     "A \<in> bad \<Longrightarrow> Key (privateKey b A) \<in> spies evs"
apply (induct_tac "evs")
apply (auto simp add: imageI knows_Cons split: event.split)
done

text\<open>Spy sees long-term shared keys of bad agents!\<close>
lemma Spy_spies_bad_shrK [intro!]:
     "A \<in> bad \<Longrightarrow> Key (shrK A) \<in> spies evs"
apply (induct_tac "evs")
apply (simp_all add: imageI knows_Cons split: event.split)
done

lemma publicKey_into_used [iff] :"Key (publicKey b A) \<in> used evs"
apply (rule initState_into_used)
apply (rule publicKey_in_initState [THEN parts.Inj])
done

lemma privateKey_into_used [iff]: "Key (privateKey b A) \<in> used evs"
apply(rule initState_into_used)
apply(rule priK_in_initState [THEN parts.Inj])
done

(*For case analysis on whether or not an agent is compromised*)
lemma Crypt_Spy_analz_bad:
     "\<lbrakk>Crypt (shrK A) X \<in> analz (knows Spy evs);  A \<in> bad\<rbrakk>  
      \<Longrightarrow> X \<in> analz (knows Spy evs)"
by force


subsection\<open>Fresh Nonces\<close>

lemma Nonce_notin_initState [iff]: "Nonce N \<notin> parts (initState B)"
by (induct_tac "B", auto)

lemma Nonce_notin_used_empty [simp]: "Nonce N \<notin> used []"
by (simp add: used_Nil)


subsection\<open>Supply fresh nonces for possibility theorems\<close>

text\<open>In any trace, there is an upper bound N on the greatest nonce in use\<close>
lemma Nonce_supply_lemma: "\<exists>N. \<forall>n. N\<le>n \<longrightarrow> Nonce n \<notin> used evs"
apply (induct_tac "evs")
apply (rule_tac x = 0 in exI)
apply (simp_all (no_asm_simp) add: used_Cons split: event.split)
apply safe
apply (rule msg_Nonce_supply [THEN exE], blast elim!: add_leE)+
done

lemma Nonce_supply1: "\<exists>N. Nonce N \<notin> used evs"
by (rule Nonce_supply_lemma [THEN exE], blast)

lemma Nonce_supply: "Nonce (SOME N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply (rule someI, fast)
done

subsection\<open>Specialized Rewriting for Theorems About \<^term>\<open>analz\<close> and Image\<close>

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} \<union> H"
by blast

lemma insert_Key_image: "insert (Key K) (Key`KK \<union> C) = Key ` (insert K KK) \<union> C"
by blast


lemma Crypt_imp_keysFor :"\<lbrakk>Crypt K X \<in> H; K \<in> symKeys\<rbrakk> \<Longrightarrow> K \<in> keysFor H"
by (drule Crypt_imp_invKey_keysFor, simp)

text\<open>Lemma for the trivial direction of the if-and-only-if of the 
Session Key Compromise Theorem\<close>
lemma analz_image_freshK_lemma:
     "(Key K \<in> analz (Key`nE \<union> H)) \<longrightarrow> (K \<in> nE | Key K \<in> analz H)  \<Longrightarrow>  
         (Key K \<in> analz (Key`nE \<union> H)) = (K \<in> nE | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

lemmas analz_image_freshK_simps =
       simp_thms mem_simps \<comment> \<open>these two allow its use with \<open>only:\<close>\<close>
       disj_comms 
       image_insert [THEN sym] image_Un [THEN sym] empty_subsetI insert_subset
       analz_insert_eq Un_upper2 [THEN analz_mono, THEN subsetD]
       insert_Key_singleton 
       Key_not_used insert_Key_image Un_assoc [THEN sym]

ML \<open>
structure Public =
struct

val analz_image_freshK_ss =
  simpset_of
   (\<^context> delsimps @{thms image_insert image_Un}
    delsimps @{thms imp_disjL}    (*reduces blow-up*)
    addsimps @{thms analz_image_freshK_simps})

(*Tactic for possibility theorems*)
fun possibility_tac ctxt =
    REPEAT (*omit used_Says so that Nonces start from different traces!*)
    (ALLGOALS (simp_tac (ctxt setSolver safe_solver delsimps [@{thm used_Says}]))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac ctxt [refl, conjI, @{thm Nonce_supply}]))

(*For harder protocols (such as Recur) where we have to set up some
  nonces and keys initially*)
fun basic_possibility_tac ctxt =
    REPEAT 
    (ALLGOALS (asm_simp_tac (ctxt setSolver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac ctxt [refl, conjI]))

end
\<close>

method_setup analz_freshK = \<open>
    Scan.succeed (fn ctxt =>
     (SIMPLE_METHOD
      (EVERY [REPEAT_FIRST (resolve_tac ctxt @{thms allI ballI impI}),
          REPEAT_FIRST (resolve_tac ctxt @{thms analz_image_freshK_lemma}),
          ALLGOALS (asm_simp_tac (put_simpset Public.analz_image_freshK_ss ctxt))])))\<close>
    "for proving the Session Key Compromise theorem"


subsection\<open>Specialized Methods for Possibility Theorems\<close>

method_setup possibility = \<open>
    Scan.succeed (SIMPLE_METHOD o Public.possibility_tac)\<close>
    "for proving possibility theorems"

method_setup basic_possibility = \<open>
    Scan.succeed (SIMPLE_METHOD o Public.basic_possibility_tac)\<close>
    "for proving possibility theorems"

end
