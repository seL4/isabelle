(*  Title:      HOL/Auth/Public
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Public Keys (common to all public-key protocols)

Private and public keys; initial states of agents
*)

theory Public = Event:

subsection{*Asymmetric Keys*}

consts
  (*the bool is TRUE if a signing key*)
  publicKey :: "[bool,agent] => key"

syntax
  pubEK :: "agent => key"
  pubSK :: "agent => key"

  privateKey :: "[bool,agent] => key"
  priEK :: "agent => key"
  priSK :: "agent => key"

translations
  "pubEK"  == "publicKey False"
  "pubSK"  == "publicKey True"

  (*BEWARE!! priEK, priSK DON'T WORK with inj, range, image, etc.*)
  "privateKey b A" == "invKey (publicKey b A)"
  "priEK A"  == "privateKey False A"
  "priSK A"  == "privateKey True A"


text{*These translations give backward compatibility.  They represent the
simple situation where the signature and encryption keys are the same.*}
syntax
  pubK :: "agent => key"
  priK :: "agent => key"

translations
  "pubK A" == "pubEK A"
  "priK A" == "invKey (pubEK A)"


axioms
  (*By freeness of agents, no two agents have the same key.  Since true\<noteq>false,
    no agent has identical signing and encryption keys*)
  injective_publicKey:
    "publicKey b A = publicKey c A' ==> b=c & A=A'"

  (*No private key equals any public key (essential to ensure that private
    keys are private!) *)
  privateKey_neq_publicKey [iff]: "privateKey b A \<noteq> publicKey c A'"




(*** Basic properties of pubK & priK ***)

lemma [iff]: "(publicKey b A = publicKey c A') = (b=c & A=A')"
by (blast dest!: injective_publicKey) 

lemma [iff]:
    "(privateKey b A = privateKey c A') = (b=c & A=A')"
apply (rule iffI) 
apply (drule_tac f = "invKey" in arg_cong)
apply (auto ); 
done

declare privateKey_neq_publicKey [THEN not_sym, iff]

lemma not_symKeys_pubK [iff]: "publicKey b A \<notin> symKeys"
apply (simp add: symKeys_def)
done

lemma not_symKeys_priK [iff]: "privateKey b A \<notin> symKeys"
apply (simp add: symKeys_def)
done

lemma symKey_neq_priEK: "K \<in> symKeys ==> K \<noteq> priEK A"
by auto

lemma symKeys_neq_imp_neq: "(K \<in> symKeys) \<noteq> (K' \<in> symKeys) ==> K \<noteq> K'"
apply blast
done

lemma symKeys_invKey_iff [iff]: "(invKey K \<in> symKeys) = (K \<in> symKeys)"
apply (unfold symKeys_def)
apply auto
done

lemma analz_symKeys_Decrypt:
     "[| Crypt K X \<in> analz H;  K \<in> symKeys;  Key K \<in> analz H |]  
      ==> X \<in> analz H"
by (auto simp add: symKeys_def)



subsection{*"Image" equations that hold for injective functions*}

lemma invKey_image_eq [simp]: "(invKey x \<in> invKey`A) = (x \<in> A)"
apply auto
done

(*holds because invKey is injective*)
lemma publicKey_image_eq [simp]:
     "(publicKey b x \<in> publicKey c ` AA) = (b=c & x \<in> AA)"
by auto

lemma privateKey_notin_image_publicKey [simp]: "privateKey b x \<notin> publicKey c ` AA"
apply auto
done

lemma privateKey_image_eq [simp]:
     "(privateKey b A \<in> invKey ` publicKey c ` AS) = (b=c & A\<in>AS)"
by auto

lemma publicKey_notin_image_privateKey [simp]: "publicKey b A \<notin> invKey ` publicKey c ` AS"
apply auto
done


subsection{*Symmetric Keys*}

text{*For some protocols, it is convenient to equip agents with symmetric as
well as asymmetric keys.  The theory @{text Shared} assumes that all keys
are symmetric.*}

consts
  shrK    :: "agent => key"    --{*long-term shared keys*}

axioms
  inj_shrK: "inj shrK"	             --{*No two agents have the same key*}
  sym_shrK [iff]: "shrK X \<in> symKeys" --{*All shared keys are symmetric*}

(*Injectiveness: Agents' long-term keys are distinct.*)
declare inj_shrK [THEN inj_eq, iff]

lemma priK_neq_shrK [iff]: "shrK A \<noteq> privateKey b C"
apply (simp add: symKeys_neq_imp_neq)
done

declare priK_neq_shrK [THEN not_sym, simp]

lemma pubK_neq_shrK [iff]: "shrK A \<noteq> publicKey b C"
apply (simp add: symKeys_neq_imp_neq)
done

declare pubK_neq_shrK [THEN not_sym, simp]

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


subsection{*Initial States of Agents*}

text{*Note: for all practical purposes, all that matters is the initial
knowledge of the Spy.  All other agents are automata, merely following the
protocol.*}

primrec
        (*Agents know their private key and all public keys*)
  initState_Server:
    "initState Server     =    
       {Key (priEK Server), Key (priSK Server)} \<union> 
       (Key ` range pubEK) \<union> (Key ` range pubSK) \<union> (Key ` range shrK)"

  initState_Friend:
    "initState (Friend i) =    
       {Key (priEK(Friend i)), Key (priSK(Friend i)), Key (shrK(Friend i))} \<union> 
       (Key ` range pubEK) \<union> (Key ` range pubSK)"

  initState_Spy:
    "initState Spy        =    
       (Key ` invKey ` pubEK ` bad) \<union> (Key ` invKey ` pubSK ` bad) \<union> 
       (Key ` shrK ` bad) \<union> 
       (Key ` range pubEK) \<union> (Key ` range pubSK)"



text{*These lemmas allow reasoning about @{term "used evs"} rather than
   @{term "knows Spy evs"}, which is useful when there are private Notes. *}

lemma used_parts_subset_parts [rule_format]:
     "\<forall>X \<in> used evs. parts {X} \<subseteq> used evs"
apply (induct evs) 
 prefer 2
 apply (simp add: used_Cons)
 apply (rule ballI)  
 apply (case_tac a, auto)
 apply (drule parts_cut, assumption, simp) 
 apply (drule parts_cut, assumption, simp) 
txt{*Base case*}
apply (simp add: used_Nil, clarify) 
apply (rename_tac B) 
apply (rule_tac x=B in exI) 
apply (case_tac B, auto) 
done

lemma MPair_used_D: "{|X,Y|} \<in> used H ==> X \<in> used H & Y \<in> used H"
by (drule used_parts_subset_parts, simp, blast)

lemma MPair_used [elim!]:
     "[| {|X,Y|} \<in> used H;
         [| X \<in> used H; Y \<in> used H |] ==> P |] 
      ==> P"
by (blast dest: MPair_used_D) 


text{*Rewrites should not refer to  @{term "initState(Friend i)"} because
  that expression is not in normal form.*}

lemma keysFor_parts_initState [simp]: "keysFor (parts (initState C)) = {}"
apply (unfold keysFor_def)
apply (induct_tac "C")
apply (auto intro: range_eqI)
done

lemma Crypt_notin_initState: "Crypt K X \<notin> parts (initState B)"
by (induct B, auto)


(*** Basic properties of shrK ***)

(*Agents see their own shared keys!*)
lemma shrK_in_initState [iff]: "Key (shrK A) \<in> initState A"
apply (induct_tac "A")
apply auto
done

lemma shrK_in_knows [iff]: "Key (shrK A) \<in> knows A evs"
by (simp add: initState_subset_knows [THEN subsetD])

lemma shrK_in_used [iff]: "Key (shrK A) \<in> used evs"
apply (rule initState_into_used)
apply blast
done

(** Fresh keys never clash with long-term shared keys **)

(*Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
  from long-term shared keys*)
lemma Key_not_used: "Key K \<notin> used evs ==> K \<notin> range shrK"
apply blast
done

lemma shrK_neq: "Key K \<notin> used evs ==> shrK B \<noteq> K"
apply blast
done



subsection{*Function @{term spies} *}

text{*Agents see their own private keys!*}
lemma priK_in_initState [iff]: "Key (privateKey b A) \<in> initState A"
apply (induct_tac "A")
apply auto
done

text{*Agents see all public keys!*}
lemma publicKey_in_initState [iff]: "Key (publicKey b A) \<in> initState B"
apply (case_tac "B")
apply auto
done

text{*All public keys are visible*}
lemma spies_pubK [iff]: "Key (publicKey b A) \<in> spies evs"
apply (induct_tac "evs")
apply (simp_all add: imageI knows_Cons split add: event.split)
done

declare spies_pubK [THEN analz.Inj, iff]

text{*Spy sees private keys of bad agents!*}
lemma Spy_spies_bad_privateKey [intro!]:
     "A \<in> bad ==> Key (privateKey b A) \<in> spies evs"
apply (induct_tac "evs")
apply (simp_all add: imageI knows_Cons split add: event.split)
done

text{*Spy sees long-term shared keys of bad agents!*}
lemma Spy_spies_bad_shrK [intro!]:
     "A \<in> bad ==> Key (shrK A) \<in> spies evs"
apply (induct_tac "evs")
apply (simp_all add: imageI knows_Cons split add: event.split)
done

lemma publicKey_into_used [iff] :"Key (publicKey b A) \<in> used evs"
apply (rule initState_into_used)
apply (rule publicKey_in_initState [THEN parts.Inj])
done

lemma privateKey_into_used [iff]: "Key (privateKey b A) \<in> used evs"
apply(rule initState_into_used)
apply(rule priK_in_initState [THEN parts.Inj])
done


subsection{*Fresh Nonces*}

lemma Nonce_notin_initState [iff]: "Nonce N \<notin> parts (initState B)"
apply (induct_tac "B")
apply auto
done

lemma Nonce_notin_used_empty [simp]: "Nonce N \<notin> used []"
apply (simp add: used_Nil)
done


subsection{*Supply fresh nonces for possibility theorems*}

text{*In any trace, there is an upper bound N on the greatest nonce in use*}
lemma Nonce_supply_lemma: "EX N. ALL n. N<=n --> Nonce n \<notin> used evs"
apply (induct_tac "evs")
apply (rule_tac x = "0" in exI)
apply (simp_all (no_asm_simp) add: used_Cons split add: event.split)
apply safe
apply (rule msg_Nonce_supply [THEN exE], blast elim!: add_leE)+
done

lemma Nonce_supply1: "EX N. Nonce N \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply blast
done

lemma Nonce_supply: "Nonce (@ N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply (rule someI)
apply fast
done

subsection{*Specialized rewriting for the analz_image_... theorems*}

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} Un H"
apply blast
done

lemma insert_Key_image: "insert (Key K) (Key`KK \<union> C) = Key ` (insert K KK) \<union> C"
apply blast
done

ML
{*
val Key_not_used = thm "Key_not_used";
val insert_Key_singleton = thm "insert_Key_singleton";
val insert_Key_image = thm "insert_Key_image";
*}

(*
val not_symKeys_pubK = thm "not_symKeys_pubK";
val not_symKeys_priK = thm "not_symKeys_priK";
val symKeys_neq_imp_neq = thm "symKeys_neq_imp_neq";
val analz_symKeys_Decrypt = thm "analz_symKeys_Decrypt";
val invKey_image_eq = thm "invKey_image_eq";
val pubK_image_eq = thm "pubK_image_eq";
val priK_pubK_image_eq = thm "priK_pubK_image_eq";
val keysFor_parts_initState = thm "keysFor_parts_initState";
val priK_in_initState = thm "priK_in_initState";
val spies_pubK = thm "spies_pubK";
val Spy_spies_bad = thm "Spy_spies_bad";
val Nonce_notin_initState = thm "Nonce_notin_initState";
val Nonce_notin_used_empty = thm "Nonce_notin_used_empty";

*)


lemma invKey_K [simp]: "K \<in> symKeys ==> invKey K = K"
by (simp add: symKeys_def)

lemma Crypt_imp_keysFor :"[|K \<in> symKeys; Crypt K X \<in> H|] ==> K \<in> keysFor H"
apply (drule Crypt_imp_invKey_keysFor, simp)
done


subsection{*Specialized Methods for Possibility Theorems*}

ML
{*
val Nonce_supply1 = thm "Nonce_supply1";
val Nonce_supply = thm "Nonce_supply";

(*Tactic for possibility theorems (Isar interface)*)
fun gen_possibility_tac ss state = state |>
    REPEAT (*omit used_Says so that Nonces start from different traces!*)
    (ALLGOALS (simp_tac (ss delsimps [used_Says]))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, Nonce_supply]))

(*Tactic for possibility theorems (ML script version)*)
fun possibility_tac state = gen_possibility_tac (simpset()) state
*}

method_setup possibility = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            gen_possibility_tac (Simplifier.get_local_simpset ctxt))) *}
    "for proving possibility theorems"



ML
{*
bind_thms ("analz_image_freshK_simps",
           simp_thms @ mem_simps @  (*these two allow its use with only:*)
           disj_comms @
           [image_insert RS sym, image_Un RS sym, empty_subsetI, insert_subset,
            analz_insert_eq, impOfSubs (Un_upper2 RS analz_mono),
	    insert_Key_singleton, 
            Key_not_used, insert_Key_image, Un_assoc RS sym]);

val analz_image_freshK_ss =
     simpset() delsimps [image_insert, image_Un]
	       delsimps [imp_disjL]    (*reduces blow-up*)
	       addsimps analz_image_freshK_simps;
*}

end
