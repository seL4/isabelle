(*  Title:      HOL/Auth/Public
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Public Keys (common to all public-key protocols)

Private and public keys; initial states of agents
*)(*<*)
theory Public imports Event
begin
(*>*)

text {*
The function
@{text pubK} maps agents to their public keys.  The function
@{text priK} maps agents to their private keys.  It is merely
an abbreviation (cf.\ \S\ref{sec:abbreviations}) defined in terms of
@{text invKey} and @{text pubK}.
*}

consts pubK :: "agent \<Rightarrow> key"
abbreviation priK :: "agent \<Rightarrow> key"
where "priK x  \<equiv>  invKey(pubK x)"
(*<*)
overloading initState \<equiv> initState
begin

primrec initState where
        (*Agents know their private key and all public keys*)
  initState_Server:  "initState Server     =    
                         insert (Key (priK Server)) (Key ` range pubK)"
| initState_Friend:  "initState (Friend i) =    
                         insert (Key (priK (Friend i))) (Key ` range pubK)"
| initState_Spy:     "initState Spy        =    
                         (Key`invKey`pubK`bad) Un (Key ` range pubK)"

end
(*>*)

text {*
\noindent
The set @{text bad} consists of those agents whose private keys are known to
the spy.

Two axioms are asserted about the public-key cryptosystem. 
No two agents have the same public key, and no private key equals
any public key.
*}

axioms
  inj_pubK:        "inj pubK"
  priK_neq_pubK:   "priK A \<noteq> pubK B"
(*<*)
lemmas [iff] = inj_pubK [THEN inj_eq]

lemma priK_inj_eq[iff]: "(priK A = priK B) = (A=B)"
  apply safe
  apply (drule_tac f=invKey in arg_cong)
  apply simp
  done

lemmas [iff] = priK_neq_pubK priK_neq_pubK [THEN not_sym]

lemma not_symKeys_pubK[iff]: "pubK A \<notin> symKeys"
  by (simp add: symKeys_def)

lemma not_symKeys_priK[iff]: "priK A \<notin> symKeys"
  by (simp add: symKeys_def)

lemma symKeys_neq_imp_neq: "(K \<in> symKeys) \<noteq> (K' \<in> symKeys) \<Longrightarrow> K \<noteq> K'"
  by blast

lemma analz_symKeys_Decrypt: "[| Crypt K X \<in> analz H;  K \<in> symKeys;  Key K \<in> analz H |]
     ==> X \<in> analz H"
  by (auto simp add: symKeys_def)


(** "Image" equations that hold for injective functions **)

lemma invKey_image_eq[simp]: "(invKey x : invKey`A) = (x:A)"
  by auto

(*holds because invKey is injective*)
lemma pubK_image_eq[simp]: "(pubK x : pubK`A) = (x:A)"
  by auto

lemma priK_pubK_image_eq[simp]: "(priK x ~: pubK`A)"
  by auto


(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

lemma keysFor_parts_initState[simp]: "keysFor (parts (initState C)) = {}"
  apply (unfold keysFor_def)
  apply (induct C)
  apply (auto intro: range_eqI)
  done


(*** Function "spies" ***)

(*Agents see their own private keys!*)
lemma priK_in_initState[iff]: "Key (priK A) : initState A"
  by (induct A) auto

(*All public keys are visible*)
lemma spies_pubK[iff]: "Key (pubK A) : spies evs"
  by (induct evs) (simp_all add: imageI knows_Cons split: event.split)

(*Spy sees private keys of bad agents!*)
lemma Spy_spies_bad[intro!]: "A: bad ==> Key (priK A) : spies evs"
  by (induct evs) (simp_all add: imageI knows_Cons split: event.split)

lemmas [iff] = spies_pubK [THEN analz.Inj]


(*** Fresh nonces ***)

lemma Nonce_notin_initState[iff]: "Nonce N ~: parts (initState B)"
  by (induct B) auto

lemma Nonce_notin_used_empty[simp]: "Nonce N ~: used []"
  by (simp add: used_Nil)


(*** Supply fresh nonces for possibility theorems. ***)

(*In any trace, there is an upper bound N on the greatest nonce in use.*)
lemma Nonce_supply_lemma: "EX N. ALL n. N<=n --> Nonce n \<notin> used evs"
apply (induct_tac "evs")
apply (rule_tac x = 0 in exI)
apply (simp_all (no_asm_simp) add: used_Cons split add: event.split)
apply safe
apply (rule msg_Nonce_supply [THEN exE], blast elim!: add_leE)+
done

lemma Nonce_supply1: "EX N. Nonce N \<notin> used evs"
by (rule Nonce_supply_lemma [THEN exE], blast)

lemma Nonce_supply: "Nonce (@ N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply (rule someI, fast)
done


(*** Specialized rewriting for the analz_image_... theorems ***)

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} Un H"
  by blast

lemma insert_Key_image: "insert (Key K) (Key`KK Un C) = Key ` (insert K KK) Un C"
  by blast


(*Specialized methods*)

(*Tactic for possibility theorems*)
ML {*
fun possibility_tac ctxt =
    REPEAT (*omit used_Says so that Nonces start from different traces!*)
    (ALLGOALS (simp_tac (simpset_of ctxt delsimps [used_Says]))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, @{thm Nonce_supply}]));
*}

method_setup possibility = {* Scan.succeed (SIMPLE_METHOD o possibility_tac) *}
    "for proving possibility theorems"

end
(*>*)