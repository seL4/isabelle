(*  Title:      HOL/Auth/Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Shared, long-term keys; initial states of agents
*)

theory Shared = Event:

consts
  shrK    :: "agent => key"  (*symmetric keys*);

specification (shrK)
  inj_shrK: "inj shrK"
  --{*No two agents have the same long-term key*}
   apply (rule exI [of _ "agent_case 0 (\<lambda>n. n + 2) 1"]) 
   apply (simp add: inj_on_def split: agent.split) 
   done

text{*All keys are symmetric*}

defs  all_symmetric_def: "all_symmetric == True"

lemma isSym_keys: "K \<in> symKeys"	
by (simp add: symKeys_def all_symmetric_def invKey_symmetric) 

text{*Server knows all long-term keys; other agents know only their own*}
primrec
  initState_Server:  "initState Server     = Key ` range shrK"
  initState_Friend:  "initState (Friend i) = {Key (shrK (Friend i))}"
  initState_Spy:     "initState Spy        = Key`shrK`bad"


subsection{*Basic properties of shrK*}

(*Injectiveness: Agents' long-term keys are distinct.*)
declare inj_shrK [THEN inj_eq, iff]

lemma invKey_K [simp]: "invKey K = K"
apply (insert isSym_keys)
apply (simp add: symKeys_def) 
done


lemma analz_Decrypt' [dest]:
     "[| Crypt K X \<in> analz H;  Key K  \<in> analz H |] ==> X \<in> analz H"
by auto

text{*Now cancel the @{text dest} attribute given to
 @{text analz.Decrypt} in its declaration.*}
ML
{*
Delrules [analz.Decrypt];
*}

text{*Rewrites should not refer to  @{term "initState(Friend i)"} because
  that expression is not in normal form.*}

lemma keysFor_parts_initState [simp]: "keysFor (parts (initState C)) = {}"
apply (unfold keysFor_def)
apply (induct_tac "C", auto)
done

(*Specialized to shared-key model: no @{term invKey}*)
lemma keysFor_parts_insert:
     "[| K \<in> keysFor (parts (insert X G));  X \<in> synth (analz H) |] \
\     ==> K \<in> keysFor (parts (G \<union> H)) | Key K \<in> parts H";
by (force dest: Event.keysFor_parts_insert)  

lemma Crypt_imp_keysFor: "Crypt K X \<in> H ==> K \<in> keysFor H"
by (drule Crypt_imp_invKey_keysFor, simp)


subsection{*Function "knows"*}

(*Spy sees shared keys of agents!*)
lemma Spy_knows_Spy_bad [intro!]: "A: bad ==> Key (shrK A) \<in> knows Spy evs"
apply (induct_tac "evs")
apply (simp_all (no_asm_simp) add: imageI knows_Cons split add: event.split)
done

(*For case analysis on whether or not an agent is compromised*)
lemma Crypt_Spy_analz_bad: "[| Crypt (shrK A) X \<in> analz (knows Spy evs);  A: bad |]  
      ==> X \<in> analz (knows Spy evs)"
apply (force dest!: analz.Decrypt)
done


(** Fresh keys never clash with long-term shared keys **)

(*Agents see their own shared keys!*)
lemma shrK_in_initState [iff]: "Key (shrK A) \<in> initState A"
by (induct_tac "A", auto)

lemma shrK_in_used [iff]: "Key (shrK A) \<in> used evs"
by (rule initState_into_used, blast)

(*Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
  from long-term shared keys*)
lemma Key_not_used [simp]: "Key K \<notin> used evs ==> K \<notin> range shrK"
by blast

lemma shrK_neq [simp]: "Key K \<notin> used evs ==> shrK B \<noteq> K"
by blast

declare shrK_neq [THEN not_sym, simp]


subsection{*Fresh nonces*}

lemma Nonce_notin_initState [iff]: "Nonce N \<notin> parts (initState B)"
by (induct_tac "B", auto)

lemma Nonce_notin_used_empty [simp]: "Nonce N \<notin> used []"
apply (simp (no_asm) add: used_Nil)
done


subsection{*Supply fresh nonces for possibility theorems.*}

(*In any trace, there is an upper bound N on the greatest nonce in use.*)
lemma Nonce_supply_lemma: "\<exists>N. ALL n. N<=n --> Nonce n \<notin> used evs"
apply (induct_tac "evs")
apply (rule_tac x = 0 in exI)
apply (simp_all (no_asm_simp) add: used_Cons split add: event.split)
apply safe
apply (rule msg_Nonce_supply [THEN exE], blast elim!: add_leE)+
done

lemma Nonce_supply1: "\<exists>N. Nonce N \<notin> used evs"
by (rule Nonce_supply_lemma [THEN exE], blast)

lemma Nonce_supply2: "\<exists>N N'. Nonce N \<notin> used evs & Nonce N' \<notin> used evs' & N \<noteq> N'"
apply (cut_tac evs = evs in Nonce_supply_lemma)
apply (cut_tac evs = "evs'" in Nonce_supply_lemma, clarify)
apply (rule_tac x = N in exI)
apply (rule_tac x = "Suc (N+Na) " in exI)
apply (simp (no_asm_simp) add: less_not_refl3 le_add1 le_add2 less_Suc_eq_le)
done

lemma Nonce_supply3: "\<exists>N N' N''. Nonce N \<notin> used evs & Nonce N' \<notin> used evs' &  
                    Nonce N'' \<notin> used evs'' & N \<noteq> N' & N' \<noteq> N'' & N \<noteq> N''"
apply (cut_tac evs = evs in Nonce_supply_lemma)
apply (cut_tac evs = "evs'" in Nonce_supply_lemma)
apply (cut_tac evs = "evs''" in Nonce_supply_lemma, clarify)
apply (rule_tac x = N in exI)
apply (rule_tac x = "Suc (N+Na) " in exI)
apply (rule_tac x = "Suc (Suc (N+Na+Nb))" in exI)
apply (simp (no_asm_simp) add: less_not_refl3 le_add1 le_add2 less_Suc_eq_le)
done

lemma Nonce_supply: "Nonce (@ N. Nonce N \<notin> used evs) \<notin> used evs"
apply (rule Nonce_supply_lemma [THEN exE])
apply (rule someI, blast)
done

subsection{*Supply fresh keys for possibility theorems.*}

axioms
  Key_supply_ax:  "finite KK ==> \<exists>K. K \<notin> KK & Key K \<notin> used evs"
  --{*Unlike the corresponding property of nonces, this cannot be proved.
    We have infinitely many agents and there is nothing to stop their
    long-term keys from exhausting all the natural numbers.  The axiom
    assumes that their keys are dispersed so as to leave room for infinitely
    many fresh session keys.  We could, alternatively, restrict agents to
    an unspecified finite number.  We could however replace @{term"used evs"} 
    by @{term "used []"}.*}

lemma Key_supply1: "\<exists>K. Key K \<notin> used evs"
by (rule Finites.emptyI [THEN Key_supply_ax, THEN exE], blast)

lemma Key_supply2: "\<exists>K K'. Key K \<notin> used evs & Key K' \<notin> used evs' & K \<noteq> K'"
apply (cut_tac evs = evs in Finites.emptyI [THEN Key_supply_ax])
apply (erule exE)
apply (cut_tac evs="evs'" in Finites.emptyI [THEN Finites.insertI, THEN Key_supply_ax], auto) 
done

lemma Key_supply3: "\<exists>K K' K''. Key K \<notin> used evs & Key K' \<notin> used evs' &  
                       Key K'' \<notin> used evs'' & K \<noteq> K' & K' \<noteq> K'' & K \<noteq> K''"
apply (cut_tac evs = evs in Finites.emptyI [THEN Key_supply_ax])
apply (erule exE)
(*Blast_tac requires instantiation of the keys for some reason*)
apply (cut_tac evs="evs'" and a1 = K in Finites.emptyI [THEN Finites.insertI, THEN Key_supply_ax])
apply (erule exE)
apply (cut_tac evs = "evs''" and a1 = Ka and a2 = K 
       in Finites.emptyI [THEN Finites.insertI, THEN Finites.insertI, THEN Key_supply_ax], blast)
done

lemma Key_supply: "Key (@ K. Key K \<notin> used evs) \<notin> used evs"
apply (rule Finites.emptyI [THEN Key_supply_ax, THEN exE])
apply (rule someI, blast)
done

subsection{*Tactics for possibility theorems*}

ML
{*
val inj_shrK      = thm "inj_shrK";
val isSym_keys    = thm "isSym_keys";
val Key_supply_ax = thm "Key_supply_ax";
val Key_supply = thm "Key_supply";
val Nonce_supply = thm "Nonce_supply";
val invKey_K = thm "invKey_K";
val analz_Decrypt' = thm "analz_Decrypt'";
val keysFor_parts_initState = thm "keysFor_parts_initState";
val keysFor_parts_insert = thm "keysFor_parts_insert";
val Crypt_imp_keysFor = thm "Crypt_imp_keysFor";
val Spy_knows_Spy_bad = thm "Spy_knows_Spy_bad";
val Crypt_Spy_analz_bad = thm "Crypt_Spy_analz_bad";
val shrK_in_initState = thm "shrK_in_initState";
val shrK_in_used = thm "shrK_in_used";
val Key_not_used = thm "Key_not_used";
val shrK_neq = thm "shrK_neq";
val Nonce_notin_initState = thm "Nonce_notin_initState";
val Nonce_notin_used_empty = thm "Nonce_notin_used_empty";
val Nonce_supply_lemma = thm "Nonce_supply_lemma";
val Nonce_supply1 = thm "Nonce_supply1";
val Nonce_supply2 = thm "Nonce_supply2";
val Nonce_supply3 = thm "Nonce_supply3";
val Nonce_supply = thm "Nonce_supply";
val Key_supply1 = thm "Key_supply1";
val Key_supply2 = thm "Key_supply2";
val Key_supply3 = thm "Key_supply3";
val Key_supply = thm "Key_supply";
*}


ML
{*
(*Omitting used_Says makes the tactic much faster: it leaves expressions
    such as  Nonce ?N \<notin> used evs that match Nonce_supply*)
fun gen_possibility_tac ss state = state |>
   (REPEAT 
    (ALLGOALS (simp_tac (ss delsimps [used_Says, used_Notes, used_Gets] 
                         setSolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, Nonce_supply, Key_supply])))

(*Tactic for possibility theorems (ML script version)*)
fun possibility_tac state = gen_possibility_tac (simpset()) state

(*For harder protocols (such as Recur) where we have to set up some
  nonces and keys initially*)
fun basic_possibility_tac st = st |>
    REPEAT 
    (ALLGOALS (asm_simp_tac (simpset() setSolver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac [refl, conjI]))
*}

subsection{*Specialized Rewriting for Theorems About @{term analz} and Image*}

lemma subset_Compl_range: "A <= - (range shrK) ==> shrK x \<notin> A"
by blast

lemma insert_Key_singleton: "insert (Key K) H = Key ` {K} \<union> H"
by blast

lemma insert_Key_image: "insert (Key K) (Key`KK \<union> C) = Key`(insert K KK) \<union> C"
by blast

(** Reverse the normal simplification of "image" to build up (not break down)
    the set of keys.  Use analz_insert_eq with (Un_upper2 RS analz_mono) to
    erase occurrences of forwarded message components (X). **)

lemmas analz_image_freshK_simps =
       simp_thms mem_simps --{*these two allow its use with @{text "only:"}*}
       disj_comms 
       image_insert [THEN sym] image_Un [THEN sym] empty_subsetI insert_subset
       analz_insert_eq Un_upper2 [THEN analz_mono, THEN [2] rev_subsetD]
       insert_Key_singleton subset_Compl_range
       Key_not_used insert_Key_image Un_assoc [THEN sym]

(*Lemma for the trivial direction of the if-and-only-if*)
lemma analz_image_freshK_lemma:
     "(Key K \<in> analz (Key`nE \<union> H)) --> (K \<in> nE | Key K \<in> analz H)  ==>  
         (Key K \<in> analz (Key`nE \<union> H)) = (K \<in> nE | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

ML
{*
val analz_image_freshK_lemma = thm "analz_image_freshK_lemma";

val analz_image_freshK_ss = 
     simpset() delsimps [image_insert, image_Un]
	       delsimps [imp_disjL]    (*reduces blow-up*)
	       addsimps thms "analz_image_freshK_simps"
*}



(*Lets blast_tac perform this step without needing the simplifier*)
lemma invKey_shrK_iff [iff]:
     "(Key (invKey K) \<in> X) = (Key K \<in> X)"
by auto

(*Specialized methods*)

method_setup analz_freshK = {*
    Method.no_args
     (Method.METHOD
      (fn facts => EVERY [REPEAT_FIRST (resolve_tac [allI, ballI, impI]),
                          REPEAT_FIRST (rtac analz_image_freshK_lemma),
                          ALLGOALS (asm_simp_tac analz_image_freshK_ss)])) *}
    "for proving the Session Key Compromise theorem"

method_setup possibility = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            gen_possibility_tac (Simplifier.get_local_simpset ctxt))) *}
    "for proving possibility theorems"

lemma knows_subset_knows_Cons: "knows A evs <= knows A (e # evs)"
by (induct e, auto simp: knows_Cons)

end
