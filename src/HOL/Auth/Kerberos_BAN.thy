(*  Title:      HOL/Auth/Kerberos_BAN.thy
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

section\<open>The Kerberos Protocol, BAN Version\<close>

theory Kerberos_BAN imports Public begin

text\<open>From page 251 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426

  Confidentiality (secrecy) and authentication properties are also
  given in a termporal version: strong guarantees in a little abstracted 
  - but very realistic - model.
\<close>

(* Temporal model of accidents: session keys can be leaked
                                ONLY when they have expired *)

consts

    (*Duration of the session key*)
    sesKlife   :: nat

    (*Duration of the authenticator*)
    authlife :: nat

text\<open>The ticket should remain fresh for two journeys on the network at least\<close>
specification (sesKlife)
  sesKlife_LB [iff]: "2 \<le> sesKlife"
    by blast

text\<open>The authenticator only for one journey\<close>
specification (authlife)
  authlife_LB [iff]:    "authlife \<noteq> 0"
    by blast

abbreviation
  CT :: "event list \<Rightarrow> nat" where
  "CT == length "

abbreviation
  expiredK :: "[nat, event list] \<Rightarrow> bool" where
  "expiredK T evs == sesKlife + T < CT evs"

abbreviation
  expiredA :: "[nat, event list] \<Rightarrow> bool" where
  "expiredA T evs == authlife + T < CT evs"


definition
 (* A is the true creator of X if she has sent X and X never appeared on
    the trace before this event. Recall that traces grow from head. *)
  Issues :: "[agent, agent, msg, event list] \<Rightarrow> bool"
             (\<open>_ Issues _ with _ on _\<close>) where
   "A Issues B with X on evs =
      (\<exists>Y. Says A B Y \<in> set evs \<and> X \<in> parts {Y} \<and>
        X \<notin> parts (spies (takeWhile (\<lambda>z. z  \<noteq> Says A B Y) (rev evs))))"

definition
 (* Yields the subtrace of a given trace from its beginning to a given event *)
  before :: "[event, event list] \<Rightarrow> event list" (\<open>before _ on _\<close>)
  where "before ev on evs = takeWhile (\<lambda>z. z \<noteq> ev) (rev evs)"

definition
 (* States than an event really appears only once on a trace *)
  Unique :: "[event, event list] \<Rightarrow> bool" (\<open>Unique _ on _\<close>)
  where "Unique ev on evs = (ev \<notin> set (tl (dropWhile (\<lambda>z. z \<noteq> ev) evs)))"


inductive_set bankerberos :: "event list set"
 where

   Nil:  "[] \<in> bankerberos"

 | Fake: "\<lbrakk> evsf \<in> bankerberos;  X \<in> synth (analz (spies evsf)) \<rbrakk>
          \<Longrightarrow> Says Spy B X # evsf \<in> bankerberos"


 | BK1:  "\<lbrakk> evs1 \<in> bankerberos \<rbrakk>
          \<Longrightarrow> Says A Server \<lbrace>Agent A, Agent B\<rbrace> # evs1
                \<in>  bankerberos"


 | BK2:  "\<lbrakk> evs2 \<in> bankerberos;  Key K \<notin> used evs2; K \<in> symKeys;
             Says A' Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs2 \<rbrakk>
          \<Longrightarrow> Says Server A
                (Crypt (shrK A)
                   \<lbrace>Number (CT evs2), Agent B, Key K,
                    (Crypt (shrK B) \<lbrace>Number (CT evs2), Agent A, Key K\<rbrace>)\<rbrace>)
                # evs2 \<in> bankerberos"


 | BK3:  "\<lbrakk> evs3 \<in> bankerberos;
             Says S A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
               \<in> set evs3;
             Says A Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs3;
             \<not> expiredK Tk evs3 \<rbrakk>
          \<Longrightarrow> Says A B \<lbrace>Ticket, Crypt K \<lbrace>Agent A, Number (CT evs3)\<rbrace> \<rbrace>
               # evs3 \<in> bankerberos"


 | BK4:  "\<lbrakk> evs4 \<in> bankerberos;
             Says A' B \<lbrace>(Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>),
                         (Crypt K \<lbrace>Agent A, Number Ta\<rbrace>) \<rbrace> \<in> set evs4;
             \<not> expiredK Tk evs4;  \<not> expiredA Ta evs4 \<rbrakk>
          \<Longrightarrow> Says B A (Crypt K (Number Ta)) # evs4
                \<in> bankerberos"

        (*Old session keys may become compromised*)
 | Oops: "\<lbrakk> evso \<in> bankerberos;
         Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
               \<in> set evso;
             expiredK Tk evso \<rbrakk>
          \<Longrightarrow> Notes Spy \<lbrace>Number Tk, Key K\<rbrace> # evso \<in> bankerberos"


declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

text\<open>A "possibility property": there are traces that reach the end.\<close>
lemma "\<lbrakk>Key K \<notin> used []; K \<in> symKeys\<rbrakk>
       \<Longrightarrow> \<exists>Timestamp. \<exists>evs \<in> bankerberos.
             Says B A (Crypt K (Number Timestamp))
                  \<in> set evs"
apply (cut_tac sesKlife_LB)
apply (intro exI bexI)
apply (rule_tac [2]
           bankerberos.Nil [THEN bankerberos.BK1, THEN bankerberos.BK2,
                             THEN bankerberos.BK3, THEN bankerberos.BK4])
apply (possibility, simp_all (no_asm_simp) add: used_Cons)
done

subsection\<open>Lemmas for reasoning about predicate "Issues"\<close>

lemma spies_Says_rev: "spies (evs @ [Says A B X]) = insert X (spies evs)"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a", auto)
done

lemma spies_Gets_rev: "spies (evs @ [Gets A X]) = spies evs"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a", auto)
done

lemma spies_Notes_rev: "spies (evs @ [Notes A X]) =
          (if A\<in>bad then insert X (spies evs) else spies evs)"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a", auto)
done

lemma spies_evs_rev: "spies evs = spies (rev evs)"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a")
apply (simp_all (no_asm_simp) add: spies_Says_rev spies_Gets_rev spies_Notes_rev)
done

lemmas parts_spies_evs_revD2 = spies_evs_rev [THEN equalityD2, THEN parts_mono]

lemma spies_takeWhile: "spies (takeWhile P evs) \<subseteq> spies evs"
apply (induct_tac "evs")
apply (rename_tac [2] a b)
apply (induct_tac [2] "a", auto)
txt\<open>Resembles \<open>used_subset_append\<close> in theory Event.\<close>
done

lemmas parts_spies_takeWhile_mono = spies_takeWhile [THEN parts_mono]


text\<open>Lemmas for reasoning about predicate "before"\<close>
lemma used_Says_rev: "used (evs @ [Says A B X]) = parts {X} \<union> (used evs)"
apply (induct_tac "evs")
apply simp
apply (rename_tac a b)
apply (induct_tac "a")
apply auto
done

lemma used_Notes_rev: "used (evs @ [Notes A X]) = parts {X} \<union> (used evs)"
apply (induct_tac "evs")
apply simp
apply (rename_tac a b)
apply (induct_tac "a")
apply auto
done

lemma used_Gets_rev: "used (evs @ [Gets B X]) = used evs"
apply (induct_tac "evs")
apply simp
apply (rename_tac a b)
apply (induct_tac "a")
apply auto
done

lemma used_evs_rev: "used evs = used (rev evs)"
apply (induct_tac "evs")
apply simp
apply (rename_tac a b)
apply (induct_tac "a")
apply (simp add: used_Says_rev)
apply (simp add: used_Gets_rev)
apply (simp add: used_Notes_rev)
done

lemma used_takeWhile_used [rule_format]: 
      "x \<in> used (takeWhile P X) \<longrightarrow> x \<in> used X"
apply (induct_tac "X")
apply simp
apply (rename_tac a b)
apply (induct_tac "a")
apply (simp_all add: used_Nil)
apply (blast dest!: initState_into_used)+
done

lemma set_evs_rev: "set evs = set (rev evs)"
apply auto
done

lemma takeWhile_void [rule_format]:
      "x \<notin> set evs \<longrightarrow> takeWhile (\<lambda>z. z \<noteq> x) evs = evs"
apply auto
done

(**** Inductive proofs about bankerberos ****)

text\<open>Forwarding Lemma for reasoning about the encrypted portion of message BK3\<close>
lemma BK3_msg_in_parts_spies:
     "Says S A (Crypt KA \<lbrace>Timestamp, B, K, X\<rbrace>) \<in> set evs
      \<Longrightarrow> X \<in> parts (spies evs)"
apply blast
done

lemma Oops_parts_spies:
     "Says Server A (Crypt (shrK A) \<lbrace>Timestamp, B, K, X\<rbrace>) \<in> set evs
      \<Longrightarrow> K \<in> parts (spies evs)"
apply blast
done

text\<open>Spy never sees another agent's shared key! (unless it's bad at start)\<close>
lemma Spy_see_shrK [simp]:
     "evs \<in> bankerberos \<Longrightarrow> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] BK3_msg_in_parts_spies, simp_all, blast+)
done


lemma Spy_analz_shrK [simp]:
     "evs \<in> bankerberos \<Longrightarrow> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
apply auto
done

lemma Spy_see_shrK_D [dest!]:
     "\<lbrakk> Key (shrK A) \<in> parts (spies evs);
                evs \<in> bankerberos \<rbrakk> \<Longrightarrow> A\<in>bad"
apply (blast dest: Spy_see_shrK)
done

lemmas Spy_analz_shrK_D = analz_subset_parts [THEN subsetD, THEN Spy_see_shrK_D,  dest!]


text\<open>Nobody can have used non-existent keys!\<close>
lemma new_keys_not_used [simp]:
    "\<lbrakk>Key K \<notin> used evs; K \<in> symKeys; evs \<in> bankerberos\<rbrakk>
     \<Longrightarrow> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] BK3_msg_in_parts_spies, simp_all)
txt\<open>Fake\<close>
apply (force dest!: keysFor_parts_insert)
txt\<open>BK2, BK3, BK4\<close>
apply (force dest!: analz_shrK_Decrypt)+
done

subsection\<open>Lemmas concerning the form of items passed in messages\<close>

text\<open>Describes the form of K, X and K' when the Server sends this message.\<close>
lemma Says_Server_message_form:
     "\<lbrakk> Says Server A (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
         \<in> set evs; evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> K' = shrK A \<and> K \<notin> range shrK \<and>
          Ticket = (Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>) \<and>
          Key K \<notin> used(before
                  Says Server A (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
                  on evs) \<and>
          Tk = CT(before 
                  Says Server A (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
                  on evs)"
unfolding before_def
apply (erule rev_mp)
apply (erule bankerberos.induct, simp_all add: takeWhile_tail)
apply auto
 apply (metis length_rev set_rev takeWhile_void used_evs_rev)+
done


text\<open>If the encrypted message appears then it originated with the Server
  PROVIDED that A is NOT compromised!
  This allows A to verify freshness of the session key.
\<close>
lemma Kab_authentic:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>
           \<in> parts (spies evs);
         A \<notin> bad;  evs \<in> bankerberos \<rbrakk>
       \<Longrightarrow> Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
             \<in> set evs"
apply (erule rev_mp)
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] BK3_msg_in_parts_spies, simp_all, blast)
done


text\<open>If the TICKET appears then it originated with the Server\<close>
text\<open>FRESHNESS OF THE SESSION KEY to B\<close>
lemma ticket_authentic:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace> \<in> parts (spies evs);
         B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
       \<Longrightarrow> Says Server A
            (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K,
                          Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>\<rbrace>)
           \<in> set evs"
apply (erule rev_mp)
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] BK3_msg_in_parts_spies, simp_all, blast)
done


text\<open>EITHER describes the form of X when the following message is sent,
  OR     reduces it to the Fake case.
  Use \<open>Says_Server_message_form\<close> if applicable.\<close>
lemma Says_S_message_form:
     "\<lbrakk> Says S A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
            \<in> set evs;
         evs \<in> bankerberos \<rbrakk>
 \<Longrightarrow> (K \<notin> range shrK \<and> X = (Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>))
          | X \<in> analz (spies evs)"
apply (case_tac "A \<in> bad")
apply (force dest!: Says_imp_spies [THEN analz.Inj])
apply (frule Says_imp_spies [THEN parts.Inj])
apply (blast dest!: Kab_authentic Says_Server_message_form)
done



(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (spies evs)) \<Longrightarrow>
  Key K \<in> analz (spies evs)

 A more general formula must be proved inductively.

****)

text\<open>Session keys are not used to encrypt other session keys\<close>
lemma analz_image_freshK [rule_format (no_asm)]:
     "evs \<in> bankerberos \<Longrightarrow>
   \<forall>K KK. KK \<subseteq> - (range shrK) \<longrightarrow>
          (Key K \<in> analz (Key`KK \<union> (spies evs))) =
          (K \<in> KK | Key K \<in> analz (spies evs))"
apply (erule bankerberos.induct)
apply (drule_tac [7] Says_Server_message_form)
apply (erule_tac [5] Says_S_message_form [THEN disjE], analz_freshK, spy_analz, auto) 
done


lemma analz_insert_freshK:
     "\<lbrakk> evs \<in> bankerberos;  KAB \<notin> range shrK \<rbrakk> \<Longrightarrow>
      (Key K \<in> analz (insert (Key KAB) (spies evs))) =
      (K = KAB | Key K \<in> analz (spies evs))"
apply (simp only: analz_image_freshK analz_image_freshK_simps)
done

text\<open>The session key K uniquely identifies the message\<close>
lemma unique_session_keys:
     "\<lbrakk> Says Server A
           (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>) \<in> set evs;
         Says Server A'
          (Crypt (shrK A') \<lbrace>Number Tk', Agent B', Key K, X'\<rbrace>) \<in> set evs;
         evs \<in> bankerberos \<rbrakk> \<Longrightarrow> A=A' \<and> Tk=Tk' \<and> B=B' \<and> X = X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] BK3_msg_in_parts_spies, simp_all)
txt\<open>BK2: it can't be a new key\<close>
apply blast
done

lemma Server_Unique:
     "\<lbrakk> Says Server A
            (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>) \<in> set evs;
        evs \<in> bankerberos \<rbrakk> \<Longrightarrow> 
   Unique Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
   on evs"
apply (erule rev_mp, erule bankerberos.induct, simp_all add: Unique_def)
apply blast
done


subsection\<open>Non-temporal guarantees, explicitly relying on non-occurrence of
oops events - refined below by temporal guarantees\<close>

text\<open>Non temporal treatment of confidentiality\<close>

text\<open>Lemma: the session key sent in msg BK2 would be lost by oops
    if the spy could see it!\<close>
lemma lemma_conf [rule_format (no_asm)]:
     "\<lbrakk> A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
  \<Longrightarrow> Says Server A
          (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K,
                            Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>\<rbrace>)
         \<in> set evs \<longrightarrow>
      Key K \<in> analz (spies evs) \<longrightarrow> Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<in> set evs"
apply (erule bankerberos.induct)
apply (frule_tac [7] Says_Server_message_form)
apply (frule_tac [5] Says_S_message_form [THEN disjE])
apply (simp_all (no_asm_simp) add: analz_insert_eq analz_insert_freshK pushes)
txt\<open>Fake\<close>
apply spy_analz
txt\<open>BK2\<close>
apply (blast intro: parts_insertI)
txt\<open>BK3\<close>
apply (case_tac "Aa \<in> bad")
 prefer 2 apply (blast dest: Kab_authentic unique_session_keys)
apply (blast dest: Says_imp_spies [THEN analz.Inj] Crypt_Spy_analz_bad elim!: MPair_analz)
txt\<open>Oops\<close>
apply (blast dest: unique_session_keys)
done


text\<open>Confidentiality for the Server: Spy does not see the keys sent in msg BK2
as long as they have not expired.\<close>
lemma Confidentiality_S:
     "\<lbrakk> Says Server A
          (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>) \<in> set evs;
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (frule Says_Server_message_form, assumption)
apply (blast intro: lemma_conf)
done

text\<open>Confidentiality for Alice\<close>
lemma Confidentiality_A:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (blast dest!: Kab_authentic Confidentiality_S)
done

text\<open>Confidentiality for Bob\<close>
lemma Confidentiality_B:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>
          \<in> parts (spies evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (blast dest!: ticket_authentic Confidentiality_S)
done

text\<open>Non temporal treatment of authentication\<close>

text\<open>Lemmas \<open>lemma_A\<close> and \<open>lemma_B\<close> in fact are common to both temporal and non-temporal treatments\<close>
lemma lemma_A [rule_format]:
     "\<lbrakk> A \<notin> bad; B \<notin> bad; evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow>
         Key K \<notin> analz (spies evs) \<longrightarrow>
         Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
         \<in> set evs \<longrightarrow>
          Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (spies evs) \<longrightarrow>
         Says A B \<lbrace>X, Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace>
             \<in> set evs"
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] Says_S_message_form)
apply (frule_tac [6] BK3_msg_in_parts_spies, analz_mono_contra)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt\<open>Fake\<close>
apply blast
txt\<open>BK2\<close>
apply (force dest: Crypt_imp_invKey_keysFor)
txt\<open>BK3\<close>
apply (blast dest: Kab_authentic unique_session_keys)
done

lemma lemma_B [rule_format]:
     "\<lbrakk> B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (spies evs) \<longrightarrow>
          Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
          \<in> set evs \<longrightarrow>
          Crypt K (Number Ta) \<in> parts (spies evs) \<longrightarrow>
          Says B A (Crypt K (Number Ta)) \<in> set evs"
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] Says_S_message_form)
apply (drule_tac [6] BK3_msg_in_parts_spies, analz_mono_contra)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt\<open>Fake\<close>
apply blast
txt\<open>BK2\<close> 
apply (force dest: Crypt_imp_invKey_keysFor)
txt\<open>BK4\<close>
apply (blast dest: ticket_authentic unique_session_keys
                   Says_imp_spies [THEN analz.Inj] Crypt_Spy_analz_bad)
done


text\<open>The "r" suffix indicates theorems where the confidentiality assumptions are relaxed by the corresponding arguments.\<close>


text\<open>Authentication of A to B\<close>
lemma B_authenticates_A_r:
     "\<lbrakk> Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (spies evs);
         Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>  \<in> parts (spies evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> Says A B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
                     Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs"
apply (blast dest!: ticket_authentic
          intro!: lemma_A
          elim!: Confidentiality_S [THEN [2] rev_notE])
done


text\<open>Authentication of B to A\<close>
lemma A_authenticates_B_r:
     "\<lbrakk> Crypt K (Number Ta) \<in> parts (spies evs);
        Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> Says B A (Crypt K (Number Ta)) \<in> set evs"
apply (blast dest!: Kab_authentic
          intro!: lemma_B elim!: Confidentiality_S [THEN [2] rev_notE])
done

lemma B_authenticates_A:
     "\<lbrakk> Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (spies evs);
         Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>  \<in> parts (spies evs);
        Key K \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> Says A B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
                     Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs"
apply (blast dest!: ticket_authentic intro!: lemma_A)
done

lemma A_authenticates_B:
     "\<lbrakk> Crypt K (Number Ta) \<in> parts (spies evs);
        Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
        Key K \<notin> analz (spies evs);
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> Says B A (Crypt K (Number Ta)) \<in> set evs"
apply (blast dest!: Kab_authentic intro!: lemma_B)
done

subsection\<open>Temporal guarantees, relying on a temporal check that insures that
no oops event occurred. These are available in the sense of goal availability\<close>


text\<open>Temporal treatment of confidentiality\<close>

text\<open>Lemma: the session key sent in msg BK2 would be EXPIRED
    if the spy could see it!\<close>
lemma lemma_conf_temporal [rule_format (no_asm)]:
     "\<lbrakk> A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
  \<Longrightarrow> Says Server A
          (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K,
                            Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>\<rbrace>)
         \<in> set evs \<longrightarrow>
      Key K \<in> analz (spies evs) \<longrightarrow> expiredK Tk evs"
apply (erule bankerberos.induct)
apply (frule_tac [7] Says_Server_message_form)
apply (frule_tac [5] Says_S_message_form [THEN disjE])
apply (simp_all (no_asm_simp) add: less_SucI analz_insert_eq analz_insert_freshK pushes)
txt\<open>Fake\<close>
apply spy_analz
txt\<open>BK2\<close>
apply (blast intro: parts_insertI less_SucI)
txt\<open>BK3\<close>
apply (metis Crypt_Spy_analz_bad Kab_authentic Says_imp_analz_Spy 
          Says_imp_parts_knows_Spy analz.Snd less_SucI unique_session_keys)
txt\<open>Oops: PROOF FAILS if unsafe intro below\<close>
apply (blast dest: unique_session_keys intro!: less_SucI)
done


text\<open>Confidentiality for the Server: Spy does not see the keys sent in msg BK2
as long as they have not expired.\<close>
lemma Confidentiality_S_temporal:
     "\<lbrakk> Says Server A
          (Crypt K' \<lbrace>Number T, Agent B, Key K, X\<rbrace>) \<in> set evs;
         \<not> expiredK T evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (frule Says_Server_message_form, assumption)
apply (blast intro: lemma_conf_temporal)
done

text\<open>Confidentiality for Alice\<close>
lemma Confidentiality_A_temporal:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Number T, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
         \<not> expiredK T evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (blast dest!: Kab_authentic Confidentiality_S_temporal)
done

text\<open>Confidentiality for Bob\<close>
lemma Confidentiality_B_temporal:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>
          \<in> parts (spies evs);
        \<not> expiredK Tk evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (blast dest!: ticket_authentic Confidentiality_S_temporal)
done

text\<open>Temporal treatment of authentication\<close>

text\<open>Authentication of A to B\<close>
lemma B_authenticates_A_temporal:
     "\<lbrakk> Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (spies evs);
         Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>
         \<in> parts (spies evs);
         \<not> expiredK Tk evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> Says A B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
                     Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs"
apply (blast dest!: ticket_authentic
          intro!: lemma_A
          elim!: Confidentiality_S_temporal [THEN [2] rev_notE])
done

text\<open>Authentication of B to A\<close>
lemma A_authenticates_B_temporal:
     "\<lbrakk> Crypt K (Number Ta) \<in> parts (spies evs);
         Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>
         \<in> parts (spies evs);
         \<not> expiredK Tk evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> Says B A (Crypt K (Number Ta)) \<in> set evs"
apply (blast dest!: Kab_authentic
          intro!: lemma_B elim!: Confidentiality_S_temporal [THEN [2] rev_notE])
done

subsection\<open>Treatment of the key distribution goal using trace inspection. All
guarantees are in non-temporal form, hence non available, though their temporal
form is trivial to derive. These guarantees also convey a stronger form of 
authentication - non-injective agreement on the session key\<close>


lemma B_Issues_A:
     "\<lbrakk> Says B A (Crypt K (Number Ta)) \<in> set evs;
         Key K \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> B Issues A with (Crypt K (Number Ta)) on evs"
unfolding Issues_def
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule bankerberos.induct, analz_mono_contra)
apply (simp_all (no_asm_simp))
txt\<open>fake\<close>
apply blast
txt\<open>K4 obviously is the non-trivial case\<close>
apply (simp add: takeWhile_tail)
apply (blast dest: ticket_authentic parts_spies_takeWhile_mono [THEN subsetD] parts_spies_evs_revD2 [THEN subsetD] intro: A_authenticates_B_temporal)
done

lemma A_authenticates_and_keydist_to_B:
     "\<lbrakk> Crypt K (Number Ta) \<in> parts (spies evs);
        Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
         Key K \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> B Issues A with (Crypt K (Number Ta)) on evs"
apply (blast dest!: A_authenticates_B B_Issues_A)
done


lemma A_Issues_B:
     "\<lbrakk> Says A B \<lbrace>Ticket, Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace>
           \<in> set evs;
         Key K \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
   \<Longrightarrow> A Issues B with (Crypt K \<lbrace>Agent A, Number Ta\<rbrace>) on evs"
unfolding Issues_def
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule bankerberos.induct, analz_mono_contra)
apply (simp_all (no_asm_simp))
txt\<open>fake\<close>
apply blast
txt\<open>K3 is the non trivial case\<close>
apply (simp add: takeWhile_tail)
apply auto (*Technically unnecessary, merely clarifies the subgoal as it is presemted in the book*)
apply (blast dest: Kab_authentic Says_Server_message_form parts_spies_takeWhile_mono [THEN subsetD] parts_spies_evs_revD2 [THEN subsetD] 
             intro!: B_authenticates_A)
done


lemma B_authenticates_and_keydist_to_A:
     "\<lbrakk> Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (spies evs);
        Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>  \<in> parts (spies evs);
        Key K \<notin> analz (spies evs);
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos \<rbrakk>
   \<Longrightarrow> A Issues B with (Crypt K \<lbrace>Agent A, Number Ta\<rbrace>) on evs"
apply (blast dest: B_authenticates_A A_Issues_B)
done




end
