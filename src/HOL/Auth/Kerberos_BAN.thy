(*  Title:      HOL/Auth/Kerberos_BAN
    ID:         $Id$
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header{*The Kerberos Protocol, BAN Version*}

theory Kerberos_BAN imports Public begin

text{*From page 251 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426

  Confidentiality (secrecy) and authentication properties are also
  given in a termporal version: strong guarantees in a little abstracted 
  - but very realistic - model.
*}

(* Temporal model of accidents: session keys can be leaked
                                ONLY when they have expired *)

consts

    (*Duration of the session key*)
    sesKlife   :: nat

    (*Duration of the authenticator*)
    authlife :: nat

text{*The ticket should remain fresh for two journeys on the network at least*}
specification (sesKlife)
  sesKlife_LB [iff]: "2 \<le> sesKlife"
    by blast

text{*The authenticator only for one journey*}
specification (authlife)
  authlife_LB [iff]:    "authlife \<noteq> 0"
    by blast

abbreviation
  CT :: "event list=>nat" where
  "CT == length "

abbreviation
  expiredK :: "[nat, event list] => bool" where
  "expiredK T evs == sesKlife + T < CT evs"

abbreviation
  expiredA :: "[nat, event list] => bool" where
  "expiredA T evs == authlife + T < CT evs"


constdefs

 (* A is the true creator of X if she has sent X and X never appeared on
    the trace before this event. Recall that traces grow from head. *)
  Issues :: "[agent, agent, msg, event list] => bool"
             ("_ Issues _ with _ on _")
   "A Issues B with X on evs ==
      \<exists>Y. Says A B Y \<in> set evs & X \<in> parts {Y} &
      X \<notin> parts (spies (takeWhile (% z. z  \<noteq> Says A B Y) (rev evs)))"

 (* Yields the subtrace of a given trace from its beginning to a given event *)
  before :: "[event, event list] => event list" ("before _ on _")
   "before ev on evs ==  takeWhile (% z. z ~= ev) (rev evs)"

 (* States than an event really appears only once on a trace *)
  Unique :: "[event, event list] => bool" ("Unique _ on _")
   "Unique ev on evs == 
      ev \<notin> set (tl (dropWhile (% z. z \<noteq> ev) evs))"


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
                         (Crypt K \<lbrace>Agent A, Number Ta\<rbrace>) \<rbrace>: set evs4;
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

text{*A "possibility property": there are traces that reach the end.*}
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

subsection{*Lemmas for reasoning about predicate "Issues"*}

lemma spies_Says_rev: "spies (evs @ [Says A B X]) = insert X (spies evs)"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
done

lemma spies_Gets_rev: "spies (evs @ [Gets A X]) = spies evs"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
done

lemma spies_Notes_rev: "spies (evs @ [Notes A X]) =
          (if A:bad then insert X (spies evs) else spies evs)"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
done

lemma spies_evs_rev: "spies evs = spies (rev evs)"
apply (induct_tac "evs")
apply (induct_tac [2] "a")
apply (simp_all (no_asm_simp) add: spies_Says_rev spies_Gets_rev spies_Notes_rev)
done

lemmas parts_spies_evs_revD2 = spies_evs_rev [THEN equalityD2, THEN parts_mono]

lemma spies_takeWhile: "spies (takeWhile P evs) <=  spies evs"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
txt{* Resembles @{text"used_subset_append"} in theory Event.*}
done

lemmas parts_spies_takeWhile_mono = spies_takeWhile [THEN parts_mono]


text{*Lemmas for reasoning about predicate "before"*}
lemma used_Says_rev: "used (evs @ [Says A B X]) = parts {X} \<union> (used evs)";
apply (induct_tac "evs")
apply simp
apply (induct_tac "a")
apply auto
done

lemma used_Notes_rev: "used (evs @ [Notes A X]) = parts {X} \<union> (used evs)";
apply (induct_tac "evs")
apply simp
apply (induct_tac "a")
apply auto
done

lemma used_Gets_rev: "used (evs @ [Gets B X]) = used evs";
apply (induct_tac "evs")
apply simp
apply (induct_tac "a")
apply auto
done

lemma used_evs_rev: "used evs = used (rev evs)"
apply (induct_tac "evs")
apply simp
apply (induct_tac "a")
apply (simp add: used_Says_rev)
apply (simp add: used_Gets_rev)
apply (simp add: used_Notes_rev)
done

lemma used_takeWhile_used [rule_format]: 
      "x : used (takeWhile P X) --> x : used X"
apply (induct_tac "X")
apply simp
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

text{*Forwarding Lemma for reasoning about the encrypted portion of message BK3*}
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

text{*Spy never sees another agent's shared key! (unless it's bad at start)*}
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
                evs \<in> bankerberos \<rbrakk> \<Longrightarrow> A:bad"
apply (blast dest: Spy_see_shrK)
done

lemmas Spy_analz_shrK_D = analz_subset_parts [THEN subsetD, THEN Spy_see_shrK_D,  dest!]


text{*Nobody can have used non-existent keys!*}
lemma new_keys_not_used [simp]:
    "\<lbrakk>Key K \<notin> used evs; K \<in> symKeys; evs \<in> bankerberos\<rbrakk>
     \<Longrightarrow> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] BK3_msg_in_parts_spies, simp_all)
txt{*Fake*}
apply (force dest!: keysFor_parts_insert)
txt{*BK2, BK3, BK4*}
apply (force dest!: analz_shrK_Decrypt)+
done

subsection{* Lemmas concerning the form of items passed in messages *}

text{*Describes the form of K, X and K' when the Server sends this message.*}
lemma Says_Server_message_form:
     "\<lbrakk> Says Server A (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
         \<in> set evs; evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> K' = shrK A & K \<notin> range shrK &
          Ticket = (Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>) &
          Key K \<notin> used(before
                  Says Server A (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
                  on evs) &
          Tk = CT(before 
                  Says Server A (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
                  on evs)"
apply (unfold before_def)
apply (erule rev_mp)
apply (erule bankerberos.induct, simp_all add: takeWhile_tail)
apply (metis length_rev set_rev takeWhile_void used_evs_rev)
done


text{*If the encrypted message appears then it originated with the Server
  PROVIDED that A is NOT compromised!
  This allows A to verify freshness of the session key.
*}
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


text{*If the TICKET appears then it originated with the Server*}
text{*FRESHNESS OF THE SESSION KEY to B*}
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


text{*EITHER describes the form of X when the following message is sent,
  OR     reduces it to the Fake case.
  Use @{text Says_Server_message_form} if applicable.*}
lemma Says_S_message_form:
     "\<lbrakk> Says S A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
            \<in> set evs;
         evs \<in> bankerberos \<rbrakk>
 \<Longrightarrow> (K \<notin> range shrK & X = (Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>))
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

text{* Session keys are not used to encrypt other session keys *}
lemma analz_image_freshK [rule_format (no_asm)]:
     "evs \<in> bankerberos \<Longrightarrow>
   \<forall>K KK. KK \<subseteq> - (range shrK) \<longrightarrow>
          (Key K \<in> analz (Key`KK Un (spies evs))) =
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

text{* The session key K uniquely identifies the message *}
lemma unique_session_keys:
     "\<lbrakk> Says Server A
           (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>) \<in> set evs;
         Says Server A'
          (Crypt (shrK A') \<lbrace>Number Tk', Agent B', Key K, X'\<rbrace>) \<in> set evs;
         evs \<in> bankerberos \<rbrakk> \<Longrightarrow> A=A' & Tk=Tk' & B=B' & X = X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule bankerberos.induct)
apply (frule_tac [7] Oops_parts_spies)
apply (frule_tac [5] BK3_msg_in_parts_spies, simp_all)
txt{*BK2: it can't be a new key*}
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


subsection{*Non-temporal guarantees, explicitly relying on non-occurrence of
oops events - refined below by temporal guarantees*}

text{*Non temporal treatment of confidentiality*}

text{* Lemma: the session key sent in msg BK2 would be lost by oops
    if the spy could see it! *}
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
txt{*Fake*}
apply spy_analz
txt{*BK2*}
apply (blast intro: parts_insertI)
txt{*BK3*}
apply (case_tac "Aa \<in> bad")
 prefer 2 apply (blast dest: Kab_authentic unique_session_keys)
apply (blast dest: Says_imp_spies [THEN analz.Inj] Crypt_Spy_analz_bad elim!: MPair_analz)
txt{*Oops*}
apply (blast dest: unique_session_keys)
done


text{*Confidentiality for the Server: Spy does not see the keys sent in msg BK2
as long as they have not expired.*}
lemma Confidentiality_S:
     "\<lbrakk> Says Server A
          (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>) \<in> set evs;
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (frule Says_Server_message_form, assumption)
apply (blast intro: lemma_conf)
done

text{*Confidentiality for Alice*}
lemma Confidentiality_A:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (blast dest!: Kab_authentic Confidentiality_S)
done

text{*Confidentiality for Bob*}
lemma Confidentiality_B:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>
          \<in> parts (spies evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (blast dest!: ticket_authentic Confidentiality_S)
done

text{*Non temporal treatment of authentication*}

text{*Lemmas @{text lemma_A} and @{text lemma_B} in fact are common to both temporal and non-temporal treatments*}
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
txt{*Fake*}
apply blast
txt{*BK2*}
apply (force dest: Crypt_imp_invKey_keysFor)
txt{*BK3*}
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
txt{*Fake*}
apply blast
txt{*BK2*} 
apply (force dest: Crypt_imp_invKey_keysFor)
txt{*BK4*}
apply (blast dest: ticket_authentic unique_session_keys
                   Says_imp_spies [THEN analz.Inj] Crypt_Spy_analz_bad)
done


text{*The "r" suffix indicates theorems where the confidentiality assumptions are relaxed by the corresponding arguments.*}


text{*Authentication of A to B*}
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


text{*Authentication of B to A*}
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

subsection{*Temporal guarantees, relying on a temporal check that insures that
no oops event occurred. These are available in the sense of goal availability*}


text{*Temporal treatment of confidentiality*}

text{* Lemma: the session key sent in msg BK2 would be EXPIRED
    if the spy could see it! *}
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
txt{*Fake*}
apply spy_analz
txt{*BK2*}
apply (blast intro: parts_insertI less_SucI)
txt{*BK3*}
apply (metis Crypt_Spy_analz_bad Kab_authentic Says_imp_analz_Spy 
          Says_imp_parts_knows_Spy analz.Snd less_SucI unique_session_keys)
txt{*Oops: PROOF FAILS if unsafe intro below*}
apply (blast dest: unique_session_keys intro!: less_SucI)
done


text{*Confidentiality for the Server: Spy does not see the keys sent in msg BK2
as long as they have not expired.*}
lemma Confidentiality_S_temporal:
     "\<lbrakk> Says Server A
          (Crypt K' \<lbrace>Number T, Agent B, Key K, X\<rbrace>) \<in> set evs;
         \<not> expiredK T evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (frule Says_Server_message_form, assumption)
apply (blast intro: lemma_conf_temporal)
done

text{*Confidentiality for Alice*}
lemma Confidentiality_A_temporal:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Number T, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
         \<not> expiredK T evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (blast dest!: Kab_authentic Confidentiality_S_temporal)
done

text{*Confidentiality for Bob*}
lemma Confidentiality_B_temporal:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>
          \<in> parts (spies evs);
        \<not> expiredK Tk evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerberos
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (spies evs)"
apply (blast dest!: ticket_authentic Confidentiality_S_temporal)
done

text{*Temporal treatment of authentication*}

text{*Authentication of A to B*}
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

text{*Authentication of B to A*}
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

subsection{*Treatment of the key distribution goal using trace inspection. All
guarantees are in non-temporal form, hence non available, though their temporal
form is trivial to derive. These guarantees also convey a stronger form of 
authentication - non-injective agreement on the session key*}


lemma B_Issues_A:
     "\<lbrakk> Says B A (Crypt K (Number Ta)) \<in> set evs;
         Key K \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; evs \<in> bankerberos \<rbrakk>
      \<Longrightarrow> B Issues A with (Crypt K (Number Ta)) on evs"
apply (simp (no_asm) add: Issues_def)
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule bankerberos.induct, analz_mono_contra)
apply (simp_all (no_asm_simp))
txt{*fake*}
apply blast
txt{*K4 obviously is the non-trivial case*}
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
apply (simp (no_asm) add: Issues_def)
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule bankerberos.induct, analz_mono_contra)
apply (simp_all (no_asm_simp))
txt{*fake*}
apply blast
txt{*K3 is the non trivial case*}
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
