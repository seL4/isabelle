(*  ID:         $Id$
    Author:     Giampaolo Bella, Catania University
*)

header{*The Kerberos Protocol, BAN Version, with Gets event*}

theory Kerberos_BAN_Gets imports Public begin

text{*From page 251 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426

  Confidentiality (secrecy) and authentication properties rely on
  temporal checks: strong guarantees in a little abstracted - but
  very realistic - model.
*}

(* Temporal modelization: session keys can be leaked
                          ONLY when they have expired *)

syntax
    CT :: "event list=>nat"
    expiredK :: "[nat, event list] => bool"
    expiredA :: "[nat, event list] => bool"

consts

    (*Duration of the session key*)
    sesKlife   :: nat

    (*Duration of the authenticator*)
    authlife :: nat

text{*The ticket should remain fresh for two journeys on the network at least*}
text{*The Gets event causes longer traces for the protocol to reach its end*}
specification (sesKlife)
  sesKlife_LB [iff]: "4 \<le> sesKlife"
    by blast

text{*The authenticator only for one journey*}
text{*The Gets event causes longer traces for the protocol to reach its end*}
specification (authlife)
  authlife_LB [iff]:    "2 \<le> authlife"
    by blast


translations
   "CT" == "length "

   "expiredK T evs" == "sesKlife + T < CT evs"

   "expiredA T evs" == "authlife + T < CT evs"


constdefs
 (* Yields the subtrace of a given trace from its beginning to a given event *)
  before :: "[event, event list] => event list" ("before _ on _")
   "before ev on evs ==  takeWhile (% z. z ~= ev) (rev evs)"

 (* States than an event really appears only once on a trace *)
  Unique :: "[event, event list] => bool" ("Unique _ on _")
   "Unique ev on evs == 
      ev \<notin> set (tl (dropWhile (% z. z \<noteq> ev) evs))"


consts  bankerb_gets   :: "event list set"
inductive "bankerb_gets"
 intros

   Nil:  "[] \<in> bankerb_gets"

   Fake: "\<lbrakk> evsf \<in> bankerb_gets;  X \<in> synth (analz (knows Spy evsf)) \<rbrakk>
	  \<Longrightarrow> Says Spy B X # evsf \<in> bankerb_gets"

   Reception: "\<lbrakk> evsr\<in> bankerb_gets; Says A B X \<in> set evsr \<rbrakk>
                \<Longrightarrow> Gets B X # evsr \<in> bankerb_gets"

   BK1:  "\<lbrakk> evs1 \<in> bankerb_gets \<rbrakk>
	  \<Longrightarrow> Says A Server \<lbrace>Agent A, Agent B\<rbrace> # evs1
		\<in>  bankerb_gets"


   BK2:  "\<lbrakk> evs2 \<in> bankerb_gets;  Key K \<notin> used evs2; K \<in> symKeys;
	     Gets Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs2 \<rbrakk>
	  \<Longrightarrow> Says Server A
		(Crypt (shrK A)
		   \<lbrace>Number (CT evs2), Agent B, Key K,
		    (Crypt (shrK B) \<lbrace>Number (CT evs2), Agent A, Key K\<rbrace>)\<rbrace>)
		# evs2 \<in> bankerb_gets"


   BK3:  "\<lbrakk> evs3 \<in> bankerb_gets;
	     Gets A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
	       \<in> set evs3;
	     Says A Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs3;
	     \<not> expiredK Tk evs3 \<rbrakk>
	  \<Longrightarrow> Says A B \<lbrace>Ticket, Crypt K \<lbrace>Agent A, Number (CT evs3)\<rbrace> \<rbrace>
	       # evs3 \<in> bankerb_gets"


   BK4:  "\<lbrakk> evs4 \<in> bankerb_gets;
	     Gets B \<lbrace>(Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>),
			 (Crypt K \<lbrace>Agent A, Number Ta\<rbrace>) \<rbrace>: set evs4;
	     \<not> expiredK Tk evs4;  \<not> expiredA Ta evs4 \<rbrakk>
	  \<Longrightarrow> Says B A (Crypt K (Number Ta)) # evs4
		\<in> bankerb_gets"

	(*Old session keys may become compromised*)
   Oops: "\<lbrakk> evso \<in> bankerb_gets;
         Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
	       \<in> set evso;
	     expiredK Tk evso \<rbrakk>
	  \<Longrightarrow> Notes Spy \<lbrace>Number Tk, Key K\<rbrace> # evso \<in> bankerb_gets"


declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]
declare knows_Spy_partsEs [elim]


text{*A "possibility property": there are traces that reach the end.*}
lemma "\<lbrakk>Key K \<notin> used []; K \<in> symKeys\<rbrakk>
       \<Longrightarrow> \<exists>Timestamp. \<exists>evs \<in> bankerb_gets.
             Says B A (Crypt K (Number Timestamp))
                  \<in> set evs"
apply (cut_tac sesKlife_LB)
apply (cut_tac authlife_LB)
apply (intro exI bexI)
apply (rule_tac [2]
           bankerb_gets.Nil [THEN bankerb_gets.BK1, THEN bankerb_gets.Reception,
                            THEN bankerb_gets.BK2, THEN bankerb_gets.Reception,
                            THEN bankerb_gets.BK3, THEN bankerb_gets.Reception,
                            THEN bankerb_gets.BK4])
apply (possibility, simp_all (no_asm_simp) add: used_Cons)
done


text{*Lemmas about reception invariant: if a message is received it certainly
was sent*}
lemma Gets_imp_Says :
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> bankerb_gets \<rbrakk> \<Longrightarrow> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule bankerb_gets.induct)
apply auto
done

lemma Gets_imp_knows_Spy: 
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> bankerb_gets \<rbrakk>  \<Longrightarrow> X \<in> knows Spy evs"
apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
done

lemma Gets_imp_knows_Spy_parts[dest]:
    "\<lbrakk> Gets B X \<in> set evs; evs \<in> bankerb_gets \<rbrakk>  \<Longrightarrow> X \<in> parts (knows Spy evs)"
apply (blast dest: Gets_imp_knows_Spy [THEN parts.Inj])
done

lemma Gets_imp_knows:
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> bankerb_gets \<rbrakk>  \<Longrightarrow> X \<in> knows B evs"
apply (case_tac "B = Spy")
apply (blast dest!: Gets_imp_knows_Spy)
apply (blast dest!: Gets_imp_knows_agents)
done

lemma Gets_imp_knows_analz:
    "\<lbrakk> Gets B X \<in> set evs; evs \<in> bankerb_gets \<rbrakk>  \<Longrightarrow> X \<in> analz (knows B evs)"
apply (blast dest: Gets_imp_knows [THEN analz.Inj])
done

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

(**** Inductive proofs about bankerb_gets ****)

text{*Forwarding Lemma for reasoning about the encrypted portion of message BK3*}
lemma BK3_msg_in_parts_knows_Spy:
     "\<lbrakk>Gets A (Crypt KA \<lbrace>Timestamp, B, K, X\<rbrace>) \<in> set evs; evs \<in> bankerb_gets \<rbrakk> 
      \<Longrightarrow> X \<in> parts (knows Spy evs)"
apply blast
done

lemma Oops_parts_knows_Spy:
     "Says Server A (Crypt (shrK A) \<lbrace>Timestamp, B, K, X\<rbrace>) \<in> set evs
      \<Longrightarrow> K \<in> parts (knows Spy evs)"
apply blast
done


text{*Spy never sees another agent's shared key! (unless it's bad at start)*}
lemma Spy_see_shrK [simp]:
     "evs \<in> bankerb_gets \<Longrightarrow> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Oops_parts_knows_Spy)
apply (frule_tac [6] BK3_msg_in_parts_knows_Spy, simp_all, blast+)
done


lemma Spy_analz_shrK [simp]:
     "evs \<in> bankerb_gets \<Longrightarrow> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "\<lbrakk> Key (shrK A) \<in> parts (knows Spy evs);
                evs \<in> bankerb_gets \<rbrakk> \<Longrightarrow> A:bad"
by (blast dest: Spy_see_shrK)

lemmas Spy_analz_shrK_D = analz_subset_parts [THEN subsetD, THEN Spy_see_shrK_D,  dest!]


text{*Nobody can have used non-existent keys!*}
lemma new_keys_not_used [simp]:
    "\<lbrakk>Key K \<notin> used evs; K \<in> symKeys; evs \<in> bankerb_gets\<rbrakk>
     \<Longrightarrow> K \<notin> keysFor (parts (knows Spy evs))"
apply (erule rev_mp)
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Oops_parts_knows_Spy)
apply (frule_tac [6] BK3_msg_in_parts_knows_Spy, simp_all)
txt{*Fake*}
apply (force dest!: keysFor_parts_insert)
txt{*BK2, BK3, BK4*}
apply (force dest!: analz_shrK_Decrypt)+
done

subsection{* Lemmas concerning the form of items passed in messages *}

text{*Describes the form of K, X and K' when the Server sends this message.*}
lemma Says_Server_message_form:
     "\<lbrakk> Says Server A (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
         \<in> set evs; evs \<in> bankerb_gets \<rbrakk>
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
apply (erule bankerb_gets.induct, simp_all)
txt{*We need this simplification only for Message 2*}
apply (simp (no_asm) add: takeWhile_tail)
apply auto
txt{*Two subcases of Message 2. Subcase: used before*}
apply (blast dest: used_evs_rev [THEN equalityD2, THEN contra_subsetD] 
                   used_takeWhile_used)
txt{*subcase: CT before*}
apply (fastsimp dest!: set_evs_rev [THEN equalityD2, THEN contra_subsetD, THEN takeWhile_void])
done


text{*If the encrypted message appears then it originated with the Server
  PROVIDED that A is NOT compromised!
  This allows A to verify freshness of the session key.
*}
lemma Kab_authentic:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>
           \<in> parts (knows Spy evs);
         A \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
       \<Longrightarrow> Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
             \<in> set evs"
apply (erule rev_mp)
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Oops_parts_knows_Spy)
apply (frule_tac [6] BK3_msg_in_parts_knows_Spy, simp_all, blast)
done


text{*If the TICKET appears then it originated with the Server*}
text{*FRESHNESS OF THE SESSION KEY to B*}
lemma ticket_authentic:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace> \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
       \<Longrightarrow> Says Server A
            (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K,
                          Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>\<rbrace>)
           \<in> set evs"
apply (erule rev_mp)
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Oops_parts_knows_Spy)
apply (frule_tac [6] BK3_msg_in_parts_knows_Spy, simp_all, blast)
done


text{*EITHER describes the form of X when the following message is sent,
  OR     reduces it to the Fake case.
  Use @{text Says_Server_message_form} if applicable.*}
lemma Gets_Server_message_form:
     "\<lbrakk> Gets A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
            \<in> set evs;
         evs \<in> bankerb_gets \<rbrakk>
 \<Longrightarrow> (K \<notin> range shrK & X = (Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>))
          | X \<in> analz (knows Spy evs)"
apply (case_tac "A \<in> bad")
apply (force dest!: Gets_imp_knows_Spy [THEN analz.Inj])
apply (blast dest!: Kab_authentic Says_Server_message_form)
done


text{*Reliability guarantees: honest agents act as we expect*}

lemma BK3_imp_Gets:
   "\<lbrakk> Says A B \<lbrace>Ticket, Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs;
      A \<notin> bad; evs \<in> bankerb_gets \<rbrakk>
    \<Longrightarrow> \<exists> Tk. Gets A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
      \<in> set evs"
apply (erule rev_mp)
apply (erule bankerb_gets.induct)
apply auto
done

lemma BK4_imp_Gets:
   "\<lbrakk> Says B A (Crypt K (Number Ta)) \<in> set evs;
      B \<notin> bad; evs \<in> bankerb_gets \<rbrakk>
  \<Longrightarrow> \<exists> Tk. Gets B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
	            Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule bankerb_gets.induct)
apply auto
done

lemma Gets_A_knows_K:
  "\<lbrakk> Gets A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>) \<in> set evs;
     evs \<in> bankerb_gets \<rbrakk>
 \<Longrightarrow> Key K \<in> analz (knows A evs)"
apply (force dest: Gets_imp_knows_analz)
done

lemma Gets_B_knows_K:
  "\<lbrakk> Gets B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
             Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs;
     evs \<in> bankerb_gets \<rbrakk>
 \<Longrightarrow> Key K \<in> analz (knows B evs)"
apply (force dest: Gets_imp_knows_analz)
done


(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (knows Spy evs)) \<Longrightarrow>
  Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.

****)


text{* Session keys are not used to encrypt other session keys *}
lemma analz_image_freshK [rule_format (no_asm)]:
     "evs \<in> bankerb_gets \<Longrightarrow>
   \<forall>K KK. KK \<subseteq> - (range shrK) \<longrightarrow>
          (Key K \<in> analz (Key`KK Un (knows Spy evs))) =
          (K \<in> KK | Key K \<in> analz (knows Spy evs))"
apply (erule bankerb_gets.induct)
apply (drule_tac [8] Says_Server_message_form)
apply (erule_tac [6] Gets_Server_message_form [THEN disjE], analz_freshK, spy_analz, auto) 
done


lemma analz_insert_freshK:
     "\<lbrakk> evs \<in> bankerb_gets;  KAB \<notin> range shrK \<rbrakk> \<Longrightarrow>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


text{* The session key K uniquely identifies the message *}
lemma unique_session_keys:
     "\<lbrakk> Says Server A
           (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>) \<in> set evs;
         Says Server A'
          (Crypt (shrK A') \<lbrace>Number Tk', Agent B', Key K, X'\<rbrace>) \<in> set evs;
         evs \<in> bankerb_gets \<rbrakk> \<Longrightarrow> A=A' & Tk=Tk' & B=B' & X = X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Oops_parts_knows_Spy)
apply (frule_tac [6] BK3_msg_in_parts_knows_Spy, simp_all)
txt{*BK2: it can't be a new key*}
apply blast
done

lemma unique_session_keys_Gets:
     "\<lbrakk> Gets A
           (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>) \<in> set evs;
        Gets A
          (Crypt (shrK A) \<lbrace>Number Tk', Agent B', Key K, X'\<rbrace>) \<in> set evs;
        A \<notin> bad; evs \<in> bankerb_gets \<rbrakk> \<Longrightarrow> Tk=Tk' & B=B' & X = X'"
apply (blast dest!: Kab_authentic unique_session_keys)
done


lemma Server_Unique:
     "\<lbrakk> Says Server A
            (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>) \<in> set evs;
        evs \<in> bankerb_gets \<rbrakk> \<Longrightarrow> 
   Unique Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>)
   on evs"
apply (erule rev_mp, erule bankerb_gets.induct, simp_all add: Unique_def)
apply blast
done



subsection{*Non-temporal guarantees, explicitly relying on non-occurrence of
oops events - refined below by temporal guarantees*}

text{*Non temporal treatment of confidentiality*}

text{* Lemma: the session key sent in msg BK2 would be lost by oops
    if the spy could see it! *}
lemma lemma_conf [rule_format (no_asm)]:
     "\<lbrakk> A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
  \<Longrightarrow> Says Server A
          (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K,
                            Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>\<rbrace>)
         \<in> set evs \<longrightarrow>
      Key K \<in> analz (knows Spy evs) \<longrightarrow> Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<in> set evs"
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Says_Server_message_form)
apply (frule_tac [6] Gets_Server_message_form [THEN disjE])
apply (simp_all (no_asm_simp) add: analz_insert_eq analz_insert_freshK pushes)
txt{*Fake*}
apply spy_analz
txt{*BK2*}
apply (blast intro: parts_insertI)
txt{*BK3*}
apply (case_tac "Aa \<in> bad")
 prefer 2 apply (blast dest: Kab_authentic unique_session_keys)
apply (blast dest: Gets_imp_knows_Spy [THEN analz.Inj] Crypt_Spy_analz_bad elim!: MPair_analz)
txt{*Oops*}
apply (blast dest: unique_session_keys)
done


text{*Confidentiality for the Server: Spy does not see the keys sent in msg BK2
as long as they have not expired.*}
lemma Confidentiality_S:
     "\<lbrakk> Says Server A
          (Crypt K' \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>) \<in> set evs;
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
apply (frule Says_Server_message_form, assumption)
apply (blast intro: lemma_conf)
done

text{*Confidentiality for Alice*}
lemma Confidentiality_A:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace> \<in> parts (knows Spy evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: Kab_authentic Confidentiality_S)

text{*Confidentiality for Bob*}
lemma Confidentiality_B:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>
          \<in> parts (knows Spy evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: ticket_authentic Confidentiality_S)


text{*Non temporal treatment of authentication*}

text{*Lemmas @{text lemma_A} and @{text lemma_B} in fact are common to both temporal and non-temporal treatments*}
lemma lemma_A [rule_format]:
     "\<lbrakk> A \<notin> bad; B \<notin> bad; evs \<in> bankerb_gets \<rbrakk>
      \<Longrightarrow>
         Key K \<notin> analz (knows Spy evs) \<longrightarrow>
         Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
         \<in> set evs \<longrightarrow>
          Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
         Says A B \<lbrace>X, Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace>
             \<in> set evs"
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Oops_parts_knows_Spy)
apply (frule_tac [6] Gets_Server_message_form)
apply (frule_tac [7] BK3_msg_in_parts_knows_Spy, analz_mono_contra)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt{*Fake*}
apply blast
txt{*BK2*}
apply (force dest: Crypt_imp_invKey_keysFor)
txt{*BK3*}
apply (blast dest: Kab_authentic unique_session_keys)
done
lemma lemma_B [rule_format]:
     "\<lbrakk> B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs) \<longrightarrow>
          Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>)
          \<in> set evs \<longrightarrow>
          Crypt K (Number Ta) \<in> parts (knows Spy evs) \<longrightarrow>
          Says B A (Crypt K (Number Ta)) \<in> set evs"
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Oops_parts_knows_Spy)
apply (frule_tac [6] Gets_Server_message_form)
apply (drule_tac [7] BK3_msg_in_parts_knows_Spy, analz_mono_contra)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt{*Fake*}
apply blast
txt{*BK2*} 
apply (force dest: Crypt_imp_invKey_keysFor)
txt{*BK4*}
apply (blast dest: ticket_authentic unique_session_keys
                   Gets_imp_knows_Spy [THEN analz.Inj] Crypt_Spy_analz_bad)
done


text{*The "r" suffix indicates theorems where the confidentiality assumptions are relaxed by the corresponding arguments.*}

text{*Authentication of A to B*}
lemma B_authenticates_A_r:
     "\<lbrakk> Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (knows Spy evs);
         Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>  \<in> parts (knows Spy evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
      \<Longrightarrow> Says A B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
                     Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs"
by (blast dest!: ticket_authentic
          intro!: lemma_A
          elim!: Confidentiality_S [THEN [2] rev_notE])

text{*Authentication of B to A*}
lemma A_authenticates_B_r:
     "\<lbrakk> Crypt K (Number Ta) \<in> parts (knows Spy evs);
        Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace> \<in> parts (knows Spy evs);
        Notes Spy \<lbrace>Number Tk, Key K\<rbrace> \<notin> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
      \<Longrightarrow> Says B A (Crypt K (Number Ta)) \<in> set evs"
by (blast dest!: Kab_authentic
          intro!: lemma_B elim!: Confidentiality_S [THEN [2] rev_notE])

lemma B_authenticates_A:
     "\<lbrakk> Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (spies evs);
         Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>  \<in> parts (spies evs);
        Key K \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
      \<Longrightarrow> Says A B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
                     Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs"
apply (blast dest!: ticket_authentic intro!: lemma_A)
done

lemma A_authenticates_B:
     "\<lbrakk> Crypt K (Number Ta) \<in> parts (spies evs);
        Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace> \<in> parts (spies evs);
        Key K \<notin> analz (spies evs);
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
      \<Longrightarrow> Says B A (Crypt K (Number Ta)) \<in> set evs"
apply (blast dest!: Kab_authentic intro!: lemma_B)
done


subsection{*Temporal guarantees, relying on a temporal check that insures that
no oops event occurred. These are available in the sense of goal availability*}


text{*Temporal treatment of confidentiality*}

text{* Lemma: the session key sent in msg BK2 would be EXPIRED
    if the spy could see it! *}
lemma lemma_conf_temporal [rule_format (no_asm)]:
     "\<lbrakk> A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
  \<Longrightarrow> Says Server A
          (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K,
                            Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>\<rbrace>)
         \<in> set evs \<longrightarrow>
      Key K \<in> analz (knows Spy evs) \<longrightarrow> expiredK Tk evs"
apply (erule bankerb_gets.induct)
apply (frule_tac [8] Says_Server_message_form)
apply (frule_tac [6] Gets_Server_message_form [THEN disjE])
apply (simp_all (no_asm_simp) add: less_SucI analz_insert_eq analz_insert_freshK pushes)
txt{*Fake*}
apply spy_analz
txt{*BK2*}
apply (blast intro: parts_insertI less_SucI)
txt{*BK3*}
apply (case_tac "Aa \<in> bad")
 prefer 2 apply (blast dest: Kab_authentic unique_session_keys)
apply (blast dest: Gets_imp_knows_Spy [THEN analz.Inj] Crypt_Spy_analz_bad elim!: MPair_analz intro: less_SucI)
txt{*Oops: PROOF FAILS if unsafe intro below*}
apply (blast dest: unique_session_keys intro!: less_SucI)
done


text{*Confidentiality for the Server: Spy does not see the keys sent in msg BK2
as long as they have not expired.*}
lemma Confidentiality_S_temporal:
     "\<lbrakk> Says Server A
          (Crypt K' \<lbrace>Number T, Agent B, Key K, X\<rbrace>) \<in> set evs;
         \<not> expiredK T evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
apply (frule Says_Server_message_form, assumption)
apply (blast intro: lemma_conf_temporal)
done

text{*Confidentiality for Alice*}
lemma Confidentiality_A_temporal:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Number T, Agent B, Key K, X\<rbrace> \<in> parts (knows Spy evs);
         \<not> expiredK T evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: Kab_authentic Confidentiality_S_temporal)

text{*Confidentiality for Bob*}
lemma Confidentiality_B_temporal:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>
          \<in> parts (knows Spy evs);
        \<not> expiredK Tk evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets
      \<rbrakk> \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: ticket_authentic Confidentiality_S_temporal)


text{*Temporal treatment of authentication*}

text{*Authentication of A to B*}
lemma B_authenticates_A_temporal:
     "\<lbrakk> Crypt K \<lbrace>Agent A, Number Ta\<rbrace> \<in> parts (knows Spy evs);
         Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>
         \<in> parts (knows Spy evs);
         \<not> expiredK Tk evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
      \<Longrightarrow> Says A B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
                     Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs"
by (blast dest!: ticket_authentic
          intro!: lemma_A
          elim!: Confidentiality_S_temporal [THEN [2] rev_notE])

text{*Authentication of B to A*}
lemma A_authenticates_B_temporal:
     "\<lbrakk> Crypt K (Number Ta) \<in> parts (knows Spy evs);
         Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, X\<rbrace>
         \<in> parts (knows Spy evs);
         \<not> expiredK Tk evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
      \<Longrightarrow> Says B A (Crypt K (Number Ta)) \<in> set evs"
by (blast dest!: Kab_authentic
          intro!: lemma_B elim!: Confidentiality_S_temporal [THEN [2] rev_notE])


subsection{*Combined guarantees of key distribution and non-injective agreement on the session keys*}

lemma B_authenticates_and_keydist_to_A:
     "\<lbrakk> Gets B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
                Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs;
        Key K \<notin> analz (spies evs);
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
    \<Longrightarrow> Says A B \<lbrace>Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>,
                  Crypt K \<lbrace>Agent A, Number Ta\<rbrace>\<rbrace> \<in> set evs 
     \<and>  Key K \<in> analz (knows A evs)"
apply (blast dest: B_authenticates_A BK3_imp_Gets Gets_A_knows_K)
done

lemma A_authenticates_and_keydist_to_B:
     "\<lbrakk> Gets A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>) \<in> set evs;
        Gets A (Crypt K (Number Ta)) \<in> set evs;
        Key K \<notin> analz (spies evs);
        A \<notin> bad;  B \<notin> bad;  evs \<in> bankerb_gets \<rbrakk>
    \<Longrightarrow> Says B A (Crypt K (Number Ta)) \<in> set evs
    \<and>   Key K \<in> analz (knows B evs)"
apply (blast dest: A_authenticates_B BK4_imp_Gets Gets_B_knows_K)
done





end
