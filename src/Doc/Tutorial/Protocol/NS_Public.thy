(*  Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_public" for the Needham-Schroeder Public-Key protocol.
Version incorporating Lowe's fix (inclusion of B's identity in round 2).
*)(*<*)
theory NS_Public imports Public begin(*>*)

section{* Modelling the Protocol \label{sec:modelling} *}

text_raw {*
\begin{figure}
\begin{isabelle}
*}

inductive_set ns_public :: "event list set"
  where

   Nil:  "[] \<in> ns_public"


 | Fake: "\<lbrakk>evsf \<in> ns_public;  X \<in> synth (analz (knows Spy evsf))\<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> ns_public"


 | NS1:  "\<lbrakk>evs1 \<in> ns_public;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>)
                 # evs1  \<in>  ns_public"


 | NS2:  "\<lbrakk>evs2 \<in> ns_public;  Nonce NB \<notin> used evs2;
           Says A' B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>)
                # evs2  \<in>  ns_public"


 | NS3:  "\<lbrakk>evs3 \<in> ns_public;
           Says A  B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
           Says B' A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>)
              \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubK B) (Nonce NB)) # evs3 \<in> ns_public"

text_raw {*
\end{isabelle}
\caption{An Inductive Protocol Definition}\label{fig:ns_public}
\end{figure}
*}

text {*
Let us formalize the Needham-Schroeder public-key protocol, as corrected by
Lowe:
\begin{alignat*%
}{2}
  &1.&\quad  A\to B  &: \comp{Na,A}\sb{Kb} \\
  &2.&\quad  B\to A  &: \comp{Na,Nb,B}\sb{Ka} \\
  &3.&\quad  A\to B  &: \comp{Nb}\sb{Kb}
\end{alignat*%
}

Each protocol step is specified by a rule of an inductive definition.  An
event trace has type @{text "event list"}, so we declare the constant
@{text ns_public} to be a set of such traces.

Figure~\ref{fig:ns_public} presents the inductive definition.  The
@{text Nil} rule introduces the empty trace.  The @{text Fake} rule models the
adversary's sending a message built from components taken from past
traffic, expressed using the functions @{text synth} and
@{text analz}. 
The next three rules model how honest agents would perform the three
protocol steps.  

Here is a detailed explanation of rule @{text NS2}.
A trace containing an event of the form
@{term [display,indent=5] "Says A' B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>)"}
may be extended by an event of the form
@{term [display,indent=5] "Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>)"}
where @{text NB} is a fresh nonce: @{term "Nonce NB \<notin> used evs2"}.
Writing the sender as @{text A'} indicates that @{text B} does not 
know who sent the message.  Calling the trace variable @{text evs2} rather
than simply @{text evs} helps us know where we are in a proof after many
case-splits: every subgoal mentioning @{text evs2} involves message~2 of the
protocol.

Benefits of this approach are simplicity and clarity.  The semantic model
is set theory, proofs are by induction and the translation from the informal
notation to the inductive rules is straightforward. 
*}

section{* Proving Elementary Properties \label{sec:regularity} *}

(*<*)
declare knows_Spy_partsEs [elim]
declare analz_subset_parts [THEN subsetD, dest]
declare Fake_parts_insert [THEN subsetD, dest]
declare image_eq_UN [simp]  (*accelerates proofs involving nested images*)

(*A "possibility property": there are traces that reach the end*)
lemma "\<exists>NB. \<exists>evs \<in> ns_public. Says A B (Crypt (pubK B) (Nonce NB)) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] ns_public.Nil [THEN ns_public.NS1, THEN ns_public.NS2,
                                   THEN ns_public.NS3])
by possibility


(**** Inductive proofs about ns_public ****)

(** Theorems of the form X \<notin> parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's bad at start)*)
(*>*)

text {*
Secrecy properties can be hard to prove.  The conclusion of a typical
secrecy theorem is 
@{term "X \<notin> analz (knows Spy evs)"}.  The difficulty arises from
having to reason about @{text analz}, or less formally, showing that the spy
can never learn~@{text X}.  Much easier is to prove that @{text X} can never
occur at all.  Such \emph{regularity} properties are typically expressed
using @{text parts} rather than @{text analz}.

The following lemma states that @{text A}'s private key is potentially
known to the spy if and only if @{text A} belongs to the set @{text bad} of
compromised agents.  The statement uses @{text parts}: the very presence of
@{text A}'s private key in a message, whether protected by encryption or
not, is enough to confirm that @{text A} is compromised.  The proof, like
nearly all protocol proofs, is by induction over traces.
*}

lemma Spy_see_priK [simp]:
      "evs \<in> ns_public
       \<Longrightarrow> (Key (priK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
apply (erule ns_public.induct, simp_all)
txt {*
The induction yields five subgoals, one for each rule in the definition of
@{text ns_public}.  The idea is to prove that the protocol property holds initially
(rule @{text Nil}), is preserved by each of the legitimate protocol steps (rules
@{text NS1}--@{text 3}), and even is preserved in the face of anything the
spy can do (rule @{text Fake}).  

The proof is trivial.  No legitimate protocol rule sends any keys
at all, so only @{text Fake} is relevant. Indeed, simplification leaves
only the @{text Fake} case, as indicated by the variable name @{text evsf}:
@{subgoals[display,indent=0,margin=65]}
*}
by blast
(*<*)
lemma Spy_analz_priK [simp]:
      "evs \<in> ns_public \<Longrightarrow> (Key (priK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto
(*>*)

text {*
The @{text Fake} case is proved automatically.  If
@{term "priK A"} is in the extended trace then either (1) it was already in the
original trace or (2) it was
generated by the spy, who must have known this key already. 
Either way, the induction hypothesis applies.

\emph{Unicity} lemmas are regularity lemmas stating that specified items
can occur only once in a trace.  The following lemma states that a nonce
cannot be used both as $Na$ and as $Nb$ unless
it is known to the spy.  Intuitively, it holds because honest agents
always choose fresh values as nonces; only the spy might reuse a value,
and he doesn't know this particular value.  The proof script is short:
induction, simplification, @{text blast}.  The first line uses the rule
@{text rev_mp} to prepare the induction by moving two assumptions into the 
induction formula.
*}

lemma no_nonce_NS1_NS2:
    "\<lbrakk>Crypt (pubK C) \<lbrace>NA', Nonce NA, Agent D\<rbrace> \<in> parts (knows Spy evs);
      Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (knows Spy evs);
      evs \<in> ns_public\<rbrakk>
     \<Longrightarrow> Nonce NA \<in> analz (knows Spy evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule ns_public.induct, simp_all)
apply (blast intro: analz_insertI)+
done

text {*
The following unicity lemma states that, if \isa{NA} is secret, then its
appearance in any instance of message~1 determines the other components. 
The proof is similar to the previous one.
*}

lemma unique_NA:
     "\<lbrakk>Crypt(pubK B)  \<lbrace>Nonce NA, Agent A \<rbrace> \<in> parts(knows Spy evs);
       Crypt(pubK B') \<lbrace>Nonce NA, Agent A'\<rbrace> \<in> parts(knows Spy evs);
       Nonce NA \<notin> analz (knows Spy evs); evs \<in> ns_public\<rbrakk>
      \<Longrightarrow> A=A' \<and> B=B'"
(*<*)
apply (erule rev_mp, erule rev_mp, erule rev_mp)
apply (erule ns_public.induct, simp_all)
(*Fake, NS1*)
apply (blast intro: analz_insertI)+
done
(*>*)

section{* Proving Secrecy Theorems \label{sec:secrecy} *}

(*<*)
(*Secrecy: Spy does not see the nonce sent in msg NS1 if A and B are secure
  The major premise "Says A B ..." makes it a dest-rule, so we use
  (erule rev_mp) rather than rule_format. *)
theorem Spy_not_see_NA:
      "\<lbrakk>Says A B (Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>
       \<Longrightarrow> Nonce NA \<notin> analz (knows Spy evs)"
apply (erule rev_mp)
apply (erule ns_public.induct, simp_all)
apply spy_analz
apply (blast dest: unique_NA intro: no_nonce_NS1_NS2)+
done


(*Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.*)
lemma A_trusts_NS2_lemma [rule_format]:
   "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>
    \<Longrightarrow> Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
        Says A B (Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs \<longrightarrow>
        Says B A (Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>) \<in> set evs"
apply (erule ns_public.induct, simp_all)
(*Fake, NS1*)
apply (blast dest: Spy_not_see_NA)+
done

theorem A_trusts_NS2:
     "\<lbrakk>Says A  B (Crypt(pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs;
       Says B' A (Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>) \<in> set evs;
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>
      \<Longrightarrow> Says B A (Crypt(pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>) \<in> set evs"
by (blast intro: A_trusts_NS2_lemma)


(*If the encrypted message appears then it originated with Alice in NS1*)
lemma B_trusts_NS1 [rule_format]:
     "evs \<in> ns_public
      \<Longrightarrow> Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
          Nonce NA \<notin> analz (knows Spy evs) \<longrightarrow>
          Says A B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs"
apply (erule ns_public.induct, simp_all)
(*Fake*)
apply (blast intro!: analz_insertI)
done



(*** Authenticity properties obtained from NS2 ***)

(*Unicity for NS2: nonce NB identifies nonce NA and agents A, B
  [unicity of B makes Lowe's fix work]
  [proof closely follows that for unique_NA] *)

lemma unique_NB [dest]:
     "\<lbrakk>Crypt(pubK A)  \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace> \<in> parts(knows Spy evs);
       Crypt(pubK A') \<lbrace>Nonce NA', Nonce NB, Agent B'\<rbrace> \<in> parts(knows Spy evs);
       Nonce NB \<notin> analz (knows Spy evs); evs \<in> ns_public\<rbrakk>
      \<Longrightarrow> A=A' \<and> NA=NA' \<and> B=B'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)
apply (erule ns_public.induct, simp_all)
(*Fake, NS2*)
apply (blast intro: analz_insertI)+
done
(*>*)

text {*
The secrecy theorems for Bob (the second participant) are especially
important because they fail for the original protocol.  The following
theorem states that if Bob sends message~2 to Alice, and both agents are
uncompromised, then Bob's nonce will never reach the spy.
*}

theorem Spy_not_see_NB [dest]:
 "\<lbrakk>Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>) \<in> set evs;
   A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>
  \<Longrightarrow> Nonce NB \<notin> analz (knows Spy evs)"
txt {*
To prove it, we must formulate the induction properly (one of the
assumptions mentions~@{text evs}), apply induction, and simplify:
*}

apply (erule rev_mp, erule ns_public.induct, simp_all)
(*<*)
apply spy_analz
defer
apply (blast intro: no_nonce_NS1_NS2)
apply (blast intro: no_nonce_NS1_NS2)
(*>*)

txt {*
The proof states are too complicated to present in full.  
Let's examine the simplest subgoal, that for message~1.  The following
event has just occurred:
\[ 1.\quad  A'\to B'  : \comp{Na',A'}\sb{Kb'} \]
The variables above have been primed because this step
belongs to a different run from that referred to in the theorem
statement --- the theorem
refers to a past instance of message~2, while this subgoal
concerns message~1 being sent just now.
In the Isabelle subgoal, instead of primed variables like $B'$ and $Na'$
we have @{text Ba} and~@{text NAa}:
@{subgoals[display,indent=0]}
The simplifier has used a 
default simplification rule that does a case
analysis for each encrypted message on whether or not the decryption key
is compromised.
@{named_thms [display,indent=0,margin=50] analz_Crypt_if [no_vars] (analz_Crypt_if)}
The simplifier has also used @{text Spy_see_priK}, proved in
{\S}\ref{sec:regularity} above, to yield @{term "Ba \<in> bad"}.

Recall that this subgoal concerns the case
where the last message to be sent was
\[ 1.\quad  A'\to B'  : \comp{Na',A'}\sb{Kb'}. \]
This message can compromise $Nb$ only if $Nb=Na'$ and $B'$ is compromised,
allowing the spy to decrypt the message.  The Isabelle subgoal says
precisely this, if we allow for its choice of variable names.
Proving @{term "NB \<noteq> NAa"} is easy: @{text NB} was
sent earlier, while @{text NAa} is fresh; formally, we have
the assumption @{term "Nonce NAa \<notin> used evs1"}. 

Note that our reasoning concerned @{text B}'s participation in another
run.  Agents may engage in several runs concurrently, and some attacks work
by interleaving the messages of two runs.  With model checking, this
possibility can cause a state-space explosion, and for us it
certainly complicates proofs.  The biggest subgoal concerns message~2.  It
splits into several cases, such as whether or not the message just sent is
the very message mentioned in the theorem statement.
Some of the cases are proved by unicity, others by
the induction hypothesis.  For all those complications, the proofs are
automatic by @{text blast} with the theorem @{text no_nonce_NS1_NS2}.

The remaining theorems about the protocol are not hard to prove.  The
following one asserts a form of \emph{authenticity}: if
@{text B} has sent an instance of message~2 to~@{text A} and has received the
expected reply, then that reply really originated with~@{text A}.  The
proof is a simple induction.
*}

(*<*)
by (blast intro: no_nonce_NS1_NS2)

lemma B_trusts_NS3_lemma [rule_format]:
     "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk> \<Longrightarrow>
      Crypt (pubK B) (Nonce NB) \<in> parts (knows Spy evs) \<longrightarrow>
      Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>) \<in> set evs \<longrightarrow>
      Says A B (Crypt (pubK B) (Nonce NB)) \<in> set evs"
by (erule ns_public.induct, auto)
(*>*)
theorem B_trusts_NS3:
 "\<lbrakk>Says B A  (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>) \<in> set evs;
   Says A' B (Crypt (pubK B) (Nonce NB)) \<in> set evs;
   A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>
  \<Longrightarrow> Says A B (Crypt (pubK B) (Nonce NB)) \<in> set evs"
(*<*)
by (blast intro: B_trusts_NS3_lemma)

(*** Overall guarantee for B ***)


(*If NS3 has been sent and the nonce NB agrees with the nonce B joined with
  NA, then A initiated the run using NA.*)
theorem B_trusts_protocol [rule_format]:
     "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk> \<Longrightarrow>
      Crypt (pubK B) (Nonce NB) \<in> parts (knows Spy evs) \<longrightarrow>
      Says B A  (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>) \<in> set evs \<longrightarrow>
      Says A B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs"
by (erule ns_public.induct, auto)
(*>*)

text {*
From similar assumptions, we can prove that @{text A} started the protocol
run by sending an instance of message~1 involving the nonce~@{text NA}\@. 
For this theorem, the conclusion is 
@{thm [display] (concl) B_trusts_protocol [no_vars]}
Analogous theorems can be proved for~@{text A}, stating that nonce~@{text NA}
remains secret and that message~2 really originates with~@{text B}.  Even the
flawed protocol establishes these properties for~@{text A};
the flaw only harms the second participant.

\medskip

Detailed information on this protocol verification technique can be found
elsewhere~\cite{paulson-jcs}, including proofs of an Internet
protocol~\cite{paulson-tls}.  We must stress that the protocol discussed
in this chapter is trivial.  There are only three messages; no keys are
exchanged; we merely have to prove that encrypted data remains secret. 
Real world protocols are much longer and distribute many secrets to their
participants.  To be realistic, the model has to include the possibility
of keys being lost dynamically due to carelessness.  If those keys have
been used to encrypt other sensitive information, there may be cascading
losses.  We may still be able to establish a bound on the losses and to
prove that other protocol runs function
correctly~\cite{paulson-yahalom}.  Proofs of real-world protocols follow
the strategy illustrated above, but the subgoals can
be much bigger and there are more of them.
\index{protocols!security|)}
*}

(*<*)end(*>*)
