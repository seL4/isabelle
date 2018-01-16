(*  Title:      HOL/Auth/TLS.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Inductive relation "tls" for the TLS (Transport Layer Security) protocol.
This protocol is essentially the same as SSL 3.0.

Abstracted from "The TLS Protocol, Version 1.0" by Tim Dierks and Christopher
Allen, Transport Layer Security Working Group, 21 May 1997,
INTERNET-DRAFT draft-ietf-tls-protocol-03.txt.  Section numbers below refer
to that memo.

An RSA cryptosystem is assumed, and X.509v3 certificates are abstracted down
to the trivial form {A, publicKey(A)}privateKey(Server), where Server is a
global signing authority.

A is the client and B is the server, not to be confused with the constant
Server, who is in charge of all public keys.

The model assumes that no fraudulent certificates are present, but it does
assume that some private keys are to the spy.

REMARK.  The event "Notes A \<lbrace>Agent B, Nonce PMS\<rbrace>" appears in ClientKeyExch,
CertVerify, ClientFinished to record that A knows M.  It is a note from A to
herself.  Nobody else can see it.  In ClientKeyExch, the Spy can substitute
his own certificate for A's, but he cannot replace A's note by one for himself.

The Note event avoids a weakness in the public-key model.  Each
agent's state is recorded as the trace of messages.  When the true client (A)
invents PMS, he encrypts PMS with B's public key before sending it.  The model
does not distinguish the original occurrence of such a message from a replay.
In the shared-key model, the ability to encrypt implies the ability to
decrypt, so the problem does not arise.

Proofs would be simpler if ClientKeyExch included A's name within
Crypt KB (Nonce PMS).  As things stand, there is much overlap between proofs
about that message (which B receives) and the stronger event
Notes A \<lbrace>Agent B, Nonce PMS\<rbrace>.
*)

section\<open>The TLS Protocol: Transport Layer Security\<close>

theory TLS imports Public "HOL-Library.Nat_Bijection" begin

definition certificate :: "[agent,key] => msg" where
    "certificate A KA == Crypt (priSK Server) \<lbrace>Agent A, Key KA\<rbrace>"

text\<open>TLS apparently does not require separate keypairs for encryption and
signature.  Therefore, we formalize signature as encryption using the
private encryption key.\<close>

datatype role = ClientRole | ServerRole

consts
  (*Pseudo-random function of Section 5*)
  PRF  :: "nat*nat*nat => nat"

  (*Client, server write keys are generated uniformly by function sessionK
    to avoid duplicating their properties.  They are distinguished by a
    tag (not a bool, to avoid the peculiarities of if-and-only-if).
    Session keys implicitly include MAC secrets.*)
  sessionK :: "(nat*nat*nat) * role => key"

abbreviation
  clientK :: "nat*nat*nat => key" where
  "clientK X == sessionK(X, ClientRole)"

abbreviation
  serverK :: "nat*nat*nat => key" where
  "serverK X == sessionK(X, ServerRole)"


specification (PRF)
  inj_PRF: "inj PRF"
  \<comment> \<open>the pseudo-random function is collision-free\<close>
   apply (rule exI [of _ "%(x,y,z). prod_encode(x, prod_encode(y,z))"])
   apply (simp add: inj_on_def prod_encode_eq)
   done

specification (sessionK)
  inj_sessionK: "inj sessionK"
  \<comment> \<open>sessionK is collision-free; also, no clientK clashes with any serverK.\<close>
   apply (rule exI [of _ 
         "%((x,y,z), r). prod_encode(case_role 0 1 r, 
                           prod_encode(x, prod_encode(y,z)))"])
   apply (simp add: inj_on_def prod_encode_eq split: role.split) 
   done

axiomatization where
  \<comment> \<open>sessionK makes symmetric keys\<close>
  isSym_sessionK: "sessionK nonces \<in> symKeys" and

  \<comment> \<open>sessionK never clashes with a long-term symmetric key  
     (they don't exist in TLS anyway)\<close>
  sessionK_neq_shrK [iff]: "sessionK nonces \<noteq> shrK A"


inductive_set tls :: "event list set"
  where
   Nil:  \<comment> \<open>The initial, empty trace\<close>
         "[] \<in> tls"

 | Fake: \<comment> \<open>The Spy may say anything he can say.  The sender field is correct,
          but agents don't use that information.\<close>
         "[| evsf \<in> tls;  X \<in> synth (analz (spies evsf)) |]
          ==> Says Spy B X # evsf \<in> tls"

 | SpyKeys: \<comment> \<open>The spy may apply @{term PRF} and @{term sessionK}
                to available nonces\<close>
         "[| evsSK \<in> tls;
             {Nonce NA, Nonce NB, Nonce M} <= analz (spies evsSK) |]
          ==> Notes Spy \<lbrace> Nonce (PRF(M,NA,NB)),
                           Key (sessionK((NA,NB,M),role))\<rbrace> # evsSK \<in> tls"

 | ClientHello:
         \<comment> \<open>(7.4.1.2)
           PA represents \<open>CLIENT_VERSION\<close>, \<open>CIPHER_SUITES\<close> and \<open>COMPRESSION_METHODS\<close>.
           It is uninterpreted but will be confirmed in the FINISHED messages.
           NA is CLIENT RANDOM, while SID is \<open>SESSION_ID\<close>.
           UNIX TIME is omitted because the protocol doesn't use it.
           May assume @{term "NA \<notin> range PRF"} because CLIENT RANDOM is 
           28 bytes while MASTER SECRET is 48 bytes\<close>
         "[| evsCH \<in> tls;  Nonce NA \<notin> used evsCH;  NA \<notin> range PRF |]
          ==> Says A B \<lbrace>Agent A, Nonce NA, Number SID, Number PA\<rbrace>
                # evsCH  \<in>  tls"

 | ServerHello:
         \<comment> \<open>7.4.1.3 of the TLS Internet-Draft
           PB represents \<open>CLIENT_VERSION\<close>, \<open>CIPHER_SUITE\<close> and \<open>COMPRESSION_METHOD\<close>.
           SERVER CERTIFICATE (7.4.2) is always present.
           \<open>CERTIFICATE_REQUEST\<close> (7.4.4) is implied.\<close>
         "[| evsSH \<in> tls;  Nonce NB \<notin> used evsSH;  NB \<notin> range PRF;
             Says A' B \<lbrace>Agent A, Nonce NA, Number SID, Number PA\<rbrace>
               \<in> set evsSH |]
          ==> Says B A \<lbrace>Nonce NB, Number SID, Number PB\<rbrace> # evsSH  \<in>  tls"

 | Certificate:
         \<comment> \<open>SERVER (7.4.2) or CLIENT (7.4.6) CERTIFICATE.\<close>
         "evsC \<in> tls ==> Says B A (certificate B (pubK B)) # evsC  \<in>  tls"

 | ClientKeyExch:
         \<comment> \<open>CLIENT KEY EXCHANGE (7.4.7).
           The client, A, chooses PMS, the PREMASTER SECRET.
           She encrypts PMS using the supplied KB, which ought to be pubK B.
           We assume @{term "PMS \<notin> range PRF"} because a clash betweem the PMS
           and another MASTER SECRET is highly unlikely (even though
           both items have the same length, 48 bytes).
           The Note event records in the trace that she knows PMS
               (see REMARK at top).\<close>
         "[| evsCX \<in> tls;  Nonce PMS \<notin> used evsCX;  PMS \<notin> range PRF;
             Says B' A (certificate B KB) \<in> set evsCX |]
          ==> Says A B (Crypt KB (Nonce PMS))
              # Notes A \<lbrace>Agent B, Nonce PMS\<rbrace>
              # evsCX  \<in>  tls"

 | CertVerify:
        \<comment> \<open>The optional Certificate Verify (7.4.8) message contains the
          specific components listed in the security analysis, F.1.1.2.
          It adds the pre-master-secret, which is also essential!
          Checking the signature, which is the only use of A's certificate,
          assures B of A's presence\<close>
         "[| evsCV \<in> tls;
             Says B' A \<lbrace>Nonce NB, Number SID, Number PB\<rbrace> \<in> set evsCV;
             Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evsCV |]
          ==> Says A B (Crypt (priK A) (Hash\<lbrace>Nonce NB, Agent B, Nonce PMS\<rbrace>))
              # evsCV  \<in>  tls"

        \<comment> \<open>Finally come the FINISHED messages (7.4.8), confirming PA and PB
          among other things.  The master-secret is PRF(PMS,NA,NB).
          Either party may send its message first.\<close>

 | ClientFinished:
        \<comment> \<open>The occurrence of \<open>Notes A \<lbrace>Agent B, Nonce PMS\<rbrace>\<close> stops the
          rule's applying when the Spy has satisfied the \<open>Says A B\<close> by
          repaying messages sent by the true client; in that case, the
          Spy does not know PMS and could not send ClientFinished.  One
          could simply put @{term "A\<noteq>Spy"} into the rule, but one should not
          expect the spy to be well-behaved.\<close>
         "[| evsCF \<in> tls;
             Says A  B \<lbrace>Agent A, Nonce NA, Number SID, Number PA\<rbrace>
               \<in> set evsCF;
             Says B' A \<lbrace>Nonce NB, Number SID, Number PB\<rbrace> \<in> set evsCF;
             Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evsCF;
             M = PRF(PMS,NA,NB) |]
          ==> Says A B (Crypt (clientK(NA,NB,M))
                        (Hash\<lbrace>Number SID, Nonce M,
                               Nonce NA, Number PA, Agent A,
                               Nonce NB, Number PB, Agent B\<rbrace>))
              # evsCF  \<in>  tls"

 | ServerFinished:
        \<comment> \<open>Keeping A' and A'' distinct means B cannot even check that the
          two messages originate from the same source.\<close>
         "[| evsSF \<in> tls;
             Says A' B  \<lbrace>Agent A, Nonce NA, Number SID, Number PA\<rbrace>
               \<in> set evsSF;
             Says B  A  \<lbrace>Nonce NB, Number SID, Number PB\<rbrace> \<in> set evsSF;
             Says A'' B (Crypt (pubK B) (Nonce PMS)) \<in> set evsSF;
             M = PRF(PMS,NA,NB) |]
          ==> Says B A (Crypt (serverK(NA,NB,M))
                        (Hash\<lbrace>Number SID, Nonce M,
                               Nonce NA, Number PA, Agent A,
                               Nonce NB, Number PB, Agent B\<rbrace>))
              # evsSF  \<in>  tls"

 | ClientAccepts:
        \<comment> \<open>Having transmitted ClientFinished and received an identical
          message encrypted with serverK, the client stores the parameters
          needed to resume this session.  The "Notes A ..." premise is
          used to prove \<open>Notes_master_imp_Crypt_PMS\<close>.\<close>
         "[| evsCA \<in> tls;
             Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evsCA;
             M = PRF(PMS,NA,NB);
             X = Hash\<lbrace>Number SID, Nonce M,
                       Nonce NA, Number PA, Agent A,
                       Nonce NB, Number PB, Agent B\<rbrace>;
             Says A  B (Crypt (clientK(NA,NB,M)) X) \<in> set evsCA;
             Says B' A (Crypt (serverK(NA,NB,M)) X) \<in> set evsCA |]
          ==>
             Notes A \<lbrace>Number SID, Agent A, Agent B, Nonce M\<rbrace> # evsCA  \<in>  tls"

 | ServerAccepts:
        \<comment> \<open>Having transmitted ServerFinished and received an identical
          message encrypted with clientK, the server stores the parameters
          needed to resume this session.  The "Says A'' B ..." premise is
          used to prove \<open>Notes_master_imp_Crypt_PMS\<close>.\<close>
         "[| evsSA \<in> tls;
             A \<noteq> B;
             Says A'' B (Crypt (pubK B) (Nonce PMS)) \<in> set evsSA;
             M = PRF(PMS,NA,NB);
             X = Hash\<lbrace>Number SID, Nonce M,
                       Nonce NA, Number PA, Agent A,
                       Nonce NB, Number PB, Agent B\<rbrace>;
             Says B  A (Crypt (serverK(NA,NB,M)) X) \<in> set evsSA;
             Says A' B (Crypt (clientK(NA,NB,M)) X) \<in> set evsSA |]
          ==>
             Notes B \<lbrace>Number SID, Agent A, Agent B, Nonce M\<rbrace> # evsSA  \<in>  tls"

 | ClientResume:
         \<comment> \<open>If A recalls the \<open>SESSION_ID\<close>, then she sends a FINISHED
             message using the new nonces and stored MASTER SECRET.\<close>
         "[| evsCR \<in> tls;
             Says A  B \<lbrace>Agent A, Nonce NA, Number SID, Number PA\<rbrace>: set evsCR;
             Says B' A \<lbrace>Nonce NB, Number SID, Number PB\<rbrace> \<in> set evsCR;
             Notes A \<lbrace>Number SID, Agent A, Agent B, Nonce M\<rbrace> \<in> set evsCR |]
          ==> Says A B (Crypt (clientK(NA,NB,M))
                        (Hash\<lbrace>Number SID, Nonce M,
                               Nonce NA, Number PA, Agent A,
                               Nonce NB, Number PB, Agent B\<rbrace>))
              # evsCR  \<in>  tls"

 | ServerResume:
         \<comment> \<open>Resumption (7.3):  If B finds the \<open>SESSION_ID\<close> then he can 
             send a FINISHED message using the recovered MASTER SECRET\<close>
         "[| evsSR \<in> tls;
             Says A' B \<lbrace>Agent A, Nonce NA, Number SID, Number PA\<rbrace>: set evsSR;
             Says B  A \<lbrace>Nonce NB, Number SID, Number PB\<rbrace> \<in> set evsSR;
             Notes B \<lbrace>Number SID, Agent A, Agent B, Nonce M\<rbrace> \<in> set evsSR |]
          ==> Says B A (Crypt (serverK(NA,NB,M))
                        (Hash\<lbrace>Number SID, Nonce M,
                               Nonce NA, Number PA, Agent A,
                               Nonce NB, Number PB, Agent B\<rbrace>)) # evsSR
                \<in>  tls"

 | Oops:
         \<comment> \<open>The most plausible compromise is of an old session key.  Losing
           the MASTER SECRET or PREMASTER SECRET is more serious but
           rather unlikely.  The assumption @{term "A\<noteq>Spy"} is essential: 
           otherwise the Spy could learn session keys merely by 
           replaying messages!\<close>
         "[| evso \<in> tls;  A \<noteq> Spy;
             Says A B (Crypt (sessionK((NA,NB,M),role)) X) \<in> set evso |]
          ==> Says A Spy (Key (sessionK((NA,NB,M),role))) # evso  \<in>  tls"

(*
Protocol goals:
* M, serverK(NA,NB,M) and clientK(NA,NB,M) will be known only to the two
     parties (though A is not necessarily authenticated).

* B upon receiving CertVerify knows that A is present (But this
    message is optional!)

* A upon receiving ServerFinished knows that B is present

* Each party who has received a FINISHED message can trust that the other
  party agrees on all message components, including PA and PB (thus foiling
  rollback attacks).
*)

declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]


text\<open>Automatically unfold the definition of "certificate"\<close>
declare certificate_def [simp]

text\<open>Injectiveness of key-generating functions\<close>
declare inj_PRF [THEN inj_eq, iff]
declare inj_sessionK [THEN inj_eq, iff]
declare isSym_sessionK [simp]


(*** clientK and serverK make symmetric keys; no clashes with pubK or priK ***)

lemma pubK_neq_sessionK [iff]: "publicKey b A \<noteq> sessionK arg"
by (simp add: symKeys_neq_imp_neq)

declare pubK_neq_sessionK [THEN not_sym, iff]

lemma priK_neq_sessionK [iff]: "invKey (publicKey b A) \<noteq> sessionK arg"
by (simp add: symKeys_neq_imp_neq)

declare priK_neq_sessionK [THEN not_sym, iff]

lemmas keys_distinct = pubK_neq_sessionK priK_neq_sessionK


subsection\<open>Protocol Proofs\<close>

text\<open>Possibility properties state that some traces run the protocol to the
end.  Four paths and 12 rules are considered.\<close>


(** These proofs assume that the Nonce_supply nonces
        (which have the form  @ N. Nonce N \<notin> used evs)
    lie outside the range of PRF.  It seems reasonable, but as it is needed
    only for the possibility theorems, it is not taken as an axiom.
**)


text\<open>Possibility property ending with ClientAccepts.\<close>
lemma "[| \<forall>evs. (@ N. Nonce N \<notin> used evs) \<notin> range PRF;  A \<noteq> B |]
      ==> \<exists>SID M. \<exists>evs \<in> tls.
            Notes A \<lbrace>Number SID, Agent A, Agent B, Nonce M\<rbrace> \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] tls.Nil
                    [THEN tls.ClientHello, THEN tls.ServerHello,
                     THEN tls.Certificate, THEN tls.ClientKeyExch,
                     THEN tls.ClientFinished, THEN tls.ServerFinished,
                     THEN tls.ClientAccepts], possibility, blast+)
done


text\<open>And one for ServerAccepts.  Either FINISHED message may come first.\<close>
lemma "[| \<forall>evs. (@ N. Nonce N \<notin> used evs) \<notin> range PRF; A \<noteq> B |]
      ==> \<exists>SID NA PA NB PB M. \<exists>evs \<in> tls.
           Notes B \<lbrace>Number SID, Agent A, Agent B, Nonce M\<rbrace> \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] tls.Nil
                    [THEN tls.ClientHello, THEN tls.ServerHello,
                     THEN tls.Certificate, THEN tls.ClientKeyExch,
                     THEN tls.ServerFinished, THEN tls.ClientFinished, 
                     THEN tls.ServerAccepts], possibility, blast+)
done


text\<open>Another one, for CertVerify (which is optional)\<close>
lemma "[| \<forall>evs. (@ N. Nonce N \<notin> used evs) \<notin> range PRF;  A \<noteq> B |]
       ==> \<exists>NB PMS. \<exists>evs \<in> tls.
              Says A B (Crypt (priK A) (Hash\<lbrace>Nonce NB, Agent B, Nonce PMS\<rbrace>)) 
                \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] tls.Nil
                    [THEN tls.ClientHello, THEN tls.ServerHello,
                     THEN tls.Certificate, THEN tls.ClientKeyExch,
                     THEN tls.CertVerify], possibility, blast+)
done


text\<open>Another one, for session resumption (both ServerResume and ClientResume).
  NO tls.Nil here: we refer to a previous session, not the empty trace.\<close>
lemma "[| evs0 \<in> tls;
          Notes A \<lbrace>Number SID, Agent A, Agent B, Nonce M\<rbrace> \<in> set evs0;
          Notes B \<lbrace>Number SID, Agent A, Agent B, Nonce M\<rbrace> \<in> set evs0;
          \<forall>evs. (@ N. Nonce N \<notin> used evs) \<notin> range PRF;
          A \<noteq> B |]
      ==> \<exists>NA PA NB PB X. \<exists>evs \<in> tls.
                X = Hash\<lbrace>Number SID, Nonce M,
                          Nonce NA, Number PA, Agent A,
                          Nonce NB, Number PB, Agent B\<rbrace>  &
                Says A B (Crypt (clientK(NA,NB,M)) X) \<in> set evs  &
                Says B A (Crypt (serverK(NA,NB,M)) X) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] tls.ClientHello
                    [THEN tls.ServerHello,
                     THEN tls.ServerResume, THEN tls.ClientResume], possibility, blast+)
done


subsection\<open>Inductive proofs about tls\<close>


(** Theorems of the form X \<notin> parts (spies evs) imply that NOBODY
    sends messages containing X! **)

text\<open>Spy never sees a good agent's private key!\<close>
lemma Spy_see_priK [simp]:
     "evs \<in> tls ==> (Key (privateKey b A) \<in> parts (spies evs)) = (A \<in> bad)"
by (erule tls.induct, force, simp_all, blast)

lemma Spy_analz_priK [simp]:
     "evs \<in> tls ==> (Key (privateKey b A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto

lemma Spy_see_priK_D [dest!]:
    "[|Key (privateKey b A) \<in> parts (knows Spy evs);  evs \<in> tls|] ==> A \<in> bad"
by (blast dest: Spy_see_priK)


text\<open>This lemma says that no false certificates exist.  One might extend the
  model to include bogus certificates for the agents, but there seems
  little point in doing so: the loss of their private keys is a worse
  breach of security.\<close>
lemma certificate_valid:
    "[| certificate B KB \<in> parts (spies evs);  evs \<in> tls |] ==> KB = pubK B"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all, blast) 
done

lemmas CX_KB_is_pubKB = Says_imp_spies [THEN parts.Inj, THEN certificate_valid]


subsubsection\<open>Properties of items found in Notes\<close>

lemma Notes_Crypt_parts_spies:
     "[| Notes A \<lbrace>Agent B, X\<rbrace> \<in> set evs;  evs \<in> tls |]
      ==> Crypt (pubK B) X \<in> parts (spies evs)"
apply (erule rev_mp)
apply (erule tls.induct, 
       frule_tac [7] CX_KB_is_pubKB, force, simp_all)
apply (blast intro: parts_insertI)
done

text\<open>C may be either A or B\<close>
lemma Notes_master_imp_Crypt_PMS:
     "[| Notes C \<lbrace>s, Agent A, Agent B, Nonce(PRF(PMS,NA,NB))\<rbrace> \<in> set evs;
         evs \<in> tls |]
      ==> Crypt (pubK B) (Nonce PMS) \<in> parts (spies evs)"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all)
txt\<open>Fake\<close>
apply (blast intro: parts_insertI)
txt\<open>Client, Server Accept\<close>
apply (blast dest!: Notes_Crypt_parts_spies)+
done

text\<open>Compared with the theorem above, both premise and conclusion are stronger\<close>
lemma Notes_master_imp_Notes_PMS:
     "[| Notes A \<lbrace>s, Agent A, Agent B, Nonce(PRF(PMS,NA,NB))\<rbrace> \<in> set evs;
         evs \<in> tls |]
      ==> Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all)
txt\<open>ServerAccepts\<close>
apply blast
done


subsubsection\<open>Protocol goal: if B receives CertVerify, then A sent it\<close>

text\<open>B can check A's signature if he has received A's certificate.\<close>
lemma TrustCertVerify_lemma:
     "[| X \<in> parts (spies evs);
         X = Crypt (priK A) (Hash\<lbrace>nb, Agent B, pms\<rbrace>);
         evs \<in> tls;  A \<notin> bad |]
      ==> Says A B X \<in> set evs"
apply (erule rev_mp, erule ssubst)
apply (erule tls.induct, force, simp_all, blast)
done

text\<open>Final version: B checks X using the distributed KA instead of priK A\<close>
lemma TrustCertVerify:
     "[| X \<in> parts (spies evs);
         X = Crypt (invKey KA) (Hash\<lbrace>nb, Agent B, pms\<rbrace>);
         certificate A KA \<in> parts (spies evs);
         evs \<in> tls;  A \<notin> bad |]
      ==> Says A B X \<in> set evs"
by (blast dest!: certificate_valid intro!: TrustCertVerify_lemma)


text\<open>If CertVerify is present then A has chosen PMS.\<close>
lemma UseCertVerify_lemma:
     "[| Crypt (priK A) (Hash\<lbrace>nb, Agent B, Nonce PMS\<rbrace>) \<in> parts (spies evs);
         evs \<in> tls;  A \<notin> bad |]
      ==> Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all, blast)
done

text\<open>Final version using the distributed KA instead of priK A\<close>
lemma UseCertVerify:
     "[| Crypt (invKey KA) (Hash\<lbrace>nb, Agent B, Nonce PMS\<rbrace>)
           \<in> parts (spies evs);
         certificate A KA \<in> parts (spies evs);
         evs \<in> tls;  A \<notin> bad |]
      ==> Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs"
by (blast dest!: certificate_valid intro!: UseCertVerify_lemma)


lemma no_Notes_A_PRF [simp]:
     "evs \<in> tls ==> Notes A \<lbrace>Agent B, Nonce (PRF x)\<rbrace> \<notin> set evs"
apply (erule tls.induct, force, simp_all)
txt\<open>ClientKeyExch: PMS is assumed to differ from any PRF.\<close>
apply blast
done


lemma MS_imp_PMS [dest!]:
     "[| Nonce (PRF (PMS,NA,NB)) \<in> parts (spies evs);  evs \<in> tls |]
      ==> Nonce PMS \<in> parts (spies evs)"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all)
txt\<open>Fake\<close>
apply (blast intro: parts_insertI)
txt\<open>Easy, e.g. by freshness\<close>
apply (blast dest: Notes_Crypt_parts_spies)+
done




subsubsection\<open>Unicity results for PMS, the pre-master-secret\<close>

text\<open>PMS determines B.\<close>
lemma Crypt_unique_PMS:
     "[| Crypt(pubK B)  (Nonce PMS) \<in> parts (spies evs);
         Crypt(pubK B') (Nonce PMS) \<in> parts (spies evs);
         Nonce PMS \<notin> analz (spies evs);
         evs \<in> tls |]
      ==> B=B'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)
apply (erule tls.induct, analz_mono_contra, force, simp_all (no_asm_simp))
txt\<open>Fake, ClientKeyExch\<close>
apply blast+
done


(** It is frustrating that we need two versions of the unicity results.
    But Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> determines both A and B.  Sometimes
    we have only the weaker assertion Crypt(pubK B) (Nonce PMS), which
    determines B alone, and only if PMS is secret.
**)

text\<open>In A's internal Note, PMS determines A and B.\<close>
lemma Notes_unique_PMS:
     "[| Notes A  \<lbrace>Agent B,  Nonce PMS\<rbrace> \<in> set evs;
         Notes A' \<lbrace>Agent B', Nonce PMS\<rbrace> \<in> set evs;
         evs \<in> tls |]
      ==> A=A' & B=B'"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, force, simp_all)
txt\<open>ClientKeyExch\<close>
apply (blast dest!: Notes_Crypt_parts_spies)
done


subsection\<open>Secrecy Theorems\<close>

text\<open>Key compromise lemma needed to prove @{term analz_image_keys}.
  No collection of keys can help the spy get new private keys.\<close>
lemma analz_image_priK [rule_format]:
     "evs \<in> tls
      ==> \<forall>KK. (Key(priK B) \<in> analz (Key`KK Un (spies evs))) =
          (priK B \<in> KK | B \<in> bad)"
apply (erule tls.induct)
apply (simp_all (no_asm_simp)
                del: image_insert
                add: image_Un [THEN sym]
                     insert_Key_image Un_assoc [THEN sym])
txt\<open>Fake\<close>
apply spy_analz
done


text\<open>slightly speeds up the big simplification below\<close>
lemma range_sessionkeys_not_priK:
     "KK <= range sessionK ==> priK B \<notin> KK"
by blast


text\<open>Lemma for the trivial direction of the if-and-only-if\<close>
lemma analz_image_keys_lemma:
     "(X \<in> analz (G Un H)) --> (X \<in> analz H)  ==>
      (X \<in> analz (G Un H))  =  (X \<in> analz H)"
by (blast intro: analz_mono [THEN subsetD])

(** Strangely, the following version doesn't work:
\<forall>Z. (Nonce N \<in> analz (Key`(sessionK`Z) Un (spies evs))) =
    (Nonce N \<in> analz (spies evs))"
**)

lemma analz_image_keys [rule_format]:
     "evs \<in> tls ==>
      \<forall>KK. KK <= range sessionK -->
              (Nonce N \<in> analz (Key`KK Un (spies evs))) =
              (Nonce N \<in> analz (spies evs))"
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (safe del: iffI)
apply (safe del: impI iffI intro!: analz_image_keys_lemma)
apply (simp_all (no_asm_simp)               (*faster*)
                del: image_insert imp_disjL (*reduces blow-up*)
                add: image_Un [THEN sym]  Un_assoc [THEN sym]
                     insert_Key_singleton
                     range_sessionkeys_not_priK analz_image_priK)
apply (simp_all add: insert_absorb)
txt\<open>Fake\<close>
apply spy_analz
done

text\<open>Knowing some session keys is no help in getting new nonces\<close>
lemma analz_insert_key [simp]:
     "evs \<in> tls ==>
      (Nonce N \<in> analz (insert (Key (sessionK z)) (spies evs))) =
      (Nonce N \<in> analz (spies evs))"
by (simp del: image_insert
         add: insert_Key_singleton analz_image_keys)


subsubsection\<open>Protocol goal: serverK(Na,Nb,M) and clientK(Na,Nb,M) remain secure\<close>

(** Some lemmas about session keys, comprising clientK and serverK **)


text\<open>Lemma: session keys are never used if PMS is fresh.
  Nonces don't have to agree, allowing session resumption.
  Converse doesn't hold; revealing PMS doesn't force the keys to be sent.
  THEY ARE NOT SUITABLE AS SAFE ELIM RULES.\<close>
lemma PMS_lemma:
     "[| Nonce PMS \<notin> parts (spies evs);
         K = sessionK((Na, Nb, PRF(PMS,NA,NB)), role);
         evs \<in> tls |]
   ==> Key K \<notin> parts (spies evs) & (\<forall>Y. Crypt K Y \<notin> parts (spies evs))"
apply (erule rev_mp, erule ssubst)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB) 
apply (force, simp_all (no_asm_simp))
txt\<open>Fake\<close>
apply (blast intro: parts_insertI)
txt\<open>SpyKeys\<close>
apply blast
txt\<open>Many others\<close>
apply (force dest!: Notes_Crypt_parts_spies Notes_master_imp_Crypt_PMS)+
done

lemma PMS_sessionK_not_spied:
     "[| Key (sessionK((Na, Nb, PRF(PMS,NA,NB)), role)) \<in> parts (spies evs);
         evs \<in> tls |]
      ==> Nonce PMS \<in> parts (spies evs)"
by (blast dest: PMS_lemma)

lemma PMS_Crypt_sessionK_not_spied:
     "[| Crypt (sessionK((Na, Nb, PRF(PMS,NA,NB)), role)) Y
           \<in> parts (spies evs);  evs \<in> tls |]
      ==> Nonce PMS \<in> parts (spies evs)"
by (blast dest: PMS_lemma)

text\<open>Write keys are never sent if M (MASTER SECRET) is secure.
  Converse fails; betraying M doesn't force the keys to be sent!
  The strong Oops condition can be weakened later by unicity reasoning,
  with some effort.
  NO LONGER USED: see \<open>clientK_not_spied\<close> and \<open>serverK_not_spied\<close>\<close>
lemma sessionK_not_spied:
     "[| \<forall>A. Says A Spy (Key (sessionK((NA,NB,M),role))) \<notin> set evs;
         Nonce M \<notin> analz (spies evs);  evs \<in> tls |]
      ==> Key (sessionK((NA,NB,M),role)) \<notin> parts (spies evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, analz_mono_contra)
apply (force, simp_all (no_asm_simp))
txt\<open>Fake, SpyKeys\<close>
apply blast+
done


text\<open>If A sends ClientKeyExch to an honest B, then the PMS will stay secret.\<close>
lemma Spy_not_see_PMS:
     "[| Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs;
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Nonce PMS \<notin> analz (spies evs)"
apply (erule rev_mp, erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt\<open>Fake\<close>
apply spy_analz
txt\<open>SpyKeys\<close>
apply force
apply (simp_all add: insert_absorb) 
txt\<open>ClientHello, ServerHello, ClientKeyExch: mostly freshness reasoning\<close>
apply (blast dest: Notes_Crypt_parts_spies)
apply (blast dest: Notes_Crypt_parts_spies)
apply (blast dest: Notes_Crypt_parts_spies)
txt\<open>ClientAccepts and ServerAccepts: because @{term "PMS \<notin> range PRF"}\<close>
apply force+
done


text\<open>If A sends ClientKeyExch to an honest B, then the MASTER SECRET
  will stay secret.\<close>
lemma Spy_not_see_MS:
     "[| Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs;
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Nonce (PRF(PMS,NA,NB)) \<notin> analz (spies evs)"
apply (erule rev_mp, erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt\<open>Fake\<close>
apply spy_analz
txt\<open>SpyKeys: by secrecy of the PMS, Spy cannot make the MS\<close>
apply (blast dest!: Spy_not_see_PMS)
apply (simp_all add: insert_absorb)
txt\<open>ClientAccepts and ServerAccepts: because PMS was already visible;
  others, freshness etc.\<close>
apply (blast dest: Notes_Crypt_parts_spies Spy_not_see_PMS 
                   Notes_imp_knows_Spy [THEN analz.Inj])+
done



subsubsection\<open>Weakening the Oops conditions for leakage of clientK\<close>

text\<open>If A created PMS then nobody else (except the Spy in replays)
  would send a message using a clientK generated from that PMS.\<close>
lemma Says_clientK_unique:
     "[| Says A' B' (Crypt (clientK(Na,Nb,PRF(PMS,NA,NB))) Y) \<in> set evs;
         Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs;
         evs \<in> tls;  A' \<noteq> Spy |]
      ==> A = A'"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all)
txt\<open>ClientKeyExch\<close>
apply (blast dest!: PMS_Crypt_sessionK_not_spied)
txt\<open>ClientFinished, ClientResume: by unicity of PMS\<close>
apply (blast dest!: Notes_master_imp_Notes_PMS 
             intro: Notes_unique_PMS [THEN conjunct1])+
done


text\<open>If A created PMS and has not leaked her clientK to the Spy,
  then it is completely secure: not even in parts!\<close>
lemma clientK_not_spied:
     "[| Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs;
         Says A Spy (Key (clientK(Na,Nb,PRF(PMS,NA,NB)))) \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;
         evs \<in> tls |]
      ==> Key (clientK(Na,Nb,PRF(PMS,NA,NB))) \<notin> parts (spies evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt\<open>ClientKeyExch\<close>
apply blast 
txt\<open>SpyKeys\<close>
apply (blast dest!: Spy_not_see_MS)
txt\<open>ClientKeyExch\<close>
apply (blast dest!: PMS_sessionK_not_spied)
txt\<open>Oops\<close>
apply (blast intro: Says_clientK_unique)
done


subsubsection\<open>Weakening the Oops conditions for leakage of serverK\<close>

text\<open>If A created PMS for B, then nobody other than B or the Spy would
  send a message using a serverK generated from that PMS.\<close>
lemma Says_serverK_unique:
     "[| Says B' A' (Crypt (serverK(Na,Nb,PRF(PMS,NA,NB))) Y) \<in> set evs;
         Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs;
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad;  B' \<noteq> Spy |]
      ==> B = B'"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all)
txt\<open>ClientKeyExch\<close>
apply (blast dest!: PMS_Crypt_sessionK_not_spied)
txt\<open>ServerResume, ServerFinished: by unicity of PMS\<close>
apply (blast dest!: Notes_master_imp_Crypt_PMS 
             dest: Spy_not_see_PMS Notes_Crypt_parts_spies Crypt_unique_PMS)+
done


text\<open>If A created PMS for B, and B has not leaked his serverK to the Spy,
  then it is completely secure: not even in parts!\<close>
lemma serverK_not_spied:
     "[| Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs;
         Says B Spy (Key(serverK(Na,Nb,PRF(PMS,NA,NB)))) \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> tls |]
      ==> Key (serverK(Na,Nb,PRF(PMS,NA,NB))) \<notin> parts (spies evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt\<open>Fake\<close>
apply blast 
txt\<open>SpyKeys\<close>
apply (blast dest!: Spy_not_see_MS)
txt\<open>ClientKeyExch\<close>
apply (blast dest!: PMS_sessionK_not_spied)
txt\<open>Oops\<close>
apply (blast intro: Says_serverK_unique)
done


subsubsection\<open>Protocol goals: if A receives ServerFinished, then B is present
     and has used the quoted values PA, PB, etc.  Note that it is up to A
     to compare PA with what she originally sent.\<close>

text\<open>The mention of her name (A) in X assures A that B knows who she is.\<close>
lemma TrustServerFinished [rule_format]:
     "[| X = Crypt (serverK(Na,Nb,M))
               (Hash\<lbrace>Number SID, Nonce M,
                      Nonce Na, Number PA, Agent A,
                      Nonce Nb, Number PB, Agent B\<rbrace>);
         M = PRF(PMS,NA,NB);
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Says B Spy (Key(serverK(Na,Nb,M))) \<notin> set evs -->
          Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs -->
          X \<in> parts (spies evs) --> Says B A X \<in> set evs"
apply (erule ssubst)+
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt\<open>Fake: the Spy doesn't have the critical session key!\<close>
apply (blast dest: serverK_not_spied)
txt\<open>ClientKeyExch\<close>
apply (blast dest!: PMS_Crypt_sessionK_not_spied)
done

text\<open>This version refers not to ServerFinished but to any message from B.
  We don't assume B has received CertVerify, and an intruder could
  have changed A's identity in all other messages, so we can't be sure
  that B sends his message to A.  If CLIENT KEY EXCHANGE were augmented
  to bind A's identity with PMS, then we could replace A' by A below.\<close>
lemma TrustServerMsg [rule_format]:
     "[| M = PRF(PMS,NA,NB);  evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Says B Spy (Key(serverK(Na,Nb,M))) \<notin> set evs -->
          Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs -->
          Crypt (serverK(Na,Nb,M)) Y \<in> parts (spies evs)  -->
          (\<exists>A'. Says B A' (Crypt (serverK(Na,Nb,M)) Y) \<in> set evs)"
apply (erule ssubst)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp) add: ex_disj_distrib)
txt\<open>Fake: the Spy doesn't have the critical session key!\<close>
apply (blast dest: serverK_not_spied)
txt\<open>ClientKeyExch\<close>
apply (clarify, blast dest!: PMS_Crypt_sessionK_not_spied)
txt\<open>ServerResume, ServerFinished: by unicity of PMS\<close>
apply (blast dest!: Notes_master_imp_Crypt_PMS 
             dest: Spy_not_see_PMS Notes_Crypt_parts_spies Crypt_unique_PMS)+
done


subsubsection\<open>Protocol goal: if B receives any message encrypted with clientK
      then A has sent it\<close>

text\<open>ASSUMING that A chose PMS.  Authentication is
     assumed here; B cannot verify it.  But if the message is
     ClientFinished, then B can then check the quoted values PA, PB, etc.\<close>

lemma TrustClientMsg [rule_format]:
     "[| M = PRF(PMS,NA,NB);  evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Says A Spy (Key(clientK(Na,Nb,M))) \<notin> set evs -->
          Notes A \<lbrace>Agent B, Nonce PMS\<rbrace> \<in> set evs -->
          Crypt (clientK(Na,Nb,M)) Y \<in> parts (spies evs) -->
          Says A B (Crypt (clientK(Na,Nb,M)) Y) \<in> set evs"
apply (erule ssubst)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt\<open>Fake: the Spy doesn't have the critical session key!\<close>
apply (blast dest: clientK_not_spied)
txt\<open>ClientKeyExch\<close>
apply (blast dest!: PMS_Crypt_sessionK_not_spied)
txt\<open>ClientFinished, ClientResume: by unicity of PMS\<close>
apply (blast dest!: Notes_master_imp_Notes_PMS dest: Notes_unique_PMS)+
done


subsubsection\<open>Protocol goal: if B receives ClientFinished, and if B is able to
     check a CertVerify from A, then A has used the quoted
     values PA, PB, etc.  Even this one requires A to be uncompromised.\<close>
lemma AuthClientFinished:
     "[| M = PRF(PMS,NA,NB);
         Says A Spy (Key(clientK(Na,Nb,M))) \<notin> set evs;
         Says A' B (Crypt (clientK(Na,Nb,M)) Y) \<in> set evs;
         certificate A KA \<in> parts (spies evs);
         Says A'' B (Crypt (invKey KA) (Hash\<lbrace>nb, Agent B, Nonce PMS\<rbrace>))
           \<in> set evs;
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Says A B (Crypt (clientK(Na,Nb,M)) Y) \<in> set evs"
by (blast intro!: TrustClientMsg UseCertVerify)

(*22/9/97: loads in 622s, which is 10 minutes 22 seconds*)
(*24/9/97: loads in 672s, which is 11 minutes 12 seconds [stronger theorems]*)
(*29/9/97: loads in 481s, after removing Certificate from ClientKeyExch*)
(*30/9/97: loads in 476s, after removing unused theorems*)
(*30/9/97: loads in 448s, after fixing ServerResume*)

(*08/9/97: loads in 189s (pike), after much reorganization,
           back to 621s on albatross?*)

(*10/2/99: loads in 139s (pike)
           down to 433s on albatross*)

(*5/5/01: conversion to Isar script
          loads in 137s (perch)
          the last ML version loaded in 122s on perch, a 600MHz machine:
                twice as fast as pike.  No idea why it's so much slower!
          The Isar script is slower still, perhaps because simp_all simplifies
          the assumptions be default.
*)

(*20/11/11: loads in 5.8s elapses time, 9.3s CPU time on dual-core laptop*)

end
