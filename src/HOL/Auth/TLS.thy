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

REMARK.  The event "Notes A {|Agent B, Nonce PMS|}" appears in ClientKeyExch,
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
Notes A {|Agent B, Nonce PMS|}.
*)

header{*The TLS Protocol: Transport Layer Security*}

theory TLS imports Public "~~/src/HOL/Library/Nat_Bijection" begin

definition certificate :: "[agent,key] => msg" where
    "certificate A KA == Crypt (priSK Server) {|Agent A, Key KA|}"

text{*TLS apparently does not require separate keypairs for encryption and
signature.  Therefore, we formalize signature as encryption using the
private encryption key.*}

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
  --{*the pseudo-random function is collision-free*}
   apply (rule exI [of _ "%(x,y,z). prod_encode(x, prod_encode(y,z))"])
   apply (simp add: inj_on_def prod_encode_eq)
   done

specification (sessionK)
  inj_sessionK: "inj sessionK"
  --{*sessionK is collision-free; also, no clientK clashes with any serverK.*}
   apply (rule exI [of _ 
         "%((x,y,z), r). prod_encode(role_case 0 1 r, 
                           prod_encode(x, prod_encode(y,z)))"])
   apply (simp add: inj_on_def prod_encode_eq split: role.split) 
   done

axiomatization where
  --{*sessionK makes symmetric keys*}
  isSym_sessionK: "sessionK nonces \<in> symKeys" and

  --{*sessionK never clashes with a long-term symmetric key  
     (they don't exist in TLS anyway)*}
  sessionK_neq_shrK [iff]: "sessionK nonces \<noteq> shrK A"


inductive_set tls :: "event list set"
  where
   Nil:  --{*The initial, empty trace*}
         "[] \<in> tls"

 | Fake: --{*The Spy may say anything he can say.  The sender field is correct,
          but agents don't use that information.*}
         "[| evsf \<in> tls;  X \<in> synth (analz (spies evsf)) |]
          ==> Says Spy B X # evsf \<in> tls"

 | SpyKeys: --{*The spy may apply @{term PRF} and @{term sessionK}
                to available nonces*}
         "[| evsSK \<in> tls;
             {Nonce NA, Nonce NB, Nonce M} <= analz (spies evsSK) |]
          ==> Notes Spy {| Nonce (PRF(M,NA,NB)),
                           Key (sessionK((NA,NB,M),role)) |} # evsSK \<in> tls"

 | ClientHello:
         --{*(7.4.1.2)
           PA represents @{text CLIENT_VERSION}, @{text CIPHER_SUITES} and @{text COMPRESSION_METHODS}.
           It is uninterpreted but will be confirmed in the FINISHED messages.
           NA is CLIENT RANDOM, while SID is @{text SESSION_ID}.
           UNIX TIME is omitted because the protocol doesn't use it.
           May assume @{term "NA \<notin> range PRF"} because CLIENT RANDOM is 
           28 bytes while MASTER SECRET is 48 bytes*}
         "[| evsCH \<in> tls;  Nonce NA \<notin> used evsCH;  NA \<notin> range PRF |]
          ==> Says A B {|Agent A, Nonce NA, Number SID, Number PA|}
                # evsCH  \<in>  tls"

 | ServerHello:
         --{*7.4.1.3 of the TLS Internet-Draft
           PB represents @{text CLIENT_VERSION}, @{text CIPHER_SUITE} and @{text COMPRESSION_METHOD}.
           SERVER CERTIFICATE (7.4.2) is always present.
           @{text CERTIFICATE_REQUEST} (7.4.4) is implied.*}
         "[| evsSH \<in> tls;  Nonce NB \<notin> used evsSH;  NB \<notin> range PRF;
             Says A' B {|Agent A, Nonce NA, Number SID, Number PA|}
               \<in> set evsSH |]
          ==> Says B A {|Nonce NB, Number SID, Number PB|} # evsSH  \<in>  tls"

 | Certificate:
         --{*SERVER (7.4.2) or CLIENT (7.4.6) CERTIFICATE.*}
         "evsC \<in> tls ==> Says B A (certificate B (pubK B)) # evsC  \<in>  tls"

 | ClientKeyExch:
         --{*CLIENT KEY EXCHANGE (7.4.7).
           The client, A, chooses PMS, the PREMASTER SECRET.
           She encrypts PMS using the supplied KB, which ought to be pubK B.
           We assume @{term "PMS \<notin> range PRF"} because a clash betweem the PMS
           and another MASTER SECRET is highly unlikely (even though
           both items have the same length, 48 bytes).
           The Note event records in the trace that she knows PMS
               (see REMARK at top). *}
         "[| evsCX \<in> tls;  Nonce PMS \<notin> used evsCX;  PMS \<notin> range PRF;
             Says B' A (certificate B KB) \<in> set evsCX |]
          ==> Says A B (Crypt KB (Nonce PMS))
              # Notes A {|Agent B, Nonce PMS|}
              # evsCX  \<in>  tls"

 | CertVerify:
        --{*The optional Certificate Verify (7.4.8) message contains the
          specific components listed in the security analysis, F.1.1.2.
          It adds the pre-master-secret, which is also essential!
          Checking the signature, which is the only use of A's certificate,
          assures B of A's presence*}
         "[| evsCV \<in> tls;
             Says B' A {|Nonce NB, Number SID, Number PB|} \<in> set evsCV;
             Notes A {|Agent B, Nonce PMS|} \<in> set evsCV |]
          ==> Says A B (Crypt (priK A) (Hash{|Nonce NB, Agent B, Nonce PMS|}))
              # evsCV  \<in>  tls"

        --{*Finally come the FINISHED messages (7.4.8), confirming PA and PB
          among other things.  The master-secret is PRF(PMS,NA,NB).
          Either party may send its message first.*}

 | ClientFinished:
        --{*The occurrence of Notes A {|Agent B, Nonce PMS|} stops the
          rule's applying when the Spy has satisfied the "Says A B" by
          repaying messages sent by the true client; in that case, the
          Spy does not know PMS and could not send ClientFinished.  One
          could simply put @{term "A\<noteq>Spy"} into the rule, but one should not
          expect the spy to be well-behaved.*}
         "[| evsCF \<in> tls;
             Says A  B {|Agent A, Nonce NA, Number SID, Number PA|}
               \<in> set evsCF;
             Says B' A {|Nonce NB, Number SID, Number PB|} \<in> set evsCF;
             Notes A {|Agent B, Nonce PMS|} \<in> set evsCF;
             M = PRF(PMS,NA,NB) |]
          ==> Says A B (Crypt (clientK(NA,NB,M))
                        (Hash{|Number SID, Nonce M,
                               Nonce NA, Number PA, Agent A,
                               Nonce NB, Number PB, Agent B|}))
              # evsCF  \<in>  tls"

 | ServerFinished:
        --{*Keeping A' and A'' distinct means B cannot even check that the
          two messages originate from the same source. *}
         "[| evsSF \<in> tls;
             Says A' B  {|Agent A, Nonce NA, Number SID, Number PA|}
               \<in> set evsSF;
             Says B  A  {|Nonce NB, Number SID, Number PB|} \<in> set evsSF;
             Says A'' B (Crypt (pubK B) (Nonce PMS)) \<in> set evsSF;
             M = PRF(PMS,NA,NB) |]
          ==> Says B A (Crypt (serverK(NA,NB,M))
                        (Hash{|Number SID, Nonce M,
                               Nonce NA, Number PA, Agent A,
                               Nonce NB, Number PB, Agent B|}))
              # evsSF  \<in>  tls"

 | ClientAccepts:
        --{*Having transmitted ClientFinished and received an identical
          message encrypted with serverK, the client stores the parameters
          needed to resume this session.  The "Notes A ..." premise is
          used to prove @{text Notes_master_imp_Crypt_PMS}.*}
         "[| evsCA \<in> tls;
             Notes A {|Agent B, Nonce PMS|} \<in> set evsCA;
             M = PRF(PMS,NA,NB);
             X = Hash{|Number SID, Nonce M,
                       Nonce NA, Number PA, Agent A,
                       Nonce NB, Number PB, Agent B|};
             Says A  B (Crypt (clientK(NA,NB,M)) X) \<in> set evsCA;
             Says B' A (Crypt (serverK(NA,NB,M)) X) \<in> set evsCA |]
          ==>
             Notes A {|Number SID, Agent A, Agent B, Nonce M|} # evsCA  \<in>  tls"

 | ServerAccepts:
        --{*Having transmitted ServerFinished and received an identical
          message encrypted with clientK, the server stores the parameters
          needed to resume this session.  The "Says A'' B ..." premise is
          used to prove @{text Notes_master_imp_Crypt_PMS}.*}
         "[| evsSA \<in> tls;
             A \<noteq> B;
             Says A'' B (Crypt (pubK B) (Nonce PMS)) \<in> set evsSA;
             M = PRF(PMS,NA,NB);
             X = Hash{|Number SID, Nonce M,
                       Nonce NA, Number PA, Agent A,
                       Nonce NB, Number PB, Agent B|};
             Says B  A (Crypt (serverK(NA,NB,M)) X) \<in> set evsSA;
             Says A' B (Crypt (clientK(NA,NB,M)) X) \<in> set evsSA |]
          ==>
             Notes B {|Number SID, Agent A, Agent B, Nonce M|} # evsSA  \<in>  tls"

 | ClientResume:
         --{*If A recalls the @{text SESSION_ID}, then she sends a FINISHED
             message using the new nonces and stored MASTER SECRET.*}
         "[| evsCR \<in> tls;
             Says A  B {|Agent A, Nonce NA, Number SID, Number PA|}: set evsCR;
             Says B' A {|Nonce NB, Number SID, Number PB|} \<in> set evsCR;
             Notes A {|Number SID, Agent A, Agent B, Nonce M|} \<in> set evsCR |]
          ==> Says A B (Crypt (clientK(NA,NB,M))
                        (Hash{|Number SID, Nonce M,
                               Nonce NA, Number PA, Agent A,
                               Nonce NB, Number PB, Agent B|}))
              # evsCR  \<in>  tls"

 | ServerResume:
         --{*Resumption (7.3):  If B finds the @{text SESSION_ID} then he can 
             send a FINISHED message using the recovered MASTER SECRET*}
         "[| evsSR \<in> tls;
             Says A' B {|Agent A, Nonce NA, Number SID, Number PA|}: set evsSR;
             Says B  A {|Nonce NB, Number SID, Number PB|} \<in> set evsSR;
             Notes B {|Number SID, Agent A, Agent B, Nonce M|} \<in> set evsSR |]
          ==> Says B A (Crypt (serverK(NA,NB,M))
                        (Hash{|Number SID, Nonce M,
                               Nonce NA, Number PA, Agent A,
                               Nonce NB, Number PB, Agent B|})) # evsSR
                \<in>  tls"

 | Oops:
         --{*The most plausible compromise is of an old session key.  Losing
           the MASTER SECRET or PREMASTER SECRET is more serious but
           rather unlikely.  The assumption @{term "A\<noteq>Spy"} is essential: 
           otherwise the Spy could learn session keys merely by 
           replaying messages!*}
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


text{*Automatically unfold the definition of "certificate"*}
declare certificate_def [simp]

text{*Injectiveness of key-generating functions*}
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


subsection{*Protocol Proofs*}

text{*Possibility properties state that some traces run the protocol to the
end.  Four paths and 12 rules are considered.*}


(** These proofs assume that the Nonce_supply nonces
        (which have the form  @ N. Nonce N \<notin> used evs)
    lie outside the range of PRF.  It seems reasonable, but as it is needed
    only for the possibility theorems, it is not taken as an axiom.
**)


text{*Possibility property ending with ClientAccepts.*}
lemma "[| \<forall>evs. (@ N. Nonce N \<notin> used evs) \<notin> range PRF;  A \<noteq> B |]
      ==> \<exists>SID M. \<exists>evs \<in> tls.
            Notes A {|Number SID, Agent A, Agent B, Nonce M|} \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] tls.Nil
                    [THEN tls.ClientHello, THEN tls.ServerHello,
                     THEN tls.Certificate, THEN tls.ClientKeyExch,
                     THEN tls.ClientFinished, THEN tls.ServerFinished,
                     THEN tls.ClientAccepts], possibility, blast+)
done


text{*And one for ServerAccepts.  Either FINISHED message may come first.*}
lemma "[| \<forall>evs. (@ N. Nonce N \<notin> used evs) \<notin> range PRF; A \<noteq> B |]
      ==> \<exists>SID NA PA NB PB M. \<exists>evs \<in> tls.
           Notes B {|Number SID, Agent A, Agent B, Nonce M|} \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] tls.Nil
                    [THEN tls.ClientHello, THEN tls.ServerHello,
                     THEN tls.Certificate, THEN tls.ClientKeyExch,
                     THEN tls.ServerFinished, THEN tls.ClientFinished, 
                     THEN tls.ServerAccepts], possibility, blast+)
done


text{*Another one, for CertVerify (which is optional)*}
lemma "[| \<forall>evs. (@ N. Nonce N \<notin> used evs) \<notin> range PRF;  A \<noteq> B |]
       ==> \<exists>NB PMS. \<exists>evs \<in> tls.
              Says A B (Crypt (priK A) (Hash{|Nonce NB, Agent B, Nonce PMS|})) 
                \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] tls.Nil
                    [THEN tls.ClientHello, THEN tls.ServerHello,
                     THEN tls.Certificate, THEN tls.ClientKeyExch,
                     THEN tls.CertVerify], possibility, blast+)
done


text{*Another one, for session resumption (both ServerResume and ClientResume).
  NO tls.Nil here: we refer to a previous session, not the empty trace.*}
lemma "[| evs0 \<in> tls;
          Notes A {|Number SID, Agent A, Agent B, Nonce M|} \<in> set evs0;
          Notes B {|Number SID, Agent A, Agent B, Nonce M|} \<in> set evs0;
          \<forall>evs. (@ N. Nonce N \<notin> used evs) \<notin> range PRF;
          A \<noteq> B |]
      ==> \<exists>NA PA NB PB X. \<exists>evs \<in> tls.
                X = Hash{|Number SID, Nonce M,
                          Nonce NA, Number PA, Agent A,
                          Nonce NB, Number PB, Agent B|}  &
                Says A B (Crypt (clientK(NA,NB,M)) X) \<in> set evs  &
                Says B A (Crypt (serverK(NA,NB,M)) X) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] tls.ClientHello
                    [THEN tls.ServerHello,
                     THEN tls.ServerResume, THEN tls.ClientResume], possibility, blast+)
done


subsection{*Inductive proofs about tls*}


(** Theorems of the form X \<notin> parts (spies evs) imply that NOBODY
    sends messages containing X! **)

text{*Spy never sees a good agent's private key!*}
lemma Spy_see_priK [simp]:
     "evs \<in> tls ==> (Key (privateKey b A) \<in> parts (spies evs)) = (A \<in> bad)"
by (erule tls.induct, force, simp_all, blast)

lemma Spy_analz_priK [simp]:
     "evs \<in> tls ==> (Key (privateKey b A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto

lemma Spy_see_priK_D [dest!]:
    "[|Key (privateKey b A) \<in> parts (knows Spy evs);  evs \<in> tls|] ==> A \<in> bad"
by (blast dest: Spy_see_priK)


text{*This lemma says that no false certificates exist.  One might extend the
  model to include bogus certificates for the agents, but there seems
  little point in doing so: the loss of their private keys is a worse
  breach of security.*}
lemma certificate_valid:
    "[| certificate B KB \<in> parts (spies evs);  evs \<in> tls |] ==> KB = pubK B"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all, blast) 
done

lemmas CX_KB_is_pubKB = Says_imp_spies [THEN parts.Inj, THEN certificate_valid]


subsubsection{*Properties of items found in Notes*}

lemma Notes_Crypt_parts_spies:
     "[| Notes A {|Agent B, X|} \<in> set evs;  evs \<in> tls |]
      ==> Crypt (pubK B) X \<in> parts (spies evs)"
apply (erule rev_mp)
apply (erule tls.induct, 
       frule_tac [7] CX_KB_is_pubKB, force, simp_all)
apply (blast intro: parts_insertI)
done

text{*C may be either A or B*}
lemma Notes_master_imp_Crypt_PMS:
     "[| Notes C {|s, Agent A, Agent B, Nonce(PRF(PMS,NA,NB))|} \<in> set evs;
         evs \<in> tls |]
      ==> Crypt (pubK B) (Nonce PMS) \<in> parts (spies evs)"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all)
txt{*Fake*}
apply (blast intro: parts_insertI)
txt{*Client, Server Accept*}
apply (blast dest!: Notes_Crypt_parts_spies)+
done

text{*Compared with the theorem above, both premise and conclusion are stronger*}
lemma Notes_master_imp_Notes_PMS:
     "[| Notes A {|s, Agent A, Agent B, Nonce(PRF(PMS,NA,NB))|} \<in> set evs;
         evs \<in> tls |]
      ==> Notes A {|Agent B, Nonce PMS|} \<in> set evs"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all)
txt{*ServerAccepts*}
apply blast
done


subsubsection{*Protocol goal: if B receives CertVerify, then A sent it*}

text{*B can check A's signature if he has received A's certificate.*}
lemma TrustCertVerify_lemma:
     "[| X \<in> parts (spies evs);
         X = Crypt (priK A) (Hash{|nb, Agent B, pms|});
         evs \<in> tls;  A \<notin> bad |]
      ==> Says A B X \<in> set evs"
apply (erule rev_mp, erule ssubst)
apply (erule tls.induct, force, simp_all, blast)
done

text{*Final version: B checks X using the distributed KA instead of priK A*}
lemma TrustCertVerify:
     "[| X \<in> parts (spies evs);
         X = Crypt (invKey KA) (Hash{|nb, Agent B, pms|});
         certificate A KA \<in> parts (spies evs);
         evs \<in> tls;  A \<notin> bad |]
      ==> Says A B X \<in> set evs"
by (blast dest!: certificate_valid intro!: TrustCertVerify_lemma)


text{*If CertVerify is present then A has chosen PMS.*}
lemma UseCertVerify_lemma:
     "[| Crypt (priK A) (Hash{|nb, Agent B, Nonce PMS|}) \<in> parts (spies evs);
         evs \<in> tls;  A \<notin> bad |]
      ==> Notes A {|Agent B, Nonce PMS|} \<in> set evs"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all, blast)
done

text{*Final version using the distributed KA instead of priK A*}
lemma UseCertVerify:
     "[| Crypt (invKey KA) (Hash{|nb, Agent B, Nonce PMS|})
           \<in> parts (spies evs);
         certificate A KA \<in> parts (spies evs);
         evs \<in> tls;  A \<notin> bad |]
      ==> Notes A {|Agent B, Nonce PMS|} \<in> set evs"
by (blast dest!: certificate_valid intro!: UseCertVerify_lemma)


lemma no_Notes_A_PRF [simp]:
     "evs \<in> tls ==> Notes A {|Agent B, Nonce (PRF x)|} \<notin> set evs"
apply (erule tls.induct, force, simp_all)
txt{*ClientKeyExch: PMS is assumed to differ from any PRF.*}
apply blast
done


lemma MS_imp_PMS [dest!]:
     "[| Nonce (PRF (PMS,NA,NB)) \<in> parts (spies evs);  evs \<in> tls |]
      ==> Nonce PMS \<in> parts (spies evs)"
apply (erule rev_mp)
apply (erule tls.induct, force, simp_all)
txt{*Fake*}
apply (blast intro: parts_insertI)
txt{*Easy, e.g. by freshness*}
apply (blast dest: Notes_Crypt_parts_spies)+
done




subsubsection{*Unicity results for PMS, the pre-master-secret*}

text{*PMS determines B.*}
lemma Crypt_unique_PMS:
     "[| Crypt(pubK B)  (Nonce PMS) \<in> parts (spies evs);
         Crypt(pubK B') (Nonce PMS) \<in> parts (spies evs);
         Nonce PMS \<notin> analz (spies evs);
         evs \<in> tls |]
      ==> B=B'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)
apply (erule tls.induct, analz_mono_contra, force, simp_all (no_asm_simp))
txt{*Fake, ClientKeyExch*}
apply blast+
done


(** It is frustrating that we need two versions of the unicity results.
    But Notes A {|Agent B, Nonce PMS|} determines both A and B.  Sometimes
    we have only the weaker assertion Crypt(pubK B) (Nonce PMS), which
    determines B alone, and only if PMS is secret.
**)

text{*In A's internal Note, PMS determines A and B.*}
lemma Notes_unique_PMS:
     "[| Notes A  {|Agent B,  Nonce PMS|} \<in> set evs;
         Notes A' {|Agent B', Nonce PMS|} \<in> set evs;
         evs \<in> tls |]
      ==> A=A' & B=B'"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, force, simp_all)
txt{*ClientKeyExch*}
apply (blast dest!: Notes_Crypt_parts_spies)
done


subsection{*Secrecy Theorems*}

text{*Key compromise lemma needed to prove @{term analz_image_keys}.
  No collection of keys can help the spy get new private keys.*}
lemma analz_image_priK [rule_format]:
     "evs \<in> tls
      ==> \<forall>KK. (Key(priK B) \<in> analz (Key`KK Un (spies evs))) =
          (priK B \<in> KK | B \<in> bad)"
apply (erule tls.induct)
apply (simp_all (no_asm_simp)
                del: image_insert
                add: image_Un [THEN sym]
                     insert_Key_image Un_assoc [THEN sym])
txt{*Fake*}
apply spy_analz
done


text{*slightly speeds up the big simplification below*}
lemma range_sessionkeys_not_priK:
     "KK <= range sessionK ==> priK B \<notin> KK"
by blast


text{*Lemma for the trivial direction of the if-and-only-if*}
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
txt{*Fake*}
apply spy_analz
done

text{*Knowing some session keys is no help in getting new nonces*}
lemma analz_insert_key [simp]:
     "evs \<in> tls ==>
      (Nonce N \<in> analz (insert (Key (sessionK z)) (spies evs))) =
      (Nonce N \<in> analz (spies evs))"
by (simp del: image_insert
         add: insert_Key_singleton analz_image_keys)


subsubsection{*Protocol goal: serverK(Na,Nb,M) and clientK(Na,Nb,M) remain secure*}

(** Some lemmas about session keys, comprising clientK and serverK **)


text{*Lemma: session keys are never used if PMS is fresh.
  Nonces don't have to agree, allowing session resumption.
  Converse doesn't hold; revealing PMS doesn't force the keys to be sent.
  THEY ARE NOT SUITABLE AS SAFE ELIM RULES.*}
lemma PMS_lemma:
     "[| Nonce PMS \<notin> parts (spies evs);
         K = sessionK((Na, Nb, PRF(PMS,NA,NB)), role);
         evs \<in> tls |]
   ==> Key K \<notin> parts (spies evs) & (\<forall>Y. Crypt K Y \<notin> parts (spies evs))"
apply (erule rev_mp, erule ssubst)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB) 
apply (force, simp_all (no_asm_simp))
txt{*Fake*}
apply (blast intro: parts_insertI)
txt{*SpyKeys*}
apply blast
txt{*Many others*}
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

text{*Write keys are never sent if M (MASTER SECRET) is secure.
  Converse fails; betraying M doesn't force the keys to be sent!
  The strong Oops condition can be weakened later by unicity reasoning,
  with some effort.
  NO LONGER USED: see @{text clientK_not_spied} and @{text serverK_not_spied}*}
lemma sessionK_not_spied:
     "[| \<forall>A. Says A Spy (Key (sessionK((NA,NB,M),role))) \<notin> set evs;
         Nonce M \<notin> analz (spies evs);  evs \<in> tls |]
      ==> Key (sessionK((NA,NB,M),role)) \<notin> parts (spies evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, analz_mono_contra)
apply (force, simp_all (no_asm_simp))
txt{*Fake, SpyKeys*}
apply blast+
done


text{*If A sends ClientKeyExch to an honest B, then the PMS will stay secret.*}
lemma Spy_not_see_PMS:
     "[| Notes A {|Agent B, Nonce PMS|} \<in> set evs;
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Nonce PMS \<notin> analz (spies evs)"
apply (erule rev_mp, erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt{*Fake*}
apply spy_analz
txt{*SpyKeys*}
apply force
apply (simp_all add: insert_absorb) 
txt{*ClientHello, ServerHello, ClientKeyExch: mostly freshness reasoning*}
apply (blast dest: Notes_Crypt_parts_spies)
apply (blast dest: Notes_Crypt_parts_spies)
apply (blast dest: Notes_Crypt_parts_spies)
txt{*ClientAccepts and ServerAccepts: because @{term "PMS \<notin> range PRF"}*}
apply force+
done


text{*If A sends ClientKeyExch to an honest B, then the MASTER SECRET
  will stay secret.*}
lemma Spy_not_see_MS:
     "[| Notes A {|Agent B, Nonce PMS|} \<in> set evs;
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Nonce (PRF(PMS,NA,NB)) \<notin> analz (spies evs)"
apply (erule rev_mp, erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt{*Fake*}
apply spy_analz
txt{*SpyKeys: by secrecy of the PMS, Spy cannot make the MS*}
apply (blast dest!: Spy_not_see_PMS)
apply (simp_all add: insert_absorb)
txt{*ClientAccepts and ServerAccepts: because PMS was already visible;
  others, freshness etc.*}
apply (blast dest: Notes_Crypt_parts_spies Spy_not_see_PMS 
                   Notes_imp_knows_Spy [THEN analz.Inj])+
done



subsubsection{*Weakening the Oops conditions for leakage of clientK*}

text{*If A created PMS then nobody else (except the Spy in replays)
  would send a message using a clientK generated from that PMS.*}
lemma Says_clientK_unique:
     "[| Says A' B' (Crypt (clientK(Na,Nb,PRF(PMS,NA,NB))) Y) \<in> set evs;
         Notes A {|Agent B, Nonce PMS|} \<in> set evs;
         evs \<in> tls;  A' \<noteq> Spy |]
      ==> A = A'"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all)
txt{*ClientKeyExch*}
apply (blast dest!: PMS_Crypt_sessionK_not_spied)
txt{*ClientFinished, ClientResume: by unicity of PMS*}
apply (blast dest!: Notes_master_imp_Notes_PMS 
             intro: Notes_unique_PMS [THEN conjunct1])+
done


text{*If A created PMS and has not leaked her clientK to the Spy,
  then it is completely secure: not even in parts!*}
lemma clientK_not_spied:
     "[| Notes A {|Agent B, Nonce PMS|} \<in> set evs;
         Says A Spy (Key (clientK(Na,Nb,PRF(PMS,NA,NB)))) \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;
         evs \<in> tls |]
      ==> Key (clientK(Na,Nb,PRF(PMS,NA,NB))) \<notin> parts (spies evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt{*ClientKeyExch*}
apply blast 
txt{*SpyKeys*}
apply (blast dest!: Spy_not_see_MS)
txt{*ClientKeyExch*}
apply (blast dest!: PMS_sessionK_not_spied)
txt{*Oops*}
apply (blast intro: Says_clientK_unique)
done


subsubsection{*Weakening the Oops conditions for leakage of serverK*}

text{*If A created PMS for B, then nobody other than B or the Spy would
  send a message using a serverK generated from that PMS.*}
lemma Says_serverK_unique:
     "[| Says B' A' (Crypt (serverK(Na,Nb,PRF(PMS,NA,NB))) Y) \<in> set evs;
         Notes A {|Agent B, Nonce PMS|} \<in> set evs;
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad;  B' \<noteq> Spy |]
      ==> B = B'"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all)
txt{*ClientKeyExch*}
apply (blast dest!: PMS_Crypt_sessionK_not_spied)
txt{*ServerResume, ServerFinished: by unicity of PMS*}
apply (blast dest!: Notes_master_imp_Crypt_PMS 
             dest: Spy_not_see_PMS Notes_Crypt_parts_spies Crypt_unique_PMS)+
done


text{*If A created PMS for B, and B has not leaked his serverK to the Spy,
  then it is completely secure: not even in parts!*}
lemma serverK_not_spied:
     "[| Notes A {|Agent B, Nonce PMS|} \<in> set evs;
         Says B Spy (Key(serverK(Na,Nb,PRF(PMS,NA,NB)))) \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> tls |]
      ==> Key (serverK(Na,Nb,PRF(PMS,NA,NB))) \<notin> parts (spies evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt{*Fake*}
apply blast 
txt{*SpyKeys*}
apply (blast dest!: Spy_not_see_MS)
txt{*ClientKeyExch*}
apply (blast dest!: PMS_sessionK_not_spied)
txt{*Oops*}
apply (blast intro: Says_serverK_unique)
done


subsubsection{*Protocol goals: if A receives ServerFinished, then B is present
     and has used the quoted values PA, PB, etc.  Note that it is up to A
     to compare PA with what she originally sent.*}

text{*The mention of her name (A) in X assures A that B knows who she is.*}
lemma TrustServerFinished [rule_format]:
     "[| X = Crypt (serverK(Na,Nb,M))
               (Hash{|Number SID, Nonce M,
                      Nonce Na, Number PA, Agent A,
                      Nonce Nb, Number PB, Agent B|});
         M = PRF(PMS,NA,NB);
         evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Says B Spy (Key(serverK(Na,Nb,M))) \<notin> set evs -->
          Notes A {|Agent B, Nonce PMS|} \<in> set evs -->
          X \<in> parts (spies evs) --> Says B A X \<in> set evs"
apply (erule ssubst)+
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt{*Fake: the Spy doesn't have the critical session key!*}
apply (blast dest: serverK_not_spied)
txt{*ClientKeyExch*}
apply (blast dest!: PMS_Crypt_sessionK_not_spied)
done

text{*This version refers not to ServerFinished but to any message from B.
  We don't assume B has received CertVerify, and an intruder could
  have changed A's identity in all other messages, so we can't be sure
  that B sends his message to A.  If CLIENT KEY EXCHANGE were augmented
  to bind A's identity with PMS, then we could replace A' by A below.*}
lemma TrustServerMsg [rule_format]:
     "[| M = PRF(PMS,NA,NB);  evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Says B Spy (Key(serverK(Na,Nb,M))) \<notin> set evs -->
          Notes A {|Agent B, Nonce PMS|} \<in> set evs -->
          Crypt (serverK(Na,Nb,M)) Y \<in> parts (spies evs)  -->
          (\<exists>A'. Says B A' (Crypt (serverK(Na,Nb,M)) Y) \<in> set evs)"
apply (erule ssubst)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp) add: ex_disj_distrib)
txt{*Fake: the Spy doesn't have the critical session key!*}
apply (blast dest: serverK_not_spied)
txt{*ClientKeyExch*}
apply (clarify, blast dest!: PMS_Crypt_sessionK_not_spied)
txt{*ServerResume, ServerFinished: by unicity of PMS*}
apply (blast dest!: Notes_master_imp_Crypt_PMS 
             dest: Spy_not_see_PMS Notes_Crypt_parts_spies Crypt_unique_PMS)+
done


subsubsection{*Protocol goal: if B receives any message encrypted with clientK
      then A has sent it*}

text{*ASSUMING that A chose PMS.  Authentication is
     assumed here; B cannot verify it.  But if the message is
     ClientFinished, then B can then check the quoted values PA, PB, etc.*}

lemma TrustClientMsg [rule_format]:
     "[| M = PRF(PMS,NA,NB);  evs \<in> tls;  A \<notin> bad;  B \<notin> bad |]
      ==> Says A Spy (Key(clientK(Na,Nb,M))) \<notin> set evs -->
          Notes A {|Agent B, Nonce PMS|} \<in> set evs -->
          Crypt (clientK(Na,Nb,M)) Y \<in> parts (spies evs) -->
          Says A B (Crypt (clientK(Na,Nb,M)) Y) \<in> set evs"
apply (erule ssubst)
apply (erule tls.induct, frule_tac [7] CX_KB_is_pubKB)
apply (force, simp_all (no_asm_simp))
txt{*Fake: the Spy doesn't have the critical session key!*}
apply (blast dest: clientK_not_spied)
txt{*ClientKeyExch*}
apply (blast dest!: PMS_Crypt_sessionK_not_spied)
txt{*ClientFinished, ClientResume: by unicity of PMS*}
apply (blast dest!: Notes_master_imp_Notes_PMS dest: Notes_unique_PMS)+
done


subsubsection{*Protocol goal: if B receives ClientFinished, and if B is able to
     check a CertVerify from A, then A has used the quoted
     values PA, PB, etc.  Even this one requires A to be uncompromised.*}
lemma AuthClientFinished:
     "[| M = PRF(PMS,NA,NB);
         Says A Spy (Key(clientK(Na,Nb,M))) \<notin> set evs;
         Says A' B (Crypt (clientK(Na,Nb,M)) Y) \<in> set evs;
         certificate A KA \<in> parts (spies evs);
         Says A'' B (Crypt (invKey KA) (Hash{|nb, Agent B, Nonce PMS|}))
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
