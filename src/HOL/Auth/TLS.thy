(*  Title:      HOL/Auth/TLS
    ID:         $Id$
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

TLS = Public + 

constdefs
  certificate      :: "[agent,key] => msg"
    "certificate A KA == Crypt (priK Server) {|Agent A, Key KA|}"

datatype role = ClientRole | ServerRole

consts
  (*Pseudo-random function of Section 5*)
  PRF  :: "nat*nat*nat => nat"

  (*Client, server write keys are generated uniformly by function sessionK
    to avoid duplicating their properties.  They are distinguished by a
    tag (not a bool, to avoid the peculiarities of if-and-only-if).
    Session keys implicitly include MAC secrets.*)
  sessionK :: "(nat*nat*nat) * role => key"

syntax
    clientK, serverK :: "nat*nat*nat => key"

translations
  "clientK X" == "sessionK(X, ClientRole)"
  "serverK X" == "sessionK(X, ServerRole)"

rules
  (*the pseudo-random function is collision-free*)
  inj_PRF       "inj PRF"	

  (*sessionK is collision-free; also, no clientK clashes with any serverK.*)
  inj_sessionK  "inj sessionK"	

  (*sessionK makes symmetric keys*)
  isSym_sessionK "isSymKey (sessionK nonces)"


consts    tls :: event list set
inductive tls
  intrs 
    Nil  (*Initial trace is empty*)
         "[]: tls"

    Fake (*The spy, an active attacker, MAY say anything he CAN say.*)
         "[| evs: tls;  X: synth (analz (spies evs)) |]
          ==> Says Spy B X # evs : tls"

    SpyKeys (*The spy may apply PRF & sessionK to available nonces*)
         "[| evsSK: tls;
	     {Nonce NA, Nonce NB, Nonce M} <= analz (spies evsSK) |]
          ==> Notes Spy {| Nonce (PRF(M,NA,NB)),
			   Key (sessionK((NA,NB,M),role)) |} # evsSK : tls"

    ClientHello
	 (*(7.4.1.2)
	   PA represents CLIENT_VERSION, CIPHER_SUITES and COMPRESSION_METHODS.
	   It is uninterpreted but will be confirmed in the FINISHED messages.
	   NA is CLIENT RANDOM, while SID is SESSION_ID.
           UNIX TIME is omitted because the protocol doesn't use it.
           May assume NA ~: range PRF because CLIENT RANDOM is 28 bytes
	   while MASTER SECRET is 48 bytes*)
         "[| evsCH: tls;  Nonce NA ~: used evsCH;  NA ~: range PRF |]
          ==> Says A B {|Agent A, Nonce NA, Number SID, Number PA|}
	        # evsCH  :  tls"

    ServerHello
         (*7.4.1.3 of the TLS Internet-Draft
	   PB represents CLIENT_VERSION, CIPHER_SUITE and COMPRESSION_METHOD.
           SERVER CERTIFICATE (7.4.2) is always present.
           CERTIFICATE_REQUEST (7.4.4) is implied.*)
         "[| evsSH: tls;  Nonce NB ~: used evsSH;  NB ~: range PRF;
             Says A' B {|Agent A, Nonce NA, Number SID, Number PA|}
	       : set evsSH |]
          ==> Says B A {|Nonce NB, Number SID, Number PB|} # evsSH  :  tls"

    Certificate
         (*SERVER (7.4.2) or CLIENT (7.4.6) CERTIFICATE.*)
         "evsC: tls ==> Says B A (certificate B (pubK B)) # evsC  :  tls"

    ClientKeyExch
         (*CLIENT KEY EXCHANGE (7.4.7).
           The client, A, chooses PMS, the PREMASTER SECRET.
           She encrypts PMS using the supplied KB, which ought to be pubK B.
           We assume PMS ~: range PRF because a clash betweem the PMS
           and another MASTER SECRET is highly unlikely (even though
	   both items have the same length, 48 bytes).
           The Note event records in the trace that she knows PMS
               (see REMARK at top). *)
         "[| evsCX: tls;  Nonce PMS ~: used evsCX;  PMS ~: range PRF;
             Says B' A (certificate B KB) : set evsCX |]
          ==> Says A B (Crypt KB (Nonce PMS))
	      # Notes A {|Agent B, Nonce PMS|}
	      # evsCX  :  tls"

    CertVerify
	(*The optional Certificate Verify (7.4.8) message contains the
          specific components listed in the security analysis, F.1.1.2.
          It adds the pre-master-secret, which is also essential!
          Checking the signature, which is the only use of A's certificate,
          assures B of A's presence*)
         "[| evsCV: tls;  
             Says B' A {|Nonce NB, Number SID, Number PB|} : set evsCV;
	     Notes A {|Agent B, Nonce PMS|} : set evsCV |]
          ==> Says A B (Crypt (priK A) (Hash{|Nonce NB, Agent B, Nonce PMS|}))
              # evsCV  :  tls"

	(*Finally come the FINISHED messages (7.4.8), confirming PA and PB
          among other things.  The master-secret is PRF(PMS,NA,NB).
          Either party may sent its message first.*)

    ClientFinished
        (*The occurrence of Notes A {|Agent B, Nonce PMS|} stops the 
          rule's applying when the Spy has satisfied the "Says A B" by
          repaying messages sent by the true client; in that case, the
          Spy does not know PMS and could not send ClientFinished.  One
          could simply put A~=Spy into the rule, but one should not
          expect the spy to be well-behaved.*)
         "[| evsCF: tls;  
	     Says A  B {|Agent A, Nonce NA, Number SID, Number PA|}
	       : set evsCF;
             Says B' A {|Nonce NB, Number SID, Number PB|} : set evsCF;
             Notes A {|Agent B, Nonce PMS|} : set evsCF;
	     M = PRF(PMS,NA,NB) |]
          ==> Says A B (Crypt (clientK(NA,NB,M))
			(Hash{|Number SID, Nonce M,
			       Nonce NA, Number PA, Agent A, 
			       Nonce NB, Number PB, Agent B|}))
              # evsCF  :  tls"

    ServerFinished
	(*Keeping A' and A'' distinct means B cannot even check that the
          two messages originate from the same source. *)
         "[| evsSF: tls;
	     Says A' B  {|Agent A, Nonce NA, Number SID, Number PA|}
	       : set evsSF;
	     Says B  A  {|Nonce NB, Number SID, Number PB|} : set evsSF;
	     Says A'' B (Crypt (pubK B) (Nonce PMS)) : set evsSF;
	     M = PRF(PMS,NA,NB) |]
          ==> Says B A (Crypt (serverK(NA,NB,M))
			(Hash{|Number SID, Nonce M,
			       Nonce NA, Number PA, Agent A, 
			       Nonce NB, Number PB, Agent B|}))
              # evsSF  :  tls"

    ClientAccepts
	(*Having transmitted ClientFinished and received an identical
          message encrypted with serverK, the client stores the parameters
          needed to resume this session.  The "Notes A ..." premise is
          used to prove Notes_master_imp_Crypt_PMS.*)
         "[| evsCA: tls;
	     Notes A {|Agent B, Nonce PMS|} : set evsCA;
	     M = PRF(PMS,NA,NB);  
	     X = Hash{|Number SID, Nonce M,
	               Nonce NA, Number PA, Agent A, 
		       Nonce NB, Number PB, Agent B|};
             Says A  B (Crypt (clientK(NA,NB,M)) X) : set evsCA;
             Says B' A (Crypt (serverK(NA,NB,M)) X) : set evsCA |]
          ==> 
             Notes A {|Number SID, Agent A, Agent B, Nonce M|} # evsCA  :  tls"

    ServerAccepts
	(*Having transmitted ServerFinished and received an identical
          message encrypted with clientK, the server stores the parameters
          needed to resume this session.  The "Says A'' B ..." premise is
          used to prove Notes_master_imp_Crypt_PMS.*)
         "[| evsSA: tls;
	     A ~= B;
             Says A'' B (Crypt (pubK B) (Nonce PMS)) : set evsSA;
	     M = PRF(PMS,NA,NB);  
	     X = Hash{|Number SID, Nonce M,
	               Nonce NA, Number PA, Agent A, 
		       Nonce NB, Number PB, Agent B|};
             Says B  A (Crypt (serverK(NA,NB,M)) X) : set evsSA;
             Says A' B (Crypt (clientK(NA,NB,M)) X) : set evsSA |]
          ==> 
             Notes B {|Number SID, Agent A, Agent B, Nonce M|} # evsSA  :  tls"

    ClientResume
         (*If A recalls the SESSION_ID, then she sends a FINISHED message
           using the new nonces and stored MASTER SECRET.*)
         "[| evsCR: tls;  
	     Says A  B {|Agent A, Nonce NA, Number SID, Number PA|}: set evsCR;
             Says B' A {|Nonce NB, Number SID, Number PB|} : set evsCR;
             Notes A {|Number SID, Agent A, Agent B, Nonce M|} : set evsCR |]
          ==> Says A B (Crypt (clientK(NA,NB,M))
			(Hash{|Number SID, Nonce M,
			       Nonce NA, Number PA, Agent A, 
			       Nonce NB, Number PB, Agent B|}))
              # evsCR  :  tls"

    ServerResume
         (*Resumption (7.3):  If B finds the SESSION_ID then he can send
           a FINISHED message using the recovered MASTER SECRET*)
         "[| evsSR: tls;
	     Says A' B {|Agent A, Nonce NA, Number SID, Number PA|}: set evsSR;
	     Says B  A {|Nonce NB, Number SID, Number PB|} : set evsSR;  
             Notes B {|Number SID, Agent A, Agent B, Nonce M|} : set evsSR |]
          ==> Says B A (Crypt (serverK(NA,NB,M))
			(Hash{|Number SID, Nonce M,
			       Nonce NA, Number PA, Agent A, 
			       Nonce NB, Number PB, Agent B|})) # evsSR
	        :  tls"

    Oops 
         (*The most plausible compromise is of an old session key.  Losing
           the MASTER SECRET or PREMASTER SECRET is more serious but
           rather unlikely.  The assumption A ~= Spy is essential: otherwise
           the Spy could learn session keys merely by replaying messages!*)
         "[| evso: tls;  A ~= Spy;
	     Says A B (Crypt (sessionK((NA,NB,M),role)) X) : set evso |]
          ==> Says A Spy (Key (sessionK((NA,NB,M),role))) # evso  :  tls"

end
