(*  Title:      HOL/Auth/TLS
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Inductive relation "tls" for the baby TLS (Transport Layer Security) protocol.

An RSA cryptosystem is assumed, and X.509v3 certificates are abstracted down
to the trivial form {A, publicKey(A)}privateKey(Server), where Server is a
global signing authority.

A is the client and B is the server, not to be confused with the constant
Server, who is in charge of all public keys.

The model assumes that no fraudulent certificates are present, but it does
assume that some private keys are lost to the spy.

Abstracted from "The TLS Protocol, Version 1.0" by Tim Dierks and Christopher
Allen, Transport Layer Security Working Group, 21 May 1997,
INTERNET-DRAFT draft-ietf-tls-protocol-03.txt

NOTE.  The event "Notes A {|Agent B, Nonce M|}" appears in ClientCertKeyEx,
CertVerify, ClientFinished to record that A knows M.  It is a note from A to
herself.  Nobody else can see it.  In ClientCertKeyEx, the Spy can substitute
his own certificate for A's, but he cannot replace A's note by one for himself.

The note is needed because of a weakness in the public-key model.  Each
agent's state is recorded as the trace of messages.  When the true client (A)
invents M, he encrypts M with B's public key before sending it.  The model
does not distinguish the original occurrence of such a message from a replay.

In the shared-key model, the ability to encrypt implies the ability to
decrypt, so the problem does not arise.
*)

TLS = Public + 

consts
  (*Client, server write keys.  They implicitly include the MAC secrets.*)
  clientK, serverK :: "nat*nat*nat => key"
  certificate      :: "[agent,key] => msg"

defs
  certificate_def
    "certificate A KA == Crypt (priK Server) {|Agent A, Key KA|}"

rules
  (*clientK is collision-free and makes symmetric keys*)
  inj_clientK   "inj clientK"	
  isSym_clientK "isSymKey (clientK x)"	(*client write keys are symmetric*)

  (*serverK is similar*)
  inj_serverK   "inj serverK"	
  isSym_serverK "isSymKey (serverK x)"	(*server write keys are symmetric*)

  (*Clashes with pubK and priK are impossible, but this axiom is needed.*)
  clientK_range "range clientK <= Compl (range serverK)"

  (*Spy has access to his own key for spoof messages, but Server is secure*)
  Spy_in_lost     "Spy: lost"
  Server_not_lost "Server ~: lost"


consts  lost :: agent set        (*No need for it to be a variable*)
	tls  :: event list set

inductive tls
  intrs 
    Nil  (*Initial trace is empty*)
         "[]: tls"

    Fake (*The spy, an active attacker, MAY say anything he CAN say.*)
         "[| evs: tls;  B ~= Spy;  
             X: synth (analz (sees lost Spy evs)) |]
          ==> Says Spy B X # evs : tls"

    SpyKeys (*The spy may apply clientK & serverK to nonces he's found*)
         "[| evs: tls;
	     Says Spy B {|Nonce NA, Nonce NB, Nonce M|} : set evs |]
          ==> Says Spy B {| Key (clientK(NA,NB,M)),
			    Key (serverK(NA,NB,M)) |} # evs : tls"

    ClientHello
	 (*XA represents CLIENT_VERSION, CIPHER_SUITES and COMPRESSION_METHODS.
	   It is uninterpreted but will be confirmed in the FINISHED messages.
	   As an initial simplification, SESSION_ID is identified with NA
           and reuse of sessions is not supported.*)
         "[| evs: tls;  A ~= B;  Nonce NA ~: used evs |]
          ==> Says A B {|Agent A, Nonce NA, Agent XA|} # evs  :  tls"

    ServerHello
         (*XB represents CLIENT_VERSION, CIPHER_SUITE and COMPRESSION_METHOD.
	   NA is returned in its role as SESSION_ID.  A CERTIFICATE_REQUEST is
	   implied and a SERVER CERTIFICATE is always present.*)
         "[| evs: tls;  A ~= B;  Nonce NB ~: used evs;
             Says A' B {|Agent A, Nonce NA, Agent XA|} : set evs |]
          ==> Says B A {|Nonce NA, Nonce NB, Agent XB,
			 certificate B (pubK B)|}
                # evs  :  tls"

    ClientCertKeyEx
         (*CLIENT CERTIFICATE and KEY EXCHANGE.  The client, A, chooses M,
           the pre-master-secret.  She encrypts M using the supplied KB,
           which ought to be pubK B, and also with her own public key,
           to record in the trace that she knows M (see NOTE at top).*)
         "[| evs: tls;  A ~= B;  Nonce M ~: used evs;
             Says B' A {|Nonce NA, Nonce NB, Agent XB, certificate B KB|}
	       : set evs |]
          ==> Says A B {|certificate A (pubK A), Crypt KB (Nonce M)|}
	      # Notes A {|Agent B, Nonce M|}
	      # evs  :  tls"

    CertVerify
	(*The optional CERTIFICATE VERIFY message contains the specific
          components listed in the security analysis, Appendix F.1.1.2;
          it also contains the pre-master-secret.  Checking the signature,
          which is the only use of A's certificate, assures B of A's presence*)
         "[| evs: tls;  A ~= B;  
             Says B' A {|Nonce NA, Nonce NB, Agent XB, certificate B KB|}
	       : set evs;
	     Notes A {|Agent B, Nonce M|} : set evs |]
          ==> Says A B (Crypt (priK A)
			(Hash{|Nonce NB, certificate B KB, Nonce M|}))
                # evs  :  tls"

	(*Finally come the FINISHED messages, confirming XA and XB among
          other things.  The master-secret is the hash of NA, NB and M.
          Either party may sent its message first.*)

        (*The occurrence of Crypt (pubK A) {|Agent B, Nonce M|} stops the 
          rule's applying when the Spy has satisfied the "Says A B" by
          repaying messages sent by the true client; in that case, the
          Spy does not know M and could not sent CLIENT FINISHED.  One
          could simply put A~=Spy into the rule, but one should not
          expect the spy to be well-behaved.*)
    ClientFinished
         "[| evs: tls;  A ~= B;
	     Says A  B {|Agent A, Nonce NA, Agent XA|} : set evs;
             Says B' A {|Nonce NA, Nonce NB, Agent XB, certificate B KB|}
	       : set evs;
             Notes A {|Agent B, Nonce M|} : set evs |]
          ==> Says A B (Crypt (clientK(NA,NB,M))
			(Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},
			       Nonce NA, Agent XA,
			       certificate A (pubK A), 
			       Nonce NB, Agent XB, Agent B|}))
                # evs  :  tls"

	(*Keeping A' and A'' distinct means B cannot even check that the
          two messages originate from the same source.  B does not attempt
          to read A's encrypted "note to herself".*)
    ServerFinished
         "[| evs: tls;  A ~= B;
	     Says A' B  {|Agent A, Nonce NA, Agent XA|} : set evs;
	     Says B  A  {|Nonce NA, Nonce NB, Agent XB,
		 	  certificate B (pubK B)|}
	       : set evs;
	     Says A'' B {|certificate A KA, Crypt (pubK B) (Nonce M)|}
	       : set evs |]
          ==> Says B A (Crypt (serverK(NA,NB,M))
			(Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},
			       Nonce NA, Agent XA, Agent A, 
			       Nonce NB, Agent XB,
			       certificate B (pubK B)|}))
                # evs  :  tls"

  (**Oops message??**)

end
