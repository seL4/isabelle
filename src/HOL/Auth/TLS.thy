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

The model assumes that no fraudulent certificates are present.

Protocol goals: 
* M, serverK(NA,NB,M) and clientK(NA,NB,M) will be known only to the two
     parties (though A is not necessarily authenticated).

* B upon receiving CERTIFICATE VERIFY knows that A is present (But this
    message is optional!)

* A upon receiving SERVER FINISHED knows that B is present

* Each party who has received a FINISHED message can trust that the other
  party agrees on all message components, including XA and XB (thus foiling
  rollback attacks).
*)

TLS = Public + 

consts
  (*Client, server write keys.  They implicitly include the MAC secrets.*)
  clientK, serverK :: "nat*nat*nat => key"

rules
  (*clientK is collision-free and makes symmetric keys*)
  inj_clientK   "inj clientK"	
  isSym_clientK "isSymKey (clientK x)"	(*client write keys are symmetric*)

  inj_serverK   "inj serverK"	
  isSym_serverK "isSymKey (serverK x)"	(*server write keys are symmetric*)

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
          ==> Says Spy B X  # evs : tls"

    ClientHello
	 (*XA represents CLIENT_VERSION, CIPHER_SUITES and COMPRESSION_METHODS.
	   It is uninterpreted but will be confirmed in the FINISHED messages.
	   As an initial simplification, SESSION_ID is identified with NA
           and reuse of sessions is not supported.*)
         "[| evs: tls;  A ~= B;  Nonce NA ~: used evs |]
          ==> Says A B {|Agent A, Nonce NA, Agent XA|} # evs  :  tls"

    ServerHello
         (*XB represents CLIENT_VERSION, CIPHER_SUITE and COMPRESSION_METHOD.
	   Na is returned in its role as SESSION_ID.  A CERTIFICATE_REQUEST is
	   implied and a SERVER CERTIFICATE is always present.*)
         "[| evs: tls;  A ~= B;  Nonce NB ~: used evs;
             Says A' B {|Agent A, Nonce NA, Agent XA|} : set evs |]
          ==> Says B A {|Nonce NA, Nonce NB, Agent XB,
			 Crypt (priK Server) {|Agent B, Key (pubK B)|}|}
                # evs  :  tls"

    ClientCertKeyEx
         (*CLIENT CERTIFICATE and KEY EXCHANGE.  M is the pre-master-secret.
           Note that A encrypts using the supplied KB, not pubK B.*)
         "[| evs: tls;  A ~= B;  Nonce M ~: used evs;
             Says B' A {|Nonce NA, Nonce NB, Agent XB,
			 Crypt (priK Server) {|Agent B, Key KB|}|} : set evs |]
          ==> Says A B {|Crypt (priK Server) {|Agent A, Key (pubK A)|},
			 Crypt KB (Nonce M)|}
                # evs  :  tls"

    CertVerify
	(*The optional CERTIFICATE VERIFY message contains the specific
          components listed in the security analysis, Appendix F.1.1.2.
          By checking the signature, B is assured of A's existence:
          the only use of A's certificate.*)
         "[| evs: tls;  A ~= B;  
             Says B' A {|Nonce NA, Nonce NB, Agent XB,
			 Crypt (priK Server) {|Agent B, Key KB|}|} : set evs |]
          ==> Says A B (Crypt (priK A)
			(Hash{|Nonce NB,
	 		       Crypt (priK Server) {|Agent B, Key KB|}|}))
                # evs  :  tls"

	(*Finally come the FINISHED messages, confirming XA and XB among
          other things.  The master-secret is the hash of NA, NB and M.
          Either party may sent its message first.*)

    ClientFinished
         "[| evs: tls;  A ~= B;
	     Says A  B {|Agent A, Nonce NA, Agent XA|} : set evs;
             Says B' A {|Nonce NA, Nonce NB, Agent XB, 
			 Crypt (priK Server) {|Agent B, Key KB|}|} : set evs;
             Says A  B {|Crypt (priK Server) {|Agent A, Key (pubK A)|},
		         Crypt KB (Nonce M)|} : set evs |]
          ==> Says A B (Crypt (clientK(NA,NB,M))
			(Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},
			       Nonce NA, Agent XA,
			       Crypt (priK Server) {|Agent A, Key(pubK A)|}, 
			       Nonce NB, Agent XB, Agent B|}))
                # evs  :  tls"

	(*Keeping A' and A'' distinct means B cannot even check that the
          two messages originate from the same source.*)

    ServerFinished
         "[| evs: tls;  A ~= B;
	     Says A' B  {|Agent A, Nonce NA, Agent XA|} : set evs;
	     Says B  A  {|Nonce NA, Nonce NB, Agent XB,
		 	  Crypt (priK Server) {|Agent B, Key (pubK B)|}|}
	       : set evs;
	     Says A'' B {|CERTA, Crypt (pubK B) (Nonce M)|} : set evs |]
          ==> Says B A (Crypt (serverK(NA,NB,M))
			(Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},
			       Nonce NA, Agent XA, Agent A, 
			       Nonce NB, Agent XB,
			       Crypt (priK Server) {|Agent B, Key(pubK B)|}|}))
                # evs  :  tls"

  (**Oops message??**)

end
