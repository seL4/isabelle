(*  Title:      HOL/Auth/TLS
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

The public-key model has a weakness, especially concerning anonymous sessions.
The Spy's state is recorded as the trace of message.  But if he himself is 
the Client and invents M, then the event he sends contains M encrypted with B's
public key.  From the trace there is no reason to believe that the spy knows
M, and yet the spy actually chose M!  So, in any property concerning the 
secrecy of some item, one must somehow establish that the spy didn't choose
the item.  In practice, this weakness does little harm, since one can expect
few guarantees when communicating directly with an enemy.

The model, at present, doesn't recognize that if the Spy has NA, NB and M then
he also has clientK(NA,NB,M) and serverK(NA,NB,M).  Maybe this doesn't really
matter, since one can prove that he doesn't get M.
*)

open TLS;

proof_timing:=true;
HOL_quantifiers := false;

AddIffs [Spy_in_lost, Server_not_lost];

(*Injectiveness of key-generating functions*)
AddIffs [inj_clientK RS inj_eq, inj_serverK RS inj_eq];

(* invKey(clientK x) = clientK x  and similarly for serverK*)
Addsimps [isSym_clientK, rewrite_rule [isSymKey_def] isSym_clientK,
	  isSym_serverK, rewrite_rule [isSymKey_def] isSym_serverK];
	  

(*Replacing the variable by a constant improves search speed by 50%!*)
val Says_imp_sees_Spy' = 
    read_instantiate_sg (sign_of thy) [("lost","lost")] Says_imp_sees_Spy;


(*** clientK and serverK make symmetric keys; no clashes with pubK or priK ***)

goal thy "pubK A ~= clientK arg";
br notI 1;
by (dres_inst_tac [("f","isSymKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "pubK_neq_clientK";

goal thy "pubK A ~= serverK arg";
br notI 1;
by (dres_inst_tac [("f","isSymKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "pubK_neq_serverK";

goal thy "priK A ~= clientK arg";
br notI 1;
by (dres_inst_tac [("f","isSymKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "priK_neq_clientK";

goal thy "priK A ~= serverK arg";
br notI 1;
by (dres_inst_tac [("f","isSymKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "priK_neq_serverK";

val ths = [pubK_neq_clientK, pubK_neq_serverK, 
	   priK_neq_clientK, priK_neq_serverK];
AddIffs (ths @ (ths RL [not_sym]));


(**** Protocol Proofs ****)

(*A "possibility property": there are traces that reach the end.
  This protocol has three end points and six messages to consider.*)

(*Possibility property ending with ServerFinished.*)
goal thy 
 "!!A B. A ~= B ==> EX NA XA NB XB M. EX evs: tls.    \
\  Says B A (Crypt (serverK(NA,NB,M))                 \
\            (Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|}, \
\                   Nonce NA, Agent XA, Agent A,      \
\                   Nonce NB, Agent XB,               \
\                   Crypt (priK Server) {|Agent B, Key (pubK B)|}|})) \
\    : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.ClientCertKeyEx
	  RS tls.ServerFinished) 2);
by possibility_tac;
result();

(*And one for ClientFinished.  Either FINISHED message may come first.*)
goal thy 
 "!!A B. A ~= B ==> EX NA XA NB XB M. EX evs: tls.    \
\  Says A B (Crypt (clientK(NA,NB,M))                 \
\            (Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|}, \
\                   Nonce NA, Agent XA,               \
\                   Crypt (priK Server) {|Agent A, Key (pubK A)|},      \
\                   Nonce NB, Agent XB, Agent B|})) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.ClientCertKeyEx
	  RS tls.ClientFinished) 2);
by possibility_tac;
result();

(*Another one, for CertVerify (which is optional)*)
goal thy 
 "!!A B. A ~= B ==> EX NB. EX evs: tls.     \
\  Says A B (Crypt (priK A)                 \
\            (Hash{|Nonce NB,               \
\                   Crypt (priK Server)     \
\                         {|Agent B, Key (pubK B)|}|})) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.CertVerify) 2);
by possibility_tac;
result();


(**** Inductive proofs about tls ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : tls ==> ALL A X. Says A A X ~: set evs";
by (etac tls.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : tls \
\        ==> (Key (priK A) : parts (sees lost Spy evs)) = (A : lost)";
by (etac tls.induct 1);
by (prove_simple_subgoals_tac 1);
by (Fake_parts_insert_tac 1);
qed "Spy_see_priK";
Addsimps [Spy_see_priK];

goal thy 
 "!!evs. evs : tls \
\        ==> (Key (priK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_priK";
Addsimps [Spy_analz_priK];

goal thy  "!!A. [| Key (priK A) : parts (sees lost Spy evs);       \
\                  evs : tls |] ==> A:lost";
by (blast_tac (!claset addDs [Spy_see_priK]) 1);
qed "Spy_see_priK_D";

bind_thm ("Spy_analz_priK_D", analz_subset_parts RS subsetD RS Spy_see_priK_D);
AddSDs [Spy_see_priK_D, Spy_analz_priK_D];


(*Every Nonce that's hashed is already in past traffic. *)
goal thy "!!evs. [| Hash {|Nonce N, X|} : parts (sees lost Spy evs);  \
\                   evs : tls |]  \
\                ==> Nonce N : parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac tls.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert_sees])));
by (step_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
		      addSEs partsEs) 1);
by (Fake_parts_insert_tac 1);
qed "Hash_imp_Nonce1";

(*Lemma needed to prove Hash_Hash_imp_Nonce*)
goal thy "!!evs. [| Hash{|Nonce NA, Nonce NB, Nonce M|}  \
\                       : parts (sees lost Spy evs);     \
\                   evs : tls |]  \
\                ==> Nonce M : parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac tls.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert_sees])));
by (step_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
		      addSEs partsEs) 1);
by (Fake_parts_insert_tac 1);
qed "Hash_imp_Nonce2";
AddSDs [Hash_imp_Nonce2];

goal thy "!!evs. [| Hash {| Hash{|Nonce NA, Nonce NB, Nonce M|}, X |}  \
\                      : parts (sees lost Spy evs);      \
\                   evs : tls |]                         \
\                ==> Nonce M : parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac tls.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert_sees])));
by (step_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
		      addSEs partsEs) 1);
by (Fake_parts_insert_tac 1);
qed "Hash_Hash_imp_Nonce";


(*NEEDED??
  Every Nonce that's hashed is already in past traffic. 
  This general formulation is tricky to prove and hard to use, since the
  2nd premise is typically proved by simplification.*)
goal thy "!!evs. [| Hash X : parts (sees lost Spy evs);  \
\                   Nonce N : parts {X};  evs : tls |]  \
\                ==> Nonce N : parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac tls.induct 1);
by (ALLGOALS Asm_simp_tac);
by (step_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
		      addSEs partsEs) 1);
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps [parts_insert_sees])));
(*ServerFinished*)
by (Blast_tac 3);
(*ClientFinished*)
by (Blast_tac 2);
by (Fake_parts_insert_tac 1);
qed "Hash_imp_Nonce_seen";


(*** Protocol goal: if B receives CERTIFICATE VERIFY, then A sent it ***)

(*Perhaps B~=Spy is unnecessary, but there's no obvious proof if the first
  message is Fake.  We don't need guarantees for the Spy anyway.*)
goal thy 
 "!!evs. [| X = Crypt (priK A)                          \
\                 (Hash{|Nonce NB,                                      \
\                        Crypt (priK Server) {|Agent B, Key KB|}|});    \
\           evs : tls;  A ~: lost;  B ~= Spy |]         \
\    ==> Says B A {|Nonce NA, Nonce NB, Agent XB,       \
\                   Crypt (priK Server) {|Agent B, Key KB|}|} : set evs --> \
\        X : parts (sees lost Spy evs) --> Says A B X : set evs";
by (Asm_simp_tac 1);
by (etac tls.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Fake_parts_insert_tac 1);
(*ServerHello*)
by (blast_tac (!claset addSDs [Hash_imp_Nonce1]
	               addSEs sees_Spy_partsEs) 1);
qed_spec_mp "TrustCertVerify";


(*This lemma says that no false certificates exist.  One might extend the
  model to include bogus certificates for the lost agents, but there seems
  little point in doing so: the loss of their private keys is a worse
  breach of security.*)
goal thy 
 "!!evs. evs : tls     \
\    ==> Crypt (priK Server) {|Agent B, Key KB|} : parts (sees lost Spy evs) \
\        --> KB = pubK B";
by (etac tls.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Fake_parts_insert_tac 2);
by (Blast_tac 1);
bind_thm ("Server_cert_pubB", result() RSN (2, rev_mp));


(*Replace key KB in ClientCertKeyEx by (pubK B) *)
val ClientCertKeyEx_tac = 
    forward_tac [Says_imp_sees_Spy' RS parts.Inj RS 
		 parts.Snd RS parts.Snd RS parts.Snd RS Server_cert_pubB]
    THEN' assume_tac
    THEN' hyp_subst_tac;

fun analz_induct_tac i = 
    etac tls.induct i   THEN
    ClientCertKeyEx_tac  (i+4)  THEN
    ALLGOALS (asm_simp_tac 
              (!simpset addsimps [not_parts_not_analz]
                        setloop split_tac [expand_if]))  THEN
    (*Remove instances of pubK B:  the Spy already knows all public keys.
      Combining the two simplifier calls makes them run extremely slowly.*)
    ALLGOALS (asm_simp_tac 
              (!simpset addsimps [insert_absorb]
                        setloop split_tac [expand_if]));

(*If A sends ClientCertKeyEx to an honest agent B, then M will stay secret.*)
goal thy 
 "!!evs. [| evs : tls;  A ~: lost;  B ~: lost |] ==> \
\    Says A B {|Crypt (priK Server) {|Agent A, Key (pubK A)|}, \
\               Crypt KB (Nonce M)|} : set evs -->  \
\    Nonce M ~: analz (sees lost Spy evs)";
by (analz_induct_tac 1);
(*ClientHello*)
by (blast_tac (!claset addSEs sees_Spy_partsEs) 2);
(*Fake*)
by (spy_analz_tac 1);
(*ServerHello and ClientCertKeyEx: mostly freshness reasoning*)
by (REPEAT (blast_tac (!claset addSEs partsEs
			       addDs  [impOfSubs analz_subset_parts,
				       Says_imp_sees_Spy' RS analz.Inj]) 1));
bind_thm ("Spy_not_see_premaster_secret", result() RSN (2, rev_mp));


(*** Protocol goal: serverK(NA,NB,M) and clientK(NA,NB,M) remain secure ***)

(*In fact, nothing of the form clientK(NA,NB,M) or serverK(NA,NB,M) is ever
  sent!  These two theorems are too strong: the Spy is quite capable of
  forming many items of the form serverK(NA,NB,M).
  Additional Fake rules could model this capability.*)

goal thy 
 "!!evs. evs : tls ==> Key (clientK(NA,NB,M)) ~: parts (sees lost Spy evs)";
by (etac tls.induct 1);
by (prove_simple_subgoals_tac 1);
by (Fake_parts_insert_tac 1);
qed "clientK_notin_parts";

goal thy 
 "!!evs. evs : tls ==> Key (serverK(NA,NB,M)) ~: parts (sees lost Spy evs)";
by (etac tls.induct 1);
by (prove_simple_subgoals_tac 1);
by (Fake_parts_insert_tac 1);
qed "serverK_notin_parts";

(*We need a version of AddIffs that takes CONDITIONAL equivalences*)
val ths = [clientK_notin_parts, clientK_notin_parts RS not_parts_not_analz,
	   serverK_notin_parts, serverK_notin_parts RS not_parts_not_analz];
Addsimps ths;
AddSEs (ths RLN (2, [rev_notE]));


(*** Protocol goals: if A receives SERVER FINISHED, then B is present 
     and has used the quoted values XA, XB, etc.  Note that it is up to A
     to compare XA with what she originally sent.
***)

(*Perhaps A~=Spy is unnecessary, but there's no obvious proof if the first
  message is Fake.  We don't need guarantees for the Spy anyway.*)
goal thy 
 "!!evs. [| X = Crypt (serverK(NA,NB,M))                        \
\                 (Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},   \
\                        Nonce NA, Agent XA, Agent A,           \
\                        Nonce NB, Agent XB,                    \
\                        Crypt (priK Server) {|Agent B, Key (pubK B)|}|}); \
\           evs : tls;  A~=Spy;  B ~: lost |] ==>               \
\    Says A B {|Crypt (priK Server) {|Agent A, Key (pubK A)|},  \
\               Crypt KB (Nonce M)|} : set evs -->              \
\    X : parts (sees lost Spy evs) --> Says B A X : set evs";
by (Asm_simp_tac 1);
by (etac tls.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Fake_parts_insert_tac 1);
(*ClientCertKeyEx*)
by (blast_tac (!claset addSDs [Hash_Hash_imp_Nonce]
                       addSEs sees_Spy_partsEs) 1);
qed_spec_mp "TrustServerFinished";


(*** Protocol goal: if B receives CLIENT FINISHED, then A  is present ??
     and has used the quoted values XA, XB, etc.  Note that it is up to B
     to compare XB with what he originally sent. ***)

(*This result seems far too strong--it may be provable because the current
  model gives the Spy access to NO keys of the form clientK(NA,NB,M).*)
goal thy 
 "!!evs. [| X = Crypt (clientK(NA,NB,M))                        \
\                 (Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},   \
\                        Nonce NA, Agent XA,                    \
\                        Crypt (priK Server) {|Agent A, Key (pubK A)|}, \
\                        Nonce NB, Agent XB, Agent B|});        \
\           evs : tls |] ==>               \
\    X : parts (sees lost Spy evs) --> Says A B X : set evs";
by (Asm_simp_tac 1);
by (etac tls.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
by (Fake_parts_insert_tac 1);
qed_spec_mp "TrustClientFinished";



