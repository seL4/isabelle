(*  Title:      HOL/Auth/TLS
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

The public-key model has a weakness, especially concerning anonymous sessions.
The Spy's state is recorded as the trace of message.  But if he himself is the
Client and invents M, then he encrypts M with B's public key before sending
it.  This message gives no evidence that the spy knows M, and yet the spy
actually chose M!  So, in any property concerning the secrecy of some item,
one must establish that the spy didn't choose the item.  Guarantees normally
assume that the other party is uncompromised (otherwise, one can prove
little).

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

open TLS;

proof_timing:=true;
HOL_quantifiers := false;

AddIffs [Spy_in_lost, Server_not_lost];
Addsimps [certificate_def];

goal thy "!!A. A ~: lost ==> A ~= Spy";
by (Blast_tac 1);
qed "not_lost_not_eq_Spy";
Addsimps [not_lost_not_eq_Spy];

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

(*clientK and serverK have disjoint ranges*)
goal thy "clientK arg ~= serverK arg'";
by (cut_facts_tac [rangeI RS impOfSubs clientK_range] 1);
by (Blast_tac 1);
qed "clientK_neq_serverK";

val ths = [pubK_neq_clientK, pubK_neq_serverK, 
	   priK_neq_clientK, priK_neq_serverK, clientK_neq_serverK];
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
\                   certificate B (pubK B)|})) \
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
\                   certificate A (pubK A),      \
\                   Nonce NB, Agent XB, Agent B|})) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.ClientCertKeyEx
	  RS tls.ClientFinished) 2);
by possibility_tac;
result();

(*Another one, for CertVerify (which is optional)*)
goal thy 
 "!!A B. A ~= B ==> EX NB M. EX evs: tls.     \
\  Says A B (Crypt (priK A)                 \
\            (Hash{|Nonce NB, certificate B (pubK B), Nonce M|})) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.ClientCertKeyEx
	  RS tls.CertVerify) 2);
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
by (Fake_parts_insert_tac 1);
(*CertVerify, ClientFinished, ServerFinished (?)*)
by (REPEAT (Blast_tac 1));
qed "Hash_imp_Nonce_seen";


(*** Protocol goal: if B receives CERTIFICATE VERIFY, then A sent it ***)

(*B can check A's signature if he has received A's certificate.
  Perhaps B~=Spy is unnecessary, but there's no obvious proof if the first
  message is Fake.  We don't need guarantees for the Spy anyway.  We must
  assume A~:lost; otherwise, the Spy can forge A's signature.*)
goalw thy [certificate_def]
 "!!evs. [| X = Crypt (priK A)                                        \
\                 (Hash{|Nonce NB, certificate B KB, Nonce M|});      \
\           evs : tls;  A ~: lost;  B ~= Spy |]                       \
\    ==> Says B A {|Nonce NA, Nonce NB, Agent XB, certificate B KB|}  \
\          : set evs --> \
\        X : parts (sees lost Spy evs) --> Says A B X : set evs";
by (hyp_subst_tac 1);
by (etac tls.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Fake_parts_insert_tac 1);
(*ServerHello: nonce NB cannot be in X because it's fresh!*)
by (blast_tac (!claset addSDs [Hash_imp_Nonce1]
	               addSEs sees_Spy_partsEs) 1);
qed_spec_mp "TrustCertVerify";


goal thy
 "!!evs. [| evs : tls;  A ~= Spy |]                                      \
\ ==> Says A B (Crypt (priK A)                                           \
\               (Hash{|Nonce NB, certificate B KB, Nonce M|})) : set evs \
\     --> Says A B {|certificate A (pubK A), Crypt KB (Nonce M)|} : set evs";
by (etac tls.induct 1);
by (ALLGOALS Asm_full_simp_tac);
bind_thm ("UseCertVerify", result() RSN (2, rev_mp));


(*This lemma says that no false certificates exist.  One might extend the
  model to include bogus certificates for the lost agents, but there seems
  little point in doing so: the loss of their private keys is a worse
  breach of security.*)
goalw thy [certificate_def]
 "!!evs. evs : tls     \
\        ==> certificate B KB : parts (sees lost Spy evs) --> KB = pubK B";
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
    ClientCertKeyEx_tac  (i+5)  THEN
    ALLGOALS (asm_simp_tac 
              (!simpset addsimps [not_parts_not_analz]
                        setloop split_tac [expand_if]))  THEN
    (*Remove instances of pubK B:  the Spy already knows all public keys.
      Combining the two simplifier calls makes them run extremely slowly.*)
    ALLGOALS (asm_simp_tac 
              (!simpset addsimps [insert_absorb]
                        setloop split_tac [expand_if]));

(*** Specialized rewriting for the analz_image_... theorems ***)

goal thy "insert (Key K) H = Key `` {K} Un H";
by (Blast_tac 1);
qed "insert_Key_singleton";

goal thy "insert (Key K) (Key``KK Un C) = Key `` (insert K KK) Un C";
by (Blast_tac 1);
qed "insert_Key_image";

(*Reverse the normal simplification of "image" to build up (not break down)
  the set of keys.  Based on analz_image_freshK_ss, but simpler.*)
val analz_image_keys_ss = 
     !simpset delsimps [image_insert, image_Un]
              addsimps [image_insert RS sym, image_Un RS sym,
			rangeI, 
			insert_Key_singleton, 
			insert_Key_image, Un_assoc RS sym]
              setloop split_tac [expand_if];

(*No collection of keys can help the spy get new private keys*)
goal thy  
 "!!evs. evs : tls ==>                                    \
\  ALL KK. (Key(priK B) : analz (Key``KK Un (sees lost Spy evs))) =  \
\            (priK B : KK | B : lost)";
by (etac tls.induct 1);
by (ALLGOALS (asm_simp_tac analz_image_keys_ss));
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed_spec_mp "analz_image_priK";


(*Lemma for the trivial direction of the if-and-only-if*)
goal thy  
 "!!evs. (X : analz (G Un H)) --> (X : analz H)  ==> \
\        (X : analz (G Un H))  =  (X : analz H)";
by (blast_tac (!claset addIs [impOfSubs analz_mono]) 1);
val lemma = result();

(*Knowing some clientKs and serverKs is no help in getting new nonces*)
goal thy  
 "!!evs. evs : tls ==>                                 \
\    ALL KK. KK <= (range clientK Un range serverK) -->           \
\            (Nonce N : analz (Key``KK Un (sees lost Spy evs))) = \
\            (Nonce N : analz (sees lost Spy evs))";
by (etac tls.induct 1);
by (ClientCertKeyEx_tac 6);
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac lemma ));
	(*SLOW: 30s!*)
by (ALLGOALS (asm_simp_tac analz_image_keys_ss));
by (ALLGOALS (asm_simp_tac
	      (!simpset addsimps [analz_image_priK, insert_absorb])));
(*ClientCertKeyEx: a nonce is sent, but one needs a priK to read it.*)
by (Blast_tac 3);
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed_spec_mp "analz_image_keys";


(*If A sends ClientCertKeyEx to an uncompromised B, then M will stay secret.
  The assumption is A~=Spy, not A~:lost, since A doesn't use her private key
  here.*)
goalw thy [certificate_def]
 "!!evs. [| evs : tls;  A~=Spy;  B ~: lost |]                        \
\        ==> Says A B {|certificate A (pubK A), Crypt KB (Nonce M)|} \
\              : set evs  -->  Nonce M ~: analz (sees lost Spy evs)";
by (analz_induct_tac 1);
(*ClientHello*)
by (blast_tac (!claset addSEs sees_Spy_partsEs) 3);
(*SpyKeys*)
by (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_keys]) 2);
(*Fake*)
by (spy_analz_tac 1);
(*ServerHello and ClientCertKeyEx: mostly freshness reasoning*)
by (REPEAT (blast_tac (!claset addSEs partsEs
			       addDs  [impOfSubs analz_subset_parts,
				       Says_imp_sees_Spy' RS analz.Inj]) 1));
bind_thm ("Spy_not_see_premaster_secret", result() RSN (2, rev_mp));


(*** Protocol goal: serverK(NA,NB,M) and clientK(NA,NB,M) remain secure ***)

(*The two proofs are identical*)
goal thy 
 "!!evs. [| Nonce M ~: analz (sees lost Spy evs);  \
\           evs : tls |]                           \
\        ==> Key (clientK(NA,NB,M)) ~: parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*SpyKeys*)
by (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_keys]) 3);
by (blast_tac (!claset addDs [Says_imp_sees_Spy' RS analz.Inj]) 3);
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed "clientK_notin_parts";

goal thy 
 "!!evs. [| Nonce M ~: analz (sees lost Spy evs);  \
\           evs : tls |]                           \
\        ==> Key (serverK(NA,NB,M)) ~: parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*SpyKeys*)
by (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_keys]) 3);
by (blast_tac (!claset addDs [Says_imp_sees_Spy' RS analz.Inj]) 3);
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed "serverK_notin_parts";


(*** Protocol goals: if A receives SERVER FINISHED, then B is present 
     and has used the quoted values XA, XB, etc.  Note that it is up to A
     to compare XA with what she originally sent.
***)

goalw thy [certificate_def]
 "!!evs. [| X = Crypt (serverK(NA,NB,M))                            \
\                 (Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},       \
\                        Nonce NA, Agent XA, Agent A,               \
\                        Nonce NB, Agent XB, certificate B (pubK B)|}); \
\           evs : tls;  A~=Spy;  B ~: lost |]                       \
\    ==> Says A B {|certificate A (pubK A), Crypt KB (Nonce M)|} \
\          : set evs -->              \
\        X : parts (sees lost Spy evs) --> Says B A X : set evs";
by (hyp_subst_tac 1);
by (etac tls.induct 1);
by (ALLGOALS Asm_simp_tac);
(*ClientCertKeyEx: M isn't in the Hash because it's fresh!*)
by (blast_tac (!claset addSDs [Hash_Hash_imp_Nonce]
                       addSEs sees_Spy_partsEs) 2);
(*Fake: the Spy doesn't have the critical session key!*)
by (REPEAT (rtac impI 1));
by (subgoal_tac "Key (serverK(NA,NB,M)) ~: analz (sees lost Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_premaster_secret, 
				     serverK_notin_parts, 
				     not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
qed_spec_mp "TrustServerFinished";


(*** Protocol goal: if B receives CLIENT FINISHED, then A has used the
     quoted values XA, XB, etc., which B can then check.  BUT NOTE:
     B has no way of knowing that A is the sender of CLIENT CERTIFICATE!
***)
goalw thy [certificate_def]
 "!!evs. [| X = Crypt (clientK(NA,NB,M))                        \
\                 (Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},   \
\                        Nonce NA, Agent XA,                    \
\                        certificate A (pubK A),                \
\                        Nonce NB, Agent XB, Agent B|});        \
\           evs : tls;  A~=Spy;  B ~: lost |]                   \
\     ==> Says A B {|certificate A (pubK A),                    \
\                    Crypt KB (Nonce M)|} : set evs -->         \
\         X : parts (sees lost Spy evs) --> Says A B X : set evs";
by (hyp_subst_tac 1);
by (etac tls.induct 1);
by (ALLGOALS Asm_simp_tac);
(*ClientCertKeyEx: M isn't in the Hash because it's fresh!*)
by (blast_tac (!claset addSDs [Hash_Hash_imp_Nonce]
                       addSEs sees_Spy_partsEs) 2);
(*Fake: the Spy doesn't have the critical session key!*)
by (REPEAT (rtac impI 1));
by (subgoal_tac "Key (clientK(NA,NB,M)) ~: analz (sees lost Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_premaster_secret, 
				     clientK_notin_parts, 
				     not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
qed_spec_mp "TrustClientFinished";


(*** Protocol goal: if B receives CLIENT FINISHED, and if B is able to
     check a CERTIFICATE VERIFY from A, then A has used the quoted
     values XA, XB, etc.  Even this one requires A to be uncompromised.
 ***)
goal thy
 "!!evs. [| X = Crypt (clientK(NA,NB,M))                        \
\                 (Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},   \
\                        Nonce NA, Agent XA,                    \
\                        certificate A (pubK A),                \
\                        Nonce NB, Agent XB, Agent B|});        \
\           Says A' B X : set evs;                              \
\           Says B A {|Nonce NA, Nonce NB, Agent XB, certificate B KB|}  \
\             : set evs;                                        \
\           Says A'' B (Crypt (priK A)                                   \
\                       (Hash{|Nonce NB, certificate B KB, Nonce M|}))   \
\             : set evs;                                        \
\        evs : tls;  A ~: lost;  B ~: lost |]                   \
\     ==> Says A B X : set evs";
br TrustClientFinished 1;
br (TrustCertVerify RS UseCertVerify) 5;
by (REPEAT_FIRST (ares_tac [refl]));
by (ALLGOALS 
    (asm_full_simp_tac (!simpset addsimps [Says_imp_sees_Spy RS parts.Inj])));
qed_spec_mp "AuthClientFinished";
