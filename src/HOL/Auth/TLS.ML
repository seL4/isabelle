(*  Title:      HOL/Auth/TLS
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

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

val keys_distinct = [pubK_neq_clientK, pubK_neq_serverK, 
		     priK_neq_clientK, priK_neq_serverK, clientK_neq_serverK];
AddIffs (keys_distinct @ (keys_distinct RL [not_sym]));


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
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 2);
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


(*This lemma says that no false certificates exist.  One might extend the
  model to include bogus certificates for the lost agents, but there seems
  little point in doing so: the loss of their private keys is a worse
  breach of security.*)
goalw thy [certificate_def]
 "!!evs. evs : tls     \
\        ==> certificate B KB : parts (sees lost Spy evs) --> KB = pubK B";
by (etac tls.induct 1);
by (ALLGOALS (asm_full_simp_tac (!simpset setloop split_tac [expand_if])));
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
    ClientCertKeyEx_tac  (i+7)  THEN	(*ClientFinished*)
    ClientCertKeyEx_tac  (i+6)  THEN	(*CertVerify*)
    ClientCertKeyEx_tac  (i+5)  THEN	(*ClientCertKeyEx*)
    rewrite_goals_tac  [certificate_def]  THEN
    ALLGOALS (asm_simp_tac 
              (!simpset addsimps [not_parts_not_analz]
                        setloop split_tac [expand_if]))  THEN
    (*Remove instances of pubK B:  the Spy already knows all public keys.
      Combining the two simplifier calls makes them run extremely slowly.*)
    ALLGOALS (asm_simp_tac 
              (!simpset addsimps [insert_absorb]
                        setloop split_tac [expand_if]));


(*** Hashing of nonces ***)

(*Every Nonce that's hashed is already in past traffic. *)
goal thy "!!evs. [| Hash {|Nonce N, X|} : parts (sees lost Spy evs);  \
\                   evs : tls |]  \
\                ==> Nonce N : parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac tls.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert_sees]
			             setloop split_tac [expand_if])));
by (Fake_parts_insert_tac 2);
by (REPEAT (blast_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
		               addSEs partsEs) 1));
qed "Hash_imp_Nonce1";

(*Lemma needed to prove Hash_Hash_imp_Nonce*)
goal thy "!!evs. [| Hash{|Nonce NA, Nonce NB, Nonce M|}  \
\                       : parts (sees lost Spy evs);     \
\                   evs : tls |]  \
\                ==> Nonce M : parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac tls.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert_sees]
			             setloop split_tac [expand_if])));
by (Fake_parts_insert_tac 2);
by (blast_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
		       addSEs partsEs) 1);
qed "Hash_imp_Nonce2";
AddSDs [Hash_imp_Nonce2];


goal thy "!!evs. [| Notes A {|Agent B, X|} : set evs;  evs : tls |]  \
\                ==> Crypt (pubK B) X : parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
by (blast_tac (!claset addIs [parts_insertI]) 1);
qed "Notes_Crypt_parts_sees";


(*NEEDED??*)
goal thy "!!evs. [| Hash {| Hash{|Nonce NA, Nonce NB, Nonce M|}, X |}  \
\                      : parts (sees lost Spy evs);      \
\                   evs : tls |]                         \
\                ==> Nonce M : parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac tls.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert_sees]
			             setloop split_tac [expand_if])));
by (Fake_parts_insert_tac 2);
by (step_tac (!claset addSDs [Notes_Crypt_parts_sees,
			      Says_imp_sees_Spy' RS parts.Inj]
		      addSEs partsEs) 1);
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
by (ALLGOALS (asm_simp_tac (!simpset setloop split_tac [expand_if])));
by (step_tac (!claset addSDs [Notes_Crypt_parts_sees,
			      Says_imp_sees_Spy' RS parts.Inj]
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
by (ALLGOALS (asm_simp_tac (!simpset setloop split_tac [expand_if])));
by (Fake_parts_insert_tac 1);
(*ServerHello: nonce NB cannot be in X because it's fresh!*)
by (blast_tac (!claset addSDs [Hash_imp_Nonce1]
	               addSEs sees_Spy_partsEs) 1);
qed_spec_mp "TrustCertVerify";


(*If CERTIFICATE VERIFY is present then A has chosen M.*)
goal thy
 "!!evs. [| Crypt (priK A) (Hash{|Nonce NB, certificate B KB, Nonce M|})  \
\             : parts (sees lost Spy evs);                                \
\           evs : tls;  A ~: lost |]                                      \
\        ==> Notes A {|Agent B, Nonce M|} : set evs";
be rev_mp 1;
by (etac tls.induct 1);
by (ALLGOALS (asm_full_simp_tac (!simpset setloop split_tac [expand_if])));
by (Fake_parts_insert_tac 2);
by (Blast_tac 1);
qed "UseCertVerify";


(*No collection of keys can help the spy get new private keys*)
goal thy  
 "!!evs. evs : tls ==>                                    \
\  ALL KK. (Key(priK B) : analz (Key``KK Un (sees lost Spy evs))) =  \
\            (priK B : KK | B : lost)";
by (etac tls.induct 1);
by (ALLGOALS
    (asm_simp_tac (analz_image_keys_ss 
		   addsimps (certificate_def::keys_distinct))));
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
by (REPEAT_FIRST (rtac lemma));
writeln"SLOW simplification: 50 secs!??";
by (ALLGOALS
    (asm_simp_tac (analz_image_keys_ss 
		   addsimps (analz_image_priK::certificate_def::
			     keys_distinct))));
by (ALLGOALS (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_priK])));
by (ALLGOALS (asm_simp_tac (!simpset addsimps [insert_absorb])));
(*ClientCertKeyEx: a nonce is sent, but one needs a priK to read it.*)
by (Blast_tac 3);
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed_spec_mp "analz_image_keys";


(*If A sends ClientCertKeyEx to an uncompromised B, then M will stay secret.*)
goal thy
 "!!evs. [| evs : tls;  A ~: lost;  B ~: lost |]           \
\        ==> Notes A {|Agent B, Nonce M|} : set evs  -->   \
\            Nonce M ~: analz (sees lost Spy evs)";
by (analz_induct_tac 1);
(*ClientHello*)
by (blast_tac (!claset addSDs [Notes_Crypt_parts_sees]
                               addSEs sees_Spy_partsEs) 3);
(*SpyKeys*)
by (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_keys]) 2);
(*Fake*)
by (spy_analz_tac 1);
(*ServerHello and ClientCertKeyEx: mostly freshness reasoning*)
by (REPEAT (blast_tac (!claset addSEs partsEs
			       addDs  [Notes_Crypt_parts_sees,
				       impOfSubs analz_subset_parts,
				       Says_imp_sees_Spy' RS analz.Inj]) 1));
bind_thm ("Spy_not_see_premaster_secret", result() RSN (2, rev_mp));


(*** Protocol goal: serverK(NA,NB,M) and clientK(NA,NB,M) remain secure ***)

(** First, some lemmas about those write keys.  The proofs for serverK are 
    nearly identical to those for clientK. **)

(*Lemma: those write keys are never sent if M is secure.  
  Converse doesn't hold; betraying M doesn't force the keys to be sent!*)

goal thy 
 "!!evs. [| Nonce M ~: analz (sees lost Spy evs);  evs : tls |]   \
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

Addsimps [clientK_notin_parts];
AddSEs [clientK_notin_parts RSN (2, rev_notE)];

goal thy 
 "!!evs. [| Nonce M ~: analz (sees lost Spy evs);  evs : tls |]   \
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

Addsimps [serverK_notin_parts];
AddSEs [serverK_notin_parts RSN (2, rev_notE)];

(*Lemma: those write keys are never used if M is fresh.  
  Converse doesn't hold; betraying M doesn't force the keys to be sent!
  NOT suitable as safe elim rules.*)

goal thy 
 "!!evs. [| Nonce M ~: used evs;  evs : tls |]                           \
\        ==> Crypt (clientK(NA,NB,M)) Y ~: parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*ClientFinished: since M is fresh, a different instance of clientK was used.*)
by (blast_tac (!claset addSDs [Notes_Crypt_parts_sees]
                               addSEs sees_Spy_partsEs) 3);
by (Fake_parts_insert_tac 2);
(*Base*)
by (Blast_tac 1);
qed "Crypt_clientK_notin_parts";

Addsimps [Crypt_clientK_notin_parts];
AddEs [Crypt_clientK_notin_parts RSN (2, rev_notE)];

goal thy 
 "!!evs. [| Nonce M ~: used evs;  evs : tls |]                           \
\        ==> Crypt (serverK(NA,NB,M)) Y ~: parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*ServerFinished: since M is fresh, a different instance of serverK was used.*)
by (blast_tac (!claset addSDs [Notes_Crypt_parts_sees]
                               addSEs sees_Spy_partsEs) 3);
by (Fake_parts_insert_tac 2);
(*Base*)
by (Blast_tac 1);
qed "Crypt_serverK_notin_parts";

Addsimps [Crypt_serverK_notin_parts];
AddEs [Crypt_serverK_notin_parts RSN (2, rev_notE)];


(*Weakening A~:lost to A~=Spy would complicate later uses of the rule*)
goal thy
 "!!evs. [| Says A B {|certA, Crypt KB (Nonce M)|} : set evs;   \
\           A ~: lost;  evs : tls |] ==> KB = pubK B";
be rev_mp 1;
by (analz_induct_tac 1);
qed "A_Crypt_pubB";


(*** Unicity results for M, the pre-master-secret ***)

(*Induction for theorems of the form X ~: analz (sees lost Spy evs) --> ...
  It simplifies the proof by discarding needless information about
	analz (insert X (sees lost Spy evs)) 
*)
fun analz_mono_parts_induct_tac i = 
    etac tls.induct i           THEN 
    ClientCertKeyEx_tac  (i+5)  THEN	(*ClientCertKeyEx*)
    REPEAT_FIRST analz_mono_contra_tac;


(*M determines B.  Proof borrowed from NS_Public/unique_NA and from Yahalom*)
goal thy 
 "!!evs. [| Nonce M ~: analz (sees lost Spy evs);  evs : tls |]   \
\        ==> EX B'. ALL B.   \
\              Crypt (pubK B) (Nonce M) : parts (sees lost Spy evs) --> B=B'";
by (etac rev_mp 1);
by (analz_mono_parts_induct_tac 1);
by (prove_simple_subgoals_tac 1);
by (asm_simp_tac (!simpset addsimps [all_conj_distrib]
                           setloop split_tac [expand_if]) 2);
(*ClientCertKeyEx*)
by (expand_case_tac "M = ?y" 2 THEN
    REPEAT (blast_tac (!claset addSEs partsEs) 2));
by (Fake_parts_insert_tac 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK B)  (Nonce M) : parts (sees lost Spy evs); \
\           Crypt(pubK B') (Nonce M) : parts (sees lost Spy evs); \
\           Nonce M ~: analz (sees lost Spy evs);                 \
\           evs : tls |]                                          \
\        ==> B=B'";
by (prove_unique_tac lemma 1);
qed "unique_M";


(*In A's note to herself, M determines A and B.*)
goal thy 
 "!!evs. [| Nonce M ~: analz (sees lost Spy evs);  evs : tls |]            \
\ ==> EX A' B'. ALL A B.                                                   \
\        Notes A {|Agent B, Nonce M|} : set evs --> A=A' & B=B'";
by (etac rev_mp 1);
by (analz_mono_parts_induct_tac 1);
by (prove_simple_subgoals_tac 1);
by (asm_simp_tac (!simpset addsimps [all_conj_distrib]) 1);
(*ClientCertKeyEx: if M is fresh, then it can't appear in Notes A X.*)
by (expand_case_tac "M = ?y" 1 THEN
    blast_tac (!claset addSDs [Notes_Crypt_parts_sees] addSEs partsEs) 1);
val lemma = result();

goal thy 
 "!!evs. [| Notes A  {|Agent B,  Nonce M|} : set evs;  \
\           Notes A' {|Agent B', Nonce M|} : set evs;  \
\           Nonce M ~: analz (sees lost Spy evs);      \
\           evs : tls |]                               \
\        ==> A=A' & B=B'";
by (prove_unique_tac lemma 1);
qed "Notes_unique_M";



(*** Protocol goals: if A receives SERVER FINISHED, then B is present 
     and has used the quoted values XA, XB, etc.  Note that it is up to A
     to compare XA with what she originally sent.
***)

(*The mention of her name (A) in X assumes A that B knows who she is.*)
goal thy
 "!!evs. [| X = Crypt (serverK(NA,NB,M))                                \
\                 (Hash{|Hash{|Nonce NA, Nonce NB, Nonce M|},           \
\                        Nonce NA, Agent XA, Agent A,                   \
\                        Nonce NB, Agent XB, certificate B (pubK B)|}); \
\           evs : tls;  A ~: lost;  B ~: lost |]                        \
\        ==> Notes A {|Agent B, Nonce M|} : set evs -->                 \
\        X : parts (sees lost Spy evs) --> Says B A X : set evs";
by (hyp_subst_tac 1);
by (analz_induct_tac 1);
by (REPEAT_FIRST (rtac impI));
(*Fake: the Spy doesn't have the critical session key!*)
by (REPEAT (rtac impI 1));
by (subgoal_tac "Key (serverK(NA,NB,M)) ~: analz (sees lost Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_premaster_secret, 
				     not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
qed_spec_mp "TrustServerFinished";


(*This version refers not to SERVER FINISHED but to any message from B.
  We don't assume B has received CERTIFICATE VERIFY, and an intruder could
  have changed A's identity in all other messages, so we can't be sure
  that B sends his message to A.*)
goal thy
 "!!evs. [| evs : tls;  A ~: lost;  B ~: lost |]                         \
\        ==> Notes A {|Agent B, Nonce M|} : set evs -->                  \
\            Crypt (serverK(NA,NB,M)) Y : parts (sees lost Spy evs)  --> \
\            (EX A'. Says B A' (Crypt (serverK(NA,NB,M)) Y) : set evs)";
by (analz_induct_tac 1);
by (REPEAT_FIRST (rtac impI));
(*Fake: the Spy doesn't have the critical session key!*)
by (subgoal_tac "Key (serverK(NA,NB,M)) ~: analz (sees lost Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_premaster_secret, 
				     not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
(*ServerFinished.  If the message is old then apply induction hypothesis...*)
by (rtac conjI 1 THEN Blast_tac 2);
(*...otherwise delete induction hyp and use unicity of M.*)
by (thin_tac "?PP-->?QQ" 1);
by (Step_tac 1);
by (subgoal_tac "Nonce M ~: analz (sees lost Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_premaster_secret]) 2);
by (blast_tac (!claset addSEs [MPair_parts]
		       addDs  [Notes_Crypt_parts_sees,
			       Says_imp_sees_Spy' RS parts.Inj,
			       unique_M]) 1);
qed_spec_mp "TrustServerMsg";


(*** Protocol goal: if B receives any message encrypted with clientK
     then A has sent it, ASSUMING that A chose M.  Authentication is
     assumed here; B cannot verify it.  But if the message is
     CLIENT FINISHED, then B can then check the quoted values XA, XB, etc.
***)
goal thy
 "!!evs. [| evs : tls;  A ~: lost;  B ~: lost |]                         \
\        ==> Notes A {|Agent B, Nonce M|} : set evs -->                  \
\            Crypt (clientK(NA,NB,M)) Y : parts (sees lost Spy evs) -->  \
\            Says A B (Crypt (clientK(NA,NB,M)) Y) : set evs";
by (analz_induct_tac 1);
by (REPEAT_FIRST (rtac impI));
(*Fake: the Spy doesn't have the critical session key!*)
by (subgoal_tac "Key (clientK(NA,NB,M)) ~: analz (sees lost Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_premaster_secret, 
				     not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
(*ClientFinished.  If the message is old then apply induction hypothesis...*)
by (step_tac (!claset delrules [conjI]) 1);
by (subgoal_tac "Nonce M ~: analz (sees lost Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_premaster_secret]) 2);
by (blast_tac (!claset addSEs [MPair_parts]
		       addDs  [Notes_unique_M]) 1);
qed_spec_mp "TrustClientMsg";


(*** Protocol goal: if B receives CLIENT FINISHED, and if B is able to
     check a CERTIFICATE VERIFY from A, then A has used the quoted
     values XA, XB, etc.  Even this one requires A to be uncompromised.
 ***)
goal thy
 "!!evs. [| Says A' B (Crypt (clientK(NA,NB,M)) Y) : set evs;             \
\           Says B  A {|Nonce NA, Nonce NB, Agent XB, certificate B KB|}  \
\             : set evs;                                                  \
\           Says A'' B (Crypt (priK A)                                    \
\                       (Hash{|Nonce NB, certificate B KB, Nonce M|}))    \
\             : set evs;                                                  \
\        evs : tls;  A ~: lost;  B ~: lost |]                             \
\     ==> Says A B (Crypt (clientK(NA,NB,M)) Y) : set evs";
by (blast_tac (!claset addSIs [TrustClientMsg, UseCertVerify]
                       addDs  [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "AuthClientFinished";
