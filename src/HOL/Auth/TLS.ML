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

(** We mostly DO NOT unfold the definition of "certificate".  The attached
    lemmas unfold it lazily, when "certificate B KB" occurs in appropriate
    contexts.
**)

goalw thy [certificate_def] 
    "parts (insert (certificate B KB) H) =  \
\    parts (insert (Crypt (priK Server) {|Agent B, Key KB|}) H)";
by (rtac refl 1);
qed "parts_insert_certificate";

goalw thy [certificate_def] 
    "analz (insert (certificate B KB) H) =  \
\    analz (insert (Crypt (priK Server) {|Agent B, Key KB|}) H)";
by (rtac refl 1);
qed "analz_insert_certificate";
Addsimps [parts_insert_certificate, analz_insert_certificate];

goalw thy [certificate_def] 
    "(X = certificate B KB) = (Crypt (priK Server) {|Agent B, Key KB|} = X)";
by (Blast_tac 1);
qed "eq_certificate_iff";
AddIffs [eq_certificate_iff];


(*Injectiveness of key-generating functions*)
AddIffs [inj_PRF RS inj_eq, inj_sessionK RS inj_eq];

(* invKey(sessionK x) = sessionK x*)
Addsimps [isSym_sessionK, rewrite_rule [isSymKey_def] isSym_sessionK];


(*** clientK and serverK make symmetric keys; no clashes with pubK or priK ***)

goal thy "pubK A ~= sessionK arg";
br notI 1;
by (dres_inst_tac [("f","isSymKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "pubK_neq_sessionK";

goal thy "priK A ~= sessionK arg";
br notI 1;
by (dres_inst_tac [("f","isSymKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "priK_neq_sessionK";

val keys_distinct = [pubK_neq_sessionK, priK_neq_sessionK];
AddIffs (keys_distinct @ (keys_distinct RL [not_sym]));


(**** Protocol Proofs ****)

(*A "possibility property": there are traces that reach the end.
  This protocol has three end points and six messages to consider.*)


(** These proofs make the further assumption that the Nonce_supply nonces 
	(which have the form  @ N. Nonce N ~: used evs)
    lie outside the range of PRF.  This assumption seems reasonable, but
    as it is needed only for the possibility theorems, it is not taken
    as an axiom.
**)



(*Possibility property ending with ServerFinished.*)
goal thy 
 "!!A B. [| ALL evs. (@ N. Nonce N ~: used evs) ~: range PRF;  \
\           A ~= B |] ==> EX SID NA XA NB XB M. EX evs: tls.    \
\  Says B A (Crypt (serverK(NA,NB,M))                       \
\            (Hash{|Nonce M, Number SID,             \
\                   Nonce NA, Number XA, Agent A,      \
\                   Nonce NB, Number XB, Agent B|})) \
\    : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.ClientCertKeyEx
	  RS tls.ServerFinished) 2);
by possibility_tac;
by (REPEAT (Blast_tac 1));
result();

(*And one for ClientFinished.  Either FINISHED message may come first.*)
goal thy 
 "!!A B. [| ALL evs. (@ N. Nonce N ~: used evs) ~: range PRF;  \
\           A ~= B |] ==> EX SID NA XA NB XB M. EX evs: tls.    \
\  Says A B (Crypt (clientK(NA,NB,M))                           \
\            (Hash{|Nonce M, Number SID,             \
\                   Nonce NA, Number XA, Agent A,      \
\                   Nonce NB, Number XB, Agent B|})) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.ClientCertKeyEx
	  RS tls.ClientFinished) 2);
by possibility_tac;
by (REPEAT (Blast_tac 1));
result();

(*Another one, for CertVerify (which is optional)*)
goal thy 
 "!!A B. [| ALL evs. (@ N. Nonce N ~: used evs) ~: range PRF;  \
\           A ~= B |] ==> EX NB PMS. EX evs: tls.   \
\  Says A B (Crypt (priK A)                 \
\            (Hash{|Nonce NB, certificate B (pubK B), Nonce PMS|})) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.ClientCertKeyEx
	  RS tls.CertVerify) 2);
by possibility_tac;
by (REPEAT (Blast_tac 1));
result();


(**** Inductive proofs about tls ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : tls ==> ALL A X. Says A A X ~: set evs";
by (etac tls.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(*Induction for regularity theorems.  If induction formula has the form
   X ~: analz (sees Spy evs) --> ... then it shortens the proof by discarding
   needless information about analz (insert X (sees Spy evs))  *)
fun parts_induct_tac i = 
    etac tls.induct i
    THEN 
    REPEAT (FIRSTGOAL analz_mono_contra_tac)
    THEN 
    fast_tac (!claset addss (!simpset)) i THEN
    ALLGOALS (asm_full_simp_tac (!simpset setloop split_tac [expand_if]));


(** Theorems of the form X ~: parts (sees Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : tls ==> (Key (priK A) : parts (sees Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed "Spy_see_priK";
Addsimps [Spy_see_priK];

goal thy 
 "!!evs. evs : tls ==> (Key (priK A) : analz (sees Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_priK";
Addsimps [Spy_analz_priK];

goal thy  "!!A. [| Key (priK A) : parts (sees Spy evs);       \
\                  evs : tls |] ==> A:lost";
by (blast_tac (!claset addDs [Spy_see_priK]) 1);
qed "Spy_see_priK_D";

bind_thm ("Spy_analz_priK_D", analz_subset_parts RS subsetD RS Spy_see_priK_D);
AddSDs [Spy_see_priK_D, Spy_analz_priK_D];


(*This lemma says that no false certificates exist.  One might extend the
  model to include bogus certificates for the agents, but there seems
  little point in doing so: the loss of their private keys is a worse
  breach of security.*)
goalw thy [certificate_def]
 "!!evs. evs : tls     \
\        ==> certificate B KB : parts (sees Spy evs) --> KB = pubK B";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
bind_thm ("Server_cert_pubB", result() RSN (2, rev_mp));


(*Replace key KB in ClientCertKeyEx by (pubK B) *)
val ClientCertKeyEx_tac = 
    forward_tac [Says_imp_sees_Spy RS parts.Inj RS 
		 parts.Snd RS parts.Snd RS parts.Snd RS Server_cert_pubB]
    THEN' assume_tac
    THEN' hyp_subst_tac;

fun analz_induct_tac i = 
    etac tls.induct i   THEN
    ClientCertKeyEx_tac  (i+7)  THEN	(*ClientFinished*)
    ClientCertKeyEx_tac  (i+6)  THEN	(*CertVerify*)
    ClientCertKeyEx_tac  (i+5)  THEN	(*ClientCertKeyEx*)
    ALLGOALS (asm_simp_tac 
              (!simpset addcongs [if_weak_cong]
                        setloop split_tac [expand_if]))  THEN
    (*Remove instances of pubK B:  the Spy already knows all public keys.
      Combining the two simplifier calls makes them run extremely slowly.*)
    ALLGOALS (asm_simp_tac 
              (!simpset addcongs [if_weak_cong]
			addsimps [insert_absorb]
                        setloop split_tac [expand_if]));


(*** Hashing of nonces ***)

(*Every Nonce that's hashed is already in past traffic.  
  This event occurs in CERTIFICATE VERIFY*)
goal thy "!!evs. [| Hash {|Nonce NB, X|} : parts (sees Spy evs);  \
\                   NB ~: range PRF;  evs : tls |]  \
\                ==> Nonce NB : parts (sees Spy evs)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert_sees])));
by (Fake_parts_insert_tac 1);
(*FINISHED messages are trivial because M : range PRF*)
by (REPEAT (Blast_tac 2));
(*CERTIFICATE VERIFY is the only interesting case*)
by (blast_tac (!claset addSEs sees_Spy_partsEs) 1);
qed "Hash_Nonce_CV";


goal thy "!!evs. [| Notes A {|Agent B, X|} : set evs;  evs : tls |]  \
\                ==> Crypt (pubK B) X : parts (sees Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
by (blast_tac (!claset addIs [parts_insertI]) 1);
qed "Notes_Crypt_parts_sees";


(*** Protocol goal: if B receives CERTIFICATE VERIFY, then A sent it ***)

(*B can check A's signature if he has received A's certificate.
  Perhaps B~=Spy is unnecessary, but there's no obvious proof if the first
  message is Fake.  We don't need guarantees for the Spy anyway.  We must
  assume A~:lost; otherwise, the Spy can forge A's signature.*)
goal thy
 "!!evs. [| X = Crypt (priK A)                                        \
\                 (Hash{|Nonce NB, certificate B KB, Nonce PMS|});      \
\           evs : tls;  A ~: lost;  B ~= Spy |]                       \
\    ==> Says B A {|Nonce NB, Number SID, Number XB, certificate B KB|}  \
\          : set evs --> \
\        X : parts (sees Spy evs) --> Says A B X : set evs";
by (hyp_subst_tac 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
(*ServerHello: nonce NB cannot be in X because it's fresh!*)
by (blast_tac (!claset addSDs [Hash_Nonce_CV]
	               addSEs sees_Spy_partsEs) 1);
qed_spec_mp "TrustCertVerify";


(*If CERTIFICATE VERIFY is present then A has chosen PMS.*)
goal thy
 "!!evs. [| Crypt (priK A) (Hash{|Nonce NB, certificate B KB, Nonce PMS|})  \
\             : parts (sees Spy evs);                                \
\           evs : tls;  A ~: lost |]                                      \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs";
be rev_mp 1;
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed "UseCertVerify";


(*No collection of keys can help the spy get new private keys*)
goal thy  
 "!!evs. evs : tls ==>                                    \
\  ALL KK. (Key(priK B) : analz (Key``KK Un (sees Spy evs))) =  \
\            (priK B : KK | B : lost)";
by (etac tls.induct 1);
by (ALLGOALS
    (asm_simp_tac (analz_image_keys_ss
		   addsimps (analz_insert_certificate::keys_distinct))));
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

(*slightly speeds up the big simplification below*)
goal thy "!!evs. KK <= range sessionK ==> priK B ~: KK";
by (Blast_tac 1);
val range_sessionkeys_not_priK = result();

(*Knowing some session keys is no help in getting new nonces*)
goal thy  
 "!!evs. evs : tls ==>                                 \
\    ALL KK. KK <= range sessionK -->           \
\            (Nonce N : analz (Key``KK Un (sees Spy evs))) = \
\            (Nonce N : analz (sees Spy evs))";
by (etac tls.induct 1);
by (ClientCertKeyEx_tac 6);
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac lemma));
writeln"SLOW simplification: 55 secs??";
(*ClientCertKeyEx is to blame, causing case splits for A, B: lost*)
by (ALLGOALS
    (asm_simp_tac (analz_image_keys_ss 
		   addsimps [range_sessionkeys_not_priK, 
			     analz_image_priK, analz_insert_certificate])));
by (ALLGOALS (asm_simp_tac (!simpset addsimps [insert_absorb])));
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed_spec_mp "analz_image_keys";


goal thy "!!evs. evs : tls ==> Notes A {|Agent B, Nonce (PRF x)|} ~: set evs";
by (parts_induct_tac 1);
(*ClientCertKeyEx: PMS is assumed to differ from any PRF.*)
by (Blast_tac 1);
qed "no_Notes_A_PRF";
Addsimps [no_Notes_A_PRF];


goal thy "!!evs. [| Nonce (PRF (PMS,NA,NB)) : parts (sees Spy evs);  \
\                   evs : tls |]  \
\                ==> Nonce PMS : parts (sees Spy evs)";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert_sees])));
by (Fake_parts_insert_tac 1);
(*Six others, all trivial or by freshness*)
by (REPEAT (blast_tac (!claset addSDs [Notes_Crypt_parts_sees]
                               addSEs sees_Spy_partsEs) 1));
qed "MS_imp_PMS";
AddSDs [MS_imp_PMS];



(*** Protocol goal: serverK(NA,NB,M) and clientK(NA,NB,M) remain secure ***)

(** Some lemmas about session keys, comprising clientK and serverK **)

(*Lemma: those write keys are never sent if M (MASTER SECRET) is secure.  
  Converse doesn't hold; betraying M doesn't force the keys to be sent!*)

goal thy 
 "!!evs. [| Nonce M ~: analz (sees Spy evs);  evs : tls |]   \
\        ==> Key (sessionK(b,NA,NB,M)) ~: parts (sees Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*SpyKeys*)
by (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_keys]) 3);
by (blast_tac (!claset addDs [Says_imp_sees_Spy RS analz.Inj]) 3);
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed "sessionK_notin_parts";
bind_thm ("sessionK_in_partsE", sessionK_notin_parts RSN (2, rev_notE));

Addsimps [sessionK_notin_parts];
AddSEs [sessionK_in_partsE, 
	impOfSubs analz_subset_parts RS sessionK_in_partsE];


(*Lemma: session keys are never used if PMS is fresh.  
  Nonces don't have to agree, allowing session resumption.
  Converse doesn't hold; revealing PMS doesn't force the keys to be sent.
  They are NOT suitable as safe elim rules.*)

goal thy 
 "!!evs. [| Nonce PMS ~: parts (sees Spy evs);  evs : tls |]             \
\  ==> Crypt (sessionK(b, Na, Nb, PRF(PMS,NA,NB))) Y ~: parts (sees Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*Fake*)
by (asm_simp_tac (!simpset addsimps [parts_insert_sees]) 2);
by (Fake_parts_insert_tac 2);
(*Base, ClientFinished, ServerFinished: trivial, e.g. by freshness*)
by (REPEAT 
    (blast_tac (!claset addSDs [Notes_Crypt_parts_sees]
                        addSEs sees_Spy_partsEs) 1));
qed "Crypt_sessionK_notin_parts";

Addsimps [Crypt_sessionK_notin_parts];
AddEs [Crypt_sessionK_notin_parts RSN (2, rev_notE)];


(*NEEDED??*)
goal thy
 "!!evs. [| Says A B {|certA, Crypt KB (Nonce M)|} : set evs;   \
\           A ~= Spy;  evs : tls |] ==> KB = pubK B";
be rev_mp 1;
by (analz_induct_tac 1);
qed "A_Crypt_pubB";


(*** Unicity results for PMS, the pre-master-secret ***)

(*PMS determines B.  Proof borrowed from NS_Public/unique_NA and from Yahalom*)
goal thy 
 "!!evs. [| Nonce PMS ~: analz (sees Spy evs);  evs : tls |]   \
\        ==> EX B'. ALL B.   \
\              Crypt (pubK B) (Nonce PMS) : parts (sees Spy evs) --> B=B'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
(*ClientCertKeyEx*)
by (ClientCertKeyEx_tac 1);
by (asm_simp_tac (!simpset addsimps [all_conj_distrib]) 1);
by (expand_case_tac "PMS = ?y" 1 THEN
    blast_tac (!claset addSEs partsEs) 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK B)  (Nonce PMS) : parts (sees Spy evs); \
\           Crypt(pubK B') (Nonce PMS) : parts (sees Spy evs); \
\           Nonce PMS ~: analz (sees Spy evs);                 \
\           evs : tls |]                                          \
\        ==> B=B'";
by (prove_unique_tac lemma 1);
qed "unique_PMS";


(*In A's internal Note, PMS determines A and B.*)
goal thy 
 "!!evs. [| Nonce PMS ~: analz (sees Spy evs);  evs : tls |]            \
\ ==> EX A' B'. ALL A B.                                                   \
\        Notes A {|Agent B, Nonce PMS|} : set evs --> A=A' & B=B'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (asm_simp_tac (!simpset addsimps [all_conj_distrib]) 1);
(*ClientCertKeyEx: if PMS is fresh, then it can't appear in Notes A X.*)
by (expand_case_tac "PMS = ?y" 1 THEN
    blast_tac (!claset addSDs [Notes_Crypt_parts_sees] addSEs partsEs) 1);
val lemma = result();

goal thy 
 "!!evs. [| Notes A  {|Agent B,  Nonce PMS|} : set evs;  \
\           Notes A' {|Agent B', Nonce PMS|} : set evs;  \
\           Nonce PMS ~: analz (sees Spy evs);      \
\           evs : tls |]                               \
\        ==> A=A' & B=B'";
by (prove_unique_tac lemma 1);
qed "Notes_unique_PMS";



(*If A sends ClientCertKeyEx to an honest B, then the PMS will stay secret.*)
goal thy
 "!!evs. [| evs : tls;  A ~: lost;  B ~: lost |]           \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs  -->   \
\            Nonce PMS ~: analz (sees Spy evs)";
by (analz_induct_tac 1);   (*30 seconds???*)
(*ClientAccepts and ServerAccepts: because PMS ~: range PRF*)
by (REPEAT (fast_tac (!claset addss (!simpset)) 6));
(*ServerHello and ClientCertKeyEx: mostly freshness reasoning*)
by (REPEAT (blast_tac (!claset addSEs partsEs
			       addDs  [Notes_Crypt_parts_sees,
				       impOfSubs analz_subset_parts,
				       Says_imp_sees_Spy RS analz.Inj]) 4));
(*ClientHello*)
by (blast_tac (!claset addSDs [Notes_Crypt_parts_sees]
                               addSEs sees_Spy_partsEs) 3);
(*SpyKeys*)
by (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_keys]) 2);
by (fast_tac (!claset addss (!simpset)) 2);
(*Fake*)
by (spy_analz_tac 1);
bind_thm ("Spy_not_see_PMS", result() RSN (2, rev_mp));





(*If A sends ClientCertKeyEx to an honest B, then the MASTER SECRET
  will stay secret.*)
goal thy
 "!!evs. [| evs : tls;  A ~: lost;  B ~: lost |]           \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs  -->   \
\            Nonce (PRF(PMS,NA,NB)) ~: analz (sees Spy evs)";
by (analz_induct_tac 1);   (*35 seconds*)
(*ClientAccepts and ServerAccepts: because PMS was already visible*)
by (REPEAT (blast_tac (!claset addDs [Spy_not_see_PMS, 
				      Says_imp_sees_Spy RS analz.Inj,
				      Notes_imp_sees_Spy RS analz.Inj]) 6));
(*ClientHello*)
by (Blast_tac 3);
(*SpyKeys: by secrecy of the PMS, Spy cannot make the MS*)
by (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_keys]) 2);
by (blast_tac (!claset addSDs [Spy_not_see_PMS, 
			       Says_imp_sees_Spy RS analz.Inj]) 2);
(*Fake*)
by (spy_analz_tac 1);
(*ServerHello and ClientCertKeyEx: mostly freshness reasoning*)
by (REPEAT (blast_tac (!claset addSEs partsEs
			       addDs  [Notes_Crypt_parts_sees,
				       impOfSubs analz_subset_parts,
				       Says_imp_sees_Spy RS analz.Inj]) 1));
bind_thm ("Spy_not_see_MS", result() RSN (2, rev_mp));


(*** Protocol goals: if A receives SERVER FINISHED, then B is present 
     and has used the quoted values XA, XB, etc.  Note that it is up to A
     to compare XA with what she originally sent.
***)

(*The mention of her name (A) in X assumes A that B knows who she is.*)
goal thy
 "!!evs. [| X = Crypt (serverK(Na,Nb,M))                  \
\                 (Hash{|Nonce M, Number SID,             \
\                        Nonce NA, Number XA, Agent A,    \
\                        Nonce NB, Number XB, Agent B|}); \
\           M = PRF(PMS,NA,NB);                           \
\           evs : tls;  A ~: lost;  B ~: lost |]          \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs --> \
\        X : parts (sees Spy evs) --> Says B A X : set evs";
by (hyp_subst_tac 1);
by (analz_induct_tac 1);	(*16 seconds*)
(*ClientCertKeyEx*)
by (Blast_tac 2);
(*Fake: the Spy doesn't have the critical session key!*)
by (REPEAT (rtac impI 1));
by (subgoal_tac "Key (serverK(Na,Nb,PRF(PMS,NA,NB))) ~: analz(sees Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_MS, 
				     not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
qed_spec_mp "TrustServerFinished";


(*This version refers not to SERVER FINISHED but to any message from B.
  We don't assume B has received CERTIFICATE VERIFY, and an intruder could
  have changed A's identity in all other messages, so we can't be sure
  that B sends his message to A.  If CLIENT KEY EXCHANGE were augmented
  to bind A's identity with M, then we could replace A' by A below.*)
goal thy
 "!!evs. [| evs : tls;  A ~: lost;  B ~: lost;                 \
\           M = PRF(PMS,NA,NB) |]            \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs -->              \
\            Crypt (serverK(Na,Nb,M)) Y : parts (sees Spy evs)  -->  \
\            (EX A'. Says B A' (Crypt (serverK(Na,Nb,M)) Y) : set evs)";
by (hyp_subst_tac 1);
by (analz_induct_tac 1);	(*12 seconds*)
by (REPEAT_FIRST (rtac impI));
(*ClientCertKeyEx*)
by (Blast_tac 2);
(*Fake: the Spy doesn't have the critical session key!*)
by (subgoal_tac "Key (serverK(Na,Nb,PRF(PMS,NA,NB))) ~: analz(sees Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_MS, 
				     not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
(*ServerFinished.  If the message is old then apply induction hypothesis...*)
by (rtac conjI 1 THEN Blast_tac 2);
(*...otherwise delete induction hyp and use unicity of PMS.*)
by (thin_tac "?PP-->?QQ" 1);
by (Step_tac 1);
by (subgoal_tac "Nonce PMS ~: analz(sees Spy evsSF)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_PMS]) 2);
by (blast_tac (!claset addSEs [MPair_parts]
		       addDs  [Notes_Crypt_parts_sees,
			       Says_imp_sees_Spy RS parts.Inj,
			       unique_PMS]) 1);
qed_spec_mp "TrustServerMsg";


(*** Protocol goal: if B receives any message encrypted with clientK
     then A has sent it, ASSUMING that A chose PMS.  Authentication is
     assumed here; B cannot verify it.  But if the message is
     CLIENT FINISHED, then B can then check the quoted values XA, XB, etc.
***)
goal thy
 "!!evs. [| evs : tls;  A ~: lost;  B ~: lost |]                         \
\  ==> Notes A {|Agent B, Nonce PMS|} : set evs -->                  \
\      Crypt (clientK(Na,Nb,PRF(PMS,NA,NB))) Y : parts (sees Spy evs) -->  \
\      Says A B (Crypt (clientK(Na,Nb,PRF(PMS,NA,NB))) Y) : set evs";
by (analz_induct_tac 1);	(*13 seconds*)
by (REPEAT_FIRST (rtac impI));
(*ClientCertKeyEx*)
by (Blast_tac 2);
(*Fake: the Spy doesn't have the critical session key!*)
by (subgoal_tac "Key (clientK(Na,Nb,PRF(PMS,NA,NB))) ~: analz(sees Spy evsa)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_MS, 
				     not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
(*ClientFinished.  If the message is old then apply induction hypothesis...*)
by (step_tac (!claset delrules [conjI]) 1);
by (subgoal_tac "Nonce PMS ~: analz (sees Spy evsCF)" 1);
by (asm_simp_tac (!simpset addsimps [Spy_not_see_PMS]) 2);
by (blast_tac (!claset addSEs [MPair_parts]
		       addDs  [Notes_unique_PMS]) 1);
qed_spec_mp "TrustClientMsg";


(*** Protocol goal: if B receives CLIENT FINISHED, and if B is able to
     check a CERTIFICATE VERIFY from A, then A has used the quoted
     values XA, XB, etc.  Even this one requires A to be uncompromised.
 ***)
goal thy
 "!!evs. [| Says A' B (Crypt (clientK(Na,Nb,PRF(PMS,NA,NB))) Y) : set evs; \
\           Says B  A {|Nonce NB, Number SID, Number XB, certificate B KB|}  \
\             : set evs;                                                  \
\           Says A'' B (Crypt (priK A)                                    \
\                       (Hash{|Nonce NB, certificate B KB, Nonce PMS|}))  \
\             : set evs;                                                  \
\        evs : tls;  A ~: lost;  B ~: lost |]                             \
\     ==> Says A B (Crypt (clientK(Na,Nb,PRF(PMS,NA,NB))) Y) : set evs";
by (blast_tac (!claset addSIs [TrustClientMsg, UseCertVerify]
                       addDs  [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "AuthClientFinished";
