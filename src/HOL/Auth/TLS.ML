(*  Title:      HOL/Auth/TLS
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

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

open TLS;

set proof_timing;
HOL_quantifiers := false;

(*Automatically unfold the definition of "certificate"*)
Addsimps [certificate_def];

(*Injectiveness of key-generating functions*)
AddIffs [inj_PRF RS inj_eq, inj_sessionK RS inj_eq];

(* invKey(sessionK x) = sessionK x*)
Addsimps [isSym_sessionK, rewrite_rule [isSymKey_def] isSym_sessionK];


(*** clientK and serverK make symmetric keys; no clashes with pubK or priK ***)

goal thy "pubK A ~= sessionK arg";
by (rtac notI 1);
by (dres_inst_tac [("f","isSymKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "pubK_neq_sessionK";

goal thy "priK A ~= sessionK arg";
by (rtac notI 1);
by (dres_inst_tac [("f","isSymKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "priK_neq_sessionK";

val keys_distinct = [pubK_neq_sessionK, priK_neq_sessionK];
AddIffs (keys_distinct @ (keys_distinct RL [not_sym]));


(**** Protocol Proofs ****)

(*Possibility properties state that some traces run the protocol to the end.
  Four paths and 12 rules are considered.*)


(** These proofs assume that the Nonce_supply nonces 
	(which have the form  @ N. Nonce N ~: used evs)
    lie outside the range of PRF.  It seems reasonable, but as it is needed
    only for the possibility theorems, it is not taken as an axiom.
**)


(*Possibility property ending with ClientAccepts.*)
goal thy 
 "!!A B. [| ALL evs. (@ N. Nonce N ~: used evs) ~: range PRF;  \
\           A ~= B |]            \
\  ==> EX SID M. EX evs: tls.    \
\        Notes A {|Number SID, Agent A, Agent B, Nonce M|} : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.Certificate RS
	  tls.ClientKeyExch RS tls.ClientFinished RS tls.ServerFinished RS
	  tls.ClientAccepts) 2);
by possibility_tac;
by (REPEAT (Blast_tac 1));
result();

(*And one for ServerAccepts.  Either FINISHED message may come first.*)
goal thy 
 "!!A B. [| ALL evs. (@ N. Nonce N ~: used evs) ~: range PRF;  \
\           A ~= B |]                        \
\  ==> EX SID NA PA NB PB M. EX evs: tls.    \
\        Notes B {|Number SID, Agent A, Agent B, Nonce M|} : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.Certificate RS
	  tls.ClientKeyExch RS tls.ServerFinished RS tls.ClientFinished RS
	  tls.ServerAccepts) 2);
by possibility_tac;
by (REPEAT (Blast_tac 1));
result();

(*Another one, for CertVerify (which is optional)*)
goal thy 
 "!!A B. [| ALL evs. (@ N. Nonce N ~: used evs) ~: range PRF;  \
\           A ~= B |]                       \
\  ==> EX NB PMS. EX evs: tls.   \
\  Says A B (Crypt (priK A) (Hash{|Nonce NB, Agent B, Nonce PMS|})) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (tls.Nil RS tls.ClientHello RS tls.ServerHello RS tls.Certificate RS
	  tls.ClientKeyExch RS tls.CertVerify) 2);
by possibility_tac;
by (REPEAT (Blast_tac 1));
result();

(*Another one, for session resumption (both ServerResume and ClientResume) *)
goal thy 
 "!!A B. [| evs0 : tls;     \
\           Notes A {|Number SID, Agent A, Agent B, Nonce M|} : set evs0; \
\           Notes B {|Number SID, Agent A, Agent B, Nonce M|} : set evs0; \
\           ALL evs. (@ N. Nonce N ~: used evs) ~: range PRF;  \
\           A ~= B |] ==> EX NA PA NB PB X. EX evs: tls.    \
\      X = Hash{|Number SID, Nonce M,             \
\                       Nonce NA, Number PA, Agent A,      \
\                       Nonce NB, Number PB, Agent B|}  &  \
\      Says A B (Crypt (clientK(NA,NB,M)) X) : set evs  &  \
\      Says B A (Crypt (serverK(NA,NB,M)) X) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (etac (tls.ClientHello RS tls.ServerHello RS tls.ServerResume RS 
	  tls.ClientResume) 2);
by possibility_tac;
by (REPEAT (Blast_tac 1));
result();



(**** Inductive proofs about tls ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : tls ==> ALL A X. Says A A X ~: set evs";
by (etac tls.induct 1);
by Auto_tac;
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(*Induction for regularity theorems.  If induction formula has the form
   X ~: analz (spies evs) --> ... then it shortens the proof by discarding
   needless information about analz (insert X (spies evs))  *)
fun parts_induct_tac i = 
    etac tls.induct i
    THEN 
    REPEAT (FIRSTGOAL analz_mono_contra_tac)
    THEN 
    fast_tac (claset() addss (simpset())) i THEN
    ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if]));


(** Theorems of the form X ~: parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's bad at start)*)
goal thy 
 "!!evs. evs : tls ==> (Key (priK A) : parts (spies evs)) = (A : bad)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed "Spy_see_priK";
Addsimps [Spy_see_priK];

goal thy 
 "!!evs. evs : tls ==> (Key (priK A) : analz (spies evs)) = (A : bad)";
by (auto_tac(claset() addDs [impOfSubs analz_subset_parts], simpset()));
qed "Spy_analz_priK";
Addsimps [Spy_analz_priK];

AddSDs [Spy_see_priK RSN (2, rev_iffD1), 
	Spy_analz_priK RSN (2, rev_iffD1)];


(*This lemma says that no false certificates exist.  One might extend the
  model to include bogus certificates for the agents, but there seems
  little point in doing so: the loss of their private keys is a worse
  breach of security.*)
goalw thy [certificate_def]
 "!!evs. [| certificate B KB : parts (spies evs);  evs : tls |]  \
\        ==> pubK B = KB";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed "certificate_valid";


(*Replace key KB in ClientKeyExch by (pubK B) *)
val ClientKeyExch_tac = 
    forward_tac [Says_imp_spies RS parts.Inj RS certificate_valid]
    THEN' assume_tac
    THEN' hyp_subst_tac;

fun analz_induct_tac i = 
    etac tls.induct i   THEN
    ClientKeyExch_tac  (i+6)  THEN	(*ClientKeyExch*)
    ALLGOALS (asm_simp_tac 
              (simpset() addcongs [if_weak_cong]
                         addsimps (expand_ifs@pushes)
                         addsplits [expand_if]))  THEN
    (*Remove instances of pubK B:  the Spy already knows all public keys.
      Combining the two simplifier calls makes them run extremely slowly.*)
    ALLGOALS (asm_simp_tac 
              (simpset() addcongs [if_weak_cong]
			 addsimps [insert_absorb]
                         addsplits [expand_if]));


(*** Properties of items found in Notes ***)

goal thy "!!evs. [| Notes A {|Agent B, X|} : set evs;  evs : tls |]  \
\                ==> Crypt (pubK B) X : parts (spies evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
by (blast_tac (claset() addIs [parts_insertI]) 1);
qed "Notes_Crypt_parts_spies";

(*C may be either A or B*)
goal thy
 "!!evs. [| Notes C {|s, Agent A, Agent B, Nonce(PRF(PMS,NA,NB))|} : set evs; \
\           evs : tls     \
\        |] ==> Crypt (pubK B) (Nonce PMS) : parts (spies evs)";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Clarify_tac);
(*Fake*)
by (blast_tac (claset() addIs [parts_insertI]) 1);
(*Client, Server Accept*)
by (REPEAT (blast_tac (claset() addSEs spies_partsEs
                                addSDs [Notes_Crypt_parts_spies]) 1));
qed "Notes_master_imp_Crypt_PMS";

(*Compared with the theorem above, both premise and conclusion are stronger*)
goal thy
 "!!evs. [| Notes A {|s, Agent A, Agent B, Nonce(PRF(PMS,NA,NB))|} : set evs;\
\           evs : tls     \
\        |] ==> Notes A {|Agent B, Nonce PMS|} : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*ServerAccepts*)
by (Fast_tac 1);	(*Blast_tac's very slow here*)
qed "Notes_master_imp_Notes_PMS";


(*** Protocol goal: if B receives CertVerify, then A sent it ***)

(*B can check A's signature if he has received A's certificate.*)
goal thy
 "!!evs. [| X : parts (spies evs);                          \
\           X = Crypt (priK A) (Hash{|nb, Agent B, pms|});  \
\           evs : tls;  A ~: bad |]                         \
\    ==> Says A B X : set evs";
by (etac rev_mp 1);
by (hyp_subst_tac 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
val lemma = result();

(*Final version: B checks X using the distributed KA instead of priK A*)
goal thy
 "!!evs. [| X : parts (spies evs);                            \
\           X = Crypt (invKey KA) (Hash{|nb, Agent B, pms|}); \
\           certificate A KA : parts (spies evs);             \
\           evs : tls;  A ~: bad |]                           \
\    ==> Says A B X : set evs";
by (blast_tac (claset() addSDs [certificate_valid] addSIs [lemma]) 1);
qed "TrustCertVerify";


(*If CertVerify is present then A has chosen PMS.*)
goal thy
 "!!evs. [| Crypt (priK A) (Hash{|nb, Agent B, Nonce PMS|}) \
\             : parts (spies evs);                          \
\           evs : tls;  A ~: bad |]                         \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
val lemma = result();

(*Final version using the distributed KA instead of priK A*)
goal thy
 "!!evs. [| Crypt (invKey KA) (Hash{|nb, Agent B, Nonce PMS|}) \
\             : parts (spies evs);                             \
\           certificate A KA : parts (spies evs);              \
\           evs : tls;  A ~: bad |]                            \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs";
by (blast_tac (claset() addSDs [certificate_valid] addSIs [lemma]) 1);
qed "UseCertVerify";


goal thy "!!evs. evs : tls ==> Notes A {|Agent B, Nonce (PRF x)|} ~: set evs";
by (parts_induct_tac 1);
(*ClientKeyExch: PMS is assumed to differ from any PRF.*)
by (Blast_tac 1);
qed "no_Notes_A_PRF";
Addsimps [no_Notes_A_PRF];


goal thy "!!evs. [| Nonce (PRF (PMS,NA,NB)) : parts (spies evs);  \
\                   evs : tls |]  \
\                ==> Nonce PMS : parts (spies evs)";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
(*Six others, all trivial or by freshness*)
by (REPEAT (blast_tac (claset() addSDs [Notes_Crypt_parts_spies]
                                addSEs spies_partsEs) 1));
qed "MS_imp_PMS";
AddSDs [MS_imp_PMS];



(*** Unicity results for PMS, the pre-master-secret ***)

(*PMS determines B.  Proof borrowed from NS_Public/unique_NA and from Yahalom*)
goal thy 
 "!!evs. [| Nonce PMS ~: analz (spies evs);  evs : tls |]   \
\        ==> EX B'. ALL B.   \
\              Crypt (pubK B) (Nonce PMS) : parts (spies evs) --> B=B'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
(*ClientKeyExch*)
by (ClientKeyExch_tac 1);
by (asm_simp_tac (simpset() addsimps [all_conj_distrib]) 1);
by (expand_case_tac "PMS = ?y" 1 THEN
    blast_tac (claset() addSEs partsEs) 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK B)  (Nonce PMS) : parts (spies evs); \
\           Crypt(pubK B') (Nonce PMS) : parts (spies evs); \
\           Nonce PMS ~: analz (spies evs);                 \
\           evs : tls |]                                          \
\        ==> B=B'";
by (prove_unique_tac lemma 1);
qed "Crypt_unique_PMS";


(** It is frustrating that we need two versions of the unicity results.
    But Notes A {|Agent B, Nonce PMS|} determines both A and B.  Sometimes
    we have only the weaker assertion Crypt(pubK B) (Nonce PMS), which 
    determines B alone, and only if PMS is secret.
**)

(*In A's internal Note, PMS determines A and B.*)
goal thy "!!evs. evs : tls               \
\                ==> EX A' B'. ALL A B.  \
\                    Notes A {|Agent B, Nonce PMS|} : set evs --> A=A' & B=B'";
by (parts_induct_tac 1);
by (asm_simp_tac (simpset() addsimps [all_conj_distrib]) 1);
(*ClientKeyExch: if PMS is fresh, then it can't appear in Notes A X.*)
by (expand_case_tac "PMS = ?y" 1 THEN
    blast_tac (claset() addSDs [Notes_Crypt_parts_spies] addSEs partsEs) 1);
val lemma = result();

goal thy 
 "!!evs. [| Notes A  {|Agent B,  Nonce PMS|} : set evs;  \
\           Notes A' {|Agent B', Nonce PMS|} : set evs;  \
\           evs : tls |]                               \
\        ==> A=A' & B=B'";
by (prove_unique_tac lemma 1);
qed "Notes_unique_PMS";



(**** Secrecy Theorems ****)

(*Key compromise lemma needed to prove analz_image_keys.
  No collection of keys can help the spy get new private keys.*)
goal thy  
 "!!evs. evs : tls ==>                                      \
\  ALL KK. (Key(priK B) : analz (Key``KK Un (spies evs))) = \
\          (priK B : KK | B : bad)";
by (etac tls.induct 1);
by (ALLGOALS
    (asm_simp_tac (analz_image_keys_ss
		   addsimps (certificate_def::keys_distinct))));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_priK";


(*slightly speeds up the big simplification below*)
goal thy "!!evs. KK <= range sessionK ==> priK B ~: KK";
by (Blast_tac 1);
val range_sessionkeys_not_priK = result();

(*Lemma for the trivial direction of the if-and-only-if*)
goal thy  
 "!!evs. (X : analz (G Un H)) --> (X : analz H)  ==> \
\        (X : analz (G Un H))  =  (X : analz H)";
by (blast_tac (claset() addIs [impOfSubs analz_mono]) 1);
val analz_image_keys_lemma = result();

(** Strangely, the following version doesn't work:
\    ALL Z. (Nonce N : analz (Key``(sessionK``Z) Un (spies evs))) = \
\           (Nonce N : analz (spies evs))";
**)

goal thy  
 "!!evs. evs : tls ==>                                    \
\    ALL KK. KK <= range sessionK -->                     \
\            (Nonce N : analz (Key``KK Un (spies evs))) = \
\            (Nonce N : analz (spies evs))";
by (etac tls.induct 1);
by (ClientKeyExch_tac 7);
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_keys_lemma));
by (ALLGOALS    (*18 seconds*)
    (asm_simp_tac (analz_image_keys_ss 
		   addsimps (expand_ifs@pushes)
		   addsimps [range_sessionkeys_not_priK, 
                             analz_image_priK, certificate_def])));
by (ALLGOALS (asm_simp_tac (simpset() addsimps [insert_absorb])));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_keys";

(*Knowing some session keys is no help in getting new nonces*)
goal thy
 "!!evs. evs : tls ==>          \
\        Nonce N : analz (insert (Key (sessionK z)) (spies evs)) =  \
\        (Nonce N : analz (spies evs))";
by (asm_simp_tac (analz_image_keys_ss addsimps [analz_image_keys]) 1);
qed "analz_insert_key";
Addsimps [analz_insert_key];


(*** Protocol goal: serverK(Na,Nb,M) and clientK(Na,Nb,M) remain secure ***)

(** Some lemmas about session keys, comprising clientK and serverK **)


(*Lemma: session keys are never used if PMS is fresh.  
  Nonces don't have to agree, allowing session resumption.
  Converse doesn't hold; revealing PMS doesn't force the keys to be sent.
  THEY ARE NOT SUITABLE AS SAFE ELIM RULES.*)
goal thy 
 "!!evs. [| Nonce PMS ~: parts (spies evs);  \
\           K = sessionK((Na, Nb, PRF(PMS,NA,NB)), b);  \
\           evs : tls |]             \
\  ==> Key K ~: parts (spies evs) & (ALL Y. Crypt K Y ~: parts (spies evs))";
by (etac rev_mp 1);
by (hyp_subst_tac 1);
by (analz_induct_tac 1);
(*SpyKeys*)
by (blast_tac (claset() addSEs spies_partsEs) 3);
(*Fake*)
by (Fake_parts_insert_tac 2);
(** LEVEL 6 **)
(*Oops*)
by (fast_tac (claset() addSEs [MPair_parts]
		       addDs  [Says_imp_spies RS parts.Inj]
		       addss (simpset())) 6);
by (REPEAT 
    (blast_tac (claset() addSDs [Notes_Crypt_parts_spies, 
				 Notes_master_imp_Crypt_PMS]
                         addSEs spies_partsEs) 1));
val lemma = result();

goal thy 
 "!!evs. [| Key (sessionK((Na, Nb, PRF(PMS,NA,NB)), b)) : parts (spies evs); \
\           evs : tls |]             \
\        ==> Nonce PMS : parts (spies evs)";
by (blast_tac (claset() addDs [lemma]) 1);
qed "PMS_sessionK_not_spied";

goal thy 
 "!!evs. [| Crypt (sessionK((Na, Nb, PRF(PMS,NA,NB)), b)) Y  \
\             : parts (spies evs);  evs : tls |]             \
\        ==> Nonce PMS : parts (spies evs)";
by (blast_tac (claset() addDs [lemma]) 1);
qed "PMS_Crypt_sessionK_not_spied";

(*Lemma: write keys are never sent if M (MASTER SECRET) is secure.  
  Converse doesn't hold; betraying M doesn't force the keys to be sent!
  The strong Oops condition can be weakened later by unicity reasoning, 
	with some effort.*)
goal thy 
 "!!evs. [| ALL A. Says A Spy (Key (sessionK((NA,NB,M),b))) ~: set evs; \
\           Nonce M ~: analz (spies evs);  evs : tls |]   \
\        ==> Key (sessionK((NA,NB,M),b)) ~: parts (spies evs)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (analz_induct_tac 1);        (*17 seconds*)
(*Oops*)
by (Blast_tac 4);
(*SpyKeys*)
by (blast_tac (claset() addDs [Says_imp_spies RS analz.Inj]) 3);
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed "sessionK_not_spied";
Addsimps [sessionK_not_spied];


(*If A sends ClientKeyExch to an honest B, then the PMS will stay secret.*)
goal thy
 "!!evs. [| evs : tls;  A ~: bad;  B ~: bad |]           \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs  -->   \
\            Nonce PMS ~: analz (spies evs)";
by (analz_induct_tac 1);   (*11 seconds*)
(*ClientAccepts and ServerAccepts: because PMS ~: range PRF*)
by (REPEAT (fast_tac (claset() addss (simpset())) 6));
(*ClientHello, ServerHello, ClientKeyExch, ServerResume: 
  mostly freshness reasoning*)
by (REPEAT (blast_tac (claset() addSEs partsEs
				addDs  [Notes_Crypt_parts_spies,
					impOfSubs analz_subset_parts,
					Says_imp_spies RS analz.Inj]) 3));
(*SpyKeys*)
by (fast_tac (claset() addss (simpset())) 2);
(*Fake*)
by (spy_analz_tac 1);
bind_thm ("Spy_not_see_PMS", result() RSN (2, rev_mp));


(*If A sends ClientKeyExch to an honest B, then the MASTER SECRET
  will stay secret.*)
goal thy
 "!!evs. [| evs : tls;  A ~: bad;  B ~: bad |]           \
\        ==> Notes A {|Agent B, Nonce PMS|} : set evs  -->   \
\            Nonce (PRF(PMS,NA,NB)) ~: analz (spies evs)";
by (analz_induct_tac 1);   (*13 seconds*)
(*ClientAccepts and ServerAccepts: because PMS was already visible*)
by (REPEAT (blast_tac (claset() addDs [Spy_not_see_PMS, 
				       Says_imp_spies RS analz.Inj,
				       Notes_imp_spies RS analz.Inj]) 6));
(*ClientHello*)
by (Blast_tac 3);
(*SpyKeys: by secrecy of the PMS, Spy cannot make the MS*)
by (blast_tac (claset() addSDs [Spy_not_see_PMS, 
				Says_imp_spies RS analz.Inj]) 2);
(*Fake*)
by (spy_analz_tac 1);
(*ServerHello and ClientKeyExch: mostly freshness reasoning*)
by (REPEAT (blast_tac (claset() addSEs partsEs
				addDs  [Notes_Crypt_parts_spies,
					impOfSubs analz_subset_parts,
					Says_imp_spies RS analz.Inj]) 1));
bind_thm ("Spy_not_see_MS", result() RSN (2, rev_mp));


(*** Weakening the Oops conditions for leakage of clientK ***)

(*If A created PMS then nobody other than the Spy would send a message
  using a clientK generated from that PMS.*)
goal thy
 "!!evs. [| evs : tls;  A' ~= Spy |]                \
\  ==> Notes A {|Agent B, Nonce PMS|} : set evs -->                  \
\      Says A' B' (Crypt (clientK(Na,Nb,PRF(PMS,NA,NB))) Y) : set evs -->  \
\      A = A'";
by (analz_induct_tac 1);	(*8 seconds*)
by (ALLGOALS Clarify_tac);
(*ClientFinished, ClientResume: by unicity of PMS*)
by (REPEAT 
    (blast_tac (claset() addSDs [Notes_master_imp_Notes_PMS]
     	 	         addIs  [Notes_unique_PMS RS conjunct1]) 2));
(*ClientKeyExch*)
by (blast_tac (claset() addSDs [PMS_Crypt_sessionK_not_spied,
				Says_imp_spies RS parts.Inj]) 1);
bind_thm ("Says_clientK_unique",
	  result() RSN(2,rev_mp) RSN(2,rev_mp));


(*If A created PMS and has not leaked her clientK to the Spy, 
  then nobody has.*)
goal thy
 "!!evs. evs : tls                         \
\  ==> Says A Spy (Key(clientK(Na,Nb,PRF(PMS,NA,NB)))) ~: set evs --> \
\      Notes A {|Agent B, Nonce PMS|} : set evs -->                   \
\      (ALL A. Says A Spy (Key(clientK(Na,Nb,PRF(PMS,NA,NB)))) ~: set evs) ";
by (etac tls.induct 1);
(*This roundabout proof sequence avoids looping in simplification*)
by (ALLGOALS Simp_tac);
by (ALLGOALS Clarify_tac);
by (Fake_parts_insert_tac 1);
by (ALLGOALS Asm_simp_tac);
(*Oops*)
by (blast_tac (claset() addIs [Says_clientK_unique]) 2);
(*ClientKeyExch*)
by (blast_tac (claset() addSDs [PMS_sessionK_not_spied]
			addSEs spies_partsEs) 1);
qed_spec_mp "clientK_Oops_ALL";



(*** Weakening the Oops conditions for leakage of serverK ***)

(*If A created PMS for B, then nobody other than B or the Spy would
  send a message using a serverK generated from that PMS.*)
goal thy
 "!!evs. [| evs : tls;  A ~: bad;  B ~: bad;  B' ~= Spy |]                \
\  ==> Notes A {|Agent B, Nonce PMS|} : set evs -->                  \
\      Says B' A' (Crypt (serverK(Na,Nb,PRF(PMS,NA,NB))) Y) : set evs -->  \
\      B = B'";
by (analz_induct_tac 1);	(*9 seconds*)
by (ALLGOALS Clarify_tac);
(*ServerResume, ServerFinished: by unicity of PMS*)
by (REPEAT
    (blast_tac (claset() addSEs [MPair_parts]
			 addSDs [Notes_master_imp_Crypt_PMS, 
				 Says_imp_spies RS parts.Inj]
			 addDs  [Spy_not_see_PMS, 
				 Notes_Crypt_parts_spies,
				 Crypt_unique_PMS]) 2));
(*ClientKeyExch*)
by (blast_tac (claset() addSDs [PMS_Crypt_sessionK_not_spied,
				Says_imp_spies RS parts.Inj]) 1);
bind_thm ("Says_serverK_unique",
	  result() RSN(2,rev_mp) RSN(2,rev_mp));

(*If A created PMS for B, and B has not leaked his serverK to the Spy, 
  then nobody has.*)
goal thy
 "!!evs. [| evs : tls;  A ~: bad;  B ~: bad |]                        \
\  ==> Says B Spy (Key(serverK(Na,Nb,PRF(PMS,NA,NB)))) ~: set evs --> \
\      Notes A {|Agent B, Nonce PMS|} : set evs -->                   \
\      (ALL A. Says A Spy (Key(serverK(Na,Nb,PRF(PMS,NA,NB)))) ~: set evs) ";
by (etac tls.induct 1);
(*This roundabout proof sequence avoids looping in simplification*)
by (ALLGOALS Simp_tac);
by (ALLGOALS Clarify_tac);
by (Fake_parts_insert_tac 1);
by (ALLGOALS Asm_simp_tac);
(*Oops*)
by (blast_tac (claset() addIs [Says_serverK_unique]) 2);
(*ClientKeyExch*)
by (blast_tac (claset() addSDs [PMS_sessionK_not_spied]
			addSEs spies_partsEs) 1);
qed_spec_mp "serverK_Oops_ALL";



(*** Protocol goals: if A receives ServerFinished, then B is present 
     and has used the quoted values PA, PB, etc.  Note that it is up to A
     to compare PA with what she originally sent.
***)

(*The mention of her name (A) in X assures A that B knows who she is.*)
goal thy
 "!!evs. [| X = Crypt (serverK(Na,Nb,M))                  \
\                 (Hash{|Number SID, Nonce M,             \
\                        Nonce Na, Number PA, Agent A,    \
\                        Nonce Nb, Number PB, Agent B|}); \
\           M = PRF(PMS,NA,NB);                           \
\           evs : tls;  A ~: bad;  B ~: bad |]            \
\        ==> (ALL A. Says A Spy (Key(serverK(Na,Nb,M))) ~: set evs) --> \
\            Notes A {|Agent B, Nonce PMS|} : set evs --> \
\            X : parts (spies evs) --> Says B A X : set evs";
by (hyp_subst_tac 1);
by (analz_induct_tac 1);        (*26 seconds*)
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
(*proves ServerResume*)
by (ALLGOALS Clarify_tac);
(*ClientKeyExch*)
by (blast_tac (claset() addSDs [PMS_Crypt_sessionK_not_spied]) 2);
(*Fake: the Spy doesn't have the critical session key!*)
by (subgoal_tac "Key (serverK(Na,Nb,PRF(PMS,NA,NB))) ~: analz(spies evsa)" 1);
by (asm_simp_tac (simpset() addsimps [Spy_not_see_MS, 
				      not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
val lemma = normalize_thm [RSmp] (result());

(*Final version*)
goal thy
 "!!evs. [| X = Crypt (serverK(Na,Nb,M))                  \
\                 (Hash{|Number SID, Nonce M,             \
\                        Nonce Na, Number PA, Agent A,    \
\                        Nonce Nb, Number PB, Agent B|}); \
\           M = PRF(PMS,NA,NB);                           \
\           X : parts (spies evs);                        \
\           Notes A {|Agent B, Nonce PMS|} : set evs;     \
\           Says B Spy (Key (serverK(Na,Nb,M))) ~: set evs; \
\           evs : tls;  A ~: bad;  B ~: bad |]          \
\        ==> Says B A X : set evs";
by (blast_tac (claset() addIs [lemma]
                        addEs [serverK_Oops_ALL RSN(2, rev_notE)]) 1);
qed_spec_mp "TrustServerFinished";



(*This version refers not to ServerFinished but to any message from B.
  We don't assume B has received CertVerify, and an intruder could
  have changed A's identity in all other messages, so we can't be sure
  that B sends his message to A.  If CLIENT KEY EXCHANGE were augmented
  to bind A's identity with PMS, then we could replace A' by A below.*)
goal thy
 "!!evs. [| M = PRF(PMS,NA,NB);  evs : tls;  A ~: bad;  B ~: bad |]     \
\        ==> (ALL A. Says A Spy (Key(serverK(Na,Nb,M))) ~: set evs) --> \
\            Notes A {|Agent B, Nonce PMS|} : set evs -->              \
\            Crypt (serverK(Na,Nb,M)) Y : parts (spies evs)  -->  \
\            (EX A'. Says B A' (Crypt (serverK(Na,Nb,M)) Y) : set evs)";
by (hyp_subst_tac 1);
by (analz_induct_tac 1);	(*20 seconds*)
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ex_disj_distrib])));
by (ALLGOALS Clarify_tac);
(*ServerResume, ServerFinished: by unicity of PMS*)
by (REPEAT
    (blast_tac (claset() addSEs [MPair_parts]
			 addSDs [Notes_master_imp_Crypt_PMS, 
				 Says_imp_spies RS parts.Inj]
			 addDs  [Spy_not_see_PMS, 
				 Notes_Crypt_parts_spies,
				 Crypt_unique_PMS]) 3));
(*ClientKeyExch*)
by (blast_tac (claset() addSDs [PMS_Crypt_sessionK_not_spied]) 2);
(*Fake: the Spy doesn't have the critical session key!*)
by (subgoal_tac "Key (serverK(Na,Nb,PRF(PMS,NA,NB))) ~: analz(spies evsa)" 1);
by (asm_simp_tac (simpset() addsimps [Spy_not_see_MS, 
				      not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
val lemma = normalize_thm [RSmp] (result());

(*Final version*)
goal thy
 "!!evs. [| M = PRF(PMS,NA,NB);                           \
\           Crypt (serverK(Na,Nb,M)) Y : parts (spies evs); \
\           Notes A {|Agent B, Nonce PMS|} : set evs;     \
\           Says B Spy (Key (serverK(Na,Nb,M))) ~: set evs; \
\           evs : tls;  A ~: bad;  B ~: bad |]          \
\        ==> EX A'. Says B A' (Crypt (serverK(Na,Nb,M)) Y) : set evs";
by (blast_tac (claset() addIs [lemma]
                        addEs [serverK_Oops_ALL RSN(2, rev_notE)]) 1);
qed_spec_mp "TrustServerMsg";



(*** Protocol goal: if B receives any message encrypted with clientK
     then A has sent it, ASSUMING that A chose PMS.  Authentication is
     assumed here; B cannot verify it.  But if the message is
     ClientFinished, then B can then check the quoted values PA, PB, etc.
***)

goal thy
 "!!evs. [| M = PRF(PMS,NA,NB);  evs : tls;  A ~: bad;  B ~: bad |] \
\    ==> (ALL A. Says A Spy (Key(clientK(Na,Nb,M))) ~: set evs) --> \
\        Notes A {|Agent B, Nonce PMS|} : set evs -->               \
\        Crypt (clientK(Na,Nb,M)) Y : parts (spies evs) -->         \
\        Says A B (Crypt (clientK(Na,Nb,M)) Y) : set evs";
by (hyp_subst_tac 1);
by (analz_induct_tac 1);	(*15 seconds*)
by (ALLGOALS Clarify_tac);
(*ClientFinished, ClientResume: by unicity of PMS*)
by (REPEAT (blast_tac (claset() delrules [conjI]
		                addSDs [Notes_master_imp_Notes_PMS]
	 	                addDs  [Notes_unique_PMS]) 3));
(*ClientKeyExch*)
by (blast_tac (claset() addSDs [PMS_Crypt_sessionK_not_spied]) 2);
(*Fake: the Spy doesn't have the critical session key!*)
by (subgoal_tac "Key (clientK(Na,Nb,PRF(PMS,NA,NB))) ~: analz(spies evsa)" 1);
by (asm_simp_tac (simpset() addsimps [Spy_not_see_MS, 
				      not_parts_not_analz]) 2);
by (Fake_parts_insert_tac 1);
val lemma = normalize_thm [RSmp] (result());

(*Final version*)
goal thy
 "!!evs. [| M = PRF(PMS,NA,NB);                           \
\           Crypt (clientK(Na,Nb,M)) Y : parts (spies evs);  \
\           Notes A {|Agent B, Nonce PMS|} : set evs;        \
\           Says A Spy (Key(clientK(Na,Nb,M))) ~: set evs;  \
\           evs : tls;  A ~: bad;  B ~: bad |]                         \
\  ==> Says A B (Crypt (clientK(Na,Nb,M)) Y) : set evs";
by (blast_tac (claset() addIs [lemma]
                        addEs [clientK_Oops_ALL RSN(2, rev_notE)]) 1);
qed "TrustClientMsg";



(*** Protocol goal: if B receives ClientFinished, and if B is able to
     check a CertVerify from A, then A has used the quoted
     values PA, PB, etc.  Even this one requires A to be uncompromised.
 ***)
goal thy
 "!!evs. [| M = PRF(PMS,NA,NB);                           \
\           Says A Spy (Key(clientK(Na,Nb,M))) ~: set evs;\
\           Says A' B (Crypt (clientK(Na,Nb,M)) Y) : set evs; \
\           certificate A KA : parts (spies evs);       \
\           Says A'' B (Crypt (invKey KA) (Hash{|nb, Agent B, Nonce PMS|}))\
\             : set evs;                                                  \
\        evs : tls;  A ~: bad;  B ~: bad |]                             \
\     ==> Says A B (Crypt (clientK(Na,Nb,M)) Y) : set evs";
by (blast_tac (claset() addSIs [TrustClientMsg, UseCertVerify]
                        addDs  [Says_imp_spies RS parts.Inj]) 1);
qed "AuthClientFinished";

(*22/9/97: loads in 622s, which is 10 minutes 22 seconds*)
(*24/9/97: loads in 672s, which is 11 minutes 12 seconds [stronger theorems]*)
(*29/9/97: loads in 481s, after removing Certificate from ClientKeyExch*)
(*30/9/97: loads in 476s, after removing unused theorems*)
(*30/9/97: loads in 448s, after fixing ServerResume*)
