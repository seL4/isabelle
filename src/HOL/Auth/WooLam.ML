(*  Title:      HOL/Auth/WooLam
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "woolam" for the Woo-Lam protocol.

Simplified version from page 11 of
  Abadi and Needham.  Prudent Engineering Practice for Cryptographic Protocols.
  IEEE Trans. S.E. 22(1), 1996, pages 6-15.
*)

open WooLam;

proof_timing:=true;
HOL_quantifiers := false;


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX NB. EX evs: woolam.               \
\              Says Server B (Crypt (shrK B) {|Agent A, Nonce NB|}) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (woolam.Nil RS woolam.WL1 RS woolam.WL2 RS woolam.WL3 RS 
          woolam.WL4 RS woolam.WL5) 2);
by possibility_tac;
result();


(**** Inductive proofs about woolam ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : woolam ==> ALL A X. Says A A X ~: set evs";
by (etac woolam.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

goal thy "!!evs. Says A' B X : set evs ==> X : analz (spies evs)";
by (etac (Says_imp_spies RS analz.Inj) 1);
qed "WL4_analz_spies";

bind_thm ("WL4_parts_spies",
          WL4_analz_spies RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X ~: parts (spies evs) *)
fun parts_induct_tac i = 
    etac woolam.induct i  THEN 
    forward_tac [WL4_parts_spies] (i+5)  THEN
    prove_simple_subgoals_tac 1;


(** Theorems of the form X ~: parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's bad at start)*)
goal thy 
 "!!evs. evs : woolam ==> (Key (shrK A) : parts (spies evs)) = (A : bad)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : woolam ==> (Key (shrK A) : analz (spies evs)) = (A : bad)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (spies evs);       \
\                  evs : woolam |] ==> A:bad";
by (blast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(**** Autheticity properties for Woo-Lam ****)


(*** WL4 ***)

(*If the encrypted message appears then it originated with Alice*)
goal thy 
 "!!evs. [| A ~: bad;  evs : woolam |]                        \
\        ==> Crypt (shrK A) (Nonce NB) : parts (spies evs)  \
\            --> (EX B. Says A B (Crypt (shrK A) (Nonce NB)) : set evs)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (Blast_tac 1);
qed_spec_mp "NB_Crypt_imp_Alice_msg";

(*Guarantee for Server: if it gets a message containing a certificate from 
  Alice, then she originated that certificate.  But we DO NOT know that B
  ever saw it: the Spy may have rerouted the message to the Server.*)
goal thy 
 "!!evs. [| A ~: bad;  evs : woolam;                      \
\           Says B' Server {|Agent A, Agent B, Crypt (shrK A) (Nonce NB)|} \
\            : set evs |]                                  \
\        ==> EX B. Says A B (Crypt (shrK A) (Nonce NB)) : set evs";
by (blast_tac (!claset addSIs [NB_Crypt_imp_Alice_msg]
                      addSEs [MPair_parts]
                      addDs  [Says_imp_spies RS parts.Inj]) 1);
qed "Server_trusts_WL4";


(*** WL5 ***)

(*Server sent WL5 only if it received the right sort of message*)
goal thy 
 "!!evs. evs : woolam ==>                                                   \
\        Says Server B (Crypt (shrK B) {|Agent A, NB|}) : set evs           \
\        --> (EX B'. Says B' Server {|Agent A, Agent B, Crypt (shrK A) NB|} \
\               : set evs)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (ALLGOALS Blast_tac);
bind_thm ("Server_sent_WL5", result() RSN (2, rev_mp));


(*If the encrypted message appears then it originated with the Server!*)
goal thy 
 "!!evs. [| B ~: bad;  evs : woolam |]                             \
\        ==> Crypt (shrK B) {|Agent A, NB|} : parts (spies evs)  \
\        --> Says Server B (Crypt (shrK B) {|Agent A, NB|}) : set evs";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed_spec_mp "NB_Crypt_imp_Server_msg";

(*Partial guarantee for B: if it gets a message of correct form then the Server
  sent the same message.*)
goal thy 
 "!!evs. [| Says S B (Crypt (shrK B) {|Agent A, NB|}) : set evs;         \
\           B ~: bad;  evs : woolam |]                                  \
\        ==> Says Server B (Crypt (shrK B) {|Agent A, NB|}) : set evs";
by (blast_tac (!claset addSIs [NB_Crypt_imp_Server_msg]
                      addDs  [Says_imp_spies RS parts.Inj]) 1);
qed "B_got_WL5";

(*Guarantee for B.  If B gets the Server's certificate then A has encrypted
  the nonce using her key.  This event can be no older than the nonce itself.
  But A may have sent the nonce to some other agent and it could have reached
  the Server via the Spy.*)
goal thy 
 "!!evs. [| Says S B (Crypt (shrK B) {|Agent A, Nonce NB|}): set evs; \
\           A ~: bad;  B ~: bad;  evs : woolam  |]                  \
\        ==> EX B. Says A B (Crypt (shrK A) (Nonce NB)) : set evs";
by (blast_tac (!claset addIs  [Server_trusts_WL4]
                      addSDs [B_got_WL5 RS Server_sent_WL5]) 1);
qed "B_trusts_WL5";


(*B only issues challenges in response to WL1.  Useful??*)
goal thy 
 "!!evs. [| B ~= Spy;  evs : woolam |]        \
\    ==> Says B A (Nonce NB) : set evs        \
\        --> (EX A'. Says A' B (Agent A) : set evs)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (ALLGOALS Blast_tac);
bind_thm ("B_said_WL2", result() RSN (2, rev_mp));


(**CANNOT be proved because A doesn't know where challenges come from...
goal thy 
 "!!evs. [| A ~: bad;  B ~= Spy;  evs : woolam |]           \
\    ==> Crypt (shrK A) (Nonce NB) : parts (spies evs) &  \
\        Says B A (Nonce NB) : set evs                       \
\        --> Says A B (Crypt (shrK A) (Nonce NB)) : set evs";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (Step_tac 1);
by (blast_tac (!claset addSEs partsEs) 1);
**)
