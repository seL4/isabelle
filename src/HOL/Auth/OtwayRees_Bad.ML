(*  Title:      HOL/Auth/OtwayRees_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

The FAULTY version omitting encryption of Nonce NB, as suggested on page 247 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)

This file illustrates the consequences of such errors.  We can still prove
impressive-looking properties such as Spy_not_see_encrypted_key, yet the
protocol is open to a middleperson attack.  Attempting to prove some key lemmas
indicates the possibility of this attack.
*)

AddDs  [Says_imp_knows_Spy RS parts.Inj, parts.Body];
AddDs  [impOfSubs analz_subset_parts, impOfSubs Fake_parts_insert];

(*A "possibility property": there are traces that reach the end*)
Goal "B \\<noteq> Server   \
\     ==> \\<exists>K. \\<exists>NA. \\<exists>evs \\<in> otway.          \
\           Says B A {|Nonce NA, Crypt (shrK A) {|Nonce NA, Key K|}|} \
\             \\<in> set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS 
          otway.OR1 RS otway.Reception RS
          otway.OR2 RS otway.Reception RS 
          otway.OR3 RS otway.Reception RS otway.OR4) 2);
by possibility_tac;
result();

Goal "[| Gets B X \\<in> set evs; evs \\<in> otway |] ==> \\<exists>A. Says A B X \\<in> set evs";
by (etac rev_mp 1);
by (etac otway.induct 1);
by Auto_tac;
qed"Gets_imp_Says";

(*Must be proved separately for each protocol*)
Goal "[| Gets B X \\<in> set evs; evs \\<in> otway |]  ==> X \\<in> knows Spy evs";
by (blast_tac (claset() addSDs [Gets_imp_Says, Says_imp_knows_Spy]) 1);
qed"Gets_imp_knows_Spy";
AddDs [Gets_imp_knows_Spy RS parts.Inj];


(**** Inductive proofs about otway ****)


(** For reasoning about the encrypted portion of messages **)

Goal "[| Gets B {|N, Agent A, Agent B, X|} \\<in> set evs;  evs \\<in> otway |] \
\     ==> X \\<in> analz (knows Spy evs)";
by (blast_tac (claset() addSDs [Gets_imp_knows_Spy RS analz.Inj]) 1);
qed "OR2_analz_knows_Spy";

Goal "[| Gets B {|N, X, Crypt (shrK B) X'|} \\<in> set evs;  evs \\<in> otway |] \
\     ==> X \\<in> analz (knows Spy evs)";
by (blast_tac (claset() addSDs [Gets_imp_knows_Spy RS analz.Inj]) 1);
qed "OR4_analz_knows_Spy";

Goal "Says Server B {|NA, X, Crypt K' {|NB,K|}|} \\<in> set evs \
\     ==> K \\<in> parts (knows Spy evs)";
by (Blast_tac 1);
qed "Oops_parts_knows_Spy";

bind_thm ("OR2_parts_knows_Spy",
          OR2_analz_knows_Spy RS (impOfSubs analz_subset_parts));
bind_thm ("OR4_parts_knows_Spy",
          OR4_analz_knows_Spy RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X \\<notin> parts (knows Spy evs).*)
fun parts_induct_tac i = 
    etac otway.induct i			THEN 
    ftac Oops_parts_knows_Spy (i+7) THEN
    ftac OR4_parts_knows_Spy (i+6) THEN
    ftac OR2_parts_knows_Spy (i+4) THEN 
    prove_simple_subgoals_tac  i;


(** Theorems of the form X \\<notin> parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees a good agent's shared key!*)
Goal "evs \\<in> otway ==> (Key (shrK A) \\<in> parts (knows Spy evs)) = (A \\<in> bad)";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

Goal "evs \\<in> otway ==> (Key (shrK A) \\<in> analz (knows Spy evs)) = (A \\<in> bad)";
by (auto_tac(claset() addDs [impOfSubs analz_subset_parts], simpset()));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

AddSDs [Spy_see_shrK RSN (2, rev_iffD1), 
	Spy_analz_shrK RSN (2, rev_iffD1)];


(*** Proofs involving analz ***)

(*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*)
Goal "[| Says Server B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} \\<in> set evs; \
\        evs \\<in> otway |]                                           \
\  ==> K \\<notin> range shrK & (\\<exists>i. NA = Nonce i) & (\\<exists>j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Simp_tac);
by (ALLGOALS Blast_tac);
qed "Says_Server_message_form";


(*For proofs involving analz.*)
val analz_knows_Spy_tac = 
    dtac OR2_analz_knows_Spy 5 THEN assume_tac 5 THEN 
    dtac OR4_analz_knows_Spy 7 THEN assume_tac 7 THEN
    ftac Says_Server_message_form 8 THEN assume_tac 8 THEN
    REPEAT ((eresolve_tac [exE, conjE] ORELSE' hyp_subst_tac) 8);


(****
 The following is to prove theorems of the form

  Key K \\<in> analz (insert (Key KAB) (knows Spy evs)) ==>
  Key K \\<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
Goal "evs \\<in> otway ==>                                 \
\  \\<forall>K KK. KK <= - (range shrK) -->                 \
\         (Key K \\<in> analz (Key`KK Un (knows Spy evs))) =  \
\         (K \\<in> KK | Key K \\<in> analz (knows Spy evs))";
by (etac otway.induct 1);
by analz_knows_Spy_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma ));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";


Goal "[| evs \\<in> otway;  KAB \\<notin> range shrK |] ==>       \
\     Key K \\<in> analz (insert (Key KAB) (knows Spy evs)) =  \
\     (K = KAB | Key K \\<in> analz (knows Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

Goal "[| Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|}   \\<in> set evs; \ 
\        Says Server B' {|NA',X',Crypt (shrK B') {|NB',K|}|} \\<in> set evs; \
\        evs \\<in> otway |] ==> X=X' & B=B' & NA=NA' & NB=NB'";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Asm_simp_tac);
(*Remaining cases: OR3 and OR4*)
by (REPEAT (Blast_tac 1)); 
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

Goal "[| A \\<notin> bad;  B \\<notin> bad;  evs \\<in> otway |]                      \
\     ==> Says Server B                                            \
\           {|NA, Crypt (shrK A) {|NA, Key K|},                    \
\             Crypt (shrK B) {|NB, Key K|}|} \\<in> set evs -->         \
\         Notes Spy {|NA, NB, Key K|} \\<notin> set evs -->               \
\         Key K \\<notin> analz (knows Spy evs)";
by (etac otway.induct 1);
by analz_knows_Spy_tac;
by (ALLGOALS
    (asm_simp_tac (simpset() addcongs [conj_cong] 
                             addsimps [analz_insert_eq, analz_insert_freshK]
                                      @ pushes @ split_ifs)));
(*Oops*)
by (blast_tac (claset() addSDs [unique_session_keys]) 4);
(*OR4*) 
by (Blast_tac 3);
(*OR3*)
by (Blast_tac 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

Goal "[| Says Server B                                           \
\         {|NA, Crypt (shrK A) {|NA, Key K|},                    \
\               Crypt (shrK B) {|NB, Key K|}|} \\<in> set evs;        \
\        Notes Spy {|NA, NB, Key K|} \\<notin> set evs;                 \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> otway |]                    \
\     ==> Key K \\<notin> analz (knows Spy evs)";
by (ftac Says_Server_message_form 1 THEN assume_tac 1);
by (blast_tac (claset() addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(*** Attempting to prove stronger properties ***)

(*Only OR1 can have caused such a part of a message to appear.
  The premise A \\<noteq> B prevents OR2's similar-looking cryptogram from being
  picked up.  Original Otway-Rees doesn't need it.*)
Goal "[| A \\<notin> bad;  A \\<noteq> B;  evs \\<in> otway |]                \
\     ==> Crypt (shrK A) {|NA, Agent A, Agent B|} \\<in> parts (knows Spy evs) --> \
\         Says A B {|NA, Agent A, Agent B,                  \
\                    Crypt (shrK A) {|NA, Agent A, Agent B|}|}  \\<in> set evs";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed_spec_mp "Crypt_imp_OR1";


(*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!
  The premise A \\<noteq> B allows use of Crypt_imp_OR1*)
(*Only it is FALSE.  Somebody could make a fake message to Server
          substituting some other nonce NA' for NB.*)
Goal "[| A \\<notin> bad;  A \\<noteq> B;  evs \\<in> otway |]                                \
\     ==> Crypt (shrK A) {|NA, Key K|} \\<in> parts (knows Spy evs) -->    \
\         Says A B {|NA, Agent A, Agent B,                        \
\                    Crypt (shrK A) {|NA, Agent A, Agent B|}|}    \
\          \\<in> set evs -->                                          \
\         (\\<exists>B NB. Says Server B                                 \
\              {|NA,                                              \
\                Crypt (shrK A) {|NA, Key K|},                    \
\                Crypt (shrK B) {|NB, Key K|}|}  \\<in> set evs)";
by (parts_induct_tac 1);
(*Fake*)
by (Blast_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (Blast_tac 1);
(*OR3 and OR4*)
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ex_disj_distrib])));
by (ALLGOALS Clarify_tac);
(*OR4*)
by (blast_tac (claset() addSIs [Crypt_imp_OR1]) 2);
(*OR3*)  (** LEVEL 5 **)
(*The hypotheses at this point suggest an attack in which nonce NB is used
  in two different roles:
          Gets Server
           {|Nonce NA, Agent Aa, Agent A,
             Crypt (shrK Aa) {|Nonce NA, Agent Aa, Agent A|}, Nonce NB,
             Crypt (shrK A) {|Nonce NA, Agent Aa, Agent A|}|}
          \\<in> set evs3;
          Says A B
           {|Nonce NB, Agent A, Agent B,
             Crypt (shrK A) {|Nonce NB, Agent A, Agent B|}|}
          \\<in> set evs3;
*)
writeln "GIVE UP! on NA_Crypt_imp_Server_msg";


(*Thus the key property A_can_trust probably fails too.*)
