(*  Title:      HOL/Auth/Recur
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "recur" for the Recursive Authentication protocol.
*)

Pretty.setdepth 30;

AddEs spies_partsEs;
AddDs [impOfSubs analz_subset_parts];
AddDs [impOfSubs Fake_parts_insert];


(** Possibility properties: traces that reach the end 
        ONE theorem would be more elegant and faster!
        By induction on a list of agents (no repetitions)
**)


(*Simplest case: Alice goes directly to the server*)
Goal "EX K NA. EX evs: recur.                                           \
\  Says Server A {|Crypt (shrK A) {|Key K, Agent Server, Nonce NA|},   \
\                  END|}  : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (recur.Nil RS recur.RA1 RS (respond.One RSN (3,recur.RA3))) 2);
by possibility_tac;
result();


(*Case two: Alice, Bob and the server*)
Goal "EX K. EX NA. EX evs: recur.                               \
\       Says B A {|Crypt (shrK A) {|Key K, Agent B, Nonce NA|}, \
\                  END|}  : set evs";
by (cut_facts_tac [Nonce_supply2, Key_supply2] 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (recur.Nil RS recur.RA1 RS recur.RA2 RS 
          (respond.One RS respond.Cons RSN (3,recur.RA3)) RS
          recur.RA4) 2);
by basic_possibility_tac;
by (DEPTH_SOLVE (eresolve_tac [asm_rl, less_not_refl2, less_not_refl3] 1));
result();


(*Case three: Alice, Bob, Charlie and the server
  TOO SLOW to run every time!
Goal "EX K. EX NA. EX evs: recur.                                      \
\       Says B A {|Crypt (shrK A) {|Key K, Agent B, Nonce NA|},        \
\                  END|}  : set evs";
by (cut_facts_tac [Nonce_supply3, Key_supply3] 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (recur.Nil RS recur.RA1 RS recur.RA2 RS recur.RA2 RS 
          (respond.One RS respond.Cons RS respond.Cons RSN
           (3,recur.RA3)) RS recur.RA4 RS recur.RA4) 2);
(*SLOW: 33 seconds*)
by basic_possibility_tac;
by (DEPTH_SOLVE (swap_res_tac [refl, conjI, disjCI] 1 
		 ORELSE
		 eresolve_tac [asm_rl, less_not_refl2, less_not_refl3] 1));
result();
****************)

(**** Inductive proofs about recur ****)


Goal "(PA,RB,KAB) : respond evs ==> Key KAB : parts{RB}";
by (etac respond.induct 1);
by (ALLGOALS Simp_tac);
qed "respond_Key_in_parts";

Goal "(PA,RB,KAB) : respond evs ==> Key KAB ~: used evs";
by (etac respond.induct 1);
by (REPEAT (assume_tac 1));
qed "respond_imp_not_used";

Goal "[| Key K : parts {RB};  (PB,RB,K') : respond evs |] \
\     ==> Key K ~: used evs";
by (etac rev_mp 1);
by (etac respond.induct 1);
by (auto_tac(claset() addDs [Key_not_used, respond_imp_not_used],
             simpset()));
qed_spec_mp "Key_in_parts_respond";

(*Simple inductive reasoning about responses*)
Goal "(PA,RB,KAB) : respond evs ==> RB : responses evs";
by (etac respond.induct 1);
by (REPEAT (ares_tac (respond_imp_not_used::responses.intrs) 1));
qed "respond_imp_responses";


(** For reasoning about the encrypted portion of messages **)

val RA2_analz_spies = Says_imp_spies RS analz.Inj |> standard;

Goal "Says C' B {|Crypt K X, X', RA|} : set evs ==> RA : analz (spies evs)";
by (blast_tac (claset() addSDs [Says_imp_spies RS analz.Inj]) 1);
qed "RA4_analz_spies";

(*RA2_analz... and RA4_analz... let us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs: Fake does not invent new nonces (as in RA2), and of course Fake
  messages originate from the Spy. *)

bind_thm ("RA2_parts_spies",
          RA2_analz_spies RS (impOfSubs analz_subset_parts));
bind_thm ("RA4_parts_spies",
          RA4_analz_spies RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X ~: parts (spies evs).*)
fun parts_induct_tac i = 
  EVERY [etac recur.induct i,
	 ftac RA4_parts_spies (i+5),
	 ftac respond_imp_responses (i+4),
	 ftac RA2_parts_spies (i+3),
	 prove_simple_subgoals_tac i];


(** Theorems of the form X ~: parts (spies evs) imply that NOBODY
    sends messages containing X! **)


(** Spy never sees another agent's shared key! (unless it's bad at start) **)

Goal "evs : recur ==> (Key (shrK A) : parts (spies evs)) = (A : bad)";
by (parts_induct_tac 1);
by Auto_tac;
(*RA3*)
by (auto_tac (claset() addDs [Key_in_parts_respond],
	      simpset() addsimps [parts_insert_spies]));
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

Goal "evs : recur ==> (Key (shrK A) : analz (spies evs)) = (A : bad)";
by Auto_tac;
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

AddSDs [Spy_see_shrK RSN (2, rev_iffD1), 
	Spy_analz_shrK RSN (2, rev_iffD1)];


(** Nobody can have used non-existent keys! **)

(*The special case of H={} has the same proof*)
Goal "[| K : keysFor (parts (insert RB H));  RB : responses evs |] \
\     ==> K : range shrK | K : keysFor (parts H)";
by (etac rev_mp 1);
by (etac responses.induct 1);
by Auto_tac;
qed_spec_mp "Key_in_keysFor_parts";


Goal "evs : recur ==> Key K ~: used evs --> K ~: keysFor (parts (spies evs))";
by (parts_induct_tac 1);
(*RA3*)
by (blast_tac (claset() addSDs [Key_in_keysFor_parts]) 2);
(*Fake*)
by (blast_tac (claset() addSDs [keysFor_parts_insert]) 1);
qed_spec_mp "new_keys_not_used";


bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];



(*** Proofs involving analz ***)

(*For proofs involving analz.*)
val analz_spies_tac = 
    dtac RA2_analz_spies 4 THEN 
    ftac respond_imp_responses 5                THEN
    dtac RA4_analz_spies 6;


(** Session keys are not used to encrypt other session keys **)

(*Version for "responses" relation.  Handles case RA3 in the theorem below.  
  Note that it holds for *any* set H (not just "spies evs")
  satisfying the inductive hypothesis.*)
Goal "[| RB : responses evs;                             \
\        ALL K KK. KK <= - (range shrK) -->              \
\                  (Key K : analz (Key``KK Un H)) =      \
\                  (K : KK | Key K : analz H) |]         \
\    ==> ALL K KK. KK <= - (range shrK) -->              \
\                  (Key K : analz (insert RB (Key``KK Un H))) = \
\                  (K : KK | Key K : analz (insert RB H))";
by (etac responses.induct 1);
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
qed "resp_analz_image_freshK_lemma";

(*Version for the protocol.  Proof is almost trivial, thanks to the lemma.*)
Goal "evs : recur ==>                                 \
\  ALL K KK. KK <= - (range shrK) -->                 \
\         (Key K : analz (Key``KK Un (spies evs))) =  \
\         (K : KK | Key K : analz (spies evs))";
by (etac recur.induct 1);
by analz_spies_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma));
by (ALLGOALS 
    (asm_simp_tac
     (analz_image_freshK_ss addsimps [resp_analz_image_freshK_lemma])));
(*Fake*) 
by (spy_analz_tac 1);
val raw_analz_image_freshK = result();
qed_spec_mp "analz_image_freshK";


(*Instance of the lemma with H replaced by (spies evs):
   [| RB : responses evs;  evs : recur; |]
   ==> KK <= - (range shrK) --> 
       Key K : analz (insert RB (Key``KK Un spies evs)) =
       (K : KK | Key K : analz (insert RB (spies evs))) 
*)
bind_thm ("resp_analz_image_freshK",
          raw_analz_image_freshK RSN
            (2, resp_analz_image_freshK_lemma) RS spec RS spec RS mp);

Goal "[| evs : recur;  KAB ~: range shrK |] ==>           \
\     Key K : analz (insert (Key KAB) (spies evs)) =      \
\     (K = KAB | Key K : analz (spies evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*Everything that's hashed is already in past traffic. *)
Goal "[| Hash {|Key(shrK A), X|} : parts (spies evs);  \
\        evs : recur;  A ~: bad |] ==> X : parts (spies evs)";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*RA3 requires a further induction*)
by (etac responses.induct 2);
by (ALLGOALS Asm_simp_tac);
(*Fake*)
by (blast_tac (claset() addIs [parts_insertI]) 1);
qed "Hash_imp_body";


(** The Nonce NA uniquely identifies A's message. 
    This theorem applies to steps RA1 and RA2!

  Unicity is not used in other proofs but is desirable in its own right.
**)

Goal "[| evs : recur; A ~: bad |]                   \
\ ==> EX B' P'. ALL B P.                                     \
\     Hash {|Key(shrK A), Agent A, B, NA, P|} : parts (spies evs) \
\       -->  B=B' & P=P'";
by (parts_induct_tac 1);
by (Blast_tac 1);
by (etac responses.induct 3);
by (ALLGOALS (simp_tac (simpset() addsimps [all_conj_distrib]))); 
by (clarify_tac (claset() addSEs partsEs) 1);
(*RA1,2: creation of new Nonce.  Move assertion into global context*)
by (ALLGOALS (expand_case_tac "NA = ?y"));
by (REPEAT_FIRST (ares_tac [exI]));
by (REPEAT (blast_tac (claset() addSDs [Hash_imp_body]) 1));
val lemma = result();

Goalw [HPair_def]
 "[| Hash[Key(shrK A)] {|Agent A, B,NA,P|}   : parts (spies evs); \
\     Hash[Key(shrK A)] {|Agent A, B',NA,P'|} : parts (spies evs); \
\     evs : recur;  A ~: bad |]                                    \
\   ==> B=B' & P=P'";
by (REPEAT (eresolve_tac partsEs 1));
by (prove_unique_tac lemma 1);
qed "unique_NA";


(*** Lemmas concerning the Server's response
      (relations "respond" and "responses") 
***)

Goal "[| RB : responses evs;  evs : recur |] \
\ ==> (Key (shrK B) : analz (insert RB (spies evs))) = (B:bad)";
by (etac responses.induct 1);
by (ALLGOALS
    (asm_simp_tac 
     (analz_image_freshK_ss addsimps [Spy_analz_shrK,
                                      resp_analz_image_freshK])));
qed "shrK_in_analz_respond";
Addsimps [shrK_in_analz_respond];


Goal "[| RB : responses evs;                         \
\        ALL K KK. KK <= - (range shrK) -->          \
\                  (Key K : analz (Key``KK Un H)) =  \
\                  (K : KK | Key K : analz H) |]     \
\    ==> (Key K : analz (insert RB H)) -->           \
\        (Key K : parts{RB} | Key K : analz H)";
by (etac responses.induct 1);
by (ALLGOALS
    (asm_simp_tac 
     (analz_image_freshK_ss addsimps [resp_analz_image_freshK_lemma])));
(*Simplification using two distinct treatments of "image"*)
by (simp_tac (simpset() addsimps [parts_insert2]) 1);
by (blast_tac (claset() delrules [allE]) 1);
qed "resp_analz_insert_lemma";

bind_thm ("resp_analz_insert",
          raw_analz_image_freshK RSN
            (2, resp_analz_insert_lemma) RSN(2, rev_mp));


(*The last key returned by respond indeed appears in a certificate*)
Goal "(Hash[Key(shrK A)] {|Agent A, B, NA, P|}, RA, K) : respond evs \
\   ==> Crypt (shrK A) {|Key K, B, NA|} : parts {RA}";
by (etac respond.elim 1);
by (ALLGOALS Asm_full_simp_tac);
qed "respond_certificate";


Goal "(PB,RB,KXY) : respond evs                          \
\     ==> EX A' B'. ALL A B N.                                \
\         Crypt (shrK A) {|Key K, Agent B, N|} : parts {RB} \
\         -->   (A'=A & B'=B) | (A'=B & B'=A)";
by (etac respond.induct 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [all_conj_distrib]))); 
(*Base case*)
by (Blast_tac 1);
by Safe_tac;
by (expand_case_tac "K = KBC" 1);
by (dtac respond_Key_in_parts 1);
by (blast_tac (claset() addSIs [exI]
                        addDs [Key_in_parts_respond]) 1);
by (expand_case_tac "K = KAB" 1);
by (REPEAT (ares_tac [exI] 2));
by (ex_strip_tac 1);
by (dtac respond_certificate 1);
by (Blast_tac 1);
val lemma = result();

Goal "[| Crypt (shrK A) {|Key K, Agent B, N|} : parts {RB};      \
\        Crypt (shrK A') {|Key K, Agent B', N'|} : parts {RB};   \
\        (PB,RB,KXY) : respond evs |]                            \
\     ==> (A'=A & B'=B) | (A'=B & B'=A)";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg RA3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

Goal "[| (PB,RB,KAB) : respond evs;  evs : recur |]              \
\     ==> ALL A A' N. A ~: bad & A' ~: bad -->                   \
\         Crypt (shrK A) {|Key K, Agent A', N|} : parts{RB} -->  \
\         Key K ~: analz (insert RB (spies evs))";
by (etac respond.induct 1);
by (ftac respond_imp_responses 2);
by (ftac respond_imp_not_used 2);
by (ALLGOALS (*6 seconds*)
    (asm_simp_tac 
     (analz_image_freshK_ss 
        addsimps split_ifs
	addsimps 
          [shrK_in_analz_respond, resp_analz_image_freshK, parts_insert2])));
by (ALLGOALS (simp_tac (simpset() addsimps [ex_disj_distrib])));
(** LEVEL 5 **)
by (Blast_tac 1);
by (REPEAT_FIRST (resolve_tac [allI, conjI, impI]));
by (ALLGOALS Clarify_tac);
by (blast_tac (claset() addSDs  [resp_analz_insert]
 		        addIs  [impOfSubs analz_subset_parts]) 3);
by (blast_tac (claset() addSDs [respond_certificate]) 2);
by (Asm_full_simp_tac 1);
(*by unicity, either B=Aa or B=A', a contradiction if B: bad*)
by (blast_tac
    (claset() addSEs [MPair_parts]
	     addDs [parts.Body,
		    respond_certificate RSN (2, unique_session_keys)]) 1);
qed_spec_mp "respond_Spy_not_see_session_key";


Goal "[| Crypt (shrK A) {|Key K, Agent A', N|} : parts (spies evs); \
\        A ~: bad;  A' ~: bad;  evs : recur |]                      \
\     ==> Key K ~: analz (spies evs)";
by (etac rev_mp 1);
by (etac recur.induct 1);
by analz_spies_tac;
by (ALLGOALS
    (asm_simp_tac
     (simpset() addsimps split_ifs @ [analz_insert_eq, analz_insert_freshK])));
(*RA4*)
by (spy_analz_tac 5);
(*RA2*)
by (spy_analz_tac 3);
(*Fake*)
by (spy_analz_tac 2);
(*Base*)
by (Force_tac 1);
(*RA3 remains*)
by (simp_tac (simpset() addsimps [parts_insert_spies]) 1);
by (safe_tac (claset() delrules [impCE]));
(*RA3, case 2: K is an old key*)
by (blast_tac (claset() addSDs [resp_analz_insert]
                        addSEs partsEs
                        addDs  [Key_in_parts_respond]) 2);
(*RA3, case 1: use lemma previously proved by induction*)
by (blast_tac (claset() addSEs [respond_Spy_not_see_session_key RSN
			       (2,rev_notE)]) 1);
qed "Spy_not_see_session_key";

(**** Authenticity properties for Agents ****)

(*The response never contains Hashes*)
Goal "[| Hash {|Key (shrK B), M|} : parts (insert RB H); \
\        (PB,RB,K) : respond evs |]                      \
\     ==> Hash {|Key (shrK B), M|} : parts H";
by (etac rev_mp 1);
by (etac (respond_imp_responses RS responses.induct) 1);
by Auto_tac;
qed "Hash_in_parts_respond";

(*Only RA1 or RA2 can have caused such a part of a message to appear.
  This result is of no use to B, who cannot verify the Hash.  Moreover,
  it can say nothing about how recent A's message is.  It might later be
  used to prove B's presence to A at the run's conclusion.*)
Goalw [HPair_def]
 "[| Hash {|Key(shrK A), Agent A, Agent B, NA, P|} : parts(spies evs); \
\        A ~: bad;  evs : recur |]                      \
\  ==> Says A B (Hash[Key(shrK A)] {|Agent A, Agent B, NA, P|}) : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
(*RA3*)
by (blast_tac (claset() addSDs [Hash_in_parts_respond]) 1);
qed_spec_mp "Hash_auth_sender";

(** These two results subsume (for all agents) the guarantees proved
    separately for A and B in the Otway-Rees protocol.
**)


(*Certificates can only originate with the Server.*)
Goal "[| Crypt (shrK A) Y : parts (spies evs);    \
\        A ~: bad;  evs : recur |]                \
\     ==> EX C RC. Says Server C RC : set evs  &  \
\                  Crypt (shrK A) Y : parts {RC}";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
(*RA4*)
by (Blast_tac 4);
(*RA3*)
by (full_simp_tac (simpset() addsimps [parts_insert_spies]) 3
    THEN Blast_tac 3);
(*RA1*)
by (Blast_tac 1);
(*RA2: it cannot be a new Nonce, contradiction.*)
by (Blast_tac 1);
qed "Cert_imp_Server_msg";
