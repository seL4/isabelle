(*  Title:      HOL/Auth/Yahalom
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Yahalom protocol.

From page 257 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

open Yahalom;

proof_timing:=true;
HOL_quantifiers := false;
Pretty.setdepth 25;

val op addss = op unsafe_addss;


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX X NB K. EX evs: yahalom lost.          \
\               Says A B {|X, Crypt K (Nonce NB)|} : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (yahalom.Nil RS yahalom.YM1 RS yahalom.YM2 RS yahalom.YM3 RS 
          yahalom.YM4) 2);
by possibility_tac;
result();


(**** Inductive proofs about yahalom ****)

(*Monotonicity*)
goal thy "!!evs. lost' <= lost ==> yahalom lost' <= yahalom lost";
by (rtac subsetI 1);
by (etac yahalom.induct 1);
by (REPEAT_FIRST
    (best_tac (!claset addIs (impOfSubs (sees_mono RS analz_mono RS synth_mono)
                              :: yahalom.intrs))));
qed "yahalom_mono";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs: yahalom lost ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac yahalom.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

(*Lets us treat YM4 using a similar argument as for the Fake case.*)
goal thy "!!evs. Says S A {|Crypt (shrK A) Y, X|} : set_of_list evs ==> \
\                X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "YM4_analz_sees_Spy";

bind_thm ("YM4_parts_sees_Spy",
          YM4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*Relates to both YM4 and Oops*)
goal thy "!!evs. Says S A {|Crypt (shrK A) {|B, K, NA, NB|}, X|} \
\                  : set_of_list evs ==> \
\                K : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "YM4_Key_parts_sees_Spy";

(*We instantiate the variable to "lost".  Leaving it as a Var makes proofs
  harder: the simplifier does less.*)
val parts_Fake_tac = 
    forw_inst_tac [("lost","lost")] YM4_parts_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] YM4_Key_parts_sees_Spy 7;

(*For proving the easier theorems about X ~: parts (sees lost Spy evs) *)
fun parts_induct_tac i = SELECT_GOAL
    (DETERM (etac yahalom.induct 1 THEN parts_Fake_tac THEN
             (*Fake message*)
             TRY (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                                           impOfSubs Fake_parts_insert]
                                    addss (!simpset)) 2)) THEN
     (*Base case*)
     fast_tac (!claset addss (!simpset)) 1 THEN
     ALLGOALS Asm_simp_tac) i;


(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : yahalom lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Auto_tac());
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : yahalom lost \
\        ==> (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (sees lost Spy evs);       \
\                  evs : yahalom lost |] ==> A:lost";
by (fast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*Nobody can have used non-existent keys!*)
goal thy "!!evs. evs : yahalom lost ==>          \
\         Key K ~: used evs --> K ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
(*YM4: Key K is not fresh!*)
by (fast_tac (!claset addSEs sees_Spy_partsEs) 3);
(*YM3*)
by (fast_tac (!claset addss (!simpset)) 2);
(*Fake*)
by (best_tac
      (!claset addIs [impOfSubs analz_subset_parts]
               addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono)]
               addss (!simpset)) 1);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(*Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.*)
goal thy 
 "!!evs. [| Says Server A {|Crypt (shrK A) {|Agent B, Key K, NA, NB|}, X|} \
\             : set_of_list evs;                                           \
\           evs : yahalom lost |]                                          \
\        ==> K ~: range shrK";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
    forw_inst_tac [("lost","lost")] YM4_analz_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Says_Server_message_form 7 THEN
    assume_tac 7 THEN REPEAT ((etac exE ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

  Key K : analz (insert (Key KAB) (sees lost Spy evs)) ==>
  Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.
****)

(** Session keys are not used to encrypt other session keys **)

goal thy  
 "!!evs. evs : yahalom lost ==> \
\  ALL K KK. KK <= Compl (range shrK) -->                      \
\            (Key K : analz (Key``KK Un (sees lost Spy evs))) = \
\            (K : KK | Key K : analz (sees lost Spy evs))";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma ));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Base*)
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
(*YM4, Fake*) 
by (REPEAT (spy_analz_tac 1));
qed_spec_mp "analz_image_freshK";

goal thy
 "!!evs. [| evs : yahalom lost;  KAB ~: range shrK |] ==>             \
\        Key K : analz (insert (Key KAB) (sees lost Spy evs)) = \
\        (K = KAB | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : yahalom lost ==>                                     \
\      EX A' B' NA' NB' X'. ALL A B NA NB X.                             \
\          Says Server A                                            \
\           {|Crypt (shrK A) {|Agent B, Key K, NA, NB|}, X|}        \
\          : set_of_list evs --> A=A' & B=B' & NA=NA' & NB=NB' & X=X'";
by (etac yahalom.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
by (ex_strip_tac 2);
by (Fast_tac 2);
(*Remaining case: YM3*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message and handle this case by contradiction*)
by (fast_tac (!claset addSEs sees_Spy_partsEs
                      delrules [conjI]    (*prevent split-up into 4 subgoals*)
                      addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();

goal thy 
"!!evs. [| Says Server A                                            \
\           {|Crypt (shrK A) {|Agent B, Key K, NA, NB|}, X|}        \
\           : set_of_list evs;                                      \
\          Says Server A'                                           \
\           {|Crypt (shrK A') {|Agent B', Key K, NA', NB'|}, X'|}   \
\           : set_of_list evs;                                      \
\          evs : yahalom lost |]                                    \
\       ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(*If the encrypted message appears then it originated with the Server*)
goal thy
 "!!evs. [| Crypt (shrK A) {|Agent B, Key K, NA, NB|}                  \
\            : parts (sees lost Spy evs);                              \
\           A ~: lost;  evs : yahalom lost |]                          \
\         ==> Says Server A                                            \
\              {|Crypt (shrK A) {|Agent B, Key K, NA, NB|},            \
\                Crypt (shrK B) {|Agent A, Key K|}|}                   \
\             : set_of_list evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
qed "A_trusts_YM3";


(** Crucial secrecy property: Spy does not see the keys sent in msg YM3 **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> Says Server A                                        \
\              {|Crypt (shrK A) {|Agent B, Key K, NA, NB|},       \
\                Crypt (shrK B) {|Agent A, Key K|}|}              \
\             : set_of_list evs -->                               \
\            Says A Spy {|NA, NB, Key K|} ~: set_of_list evs -->  \
\            Key K ~: analz (sees lost Spy evs)";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps [not_parts_not_analz, analz_insert_freshK]
               setloop split_tac [expand_if])));
(*YM3*)
by (fast_tac (!claset delrules [impCE]
                      addSEs sees_Spy_partsEs
                      addIs [impOfSubs analz_subset_parts]
                      addss (!simpset addsimps [parts_insert2])) 2);
(*OR4, Fake*) 
by (REPEAT_FIRST spy_analz_tac);
(*Oops*)
by (fast_tac (!claset delrules [disjE] 
                      addDs [unique_session_keys]
                      addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version: Server's message in the most abstract form*)
goal thy 
 "!!evs. [| Says Server A                                         \
\              {|Crypt (shrK A) {|Agent B, Key K, NA, NB|},       \
\                Crypt (shrK B) {|Agent A, Key K|}|}              \
\             : set_of_list evs;                                  \
\           Says A Spy {|NA, NB, Key K|} ~: set_of_list evs;      \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> Key K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                    \
\           Says Server A                                         \
\              {|Crypt (shrK A) {|Agent B, Key K, NA, NB|},       \
\                Crypt (shrK B) {|Agent A, Key K|}|}              \
\             : set_of_list evs;                                  \
\           Says A Spy {|NA, NB, Key K|} ~: set_of_list evs;      \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> Key K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [yahalom_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(*** Security Guarantee for B upon receiving YM4 ***)

(*B knows, by the first part of A's message, that the Server distributed 
  the key for A and B.  But this part says nothing about nonces.*)
goal thy 
 "!!evs. [| Crypt (shrK B) {|Agent A, Key K|} : parts (sees lost Spy evs); \
\           B ~: lost;  evs : yahalom lost |]                           \
\        ==> EX NA NB. Says Server A                                    \
\                        {|Crypt (shrK A) {|Agent B, Key K,             \
\                                           Nonce NA, Nonce NB|},       \
\                          Crypt (shrK B) {|Agent A, Key K|}|}          \
\                       : set_of_list evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*YM3*)
by (Fast_tac 1);
qed "B_trusts_YM4_shrK";


(** The Nonce NB uniquely identifies B's message. **)

goal thy 
 "!!evs. evs : yahalom lost ==> \
\   EX NA' A' B'. ALL NA A B. \
\      Crypt (shrK B) {|Agent A, Nonce NA, NB|} : parts(sees lost Spy evs) \
\      --> B ~: lost --> NA = NA' & A = A' & B = B'";
by (etac yahalom.induct 1 THEN parts_Fake_tac);
(*Fake: the tactic in parts_induct_tac works, but takes 4 times longer*)
by (REPEAT (etac exE 2) THEN 
    best_tac (!claset addSIs [exI]
                      addDs [impOfSubs Fake_parts_insert]
                      addss (!simpset)) 2);
(*Base case*)
by (fast_tac (!claset addss (!simpset)) 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib]))); 
(*YM2: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NB = ?y" 1);
by (REPEAT (resolve_tac [exI, conjI, impI, refl] 1));
by (fast_tac (!claset addSEs sees_Spy_partsEs) 1);
val lemma = result();

goal thy 
 "!!evs.[| Crypt (shrK B) {|Agent A, Nonce NA, NB|} \
\                  : parts (sees lost Spy evs);         \
\          Crypt (shrK B') {|Agent A', Nonce NA', NB|} \
\                  : parts (sees lost Spy evs);         \
\          evs : yahalom lost;  B ~: lost;  B' ~: lost |]  \
\        ==> NA' = NA & A' = A & B' = B";
by (prove_unique_tac lemma 1);
qed "unique_NB";

fun lost_tac s =
    case_tac ("(" ^ s ^ ") : lost") THEN'
    SELECT_GOAL 
      (REPEAT_DETERM (dtac (Says_imp_sees_Spy RS analz.Inj) 1) THEN
       REPEAT_DETERM (etac MPair_analz 1) THEN
       THEN_BEST_FIRST 
         (dres_inst_tac [("A", s)] Crypt_Spy_analz_lost 1 THEN assume_tac 1)
         (has_fewer_prems 1, size_of_thm)
         (Step_tac 1));


(*Variant useful for proving secrecy of NB*)
goal thy 
 "!!evs.[| Says C D   {|X,  Crypt (shrK B) {|Agent A, Nonce NA, NB|}|} \
\          : set_of_list evs;  B ~: lost;         \
\          Says C' D' {|X', Crypt (shrK B') {|Agent A', Nonce NA', NB|}|} \
\          : set_of_list evs;                           \
\          NB ~: analz (sees lost Spy evs);             \
\          evs : yahalom lost |]  \
\        ==> NA' = NA & A' = A & B' = B";
by (lost_tac "B'" 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addSEs [MPair_parts]
                      addDs  [unique_NB]) 1);
qed "Says_unique_NB";

goal thy 
 "!!evs. [| B ~: lost;  evs : yahalom lost  |]               \
\ ==>  Nonce NB ~: analz (sees lost Spy evs) -->  \
\      Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|} : parts (sees lost Spy evs) \
\ --> Crypt (shrK B') {|Agent A', Nonce NB, NB'|} ~: parts (sees lost Spy evs)";
by (etac yahalom.induct 1);
by parts_Fake_tac;
by (REPEAT_FIRST 
    (rtac impI THEN' 
     dtac (sees_subset_sees_Says RS analz_mono RS contra_subsetD) THEN'
     mp_tac));
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                             impOfSubs Fake_parts_insert]
                      addss (!simpset)) 2);
by (ALLGOALS Asm_simp_tac);
by (fast_tac (!claset addss (!simpset)) 1);
by (fast_tac (!claset addDs [Says_imp_sees_Spy RS analz.Inj]
                      addSIs [parts_insertI]
                      addSEs partsEs
                      addss (!simpset)) 1);
val no_nonce_YM1_YM2 = standard (result() RS mp RSN (2, rev_mp) RS notE);



(**** Towards proving secrecy of Nonce NB ****)

(*B knows, by the second part of A's message, that the Server distributed 
  the key quoting nonce NB.  This part says nothing about agent names. 
  Secrecy of NB is crucial.*)
goal thy 
 "!!evs. evs : yahalom lost                                             \
\        ==> Nonce NB ~: analz (sees lost Spy evs) -->                  \
\            Crypt K (Nonce NB) : parts (sees lost Spy evs) -->         \
\            (EX A B NA. Says Server A                                  \
\                        {|Crypt (shrK A) {|Agent B, Key K,             \
\                                  Nonce NA, Nonce NB|},                \
\                          Crypt (shrK B) {|Agent A, Key K|}|}          \
\                       : set_of_list evs)";
by (etac yahalom.induct 1);
by parts_Fake_tac;
by (fast_tac (!claset addss (!simpset)) 1);
by (REPEAT_FIRST
    (rtac impI THEN'
     dtac (sees_subset_sees_Says RS analz_mono RS contra_subsetD)));
by (ALLGOALS Asm_simp_tac);
(*Fake, YM3, YM4*)
by (Fast_tac 2);
by (fast_tac (!claset addSDs [impOfSubs Fake_parts_insert]
                      addDs [impOfSubs analz_subset_parts]
                      addss (!simpset)) 1);
(*YM4*)
by (Step_tac 1);
by (lost_tac "A" 1);
by (fast_tac (!claset addDs [Says_imp_sees_Spy RS parts.Inj RS parts.Fst RS
                             A_trusts_YM3]) 1);
val B_trusts_YM4_newK = result() RS mp RSN (2, rev_mp);


(*This is the original version of the result above.  But it is of little
  value because it assumes secrecy of K, which we cannot be assured of
  until we know that K is fresh -- which we do not know at the point this
  result is applied.*)
goal thy 
 "!!evs. evs : yahalom lost                                             \
\        ==> Key K ~: analz (sees lost Spy evs) -->                     \
\            Crypt K (Nonce NB) : parts (sees lost Spy evs) -->         \
\            (EX A B NA. Says Server A                                  \
\                        {|Crypt (shrK A) {|Agent B, Key K,                      \
\                                  Nonce NA, Nonce NB|},       \
\                          Crypt (shrK B) {|Agent A, Key K|}|}          \
\                       : set_of_list evs)";
by (etac yahalom.induct 1);
by parts_Fake_tac;
by (fast_tac (!claset addss (!simpset)) 1);
by (TRYALL (rtac impI));
by (REPEAT_FIRST
    (dtac (sees_subset_sees_Says RS analz_mono RS contra_subsetD)));
by (ALLGOALS Asm_simp_tac);
(*Fake, YM3, YM4*)
by (fast_tac (!claset addSDs [Crypt_Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts]) 1);
by (Fast_tac 1);
(*YM4*)
by (Step_tac 1);
by (lost_tac "A" 1);
by (fast_tac (!claset addDs [Says_imp_sees_Spy RS parts.Inj RS parts.Fst RS
                             A_trusts_YM3]) 1);
result() RS mp RSN (2, rev_mp);


(*YM3 can only be triggered by YM2*)
goal thy 
 "!!evs. [| Says Server A                                           \
\            {|Crypt (shrK A) {|Agent B, k, na, nb|}, X|} : set_of_list evs; \
\           evs : yahalom lost |]                                        \
\        ==> EX B'. Says B' Server                                       \
\                      {| Agent B, Crypt (shrK B) {|Agent A, na, nb|} |} \
\                   : set_of_list evs";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Fast_tac);
qed "Says_Server_imp_YM2";


(** Dedicated tactics for the nonce secrecy proofs **)

val no_nonce_tac = SELECT_GOAL
   (REPEAT (resolve_tac [impI, notI] 1) THEN
    REPEAT (hyp_subst_tac 1) THEN
    etac (Says_imp_sees_Spy RS parts.Inj RS parts.Snd RS no_nonce_YM1_YM2) 1
    THEN
    etac (Says_imp_sees_Spy RS parts.Inj RS parts.Snd) 4
    THEN 
    REPEAT_FIRST assume_tac);

val not_analz_insert = subset_insertI RS analz_mono RS contra_subsetD;


(*The only nonces that can be found with the help of session keys are
  those distributed as nonce NB by the Server.  The form of the theorem
  recalls analz_image_freshK, but it is much more complicated.*)

(*As with analz_image_freshK, we take some pains to express the property
  as a logical equivalence so that the simplifier can apply it.*)
goal thy  
 "!!evs. P --> (X : analz (G Un H)) --> (X : analz H)  ==> \
\        P --> (X : analz (G Un H)) = (X : analz H)";
by (fast_tac (!claset addSEs [impOfSubs analz_mono]) 1);
qed "Nonce_secrecy_lemma";

goal thy 
 "!!evs. evs : yahalom lost ==>                                          \
\        (ALL KK. KK <= Compl (range shrK) -->                               \
\             (ALL K: KK. ALL A B na X.                                       \
\                 Says Server A                                              \
\                     {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB|}, X|} \
\                 ~: set_of_list evs)   -->  \
\             (Nonce NB : analz (Key``KK Un (sees lost Spy evs))) =      \
\             (Nonce NB : analz (sees lost Spy evs)))";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (resolve_tac [impI RS allI]));
by (REPEAT_FIRST (rtac Nonce_secrecy_lemma ));
by (rtac ccontr 7);
by (subgoal_tac "ALL A B na X.                                       \
\                 Says Server A                                              \
\                     {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB|}, X|} \
\                 ~: set_of_list evsa" 7);
by (eres_inst_tac [("P","?PP-->?QQ")] notE 7);
by (subgoal_tac "ALL A B na X.                                       \
\                 Says Server A                                              \
\                    {|Crypt (shrK A) {|Agent B, Key KAB, na, Nonce NB|}, X|} \
\                 ~: set_of_list evsa" 5);
by (ALLGOALS  (*22 seconds*)
    (asm_simp_tac 
     (analz_image_freshK_ss  addsimps
             ([all_conj_distrib, 
               not_parts_not_analz, analz_image_freshK]
              @ pushes @ ball_simps))));
(*Base*)
by (fast_tac (!claset addss (!simpset)) 1);
(*Fake*) (** LEVEL 10 **)
by (spy_analz_tac 1);
(*YM3*)
by (fast_tac (!claset addSEs sees_Spy_partsEs) 1);
(*Oops*)
(*20 secs*)
by (fast_tac (!claset delrules [ballE] addDs [unique_session_keys]
                      addss (!simpset)) 2);
(*YM4*)
(** LEVEL 13 **)
by (REPEAT (resolve_tac [impI, allI] 1));
by (dtac (impOfSubs Fake_analz_insert) 1 THEN etac synth.Inj 1);
by (stac insert_commute 1);
by (eres_inst_tac [("P","Nonce NB : ?HH")] rev_mp 1);
by (asm_simp_tac (analz_image_freshK_ss 
                  addsimps [analz_insertI, analz_image_freshK]) 1);
by (step_tac (!claset addSDs [not_analz_insert]) 1);
by (lost_tac "A" 1);
(** LEVEL 20 **)
by (dtac (Says_imp_sees_Spy RS parts.Inj RS parts.Fst RS A_trusts_YM3) 1
    THEN REPEAT (assume_tac 1));
by (thin_tac "All ?PP" 1);
by (Fast_tac 1);
qed_spec_mp "Nonce_secrecy";


(*Version required below: if NB can be decrypted using a session key then it
  was distributed with that key.  The more general form above is required
  for the induction to carry through.*)
goal thy 
 "!!evs. [| Says Server A                                              \
\            {|Crypt (shrK A) {|Agent B, Key KAB, na, Nonce NB'|}, X|} \
\           : set_of_list evs;                                         \
\           Nonce NB : analz (insert (Key KAB) (sees lost Spy evs));   \
\           Nonce NB ~: analz (sees lost Spy evs);                     \
\           KAB ~: range shrK;  evs : yahalom lost |]                  \
\        ==>  NB = NB'";
by (rtac ccontr 1);
by (subgoal_tac "ALL A B na X.                                       \
\                 Says Server A                                              \
\                    {|Crypt (shrK A) {|Agent B, Key KAB, na, Nonce NB|}, X|} \
\                 ~: set_of_list evs" 1);
by (eres_inst_tac [("P","Nonce NB : ?HH")] rev_mp 1);
by (asm_simp_tac (analz_image_freshK_ss 
                  addsimps ([Nonce_secrecy] @ ball_simps)) 1);
by (auto_tac (!claset addDs [unique_session_keys], (!simpset)));
qed "single_Nonce_secrecy";


goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  Spy: lost;  evs : yahalom lost |]  \
\ ==> Says B Server                                                    \
\          {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|} \
\     : set_of_list evs -->                               \
\     (ALL k. Says A Spy {|Nonce NA, Nonce NB, k|} ~: set_of_list evs) -->  \
\     Nonce NB ~: analz (sees lost Spy evs)";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps ([not_parts_not_analz,
                          analz_insert_freshK] @ pushes)
               setloop split_tac [expand_if])));
by (fast_tac (!claset addSIs [parts_insertI]
                      addSEs sees_Spy_partsEs
                      addss (!simpset)) 2);
(*Proof of YM2*) (** LEVEL 4 **)
by (deepen_tac (!claset addDs [Says_imp_sees_Spy RS analz.Inj,
                               impOfSubs analz_subset_parts]
                        addSEs partsEs) 3 2);
(*Prove YM3 by showing that no NB can also be an NA*)
by (REPEAT (Safe_step_tac 2 ORELSE no_nonce_tac 2));
by (deepen_tac (!claset addDs [Says_unique_NB]) 1 2);
(*Fake*)
by (spy_analz_tac 1);
(*YM4*) (** LEVEL 8 **)
by (res_inst_tac [("x1","X")] (insert_commute RS ssubst) 1);
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
(*43 secs??*)
by (SELECT_GOAL (REPEAT_FIRST (spy_analz_tac ORELSE' Safe_step_tac)) 1);
by (lost_tac "Aa" 1);
by (dtac (Says_imp_sees_Spy RS parts.Inj RS parts.Fst RS A_trusts_YM3) 1);
by (forward_tac [Says_Server_message_form] 3);
by (forward_tac [Says_Server_imp_YM2] 4);
(** LEVEL 15 **)
by (REPEAT_FIRST ((eresolve_tac [asm_rl, bexE, exE, disjE])));
by (lost_tac "Ba" 1);
by (dtac (Says_imp_sees_Spy RS parts.Inj RS parts.Snd RS unique_NB) 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addSEs [MPair_parts]) 1);
by (REPEAT (assume_tac 1 ORELSE Safe_step_tac 1)); 
(** LEVEL 20 **)
by (dtac Spy_not_see_encrypted_key 1);
by (REPEAT (assume_tac 1 ORELSE Fast_tac 1)); 
by (spy_analz_tac 1);
(*Oops case*) (** LEVEL 23 **)
by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 1);
by (step_tac (!claset delrules [disjE, conjI]) 1);
by (forward_tac [Says_Server_imp_YM2] 1 THEN assume_tac 1 THEN etac exE 1);
by (expand_case_tac "NB = NBa" 1);
by (deepen_tac (!claset addDs [Says_unique_NB]) 1 1);
by (rtac conjI 1);
by (no_nonce_tac 1);
(** LEVEL 30 **)
by (thin_tac "?PP|?QQ" 1);  (*subsumption!*)
by (fast_tac (!claset addSDs [single_Nonce_secrecy]) 1);
val Spy_not_see_NB = result() RSN(2,rev_mp) RSN(2,rev_mp) |> standard;


(*What can B deduce from receipt of YM4?  Note how the two components of
  the message contribute to a single conclusion about the Server's message.
  It's annoying that the "Says A Spy" assumption must quantify over 
  ALL POSSIBLE keys instead of our particular K (though at least the
  nonces are forced to agree with NA and NB). *)
goal thy 
 "!!evs. [| Says B Server                                               \
\            {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}  \
\           : set_of_list evs;       \
\           Says A' B {|Crypt (shrK B) {|Agent A, Key K|},              \
\                       Crypt K (Nonce NB)|} : set_of_list evs;         \
\           ALL k. Says A Spy {|Nonce NA, Nonce NB, k|} ~: set_of_list evs; \
\           A ~: lost;  B ~: lost;  Spy: lost;  evs : yahalom lost |]   \
\         ==> Says Server A                                             \
\                     {|Crypt (shrK A) {|Agent B, Key K,                \
\                               Nonce NA, Nonce NB|},                   \
\                       Crypt (shrK B) {|Agent A, Key K|}|}             \
\                   : set_of_list evs";
by (forward_tac [Spy_not_see_NB] 1 THEN REPEAT (assume_tac 1));
by (etac (Says_imp_sees_Spy RS parts.Inj RS MPair_parts) 1 THEN
    dtac B_trusts_YM4_shrK 1);
by (dtac B_trusts_YM4_newK 3);
by (REPEAT_FIRST (eresolve_tac [asm_rl, exE]));
by (forward_tac [Says_Server_imp_YM2] 1 THEN assume_tac 1);
by (dtac unique_session_keys 1 THEN REPEAT (assume_tac 1));
by (deepen_tac (!claset addDs [Says_unique_NB] addss (!simpset)) 0 1);
qed "B_trusts_YM4";
