(*  Title:      HOL/Auth/Recur
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "recur" for the Recursive Authentication protocol.
*)

open Recur;

proof_timing:=true;
HOL_quantifiers := false;
Pretty.setdepth 25;


(** Possibility properties: traces that reach the end 
	ONE theorem would be more elegant and faster!
	By induction on a list of agents (no repetitions)
**)

(*Simplest case: Alice goes directly to the server*)
goal thy
 "!!A. A ~= Server   \
\ ==> EX K NA. EX evs: recur lost.          \
\     Says Server A {|Agent A,              \
\                     Crypt (shrK A) {|Key K, Agent Server, Nonce NA|}, \
\                       Agent Server|}      \
\         : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (recur.Nil RS recur.RA1 RS 
	  (respond.One RSN (4,recur.RA3))) 2);
by (REPEAT
    (ALLGOALS (asm_simp_tac (!simpset setsolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' resolve_tac [refl, conjI])));
result();


(*Case two: Alice, Bob and the server*)
goal thy
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\ ==> EX K. EX NA. EX evs: recur lost.          \
\       Says B A {|Agent A, Crypt (shrK A) {|Key K, Agent B, Nonce NA|}, \
\                       Agent Server|}                          \
\         : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (recur.Nil RS recur.RA1 RS recur.RA2 RS 
	  (respond.One RS respond.Cons RSN (4,recur.RA3)) RS
	  recur.RA4) 2);
bw HPair_def;
by (REPEAT
    (REPEAT_FIRST (eq_assume_tac ORELSE' resolve_tac [refl, conjI])
     THEN
     ALLGOALS (asm_simp_tac (!simpset setsolver safe_solver))));
result();


(*Case three: Alice, Bob, Charlie and the server*)
goal thy
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\ ==> EX K. EX NA. EX evs: recur lost.          \
\       Says B A {|Agent A, Crypt (shrK A) {|Key K, Agent B, Nonce NA|}, \
\                       Agent Server|}                          \
\         : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (recur.Nil RS recur.RA1 RS recur.RA2 RS recur.RA2 RS 
	  (respond.One RS respond.Cons RS respond.Cons RSN
	   (4,recur.RA3)) RS recur.RA4 RS recur.RA4) 2);
bw HPair_def;
by (REPEAT	(*SLOW: 37 seconds*)
    (REPEAT_FIRST (eq_assume_tac ORELSE' resolve_tac [refl, conjI])
     THEN
     ALLGOALS (asm_simp_tac (!simpset setsolver safe_solver))));
by (ALLGOALS 
    (SELECT_GOAL (DEPTH_SOLVE
		  (swap_res_tac [refl, conjI, disjI1, disjI2] 1 APPEND 
		   etac not_sym 1))));
result();



(**** Inductive proofs about recur ****)

(*Monotonicity*)
goal thy "!!evs. lost' <= lost ==> recur lost' <= recur lost";
by (rtac subsetI 1);
by (etac recur.induct 1);
by (REPEAT_FIRST
    (best_tac (!claset addIs (impOfSubs (sees_mono RS analz_mono RS synth_mono)
                              :: recur.intrs))));
qed "recur_mono";

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : recur lost ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac recur.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(*Simple inductive reasoning about responses*)
goal thy "!!j. (j,PA,RB) : respond i ==> RB : responses i";
by (etac respond.induct 1);
by (REPEAT (ares_tac responses.intrs 1));
qed "respond_imp_responses";


(** For reasoning about the encrypted portion of messages **)

val RA2_analz_sees_Spy = Says_imp_sees_Spy RS analz.Inj |> standard;

goal thy "!!evs. Says C' B {|Agent B, X, Agent B, X', RA|} : set_of_list evs \
\                ==> RA : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "RA4_analz_sees_Spy";

(*RA2_analz... and RA4_analz... let us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs: Fake does not invent new nonces (as in RA2), and of course Fake
  messages originate from the Spy. *)

bind_thm ("RA2_parts_sees_Spy",
          RA2_analz_sees_Spy RS (impOfSubs analz_subset_parts));
bind_thm ("RA4_parts_sees_Spy",
          RA4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*We instantiate the variable to "lost".  Leaving it as a Var makes proofs
  harder to complete, since simplification does less for us.*)
val parts_Fake_tac = 
    let val tac = forw_inst_tac [("lost","lost")] 
    in  tac RA2_parts_sees_Spy 4              THEN
	forward_tac [respond_imp_responses] 5 THEN
	tac RA4_parts_sees_Spy 6
    end;

(*For proving the easier theorems about X ~: parts (sees lost Spy evs) *)
fun parts_induct_tac i = SELECT_GOAL
    (DETERM (etac recur.induct 1 THEN parts_Fake_tac THEN
             (*Fake message*)
             TRY (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                                           impOfSubs Fake_parts_insert]
                                    addss (!simpset)) 2)) THEN
     (*Base case*)
     fast_tac (!claset addss (!simpset)) 1 THEN
     ALLGOALS Asm_simp_tac) i;

(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)


(** Spy never sees another agent's long-term key (unless initially lost) **)

goal thy 
 "!!evs. (j,PB,RB) : respond i \
\  ==> Key K : parts {RB} --> (EX j'. K = newK2(i,j') & j<=j')";
be respond.induct 1;
by (Auto_tac());
by (best_tac (!claset addDs [Suc_leD]) 1);
qed_spec_mp "Key_in_parts_respond";

goal thy 
 "!!evs. evs : recur lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
(*RA2*)
by (best_tac (!claset addSEs partsEs addSDs [parts_cut]
                      addss (!simpset)) 1);
(*RA3*)
by (fast_tac (!claset addDs [Key_in_parts_respond]
                      addss (!simpset addsimps [parts_insert_sees])) 1);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : recur lost \
\        ==> (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (sees lost Spy evs);       \
\                  evs : recur lost |] ==> A:lost";
by (fast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future. *)
goal thy "!!evs. evs : recur lost ==> \
\                length evs <= i -->   \
\                Key (newK2(i,j)) ~: parts (sees lost Spy evs)";
by (parts_induct_tac 1);
(*RA2*)
by (best_tac (!claset addSEs partsEs 
	              addSDs [parts_cut]
                      addDs  [Suc_leD]
                      addss  (!simpset addsimps [parts_insert2])) 3);
(*Fake*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
			     impOfSubs parts_insert_subset_Un,
			     Suc_leD]
		      addss (!simpset)) 1);
(*For RA3*)
by (asm_simp_tac (!simpset addsimps [parts_insert_sees]) 2);
(*RA1-RA4*)
by (REPEAT (best_tac (!claset addDs [Key_in_parts_respond, Suc_leD]
		              addss (!simpset)) 1));
qed_spec_mp "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;     \
\           Key (newK2(i,j)) : parts {X};     \
\           evs : recur lost                 \
\        |] ==> i < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*** Future nonces can't be seen or used! ***)

goal thy 
 "!!evs. (j, PB, RB) : respond i \
\        ==> Nonce N : parts {RB} --> Nonce N : parts {PB}";
be respond.induct 1;
by (Auto_tac());
qed_spec_mp "Nonce_in_parts_respond";


goal thy "!!i. evs : recur lost ==> \
\              length evs <= i --> Nonce(newN i) ~: parts (sees lost Spy evs)";
by (parts_induct_tac 1);
(*For RA3*)
by (asm_simp_tac (!simpset addsimps [parts_insert_sees]) 4);
by (deepen_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]
                        addDs  [Nonce_in_parts_respond, parts_cut, Suc_leD]
			addss (!simpset)) 0 4);
(*Fake*)
by (fast_tac (!claset addDs  [impOfSubs analz_subset_parts,
			      impOfSubs parts_insert_subset_Un,
			      Suc_leD]
		      addss (!simpset)) 1);
(*RA1, RA2, RA4*)
by (REPEAT_FIRST  (fast_tac (!claset 
                              addSEs partsEs
                              addEs [leD RS notE]
                              addDs [Suc_leD]
                              addss (!simpset))));
qed_spec_mp "new_nonces_not_seen";
Addsimps [new_nonces_not_seen];

(*Variant: old messages must contain old nonces!*)
goal thy "!!evs. [| Says A B X : set_of_list evs;    \
\                   Nonce (newN i) : parts {X};      \
\                   evs : recur lost                 \
\                |] ==> i < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_nonces_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_nonces";


(** Nobody can have USED keys that will be generated in the future. **)

goal thy
 "!!evs. (j,PB,RB) : respond i \
\        ==> K : keysFor (parts {RB}) --> (EX A. K = shrK A)";
be (respond_imp_responses RS responses.induct) 1;
by (Auto_tac());
qed_spec_mp "Key_in_keysFor_parts_respond";


goal thy "!!i. evs : recur lost ==>          \
\       length evs <= i --> newK2(i,j) ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
(*RA3*)
by (fast_tac (!claset addDs  [Key_in_keysFor_parts_respond, Suc_leD]
		      addss  (!simpset addsimps [parts_insert_sees])) 4);
(*RA2*)
by (fast_tac (!claset addSEs partsEs 
	              addDs  [Suc_leD] addss (!simpset)) 3);
(*Fake, RA1, RA4*)
by (REPEAT 
    (best_tac
      (!claset addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono),
                      Suc_leD]
               addEs [new_keys_not_seen RS not_parts_not_analz RSN(2,rev_notE)]
               addss (!simpset)) 1));
qed_spec_mp "new_keys_not_used";


bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];



(*** Proofs involving analz ***)

(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
    dres_inst_tac [("lost","lost")] RA2_analz_sees_Spy 4 THEN 
    forward_tac [respond_imp_responses] 5                THEN
    dres_inst_tac [("lost","lost")] RA4_analz_sees_Spy 6;


Delsimps [image_insert];

(** Session keys are not used to encrypt other session keys **)

(*Version for "responses" relation.  Handles case RA3 in the theorem below.  
  Note that it holds for *any* set H (not just "sees lost Spy evs")
  satisfying the inductive hypothesis.*)
goal thy  
 "!!evs. [| RB : responses i;                             \
\           ALL K I. (Key K : analz (Key``(newK``I) Un H)) = \
\           (K : newK``I | Key K : analz H) |]                \
\       ==> ALL K I. (Key K : analz (insert RB (Key``(newK``I) Un H))) = \
\           (K : newK``I | Key K : analz (insert RB H))";
be responses.induct 1;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps [insert_Key_singleton, insert_Key_image, 
			 Un_assoc RS sym, pushKey_newK]
               setloop split_tac [expand_if])));
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
qed "resp_analz_image_newK_lemma";

(*Version for the protocol.  Proof is almost trivial, thanks to the lemma.*)
goal thy  
 "!!evs. evs : recur lost ==>                                            \
\  ALL K I. (Key K : analz (Key``(newK``I) Un (sees lost Spy evs))) = \
\           (K : newK``I | Key K : analz (sees lost Spy evs))";
by (etac recur.induct 1);
be subst 4;	(*RA2: DELETE needless definition of PA!*)
by analz_Fake_tac;
by (REPEAT_FIRST (ares_tac [allI, analz_image_newK_lemma]));
by (ALLGOALS (asm_simp_tac (!simpset addsimps [resp_analz_image_newK_lemma])));
(*Base*)
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
(*RA4, RA2, Fake*) 
by (REPEAT (spy_analz_tac 1));
val raw_analz_image_newK = result();
qed_spec_mp "analz_image_newK";


(*Instance of the lemma with H replaced by (sees lost Spy evs):
   [| RB : responses i;  evs : recur lost |]
   ==> Key xa : analz (insert RB (Key``newK``x Un sees lost Spy evs)) =
       (xa : newK``x | Key xa : analz (insert RB (sees lost Spy evs))) 
*)
bind_thm ("resp_analz_image_newK",
	  raw_analz_image_newK RSN
	    (2, resp_analz_image_newK_lemma) RS spec RS spec);

goal thy
 "!!evs. evs : recur lost ==>                               \
\        Key K : analz (insert (Key (newK x)) (sees lost Spy evs)) = \
\        (K = newK x | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
                                   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(** Nonces cannot appear before their time, even hashed!
    One is tempted to add the rule
	"Hash X : parts H ==> X : parts H"
    but we'd then lose theorems like Spy_see_shrK
***)

goal thy "!!i. evs : recur lost ==>              \
\                length evs <= i -->             \
\                (Nonce (newN i) : parts {X} --> \
\                 Hash X ~: parts (sees lost Spy evs))";
be recur.induct 1;
be subst 4;	(*RA2: DELETE needless definition of PA!*)
by parts_Fake_tac;
(*RA3 requires a further induction*)
be responses.induct 5;
by (ALLGOALS Asm_simp_tac);
(*RA2*)
by (best_tac (!claset addDs  [Suc_leD, parts_cut]
                      addEs  [leD RS notE,
			      new_nonces_not_seen RSN(2,rev_notE)]
		      addss (!simpset)) 4);
(*Fake*)
by (best_tac (!claset addSDs  [impOfSubs analz_subset_parts,
			      impOfSubs parts_insert_subset_Un,
			      Suc_leD]
		      addss (!simpset)) 2);
(*Five others!*)
by (REPEAT (fast_tac (!claset addEs [leD RS notE]
		              addDs [Suc_leD] 
			      addss (!simpset)) 1));
bind_thm ("Hash_new_nonces_not_seen",
	  result() RS mp RS mp RSN (2, rev_notE));


(** The Nonce NA uniquely identifies A's message. 
    This theorem applies to rounds RA1 and RA2!

  Unicity is not used in other proofs but is desirable in its own right.
**)

goal thy 
 "!!evs. [| evs : recur lost; A ~: lost |]               \
\ ==> EX B' P'. ALL B P.    \
\        Hash {|Key(shrK A), Agent A, Agent B, Nonce NA, P|} \
\          : parts (sees lost Spy evs)  -->  B=B' & P=P'";
be recur.induct 1;
be subst 4;	(*RA2: DELETE needless definition of PA!*)
(*For better simplification of RA2*)
by (res_inst_tac [("x1","XA")] (insert_commute RS ssubst) 4);
by parts_Fake_tac;
(*RA3 requires a further induction*)
be responses.induct 5;
by (ALLGOALS Asm_simp_tac);
by (step_tac (!claset addSEs partsEs) 1);
(*RA3: inductive case*)
by (best_tac (!claset addss  (!simpset)) 5);
(*Fake*)
by (best_tac (!claset addSIs [exI]
                      addDs [impOfSubs analz_subset_parts,
			     impOfSubs Fake_parts_insert]
		      addss (!simpset)) 2);
(*Base*) (** LEVEL 9 **)
by (fast_tac (!claset addss (!simpset)) 1);
by (ALLGOALS (simp_tac (!simpset addsimps [all_conj_distrib]))); 
(*RA1: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NA = ?y" 1);
by (best_tac (!claset addSIs [exI]
                      addEs  [Hash_new_nonces_not_seen]
		      addss (!simpset)) 1);
by (best_tac (!claset addss  (!simpset)) 1);
(*RA2: creation of new Nonce*)
by (expand_case_tac "NA = ?y" 1);
by (best_tac (!claset addSIs [exI]
                      addDs  [parts_cut]
		      addEs  [Hash_new_nonces_not_seen]
		      addss  (!simpset)) 1);
by (best_tac (!claset addss  (!simpset)) 1);
val lemma = result();

goalw thy [HPair_def]
 "!!evs.[| HPair (Key(shrK A)) {|Agent A, Agent B, Nonce NA, P|}   \
\            : parts (sees lost Spy evs);                        \
\          HPair (Key(shrK A)) {|Agent A, Agent B', Nonce NA, P'|} \
\            : parts (sees lost Spy evs);                        \
\          evs : recur lost;  A ~: lost |]                      \
\        ==> B=B' & P=P'";
by (REPEAT (eresolve_tac partsEs 1));
by (prove_unique_tac lemma 1);
qed "unique_NA";


(*** Lemmas concerning the Server's response
      (relations "respond" and "responses") 
***)

goal thy
 "!!evs. [| RB : responses i;  evs : recur lost |] \
\ ==> (Key (shrK B) : analz (insert RB (sees lost Spy evs))) = (B:lost)";
be responses.induct 1;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps [resp_analz_image_newK, insert_Key_singleton]
               setloop split_tac [expand_if])));
qed "shrK_in_analz_respond";
Addsimps [shrK_in_analz_respond];


goal thy  
 "!!evs. [| RB : responses i;                             \
\           ALL K I. (Key K : analz (Key``(newK``I) Un H)) = \
\           (K : newK``I | Key K : analz H) |]                \
\       ==> (Key K : analz (insert RB H)) --> \
\                  (Key K : parts{RB} | Key K : analz H)";
be responses.induct 1;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps [read_instantiate [("H", "?ff``?xx")] parts_insert,
			 resp_analz_image_newK_lemma,
			 insert_Key_singleton, insert_Key_image, 
			 Un_assoc RS sym, pushKey_newK]
               setloop split_tac [expand_if])));
(*The "Message" simpset gives the standard treatment of "image"*)
by (simp_tac (simpset_of "Message") 1);
by (fast_tac (!claset delrules [allE]) 1);
qed "resp_analz_insert_lemma";

bind_thm ("resp_analz_insert",
	  raw_analz_image_newK RSN
	    (2, resp_analz_insert_lemma) RSN(2, rev_mp));


(*The Server does not send such messages.  This theorem lets us avoid
  assuming B~=Server in RA4.*)
goal thy 
 "!!evs. evs : recur lost       \
\ ==> ALL C X Y P. Says Server C {|X, Agent Server, Agent C, Y, P|} \
\                  ~: set_of_list evs";
by (etac recur.induct 1);
be (respond.induct) 5;
by (Auto_tac());
qed_spec_mp "Says_Server_not";
AddSEs [Says_Server_not RSN (2,rev_notE)];


goal thy 
 "!!i. (j,PB,RB) : respond i               \
\  ==> EX A' B'. ALL A B N.                \
\        Crypt (shrK A) {|Key K, Agent B, N|} : parts {RB} \
\          -->   (A'=A & B'=B) | (A'=B & B'=A)";
be respond.induct 1;
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps [all_conj_distrib]))); 
(*Base case*)
by (Fast_tac 1);
by (Step_tac 1);
by (expand_case_tac "K = ?y" 1);
by (best_tac (!claset addSIs [exI]
                      addSEs partsEs
                      addDs [Key_in_parts_respond]
                      addss (!simpset)) 1);
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [exI] 2));
by (ex_strip_tac 1);
be respond.elim 1;
by (REPEAT_FIRST (etac Pair_inject ORELSE' hyp_subst_tac));
by (ALLGOALS (asm_full_simp_tac 
	      (!simpset addsimps [all_conj_distrib, ex_disj_distrib]))); 
by (Fast_tac 1);
by (Fast_tac 1);
val lemma = result();

goal thy 
 "!!RB. [| Crypt (shrK A) {|Key K, Agent B, N|} : parts {RB};    \
\          Crypt (shrK A') {|Key K, Agent B', N'|} : parts {RB};   \
\          (j,PB,RB) : respond i |]               \
\ ==>   (A'=A & B'=B) | (A'=B & B'=A)";
by (prove_unique_tac lemma 1);	(*50 seconds??, due to the disjunctions*)
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg RA3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

goal thy 
 "!!j. (j, HPair (Key(shrK A)) {|Agent A, B, NA, P|}, RA) : respond i \
\ ==> Crypt (shrK A) {|Key (newK2 (i,j)), B, NA|} : parts {RA}";
be respond.elim 1;
by (ALLGOALS Asm_full_simp_tac);
qed "newK2_respond_lemma";


goal thy 
 "!!evs. [| (j,PB,RB) : respond (length evs);  evs : recur lost |]       \
\        ==> ALL A A' N. A ~: lost & A' ~: lost -->  \
\            Crypt (shrK A) {|Key K, Agent A', N|} : parts{RB} -->  \
\            Key K ~: analz (insert RB (sees lost Spy evs))";
be respond.induct 1;
by (forward_tac [respond_imp_responses] 2);
by (ALLGOALS (*4 MINUTES???*)
    (asm_simp_tac 
     (!simpset addsimps 
	  ([analz_image_newK, not_parts_not_analz,
	    read_instantiate [("H", "?ff``?xx")] parts_insert,
	    Un_assoc RS sym, resp_analz_image_newK,
	    insert_Key_singleton, analz_insert_Key_newK])
      setloop split_tac [expand_if])));
by (ALLGOALS (simp_tac (simpset_of "Message")));
by (Fast_tac 1);
by (step_tac (!claset addSEs [MPair_parts]) 1);
(** LEVEL 6 **)
by (fast_tac (!claset addDs [resp_analz_insert, Key_in_parts_respond]
                      addSEs [new_keys_not_seen RS not_parts_not_analz 
			      RSN(2,rev_notE)]
                      addss (!simpset)) 4);
by (fast_tac (!claset addSDs [newK2_respond_lemma]) 3);
by (best_tac (!claset addSEs partsEs
                      addDs [Key_in_parts_respond]
                      addss (!simpset)) 2);
by (thin_tac "ALL x.?P(x)" 1);
be respond.elim 1;
by (fast_tac (!claset addss (!simpset)) 1);
by (step_tac (!claset addss (!simpset)) 1);
by (best_tac (!claset addSEs partsEs
                      addDs [Key_in_parts_respond]
                      addss (!simpset)) 1);
qed_spec_mp "respond_Spy_not_see_encrypted_key";


goal thy
 "!!evs. [| A ~: lost;  A' ~: lost;  evs : recur lost |]            \
\        ==> Says Server B RB : set_of_list evs -->                 \
\            Crypt (shrK A) {|Key K, Agent A', N|} : parts{RB} -->  \
\            Key K ~: analz (sees lost Spy evs)";
by (etac recur.induct 1);
be subst 4;	(*RA2: DELETE needless definition of PA!*)
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac
     (!simpset addsimps [not_parts_not_analz, analz_insert_Key_newK] 
               setloop split_tac [expand_if])));
(*RA4*)
by (spy_analz_tac 4);
(*Fake*)
by (spy_analz_tac 1);
by (step_tac (!claset delrules [impCE]) 1);
(*RA2*)
by (spy_analz_tac 1);
(*RA3, case 2: K is an old key*)
by (fast_tac (!claset addSDs [resp_analz_insert]
		      addSEs partsEs
                      addDs [Key_in_parts_respond]
	              addEs [Says_imp_old_keys RS less_irrefl]) 2);
(*RA3, case 1: use lemma previously proved by induction*)
by (fast_tac (!claset addSEs [respond_Spy_not_see_encrypted_key RSN
			      (2,rev_notE)]) 1);
bind_thm ("Spy_not_see_encrypted_key", result() RS mp RSN (2, rev_mp));


goal thy 
 "!!evs. [| Says Server B RB : set_of_list evs;                 \
\           Crypt (shrK A) {|Key K, Agent A', N|} : parts{RB};  \
\           C ~: {A,A',Server};                                 \
\           A ~: lost;  A' ~: lost;  evs : recur lost |]        \
\        ==> Key K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [recur_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(**** Authenticity properties for Agents ****)

(*The response never contains Hashes*)
(*NEEDED????????????????*)
goal thy
 "!!evs. (j,PB,RB) : respond i \
\        ==> Hash {|Key (shrK B), M|} : parts (insert RB H) --> \
\            Hash {|Key (shrK B), M|} : parts H";
be (respond_imp_responses RS responses.induct) 1;
by (Auto_tac());
bind_thm ("Hash_in_parts_respond", result() RSN (2, rev_mp));

(*NEEDED????????????????*)
(*Only RA1 or RA2 can have caused such a part of a message to appear.*)
goalw thy [HPair_def]
 "!!evs. [| Hash {|Key(shrK A), Agent A, Agent B, NA, P|}         \
\             : parts (sees lost Spy evs);                        \
\            A ~: lost;  evs : recur lost |]                        \
\        ==> Says A B (HPair (Key(shrK A)) {|Agent A, Agent B, NA, P|})  \
\             : set_of_list evs";
be rev_mp 1;
by (parts_induct_tac 1);
(*RA3*)
by (fast_tac (!claset addSDs [Hash_in_parts_respond]) 2);
(*RA2*)
by ((REPEAT o CHANGED)     (*Push in XA--for more simplification*)
    (res_inst_tac [("x1","XA")] (insert_commute RS ssubst) 1));
by (best_tac (!claset addSEs partsEs 
                      addDs [parts_cut]
                      addss  (!simpset)) 1);
qed_spec_mp "Hash_auth_sender";


val nonce_not_seen_now = le_refl RSN (2, new_nonces_not_seen) RSN (2,rev_notE);


(** These two results should subsume (for all agents) the guarantees proved
    separately for A and B in the Otway-Rees protocol.
**)


(*Encrypted messages can only originate with the Server.*)
goal thy 
 "!!evs. [| A ~: lost;  A ~= Spy;  evs : recur lost |]       \
\    ==> Crypt (shrK A) Y : parts (sees lost Spy evs)        \
\        --> (EX C RC. Says Server C RC : set_of_list evs &  \
\                      Crypt (shrK A) Y : parts {RC})";
by (parts_induct_tac 1);
(*RA4*)
by (Fast_tac 4);
(*RA3*)
by (full_simp_tac (!simpset addsimps [parts_insert_sees]) 3
    THEN Fast_tac 3);
(*RA1*)
by (Fast_tac 1);
(*RA2: it cannot be a new Nonce, contradiction.*)
by ((REPEAT o CHANGED)     (*Push in XA--for more simplification*)
    (res_inst_tac [("x1","XA")] (insert_commute RS ssubst) 1));
by (deepen_tac (!claset delrules [impCE]
                      addSIs [disjI2]
                      addSEs [MPair_parts]
                      addDs  [parts_cut, parts.Body]
                      addss  (!simpset)) 0 1);
qed_spec_mp "Crypt_imp_Server_msg";


(*Corollary: if A receives B's message then the key came from the Server*)
goal thy 
 "!!evs. [| Says B' A RA : set_of_list evs;                        \
\           Crypt (shrK A) {|Key K, Agent A', NA|} : parts {RA};   \
\           A ~: lost;  A ~= Spy;  evs : recur lost |]             \
\        ==> EX C RC. Says Server C RC : set_of_list evs &         \
\                       Crypt (shrK A) {|Key K, Agent A', NA|} : parts {RC}";
by (best_tac (!claset addSIs [Crypt_imp_Server_msg]
                      addDs  [Says_imp_sees_Spy RS parts.Inj RSN (2,parts_cut)]
                      addss  (!simpset)) 1);
qed "Agent_trust";


(*Overall guarantee: if A receives a certificant mentioning A'
  then the only other agent who knows the key is A'.*)
goal thy 
 "!!evs. [| Says B' A RA : set_of_list evs;                           \
\           Crypt (shrK A) {|Key K, Agent A', NA|} : parts {RA};      \
\           C ~: {A,A',Server};                                       \
\           A ~: lost;  A' ~: lost;  A ~= Spy;  evs : recur lost |]   \
\        ==> Key K ~: analz (sees lost C evs)";
by (dtac Agent_trust 1 THEN REPEAT_FIRST assume_tac);
by (fast_tac (!claset addSEs [Agent_not_see_encrypted_key RSN(2,rev_notE)]) 1);
qed "Agent_secrecy";

