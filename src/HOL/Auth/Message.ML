(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analyze" and "synthesize"
*)

open Message;


(**************** INSTALL CENTRALLY SOMEWHERE? ****************)

(*Maybe swap the safe_tac and simp_tac lines?**)
fun auto_tac (cs,ss) = 
    TRY (safe_tac cs) THEN 
    ALLGOALS (asm_full_simp_tac ss) THEN
    REPEAT (FIRSTGOAL (best_tac (cs addss ss)));

fun Auto_tac() = auto_tac (!claset, !simpset);

fun auto() = by (Auto_tac());

fun impOfSubs th = th RSN (2, rev_subsetD);

(**************** INSTALL CENTRALLY SOMEWHERE? ****************)



(** Inverse of keys **)

goal thy "!!K K'. (invKey K = invKey K') = (K=K')";
by (Step_tac 1);
br box_equals 1;
by (REPEAT (rtac invKey 2));
by (Asm_simp_tac 1);
qed "invKey_eq";

Addsimps [invKey, invKey_eq];


(**** keysFor operator ****)

goalw thy [keysFor_def] "keysFor {} = {}";
by (Fast_tac 1);
qed "keysFor_empty";

goalw thy [keysFor_def] "keysFor (H Un H') = keysFor H Un keysFor H'";
by (Fast_tac 1);
qed "keysFor_Un";

goalw thy [keysFor_def] "keysFor (UN i. H i) = (UN i. keysFor (H i))";
by (Fast_tac 1);
qed "keysFor_UN";

(*Monotonicity*)
goalw thy [keysFor_def] "!!G H. G<=H ==> keysFor(G) <= keysFor(H)";
by (Fast_tac 1);
qed "keysFor_mono";

goalw thy [keysFor_def] "keysFor (insert (Agent A) H) = keysFor H";
by (fast_tac (!claset addss (!simpset)) 1);
qed "keysFor_insert_Agent";

goalw thy [keysFor_def] "keysFor (insert (Nonce N) H) = keysFor H";
by (fast_tac (!claset addss (!simpset)) 1);
qed "keysFor_insert_Nonce";

goalw thy [keysFor_def] "keysFor (insert (Key K) H) = keysFor H";
by (fast_tac (!claset addss (!simpset)) 1);
qed "keysFor_insert_Key";

goalw thy [keysFor_def] "keysFor (insert {|X,Y|} H) = keysFor H";
by (fast_tac (!claset addss (!simpset)) 1);
qed "keysFor_insert_MPair";

goalw thy [keysFor_def]
    "keysFor (insert (Crypt X K) H) = insert (invKey K) (keysFor H)";
by (Auto_tac());
by (fast_tac (!claset addIs [image_eqI]) 1);
qed "keysFor_insert_Crypt";

Addsimps [keysFor_empty, keysFor_Un, keysFor_UN, 
	  keysFor_insert_Agent, keysFor_insert_Nonce,
	  keysFor_insert_Key, keysFor_insert_MPair,
	  keysFor_insert_Crypt];


(**** Inductive relation "parts" ****)

val major::prems = 
goal thy "[| {|X,Y|} : parts H;       \
\            [| X : parts H; Y : parts H |] ==> P  \
\         |] ==> P";
by (cut_facts_tac [major] 1);
brs prems 1;
by (REPEAT (eresolve_tac [asm_rl, parts.Fst, parts.Snd] 1));
qed "MPair_parts";

AddIs  [parts.Inj];
AddSEs [MPair_parts];
AddDs  [parts.Body];

goal thy "H <= parts(H)";
by (Fast_tac 1);
qed "parts_increasing";

(*Monotonicity*)
goalw thy parts.defs "!!G H. G<=H ==> parts(G) <= parts(H)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "parts_mono";

goal thy "parts{} = {}";
by (Step_tac 1);
be parts.induct 1;
by (ALLGOALS Fast_tac);
qed "parts_empty";
Addsimps [parts_empty];

goal thy "!!X. X: parts{} ==> P";
by (Asm_full_simp_tac 1);
qed "parts_emptyE";
AddSEs [parts_emptyE];


(** Unions **)

goal thy "parts(G) Un parts(H) <= parts(G Un H)";
by (REPEAT (ares_tac [Un_least, parts_mono, Un_upper1, Un_upper2] 1));
val parts_Un_subset1 = result();

goal thy "parts(G Un H) <= parts(G) Un parts(H)";
br subsetI 1;
be parts.induct 1;
by (ALLGOALS Fast_tac);
val parts_Un_subset2 = result();

goal thy "parts(G Un H) = parts(G) Un parts(H)";
by (REPEAT (ares_tac [equalityI, parts_Un_subset1, parts_Un_subset2] 1));
qed "parts_Un";

(*TWO inserts to avoid looping.  This rewrite is better than nothing...*)
goal thy "parts (insert X (insert Y H)) = parts {X} Un parts {Y} Un parts H";
by (stac (read_instantiate [("A","H")] insert_is_Un) 1);
by (stac (read_instantiate [("A","{Y} Un H")] insert_is_Un) 1);
by (simp_tac (HOL_ss addsimps [parts_Un, Un_assoc]) 1);
qed "parts_insert2";

goal thy "(UN x:A. parts(H x)) <= parts(UN x:A. H x)";
by (REPEAT (ares_tac [UN_least, parts_mono, UN_upper] 1));
val parts_UN_subset1 = result();

goal thy "parts(UN x:A. H x) <= (UN x:A. parts(H x))";
br subsetI 1;
be parts.induct 1;
by (ALLGOALS Fast_tac);
val parts_UN_subset2 = result();

goal thy "parts(UN x:A. H x) = (UN x:A. parts(H x))";
by (REPEAT (ares_tac [equalityI, parts_UN_subset1, parts_UN_subset2] 1));
qed "parts_UN";

goal thy "parts(UN x. H x) = (UN x. parts(H x))";
by (simp_tac (!simpset addsimps [UNION1_def, parts_UN]) 1);
qed "parts_UN1";

(*Added to simplify arguments to parts, analyze and synthesize*)
Addsimps [parts_Un, parts_UN, parts_UN1];

goal thy "insert X (parts H) <= parts(insert X H)";
by (fast_tac (!claset addEs [impOfSubs parts_mono]) 1);
qed "parts_insert_subset";

(*Especially for reasoning about the Fake rule in traces*)
goal thy "!!Y. X: G ==> parts(insert X H) <= parts G Un parts H";
br ([parts_mono, parts_Un_subset2] MRS subset_trans) 1;
by (Fast_tac 1);
qed "parts_insert_subset_Un";

(** Idempotence and transitivity **)

goal thy "!!H. X: parts (parts H) ==> X: parts H";
be parts.induct 1;
by (ALLGOALS Fast_tac);
qed "parts_partsE";
AddSEs [parts_partsE];

goal thy "parts (parts H) = parts H";
by (Fast_tac 1);
qed "parts_idem";
Addsimps [parts_idem];

goal thy "!!H. [| X: parts G;  G <= parts H |] ==> X: parts H";
by (dtac parts_mono 1);
by (Fast_tac 1);
qed "parts_trans";

(*Cut*)
goal thy "!!H. [| X: parts H;  Y: parts (insert X H) |] ==> Y: parts H";
be parts_trans 1;
by (Fast_tac 1);
qed "parts_cut";


(** Rewrite rules for pulling out atomic messages **)

goal thy "parts (insert (Agent agt) H) = insert (Agent agt) (parts H)";
by (rtac (parts_insert_subset RSN (2, equalityI)) 1);
br subsetI 1;
be parts.induct 1;
(*Simplification breaks up equalities between messages;
  how to make it work for fast_tac??*)
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_insert_Agent";

goal thy "parts (insert (Nonce N) H) = insert (Nonce N) (parts H)";
by (rtac (parts_insert_subset RSN (2, equalityI)) 1);
br subsetI 1;
be parts.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_insert_Nonce";

goal thy "parts (insert (Key K) H) = insert (Key K) (parts H)";
by (rtac (parts_insert_subset RSN (2, equalityI)) 1);
br subsetI 1;
be parts.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_insert_Key";

goal thy "parts (insert (Crypt X K) H) = \
\         insert (Crypt X K) (parts (insert X H))";
br equalityI 1;
br subsetI 1;
be parts.induct 1;
by (Auto_tac());
be parts.induct 1;
by (ALLGOALS (best_tac (!claset addIs [parts.Body])));
qed "parts_insert_Crypt";

goal thy "parts (insert {|X,Y|} H) = \
\         insert {|X,Y|} (parts (insert X (insert Y H)))";
br equalityI 1;
br subsetI 1;
be parts.induct 1;
by (Auto_tac());
be parts.induct 1;
by (ALLGOALS (best_tac (!claset addIs [parts.Fst, parts.Snd])));
qed "parts_insert_MPair";

Addsimps [parts_insert_Agent, parts_insert_Nonce, 
	  parts_insert_Key, parts_insert_Crypt, parts_insert_MPair];


(**** Inductive relation "analyze" ****)

val major::prems = 
goal thy "[| {|X,Y|} : analyze H;       \
\            [| X : analyze H; Y : analyze H |] ==> P  \
\         |] ==> P";
by (cut_facts_tac [major] 1);
brs prems 1;
by (REPEAT (eresolve_tac [asm_rl, analyze.Fst, analyze.Snd] 1));
qed "MPair_analyze";

AddIs  [analyze.Inj];
AddSEs [MPair_analyze];
AddDs  [analyze.Decrypt];

goal thy "H <= analyze(H)";
by (Fast_tac 1);
qed "analyze_increasing";

goal thy "analyze H <= parts H";
by (rtac subsetI 1);
be analyze.induct 1;
by (ALLGOALS Fast_tac);
qed "analyze_subset_parts";

bind_thm ("not_parts_not_analyze", analyze_subset_parts RS contra_subsetD);


goal thy "parts (analyze H) = parts H";
br equalityI 1;
br (analyze_subset_parts RS parts_mono RS subset_trans) 1;
by (Simp_tac 1);
by (fast_tac (!claset addDs [analyze_increasing RS parts_mono RS subsetD]) 1);
qed "parts_analyze";
Addsimps [parts_analyze];

(*Monotonicity; Lemma 1 of Lowe*)
goalw thy analyze.defs "!!G H. G<=H ==> analyze(G) <= analyze(H)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "analyze_mono";

(** General equational properties **)

goal thy "analyze{} = {}";
by (Step_tac 1);
be analyze.induct 1;
by (ALLGOALS Fast_tac);
qed "analyze_empty";
Addsimps [analyze_empty];

(*Converse fails: we can analyze more from the union than from the 
  separate parts, as a key in one might decrypt a message in the other*)
goal thy "analyze(G) Un analyze(H) <= analyze(G Un H)";
by (REPEAT (ares_tac [Un_least, analyze_mono, Un_upper1, Un_upper2] 1));
qed "analyze_Un";

goal thy "insert X (analyze H) <= analyze(insert X H)";
by (fast_tac (!claset addEs [impOfSubs analyze_mono]) 1);
qed "analyze_insert";

(** Rewrite rules for pulling out atomic messages **)

goal thy "analyze (insert (Agent agt) H) = insert (Agent agt) (analyze H)";
by (rtac (analyze_insert RSN (2, equalityI)) 1);
br subsetI 1;
be analyze.induct 1;
(*Simplification breaks up equalities between messages;
  how to make it work for fast_tac??*)
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analyze_insert_Agent";

goal thy "analyze (insert (Nonce N) H) = insert (Nonce N) (analyze H)";
by (rtac (analyze_insert RSN (2, equalityI)) 1);
br subsetI 1;
be analyze.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analyze_insert_Nonce";

(*Can only pull out Keys if they are not needed to decrypt the rest*)
goalw thy [keysFor_def]
    "!!K. K ~: keysFor (analyze H) ==>  \
\         analyze (insert (Key K) H) = insert (Key K) (analyze H)";
by (rtac (analyze_insert RSN (2, equalityI)) 1);
br subsetI 1;
be analyze.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analyze_insert_Key";

goal thy "!!H. Key (invKey K) ~: analyze H ==>  \
\              analyze (insert (Crypt X K) H) = \
\              insert (Crypt X K) (analyze H)";
by (rtac (analyze_insert RSN (2, equalityI)) 1);
br subsetI 1;
be analyze.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analyze_insert_Crypt";

goal thy "!!H. Key (invKey K) : analyze H ==>  \
\              analyze (insert (Crypt X K) H) <= \
\              insert (Crypt X K) (analyze (insert X H))";
br subsetI 1;
by (eres_inst_tac [("za","x")] analyze.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
val lemma1 = result();

goal thy "!!H. Key (invKey K) : analyze H ==>  \
\              insert (Crypt X K) (analyze (insert X H)) <= \
\              analyze (insert (Crypt X K) H)";
by (Auto_tac());
by (eres_inst_tac [("za","x")] analyze.induct 1);
by (Auto_tac());
by (best_tac (!claset addIs [subset_insertI RS analyze_mono RS subsetD,
			     analyze.Decrypt]) 1);
val lemma2 = result();

goal thy "!!H. Key (invKey K) : analyze H ==>  \
\              analyze (insert (Crypt X K) H) = \
\              insert (Crypt X K) (analyze (insert X H))";
by (REPEAT (ares_tac [equalityI, lemma1, lemma2] 1));
qed "analyze_insert_Decrypt";

Addsimps [analyze_insert_Agent, analyze_insert_Nonce, 
	  analyze_insert_Key, analyze_insert_Crypt,
	  analyze_insert_Decrypt];


(*This rule supposes "for the sake of argument" that we have the key.*)
goal thy  "analyze (insert (Crypt X K) H) <=  \
\         insert (Crypt X K) (analyze (insert X H))";
br subsetI 1;
be analyze.induct 1;
by (Auto_tac());
qed "analyze_insert_Crypt_subset";


(** Rewrite rules for pulling out atomic parts of messages **)

goal thy "analyze (insert X H) <= analyze (insert {|X,Y|} H)";
br subsetI 1;
be analyze.induct 1;
by (ALLGOALS (best_tac (!claset addIs [analyze.Fst]))); 
qed "analyze_insert_subset_MPair1";

goal thy "analyze (insert Y H) <= analyze (insert {|X,Y|} H)";
br subsetI 1;
be analyze.induct 1;
by (ALLGOALS (best_tac (!claset addIs [analyze.Snd]))); 
qed "analyze_insert_subset_MPair2";

goal thy "analyze (insert {|Agent agt,Y|} H) = \
\         insert {|Agent agt,Y|} (insert (Agent agt) (analyze (insert Y H)))";
by (rtac equalityI 1);
by (best_tac (!claset addIs [analyze.Fst,
			     impOfSubs analyze_insert_subset_MPair2]) 2); 
br subsetI 1;
be analyze.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analyze_insert_Agent_MPair";

goal thy "analyze (insert {|Nonce N,Y|} H) = \
\         insert {|Nonce N,Y|} (insert (Nonce N) (analyze (insert Y H)))";
by (rtac equalityI 1);
by (best_tac (!claset addIs [analyze.Fst,
			     impOfSubs analyze_insert_subset_MPair2]) 2); 
br subsetI 1;
be analyze.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analyze_insert_Nonce_MPair";

(*Can only pull out Keys if they are not needed to decrypt the rest*)
goalw thy [keysFor_def]
    "!!K. K ~: keysFor (analyze (insert Y H)) ==>  \
\         analyze (insert {|Key K, Y|} H) = \
\         insert {|Key K, Y|} (insert (Key K) (analyze (insert Y H)))";
by (rtac equalityI 1);
by (best_tac (!claset addIs [analyze.Fst,
			     impOfSubs analyze_insert_subset_MPair2]) 2); 
br subsetI 1;
be analyze.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analyze_insert_Key_MPair";

Addsimps [analyze_insert_Agent_MPair, analyze_insert_Nonce_MPair,
	  analyze_insert_Key_MPair];

(** Idempotence and transitivity **)

goal thy "!!H. X: analyze (analyze H) ==> X: analyze H";
be analyze.induct 1;
by (ALLGOALS Fast_tac);
qed "analyze_analyzeE";
AddSEs [analyze_analyzeE];

goal thy "analyze (analyze H) = analyze H";
by (Fast_tac 1);
qed "analyze_idem";
Addsimps [analyze_idem];

goal thy "!!H. [| X: analyze G;  G <= analyze H |] ==> X: analyze H";
by (dtac analyze_mono 1);
by (Fast_tac 1);
qed "analyze_trans";

(*Cut; Lemma 2 of Lowe*)
goal thy "!!H. [| X: analyze H;  Y: analyze (insert X H) |] ==> Y: analyze H";
be analyze_trans 1;
by (Fast_tac 1);
qed "analyze_cut";

(*Cut can be proved easily by induction on
   "!!H. Y: analyze (insert X H) ==> X: analyze H --> Y: analyze H"
*)

(*If there are no pairs or encryptions then analyze does nothing*)
goal thy "!!H. [| ALL X Y. {|X,Y|} ~: H;  ALL X K. Crypt X K ~: H |] ==> \
\         analyze H = H";
by (Step_tac 1);
be analyze.induct 1;
by (ALLGOALS Fast_tac);
qed "analyze_trivial";

(*Helps to prove Fake cases*)
goal thy "!!X. X: analyze (UN i. analyze (H i)) ==> X: analyze (UN i. H i)";
be analyze.induct 1;
by (ALLGOALS (fast_tac (!claset addEs [impOfSubs analyze_mono])));
val lemma = result();

goal thy "analyze (UN i. analyze (H i)) = analyze (UN i. H i)";
by (fast_tac (!claset addIs [lemma]
		      addEs [impOfSubs analyze_mono]) 1);
qed "analyze_UN_analyze";
Addsimps [analyze_UN_analyze];


(**** Inductive relation "synthesize" ****)

AddIs  synthesize.intrs;

goal thy "H <= synthesize(H)";
by (Fast_tac 1);
qed "synthesize_increasing";

(*Monotonicity*)
goalw thy synthesize.defs "!!G H. G<=H ==> synthesize(G) <= synthesize(H)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "synthesize_mono";

(** Unions **)

(*Converse fails: we can synthesize more from the union than from the 
  separate parts, building a compound message using elements of each.*)
goal thy "synthesize(G) Un synthesize(H) <= synthesize(G Un H)";
by (REPEAT (ares_tac [Un_least, synthesize_mono, Un_upper1, Un_upper2] 1));
qed "synthesize_Un";

(** Idempotence and transitivity **)

goal thy "!!H. X: synthesize (synthesize H) ==> X: synthesize H";
be synthesize.induct 1;
by (ALLGOALS Fast_tac);
qed "synthesize_synthesizeE";
AddSEs [synthesize_synthesizeE];

goal thy "synthesize (synthesize H) = synthesize H";
by (Fast_tac 1);
qed "synthesize_idem";

goal thy "!!H. [| X: synthesize G;  G <= synthesize H |] ==> X: synthesize H";
by (dtac synthesize_mono 1);
by (Fast_tac 1);
qed "synthesize_trans";

(*Cut; Lemma 2 of Lowe*)
goal thy "!!H. [| X: synthesize H;  Y: synthesize (insert X H) \
\              |] ==> Y: synthesize H";
be synthesize_trans 1;
by (Fast_tac 1);
qed "synthesize_cut";


(*Can only produce a nonce or key if it is already known,
  but can synthesize a pair or encryption from its components...*)
val mk_cases = synthesize.mk_cases msg.simps;

val Nonce_synthesize = mk_cases "Nonce n : synthesize H";
val Key_synthesize   = mk_cases "Key K : synthesize H";
val MPair_synthesize = mk_cases "{|X,Y|} : synthesize H";
val Crypt_synthesize = mk_cases "Crypt X K : synthesize H";

AddSEs [Nonce_synthesize, Key_synthesize, MPair_synthesize, Crypt_synthesize];

goal thy "(Nonce N : synthesize H) = (Nonce N : H)";
by (Fast_tac 1);
qed "Nonce_synthesize_eq";

goal thy "(Key K : synthesize H) = (Key K : H)";
by (Fast_tac 1);
qed "Key_synthesize_eq";

Addsimps [Nonce_synthesize_eq, Key_synthesize_eq];


goalw thy [keysFor_def]
    "keysFor (synthesize H) = keysFor H Un invKey``{K. Key K : H}";
by (Fast_tac 1);
qed "keysFor_synthesize";
Addsimps [keysFor_synthesize];


(*** Combinations of parts, analyze and synthesize ***)

(*Not that useful, in view of the following one...*)
goal thy "parts (synthesize H) <= synthesize (parts H)";
by (Step_tac 1);
be parts.induct 1;
be (parts_increasing RS synthesize_mono RS subsetD) 1;
by (ALLGOALS Fast_tac);
qed "parts_synthesize_subset";

goal thy "parts (synthesize H) = parts H Un synthesize H";
br equalityI 1;
br subsetI 1;
be parts.induct 1;
by (ALLGOALS
    (best_tac (!claset addIs ((synthesize_increasing RS parts_mono RS subsetD)
			     ::parts.intrs))));
qed "parts_synthesize";
Addsimps [parts_synthesize];

goal thy "analyze (synthesize H) = analyze H Un synthesize H";
br equalityI 1;
br subsetI 1;
be analyze.induct 1;
by (best_tac
    (!claset addIs [synthesize_increasing RS analyze_mono RS subsetD]) 5);
(*Strange that best_tac just can't hack this one...*)
by (ALLGOALS (deepen_tac (!claset addIs analyze.intrs) 0));
qed "analyze_synthesize";
Addsimps [analyze_synthesize];

(*Hard to prove; still needed now that there's only one Enemy?*)
goal thy "analyze (UN i. synthesize (H i)) = \
\         analyze (UN i. H i) Un (UN i. synthesize (H i))";
br equalityI 1;
br subsetI 1;
be analyze.induct 1;
by (best_tac
    (!claset addEs [impOfSubs synthesize_increasing,
		    impOfSubs analyze_mono]) 5);
by (Best_tac 1);
by (deepen_tac (!claset addIs [analyze.Fst]) 0 1);
by (deepen_tac (!claset addIs [analyze.Snd]) 0 1);
by (deepen_tac (!claset addSEs [analyze.Decrypt]
			addIs  [analyze.Decrypt]) 0 1);
qed "analyze_UN1_synthesize";
Addsimps [analyze_UN1_synthesize];
