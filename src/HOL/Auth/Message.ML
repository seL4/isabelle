(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analz" and "synth"
*)

open Message;


(** Inverse of keys **)

goal thy "!!K K'. (invKey K = invKey K') = (K=K')";
by (Step_tac 1);
by (rtac box_equals 1);
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
by (Fast_tac 1);
qed "keysFor_insert_Crypt";

Addsimps [keysFor_empty, keysFor_Un, keysFor_UN, 
          keysFor_insert_Agent, keysFor_insert_Nonce,
          keysFor_insert_Key, keysFor_insert_MPair,
          keysFor_insert_Crypt];

goalw thy [keysFor_def] "!!H. Crypt X K : H ==> invKey K : keysFor H";
by (Fast_tac 1);
qed "Crypt_imp_invKey_keysFor";


(**** Inductive relation "parts" ****)

val major::prems = 
goal thy "[| {|X,Y|} : parts H;       \
\            [| X : parts H; Y : parts H |] ==> P  \
\         |] ==> P";
by (cut_facts_tac [major] 1);
by (resolve_tac prems 1);
by (REPEAT (eresolve_tac [asm_rl, parts.Fst, parts.Snd] 1));
qed "MPair_parts";

AddIs  [parts.Inj];

val partsEs = [MPair_parts, make_elim parts.Body];

AddSEs partsEs;
(*NB These two rules are UNSAFE in the formal sense, as they discard the
     compound message.  They work well on THIS FILE, perhaps because its
     proofs concern only atomic messages.*)

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
by (etac parts.induct 1);
by (ALLGOALS Fast_tac);
qed "parts_empty";
Addsimps [parts_empty];

goal thy "!!X. X: parts{} ==> P";
by (Asm_full_simp_tac 1);
qed "parts_emptyE";
AddSEs [parts_emptyE];

(*WARNING: loops if H = {Y}, therefore must not be repeated!*)
goal thy "!!H. X: parts H ==> EX Y:H. X: parts {Y}";
by (etac parts.induct 1);
by (ALLGOALS Fast_tac);
qed "parts_singleton";


(** Unions **)

goal thy "parts(G) Un parts(H) <= parts(G Un H)";
by (REPEAT (ares_tac [Un_least, parts_mono, Un_upper1, Un_upper2] 1));
val parts_Un_subset1 = result();

goal thy "parts(G Un H) <= parts(G) Un parts(H)";
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS Fast_tac);
val parts_Un_subset2 = result();

goal thy "parts(G Un H) = parts(G) Un parts(H)";
by (REPEAT (ares_tac [equalityI, parts_Un_subset1, parts_Un_subset2] 1));
qed "parts_Un";

goal thy "parts (insert X H) = parts {X} Un parts H";
by (stac (read_instantiate [("A","H")] insert_is_Un) 1);
by (simp_tac (HOL_ss addsimps [parts_Un]) 1);
qed "parts_insert";

(*TWO inserts to avoid looping.  This rewrite is better than nothing.
  Not suitable for Addsimps: its behaviour can be strange.*)
goal thy "parts (insert X (insert Y H)) = parts {X} Un parts {Y} Un parts H";
by (simp_tac (!simpset addsimps [Un_assoc]) 1);
by (simp_tac (!simpset addsimps [parts_insert RS sym]) 1);
qed "parts_insert2";

goal thy "(UN x:A. parts(H x)) <= parts(UN x:A. H x)";
by (REPEAT (ares_tac [UN_least, parts_mono, UN_upper] 1));
val parts_UN_subset1 = result();

goal thy "parts(UN x:A. H x) <= (UN x:A. parts(H x))";
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS Fast_tac);
val parts_UN_subset2 = result();

goal thy "parts(UN x:A. H x) = (UN x:A. parts(H x))";
by (REPEAT (ares_tac [equalityI, parts_UN_subset1, parts_UN_subset2] 1));
qed "parts_UN";

goal thy "parts(UN x. H x) = (UN x. parts(H x))";
by (simp_tac (!simpset addsimps [UNION1_def, parts_UN]) 1);
qed "parts_UN1";

(*Added to simplify arguments to parts, analz and synth*)
Addsimps [parts_Un, parts_UN, parts_UN1];

goal thy "insert X (parts H) <= parts(insert X H)";
by (fast_tac (!claset addEs [impOfSubs parts_mono]) 1);
qed "parts_insert_subset";

(** Idempotence and transitivity **)

goal thy "!!H. X: parts (parts H) ==> X: parts H";
by (etac parts.induct 1);
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
goal thy "!!H. [| Y: parts (insert X H);  X: parts H |] ==> Y: parts H";
by (etac parts_trans 1);
by (Fast_tac 1);
qed "parts_cut";

val parts_insertI = impOfSubs (subset_insertI RS parts_mono);

goal thy "!!H. X: parts H ==> parts (insert X H) = parts H";
by (fast_tac (!claset addSEs [parts_cut]
                      addIs  [parts_insertI]) 1);
qed "parts_cut_eq";

Addsimps [parts_cut_eq];


(** Rewrite rules for pulling out atomic messages **)

goal thy "parts (insert (Agent agt) H) = insert (Agent agt) (parts H)";
by (rtac (parts_insert_subset RSN (2, equalityI)) 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
(*Simplification breaks up equalities between messages;
  how to make it work for fast_tac??*)
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_insert_Agent";

goal thy "parts (insert (Nonce N) H) = insert (Nonce N) (parts H)";
by (rtac (parts_insert_subset RSN (2, equalityI)) 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_insert_Nonce";

goal thy "parts (insert (Key K) H) = insert (Key K) (parts H)";
by (rtac (parts_insert_subset RSN (2, equalityI)) 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_insert_Key";

goal thy "parts (insert (Crypt X K) H) = \
\         insert (Crypt X K) (parts (insert X H))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (Auto_tac());
by (etac parts.induct 1);
by (ALLGOALS (best_tac (!claset addIs [parts.Body])));
qed "parts_insert_Crypt";

goal thy "parts (insert {|X,Y|} H) = \
\         insert {|X,Y|} (parts (insert X (insert Y H)))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (Auto_tac());
by (etac parts.induct 1);
by (ALLGOALS (best_tac (!claset addIs [parts.Fst, parts.Snd])));
qed "parts_insert_MPair";

Addsimps [parts_insert_Agent, parts_insert_Nonce, 
          parts_insert_Key, parts_insert_Crypt, parts_insert_MPair];


goal thy "parts (Key``N) = Key``N";
by (Auto_tac());
by (etac parts.induct 1);
by (Auto_tac());
qed "parts_image_Key";

Addsimps [parts_image_Key];


(**** Inductive relation "analz" ****)

val major::prems = 
goal thy "[| {|X,Y|} : analz H;       \
\            [| X : analz H; Y : analz H |] ==> P  \
\         |] ==> P";
by (cut_facts_tac [major] 1);
by (resolve_tac prems 1);
by (REPEAT (eresolve_tac [asm_rl, analz.Fst, analz.Snd] 1));
qed "MPair_analz";

AddIs  [analz.Inj];
AddSEs [MPair_analz];      (*Perhaps it should NOT be deemed safe!*)
AddDs  [analz.Decrypt];

Addsimps [analz.Inj];

goal thy "H <= analz(H)";
by (Fast_tac 1);
qed "analz_increasing";

goal thy "analz H <= parts H";
by (rtac subsetI 1);
by (etac analz.induct 1);
by (ALLGOALS Fast_tac);
qed "analz_subset_parts";

bind_thm ("not_parts_not_analz", analz_subset_parts RS contra_subsetD);


goal thy "parts (analz H) = parts H";
by (rtac equalityI 1);
by (rtac (analz_subset_parts RS parts_mono RS subset_trans) 1);
by (Simp_tac 1);
by (fast_tac (!claset addDs [analz_increasing RS parts_mono RS subsetD]) 1);
qed "parts_analz";
Addsimps [parts_analz];

goal thy "analz (parts H) = parts H";
by (Auto_tac());
by (etac analz.induct 1);
by (Auto_tac());
qed "analz_parts";
Addsimps [analz_parts];

(*Monotonicity; Lemma 1 of Lowe*)
goalw thy analz.defs "!!G H. G<=H ==> analz(G) <= analz(H)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "analz_mono";

(** General equational properties **)

goal thy "analz{} = {}";
by (Step_tac 1);
by (etac analz.induct 1);
by (ALLGOALS Fast_tac);
qed "analz_empty";
Addsimps [analz_empty];

(*Converse fails: we can analz more from the union than from the 
  separate parts, as a key in one might decrypt a message in the other*)
goal thy "analz(G) Un analz(H) <= analz(G Un H)";
by (REPEAT (ares_tac [Un_least, analz_mono, Un_upper1, Un_upper2] 1));
qed "analz_Un";

goal thy "insert X (analz H) <= analz(insert X H)";
by (fast_tac (!claset addEs [impOfSubs analz_mono]) 1);
qed "analz_insert";

(** Rewrite rules for pulling out atomic messages **)

goal thy "analz (insert (Agent agt) H) = insert (Agent agt) (analz H)";
by (rtac (analz_insert RSN (2, equalityI)) 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
(*Simplification breaks up equalities between messages;
  how to make it work for fast_tac??*)
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analz_insert_Agent";

goal thy "analz (insert (Nonce N) H) = insert (Nonce N) (analz H)";
by (rtac (analz_insert RSN (2, equalityI)) 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analz_insert_Nonce";

(*Can only pull out Keys if they are not needed to decrypt the rest*)
goalw thy [keysFor_def]
    "!!K. K ~: keysFor (analz H) ==>  \
\         analz (insert (Key K) H) = insert (Key K) (analz H)";
by (rtac (analz_insert RSN (2, equalityI)) 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analz_insert_Key";

goal thy "analz (insert {|X,Y|} H) = \
\         insert {|X,Y|} (analz (insert X (insert Y H)))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (Auto_tac());
by (etac analz.induct 1);
by (ALLGOALS (deepen_tac (!claset addIs [analz.Fst, analz.Snd, analz.Decrypt]) 0));
qed "analz_insert_MPair";

(*Can pull out enCrypted message if the Key is not known*)
goal thy "!!H. Key (invKey K) ~: analz H ==>  \
\              analz (insert (Crypt X K) H) = \
\              insert (Crypt X K) (analz H)";
by (rtac (analz_insert RSN (2, equalityI)) 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analz_insert_Crypt";

goal thy "!!H. Key (invKey K) : analz H ==>  \
\              analz (insert (Crypt X K) H) <= \
\              insert (Crypt X K) (analz (insert X H))";
by (rtac subsetI 1);
by (eres_inst_tac [("za","x")] analz.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
val lemma1 = result();

goal thy "!!H. Key (invKey K) : analz H ==>  \
\              insert (Crypt X K) (analz (insert X H)) <= \
\              analz (insert (Crypt X K) H)";
by (Auto_tac());
by (eres_inst_tac [("za","x")] analz.induct 1);
by (Auto_tac());
by (best_tac (!claset addIs [subset_insertI RS analz_mono RS subsetD,
                             analz.Decrypt]) 1);
val lemma2 = result();

goal thy "!!H. Key (invKey K) : analz H ==>  \
\              analz (insert (Crypt X K) H) = \
\              insert (Crypt X K) (analz (insert X H))";
by (REPEAT (ares_tac [equalityI, lemma1, lemma2] 1));
qed "analz_insert_Decrypt";

(*Case analysis: either the message is secure, or it is not!
  Effective, but can cause subgoals to blow up!
  Use with expand_if;  apparently split_tac does not cope with patterns
  such as "analz (insert (Crypt X' K) H)" *)
goal thy "analz (insert (Crypt X' K) H) = \
\         (if (Key (invKey K)  : analz H) then    \
\               insert (Crypt X' K) (analz (insert X' H)) \
\          else insert (Crypt X' K) (analz H))";
by (excluded_middle_tac "Key (invKey K)  : analz H " 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [analz_insert_Crypt, 
                                               analz_insert_Decrypt])));
qed "analz_Crypt_if";

Addsimps [analz_insert_Agent, analz_insert_Nonce, 
          analz_insert_Key, analz_insert_MPair, 
          analz_Crypt_if];

(*This rule supposes "for the sake of argument" that we have the key.*)
goal thy  "analz (insert (Crypt X K) H) <=  \
\          insert (Crypt X K) (analz (insert X H))";
by (rtac subsetI 1);
by (etac analz.induct 1);
by (Auto_tac());
qed "analz_insert_Crypt_subset";


goal thy "analz (Key``N) = Key``N";
by (Auto_tac());
by (etac analz.induct 1);
by (Auto_tac());
qed "analz_image_Key";

Addsimps [analz_image_Key];


(** Idempotence and transitivity **)

goal thy "!!H. X: analz (analz H) ==> X: analz H";
by (etac analz.induct 1);
by (ALLGOALS Fast_tac);
qed "analz_analzE";
AddSEs [analz_analzE];

goal thy "analz (analz H) = analz H";
by (Fast_tac 1);
qed "analz_idem";
Addsimps [analz_idem];

goal thy "!!H. [| X: analz G;  G <= analz H |] ==> X: analz H";
by (dtac analz_mono 1);
by (Fast_tac 1);
qed "analz_trans";

(*Cut; Lemma 2 of Lowe*)
goal thy "!!H. [| Y: analz (insert X H);  X: analz H |] ==> Y: analz H";
by (etac analz_trans 1);
by (Fast_tac 1);
qed "analz_cut";

(*Cut can be proved easily by induction on
   "!!H. Y: analz (insert X H) ==> X: analz H --> Y: analz H"
*)


(** A congruence rule for "analz" **)

goal thy "!!H. [| analz G <= analz G'; analz H <= analz H' \
\              |] ==> analz (G Un H) <= analz (G' Un H')";
by (Step_tac 1);
by (etac analz.induct 1);
by (ALLGOALS (best_tac (!claset addIs [analz_mono RS subsetD])));
qed "analz_subset_cong";

goal thy "!!H. [| analz G = analz G'; analz H = analz H' \
\              |] ==> analz (G Un H) = analz (G' Un H')";
by (REPEAT_FIRST (ares_tac [equalityI, analz_subset_cong]
          ORELSE' etac equalityE));
qed "analz_cong";


goal thy "!!H. analz H = analz H' ==> analz(insert X H) = analz(insert X H')";
by (asm_simp_tac (!simpset addsimps [insert_def] 
                           setloop (rtac analz_cong)) 1);
qed "analz_insert_cong";

(*If there are no pairs or encryptions then analz does nothing*)
goal thy "!!H. [| ALL X Y. {|X,Y|} ~: H;  ALL X K. Crypt X K ~: H |] ==> \
\         analz H = H";
by (Step_tac 1);
by (etac analz.induct 1);
by (ALLGOALS Fast_tac);
qed "analz_trivial";

(*Helps to prove Fake cases*)
goal thy "!!X. X: analz (UN i. analz (H i)) ==> X: analz (UN i. H i)";
by (etac analz.induct 1);
by (ALLGOALS (fast_tac (!claset addEs [impOfSubs analz_mono])));
val lemma = result();

goal thy "analz (UN i. analz (H i)) = analz (UN i. H i)";
by (fast_tac (!claset addIs [lemma]
                      addEs [impOfSubs analz_mono]) 1);
qed "analz_UN_analz";
Addsimps [analz_UN_analz];


(**** Inductive relation "synth" ****)

AddIs  synth.intrs;

(*Can only produce a nonce or key if it is already known,
  but can synth a pair or encryption from its components...*)
val mk_cases = synth.mk_cases msg.simps;

(*NO Agent_synth, as any Agent name can be synthd*)
val Nonce_synth = mk_cases "Nonce n : synth H";
val Key_synth   = mk_cases "Key K : synth H";
val MPair_synth = mk_cases "{|X,Y|} : synth H";
val Crypt_synth = mk_cases "Crypt X K : synth H";

AddSEs [Nonce_synth, Key_synth, MPair_synth, Crypt_synth];

goal thy "H <= synth(H)";
by (Fast_tac 1);
qed "synth_increasing";

(*Monotonicity*)
goalw thy synth.defs "!!G H. G<=H ==> synth(G) <= synth(H)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "synth_mono";

(** Unions **)

(*Converse fails: we can synth more from the union than from the 
  separate parts, building a compound message using elements of each.*)
goal thy "synth(G) Un synth(H) <= synth(G Un H)";
by (REPEAT (ares_tac [Un_least, synth_mono, Un_upper1, Un_upper2] 1));
qed "synth_Un";

goal thy "insert X (synth H) <= synth(insert X H)";
by (fast_tac (!claset addEs [impOfSubs synth_mono]) 1);
qed "synth_insert";

(** Idempotence and transitivity **)

goal thy "!!H. X: synth (synth H) ==> X: synth H";
by (etac synth.induct 1);
by (ALLGOALS Fast_tac);
qed "synth_synthE";
AddSEs [synth_synthE];

goal thy "synth (synth H) = synth H";
by (Fast_tac 1);
qed "synth_idem";

goal thy "!!H. [| X: synth G;  G <= synth H |] ==> X: synth H";
by (dtac synth_mono 1);
by (Fast_tac 1);
qed "synth_trans";

(*Cut; Lemma 2 of Lowe*)
goal thy "!!H. [| Y: synth (insert X H);  X: synth H |] ==> Y: synth H";
by (etac synth_trans 1);
by (Fast_tac 1);
qed "synth_cut";

goal thy "Agent A : synth H";
by (Fast_tac 1);
qed "Agent_synth";

goal thy "(Nonce N : synth H) = (Nonce N : H)";
by (Fast_tac 1);
qed "Nonce_synth_eq";

goal thy "(Key K : synth H) = (Key K : H)";
by (Fast_tac 1);
qed "Key_synth_eq";

goal thy "!!K. Key K ~: H ==> (Crypt X K : synth H) = (Crypt X K: H)";
by (Fast_tac 1);
qed "Crypt_synth_eq";

Addsimps [Agent_synth, Nonce_synth_eq, Key_synth_eq, Crypt_synth_eq];


goalw thy [keysFor_def]
    "keysFor (synth H) = keysFor H Un invKey``{K. Key K : H}";
by (Fast_tac 1);
qed "keysFor_synth";
Addsimps [keysFor_synth];


(*** Combinations of parts, analz and synth ***)

goal thy "parts (synth H) = parts H Un synth H";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS
    (best_tac (!claset addIs ((synth_increasing RS parts_mono RS subsetD)
                             ::parts.intrs))));
qed "parts_synth";
Addsimps [parts_synth];

goal thy "analz (synth H) = analz H Un synth H";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (best_tac
    (!claset addIs [synth_increasing RS analz_mono RS subsetD]) 5);
(*Strange that best_tac just can't hack this one...*)
by (ALLGOALS (deepen_tac (!claset addIs analz.intrs) 0));
qed "analz_synth";
Addsimps [analz_synth];

(*Hard to prove; still needed now that there's only one Spy?*)
goal thy "analz (UN i. synth (H i)) = \
\         analz (UN i. H i) Un (UN i. synth (H i))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (best_tac
    (!claset addEs [impOfSubs synth_increasing,
                    impOfSubs analz_mono]) 5);
by (Best_tac 1);
by (deepen_tac (!claset addIs [analz.Fst]) 0 1);
by (deepen_tac (!claset addIs [analz.Snd]) 0 1);
by (deepen_tac (!claset addSEs [analz.Decrypt]
                        addIs  [analz.Decrypt]) 0 1);
qed "analz_UN1_synth";
Addsimps [analz_UN1_synth];


(** For reasoning about the Fake rule in traces **)

goal thy "!!Y. X: G ==> parts(insert X H) <= parts G Un parts H";
by (rtac ([parts_mono, parts_Un_subset2] MRS subset_trans) 1);
by (Fast_tac 1);
qed "parts_insert_subset_Un";

(*More specifically for Fake*)
goal thy "!!H. X: synth (analz G) ==> \
\              parts (insert X H) <= synth (analz G) Un parts G Un parts H";
by (dtac parts_insert_subset_Un 1);
by (Full_simp_tac 1);
by (Deepen_tac 0 1);
qed "Fake_parts_insert";

goal thy
     "!!H. [| Crypt Y K : parts (insert X H);  X: synth (analz G);  \
\             Key K ~: analz G |]                                   \
\          ==> Crypt Y K : parts G Un parts H";
by (dtac (impOfSubs Fake_parts_insert) 1);
ba 1;
by (fast_tac (!claset addDs [impOfSubs analz_subset_parts]
                      addss (!simpset)) 1);
qed "Crypt_Fake_parts_insert";

goal thy "!!H. [| X: synth (analz G); G <= H |] ==> \
\              analz (insert X H) <= synth (analz H) Un analz H";
by (rtac subsetI 1);
by (subgoal_tac "x : analz (synth (analz H))" 1);
by (best_tac (!claset addIs [impOfSubs (analz_mono RS synth_mono)]
                      addSEs [impOfSubs analz_mono]) 2);
by (Full_simp_tac 1);
by (Fast_tac 1);
qed "Fake_analz_insert";

goal thy "(X: analz H & X: parts H) = (X: analz H)";
by (fast_tac (!claset addDs [impOfSubs analz_subset_parts]) 1);
val analz_conj_parts = result();

goal thy "(X: analz H | X: parts H) = (X: parts H)";
by (fast_tac (!claset addDs [impOfSubs analz_subset_parts]) 1);
val analz_disj_parts = result();

AddIffs [analz_conj_parts, analz_disj_parts];

(*Without this equation, other rules for synth and analz would yield
  redundant cases*)
goal thy "({|X,Y|} : synth (analz H)) = \
\         (X : synth (analz H) & Y : synth (analz H))";
by (Fast_tac 1);
qed "MPair_synth_analz";

AddIffs [MPair_synth_analz];


(*We do NOT want Crypt... messages broken up in protocols!!*)
Delrules partsEs;

