(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatypes of agents and messages;
Inductive relations "parts", "analz" and "synth"
*)


(*Eliminates a commonly-occurring expression*)
goal HOL.thy "~ (ALL x. x~=y)";
by (Blast_tac 1);
Addsimps [result()];

open Message;

AddIffs atomic.inject;
AddIffs msg.inject;

(*Holds because Friend is injective: thus cannot prove for all f*)
goal thy "(Friend x : Friend``A) = (x:A)";
by (Auto_tac());
qed "Friend_image_eq";
Addsimps [Friend_image_eq];


(** Inverse of keys **)

goal thy "!!K K'. (invKey K = invKey K') = (K=K')";
by Safe_tac;
by (rtac box_equals 1);
by (REPEAT (rtac invKey 2));
by (Asm_simp_tac 1);
qed "invKey_eq";

Addsimps [invKey, invKey_eq];


(**** keysFor operator ****)

goalw thy [keysFor_def] "keysFor {} = {}";
by (Blast_tac 1);
qed "keysFor_empty";

goalw thy [keysFor_def] "keysFor (H Un H') = keysFor H Un keysFor H'";
by (Blast_tac 1);
qed "keysFor_Un";

goalw thy [keysFor_def] "keysFor (UN i. H i) = (UN i. keysFor (H i))";
by (Blast_tac 1);
qed "keysFor_UN1";

(*Monotonicity*)
goalw thy [keysFor_def] "!!G H. G<=H ==> keysFor(G) <= keysFor(H)";
by (Blast_tac 1);
qed "keysFor_mono";

goalw thy [keysFor_def] "keysFor (insert (Agent A) H) = keysFor H";
by (Blast_tac 1);
qed "keysFor_insert_Agent";

goalw thy [keysFor_def] "keysFor (insert (Nonce N) H) = keysFor H";
by (Blast_tac 1);
qed "keysFor_insert_Nonce";

goalw thy [keysFor_def] "keysFor (insert (Number N) H) = keysFor H";
by (Blast_tac 1);
qed "keysFor_insert_Number";

goalw thy [keysFor_def] "keysFor (insert (Key K) H) = keysFor H";
by (Blast_tac 1);
qed "keysFor_insert_Key";

goalw thy [keysFor_def] "keysFor (insert (Hash X) H) = keysFor H";
by (Blast_tac 1);
qed "keysFor_insert_Hash";

goalw thy [keysFor_def] "keysFor (insert {|X,Y|} H) = keysFor H";
by (Blast_tac 1);
qed "keysFor_insert_MPair";

goalw thy [keysFor_def]
    "keysFor (insert (Crypt K X) H) = insert (invKey K) (keysFor H)";
by (Auto_tac());
qed "keysFor_insert_Crypt";

Addsimps [keysFor_empty, keysFor_Un, keysFor_UN1, 
          keysFor_insert_Agent, keysFor_insert_Nonce, 
	  keysFor_insert_Number, keysFor_insert_Key, 
          keysFor_insert_Hash, keysFor_insert_MPair, keysFor_insert_Crypt];
AddSEs [keysFor_Un RS equalityD1 RS subsetD RS UnE,
	keysFor_UN1 RS equalityD1 RS subsetD RS UN1_E];

goalw thy [keysFor_def] "keysFor (Key``E) = {}";
by (Auto_tac ());
qed "keysFor_image_Key";
Addsimps [keysFor_image_Key];

goalw thy [keysFor_def] "!!H. Crypt K X : H ==> invKey K : keysFor H";
by (Blast_tac 1);
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
by (Blast_tac 1);
qed "parts_increasing";

(*Monotonicity*)
goalw thy parts.defs "!!G H. G<=H ==> parts(G) <= parts(H)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "parts_mono";

val parts_insertI = impOfSubs (subset_insertI RS parts_mono);

goal thy "parts{} = {}";
by Safe_tac;
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
qed "parts_empty";
Addsimps [parts_empty];

goal thy "!!X. X: parts{} ==> P";
by (Asm_full_simp_tac 1);
qed "parts_emptyE";
AddSEs [parts_emptyE];

(*WARNING: loops if H = {Y}, therefore must not be repeated!*)
goal thy "!!H. X: parts H ==> EX Y:H. X: parts {Y}";
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
qed "parts_singleton";


(** Unions **)

goal thy "parts(G) Un parts(H) <= parts(G Un H)";
by (REPEAT (ares_tac [Un_least, parts_mono, Un_upper1, Un_upper2] 1));
val parts_Un_subset1 = result();

goal thy "parts(G Un H) <= parts(G) Un parts(H)";
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
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
by (ALLGOALS Blast_tac);
val parts_UN_subset2 = result();

goal thy "parts(UN x:A. H x) = (UN x:A. parts(H x))";
by (REPEAT (ares_tac [equalityI, parts_UN_subset1, parts_UN_subset2] 1));
qed "parts_UN";

goal thy "parts(UN x. H x) = (UN x. parts(H x))";
by (simp_tac (!simpset addsimps [UNION1_def, parts_UN]) 1);
qed "parts_UN1";

(*Added to simplify arguments to parts, analz and synth.
  NOTE: the UN versions are no longer used!*)
Addsimps [parts_Un, parts_UN, parts_UN1];
AddSEs [parts_Un RS equalityD1 RS subsetD RS UnE,
	parts_UN RS equalityD1 RS subsetD RS UN_E,
	parts_UN1 RS equalityD1 RS subsetD RS UN1_E];

goal thy "insert X (parts H) <= parts(insert X H)";
by (blast_tac (!claset addIs [impOfSubs parts_mono]) 1);
qed "parts_insert_subset";

(** Idempotence and transitivity **)

goal thy "!!H. X: parts (parts H) ==> X: parts H";
by (etac parts.induct 1);
by (ALLGOALS Blast_tac);
qed "parts_partsD";
AddSDs [parts_partsD];

goal thy "parts (parts H) = parts H";
by (Blast_tac 1);
qed "parts_idem";
Addsimps [parts_idem];

goal thy "!!H. [| X: parts G;  G <= parts H |] ==> X: parts H";
by (dtac parts_mono 1);
by (Blast_tac 1);
qed "parts_trans";

(*Cut*)
goal thy "!!H. [| Y: parts (insert X G);  X: parts H |] \
\              ==> Y: parts (G Un H)";
by (etac parts_trans 1);
by (Auto_tac());
qed "parts_cut";

goal thy "!!H. X: parts H ==> parts (insert X H) = parts H";
by (fast_tac (!claset addSDs [parts_cut]
                      addIs  [parts_insertI] 
                      addss (!simpset)) 1);
qed "parts_cut_eq";

Addsimps [parts_cut_eq];


(** Rewrite rules for pulling out atomic messages **)

fun parts_tac i =
  EVERY [rtac ([subsetI, parts_insert_subset] MRS equalityI) i,
         etac parts.induct i,
         REPEAT (Blast_tac i)];

goal thy "parts (insert (Agent agt) H) = insert (Agent agt) (parts H)";
by (parts_tac 1);
qed "parts_insert_Agent";

goal thy "parts (insert (Nonce N) H) = insert (Nonce N) (parts H)";
by (parts_tac 1);
qed "parts_insert_Nonce";

goal thy "parts (insert (Number N) H) = insert (Number N) (parts H)";
by (parts_tac 1);
qed "parts_insert_Number";

goal thy "parts (insert (Key K) H) = insert (Key K) (parts H)";
by (parts_tac 1);
qed "parts_insert_Key";

goal thy "parts (insert (Hash X) H) = insert (Hash X) (parts H)";
by (parts_tac 1);
qed "parts_insert_Hash";

goal thy "parts (insert (Crypt K X) H) = \
\         insert (Crypt K X) (parts (insert X H))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (Auto_tac());
by (etac parts.induct 1);
by (ALLGOALS (blast_tac (!claset addIs [parts.Body])));
qed "parts_insert_Crypt";

goal thy "parts (insert {|X,Y|} H) = \
\         insert {|X,Y|} (parts (insert X (insert Y H)))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (Auto_tac());
by (etac parts.induct 1);
by (ALLGOALS (blast_tac (!claset addIs [parts.Fst, parts.Snd])));
qed "parts_insert_MPair";

Addsimps [parts_insert_Agent, parts_insert_Nonce, 
	  parts_insert_Number, parts_insert_Key, 
          parts_insert_Hash, parts_insert_Crypt, parts_insert_MPair];


goal thy "parts (Key``N) = Key``N";
by (Auto_tac());
by (etac parts.induct 1);
by (Auto_tac());
qed "parts_image_Key";
Addsimps [parts_image_Key];


(*In any message, there is an upper bound N on its greatest nonce.*)
goal thy "EX N. ALL n. N<=n --> Nonce n ~: parts {msg}";
by (induct_tac "msg" 1);
by (induct_tac "atomic" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [exI, parts_insert2])));
(*MPair case: blast_tac works out the necessary sum itself!*)
by (blast_tac (!claset addSEs [add_leE]) 2);
(*Nonce case*)
by (res_inst_tac [("x","N + Suc nat")] exI 1);
by (fast_tac (!claset addSEs [add_leE] addaltern trans_tac) 1);
qed "msg_Nonce_supply";


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
by (Blast_tac 1);
qed "analz_increasing";

goal thy "analz H <= parts H";
by (rtac subsetI 1);
by (etac analz.induct 1);
by (ALLGOALS Blast_tac);
qed "analz_subset_parts";

bind_thm ("not_parts_not_analz", analz_subset_parts RS contra_subsetD);


goal thy "parts (analz H) = parts H";
by (rtac equalityI 1);
by (rtac (analz_subset_parts RS parts_mono RS subset_trans) 1);
by (Simp_tac 1);
by (blast_tac (!claset addIs [analz_increasing RS parts_mono RS subsetD]) 1);
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

val analz_insertI = impOfSubs (subset_insertI RS analz_mono);

(** General equational properties **)

goal thy "analz{} = {}";
by Safe_tac;
by (etac analz.induct 1);
by (ALLGOALS Blast_tac);
qed "analz_empty";
Addsimps [analz_empty];

(*Converse fails: we can analz more from the union than from the 
  separate parts, as a key in one might decrypt a message in the other*)
goal thy "analz(G) Un analz(H) <= analz(G Un H)";
by (REPEAT (ares_tac [Un_least, analz_mono, Un_upper1, Un_upper2] 1));
qed "analz_Un";

goal thy "insert X (analz H) <= analz(insert X H)";
by (blast_tac (!claset addIs [impOfSubs analz_mono]) 1);
qed "analz_insert";

(** Rewrite rules for pulling out atomic messages **)

fun analz_tac i =
  EVERY [rtac ([subsetI, analz_insert] MRS equalityI) i,
         etac analz.induct i,
         REPEAT (Blast_tac i)];

goal thy "analz (insert (Agent agt) H) = insert (Agent agt) (analz H)";
by (analz_tac 1);
qed "analz_insert_Agent";

goal thy "analz (insert (Nonce N) H) = insert (Nonce N) (analz H)";
by (analz_tac 1);
qed "analz_insert_Nonce";

goal thy "analz (insert (Number N) H) = insert (Number N) (analz H)";
by (analz_tac 1);
qed "analz_insert_Number";

goal thy "analz (insert (Hash X) H) = insert (Hash X) (analz H)";
by (analz_tac 1);
qed "analz_insert_Hash";

(*Can only pull out Keys if they are not needed to decrypt the rest*)
goalw thy [keysFor_def]
    "!!K. K ~: keysFor (analz H) ==>  \
\         analz (insert (Key K) H) = insert (Key K) (analz H)";
by (analz_tac 1);
qed "analz_insert_Key";

goal thy "analz (insert {|X,Y|} H) = \
\         insert {|X,Y|} (analz (insert X (insert Y H)))";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (Auto_tac());
by (etac analz.induct 1);
by (ALLGOALS (blast_tac (!claset addIs [analz.Fst, analz.Snd])));
qed "analz_insert_MPair";

(*Can pull out enCrypted message if the Key is not known*)
goal thy "!!H. Key (invKey K) ~: analz H ==>  \
\              analz (insert (Crypt K X) H) = \
\              insert (Crypt K X) (analz H)";
by (analz_tac 1);
qed "analz_insert_Crypt";

goal thy "!!H. Key (invKey K) : analz H ==>  \
\              analz (insert (Crypt K X) H) <= \
\              insert (Crypt K X) (analz (insert X H))";
by (rtac subsetI 1);
by (eres_inst_tac [("za","x")] analz.induct 1);
by (ALLGOALS (Blast_tac));
val lemma1 = result();

goal thy "!!H. Key (invKey K) : analz H ==>  \
\              insert (Crypt K X) (analz (insert X H)) <= \
\              analz (insert (Crypt K X) H)";
by (Auto_tac());
by (eres_inst_tac [("za","x")] analz.induct 1);
by (Auto_tac());
by (blast_tac (!claset addIs [analz_insertI, analz.Decrypt]) 1);
val lemma2 = result();

goal thy "!!H. Key (invKey K) : analz H ==>  \
\              analz (insert (Crypt K X) H) = \
\              insert (Crypt K X) (analz (insert X H))";
by (REPEAT (ares_tac [equalityI, lemma1, lemma2] 1));
qed "analz_insert_Decrypt";

(*Case analysis: either the message is secure, or it is not!
  Effective, but can cause subgoals to blow up!
  Use with expand_if;  apparently split_tac does not cope with patterns
  such as "analz (insert (Crypt K X) H)" *)
goal thy "analz (insert (Crypt K X) H) =                \
\         (if (Key (invKey K) : analz H)                \
\          then insert (Crypt K X) (analz (insert X H)) \
\          else insert (Crypt K X) (analz H))";
by (case_tac "Key (invKey K)  : analz H " 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [analz_insert_Crypt, 
                                               analz_insert_Decrypt])));
qed "analz_Crypt_if";

Addsimps [analz_insert_Agent, analz_insert_Nonce, 
	  analz_insert_Number, analz_insert_Key, 
          analz_insert_Hash, analz_insert_MPair, analz_Crypt_if];

(*This rule supposes "for the sake of argument" that we have the key.*)
goal thy  "analz (insert (Crypt K X) H) <=  \
\          insert (Crypt K X) (analz (insert X H))";
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
by (ALLGOALS Blast_tac);
qed "analz_analzD";
AddSDs [analz_analzD];

goal thy "analz (analz H) = analz H";
by (Blast_tac 1);
qed "analz_idem";
Addsimps [analz_idem];

goal thy "!!H. [| X: analz G;  G <= analz H |] ==> X: analz H";
by (dtac analz_mono 1);
by (Blast_tac 1);
qed "analz_trans";

(*Cut; Lemma 2 of Lowe*)
goal thy "!!H. [| Y: analz (insert X H);  X: analz H |] ==> Y: analz H";
by (etac analz_trans 1);
by (Blast_tac 1);
qed "analz_cut";

(*Cut can be proved easily by induction on
   "!!H. Y: analz (insert X H) ==> X: analz H --> Y: analz H"
*)

(*This rewrite rule helps in the simplification of messages that involve
  the forwarding of unknown components (X).  Without it, removing occurrences
  of X can be very complicated. *)
goal thy "!!H. X: analz H ==> analz (insert X H) = analz H";
by (blast_tac (!claset addIs [analz_cut, analz_insertI]) 1);
qed "analz_insert_eq";


(** A congruence rule for "analz" **)

goal thy "!!H. [| analz G <= analz G'; analz H <= analz H' \
\              |] ==> analz (G Un H) <= analz (G' Un H')";
by (Clarify_tac 1);
by (etac analz.induct 1);
by (ALLGOALS (best_tac (!claset addIs [analz_mono RS subsetD])));
qed "analz_subset_cong";

goal thy "!!H. [| analz G = analz G'; analz H = analz H' \
\              |] ==> analz (G Un H) = analz (G' Un H')";
by (REPEAT_FIRST (ares_tac [equalityI, analz_subset_cong]
          ORELSE' etac equalityE));
qed "analz_cong";


goal thy "!!H. analz H = analz H' ==> analz(insert X H) = analz(insert X H')";
by (asm_simp_tac (!simpset addsimps [insert_def] delsimps [singleton_conv]
                           setloop (rtac analz_cong)) 1);
qed "analz_insert_cong";

(*If there are no pairs or encryptions then analz does nothing*)
goal thy "!!H. [| ALL X Y. {|X,Y|} ~: H;  ALL X K. Crypt K X ~: H |] ==> \
\         analz H = H";
by Safe_tac;
by (etac analz.induct 1);
by (ALLGOALS Blast_tac);
qed "analz_trivial";

(*Helps to prove Fake cases*)
goal thy "!!X. X: analz (UN i. analz (H i)) ==> X: analz (UN i. H i)";
by (etac analz.induct 1);
by (ALLGOALS (blast_tac (!claset addIs [impOfSubs analz_mono])));
val lemma = result();

goal thy "analz (UN i. analz (H i)) = analz (UN i. H i)";
by (blast_tac (!claset addIs [lemma, impOfSubs analz_mono]) 1);
qed "analz_UN_analz";
Addsimps [analz_UN_analz];


(**** Inductive relation "synth" ****)

AddIs  synth.intrs;

(*Can only produce a nonce or key if it is already known,
  but can synth a pair or encryption from its components...*)
val mk_cases = synth.mk_cases (atomic.simps @ msg.simps);

(*NO Agent_synth, as any Agent name can be synthesized.  Ditto for Number*)
val Nonce_synth = mk_cases "Nonce n : synth H";
val Key_synth   = mk_cases "Key K : synth H";
val Hash_synth  = mk_cases "Hash X : synth H";
val MPair_synth = mk_cases "{|X,Y|} : synth H";
val Crypt_synth = mk_cases "Crypt K X : synth H";

AddSEs [Nonce_synth, Key_synth, Hash_synth, MPair_synth, Crypt_synth];

goal thy "H <= synth(H)";
by (Blast_tac 1);
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
by (blast_tac (!claset addIs [impOfSubs synth_mono]) 1);
qed "synth_insert";

(** Idempotence and transitivity **)

goal thy "!!H. X: synth (synth H) ==> X: synth H";
by (etac synth.induct 1);
by (ALLGOALS Blast_tac);
qed "synth_synthD";
AddSDs [synth_synthD];

goal thy "synth (synth H) = synth H";
by (Blast_tac 1);
qed "synth_idem";

goal thy "!!H. [| X: synth G;  G <= synth H |] ==> X: synth H";
by (dtac synth_mono 1);
by (Blast_tac 1);
qed "synth_trans";

(*Cut; Lemma 2 of Lowe*)
goal thy "!!H. [| Y: synth (insert X H);  X: synth H |] ==> Y: synth H";
by (etac synth_trans 1);
by (Blast_tac 1);
qed "synth_cut";

goal thy "Agent A : synth H";
by (Blast_tac 1);
qed "Agent_synth";

goal thy "Number n : synth H";
by (Blast_tac 1);
qed "Number_synth";

goal thy "(Nonce N : synth H) = (Nonce N : H)";
by (Blast_tac 1);
qed "Nonce_synth_eq";

goal thy "(Key K : synth H) = (Key K : H)";
by (Blast_tac 1);
qed "Key_synth_eq";

goal thy "!!K. Key K ~: H ==> (Crypt K X : synth H) = (Crypt K X : H)";
by (Blast_tac 1);
qed "Crypt_synth_eq";

Addsimps [Agent_synth, Number_synth, 
	  Nonce_synth_eq, Key_synth_eq, Crypt_synth_eq];


goalw thy [keysFor_def]
    "keysFor (synth H) = keysFor H Un invKey``{K. Key K : H}";
by (Blast_tac 1);
qed "keysFor_synth";
Addsimps [keysFor_synth];


(*** Combinations of parts, analz and synth ***)

goal thy "parts (synth H) = parts H Un synth H";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac parts.induct 1);
by (ALLGOALS
    (blast_tac (!claset addIs ((synth_increasing RS parts_mono RS subsetD)
                             ::parts.intrs))));
qed "parts_synth";
Addsimps [parts_synth];

goal thy "analz (analz G Un H) = analz (G Un H)";
by (REPEAT_FIRST (resolve_tac [equalityI, analz_subset_cong]));
by (ALLGOALS Simp_tac);
qed "analz_analz_Un";

goal thy "analz (synth G Un H) = analz (G Un H) Un synth G";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac analz.induct 1);
by (blast_tac (!claset addIs [impOfSubs analz_mono]) 5);
by (ALLGOALS (blast_tac (!claset addIs analz.intrs)));
qed "analz_synth_Un";

goal thy "analz (synth H) = analz H Un synth H";
by (cut_inst_tac [("H","{}")] analz_synth_Un 1);
by (Full_simp_tac 1);
qed "analz_synth";
Addsimps [analz_analz_Un, analz_synth_Un, analz_synth];


(** For reasoning about the Fake rule in traces **)

goal thy "!!Y. X: G ==> parts(insert X H) <= parts G Un parts H";
by (rtac ([parts_mono, parts_Un_subset2] MRS subset_trans) 1);
by (Blast_tac 1);
qed "parts_insert_subset_Un";

(*More specifically for Fake*)
goal thy "!!H. X: synth (analz G) ==> \
\              parts (insert X H) <= synth (analz G) Un parts G Un parts H";
by (dtac parts_insert_subset_Un 1);
by (Full_simp_tac 1);
by (Blast_tac 1);
qed "Fake_parts_insert";

goal thy
     "!!H. [| Crypt K Y : parts (insert X H);  X: synth (analz G);  \
\             Key K ~: analz G |]                                   \
\          ==> Crypt K Y : parts G Un parts H";
by (dtac (impOfSubs Fake_parts_insert) 1);
by (assume_tac 1);
by (blast_tac (!claset addDs [impOfSubs analz_subset_parts]) 1);
qed "Crypt_Fake_parts_insert";

goal thy "!!H. X: synth (analz G) ==> \
\              analz (insert X H) <= synth (analz G) Un analz (G Un H)";
by (rtac subsetI 1);
by (subgoal_tac "x : analz (synth (analz G) Un H)" 1);
by (blast_tac (!claset addIs [impOfSubs analz_mono,
			      impOfSubs (analz_mono RS synth_mono)]) 2);
by (Full_simp_tac 1);
by (Blast_tac 1);
qed "Fake_analz_insert";

goal thy "(X: analz H & X: parts H) = (X: analz H)";
by (blast_tac (!claset addIs [impOfSubs analz_subset_parts]) 1);
val analz_conj_parts = result();

goal thy "(X: analz H | X: parts H) = (X: parts H)";
by (blast_tac (!claset addIs [impOfSubs analz_subset_parts]) 1);
val analz_disj_parts = result();

AddIffs [analz_conj_parts, analz_disj_parts];

(*Without this equation, other rules for synth and analz would yield
  redundant cases*)
goal thy "({|X,Y|} : synth (analz H)) = \
\         (X : synth (analz H) & Y : synth (analz H))";
by (Blast_tac 1);
qed "MPair_synth_analz";

AddIffs [MPair_synth_analz];

goal thy "!!K. [| Key K : analz H;  Key (invKey K) : analz H |] \
\              ==> (Crypt K X : synth (analz H)) = (X : synth (analz H))";
by (Blast_tac 1);
qed "Crypt_synth_analz";


goal thy "!!K. X ~: synth (analz H) \
\   ==> (Hash{|X,Y|} : synth (analz H)) = (Hash{|X,Y|} : analz H)";
by (Blast_tac 1);
qed "Hash_synth_analz";
Addsimps [Hash_synth_analz];


(**** HPair: a combination of Hash and MPair ****)

(*** Freeness ***)

goalw thy [HPair_def] "Agent A ~= Hash[X] Y";
by (Simp_tac 1);
qed "Agent_neq_HPair";

goalw thy [HPair_def] "Nonce N ~= Hash[X] Y";
by (Simp_tac 1);
qed "Nonce_neq_HPair";

goalw thy [HPair_def] "Number N ~= Hash[X] Y";
by (Simp_tac 1);
qed "Number_neq_HPair";

goalw thy [HPair_def] "Key K ~= Hash[X] Y";
by (Simp_tac 1);
qed "Key_neq_HPair";

goalw thy [HPair_def] "Hash Z ~= Hash[X] Y";
by (Simp_tac 1);
qed "Hash_neq_HPair";

goalw thy [HPair_def] "Crypt K X' ~= Hash[X] Y";
by (Simp_tac 1);
qed "Crypt_neq_HPair";

val HPair_neqs = [Agent_neq_HPair, Nonce_neq_HPair, Number_neq_HPair, 
                  Key_neq_HPair, Hash_neq_HPair, Crypt_neq_HPair];

AddIffs HPair_neqs;
AddIffs (HPair_neqs RL [not_sym]);

goalw thy [HPair_def] "(Hash[X'] Y' = Hash[X] Y) = (X' = X & Y'=Y)";
by (Simp_tac 1);
qed "HPair_eq";

goalw thy [HPair_def] "({|X',Y'|} = Hash[X] Y) = (X' = Hash{|X,Y|} & Y'=Y)";
by (Simp_tac 1);
qed "MPair_eq_HPair";

goalw thy [HPair_def] "(Hash[X] Y = {|X',Y'|}) = (X' = Hash{|X,Y|} & Y'=Y)";
by (Auto_tac());
qed "HPair_eq_MPair";

AddIffs [HPair_eq, MPair_eq_HPair, HPair_eq_MPair];


(*** Specialized laws, proved in terms of those for Hash and MPair ***)

goalw thy [HPair_def] "keysFor (insert (Hash[X] Y) H) = keysFor H";
by (Simp_tac 1);
qed "keysFor_insert_HPair";

goalw thy [HPair_def]
    "parts (insert (Hash[X] Y) H) = \
\    insert (Hash[X] Y) (insert (Hash{|X,Y|}) (parts (insert Y H)))";
by (Simp_tac 1);
qed "parts_insert_HPair";

goalw thy [HPair_def]
    "analz (insert (Hash[X] Y) H) = \
\    insert (Hash[X] Y) (insert (Hash{|X,Y|}) (analz (insert Y H)))";
by (Simp_tac 1);
qed "analz_insert_HPair";

goalw thy [HPair_def] "!!H. X ~: synth (analz H) \
\   ==> (Hash[X] Y : synth (analz H)) = \
\       (Hash {|X, Y|} : analz H & Y : synth (analz H))";
by (Simp_tac 1);
by (Blast_tac 1);
qed "HPair_synth_analz";

Addsimps [keysFor_insert_HPair, parts_insert_HPair, analz_insert_HPair, 
          HPair_synth_analz, HPair_synth_analz];


(*We do NOT want Crypt... messages broken up in protocols!!*)
Delrules partsEs;


(** Rewrites to push in Key and Crypt messages, so that other messages can
    be pulled out using the analz_insert rules **)

fun insComm thy x y = read_instantiate_sg (sign_of thy) [("x",x), ("y",y)] 
                          insert_commute;

val pushKeys = map (insComm thy "Key ?K") 
                   ["Agent ?C", "Nonce ?N", "Number ?N", 
		    "Hash ?X", "MPair ?X ?Y", "Crypt ?X ?K'"];

val pushCrypts = map (insComm thy "Crypt ?X ?K") 
                     ["Agent ?C", "Nonce ?N", "Number ?N", 
		      "Hash ?X'", "MPair ?X' ?Y"];

(*Cannot be added with Addsimps -- we don't always want to re-order messages*)
val pushes = pushKeys@pushCrypts;


(*** Tactics useful for many protocol proofs ***)

(*Prove base case (subgoal i) and simplify others.  A typical base case
  concerns  Crypt K X ~: Key``shrK``bad  and cannot be proved by rewriting
  alone.*)
fun prove_simple_subgoals_tac i = 
    fast_tac (!claset addss (!simpset)) i THEN
    ALLGOALS Asm_simp_tac;

fun Fake_parts_insert_tac i = 
    blast_tac (!claset addDs [impOfSubs analz_subset_parts,
			      impOfSubs Fake_parts_insert]) i;

(*Apply rules to break down assumptions of the form
  Y : parts(insert X H)  and  Y : analz(insert X H)
*)
val Fake_insert_tac = 
    dresolve_tac [impOfSubs Fake_analz_insert,
                  impOfSubs Fake_parts_insert] THEN'
    eresolve_tac [asm_rl, synth.Inj];

fun Fake_insert_simp_tac i = 
    REPEAT (Fake_insert_tac i) THEN Asm_full_simp_tac i;


(*Analysis of Fake cases.  Also works for messages that forward unknown parts,
  but this application is no longer necessary if analz_insert_eq is used.
  Abstraction over i is ESSENTIAL: it delays the dereferencing of claset
  DEPENDS UPON "X" REFERRING TO THE FRADULENT MESSAGE *)
fun spy_analz_tac i =
  DETERM
   (SELECT_GOAL
     (EVERY 
      [  (*push in occurrences of X...*)
       (REPEAT o CHANGED)
           (res_inst_tac [("x1","X")] (insert_commute RS ssubst) 1),
       (*...allowing further simplifications*)
       simp_tac (!simpset addsplits [expand_if]) 1,
       REPEAT (FIRSTGOAL (resolve_tac [allI,impI,notI,conjI,iffI])),
       DEPTH_SOLVE 
         (Fake_insert_simp_tac 1
          THEN
          IF_UNSOLVED (Blast.depth_tac
		       (!claset addIs [analz_insertI,
				       impOfSubs analz_subset_parts]) 4 1))
       ]) i);

(** Useful in many uniqueness proofs **)
fun ex_strip_tac i = REPEAT (swap_res_tac [exI, conjI] i) THEN 
                     assume_tac (i+1);

(*Apply the EX-ALL quantifification to prove uniqueness theorems in 
  their standard form*)
fun prove_unique_tac lemma = 
  EVERY' [dtac lemma,
          REPEAT o (mp_tac ORELSE' eresolve_tac [asm_rl,exE]),
          (*Duplicate the assumption*)
          forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl,
          Blast.depth_tac (!claset addSDs [spec]) 0];


(*Needed occasionally with spy_analz_tac, e.g. in analz_insert_Key_newK*)
goal Set.thy "A Un (B Un A) = B Un A";
by (Blast_tac 1);
val Un_absorb3 = result();
Addsimps [Un_absorb3];

(*By default only o_apply is built-in.  But in the presence of eta-expansion
  this means that some terms displayed as (f o g) will be rewritten, and others
  will not!*)
Addsimps [o_def];
