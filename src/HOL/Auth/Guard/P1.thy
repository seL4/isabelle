(******************************************************************************
from G. Karjoth, N. Asokan and C. Gulcu
"Protecting the computation results of free-roaming agents"
Mobiles Agents 1998, LNCS 1477

date: february 2002
author: Frederic Blanqui
email: blanqui@lri.fr
webpage: http://www.lri.fr/~blanqui/

University of Cambridge, Computer Laboratory
William Gates Building, JJ Thomson Avenue
Cambridge CB3 0FD, United Kingdom
******************************************************************************)

header{*Protocol P1*}

theory P1 = Guard_Public + List_Msg:

subsection{*Protocol Definition*}

(******************************************************************************

the contents of the messages are not completely specified in the paper
we assume that the user sends his request and his itinerary in the clear

we will adopt the following format for messages: {|A,r,I,L|}
A: originator (agent)
r: request (number)
I: next shops (agent list)
L: collected offers (offer list)

in the paper, the authors use nonces r_i to add redundancy in the offer
in order to make it safer against dictionary attacks
it is not necessary in our modelization since crypto is assumed to be strong
(Crypt in injective)
******************************************************************************)

subsubsection{*offer chaining:
B chains his offer for A with the head offer of L for sending it to C*}

constdefs chain :: "agent => nat => agent => msg => agent => msg"
"chain B ofr A L C ==
let m1= Crypt (pubK A) (Nonce ofr) in
let m2= Hash {|head L, Agent C|} in
sign B {|m1,m2|}"

declare Let_def [simp]

lemma chain_inj [iff]: "(chain B ofr A L C = chain B' ofr' A' L' C')
= (B=B' & ofr=ofr' & A=A' & head L = head L' & C=C')"
by (auto simp: chain_def Let_def)

lemma Nonce_in_chain [iff]: "Nonce ofr:parts {chain B ofr A L C}"
by (auto simp: chain_def sign_def)

subsubsection{*agent whose key is used to sign an offer*}

consts shop :: "msg => msg"

recdef shop "measure size"
"shop {|B,X,Crypt K H|} = Agent (agt K)"

lemma shop_chain [simp]: "shop (chain B ofr A L C) = Agent B"
by (simp add: chain_def sign_def)

subsubsection{*nonce used in an offer*}

consts nonce :: "msg => msg"

recdef nonce "measure size"
"nonce {|B,{|Crypt K ofr,m2|},CryptH|} = ofr"

lemma nonce_chain [simp]: "nonce (chain B ofr A L C) = Nonce ofr"
by (simp add: chain_def sign_def)

subsubsection{*next shop*}

consts next_shop :: "msg => agent"

recdef next_shop "measure size"
"next_shop {|B,{|m1,Hash{|headL,Agent C|}|},CryptH|} = C"

lemma next_shop_chain [iff]: "next_shop (chain B ofr A L C) = C"
by (simp add: chain_def sign_def)

subsubsection{*anchor of the offer list*}

constdefs anchor :: "agent => nat => agent => msg"
"anchor A n B == chain A n A (cons nil nil) B"

lemma anchor_inj [iff]: "(anchor A n B = anchor A' n' B')
= (A=A' & n=n' & B=B')"
by (auto simp: anchor_def)

lemma Nonce_in_anchor [iff]: "Nonce n:parts {anchor A n B}"
by (auto simp: anchor_def)

lemma shop_anchor [simp]: "shop (anchor A n B) = Agent A"
by (simp add: anchor_def)

lemma nonce_anchor [simp]: "nonce (anchor A n B) = Nonce n"
by (simp add: anchor_def)

lemma next_shop_anchor [iff]: "next_shop (anchor A n B) = B"
by (simp add: anchor_def)

subsubsection{*request event*}

constdefs reqm :: "agent => nat => nat => msg => agent => msg"
"reqm A r n I B == {|Agent A, Number r, cons (Agent A) (cons (Agent B) I),
cons (anchor A n B) nil|}"

lemma reqm_inj [iff]: "(reqm A r n I B = reqm A' r' n' I' B')
= (A=A' & r=r' & n=n' & I=I' & B=B')"
by (auto simp: reqm_def)

lemma Nonce_in_reqm [iff]: "Nonce n:parts {reqm A r n I B}"
by (auto simp: reqm_def)

constdefs req :: "agent => nat => nat => msg => agent => event"
"req A r n I B == Says A B (reqm A r n I B)"

lemma req_inj [iff]: "(req A r n I B = req A' r' n' I' B')
= (A=A' & r=r' & n=n' & I=I' & B=B')"
by (auto simp: req_def)

subsubsection{*propose event*}

constdefs prom :: "agent => nat => agent => nat => msg => msg =>
msg => agent => msg"
"prom B ofr A r I L J C == {|Agent A, Number r,
app (J, del (Agent B, I)), cons (chain B ofr A L C) L|}"

lemma prom_inj [dest]: "prom B ofr A r I L J C
= prom B' ofr' A' r' I' L' J' C'
==> B=B' & ofr=ofr' & A=A' & r=r' & L=L' & C=C'"
by (auto simp: prom_def)

lemma Nonce_in_prom [iff]: "Nonce ofr:parts {prom B ofr A r I L J C}"
by (auto simp: prom_def)

constdefs pro :: "agent => nat => agent => nat => msg => msg =>
msg => agent => event"
"pro B ofr A r I L J C == Says B C (prom B ofr A r I L J C)"

lemma pro_inj [dest]: "pro B ofr A r I L J C = pro B' ofr' A' r' I' L' J' C'
==> B=B' & ofr=ofr' & A=A' & r=r' & L=L' & C=C'"
by (auto simp: pro_def dest: prom_inj)

subsubsection{*protocol*}

consts p1 :: "event list set"

inductive p1
intros

Nil: "[]:p1"

Fake: "[| evsf:p1; X:synth (analz (spies evsf)) |] ==> Says Spy B X # evsf : p1"

Request: "[| evsr:p1; Nonce n ~:used evsr; I:agl |] ==> req A r n I B # evsr : p1"

Propose: "[| evsp:p1; Says A' B {|Agent A,Number r,I,cons M L|}:set evsp;
I:agl; J:agl; isin (Agent C, app (J, del (Agent B, I)));
Nonce ofr ~:used evsp |] ==> pro B ofr A r I (cons M L) J C # evsp : p1"

subsubsection{*Composition of Traces*}

lemma "evs':p1 ==> 
       evs:p1 & (ALL n. Nonce n:used evs' --> Nonce n ~:used evs) --> 
       evs'@evs : p1"
apply (erule p1.induct, safe) 
apply (simp_all add: used_ConsI) 
apply (erule p1.Fake, erule synth_sub, rule analz_mono, rule knows_sub_app)
apply (erule p1.Request, safe, simp_all add: req_def, force) 
apply (erule_tac A'=A' in p1.Propose, simp_all) 
apply (drule_tac x=ofr in spec, simp add: pro_def, blast) 
apply (erule_tac A'=A' in p1.Propose, auto simp: pro_def)
done

subsubsection{*Valid Offer Lists*}

consts valid :: "agent => nat => agent => msg set"

inductive "valid A n B"
intros
Request [intro]: "cons (anchor A n B) nil:valid A n B"

Propose [intro]: "L:valid A n B
==> cons (chain (next_shop (head L)) ofr A L C) L:valid A n B"

subsubsection{*basic properties of valid*}

lemma valid_not_empty: "L:valid A n B ==> EX M L'. L = cons M L'"
by (erule valid.cases, auto)

lemma valid_pos_len: "L:valid A n B ==> 0 < len L"
by (erule valid.induct, auto)

subsubsection{*offers of an offer list*}

constdefs offer_nonces :: "msg => msg set"
"offer_nonces L == {X. X:parts {L} & (EX n. X = Nonce n)}"

subsubsection{*the originator can get the offers*}

lemma "L:valid A n B ==> offer_nonces L <= analz (insert L (initState A))"
by (erule valid.induct, auto simp: anchor_def chain_def sign_def
offer_nonces_def initState.simps)

subsubsection{*list of offers*}

consts offers :: "msg => msg"

recdef offers "measure size"
"offers (cons M L) = cons {|shop M, nonce M|} (offers L)"
"offers other = nil"

subsubsection{*list of agents whose keys are used to sign a list of offers*}

consts shops :: "msg => msg"

recdef shops "measure size"
"shops (cons M L) = cons (shop M) (shops L)"
"shops other = other"

lemma shops_in_agl: "L:valid A n B ==> shops L:agl"
by (erule valid.induct, auto simp: anchor_def chain_def sign_def)

subsubsection{*builds a trace from an itinerary*}

consts offer_list :: "agent * nat * agent * msg * nat => msg"

recdef offer_list "measure (%(A,n,B,I,ofr). size I)"
"offer_list (A,n,B,nil,ofr) = cons (anchor A n B) nil"
"offer_list (A,n,B,cons (Agent C) I,ofr) = (
let L = offer_list (A,n,B,I,Suc ofr) in
cons (chain (next_shop (head L)) ofr A L C) L)"

lemma "I:agl ==> ALL ofr. offer_list (A,n,B,I,ofr):valid A n B"
by (erule agl.induct, auto)

consts trace :: "agent * nat * agent * nat * msg * msg * msg
=> event list"

recdef trace "measure (%(B,ofr,A,r,I,L,K). size K)"
"trace (B,ofr,A,r,I,L,nil) = []"
"trace (B,ofr,A,r,I,L,cons (Agent D) K) = (
let C = (if K=nil then B else agt_nb (head K)) in
let I' = (if K=nil then cons (Agent A) (cons (Agent B) I)
          else cons (Agent A) (app (I, cons (head K) nil))) in
let I'' = app (I, cons (head K) nil) in
pro C (Suc ofr) A r I' L nil D
# trace (B,Suc ofr,A,r,I'',tail L,K))"

constdefs trace' :: "agent => nat => nat => msg => agent => nat => event list"
"trace' A r n I B ofr == (
let AI = cons (Agent A) I in
let L = offer_list (A,n,B,AI,ofr) in
trace (B,ofr,A,r,nil,L,AI))"

declare trace'_def [simp]

subsubsection{*there is a trace in which the originator receives a valid answer*}

lemma p1_not_empty: "evs:p1 ==> req A r n I B:set evs -->
(EX evs'. evs'@evs:p1 & pro B' ofr A r I' L J A:set evs' & L:valid A n B)"
oops


subsection{*properties of protocol P1*}

text{*publicly verifiable forward integrity:
anyone can verify the validity of an offer list*}

subsubsection{*strong forward integrity:
except the last one, no offer can be modified*}

lemma strong_forward_integrity: "ALL L. Suc i < len L
--> L:valid A n B & repl (L,Suc i,M):valid A n B --> M = ith (L,Suc i)"
apply (induct i)
(* i = 0 *)
apply clarify
apply (frule len_not_empty, clarsimp)
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|x,xa,l'a|}:valid A n B")
apply (ind_cases "{|x,M,l'a|}:valid A n B")
apply (simp add: chain_def)
(* i > 0 *)
apply clarify
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|x,repl(l',Suc na,M)|}:valid A n B")
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|x,l'|}:valid A n B")
by (drule_tac x=l' in spec, simp, blast)

subsubsection{*insertion resilience:
except at the beginning, no offer can be inserted*}

lemma chain_isnt_head [simp]: "L:valid A n B ==>
head L ~= chain (next_shop (head L)) ofr A L C"
by (erule valid.induct, auto simp: chain_def sign_def anchor_def)

lemma insertion_resilience: "ALL L. L:valid A n B --> Suc i < len L
--> ins (L,Suc i,M) ~:valid A n B"
apply (induct i)
(* i = 0 *)
apply clarify
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|x,l'|}:valid A n B", simp)
apply (ind_cases "{|x,M,l'|}:valid A n B", clarsimp)
apply (ind_cases "{|head l',l'|}:valid A n B", simp, simp)
(* i > 0 *)
apply clarify
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|x,l'|}:valid A n B")
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|x,ins(l',Suc na,M)|}:valid A n B")
apply (frule len_not_empty, clarsimp)
by (drule_tac x=l' in spec, clarsimp)

subsubsection{*truncation resilience:
only shop i can truncate at offer i*}

lemma truncation_resilience: "ALL L. L:valid A n B --> Suc i < len L
--> cons M (trunc (L,Suc i)):valid A n B --> shop M = shop (ith (L,i))"
apply (induct i)
(* i = 0 *)
apply clarify
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|x,l'|}:valid A n B")
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|M,l'|}:valid A n B")
apply (frule len_not_empty, clarsimp, simp)
(* i > 0 *)
apply clarify
apply (frule len_not_empty, clarsimp)
apply (ind_cases "{|x,l'|}:valid A n B")
apply (frule len_not_empty, clarsimp)
by (drule_tac x=l' in spec, clarsimp)

subsubsection{*declarations for tactics*}

declare knows_Spy_partsEs [elim]
declare Fake_parts_insert [THEN subsetD, dest]
declare initState.simps [simp del]

subsubsection{*get components of a message*}

lemma get_ML [dest]: "Says A' B {|A,r,I,M,L|}:set evs ==>
M:parts (spies evs) & L:parts (spies evs)"
by blast

subsubsection{*general properties of p1*}

lemma reqm_neq_prom [iff]:
"reqm A r n I B ~= prom B' ofr A' r' I' (cons M L) J C"
by (auto simp: reqm_def prom_def)

lemma prom_neq_reqm [iff]:
"prom B' ofr A' r' I' (cons M L) J C ~= reqm A r n I B"
by (auto simp: reqm_def prom_def)

lemma req_neq_pro [iff]: "req A r n I B ~= pro B' ofr A' r' I' (cons M L) J C"
by (auto simp: req_def pro_def)

lemma pro_neq_req [iff]: "pro B' ofr A' r' I' (cons M L) J C ~= req A r n I B"
by (auto simp: req_def pro_def)

lemma p1_has_no_Gets: "evs:p1 ==> ALL A X. Gets A X ~:set evs"
by (erule p1.induct, auto simp: req_def pro_def)

lemma p1_is_Gets_correct [iff]: "Gets_correct p1"
by (auto simp: Gets_correct_def dest: p1_has_no_Gets)

lemma p1_is_one_step [iff]: "one_step p1"
by (unfold one_step_def, clarify, ind_cases "ev#evs:p1", auto)

lemma p1_has_only_Says' [rule_format]: "evs:p1 ==>
ev:set evs --> (EX A B X. ev=Says A B X)"
by (erule p1.induct, auto simp: req_def pro_def)

lemma p1_has_only_Says [iff]: "has_only_Says p1"
by (auto simp: has_only_Says_def dest: p1_has_only_Says')

lemma p1_is_regular [iff]: "regular p1"
apply (simp only: regular_def, clarify)
apply (erule_tac p1.induct)
apply (simp_all add: initState.simps knows.simps pro_def prom_def
                     req_def reqm_def anchor_def chain_def sign_def)
by (auto dest: no_Key_in_agl no_Key_in_appdel parts_trans)

subsubsection{*private keys are safe*}

lemma priK_parts_Friend_imp_bad [rule_format,dest]:
     "[| evs:p1; Friend B ~= A |]
      ==> (Key (priK A):parts (knows (Friend B) evs)) --> (A:bad)"
apply (erule p1.induct)
apply (simp_all add: initState.simps knows.simps pro_def prom_def
                req_def reqm_def anchor_def chain_def sign_def, blast) 
apply (blast dest: no_Key_in_agl)
apply (auto del: parts_invKey disjE  dest: parts_trans
            simp add: no_Key_in_appdel)
done

lemma priK_analz_Friend_imp_bad [rule_format,dest]:
     "[| evs:p1; Friend B ~= A |]
==> (Key (priK A):analz (knows (Friend B) evs)) --> (A:bad)"
by auto

lemma priK_notin_knows_max_Friend: "[| evs:p1; A ~:bad; A ~= Friend C |]
==> Key (priK A) ~:analz (knows_max (Friend C) evs)"
apply (rule not_parts_not_analz, simp add: knows_max_def, safe)
apply (drule_tac H="spies' evs" in parts_sub)
apply (rule_tac p=p1 in knows_max'_sub_spies', simp+)
apply (drule_tac H="spies evs" in parts_sub)
by (auto dest: knows'_sub_knows [THEN subsetD] priK_notin_initState_Friend)

subsubsection{*general guardedness properties*}

lemma agl_guard [intro]: "I:agl ==> I:guard n Ks"
by (erule agl.induct, auto)

lemma Says_to_knows_max'_guard: "[| Says A' C {|A'',r,I,L|}:set evs;
Guard n Ks (knows_max' C evs) |] ==> L:guard n Ks"
by (auto dest: Says_to_knows_max')

lemma Says_from_knows_max'_guard: "[| Says C A' {|A'',r,I,L|}:set evs;
Guard n Ks (knows_max' C evs) |] ==> L:guard n Ks"
by (auto dest: Says_from_knows_max')

lemma Says_Nonce_not_used_guard: "[| Says A' B {|A'',r,I,L|}:set evs;
Nonce n ~:used evs |] ==> L:guard n Ks"
by (drule not_used_not_parts, auto)

subsubsection{*guardedness of messages*}

lemma chain_guard [iff]: "chain B ofr A L C:guard n {priK A}"
by (case_tac "ofr=n", auto simp: chain_def sign_def)

lemma chain_guard_Nonce_neq [intro]: "n ~= ofr
==> chain B ofr A' L C:guard n {priK A}"
by (auto simp: chain_def sign_def)

lemma anchor_guard [iff]: "anchor A n' B:guard n {priK A}"
by (case_tac "n'=n", auto simp: anchor_def)

lemma anchor_guard_Nonce_neq [intro]: "n ~= n'
==> anchor A' n' B:guard n {priK A}"
by (auto simp: anchor_def)

lemma reqm_guard [intro]: "I:agl ==> reqm A r n' I B:guard n {priK A}"
by (case_tac "n'=n", auto simp: reqm_def)

lemma reqm_guard_Nonce_neq [intro]: "[| n ~= n'; I:agl |]
==> reqm A' r n' I B:guard n {priK A}"
by (auto simp: reqm_def)

lemma prom_guard [intro]: "[| I:agl; J:agl; L:guard n {priK A} |]
==> prom B ofr A r I L J C:guard n {priK A}"
by (auto simp: prom_def)

lemma prom_guard_Nonce_neq [intro]: "[| n ~= ofr; I:agl; J:agl;
L:guard n {priK A} |] ==> prom B ofr A' r I L J C:guard n {priK A}"
by (auto simp: prom_def)

subsubsection{*Nonce uniqueness*}

lemma uniq_Nonce_in_chain [dest]: "Nonce k:parts {chain B ofr A L C} ==> k=ofr"
by (auto simp: chain_def sign_def)

lemma uniq_Nonce_in_anchor [dest]: "Nonce k:parts {anchor A n B} ==> k=n"
by (auto simp: anchor_def chain_def sign_def)

lemma uniq_Nonce_in_reqm [dest]: "[| Nonce k:parts {reqm A r n I B};
I:agl |] ==> k=n"
by (auto simp: reqm_def dest: no_Nonce_in_agl)

lemma uniq_Nonce_in_prom [dest]: "[| Nonce k:parts {prom B ofr A r I L J C};
I:agl; J:agl; Nonce k ~:parts {L} |] ==> k=ofr"
by (auto simp: prom_def dest: no_Nonce_in_agl no_Nonce_in_appdel)

subsubsection{*requests are guarded*}

lemma req_imp_Guard [rule_format]: "[| evs:p1; A ~:bad |] ==>
req A r n I B:set evs --> Guard n {priK A} (spies evs)"
apply (erule p1.induct, simp)
apply (simp add: req_def knows.simps, safe)
apply (erule in_synth_Guard, erule Guard_analz, simp)
by (auto simp: req_def pro_def dest: Says_imp_knows_Spy)

lemma req_imp_Guard_Friend: "[| evs:p1; A ~:bad; req A r n I B:set evs |]
==> Guard n {priK A} (knows_max (Friend C) evs)"
apply (rule Guard_knows_max')
apply (rule_tac H="spies evs" in Guard_mono)
apply (rule req_imp_Guard, simp+)
apply (rule_tac B="spies' evs" in subset_trans)
apply (rule_tac p=p1 in knows_max'_sub_spies', simp+)
by (rule knows'_sub_knows)

subsubsection{*propositions are guarded*}

lemma pro_imp_Guard [rule_format]: "[| evs:p1; B ~:bad; A ~:bad |] ==>
pro B ofr A r I (cons M L) J C:set evs --> Guard ofr {priK A} (spies evs)"
apply (erule p1.induct) (* +3 subgoals *)
(* Nil *)
apply simp
(* Fake *)
apply (simp add: pro_def, safe) (* +4 subgoals *)
(* 1 *)
apply (erule in_synth_Guard, drule Guard_analz, simp, simp)
(* 2 *)
apply simp
(* 3 *)
apply (simp, simp add: req_def pro_def, blast)
(* 4 *)
apply (simp add: pro_def)
apply (blast dest: prom_inj Says_Nonce_not_used_guard Nonce_not_used_Guard)
(* 5 *)
apply simp
apply safe (* +1 subgoal *)
apply (simp add: pro_def)
apply (blast dest: prom_inj Says_Nonce_not_used_guard)
(* 6 *)
apply (simp add: pro_def)
apply (blast dest: Says_imp_knows_Spy)
(* Request *)
apply (simp add: pro_def)
apply (blast dest: prom_inj Says_Nonce_not_used_guard Nonce_not_used_Guard)
(* Propose *)
apply simp
apply safe (* +1 subgoal *)
(* 1 *)
apply (simp add: pro_def)
apply (blast dest: prom_inj Says_Nonce_not_used_guard)
(* 2 *)
apply (simp add: pro_def)
by (blast dest: Says_imp_knows_Spy)

lemma pro_imp_Guard_Friend: "[| evs:p1; B ~:bad; A ~:bad;
pro B ofr A r I (cons M L) J C:set evs |]
==> Guard ofr {priK A} (knows_max (Friend D) evs)"
apply (rule Guard_knows_max')
apply (rule_tac H="spies evs" in Guard_mono)
apply (rule pro_imp_Guard, simp+)
apply (rule_tac B="spies' evs" in subset_trans)
apply (rule_tac p=p1 in knows_max'_sub_spies', simp+)
by (rule knows'_sub_knows)

subsubsection{*data confidentiality:
no one other than the originator can decrypt the offers*}

lemma Nonce_req_notin_spies: "[| evs:p1; req A r n I B:set evs; A ~:bad |]
==> Nonce n ~:analz (spies evs)"
by (frule req_imp_Guard, simp+, erule Guard_Nonce_analz, simp+)

lemma Nonce_req_notin_knows_max_Friend: "[| evs:p1; req A r n I B:set evs;
A ~:bad; A ~= Friend C |] ==> Nonce n ~:analz (knows_max (Friend C) evs)"
apply (clarify, frule_tac C=C in req_imp_Guard_Friend, simp+)
apply (simp add: knows_max_def, drule Guard_invKey_keyset, simp+)
by (drule priK_notin_knows_max_Friend, auto simp: knows_max_def)

lemma Nonce_pro_notin_spies: "[| evs:p1; B ~:bad; A ~:bad;
pro B ofr A r I (cons M L) J C:set evs |] ==> Nonce ofr ~:analz (spies evs)"
by (frule pro_imp_Guard, simp+, erule Guard_Nonce_analz, simp+)

lemma Nonce_pro_notin_knows_max_Friend: "[| evs:p1; B ~:bad; A ~:bad;
A ~= Friend D; pro B ofr A r I (cons M L) J C:set evs |]
==> Nonce ofr ~:analz (knows_max (Friend D) evs)"
apply (clarify, frule_tac A=A in pro_imp_Guard_Friend, simp+)
apply (simp add: knows_max_def, drule Guard_invKey_keyset, simp+)
by (drule priK_notin_knows_max_Friend, auto simp: knows_max_def)

subsubsection{*non repudiability:
an offer signed by B has been sent by B*}

lemma Crypt_reqm: "[| Crypt (priK A) X:parts {reqm A' r n I B}; I:agl |] ==> A=A'"
by (auto simp: reqm_def anchor_def chain_def sign_def dest: no_Crypt_in_agl)

lemma Crypt_prom: "[| Crypt (priK A) X:parts {prom B ofr A' r I L J C};
I:agl; J:agl |] ==> A=B | Crypt (priK A) X:parts {L}"
apply (simp add: prom_def anchor_def chain_def sign_def)
by (blast dest: no_Crypt_in_agl no_Crypt_in_appdel)

lemma Crypt_safeness: "[| evs:p1; A ~:bad |] ==> Crypt (priK A) X:parts (spies evs)
--> (EX B Y. Says A B Y:set evs & Crypt (priK A) X:parts {Y})"
apply (erule p1.induct)
(* Nil *)
apply simp
(* Fake *)
apply clarsimp
apply (drule_tac P="%G. Crypt (priK A) X:G" in parts_insert_substD, simp)
apply (erule disjE)
apply (drule_tac K="priK A" in Crypt_synth, simp+, blast, blast)
(* Request *)
apply (simp add: req_def, clarify)
apply (drule_tac P="%G. Crypt (priK A) X:G" in parts_insert_substD, simp)
apply (erule disjE)
apply (frule Crypt_reqm, simp, clarify)
apply (rule_tac x=B in exI, rule_tac x="reqm A r n I B" in exI, simp, blast)
(* Propose *)
apply (simp add: pro_def, clarify)
apply (drule_tac P="%G. Crypt (priK A) X:G" in parts_insert_substD, simp)
apply (rotate_tac -1, erule disjE)
apply (frule Crypt_prom, simp, simp)
apply (rotate_tac -1, erule disjE)
apply (rule_tac x=C in exI)
apply (rule_tac x="prom B ofr Aa r I (cons M L) J C" in exI, blast)
apply (subgoal_tac "cons M L:parts (spies evsp)")
apply (drule_tac G="{cons M L}" and H="spies evsp" in parts_trans, blast, blast)
apply (drule Says_imp_spies, rotate_tac -1, drule parts.Inj)
apply (drule parts.Snd, drule parts.Snd, drule parts.Snd)
by auto

lemma Crypt_Hash_imp_sign: "[| evs:p1; A ~:bad |] ==>
Crypt (priK A) (Hash X):parts (spies evs)
--> (EX B Y. Says A B Y:set evs & sign A X:parts {Y})"
apply (erule p1.induct)
(* Nil *)
apply simp
(* Fake *)
apply clarsimp
apply (drule_tac P="%G. Crypt (priK A) (Hash X):G" in parts_insert_substD)
apply simp
apply (erule disjE)
apply (drule_tac K="priK A" in Crypt_synth, simp+, blast, blast)
(* Request *)
apply (simp add: req_def, clarify)
apply (drule_tac P="%G. Crypt (priK A) (Hash X):G" in parts_insert_substD)
apply simp
apply (erule disjE)
apply (frule Crypt_reqm, simp+)
apply (rule_tac x=B in exI, rule_tac x="reqm Aa r n I B" in exI)
apply (simp add: reqm_def sign_def anchor_def no_Crypt_in_agl)
apply (simp add: chain_def sign_def, blast)
(* Propose *)
apply (simp add: pro_def, clarify)
apply (drule_tac P="%G. Crypt (priK A) (Hash X):G" in parts_insert_substD)
apply simp
apply (rotate_tac -1, erule disjE)
apply (simp add: prom_def sign_def no_Crypt_in_agl no_Crypt_in_appdel)
apply (simp add: chain_def sign_def)
apply (rotate_tac -1, erule disjE)
apply (rule_tac x=C in exI)
apply (rule_tac x="prom B ofr Aa r I (cons M L) J C" in exI)
apply (simp add: prom_def chain_def sign_def)
apply (erule impE) 
apply (blast dest: get_ML parts_sub) 
apply (blast del: MPair_parts)+
done

lemma sign_safeness: "[| evs:p1; A ~:bad |] ==> sign A X:parts (spies evs)
--> (EX B Y. Says A B Y:set evs & sign A X:parts {Y})"
apply (clarify, simp add: sign_def, frule parts.Snd)
apply (blast dest: Crypt_Hash_imp_sign [unfolded sign_def])
done

end