(*  Title:      ZF/Cardinal.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinals in Zermelo-Fraenkel Set Theory 

This theory does NOT assume the Axiom of Choice
*)

(*** The Schroeder-Bernstein Theorem -- see Davey & Priestly, page 106 ***)

(** Lemma: Banach's Decomposition Theorem **)

Goal "bnd_mono(X, %W. X - g``(Y - f``W))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [Diff_subset, subset_refl, Diff_mono, image_mono] 1));
qed "decomp_bnd_mono";

val [gfun] = goal Cardinal.thy
    "g: Y->X ==>                                        \
\    g``(Y - f`` lfp(X, %W. X - g``(Y - f``W))) =       \
\    X - lfp(X, %W. X - g``(Y - f``W)) ";
by (res_inst_tac [("P", "%u. ?v = X-u")] 
     (decomp_bnd_mono RS lfp_Tarski RS ssubst) 1);
by (simp_tac (simpset() addsimps [subset_refl, double_complement,
                             gfun RS fun_is_rel RS image_subset]) 1);
qed "Banach_last_equation";

Goal "[| f: X->Y;  g: Y->X |] ==>   \
\     EX XA XB YA YB. (XA Int XB = 0) & (XA Un XB = X) &    \
\                     (YA Int YB = 0) & (YA Un YB = Y) &    \
\                     f``XA=YA & g``YB=XB";
by (REPEAT 
    (FIRSTGOAL
     (resolve_tac [refl, exI, conjI, Diff_disjoint, Diff_partition])));
by (rtac Banach_last_equation 3);
by (REPEAT (ares_tac [fun_is_rel, image_subset, lfp_subset] 1));
qed "decomposition";

val prems = goal Cardinal.thy
    "[| f: inj(X,Y);  g: inj(Y,X) |] ==> EX h. h: bij(X,Y)";
by (cut_facts_tac prems 1);
by (cut_facts_tac [(prems RL [inj_is_fun]) MRS decomposition] 1);
by (blast_tac (claset() addSIs [restrict_bij,bij_disjoint_Un]
                    addIs [bij_converse_bij]) 1);
(* The instantiation of exI to "restrict(f,XA) Un converse(restrict(g,YB))"
   is forced by the context!! *)
qed "schroeder_bernstein";


(** Equipollence is an equivalence relation **)

Goalw [eqpoll_def] "f: bij(A,B) ==> A eqpoll B";
by (etac exI 1);
qed "bij_imp_eqpoll";

(*A eqpoll A*)
bind_thm ("eqpoll_refl", id_bij RS bij_imp_eqpoll);

Goalw [eqpoll_def] "X eqpoll Y ==> Y eqpoll X";
by (blast_tac (claset() addIs [bij_converse_bij]) 1);
qed "eqpoll_sym";

Goalw [eqpoll_def]
    "[| X eqpoll Y;  Y eqpoll Z |] ==> X eqpoll Z";
by (blast_tac (claset() addIs [comp_bij]) 1);
qed "eqpoll_trans";

(** Le-pollence is a partial ordering **)

Goalw [lepoll_def] "X<=Y ==> X lepoll Y";
by (rtac exI 1);
by (etac id_subset_inj 1);
qed "subset_imp_lepoll";

bind_thm ("lepoll_refl", subset_refl RS subset_imp_lepoll);

bind_thm ("le_imp_lepoll", le_imp_subset RS subset_imp_lepoll);

Goalw [eqpoll_def, bij_def, lepoll_def]
    "X eqpoll Y ==> X lepoll Y";
by (Blast_tac 1);
qed "eqpoll_imp_lepoll";

Goalw [lepoll_def]
    "[| X lepoll Y;  Y lepoll Z |] ==> X lepoll Z";
by (blast_tac (claset() addIs [comp_inj]) 1);
qed "lepoll_trans";

(*Asymmetry law*)
Goalw [lepoll_def,eqpoll_def]
    "[| X lepoll Y;  Y lepoll X |] ==> X eqpoll Y";
by (REPEAT (etac exE 1));
by (rtac schroeder_bernstein 1);
by (REPEAT (assume_tac 1));
qed "eqpollI";

val [major,minor] = Goal
    "[| X eqpoll Y; [| X lepoll Y; Y lepoll X |] ==> P |] ==> P";
by (rtac minor 1);
by (REPEAT (resolve_tac [major, eqpoll_imp_lepoll, eqpoll_sym] 1));
qed "eqpollE";

Goal "X eqpoll Y <-> X lepoll Y & Y lepoll X";
by (blast_tac (claset() addIs [eqpollI] addSEs [eqpollE]) 1);
qed "eqpoll_iff";

Goalw [lepoll_def, inj_def] "A lepoll 0 ==> A = 0";
by (blast_tac (claset() addDs [apply_type]) 1);
qed "lepoll_0_is_0";

(*0 lepoll Y*)
bind_thm ("empty_lepollI", empty_subsetI RS subset_imp_lepoll);

Goal "A lepoll 0 <-> A=0";
by (blast_tac (claset() addIs [lepoll_0_is_0, lepoll_refl]) 1);
qed "lepoll_0_iff";

Goalw [lepoll_def] 
    "[| A lepoll B; C lepoll D; B Int D = 0 |] ==> A Un C lepoll B Un D";
by (blast_tac (claset() addIs [inj_disjoint_Un]) 1);
qed "Un_lepoll_Un";

(*A eqpoll 0 ==> A=0*)
bind_thm ("eqpoll_0_is_0",  eqpoll_imp_lepoll RS lepoll_0_is_0);

Goal "A eqpoll 0 <-> A=0";
by (blast_tac (claset() addIs [eqpoll_0_is_0, eqpoll_refl]) 1);
qed "eqpoll_0_iff";

Goalw [eqpoll_def] 
    "[| A eqpoll B;  C eqpoll D;  A Int C = 0;  B Int D = 0 |]  \
\    ==> A Un C eqpoll B Un D";
by (blast_tac (claset() addIs [bij_disjoint_Un]) 1);
qed "eqpoll_disjoint_Un";


(*** lesspoll: contributions by Krzysztof Grabczewski ***)

Goalw [lesspoll_def] "A lesspoll B ==> A lepoll B";
by (Blast_tac 1);
qed "lesspoll_imp_lepoll";

Goalw [lepoll_def] "[| A lepoll B; well_ord(B,r) |] ==> EX s. well_ord(A,s)";
by (blast_tac (claset() addIs [well_ord_rvimage]) 1);
qed "lepoll_well_ord";

Goalw [lesspoll_def] "A lepoll B <-> A lesspoll B | A eqpoll B";
by (blast_tac (claset() addSIs [eqpollI] addSEs [eqpollE]) 1);
qed "lepoll_iff_leqpoll";

Goalw [inj_def, surj_def] 
  "[| f : inj(A, succ(m)); f ~: surj(A, succ(m)) |] ==> EX f. f:inj(A,m)";
by (safe_tac (claset_of ZF.thy));
by (swap_res_tac [exI] 1);
by (res_inst_tac [("a", "lam z:A. if f`z=m then y else f`z")] CollectI 1);
by (best_tac (claset() addSIs [if_type RS lam_type]
                       addEs [apply_funtype RS succE]) 1);
(*Proving it's injective*)
by (Asm_simp_tac 1);
by (blast_tac (claset() delrules [equalityI]) 1);
qed "inj_not_surj_succ";

(** Variations on transitivity **)

Goalw [lesspoll_def]
      "[| X lesspoll Y; Y lesspoll Z |] ==> X lesspoll Z";
by (blast_tac (claset() addSEs [eqpollE] addIs [eqpollI, lepoll_trans]) 1);
qed "lesspoll_trans";

Goalw [lesspoll_def]
      "[| X lesspoll Y; Y lepoll Z |] ==> X lesspoll Z";
by (blast_tac (claset() addSEs [eqpollE] addIs [eqpollI, lepoll_trans]) 1);
qed "lesspoll_lepoll_lesspoll";

Goalw [lesspoll_def] 
      "[| X lesspoll Y; Z lepoll X |] ==> Z lesspoll Y";
by (blast_tac (claset() addSEs [eqpollE] addIs [eqpollI, lepoll_trans]) 1);
qed "lepoll_lesspoll_lesspoll";


(** LEAST -- the least number operator [from HOL/Univ.ML] **)

val [premP,premOrd,premNot] = Goalw [Least_def]
    "[| P(i);  Ord(i);  !!x. x<i ==> ~P(x) |] ==> (LEAST x. P(x)) = i";
by (rtac the_equality 1);
by (blast_tac (claset() addSIs [premP,premOrd,premNot]) 1);
by (REPEAT (etac conjE 1));
by (etac (premOrd RS Ord_linear_lt) 1);
by (ALLGOALS (blast_tac (claset() addSIs [premP] addSDs [premNot])));
qed "Least_equality";

Goal "[| P(i);  Ord(i) |] ==> P(LEAST x. P(x))";
by (etac rev_mp 1);
by (trans_ind_tac "i" [] 1);
by (rtac impI 1);
by (rtac classical 1);
by (EVERY1 [stac Least_equality, assume_tac, assume_tac]);
by (assume_tac 2);
by (blast_tac (claset() addSEs [ltE]) 1);
qed "LeastI";

(*Proof is almost identical to the one above!*)
Goal "[| P(i);  Ord(i) |] ==> (LEAST x. P(x)) le i";
by (etac rev_mp 1);
by (trans_ind_tac "i" [] 1);
by (rtac impI 1);
by (rtac classical 1);
by (EVERY1 [stac Least_equality, assume_tac, assume_tac]);
by (etac le_refl 2);
by (blast_tac (claset() addEs [ltE] addIs [leI, ltI, lt_trans1]) 1);
qed "Least_le";

(*LEAST really is the smallest*)
Goal "[| P(i);  i < (LEAST x. P(x)) |] ==> Q";
by (rtac (Least_le RSN (2,lt_trans2) RS lt_irrefl) 1);
by (REPEAT (eresolve_tac [asm_rl, ltE] 1));
qed "less_LeastE";

(*Easier to apply than LeastI: conclusion has only one occurrence of P*)
val prems = goal Cardinal.thy
    "[| P(i);  Ord(i);  !!j. P(j) ==> Q(j) |] ==> Q(LEAST j. P(j))";
by (resolve_tac prems 1);
by (rtac LeastI 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1) ;
qed "LeastI2";

(*If there is no such P then LEAST is vacuously 0*)
Goalw [Least_def]
    "[| ~ (EX i. Ord(i) & P(i)) |] ==> (LEAST x. P(x)) = 0";
by (rtac the_0 1);
by (Blast_tac 1);
qed "Least_0";

Goal "Ord(LEAST x. P(x))";
by (excluded_middle_tac "EX i. Ord(i) & P(i)" 1);
by Safe_tac;
by (rtac (Least_le RS ltE) 2);
by (REPEAT_SOME assume_tac);
by (etac (Least_0 RS ssubst) 1);
by (rtac Ord_0 1);
qed "Ord_Least";


(** Basic properties of cardinals **)

(*Not needed for simplification, but helpful below*)
val prems = Goal "(!!y. P(y) <-> Q(y)) ==> (LEAST x. P(x)) = (LEAST x. Q(x))";
by (simp_tac (simpset() addsimps prems) 1);
qed "Least_cong";

(*Need AC to get X lepoll Y ==> |X| le |Y|;  see well_ord_lepoll_imp_Card_le
  Converse also requires AC, but see well_ord_cardinal_eqE*)
Goalw [eqpoll_def,cardinal_def] "X eqpoll Y ==> |X| = |Y|";
by (rtac Least_cong 1);
by (blast_tac (claset() addIs [comp_bij, bij_converse_bij]) 1);
qed "cardinal_cong";

(*Under AC, the premise becomes trivial; one consequence is ||A|| = |A|*)
Goalw [cardinal_def]
    "well_ord(A,r) ==> |A| eqpoll A";
by (rtac LeastI 1);
by (etac Ord_ordertype 2);
by (etac (ordermap_bij RS bij_converse_bij RS bij_imp_eqpoll) 1);
qed "well_ord_cardinal_eqpoll";

(* Ord(A) ==> |A| eqpoll A *)
bind_thm ("Ord_cardinal_eqpoll", well_ord_Memrel RS well_ord_cardinal_eqpoll);

Goal "[| well_ord(X,r);  well_ord(Y,s);  |X| = |Y| |] ==> X eqpoll Y";
by (rtac (eqpoll_sym RS eqpoll_trans) 1);
by (etac well_ord_cardinal_eqpoll 1);
by (asm_simp_tac (simpset() addsimps [well_ord_cardinal_eqpoll]) 1);
qed "well_ord_cardinal_eqE";

Goal "[| well_ord(X,r);  well_ord(Y,s) |] ==> |X| = |Y| <-> X eqpoll Y";
by (blast_tac (claset() addIs [cardinal_cong, well_ord_cardinal_eqE]) 1);
qed "well_ord_cardinal_eqpoll_iff";


(** Observations from Kunen, page 28 **)

Goalw [cardinal_def] "Ord(i) ==> |i| le i";
by (etac (eqpoll_refl RS Least_le) 1);
qed "Ord_cardinal_le";

Goalw [Card_def] "Card(K) ==> |K| = K";
by (etac sym 1);
qed "Card_cardinal_eq";

(* Could replace the  ~(j eqpoll i)  by  ~(i lepoll j) *)
val prems = Goalw [Card_def,cardinal_def]
    "[| Ord(i);  !!j. j<i ==> ~(j eqpoll i) |] ==> Card(i)";
by (stac Least_equality 1);
by (REPEAT (ares_tac ([refl,eqpoll_refl]@prems) 1));
qed "CardI";

Goalw [Card_def, cardinal_def] "Card(i) ==> Ord(i)";
by (etac ssubst 1);
by (rtac Ord_Least 1);
qed "Card_is_Ord";

Goal "Card(K) ==> K le |K|";
by (asm_simp_tac (simpset() addsimps [Card_is_Ord, Card_cardinal_eq]) 1);
qed "Card_cardinal_le";

Goalw [cardinal_def] "Ord(|A|)";
by (rtac Ord_Least 1);
qed "Ord_cardinal";

Addsimps [Ord_cardinal];
AddSIs [Ord_cardinal];

(*The cardinals are the initial ordinals*)
Goal "Card(K) <-> Ord(K) & (ALL j. j<K --> ~ j eqpoll K)";
by (safe_tac (claset() addSIs [CardI, Card_is_Ord]));
by (Blast_tac 2);
by (rewrite_goals_tac [Card_def, cardinal_def]);
by (rtac less_LeastE 1);
by (etac subst 2);
by (ALLGOALS assume_tac);
qed "Card_iff_initial";

Goalw [lesspoll_def] "[| Card(a); i<a |] ==> i lesspoll a";
by (dresolve_tac [Card_iff_initial RS iffD1] 1);
by (blast_tac (claset() addSIs [leI RS le_imp_lepoll]) 1);
qed "lt_Card_imp_lesspoll";

Goal "Card(0)";
by (rtac (Ord_0 RS CardI) 1);
by (blast_tac (claset() addSEs [ltE]) 1);
qed "Card_0";

val [premK,premL] = goal Cardinal.thy
    "[| Card(K);  Card(L) |] ==> Card(K Un L)";
by (rtac ([premK RS Card_is_Ord, premL RS Card_is_Ord] MRS Ord_linear_le) 1);
by (asm_simp_tac 
    (simpset() addsimps [premL, le_imp_subset, subset_Un_iff RS iffD1]) 1);
by (asm_simp_tac
    (simpset() addsimps [premK, le_imp_subset, subset_Un_iff2 RS iffD1]) 1);
qed "Card_Un";

(*Infinite unions of cardinals?  See Devlin, Lemma 6.7, page 98*)

Goalw [cardinal_def] "Card(|A|)";
by (excluded_middle_tac "EX i. Ord(i) & i eqpoll A" 1);
by (etac (Least_0 RS ssubst) 1 THEN rtac Card_0 1);
by (rtac (Ord_Least RS CardI) 1);
by Safe_tac;
by (rtac less_LeastE 1);
by (assume_tac 2);
by (etac eqpoll_trans 1);
by (REPEAT (ares_tac [LeastI] 1));
qed "Card_cardinal";

(*Kunen's Lemma 10.5*)
Goal "[| |i| le j;  j le i |] ==> |j| = |i|";
by (rtac (eqpollI RS cardinal_cong) 1);
by (etac le_imp_lepoll 1);
by (rtac lepoll_trans 1);
by (etac le_imp_lepoll 2);
by (rtac (eqpoll_sym RS eqpoll_imp_lepoll) 1);
by (rtac Ord_cardinal_eqpoll 1);
by (REPEAT (eresolve_tac [ltE, Ord_succD] 1));
qed "cardinal_eq_lemma";

Goal "i le j ==> |i| le |j|";
by (res_inst_tac [("i","|i|"),("j","|j|")] Ord_linear_le 1);
by (REPEAT_FIRST (ares_tac [Ord_cardinal, le_eqI]));
by (rtac cardinal_eq_lemma 1);
by (assume_tac 2);
by (etac le_trans 1);
by (etac ltE 1);
by (etac Ord_cardinal_le 1);
qed "cardinal_mono";

(*Since we have |succ(nat)| le |nat|, the converse of cardinal_mono fails!*)
Goal "[| |i| < |j|;  Ord(i);  Ord(j) |] ==> i < j";
by (rtac Ord_linear2 1);
by (REPEAT_SOME assume_tac);
by (etac (lt_trans2 RS lt_irrefl) 1);
by (etac cardinal_mono 1);
qed "cardinal_lt_imp_lt";

Goal "[| |i| < K;  Ord(i);  Card(K) |] ==> i < K";
by (asm_simp_tac (simpset() addsimps 
                  [cardinal_lt_imp_lt, Card_is_Ord, Card_cardinal_eq]) 1);
qed "Card_lt_imp_lt";

Goal "[| Ord(i);  Card(K) |] ==> (|i| < K) <-> (i < K)";
by (blast_tac (claset() addIs [Card_lt_imp_lt, Ord_cardinal_le RS lt_trans1]) 1);
qed "Card_lt_iff";

Goal "[| Ord(i);  Card(K) |] ==> (K le |i|) <-> (K le i)";
by (asm_simp_tac (simpset() addsimps 
                  [Card_lt_iff, Card_is_Ord, Ord_cardinal, 
                   not_lt_iff_le RS iff_sym]) 1);
qed "Card_le_iff";

(*Can use AC or finiteness to discharge first premise*)
Goal "[| well_ord(B,r);  A lepoll B |] ==> |A| le |B|";
by (res_inst_tac [("i","|A|"),("j","|B|")] Ord_linear_le 1);
by (REPEAT_FIRST (ares_tac [Ord_cardinal, le_eqI]));
by (rtac (eqpollI RS cardinal_cong) 1 THEN assume_tac 1);
by (rtac lepoll_trans 1);
by (rtac (well_ord_cardinal_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll) 1);
by (assume_tac 1);
by (etac (le_imp_lepoll RS lepoll_trans) 1);
by (rtac eqpoll_imp_lepoll 1);
by (rewtac lepoll_def);
by (etac exE 1);
by (rtac well_ord_cardinal_eqpoll 1);
by (etac well_ord_rvimage 1);
by (assume_tac 1);
qed "well_ord_lepoll_imp_Card_le";


Goal "[| A lepoll i; Ord(i) |] ==> |A| le i";
by (rtac le_trans 1);
by (etac (well_ord_Memrel RS well_ord_lepoll_imp_Card_le) 1);
by (assume_tac 1);
by (etac Ord_cardinal_le 1);
qed "lepoll_cardinal_le";

Goal "[| A lepoll i; Ord(i) |] ==> |A| eqpoll A";
by (blast_tac (claset() addIs [lepoll_cardinal_le, well_ord_Memrel,
                                well_ord_cardinal_eqpoll]
                        addSDs [lepoll_well_ord]) 1);
qed "lepoll_Ord_imp_eqpoll";

Goalw [lesspoll_def]
     "[| A lesspoll i; Ord(i) |] ==> |A| eqpoll A";
by (blast_tac (claset() addIs [lepoll_Ord_imp_eqpoll]) 1);
qed "lesspoll_imp_eqpoll";

Goalw [lesspoll_def]
     "[| A lesspoll i; Ord(i) |] ==> |A| eqpoll A";
by (blast_tac (claset() addIs [lepoll_Ord_imp_eqpoll]) 1);
qed "lesspoll_imp_eqpoll";


(*** The finite cardinals ***)

Goalw [lepoll_def, inj_def]
 "[| cons(u,A) lepoll cons(v,B);  u~:A;  v~:B |] ==> A lepoll B";
by Safe_tac;
by (res_inst_tac [("x", "lam x:A. if f`x=v then f`u else f`x")] exI 1);
by (rtac CollectI 1);
(*Proving it's in the function space A->B*)
by (rtac (if_type RS lam_type) 1);
by (blast_tac (claset() addDs [apply_funtype]) 1);
by (blast_tac (claset() addSEs [mem_irrefl] addDs [apply_funtype]) 1);
(*Proving it's injective*)
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "cons_lepoll_consD";

Goal "[| cons(u,A) eqpoll cons(v,B);  u~:A;  v~:B |] ==> A eqpoll B";
by (asm_full_simp_tac (simpset() addsimps [eqpoll_iff]) 1);
by (blast_tac (claset() addIs [cons_lepoll_consD]) 1);
qed "cons_eqpoll_consD";

(*Lemma suggested by Mike Fourman*)
Goalw [succ_def] "succ(m) lepoll succ(n) ==> m lepoll n";
by (etac cons_lepoll_consD 1);
by (REPEAT (rtac mem_not_refl 1));
qed "succ_lepoll_succD";

Goal "m:nat ==> ALL n: nat. m lepoll n --> m le n";
by (nat_ind_tac "m" [] 1);  (*induct_tac isn't available yet*)
by (blast_tac (claset() addSIs [nat_0_le]) 1);
by (rtac ballI 1);
by (eres_inst_tac [("n","n")] natE 1);
by (asm_simp_tac (simpset() addsimps [lepoll_def, inj_def]) 1);
by (blast_tac (claset() addSIs [succ_leI] addSDs [succ_lepoll_succD]) 1);
qed_spec_mp "nat_lepoll_imp_le";

Goal "[| m:nat; n: nat |] ==> m eqpoll n <-> m = n";
by (rtac iffI 1);
by (asm_simp_tac (simpset() addsimps [eqpoll_refl]) 2);
by (blast_tac (claset() addIs [nat_lepoll_imp_le, le_anti_sym] 
                        addSEs [eqpollE]) 1);
qed "nat_eqpoll_iff";

(*The object of all this work: every natural number is a (finite) cardinal*)
Goalw [Card_def,cardinal_def]
    "n: nat ==> Card(n)";
by (stac Least_equality 1);
by (REPEAT_FIRST (ares_tac [eqpoll_refl, nat_into_Ord, refl]));
by (asm_simp_tac (simpset() addsimps [lt_nat_in_nat RS nat_eqpoll_iff]) 1);
by (blast_tac (claset() addSEs [lt_irrefl]) 1);
qed "nat_into_Card";

(*Part of Kunen's Lemma 10.6*)
Goal "[| succ(n) lepoll n;  n:nat |] ==> P";
by (rtac (nat_lepoll_imp_le RS lt_irrefl) 1);
by (REPEAT (ares_tac [nat_succI] 1));
qed "succ_lepoll_natE";


(** lepoll, lesspoll and natural numbers **)

Goalw [lesspoll_def]
     "[| A lepoll m; m:nat |] ==> A lesspoll succ(m)";
by (rtac conjI 1);
by (blast_tac (claset() addIs [subset_imp_lepoll RSN (2,lepoll_trans)]) 1);
by (rtac notI 1);
by (dresolve_tac [eqpoll_sym RS eqpoll_imp_lepoll] 1);
by (dtac lepoll_trans 1 THEN assume_tac 1);
by (etac succ_lepoll_natE 1 THEN assume_tac 1);
qed "lepoll_imp_lesspoll_succ";

Goalw [lesspoll_def, lepoll_def, eqpoll_def, bij_def]
     "[| A lesspoll succ(m); m:nat |] ==> A lepoll m";
by (Clarify_tac 1);
by (blast_tac (claset() addSIs [inj_not_surj_succ]) 1);
qed "lesspoll_succ_imp_lepoll";

Goal "m:nat ==> A lesspoll succ(m) <-> A lepoll m";
by (blast_tac (claset() addSIs [lepoll_imp_lesspoll_succ, 
				lesspoll_succ_imp_lepoll]) 1);
qed "lesspoll_succ_iff";

Goal "[| A lepoll succ(m);  m:nat |] ==> A lepoll m | A eqpoll succ(m)";
by (rtac disjCI 1);
by (rtac lesspoll_succ_imp_lepoll 1);
by (assume_tac 2);
by (asm_simp_tac (simpset() addsimps [lesspoll_def]) 1);
qed "lepoll_succ_disj";

Goalw [lesspoll_def] "[| A lesspoll i; Ord(i) |] ==> |A| < i";
by (Clarify_tac 1);
by (ftac lepoll_cardinal_le 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [well_ord_Memrel,
			       well_ord_cardinal_eqpoll RS eqpoll_sym]
                        addDs [lepoll_well_ord] 
                        addSEs [leE]) 1);
qed "lesspoll_cardinal_lt";


(*** The first infinite cardinal: Omega, or nat ***)

(*This implies Kunen's Lemma 10.6*)
Goal "[| n<i;  n:nat |] ==> ~ i lepoll n";
by (rtac notI 1);
by (rtac succ_lepoll_natE 1 THEN assume_tac 2);
by (rtac lepoll_trans 1 THEN assume_tac 2);
by (etac ltE 1);
by (REPEAT (ares_tac [Ord_succ_subsetI RS subset_imp_lepoll] 1));
qed "lt_not_lepoll";

Goal "[| Ord(i);  n:nat |] ==> i eqpoll n <-> i=n";
by (rtac iffI 1);
by (asm_simp_tac (simpset() addsimps [eqpoll_refl]) 2);
by (rtac Ord_linear_lt 1);
by (REPEAT_SOME (eresolve_tac [asm_rl, nat_into_Ord]));
by (etac (lt_nat_in_nat RS nat_eqpoll_iff RS iffD1) 1 THEN
    REPEAT (assume_tac 1));
by (rtac (lt_not_lepoll RS notE) 1 THEN (REPEAT (assume_tac 1)));
by (etac eqpoll_imp_lepoll 1);
qed "Ord_nat_eqpoll_iff";

Goalw [Card_def,cardinal_def] "Card(nat)";
by (stac Least_equality 1);
by (REPEAT_FIRST (ares_tac [eqpoll_refl, Ord_nat, refl]));
by (etac ltE 1);
by (asm_simp_tac (simpset() addsimps [eqpoll_iff, lt_not_lepoll, ltI]) 1);
qed "Card_nat";

(*Allows showing that |i| is a limit cardinal*)
Goal  "nat le i ==> nat le |i|";
by (rtac (Card_nat RS Card_cardinal_eq RS subst) 1);
by (etac cardinal_mono 1);
qed "nat_le_cardinal";


(*** Towards Cardinal Arithmetic ***)
(** Congruence laws for successor, cardinal addition and multiplication **)

(*Congruence law for  cons  under equipollence*)
Goalw [lepoll_def]
    "[| A lepoll B;  b ~: B |] ==> cons(a,A) lepoll cons(b,B)";
by Safe_tac;
by (res_inst_tac [("x", "lam y: cons(a,A). if y=a then b else f`y")] exI 1);
by (res_inst_tac [("d","%z. if z:B then converse(f)`z else a")] 
    lam_injective 1);
by (asm_simp_tac (simpset() addsimps [inj_is_fun RS apply_type, cons_iff]
                        setloop etac consE') 1);
by (asm_simp_tac (simpset() addsimps [inj_is_fun RS apply_type]
                        setloop etac consE') 1);
qed "cons_lepoll_cong";

Goal "[| A eqpoll B;  a ~: A;  b ~: B |] ==> cons(a,A) eqpoll cons(b,B)";
by (asm_full_simp_tac (simpset() addsimps [eqpoll_iff, cons_lepoll_cong]) 1);
qed "cons_eqpoll_cong";

Goal "[| a ~: A;  b ~: B |] ==> \
\           cons(a,A) lepoll cons(b,B)  <->  A lepoll B";
by (blast_tac (claset() addIs [cons_lepoll_cong, cons_lepoll_consD]) 1);
qed "cons_lepoll_cons_iff";

Goal "[| a ~: A;  b ~: B |] ==> \
\           cons(a,A) eqpoll cons(b,B)  <->  A eqpoll B";
by (blast_tac (claset() addIs [cons_eqpoll_cong, cons_eqpoll_consD]) 1);
qed "cons_eqpoll_cons_iff";

Goalw [succ_def] "{a} eqpoll 1";
by (blast_tac (claset() addSIs [eqpoll_refl RS cons_eqpoll_cong]) 1);
qed "singleton_eqpoll_1";

Goal "|{a}| = 1";
by (resolve_tac [singleton_eqpoll_1 RS cardinal_cong RS trans] 1);
by (simp_tac (simpset() addsimps [nat_into_Card RS Card_cardinal_eq]) 1);
qed "cardinal_singleton";

(*Congruence law for  succ  under equipollence*)
Goalw [succ_def]
    "A eqpoll B ==> succ(A) eqpoll succ(B)";
by (REPEAT (ares_tac [cons_eqpoll_cong, mem_not_refl] 1));
qed "succ_eqpoll_cong";

(*Congruence law for + under equipollence*)
Goalw [eqpoll_def]
    "[| A eqpoll C;  B eqpoll D |] ==> A+B eqpoll C+D";
by (blast_tac (claset() addSIs [sum_bij]) 1);
qed "sum_eqpoll_cong";

(*Congruence law for * under equipollence*)
Goalw [eqpoll_def]
    "[| A eqpoll C;  B eqpoll D |] ==> A*B eqpoll C*D";
by (blast_tac (claset() addSIs [prod_bij]) 1);
qed "prod_eqpoll_cong";

Goalw [eqpoll_def]
    "[| f: inj(A,B);  A Int B = 0 |] ==> A Un (B - range(f)) eqpoll B";
by (rtac exI 1);
by (res_inst_tac [("c", "%x. if x:A then f`x else x"),
                  ("d", "%y. if y: range(f) then converse(f)`y else y")] 
    lam_bijective 1);
by (blast_tac (claset() addSIs [if_type, inj_is_fun RS apply_type]) 1);
by (asm_simp_tac 
    (simpset() addsimps [inj_converse_fun RS apply_funtype]) 1);
by (asm_simp_tac (simpset() addsimps [inj_is_fun RS apply_rangeI]
                        setloop etac UnE') 1);
by (asm_simp_tac (simpset() addsimps [inj_converse_fun RS apply_funtype]) 1);
by (Blast_tac 1);
qed "inj_disjoint_eqpoll";


(*** Lemmas by Krzysztof Grabczewski.  New proofs using cons_lepoll_cons.
     Could easily generalise from succ to cons. ***)

(*If A has at most n+1 elements and a:A then A-{a} has at most n.*)
Goalw [succ_def]
      "[| a:A;  A lepoll succ(n) |] ==> A - {a} lepoll n";
by (rtac cons_lepoll_consD 1);
by (rtac mem_not_refl 3);
by (eresolve_tac [cons_Diff RS ssubst] 1);
by Safe_tac;
qed "Diff_sing_lepoll";

(*If A has at least n+1 elements then A-{a} has at least n.*)
Goalw [succ_def]
      "[| succ(n) lepoll A |] ==> n lepoll A - {a}";
by (rtac cons_lepoll_consD 1);
by (rtac mem_not_refl 2);
by (Blast_tac 2);
by (blast_tac (claset() addIs [subset_imp_lepoll RSN (2, lepoll_trans)]) 1);
qed "lepoll_Diff_sing";

Goal "[| a:A; A eqpoll succ(n) |] ==> A - {a} eqpoll n";
by (blast_tac (claset() addSIs [eqpollI] addSEs [eqpollE] 
                    addIs [Diff_sing_lepoll,lepoll_Diff_sing]) 1);
qed "Diff_sing_eqpoll";

Goal "[| A lepoll 1; a:A |] ==> A = {a}";
by (ftac Diff_sing_lepoll 1);
by (assume_tac 1);
by (dtac lepoll_0_is_0 1);
by (blast_tac (claset() addEs [equalityE]) 1);
qed "lepoll_1_is_sing";

Goalw [lepoll_def] "A Un B lepoll A+B";
by (res_inst_tac [("x",
		   "lam x: A Un B. if x:A then Inl(x) else Inr(x)")] exI 1);
by (res_inst_tac [("d","%z. snd(z)")] lam_injective 1);
by (asm_full_simp_tac (simpset() addsimps [Inl_def, Inr_def]) 2);
by Auto_tac;
qed "Un_lepoll_sum";

Goal "[| well_ord(X,R); well_ord(Y,S) |] ==> EX T. well_ord(X Un Y, T)";
by (eresolve_tac [well_ord_radd RS (Un_lepoll_sum RS lepoll_well_ord)] 1);
by (assume_tac 1);
qed "well_ord_Un";

(*Krzysztof Grabczewski*)
Goalw [eqpoll_def] "A Int B = 0 ==> A Un B eqpoll A + B";
by (res_inst_tac [("x","lam a:A Un B. if a:A then Inl(a) else Inr(a)")] exI 1);
by (res_inst_tac [("d","%z. case(%x. x, %x. x, z)")] lam_bijective 1);
by Auto_tac;
qed "disj_Un_eqpoll_sum";


(*** Finite and infinite sets ***)

Goalw [Finite_def] "Finite(0)";
by (blast_tac (claset() addSIs [eqpoll_refl, nat_0I]) 1);
qed "Finite_0";

Goalw [Finite_def]
    "[| A lepoll n;  n:nat |] ==> Finite(A)";
by (etac rev_mp 1);
by (etac nat_induct 1);
by (blast_tac (claset() addSDs [lepoll_0_is_0] addSIs [eqpoll_refl,nat_0I]) 1);
by (blast_tac (claset() addSDs [lepoll_succ_disj]) 1);
qed "lepoll_nat_imp_Finite";

Goalw [Finite_def]
     "A lesspoll nat ==> Finite(A)";
by (blast_tac (claset() addDs [ltD, lesspoll_cardinal_lt,
	       lesspoll_imp_eqpoll RS eqpoll_sym]) 1);;
qed "lesspoll_nat_is_Finite";

Goalw [Finite_def]
     "[| Y lepoll X;  Finite(X) |] ==> Finite(Y)";
by (blast_tac 
    (claset() addSEs [eqpollE] 
             addIs [lepoll_trans RS 
		    rewrite_rule [Finite_def] lepoll_nat_imp_Finite]) 1);
qed "lepoll_Finite";

bind_thm ("subset_Finite", subset_imp_lepoll RS lepoll_Finite);

bind_thm ("Finite_Diff", Diff_subset RS subset_Finite);

Goalw [Finite_def] "Finite(x) ==> Finite(cons(y,x))";
by (excluded_middle_tac "y:x" 1);
by (asm_simp_tac (simpset() addsimps [cons_absorb]) 2);
by (etac bexE 1);
by (rtac bexI 1);
by (etac nat_succI 2);
by (asm_simp_tac 
    (simpset() addsimps [succ_def, cons_eqpoll_cong, mem_not_refl]) 1);
qed "Finite_cons";

Goalw [succ_def] "Finite(x) ==> Finite(succ(x))";
by (etac Finite_cons 1);
qed "Finite_succ";

Goalw [Finite_def] 
      "[| Ord(i);  ~ Finite(i) |] ==> nat le i";
by (eresolve_tac [Ord_nat RSN (2,Ord_linear2)] 1);
by (assume_tac 2);
by (blast_tac (claset() addSIs [eqpoll_refl] addSEs [ltE]) 1);
qed "nat_le_infinite_Ord";

Goalw [Finite_def, eqpoll_def]
    "Finite(A) ==> EX r. well_ord(A,r)";
by (blast_tac (claset() addIs [well_ord_rvimage, bij_is_inj, well_ord_Memrel, 
			      nat_into_Ord]) 1);
qed "Finite_imp_well_ord";


(*Krzysztof Grabczewski's proof that the converse of a finite, well-ordered
  set is well-ordered.  Proofs simplified by lcp. *)

Goal "n:nat ==> wf[n](converse(Memrel(n)))";
by (etac nat_induct 1);
by (blast_tac (claset() addIs [wf_onI]) 1);
by (rtac wf_onI 1);
by (asm_full_simp_tac (simpset() addsimps [wf_on_def, wf_def, Memrel_iff]) 1);
by (excluded_middle_tac "x:Z" 1);
by (dres_inst_tac [("x", "x")] bspec 2 THEN assume_tac 2);
by (blast_tac (claset() addEs [mem_irrefl, mem_asym]) 2);
by (dres_inst_tac [("x", "Z")] spec 1);
by (Blast.depth_tac (claset()) 4 1);
qed "nat_wf_on_converse_Memrel";

Goal "n:nat ==> well_ord(n,converse(Memrel(n)))";
by (forward_tac [transfer thy Ord_nat RS Ord_in_Ord RS well_ord_Memrel] 1);
by (rewtac well_ord_def);
by (blast_tac (claset() addSIs [tot_ord_converse, 
			       nat_wf_on_converse_Memrel]) 1);
qed "nat_well_ord_converse_Memrel";

Goal "[| well_ord(A,r);     \
\            well_ord(ordertype(A,r), converse(Memrel(ordertype(A, r)))) \
\         |] ==> well_ord(A,converse(r))";
by (resolve_tac [well_ord_Int_iff RS iffD1] 1);
by (forward_tac [ordermap_bij RS bij_is_inj RS well_ord_rvimage] 1);
by (assume_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [rvimage_converse, converse_Int, converse_prod, 
                     ordertype_ord_iso RS ord_iso_rvimage_eq]) 1);
qed "well_ord_converse";

Goal "[| well_ord(A,r);  A eqpoll n;  n:nat |] ==> ordertype(A,r)=n";
by (rtac (Ord_ordertype RS Ord_nat_eqpoll_iff RS iffD1) 1 THEN 
    REPEAT (assume_tac 1));
by (rtac eqpoll_trans 1 THEN assume_tac 2);
by (rewtac eqpoll_def);
by (blast_tac (claset() addSIs [ordermap_bij RS bij_converse_bij]) 1);
qed "ordertype_eq_n";

Goalw [Finite_def]
    "[| Finite(A);  well_ord(A,r) |] ==> well_ord(A,converse(r))";
by (rtac well_ord_converse 1 THEN assume_tac 1);
by (blast_tac (claset() addDs [ordertype_eq_n] 
                       addSIs [nat_well_ord_converse_Memrel]) 1);
qed "Finite_well_ord_converse";

Goalw [Finite_def] "n:nat ==> Finite(n)";
by (fast_tac (claset() addSIs [eqpoll_refl]) 1);
qed "nat_into_Finite";
