(*  Title: 	ZF/Cardinal.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinals in Zermelo-Fraenkel Set Theory 

This theory does NOT assume the Axiom of Choice
*)

open Cardinal;

(*** The Schroeder-Bernstein Theorem -- see Davey & Priestly, page 106 ***)

(** Lemma: Banach's Decomposition Theorem **)

goal Cardinal.thy "bnd_mono(X, %W. X - g``(Y - f``W))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [Diff_subset, subset_refl, Diff_mono, image_mono] 1));
qed "decomp_bnd_mono";

val [gfun] = goal Cardinal.thy
    "g: Y->X ==>   					\
\    g``(Y - f`` lfp(X, %W. X - g``(Y - f``W))) = 	\
\    X - lfp(X, %W. X - g``(Y - f``W)) ";
by (res_inst_tac [("P", "%u. ?v = X-u")] 
     (decomp_bnd_mono RS lfp_Tarski RS ssubst) 1);
by (simp_tac (ZF_ss addsimps [subset_refl, double_complement,
			     gfun RS fun_is_rel RS image_subset]) 1);
qed "Banach_last_equation";

val prems = goal Cardinal.thy
    "[| f: X->Y;  g: Y->X |] ==>   \
\    EX XA XB YA YB. (XA Int XB = 0) & (XA Un XB = X) &    \
\                    (YA Int YB = 0) & (YA Un YB = Y) &    \
\                    f``XA=YA & g``YB=XB";
by (REPEAT 
    (FIRSTGOAL
     (resolve_tac [refl, exI, conjI, Diff_disjoint, Diff_partition])));
by (rtac Banach_last_equation 3);
by (REPEAT (resolve_tac (prems@[fun_is_rel, image_subset, lfp_subset]) 1));
qed "decomposition";

val prems = goal Cardinal.thy
    "[| f: inj(X,Y);  g: inj(Y,X) |] ==> EX h. h: bij(X,Y)";
by (cut_facts_tac prems 1);
by (cut_facts_tac [(prems RL [inj_is_fun]) MRS decomposition] 1);
by (fast_tac (ZF_cs addSIs [restrict_bij,bij_disjoint_Un]
                    addIs [bij_converse_bij]) 1);
(* The instantiation of exI to "restrict(f,XA) Un converse(restrict(g,YB))"
   is forced by the context!! *)
qed "schroeder_bernstein";


(** Equipollence is an equivalence relation **)

goalw Cardinal.thy [eqpoll_def] "X eqpoll X";
by (rtac exI 1);
by (rtac id_bij 1);
qed "eqpoll_refl";

goalw Cardinal.thy [eqpoll_def] "!!X Y. X eqpoll Y ==> Y eqpoll X";
by (fast_tac (ZF_cs addIs [bij_converse_bij]) 1);
qed "eqpoll_sym";

goalw Cardinal.thy [eqpoll_def]
    "!!X Y. [| X eqpoll Y;  Y eqpoll Z |] ==> X eqpoll Z";
by (fast_tac (ZF_cs addIs [comp_bij]) 1);
qed "eqpoll_trans";

(** Le-pollence is a partial ordering **)

goalw Cardinal.thy [lepoll_def] "!!X Y. X<=Y ==> X lepoll Y";
by (rtac exI 1);
by (etac id_subset_inj 1);
qed "subset_imp_lepoll";

val lepoll_refl = subset_refl RS subset_imp_lepoll;

goalw Cardinal.thy [eqpoll_def, bij_def, lepoll_def]
    "!!X Y. X eqpoll Y ==> X lepoll Y";
by (fast_tac ZF_cs 1);
qed "eqpoll_imp_lepoll";

goalw Cardinal.thy [lepoll_def]
    "!!X Y. [| X lepoll Y;  Y lepoll Z |] ==> X lepoll Z";
by (fast_tac (ZF_cs addIs [comp_inj]) 1);
qed "lepoll_trans";

(*Asymmetry law*)
goalw Cardinal.thy [lepoll_def,eqpoll_def]
    "!!X Y. [| X lepoll Y;  Y lepoll X |] ==> X eqpoll Y";
by (REPEAT (etac exE 1));
by (rtac schroeder_bernstein 1);
by (REPEAT (assume_tac 1));
qed "eqpollI";

val [major,minor] = goal Cardinal.thy
    "[| X eqpoll Y; [| X lepoll Y; Y lepoll X |] ==> P |] ==> P";
by (rtac minor 1);
by (REPEAT (resolve_tac [major, eqpoll_imp_lepoll, eqpoll_sym] 1));
qed "eqpollE";

goal Cardinal.thy "X eqpoll Y <-> X lepoll Y & Y lepoll X";
by (fast_tac (ZF_cs addIs [eqpollI] addSEs [eqpollE]) 1);
qed "eqpoll_iff";


(** LEAST -- the least number operator [from HOL/Univ.ML] **)

val [premP,premOrd,premNot] = goalw Cardinal.thy [Least_def]
    "[| P(i);  Ord(i);  !!x. x<i ==> ~P(x) |] ==> (LEAST x.P(x)) = i";
by (rtac the_equality 1);
by (fast_tac (ZF_cs addSIs [premP,premOrd,premNot]) 1);
by (REPEAT (etac conjE 1));
by (etac (premOrd RS Ord_linear_lt) 1);
by (ALLGOALS (fast_tac (ZF_cs addSIs [premP] addSDs [premNot])));
qed "Least_equality";

goal Cardinal.thy "!!i. [| P(i);  Ord(i) |] ==> P(LEAST x.P(x))";
by (etac rev_mp 1);
by (trans_ind_tac "i" [] 1);
by (rtac impI 1);
by (rtac classical 1);
by (EVERY1 [rtac (Least_equality RS ssubst), assume_tac, assume_tac]);
by (assume_tac 2);
by (fast_tac (ZF_cs addSEs [ltE]) 1);
qed "LeastI";

(*Proof is almost identical to the one above!*)
goal Cardinal.thy "!!i. [| P(i);  Ord(i) |] ==> (LEAST x.P(x)) le i";
by (etac rev_mp 1);
by (trans_ind_tac "i" [] 1);
by (rtac impI 1);
by (rtac classical 1);
by (EVERY1 [rtac (Least_equality RS ssubst), assume_tac, assume_tac]);
by (etac le_refl 2);
by (fast_tac (ZF_cs addEs [ltE, lt_trans1] addIs [leI, ltI]) 1);
qed "Least_le";

(*LEAST really is the smallest*)
goal Cardinal.thy "!!i. [| P(i);  i < (LEAST x.P(x)) |] ==> Q";
by (rtac (Least_le RSN (2,lt_trans2) RS lt_irrefl) 1);
by (REPEAT (eresolve_tac [asm_rl, ltE] 1));
qed "less_LeastE";

(*If there is no such P then LEAST is vacuously 0*)
goalw Cardinal.thy [Least_def]
    "!!P. [| ~ (EX i. Ord(i) & P(i)) |] ==> (LEAST x.P(x)) = 0";
by (rtac the_0 1);
by (fast_tac ZF_cs 1);
qed "Least_0";

goal Cardinal.thy "Ord(LEAST x.P(x))";
by (excluded_middle_tac "EX i. Ord(i) & P(i)" 1);
by (safe_tac ZF_cs);
by (rtac (Least_le RS ltE) 2);
by (REPEAT_SOME assume_tac);
by (etac (Least_0 RS ssubst) 1);
by (rtac Ord_0 1);
qed "Ord_Least";


(** Basic properties of cardinals **)

(*Not needed for simplification, but helpful below*)
val prems = goal Cardinal.thy
    "[| !!y. P(y) <-> Q(y) |] ==> (LEAST x.P(x)) = (LEAST x.Q(x))";
by (simp_tac (FOL_ss addsimps prems) 1);
qed "Least_cong";

(*Need AC to prove   X lepoll Y ==> |X| le |Y| ; 
  see well_ord_lepoll_imp_Card_le  *)
goalw Cardinal.thy [eqpoll_def,cardinal_def] "!!X Y. X eqpoll Y ==> |X| = |Y|";
by (rtac Least_cong 1);
by (fast_tac (ZF_cs addEs [comp_bij,bij_converse_bij]) 1);
qed "cardinal_cong";

(*Under AC, the premise becomes trivial; one consequence is ||A|| = |A|*)
goalw Cardinal.thy [eqpoll_def, cardinal_def]
    "!!A. well_ord(A,r) ==> |A| eqpoll A";
by (rtac LeastI 1);
by (etac Ord_ordertype 2);
by (rtac exI 1);
by (etac (ordermap_bij RS bij_converse_bij) 1);
qed "well_ord_cardinal_eqpoll";

val Ord_cardinal_eqpoll = well_ord_Memrel RS well_ord_cardinal_eqpoll 
                          |> standard;

goal Cardinal.thy
    "!!X Y. [| well_ord(X,r);  well_ord(Y,s);  |X| = |Y| |] ==> X eqpoll Y";
by (rtac (eqpoll_sym RS eqpoll_trans) 1);
by (etac well_ord_cardinal_eqpoll 1);
by (asm_simp_tac (ZF_ss addsimps [well_ord_cardinal_eqpoll]) 1);
qed "well_ord_cardinal_eqE";


(** Observations from Kunen, page 28 **)

goalw Cardinal.thy [cardinal_def] "!!i. Ord(i) ==> |i| le i";
by (etac (eqpoll_refl RS Least_le) 1);
qed "Ord_cardinal_le";

goalw Cardinal.thy [Card_def] "!!K. Card(K) ==> |K| = K";
by (etac sym 1);
qed "Card_cardinal_eq";

val prems = goalw Cardinal.thy [Card_def,cardinal_def]
    "[| Ord(i);  !!j. j<i ==> ~(j eqpoll i) |] ==> Card(i)";
by (rtac (Least_equality RS ssubst) 1);
by (REPEAT (ares_tac ([refl,eqpoll_refl]@prems) 1));
qed "CardI";

goalw Cardinal.thy [Card_def, cardinal_def] "!!i. Card(i) ==> Ord(i)";
by (etac ssubst 1);
by (rtac Ord_Least 1);
qed "Card_is_Ord";

goal Cardinal.thy "!!K. Card(K) ==> K le |K|";
by (asm_simp_tac (ZF_ss addsimps [le_refl, Card_is_Ord, Card_cardinal_eq]) 1);
qed "Card_cardinal_le";

goalw Cardinal.thy [cardinal_def] "Ord(|A|)";
by (rtac Ord_Least 1);
qed "Ord_cardinal";

goal Cardinal.thy "Card(0)";
by (rtac (Ord_0 RS CardI) 1);
by (fast_tac (ZF_cs addSEs [ltE]) 1);
qed "Card_0";

val [premK,premL] = goal Cardinal.thy
    "[| Card(K);  Card(L) |] ==> Card(K Un L)";
by (rtac ([premK RS Card_is_Ord, premL RS Card_is_Ord] MRS Ord_linear_le) 1);
by (asm_simp_tac 
    (ZF_ss addsimps [premL, le_imp_subset, subset_Un_iff RS iffD1]) 1);
by (asm_simp_tac
    (ZF_ss addsimps [premK, le_imp_subset, subset_Un_iff2 RS iffD1]) 1);
qed "Card_Un";

(*Infinite unions of cardinals?  See Devlin, Lemma 6.7, page 98*)

goalw Cardinal.thy [cardinal_def] "Card(|A|)";
by (excluded_middle_tac "EX i. Ord(i) & i eqpoll A" 1);
by (etac (Least_0 RS ssubst) 1 THEN rtac Card_0 1);
by (rtac (Ord_Least RS CardI) 1);
by (safe_tac ZF_cs);
by (rtac less_LeastE 1);
by (assume_tac 2);
by (etac eqpoll_trans 1);
by (REPEAT (ares_tac [LeastI] 1));
qed "Card_cardinal";

(*Kunen's Lemma 10.5*)
goal Cardinal.thy "!!i j. [| |i| le j;  j le i |] ==> |j| = |i|";
by (rtac (eqpollI RS cardinal_cong) 1);
by (etac (le_imp_subset RS subset_imp_lepoll) 1);
by (rtac lepoll_trans 1);
by (etac (le_imp_subset RS subset_imp_lepoll) 2);
by (rtac (eqpoll_sym RS eqpoll_imp_lepoll) 1);
by (rtac Ord_cardinal_eqpoll 1);
by (REPEAT (eresolve_tac [ltE, Ord_succD] 1));
qed "cardinal_eq_lemma";

goal Cardinal.thy "!!i j. i le j ==> |i| le |j|";
by (res_inst_tac [("i","|i|"),("j","|j|")] Ord_linear_le 1);
by (REPEAT_FIRST (ares_tac [Ord_cardinal, le_eqI]));
by (rtac cardinal_eq_lemma 1);
by (assume_tac 2);
by (etac le_trans 1);
by (etac ltE 1);
by (etac Ord_cardinal_le 1);
qed "cardinal_mono";

(*Since we have |succ(nat)| le |nat|, the converse of cardinal_mono fails!*)
goal Cardinal.thy "!!i j. [| |i| < |j|;  Ord(i);  Ord(j) |] ==> i < j";
by (rtac Ord_linear2 1);
by (REPEAT_SOME assume_tac);
by (etac (lt_trans2 RS lt_irrefl) 1);
by (etac cardinal_mono 1);
qed "cardinal_lt_imp_lt";

goal Cardinal.thy "!!i j. [| |i| < K;  Ord(i);  Card(K) |] ==> i < K";
by (asm_simp_tac (ZF_ss addsimps 
		  [cardinal_lt_imp_lt, Card_is_Ord, Card_cardinal_eq]) 1);
qed "Card_lt_imp_lt";

goal Cardinal.thy "!!i j. [| Ord(i);  Card(K) |] ==> (|i| < K) <-> (i < K)";
by (fast_tac (ZF_cs addEs [Card_lt_imp_lt, Ord_cardinal_le RS lt_trans1]) 1);
qed "Card_lt_iff";

goal Cardinal.thy "!!i j. [| Ord(i);  Card(K) |] ==> (K le |i|) <-> (K le i)";
by (asm_simp_tac (ZF_ss addsimps 
		  [Card_lt_iff, Card_is_Ord, Ord_cardinal, 
		   not_lt_iff_le RS iff_sym]) 1);
qed "Card_le_iff";


(** The swap operator [NOT USED] **)

goalw Cardinal.thy [swap_def]
    "!!A. [| x:A;  y:A |] ==> swap(A,x,y) : A->A";
by (REPEAT (ares_tac [lam_type,if_type] 1));
qed "swap_type";

goalw Cardinal.thy [swap_def]
    "!!A. [| x:A;  y:A;  z:A |] ==> swap(A,x,y)`(swap(A,x,y)`z) = z";
by (asm_simp_tac (ZF_ss setloop split_tac [expand_if]) 1);
qed "swap_swap_identity";

goal Cardinal.thy "!!A. [| x:A;  y:A |] ==> swap(A,x,y) : bij(A,A)";
by (rtac nilpotent_imp_bijective 1);
by (REPEAT (ares_tac [swap_type, comp_eq_id_iff RS iffD2,
		      ballI, swap_swap_identity] 1));
qed "swap_bij";

(*** The finite cardinals ***)

(*Lemma suggested by Mike Fourman*)
val [prem] = goalw Cardinal.thy [inj_def]
 "f: inj(succ(m), succ(n)) ==> (lam x:m. if(f`x=n, f`m, f`x)) : inj(m,n)";
by (rtac CollectI 1);
(*Proving it's in the function space m->n*)
by (cut_facts_tac [prem] 1);
by (rtac (if_type RS lam_type) 1);
by (fast_tac (ZF_cs addSEs [mem_irrefl] addEs [apply_funtype RS succE]) 1);
by (fast_tac (ZF_cs addSEs [mem_irrefl] addEs [apply_funtype RS succE]) 1);
(*Proving it's injective*)
by (asm_simp_tac (ZF_ss setloop split_tac [expand_if]) 1);
(*Adding  prem  earlier would cause the simplifier to loop*)
by (cut_facts_tac [prem] 1);
by (fast_tac (ZF_cs addSEs [mem_irrefl]) 1);
qed "inj_succ_succD";

val [prem] = goalw Cardinal.thy [lepoll_def]
    "m:nat ==> ALL n: nat. m lepoll n --> m le n";
by (nat_ind_tac "m" [prem] 1);
by (fast_tac (ZF_cs addSIs [nat_0_le]) 1);
by (rtac ballI 1);
by (eres_inst_tac [("n","n")] natE 1);
by (asm_simp_tac (ZF_ss addsimps [inj_def, succI1 RS Pi_empty2]) 1);
by (fast_tac (ZF_cs addSIs [succ_leI] addSDs [inj_succ_succD]) 1);
qed "nat_lepoll_imp_le_lemma";
val nat_lepoll_imp_le = nat_lepoll_imp_le_lemma RS bspec RS mp |> standard;

goal Cardinal.thy
    "!!m n. [| m:nat; n: nat |] ==> m eqpoll n <-> m = n";
by (rtac iffI 1);
by (asm_simp_tac (ZF_ss addsimps [eqpoll_refl]) 2);
by (fast_tac (ZF_cs addIs [nat_lepoll_imp_le, le_anti_sym] 
                    addSEs [eqpollE]) 1);
qed "nat_eqpoll_iff";

goalw Cardinal.thy [Card_def,cardinal_def]
    "!!n. n: nat ==> Card(n)";
by (rtac (Least_equality RS ssubst) 1);
by (REPEAT_FIRST (ares_tac [eqpoll_refl, nat_into_Ord, refl]));
by (asm_simp_tac (ZF_ss addsimps [lt_nat_in_nat RS nat_eqpoll_iff]) 1);
by (fast_tac (ZF_cs addSEs [lt_irrefl]) 1);
qed "nat_into_Card";

(*Part of Kunen's Lemma 10.6*)
goal Cardinal.thy "!!n. [| succ(n) lepoll n;  n:nat |] ==> P";
by (rtac (nat_lepoll_imp_le RS lt_irrefl) 1);
by (REPEAT (ares_tac [nat_succI] 1));
qed "succ_lepoll_natE";


(*** The first infinite cardinal: Omega, or nat ***)

(*This implies Kunen's Lemma 10.6*)
goal Cardinal.thy "!!n. [| n<i;  n:nat |] ==> ~ i lepoll n";
by (rtac notI 1);
by (rtac succ_lepoll_natE 1 THEN assume_tac 2);
by (rtac lepoll_trans 1 THEN assume_tac 2);
by (etac ltE 1);
by (REPEAT (ares_tac [Ord_succ_subsetI RS subset_imp_lepoll] 1));
qed "lt_not_lepoll";

goal Cardinal.thy "!!i n. [| Ord(i);  n:nat |] ==> i eqpoll n <-> i=n";
by (rtac iffI 1);
by (asm_simp_tac (ZF_ss addsimps [eqpoll_refl]) 2);
by (rtac Ord_linear_lt 1);
by (REPEAT_SOME (eresolve_tac [asm_rl, nat_into_Ord]));
by (etac (lt_nat_in_nat RS nat_eqpoll_iff RS iffD1) 1 THEN
    REPEAT (assume_tac 1));
by (rtac (lt_not_lepoll RS notE) 1 THEN (REPEAT (assume_tac 1)));
by (etac eqpoll_imp_lepoll 1);
qed "Ord_nat_eqpoll_iff";

goalw Cardinal.thy [Card_def,cardinal_def] "Card(nat)";
by (rtac (Least_equality RS ssubst) 1);
by (REPEAT_FIRST (ares_tac [eqpoll_refl, Ord_nat, refl]));
by (etac ltE 1);
by (asm_simp_tac (ZF_ss addsimps [eqpoll_iff, lt_not_lepoll, ltI]) 1);
qed "Card_nat";

(*Allows showing that |i| is a limit cardinal*)
goal Cardinal.thy  "!!i. nat le i ==> nat le |i|";
by (rtac (Card_nat RS Card_cardinal_eq RS subst) 1);
by (etac cardinal_mono 1);
qed "nat_le_cardinal";


(*** Towards Cardinal Arithmetic ***)
(** Congruence laws for successor, cardinal addition and multiplication **)

val case_ss = ZF_ss addsimps [Inl_iff, Inl_Inr_iff, Inr_iff, Inr_Inl_iff,
			      case_Inl, case_Inr, InlI, InrI];

val bij_inverse_ss =
    case_ss addsimps [bij_is_fun RS apply_type,
		      bij_converse_bij RS bij_is_fun RS apply_type,
		      left_inverse_bij, right_inverse_bij];


(*Congruence law for  cons  under equipollence*)
goalw Cardinal.thy [lepoll_def]
    "!!A B. [| A lepoll B;  b ~: B |] ==> cons(a,A) lepoll cons(b,B)";
by (safe_tac ZF_cs);
by (res_inst_tac [("x", "lam y: cons(a,A).if(y=a, b, f`y)")] exI 1);
by (res_inst_tac [("d","%z.if(z:B, converse(f)`z, a)")] 
    lam_injective 1);
by (asm_simp_tac (ZF_ss addsimps [inj_is_fun RS apply_type, cons_iff]
                        setloop etac consE') 1);
by (asm_simp_tac (ZF_ss addsimps [inj_is_fun RS apply_type, left_inverse]
                        setloop etac consE') 1);
qed "cons_lepoll_cong";

goal Cardinal.thy
    "!!A B. [| A eqpoll B;  a ~: A;  b ~: B |] ==> cons(a,A) eqpoll cons(b,B)";
by (asm_full_simp_tac (ZF_ss addsimps [eqpoll_iff, cons_lepoll_cong]) 1);
qed "cons_eqpoll_cong";

(*Congruence law for  succ  under equipollence*)
goalw Cardinal.thy [succ_def]
    "!!A B. A eqpoll B ==> succ(A) eqpoll succ(B)";
by (REPEAT (ares_tac [cons_eqpoll_cong, mem_not_refl] 1));
qed "succ_eqpoll_cong";

(*Congruence law for + under equipollence*)
goalw Cardinal.thy [eqpoll_def]
    "!!A B C D. [| A eqpoll C;  B eqpoll D |] ==> A+B eqpoll C+D";
by (safe_tac ZF_cs);
by (rtac exI 1);
by (res_inst_tac [("c", "case(%x. Inl(f`x), %y. Inr(fa`y))"),
	 ("d", "case(%x. Inl(converse(f)`x), %y. Inr(converse(fa)`y))")] 
    lam_bijective 1);
by (safe_tac (ZF_cs addSEs [sumE]));
by (ALLGOALS (asm_simp_tac bij_inverse_ss));
qed "sum_eqpoll_cong";

(*Congruence law for * under equipollence*)
goalw Cardinal.thy [eqpoll_def]
    "!!A B C D. [| A eqpoll C;  B eqpoll D |] ==> A*B eqpoll C*D";
by (safe_tac ZF_cs);
by (rtac exI 1);
by (res_inst_tac [("c", "split(%x y. <f`x, fa`y>)"),
		  ("d", "split(%x y. <converse(f)`x, converse(fa)`y>)")] 
    lam_bijective 1);
by (safe_tac ZF_cs);
by (ALLGOALS (asm_simp_tac bij_inverse_ss));
qed "prod_eqpoll_cong";

goalw Cardinal.thy [eqpoll_def]
    "!!f. [| f: inj(A,B);  A Int B = 0 |] ==> A Un (B - range(f)) eqpoll B";
by (rtac exI 1);
by (res_inst_tac [("c", "%x. if(x:A, f`x, x)"),
		  ("d", "%y. if(y: range(f), converse(f)`y, y)")] 
    lam_bijective 1);
by (fast_tac (ZF_cs addSIs [if_type, apply_type] addIs [inj_is_fun]) 1);
by (asm_simp_tac 
    (ZF_ss addsimps [inj_converse_fun RS apply_funtype]
           setloop split_tac [expand_if]) 1);
by (asm_simp_tac (ZF_ss addsimps [inj_is_fun RS apply_rangeI, left_inverse]
                        setloop etac UnE') 1);
by (asm_simp_tac 
    (ZF_ss addsimps [inj_converse_fun RS apply_funtype, right_inverse]
           setloop split_tac [expand_if]) 1);
by (fast_tac (ZF_cs addEs [equals0D]) 1);
qed "inj_disjoint_eqpoll";
