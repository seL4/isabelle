(*  Title:      ZF/AC/AC16_WO4.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

  The proof of AC16(n, k) ==> WO4(n-k)
*)

open AC16_WO4;

(* ********************************************************************** *)
(* The case of finite set                                                 *)
(* ********************************************************************** *)

goalw thy [Finite_def] "!!A. [| Finite(A); 0<m; m:nat |] ==>  \
\       EX a f. Ord(a) & domain(f) = a &  \
\               (UN b<a. f`b) = A & (ALL b<a. f`b lepoll m)";
by (etac bexE 1);
by (dresolve_tac [eqpoll_sym RS (eqpoll_def RS def_imp_iff RS iffD1)] 1);
by (etac exE 1);
by (res_inst_tac [("x","n")] exI 1);
by (res_inst_tac [("x","lam i:n. {f`i}")] exI 1);
by (asm_full_simp_tac AC_ss 1);
by (rewrite_goals_tac [bij_def, surj_def]);
by (fast_tac (AC_cs addSIs [ltI, nat_into_Ord, lam_funtype RS domain_of_fun,
        equalityI, singleton_eqpoll_1 RS eqpoll_imp_lepoll RS lepoll_trans,
        nat_1_lepoll_iff RS iffD2]
        addSEs [apply_type, ltE]) 1);
val lemma1 = result();

(* ********************************************************************** *)
(* The case of infinite set                                               *)
(* ********************************************************************** *)

(* well_ord(x,r) ==> well_ord({{y,z}. y:x}, Something(x,z))  **)
val well_ord_paired = standard (paired_bij RS bij_is_inj RS well_ord_rvimage);

goal thy "!!A. [| A lepoll B; ~ A lepoll C |] ==> ~ B lepoll C";
by (fast_tac (FOL_cs addEs [notE, lepoll_trans]) 1);
val lepoll_trans1 = result();

goalw thy [lepoll_def]
        "!!X.[| Y lepoll X; well_ord(X, R) |] ==> EX S. well_ord(Y, S)";
by (fast_tac (AC_cs addSEs [well_ord_rvimage]) 1);
val well_ord_lepoll = result();

goal thy "!!X. [| well_ord(X,R); well_ord(Y,S)  \
\               |] ==> EX T. well_ord(X Un Y, T)";
by (eresolve_tac [well_ord_radd RS (Un_lepoll_sum RS well_ord_lepoll)] 1);
by (assume_tac 1);
val well_ord_Un = result();

(* ********************************************************************** *)
(* There exists a well ordered set y such that ...                        *)
(* ********************************************************************** *)

goal thy "EX y R. well_ord(y,R) & x Int y = 0 & ~y lepoll z & ~Finite(y)";
by (res_inst_tac [("x","{{a,x}. a:nat Un  Hartog(z)}")] exI 1);
by (resolve_tac [Ord_nat RS well_ord_Memrel RS (Ord_Hartog RS
                well_ord_Memrel RSN (2, well_ord_Un)) RS exE] 1);
by (fast_tac (AC_cs addSIs [Ord_Hartog, well_ord_Memrel, well_ord_paired,
        equals0I, HartogI RSN (2, lepoll_trans1),
        subset_imp_lepoll RS (paired_eqpoll RS eqpoll_sym RS
        eqpoll_imp_lepoll RSN (2, lepoll_trans))]
        addSEs [RepFunE, nat_not_Finite RS notE] addEs [mem_asym]
        addSDs [Un_upper1 RS subset_imp_lepoll RS lepoll_Finite,
        paired_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll
        RS lepoll_Finite]) 1);
val lemma2 = result();

val [prem] = goal thy "~Finite(B) ==> ~Finite(A Un B)";
by (fast_tac (AC_cs
        addSIs [subset_imp_lepoll RS (prem RSN (2, lepoll_infinite))]) 1);
val infinite_Un = result();

(* ********************************************************************** *)
(* There is a v : s_u such that k lepoll x Int y (in our case succ(k))    *)
(* The idea of the proof is the following :                               *)
(* Suppose not, i.e. every element of s_u has exactly k-1 elements of y   *)
(* Thence y is less than or equipollent to {v:Pow(x). v eqpoll n#-k}      *)
(*   We have obtained this result in two steps :                          *)
(*   1. y is less than or equipollent to {v:s_u. a <= v}                  *)
(*      where a is certain k-2 element subset of y                        *)
(*   2. {v:s_u. a <= v} is less than or equipollent                       *)
(*      to {v:Pow(x). v eqpoll n-k}                                       *)
(* ********************************************************************** *)

(*Proof simplified by LCP*)
goal thy "!!A. [| ~(EX x:A. f`x=y); f : inj(A, B); y:B |]  \
\       ==> (lam a:succ(A). if(a=A, y, f`a)) : inj(succ(A), B)";
by (res_inst_tac [("d","%z. if(z=y, A, converse(f)`z)")] lam_injective 1);
by (ALLGOALS
    (asm_simp_tac 
     (ZF_ss addsimps [inj_is_fun RS apply_type, left_inverse] 
      setloop (split_tac [expand_if] ORELSE' step_tac ZF_cs))));
val succ_not_lepoll_lemma = result();

goalw thy [lepoll_def, eqpoll_def, bij_def, surj_def]
        "!!A. [| ~A eqpoll B; A lepoll B |] ==> succ(A) lepoll B";
by (fast_tac (AC_cs addSEs [succ_not_lepoll_lemma, inj_is_fun]) 1);
val succ_not_lepoll_imp_eqpoll = result();

val [prem] = goalw thy [s_u_def]
        "(ALL v:s_u(u, t_n, k, y). k eqpoll v Int y ==> False)  \
\       ==> EX v : s_u(u, t_n, k, y). succ(k) lepoll v Int y";
by (excluded_middle_tac "?P" 1 THEN (assume_tac 2));
by (resolve_tac [prem RS FalseE] 1);
by (rtac ballI 1);
by (etac CollectE 1);
by (etac conjE 1);
by (etac swap 1);
by (fast_tac (AC_cs addSEs [succ_not_lepoll_imp_eqpoll]) 1);
val suppose_not = result();

(* ********************************************************************** *)
(* There is a k-2 element subset of y                                     *)
(* ********************************************************************** *)

goalw thy [lepoll_def, eqpoll_def]
        "!!X. [| n:nat; nat lepoll X |] ==> EX Y. Y<=X & n eqpoll Y";
by (fast_tac (FOL_cs addSDs [Ord_nat RSN (2, OrdmemD) RSN (2, restrict_inj)]
        addSIs [subset_refl]
        addSEs [restrict_bij, inj_is_fun RS fun_is_rel RS image_subset]) 1);
val nat_lepoll_imp_ex_eqpoll_n = result();

val ordertype_eqpoll =
        ordermap_bij RS (exI RS (eqpoll_def RS def_imp_iff RS iffD2));

goal thy "!!y. [| well_ord(y,R); ~Finite(y); n:nat  \
\       |] ==> EX z. z<=y & n eqpoll z";
by (etac nat_lepoll_imp_ex_eqpoll_n 1);
by (resolve_tac [ordertype_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll
        RSN (2, lepoll_trans)] 1 THEN (assume_tac 2));
by (fast_tac (AC_cs addSIs [nat_le_infinite_Ord RS le_imp_lepoll]
                addSEs [Ord_ordertype, ordertype_eqpoll RS eqpoll_imp_lepoll
                        RS lepoll_infinite]) 1);
val ex_subset_eqpoll_n = result();

goalw thy [lesspoll_def] "!!n. n: nat ==> n lesspoll nat";
by (fast_tac (AC_cs addSEs [Ord_nat RSN (2, ltI) RS leI RS le_imp_lepoll,
        eqpoll_sym RS eqpoll_imp_lepoll]
        addIs [Ord_nat RSN (2, nat_succI RS ltI) RS leI
        RS le_imp_lepoll RS lepoll_trans RS succ_lepoll_natE]) 1);
val n_lesspoll_nat = result();

goal thy "!!y. [| well_ord(y,R); ~Finite(y); k eqpoll a; a <= y; k: nat |]  \
\       ==> y - a eqpoll y";
by (fast_tac (empty_cs addIs [lepoll_lesspoll_lesspoll]
        addSIs [Card_cardinal, Diff_lesspoll_eqpoll_Card RS eqpoll_trans,
                Card_cardinal RS Card_is_Ord RS nat_le_infinite_Ord
                RS le_imp_lepoll]
        addSEs [well_ord_cardinal_eqpoll,
                well_ord_cardinal_eqpoll RS eqpoll_sym,
                eqpoll_sym RS eqpoll_imp_lepoll,
                n_lesspoll_nat RS lesspoll_lepoll_lesspoll,
                well_ord_cardinal_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll
                RS lepoll_infinite]) 1);
val Diff_Finite_eqpoll = result();

goal thy "!!x. [| a<=y; b:y-a; u:x |] ==> cons(b, cons(u, a)) : Pow(x Un y)";
by (fast_tac AC_cs 1);
val cons_cons_subset = result();

goal thy "!!x. [| a eqpoll k; a<=y; b:y-a; u:x; x Int y = 0  \
\       |] ==> cons(b, cons(u, a)) eqpoll succ(succ(k))";
by (fast_tac (AC_cs addSIs [cons_eqpoll_succ] addEs [equals0D]) 1);
val cons_cons_eqpoll = result();

goalw thy [s_u_def] "s_u(u, t_n, k, y) <= t_n";
by (fast_tac AC_cs 1);
val s_u_subset = result();

goalw thy [s_u_def, succ_def]
        "!!w. [| w:t_n; cons(b,cons(u,a)) <= w; a <= y; b : y-a; k eqpoll a  \
\       |] ==> w: s_u(u, t_n, succ(k), y)";
by (fast_tac (AC_cs addDs [eqpoll_imp_lepoll RS cons_lepoll_cong]
                addSEs [subset_imp_lepoll RSN (2, lepoll_trans)]) 1);
val s_uI = result();

goalw thy [s_u_def] "!!v. v : s_u(u, t_n, k, y) ==> u : v";
by (fast_tac AC_cs 1);
val in_s_u_imp_u_in = result();

goal thy
        "!!y. [| ALL z:{z: Pow(x Un y) . z eqpoll succ(succ(k))}.  \
\       EX! w. w:t_n & z <= w; \
\       k eqpoll a; a <= y; b : y - a; u : x; x Int y = 0 |]  \
\       ==> EX! c. c:{v:s_u(u, t_n, succ(k), y). a <= v} & b:c";
by (etac ballE 1);
by (fast_tac (FOL_cs addSIs [CollectI, cons_cons_subset,
                eqpoll_sym RS cons_cons_eqpoll]) 2);
by (etac ex1E 1);
by (res_inst_tac [("a","w")] ex1I 1);
by (rtac conjI 1);
by (rtac CollectI 1);
by (fast_tac (FOL_cs addSEs [s_uI]) 1);
by (fast_tac AC_cs 1);
by (fast_tac AC_cs 1);
by (etac allE 1);
by (etac impE 1);
by (assume_tac 2);
by (fast_tac (AC_cs addSEs [s_u_subset RS subsetD, in_s_u_imp_u_in]) 1);
val ex1_superset_a = result();

goal thy
        "!!A. [| succ(k) eqpoll A; k eqpoll B; B <= A; a : A-B; k:nat  \
\       |] ==> A = cons(a, B)";
by (rtac equalityI 1);
by (fast_tac AC_cs 2);
by (resolve_tac [Diff_eq_0_iff RS iffD1] 1);
by (rtac equals0I 1);
by (dresolve_tac [eqpoll_sym RS eqpoll_imp_lepoll] 1);
by (dresolve_tac [eqpoll_sym RS cons_eqpoll_succ] 1);
by (fast_tac AC_cs 1);
by (dtac cons_eqpoll_succ 1);
by (fast_tac AC_cs 1);
by (fast_tac (AC_cs addSIs [nat_succI]
        addSEs [[eqpoll_sym RS eqpoll_imp_lepoll, subset_imp_lepoll] MRS
        (lepoll_trans RS lepoll_trans) RS succ_lepoll_natE]) 1);
val set_eq_cons = result();

goal thy
        "!!y. [| ALL z:{z: Pow(x Un y) . z eqpoll succ(succ(k))}.  \
\       EX! w. w:t_n & z <= w; \
\       ALL v:s_u(u, t_n, succ(k), y). succ(k) eqpoll v Int y;  \
\       k eqpoll a; a <= y; b : y - a; u : x; x Int y = 0; k:nat   \
\       |] ==> (THE c. c:{v:s_u(u, t_n, succ(k), y). a <= v} & b:c)  \
\       Int y = cons(b, a)";
by (dresolve_tac [ex1_superset_a RS theI] 1 THEN REPEAT (assume_tac 1));
by (rtac set_eq_cons 1);
by (REPEAT (fast_tac AC_cs 1));
val the_eq_cons = result();

goal thy "!!a. [| cons(x,a) = cons(y,a); x~: a |] ==> x = y ";
by (fast_tac (AC_cs addSEs [equalityE]) 1);
val cons_eqE = result();

goal thy "!!A. A = B ==> A Int C = B Int C";
by (asm_simp_tac AC_ss 1);
val eq_imp_Int_eq = result();

goal thy "!!a. [| a=b; a=c; b=d |] ==> c=d";
by (asm_full_simp_tac AC_ss 1);
val msubst = result();

(* ********************************************************************** *)
(*   1. y is less than or equipollent to {v:s_u. a <= v}                  *)
(*      where a is certain k-2 element subset of y                        *)
(* ********************************************************************** *)

goal thy
        "!!y. [| ALL z:{z: Pow(x Un y) . z eqpoll succ(succ(k))}.  \
\       EX! w. w:t_n & z <= w; \
\       ALL v:s_u(u, t_n, succ(k), y). succ(k) eqpoll v Int y;  \
\       well_ord(y,R); ~Finite(y); k eqpoll a; a <= y;  \
\       k:nat; u:x; x Int y = 0 |]  \
\       ==> y lepoll {v:s_u(u, t_n, succ(k), y). a <= v}";
by (resolve_tac [Diff_Finite_eqpoll RS eqpoll_sym RS 
        eqpoll_imp_lepoll RS lepoll_trans] 1
        THEN REPEAT (assume_tac 1));
by (res_inst_tac [("f3","lam b:y-a.  \
\       THE c. c:{v:s_u(u, t_n, succ(k), y). a <= v} & b:c")]
        (exI RS (lepoll_def RS def_imp_iff RS iffD2)) 1);
by (resolve_tac [inj_def RS def_imp_eq RS ssubst] 1);
by (rtac CollectI 1);
by (rtac lam_type 1);
by (resolve_tac [ex1_superset_a RS theI RS conjunct1] 1
        THEN REPEAT (assume_tac 1));
by (rtac ballI 1);
by (rtac ballI 1);
by (resolve_tac [beta RS ssubst] 1 THEN (assume_tac 1));
by (resolve_tac [beta RS ssubst] 1 THEN (assume_tac 1));
by (rtac impI 1);
by (rtac cons_eqE 1);
by (fast_tac AC_cs 2);
by (dres_inst_tac [("A","THE c. ?P(c)"), ("C","y")] eq_imp_Int_eq 1);
by (eresolve_tac [[asm_rl, the_eq_cons, the_eq_cons] MRS msubst] 1
        THEN REPEAT (assume_tac 1));
val y_lepoll_subset_s_u = result();

(* ********************************************************************** *)
(* some arithmetic                                                        *)
(* ********************************************************************** *)

goal thy 
        "!!k. [| k:nat; m:nat |] ==>  \
\       ALL A B. A eqpoll k #+ m & k lepoll B & B<=A --> A-B lepoll m";
by (eres_inst_tac [("n","k")] nat_induct 1);
by (simp_tac (AC_ss addsimps [add_0]) 1);
by (fast_tac (AC_cs addIs [eqpoll_imp_lepoll RS
        (Diff_subset RS subset_imp_lepoll RS lepoll_trans)]) 1);
by (REPEAT (resolve_tac [allI,impI] 1));
by (resolve_tac [succ_lepoll_imp_not_empty RS not_emptyE] 1);
by (fast_tac AC_cs 1);
by (eres_inst_tac [("x","A - {xa}")] allE 1);
by (eres_inst_tac [("x","B - {xa}")] allE 1);
by (etac impE 1);
by (asm_full_simp_tac (AC_ss addsimps [add_succ]) 1);
by (fast_tac (AC_cs addSIs [Diff_sing_eqpoll, lepoll_Diff_sing]) 1);
by (res_inst_tac [("P","%z. z lepoll m")] subst 1 THEN (assume_tac 2));
by (fast_tac (AC_cs addSIs [equalityI]) 1);
val eqpoll_sum_imp_Diff_lepoll_lemma = result();

goal thy "!!k. [| A eqpoll succ(k #+ m); B<=A; succ(k) lepoll B;  \
\       k:nat; m:nat |]  \
\       ==> A-B lepoll m";
by (dresolve_tac [add_succ RS ssubst] 1);
by (dresolve_tac [nat_succI RS eqpoll_sum_imp_Diff_lepoll_lemma] 1
        THEN (REPEAT (assume_tac 1)));
by (fast_tac AC_cs 1);
val eqpoll_sum_imp_Diff_lepoll = result();

(* ********************************************************************** *)
(* similar properties for eqpoll                                          *)
(* ********************************************************************** *)

goal thy 
        "!!k. [| k:nat; m:nat |] ==>  \
\       ALL A B. A eqpoll k #+ m & k eqpoll B & B<=A --> A-B eqpoll m";
by (eres_inst_tac [("n","k")] nat_induct 1);
by (fast_tac (AC_cs addSDs [eqpoll_sym RS eqpoll_imp_lepoll RS lepoll_0_is_0]
        addss (AC_ss addsimps [add_0])) 1);
by (REPEAT (resolve_tac [allI,impI] 1));
by (resolve_tac [succ_lepoll_imp_not_empty RS not_emptyE] 1);
by (fast_tac (AC_cs addSEs [eqpoll_imp_lepoll]) 1);
by (eres_inst_tac [("x","A - {xa}")] allE 1);
by (eres_inst_tac [("x","B - {xa}")] allE 1);
by (etac impE 1);
by (fast_tac (AC_cs addSIs [Diff_sing_eqpoll,
        eqpoll_sym RSN (2, Diff_sing_eqpoll) RS eqpoll_sym]
        addss (AC_ss addsimps [add_succ])) 1);
by (res_inst_tac [("P","%z. z eqpoll m")] subst 1 THEN (assume_tac 2));
by (fast_tac (AC_cs addSIs [equalityI]) 1);
val eqpoll_sum_imp_Diff_eqpoll_lemma = result();

goal thy "!!k. [| A eqpoll succ(k #+ m); B<=A; succ(k) eqpoll B;  \
\       k:nat; m:nat |]  \
\       ==> A-B eqpoll m";
by (dresolve_tac [add_succ RS ssubst] 1);
by (dresolve_tac [nat_succI RS eqpoll_sum_imp_Diff_eqpoll_lemma] 1
        THEN (REPEAT (assume_tac 1)));
by (fast_tac AC_cs 1);
val eqpoll_sum_imp_Diff_eqpoll = result();

(* ********************************************************************** *)
(* back to the second part                                                *)
(* ********************************************************************** *)

goal thy "!!w. [| x Int y = 0; w <= x Un y |]  \
\        ==> w Int (x - {u}) = w - cons(u, w Int y)";
by (fast_tac (AC_cs addSIs [equalityI] addEs [equals0D]) 1);
val w_Int_eq_w_Diff = result();

goal thy "!!w. [| w:{v:s_u(u, t_n, succ(l), y). a <= v};  \
\       l eqpoll a; t_n <= {v:Pow(x Un y). v eqpoll succ(succ(l) #+ m)};  \
\       m:nat; l:nat; x Int y = 0; u : x;  \
\       ALL v:s_u(u, t_n, succ(l), y). succ(l) eqpoll v Int y  \
\       |] ==> w Int (x - {u}) eqpoll m";
by (etac CollectE 1);
by (resolve_tac [w_Int_eq_w_Diff RS ssubst] 1 THEN (assume_tac 1));
by (fast_tac (AC_cs addSDs [s_u_subset RS subsetD]) 1);
by (fast_tac (AC_cs addEs [equals0D] addSDs [bspec]
        addDs [s_u_subset RS subsetD]
        addSEs [eqpoll_sym RS cons_eqpoll_succ RS eqpoll_sym, in_s_u_imp_u_in]
        addSIs [nat_succI, eqpoll_sum_imp_Diff_eqpoll]) 1);
val w_Int_eqpoll_m = result();

goal thy "!!m. [| 0<m; x eqpoll m; m:nat |] ==> x ~= 0";
by (fast_tac (empty_cs
        addSEs [mem_irrefl, ltE, eqpoll_succ_imp_not_empty, natE]) 1);
val eqpoll_m_not_empty = result();

goal thy
        "!!z. [| z : xa Int (x - {u}); l eqpoll a; a <= y; x Int y = 0; u:x  \
\       |] ==> cons(z, cons(u, a)) : {v: Pow(x Un y). v eqpoll succ(succ(l))}";
by (fast_tac (AC_cs addSIs [cons_eqpoll_succ] addEs [equals0D, eqpoll_sym]) 1);
val cons_cons_in = result();

(* ********************************************************************** *)
(*   2. {v:s_u. a <= v} is less than or equipollent                       *)
(*      to {v:Pow(x). v eqpoll n-k}                                       *)
(* ********************************************************************** *)

goal thy 
        "!!x. [| ALL z:{z: Pow(x Un y) . z eqpoll succ(succ(l))}.  \
\       EX! w. w:t_n & z <= w; \
\       t_n <= {v:Pow(x Un y). v eqpoll succ(succ(l) #+ m)};  \
\       0<m; m:nat; l:nat;  \
\       ALL v:s_u(u, t_n, succ(l), y). succ(l) eqpoll v Int y;  \
\       a <= y; l eqpoll a; x Int y = 0; u : x  \
\       |] ==> {v:s_u(u, t_n, succ(l), y). a <= v}  \
\               lepoll {v:Pow(x). v eqpoll m}";
by (res_inst_tac [("f3","lam w:{v:s_u(u, t_n, succ(l), y). a <= v}.  \
\       w Int (x - {u})")] 
        (exI RS (lepoll_def RS def_imp_iff RS iffD2)) 1);
by (resolve_tac [inj_def RS def_imp_eq RS ssubst] 1);
by (rtac CollectI 1);
by (rtac lam_type 1);
by (rtac CollectI 1);
by (fast_tac AC_cs 1);
by (rtac w_Int_eqpoll_m 1 THEN REPEAT (assume_tac 1));
by (simp_tac AC_ss 1);
by (REPEAT (resolve_tac [ballI, impI] 1));
by (eresolve_tac [w_Int_eqpoll_m RSN (2, eqpoll_m_not_empty) RS not_emptyE] 1
        THEN REPEAT (assume_tac 1));
by (dresolve_tac [equalityD1 RS subsetD] 1 THEN (assume_tac 1));
by (dresolve_tac [cons_cons_in RSN (2, bspec)] 1 THEN REPEAT (assume_tac 1));
by (etac ex1_two_eq 1);
by (fast_tac (AC_cs addSEs [s_u_subset RS subsetD, in_s_u_imp_u_in]) 1);
by (fast_tac (AC_cs addSEs [s_u_subset RS subsetD, in_s_u_imp_u_in]) 1);
val subset_s_u_lepoll_w = result();

goal thy "!!k. [| 0<k; k:nat |] ==> EX l:nat. k = succ(l)";
by (etac natE 1);
by (fast_tac (empty_cs addSEs [ltE, mem_irrefl]) 1);
by (fast_tac (empty_cs addSIs [refl, bexI]) 1);
val ex_eq_succ = result();

goal thy
        "!!x. [| ALL z:{z: Pow(x Un y) . z eqpoll succ(k)}.  \
\       EX! w. w:t_n & z <= w; \
\       well_ord(y,R); ~Finite(y); u:x; x Int y = 0;  \
\       t_n <= {v:Pow(x Un y). v eqpoll succ(k #+ m)};  \
\       ~ y lepoll {v:Pow(x). v eqpoll m}; 0<k; 0<m; k:nat; m:nat  \
\       |] ==> EX v : s_u(u, t_n, k, y). succ(k) lepoll v Int y";
by (rtac suppose_not 1);
by (eresolve_tac [ex_eq_succ RS bexE] 1 THEN (assume_tac 1));
by (hyp_subst_tac 1);
by (res_inst_tac [("n1","xa")] (ex_subset_eqpoll_n RS exE) 1
        THEN REPEAT (assume_tac 1));
by (etac conjE 1);
by (forward_tac [[y_lepoll_subset_s_u, subset_s_u_lepoll_w] MRS lepoll_trans] 1
        THEN REPEAT (assume_tac 1));
by (contr_tac 1);
val exists_proper_in_s_u = result();

(* ********************************************************************** *)
(* LL can be well ordered                                                 *)
(* ********************************************************************** *)

goal thy "{x:Pow(X). x lepoll 0} = {0}";
by (fast_tac (AC_cs addSDs [lepoll_0_is_0]
                    addSIs [lepoll_refl, equalityI]) 1);
val subsets_lepoll_0_eq_unit = result();

goal thy "!!X. [| well_ord(X, R); ~Finite(X); n:nat |]  \
\               ==> EX S. well_ord({Y: Pow(X) . Y eqpoll succ(n)}, S)";
by (resolve_tac [well_ord_infinite_subsets_eqpoll_X
        RS (eqpoll_def RS def_imp_iff RS iffD1) RS exE] 1
    THEN (REPEAT (assume_tac 1)));
by (fast_tac (ZF_cs addSEs [bij_is_inj RS well_ord_rvimage]) 1);
val well_ord_subsets_eqpoll_n = result();

goal thy "!!n. n:nat ==> {z:Pow(y). z lepoll succ(n)} =  \
\       {z:Pow(y). z lepoll n} Un {z:Pow(y). z eqpoll succ(n)}";
by (fast_tac (ZF_cs addIs [le_refl, leI,
                le_imp_lepoll, equalityI]
                addSDs [lepoll_succ_disj]
                addSEs [nat_into_Ord, lepoll_trans, eqpoll_imp_lepoll]) 1);
val subsets_lepoll_succ = result();

goal thy "!!n. n:nat ==>  \
\       {z:Pow(y). z lepoll n} Int {z:Pow(y). z eqpoll succ(n)} = 0";
by (fast_tac (ZF_cs addSEs [eqpoll_sym RS eqpoll_imp_lepoll 
                RS lepoll_trans RS succ_lepoll_natE]
                addSIs [equals0I]) 1);
val Int_empty = result();

(* ********************************************************************** *)
(* unit set is well-ordered by the empty relation                         *)
(* ********************************************************************** *)

goalw thy [irrefl_def, trans_on_def, part_ord_def, linear_def, tot_ord_def]
        "tot_ord({a},0)";
by (simp_tac ZF_ss 1);
val tot_ord_unit = result();

goalw thy [wf_on_def, wf_def] "wf[{a}](0)";
by (fast_tac (ZF_cs addSIs [equalityI]) 1);
val wf_on_unit = result();

goalw thy [well_ord_def] "well_ord({a},0)";
by (simp_tac (ZF_ss addsimps [tot_ord_unit, wf_on_unit]) 1);
val well_ord_unit = result();

(* ********************************************************************** *)
(* well_ord_subsets_lepoll_n                                              *)
(* ********************************************************************** *)

goal thy "!!y r. [| well_ord(y,r); ~Finite(y); n:nat |] ==>  \
\       EX R. well_ord({z:Pow(y). z lepoll n}, R)";
by (etac nat_induct 1);
by (fast_tac (ZF_cs addSIs [well_ord_unit]
        addss (ZF_ss addsimps [subsets_lepoll_0_eq_unit])) 1);
by (etac exE 1);
by (eresolve_tac [well_ord_subsets_eqpoll_n RS exE] 1 
        THEN REPEAT (assume_tac 1));
by (asm_simp_tac (ZF_ss addsimps [subsets_lepoll_succ]) 1);
by (dtac well_ord_radd 1 THEN (assume_tac 1));
by (eresolve_tac [Int_empty RS disj_Un_eqpoll_sum RS 
                (eqpoll_def RS def_imp_iff RS iffD1) RS exE] 1);
by (fast_tac (ZF_cs addSEs [bij_is_inj RS well_ord_rvimage]) 1);
val well_ord_subsets_lepoll_n = result();

goalw thy [LL_def, MM_def]
        "!!x. t_n <= {v:Pow(x Un y). v eqpoll n}  \
\               ==> LL(t_n, k, y) <= {z:Pow(y). z lepoll n}";
by (fast_tac (AC_cs addSEs [RepFunE]
        addIs [subset_imp_lepoll RS (eqpoll_imp_lepoll
                RSN (2, lepoll_trans))]) 1);
val LL_subset = result();

goal thy "!!x. [| t_n <= {v:Pow(x Un y). v eqpoll n}; \
\               well_ord(y, R); ~Finite(y); n:nat  \
\               |] ==> EX S. well_ord(LL(t_n, k, y), S)";
by (fast_tac (FOL_cs addIs [exI]
                addSEs [LL_subset RSN (2,  well_ord_subset)]
                addEs [well_ord_subsets_lepoll_n RS exE]) 1);
val well_ord_LL = result();

(* ********************************************************************** *)
(* every element of LL is a contained in exactly one element of MM        *)
(* ********************************************************************** *)

goalw thy [MM_def, LL_def]
        "!!x. [| ALL z:{z: Pow(x Un y) . z eqpoll k}. EX! w. w:t_n & z <= w; \
\       t_n <= {v:Pow(x Un y). v eqpoll n}; \
\       v:LL(t_n, k, y)  \
\       |] ==> EX! w. w:MM(t_n, k, y) & v<=w";
by (step_tac (AC_cs addSEs [RepFunE]) 1);
by (resolve_tac [lepoll_imp_eqpoll_subset RS exE] 1 THEN (assume_tac 1));
by (eres_inst_tac [("x","xa")] ballE 1);
by (fast_tac (AC_cs addSEs [eqpoll_sym]) 2);
by (res_inst_tac [("a","v")] ex1I 1);
by (fast_tac AC_cs 1);
by (etac ex1E 1);
by (res_inst_tac [("x","v")] allE 1 THEN (assume_tac 1));
by (eres_inst_tac [("x","xb")] allE 1);
by (fast_tac AC_cs 1);
val unique_superset_in_MM = result();

(* ********************************************************************** *)
(* The function GG satisfies the conditions of WO4                        *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* The union of appropriate values is the whole x                         *)
(* ********************************************************************** *)

goal thy
        "!!x. [| ALL z:{z: Pow(x Un y) . z eqpoll succ(k)}.  \
\       EX! w. w:t_n & z <= w; \
\       well_ord(y,R); ~Finite(y); u:x; x Int y = 0;  \
\       t_n <= {v:Pow(x Un y). v eqpoll succ(k #+ m)};  \
\       ~ y lepoll {v:Pow(x). v eqpoll m}; 0<k; 0<m; k:nat; m:nat  \
\       |] ==> EX w:MM(t_n, succ(k), y). u:w";
by (eresolve_tac [exists_proper_in_s_u RS bexE] 1
        THEN REPEAT (assume_tac 1));
by (rewrite_goals_tac [MM_def, s_u_def]);
by (fast_tac AC_cs 1);
val exists_in_MM = result();

goalw thy [LL_def] "!!w. w : MM(t_n, k, y) ==> w Int y : LL(t_n, k, y)";
by (fast_tac AC_cs 1);
val Int_in_LL = result();

goalw thy [MM_def] "MM(t_n, k, y) <= t_n";
by (fast_tac AC_cs 1);
val MM_subset = result();

goal thy 
        "!!x. [| ALL z:{z: Pow(x Un y) . z eqpoll succ(k)}.  \
\       EX! w. w:t_n & z <= w; \
\       well_ord(y,R); ~Finite(y); u:x; x Int y = 0;  \
\       t_n <= {v:Pow(x Un y). v eqpoll succ(k #+ m)};  \
\       ~ y lepoll {v:Pow(x). v eqpoll m}; 0<k; 0<m; k:nat; m:nat  \
\       |] ==> EX w:LL(t_n, succ(k), y). u:GG(t_n, succ(k), y)`w";
by (forward_tac [exists_in_MM] 1 THEN REPEAT (assume_tac 1));
by (etac bexE 1);
by (res_inst_tac [("x","w Int y")] bexI 1);
by (etac Int_in_LL 2);
by (rewtac GG_def);
by (asm_full_simp_tac (AC_ss addsimps [Int_in_LL]) 1);
by (eresolve_tac [unique_superset_in_MM RS the_equality2 RS ssubst] 1
        THEN (assume_tac 1));
by (REPEAT (fast_tac (AC_cs addEs [equals0D] addSEs [Int_in_LL]) 1));
val exists_in_LL = result();

goalw thy [LL_def] 
        "!!x. [| ALL z:{z: Pow(x Un y) . z eqpoll k}. EX! w. w:t_n & z <= w; \
\       t_n <= {v:Pow(x Un y). v eqpoll n};  \
\       v : LL(t_n, k, y) |]  \
\       ==> v = (THE x. x : MM(t_n, k, y) & v <= x) Int y";
by (fast_tac (AC_cs addSEs [Int_in_LL,
                unique_superset_in_MM RS the_equality2 RS ssubst]) 1);
val in_LL_eq_Int = result();

goal thy  
        "!!x. [| ALL z:{z: Pow(x Un y) . z eqpoll k}. EX! w. w:t_n & z <= w; \
\       t_n <= {v:Pow(x Un y). v eqpoll n};  \
\       v : LL(t_n, k, y) |]  \
\       ==> (THE x. x : MM(t_n, k, y) & v <= x) <= x Un y";
by (fast_tac (AC_cs addSDs [unique_superset_in_MM RS theI RS conjunct1 RS 
        (MM_subset RS subsetD)]) 1);
val the_in_MM_subset = result();

goalw thy [GG_def] 
        "!!x. [| ALL z:{z: Pow(x Un y) . z eqpoll k}. EX! w. w:t_n & z <= w; \
\       t_n <= {v:Pow(x Un y). v eqpoll n};  \
\       v : LL(t_n, k, y) |]  \
\       ==> GG(t_n, k, y) ` v <= x";
by (asm_full_simp_tac AC_ss 1);
by (forward_tac [the_in_MM_subset] 1 THEN REPEAT (assume_tac 1));
by (dtac in_LL_eq_Int 1 THEN REPEAT (assume_tac 1));
by (rtac subsetI 1);
by (etac DiffE 1);
by (etac swap 1);
by (fast_tac (AC_cs addEs [ssubst]) 1);
val GG_subset = result();

goal thy  
        "!!x. [| well_ord(LL(t_n, succ(k), y), S);  \
\       ALL z:{z: Pow(x Un y) . z eqpoll succ(k)}. EX! w. w:t_n & z <= w; \
\       well_ord(y,R); ~Finite(y); x Int y = 0;  \
\       t_n <= {v:Pow(x Un y). v eqpoll succ(k #+ m)};  \
\       ~ y lepoll {v:Pow(x). v eqpoll m}; 0<k; 0<m; k:nat; m:nat  \
\       |] ==> (UN b<ordertype(LL(t_n, succ(k), y), S).  \
\       (GG(t_n, succ(k), y)) `  \
\       (converse(ordermap(LL(t_n, succ(k), y), S)) ` b)) = x";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac OUN_E 1);
by (eresolve_tac [GG_subset RS subsetD] 1 THEN TRYALL assume_tac);
by (eresolve_tac [ordermap_bij RS bij_converse_bij RS
                bij_is_fun RS apply_type] 1);
by (etac ltD 1);
by (rtac subsetI 1);
by (eresolve_tac [exists_in_LL RS bexE] 1 THEN REPEAT (assume_tac 1));
by (rtac OUN_I 1);
by (resolve_tac [Ord_ordertype RSN (2, ltI)] 1 THEN (assume_tac 2));
by (eresolve_tac [ordermap_type RS apply_type] 1);
by (eresolve_tac [ordermap_bij RS bij_is_inj RS left_inverse RS ssubst] 1
        THEN REPEAT (assume_tac 1));
val OUN_eq_x = result();

(* ********************************************************************** *)
(* Every element of the family is less than or equipollent to n-k (m)     *)
(* ********************************************************************** *)

goalw thy [MM_def]
        "!!w. [| w : MM(t_n, k, y); t_n <= {v:Pow(x Un y). v eqpoll n}  \
\       |] ==> w eqpoll n";
by (fast_tac AC_cs 1);
val in_MM_eqpoll_n = result();

goalw thy [LL_def, MM_def]
        "!!w. w : LL(t_n, k, y) ==> k lepoll w";
by (fast_tac AC_cs 1);
val in_LL_eqpoll_n = result();

goalw thy [GG_def] 
        "!!x. [|  \
\       ALL z:{z: Pow(x Un y) . z eqpoll succ(k)}. EX! w. w:t_n & z <= w; \
\       t_n <= {v:Pow(x Un y). v eqpoll succ(k #+ m)};  \
\       well_ord(LL(t_n, succ(k), y), S); k:nat; m:nat |]  \
\       ==> ALL b<ordertype(LL(t_n, succ(k), y), S).  \
\       (GG(t_n, succ(k), y)) `  \
\       (converse(ordermap(LL(t_n, succ(k), y), S)) ` b) lepoll m";
by (rtac oallI 1);
by (asm_full_simp_tac (AC_ss addsimps [ltD,
        ordermap_bij RS bij_converse_bij RS bij_is_fun RS apply_type]) 1);
by (rtac eqpoll_sum_imp_Diff_lepoll 1);
by (REPEAT (fast_tac (FOL_cs addSDs [ltD]
        addSIs [eqpoll_sum_imp_Diff_lepoll, in_LL_eqpoll_n]
        addEs [unique_superset_in_MM RS theI RS conjunct1 RS in_MM_eqpoll_n,
        in_LL_eq_Int RS equalityD1 RS (Int_lower1 RSN (2, subset_trans)),
        ordermap_bij RS bij_converse_bij RS bij_is_fun RS apply_type]) 1));
val all_in_lepoll_m = result();

(* ********************************************************************** *)
(* The main theorem AC16(n, k) ==> WO4(n-k)                               *)
(* ********************************************************************** *)

goalw thy [AC16_def,WO4_def]
        "!!n k. [| AC16(k #+ m, k); 0 < k; 0 < m; k:nat; m:nat |] ==> WO4(m)";
by (rtac allI 1);
by (excluded_middle_tac "Finite(A)" 1);
by (rtac lemma1 2 THEN REPEAT (assume_tac 2));
by (resolve_tac [lemma2 RS revcut_rl] 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (eres_inst_tac [("x","A Un y")] allE 1);
by (forward_tac [infinite_Un] 1 THEN (mp_tac 1));
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (resolve_tac [well_ord_LL RS exE] 1 THEN REPEAT (assume_tac 1));
by (fast_tac (AC_cs addSIs [nat_succI, add_type]) 1);
by (res_inst_tac [("x","ordertype(LL(T, succ(k), y), x)")] exI 1);
by (res_inst_tac [("x","lam b:ordertype(LL(T, succ(k), y), x).  \
\       (GG(T, succ(k), y)) `  \
\       (converse(ordermap(LL(T, succ(k), y), x)) ` b)")] exI 1);
by (simp_tac AC_ss 1);
by (fast_tac (empty_cs addSIs [conjI, lam_funtype RS domain_of_fun]
        addSEs [Ord_ordertype, all_in_lepoll_m, OUN_eq_x]) 1);
qed "AC16_WO4";
