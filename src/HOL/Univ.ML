(*  Title:      HOL/univ
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For univ.thy
*)

open Univ;

(** LEAST -- the least number operator **)


val [prem1,prem2] = goalw Univ.thy [Least_def]
    "[| P(k);  !!x. x<k ==> ~P(x) |] ==> (LEAST x.P(x)) = k";
by (rtac select_equality 1);
by (fast_tac (HOL_cs addSIs [prem1,prem2]) 1);
by (cut_facts_tac [less_linear] 1);
by (fast_tac (HOL_cs addSIs [prem1] addSDs [prem2]) 1);
qed "Least_equality";

val [prem] = goal Univ.thy "P(k) ==> P(LEAST x.P(x))";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("n","k")] less_induct 1);
by (rtac impI 1);
by (rtac classical 1);
by (res_inst_tac [("s","n")] (Least_equality RS ssubst) 1);
by (assume_tac 1);
by (assume_tac 2);
by (fast_tac HOL_cs 1);
qed "LeastI";

(*Proof is almost identical to the one above!*)
val [prem] = goal Univ.thy "P(k) ==> (LEAST x.P(x)) <= k";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("n","k")] less_induct 1);
by (rtac impI 1);
by (rtac classical 1);
by (res_inst_tac [("s","n")] (Least_equality RS ssubst) 1);
by (assume_tac 1);
by (rtac le_refl 2);
by (fast_tac (HOL_cs addIs [less_imp_le,le_trans]) 1);
qed "Least_le";

val [prem] = goal Univ.thy "k < (LEAST x.P(x)) ==> ~P(k)";
by (rtac notI 1);
by (etac (rewrite_rule [le_def] Least_le RS notE) 1);
by (rtac prem 1);
qed "not_less_Least";


(** apfst -- can be used in similar type definitions **)

goalw Univ.thy [apfst_def] "apfst f (a,b) = (f(a),b)";
by (rtac split 1);
qed "apfst_conv";

val [major,minor] = goal Univ.thy
    "[| q = apfst f p;  !!x y. [| p = (x,y);  q = (f(x),y) |] ==> R \
\    |] ==> R";
by (rtac PairE 1);
by (rtac minor 1);
by (assume_tac 1);
by (rtac (major RS trans) 1);
by (etac ssubst 1);
by (rtac apfst_conv 1);
qed "apfst_convE";

(** Push -- an injection, analogous to Cons on lists **)

val [major] = goalw Univ.thy [Push_def] "Push i f =Push j g  ==> i=j";
by (rtac (major RS fun_cong RS box_equals RS Suc_inject) 1);
by (rtac nat_case_0 1);
by (rtac nat_case_0 1);
qed "Push_inject1";

val [major] = goalw Univ.thy [Push_def] "Push i f =Push j g  ==> f=g";
by (rtac (major RS fun_cong RS ext RS box_equals) 1);
by (rtac (nat_case_Suc RS ext) 1);
by (rtac (nat_case_Suc RS ext) 1);
qed "Push_inject2";

val [major,minor] = goal Univ.thy
    "[| Push i f =Push j g;  [| i=j;  f=g |] ==> P \
\    |] ==> P";
by (rtac ((major RS Push_inject2) RS ((major RS Push_inject1) RS minor)) 1);
qed "Push_inject";

val [major] = goalw Univ.thy [Push_def] "Push k f =(%z.0) ==> P";
by (rtac (major RS fun_cong RS box_equals RS Suc_neq_Zero) 1);
by (rtac nat_case_0 1);
by (rtac refl 1);
qed "Push_neq_K0";

(*** Isomorphisms ***)

goal Univ.thy "inj(Rep_Node)";
by (rtac inj_inverseI 1);       (*cannot combine by RS: multiple unifiers*)
by (rtac Rep_Node_inverse 1);
qed "inj_Rep_Node";

goal Univ.thy "inj_onto Abs_Node Node";
by (rtac inj_onto_inverseI 1);
by (etac Abs_Node_inverse 1);
qed "inj_onto_Abs_Node";

val Abs_Node_inject = inj_onto_Abs_Node RS inj_ontoD;


(*** Introduction rules for Node ***)

goalw Univ.thy [Node_def] "(%k. 0,a) : Node";
by (fast_tac set_cs 1);
qed "Node_K0_I";

goalw Univ.thy [Node_def,Push_def]
    "!!p. p: Node ==> apfst (Push i) p : Node";
by (fast_tac (set_cs addSIs [apfst_conv, nat_case_Suc RS trans]) 1);
qed "Node_Push_I";


(*** Distinctness of constructors ***)

(** Scons vs Atom **)

goalw Univ.thy [Atom_def,Scons_def,Push_Node_def] "(M$N) ~= Atom(a)";
by (rtac notI 1);
by (etac (equalityD2 RS subsetD RS UnE) 1);
by (rtac singletonI 1);
by (REPEAT (eresolve_tac [imageE, Abs_Node_inject RS apfst_convE, 
                          Pair_inject, sym RS Push_neq_K0] 1
     ORELSE resolve_tac [Node_K0_I, Rep_Node RS Node_Push_I] 1));
qed "Scons_not_Atom";
bind_thm ("Atom_not_Scons", (Scons_not_Atom RS not_sym));

bind_thm ("Scons_neq_Atom", (Scons_not_Atom RS notE));
val Atom_neq_Scons = sym RS Scons_neq_Atom;

(*** Injectiveness ***)

(** Atomic nodes **)

goalw Univ.thy [Atom_def] "inj(Atom)";
by (rtac injI 1);
by (etac (singleton_inject RS Abs_Node_inject RS Pair_inject) 1);
by (REPEAT (ares_tac [Node_K0_I] 1));
qed "inj_Atom";
val Atom_inject = inj_Atom RS injD;

goalw Univ.thy [Leaf_def,o_def] "inj(Leaf)";
by (rtac injI 1);
by (etac (Atom_inject RS Inl_inject) 1);
qed "inj_Leaf";

val Leaf_inject = inj_Leaf RS injD;

goalw Univ.thy [Numb_def,o_def] "inj(Numb)";
by (rtac injI 1);
by (etac (Atom_inject RS Inr_inject) 1);
qed "inj_Numb";

val Numb_inject = inj_Numb RS injD;

(** Injectiveness of Push_Node **)

val [major,minor] = goalw Univ.thy [Push_Node_def]
    "[| Push_Node i m =Push_Node j n;  [| i=j;  m=n |] ==> P \
\    |] ==> P";
by (rtac (major RS Abs_Node_inject RS apfst_convE) 1);
by (REPEAT (resolve_tac [Rep_Node RS Node_Push_I] 1));
by (etac (sym RS apfst_convE) 1);
by (rtac minor 1);
by (etac Pair_inject 1);
by (etac (Push_inject1 RS sym) 1);
by (rtac (inj_Rep_Node RS injD) 1);
by (etac trans 1);
by (safe_tac (HOL_cs addSEs [Pair_inject,Push_inject,sym]));
qed "Push_Node_inject";


(** Injectiveness of Scons **)

val [major] = goalw Univ.thy [Scons_def] "M$N <= M'$N' ==> M<=M'";
by (cut_facts_tac [major] 1);
by (fast_tac (set_cs addSDs [Suc_inject]
                     addSEs [Push_Node_inject, Zero_neq_Suc]) 1);
qed "Scons_inject_lemma1";

val [major] = goalw Univ.thy [Scons_def] "M$N <= M'$N' ==> N<=N'";
by (cut_facts_tac [major] 1);
by (fast_tac (set_cs addSDs [Suc_inject]
                     addSEs [Push_Node_inject, Suc_neq_Zero]) 1);
qed "Scons_inject_lemma2";

val [major] = goal Univ.thy "M$N = M'$N' ==> M=M'";
by (rtac (major RS equalityE) 1);
by (REPEAT (ares_tac [equalityI, Scons_inject_lemma1] 1));
qed "Scons_inject1";

val [major] = goal Univ.thy "M$N = M'$N' ==> N=N'";
by (rtac (major RS equalityE) 1);
by (REPEAT (ares_tac [equalityI, Scons_inject_lemma2] 1));
qed "Scons_inject2";

val [major,minor] = goal Univ.thy
    "[| M$N = M'$N';  [| M=M';  N=N' |] ==> P \
\    |] ==> P";
by (rtac ((major RS Scons_inject2) RS ((major RS Scons_inject1) RS minor)) 1);
qed "Scons_inject";

(*rewrite rules*)
goal Univ.thy "(Atom(a)=Atom(b)) = (a=b)";
by (fast_tac (HOL_cs addSEs [Atom_inject]) 1);
qed "Atom_Atom_eq";

goal Univ.thy "(M$N = M'$N') = (M=M' & N=N')";
by (fast_tac (HOL_cs addSEs [Scons_inject]) 1);
qed "Scons_Scons_eq";

(*** Distinctness involving Leaf and Numb ***)

(** Scons vs Leaf **)

goalw Univ.thy [Leaf_def,o_def] "(M$N) ~= Leaf(a)";
by (rtac Scons_not_Atom 1);
qed "Scons_not_Leaf";
bind_thm ("Leaf_not_Scons", (Scons_not_Leaf RS not_sym));

bind_thm ("Scons_neq_Leaf", (Scons_not_Leaf RS notE));
val Leaf_neq_Scons = sym RS Scons_neq_Leaf;

(** Scons vs Numb **)

goalw Univ.thy [Numb_def,o_def] "(M$N) ~= Numb(k)";
by (rtac Scons_not_Atom 1);
qed "Scons_not_Numb";
bind_thm ("Numb_not_Scons", (Scons_not_Numb RS not_sym));

bind_thm ("Scons_neq_Numb", (Scons_not_Numb RS notE));
val Numb_neq_Scons = sym RS Scons_neq_Numb;

(** Leaf vs Numb **)

goalw Univ.thy [Leaf_def,Numb_def] "Leaf(a) ~= Numb(k)";
by (simp_tac (!simpset addsimps [Atom_Atom_eq,Inl_not_Inr]) 1);
qed "Leaf_not_Numb";
bind_thm ("Numb_not_Leaf", (Leaf_not_Numb RS not_sym));

bind_thm ("Leaf_neq_Numb", (Leaf_not_Numb RS notE));
val Numb_neq_Leaf = sym RS Leaf_neq_Numb;


(*** ndepth -- the depth of a node ***)

Addsimps [apfst_conv,Scons_not_Atom,Atom_not_Scons,Scons_Scons_eq];


goalw Univ.thy [ndepth_def] "ndepth (Abs_Node((%k.0, x))) = 0";
by (sstac [Node_K0_I RS Abs_Node_inverse, split] 1);
by (rtac Least_equality 1);
by (rtac refl 1);
by (etac less_zeroE 1);
qed "ndepth_K0";

goal Univ.thy "k < Suc(LEAST x. f(x)=0) --> nat_case (Suc i) f k ~= 0";
by (nat_ind_tac "k" 1);
by (ALLGOALS Simp_tac);
by (rtac impI 1);
by (etac not_less_Least 1);
qed "ndepth_Push_lemma";

goalw Univ.thy [ndepth_def,Push_Node_def]
    "ndepth (Push_Node i n) = Suc(ndepth(n))";
by (stac (Rep_Node RS Node_Push_I RS Abs_Node_inverse) 1);
by (cut_facts_tac [rewrite_rule [Node_def] Rep_Node] 1);
by (safe_tac set_cs);
by (etac ssubst 1);  (*instantiates type variables!*)
by (Simp_tac 1);
by (rtac Least_equality 1);
by (rewtac Push_def);
by (rtac (nat_case_Suc RS trans) 1);
by (etac LeastI 1);
by (etac (ndepth_Push_lemma RS mp) 1);
qed "ndepth_Push_Node";


(*** ntrunc applied to the various node sets ***)

goalw Univ.thy [ntrunc_def] "ntrunc 0 M = {}";
by (safe_tac (set_cs addSIs [equalityI] addSEs [less_zeroE]));
qed "ntrunc_0";

goalw Univ.thy [Atom_def,ntrunc_def] "ntrunc (Suc k) (Atom a) = Atom(a)";
by (safe_tac (set_cs addSIs [equalityI]));
by (stac ndepth_K0 1);
by (rtac zero_less_Suc 1);
qed "ntrunc_Atom";

goalw Univ.thy [Leaf_def,o_def] "ntrunc (Suc k) (Leaf a) = Leaf(a)";
by (rtac ntrunc_Atom 1);
qed "ntrunc_Leaf";

goalw Univ.thy [Numb_def,o_def] "ntrunc (Suc k) (Numb i) = Numb(i)";
by (rtac ntrunc_Atom 1);
qed "ntrunc_Numb";

goalw Univ.thy [Scons_def,ntrunc_def]
    "ntrunc (Suc k) (M$N) = ntrunc k M $ ntrunc k N";
by (safe_tac (set_cs addSIs [equalityI,imageI]));
by (REPEAT (stac ndepth_Push_Node 3 THEN etac Suc_mono 3));
by (REPEAT (rtac Suc_less_SucD 1 THEN 
            rtac (ndepth_Push_Node RS subst) 1 THEN 
            assume_tac 1));
qed "ntrunc_Scons";

(** Injection nodes **)

goalw Univ.thy [In0_def] "ntrunc (Suc 0) (In0 M) = {}";
by (simp_tac (!simpset addsimps [ntrunc_Scons,ntrunc_0]) 1);
by (rewtac Scons_def);
by (safe_tac (set_cs addSIs [equalityI]));
qed "ntrunc_one_In0";

goalw Univ.thy [In0_def]
    "ntrunc (Suc (Suc k)) (In0 M) = In0 (ntrunc (Suc k) M)";
by (simp_tac (!simpset addsimps [ntrunc_Scons,ntrunc_Numb]) 1);
qed "ntrunc_In0";

goalw Univ.thy [In1_def] "ntrunc (Suc 0) (In1 M) = {}";
by (simp_tac (!simpset addsimps [ntrunc_Scons,ntrunc_0]) 1);
by (rewtac Scons_def);
by (safe_tac (set_cs addSIs [equalityI]));
qed "ntrunc_one_In1";

goalw Univ.thy [In1_def]
    "ntrunc (Suc (Suc k)) (In1 M) = In1 (ntrunc (Suc k) M)";
by (simp_tac (!simpset addsimps [ntrunc_Scons,ntrunc_Numb]) 1);
qed "ntrunc_In1";


(*** Cartesian Product ***)

goalw Univ.thy [uprod_def] "!!M N. [| M:A;  N:B |] ==> (M$N) : A<*>B";
by (REPEAT (ares_tac [singletonI,UN_I] 1));
qed "uprodI";

(*The general elimination rule*)
val major::prems = goalw Univ.thy [uprod_def]
    "[| c : A<*>B;  \
\       !!x y. [| x:A;  y:B;  c=x$y |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac [asm_rl,singletonE,UN_E] 1
     ORELSE resolve_tac prems 1));
qed "uprodE";

(*Elimination of a pair -- introduces no eigenvariables*)
val prems = goal Univ.thy
    "[| (M$N) : A<*>B;      [| M:A;  N:B |] ==> P   \
\    |] ==> P";
by (rtac uprodE 1);
by (REPEAT (ares_tac prems 1 ORELSE eresolve_tac [Scons_inject,ssubst] 1));
qed "uprodE2";


(*** Disjoint Sum ***)

goalw Univ.thy [usum_def] "!!M. M:A ==> In0(M) : A<+>B";
by (fast_tac set_cs 1);
qed "usum_In0I";

goalw Univ.thy [usum_def] "!!N. N:B ==> In1(N) : A<+>B";
by (fast_tac set_cs 1);
qed "usum_In1I";

val major::prems = goalw Univ.thy [usum_def]
    "[| u : A<+>B;  \
\       !!x. [| x:A;  u=In0(x) |] ==> P; \
\       !!y. [| y:B;  u=In1(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1 
     ORELSE eresolve_tac (prems@[imageE,ssubst]) 1));
qed "usumE";


(** Injection **)

goalw Univ.thy [In0_def,In1_def] "In0(M) ~= In1(N)";
by (rtac notI 1);
by (etac (Scons_inject1 RS Numb_inject RS Zero_neq_Suc) 1);
qed "In0_not_In1";

bind_thm ("In1_not_In0", (In0_not_In1 RS not_sym));
bind_thm ("In0_neq_In1", (In0_not_In1 RS notE));
val In1_neq_In0 = sym RS In0_neq_In1;

val [major] = goalw Univ.thy [In0_def] "In0(M) = In0(N) ==>  M=N";
by (rtac (major RS Scons_inject2) 1);
qed "In0_inject";

val [major] = goalw Univ.thy [In1_def] "In1(M) = In1(N) ==>  M=N";
by (rtac (major RS Scons_inject2) 1);
qed "In1_inject";


(*** proving equality of sets and functions using ntrunc ***)

goalw Univ.thy [ntrunc_def] "ntrunc k M <= M";
by (fast_tac set_cs 1);
qed "ntrunc_subsetI";

val [major] = goalw Univ.thy [ntrunc_def]
    "(!!k. ntrunc k M <= N) ==> M<=N";
by (fast_tac (set_cs addIs [less_add_Suc1, less_add_Suc2, 
                            major RS subsetD]) 1);
qed "ntrunc_subsetD";

(*A generalized form of the take-lemma*)
val [major] = goal Univ.thy "(!!k. ntrunc k M = ntrunc k N) ==> M=N";
by (rtac equalityI 1);
by (ALLGOALS (rtac ntrunc_subsetD));
by (ALLGOALS (rtac (ntrunc_subsetI RSN (2, subset_trans))));
by (rtac (major RS equalityD1) 1);
by (rtac (major RS equalityD2) 1);
qed "ntrunc_equality";

val [major] = goalw Univ.thy [o_def]
    "[| !!k. (ntrunc(k) o h1) = (ntrunc(k) o h2) |] ==> h1=h2";
by (rtac (ntrunc_equality RS ext) 1);
by (rtac (major RS fun_cong) 1);
qed "ntrunc_o_equality";

(*** Monotonicity ***)

goalw Univ.thy [uprod_def] "!!A B. [| A<=A';  B<=B' |] ==> A<*>B <= A'<*>B'";
by (fast_tac set_cs 1);
qed "uprod_mono";

goalw Univ.thy [usum_def] "!!A B. [| A<=A';  B<=B' |] ==> A<+>B <= A'<+>B'";
by (fast_tac set_cs 1);
qed "usum_mono";

goalw Univ.thy [Scons_def] "!!M N. [| M<=M';  N<=N' |] ==> M$N <= M'$N'";
by (fast_tac set_cs 1);
qed "Scons_mono";

goalw Univ.thy [In0_def] "!!M N. M<=N ==> In0(M) <= In0(N)";
by (REPEAT (ares_tac [subset_refl,Scons_mono] 1));
qed "In0_mono";

goalw Univ.thy [In1_def] "!!M N. M<=N ==> In1(M) <= In1(N)";
by (REPEAT (ares_tac [subset_refl,Scons_mono] 1));
qed "In1_mono";


(*** Split and Case ***)

goalw Univ.thy [Split_def] "Split c (M$N) = c M N";
by (fast_tac (set_cs addIs [select_equality] addEs [Scons_inject]) 1);
qed "Split";

goalw Univ.thy [Case_def] "Case c d (In0 M) = c(M)";
by (fast_tac (set_cs addIs [select_equality] 
                     addEs [make_elim In0_inject, In0_neq_In1]) 1);
qed "Case_In0";

goalw Univ.thy [Case_def] "Case c d (In1 N) = d(N)";
by (fast_tac (set_cs addIs [select_equality] 
                     addEs [make_elim In1_inject, In1_neq_In0]) 1);
qed "Case_In1";

(**** UN x. B(x) rules ****)

goalw Univ.thy [ntrunc_def] "ntrunc k (UN x.f(x)) = (UN x. ntrunc k (f x))";
by (fast_tac (set_cs addIs [equalityI]) 1);
qed "ntrunc_UN1";

goalw Univ.thy [Scons_def] "(UN x.f(x)) $ M = (UN x. f(x) $ M)";
by (fast_tac (set_cs addIs [equalityI]) 1);
qed "Scons_UN1_x";

goalw Univ.thy [Scons_def] "M $ (UN x.f(x)) = (UN x. M $ f(x))";
by (fast_tac (set_cs addIs [equalityI]) 1);
qed "Scons_UN1_y";

goalw Univ.thy [In0_def] "In0(UN x.f(x)) = (UN x. In0(f(x)))";
by (rtac Scons_UN1_y 1);
qed "In0_UN1";

goalw Univ.thy [In1_def] "In1(UN x.f(x)) = (UN x. In1(f(x)))";
by (rtac Scons_UN1_y 1);
qed "In1_UN1";


(*** Equality : the diagonal relation ***)

goalw Univ.thy [diag_def] "!!a A. [| a=b;  a:A |] ==> (a,b) : diag(A)";
by (fast_tac set_cs 1);
qed "diag_eqI";

val diagI = refl RS diag_eqI |> standard;

(*The general elimination rule*)
val major::prems = goalw Univ.thy [diag_def]
    "[| c : diag(A);  \
\       !!x y. [| x:A;  c = (x,x) |] ==> P \
\    |] ==> P";
by (rtac (major RS UN_E) 1);
by (REPEAT (eresolve_tac [asm_rl,singletonE] 1 ORELSE resolve_tac prems 1));
qed "diagE";

(*** Equality for Cartesian Product ***)

goalw Univ.thy [dprod_def]
    "!!r s. [| (M,M'):r;  (N,N'):s |] ==> (M$N, M'$N') : r<**>s";
by (fast_tac prod_cs 1);
qed "dprodI";

(*The general elimination rule*)
val major::prems = goalw Univ.thy [dprod_def]
    "[| c : r<**>s;  \
\       !!x y x' y'. [| (x,x') : r;  (y,y') : s;  c = (x$y,x'$y') |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT_FIRST (eresolve_tac [asm_rl, UN_E, mem_splitE, singletonE]));
by (REPEAT (ares_tac prems 1 ORELSE hyp_subst_tac 1));
qed "dprodE";


(*** Equality for Disjoint Sum ***)

goalw Univ.thy [dsum_def]  "!!r. (M,M'):r ==> (In0(M), In0(M')) : r<++>s";
by (fast_tac prod_cs 1);
qed "dsum_In0I";

goalw Univ.thy [dsum_def]  "!!r. (N,N'):s ==> (In1(N), In1(N')) : r<++>s";
by (fast_tac prod_cs 1);
qed "dsum_In1I";

val major::prems = goalw Univ.thy [dsum_def]
    "[| w : r<++>s;  \
\       !!x x'. [| (x,x') : r;  w = (In0(x), In0(x')) |] ==> P; \
\       !!y y'. [| (y,y') : s;  w = (In1(y), In1(y')) |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT_FIRST (eresolve_tac [asm_rl, UN_E, UnE, mem_splitE, singletonE]));
by (DEPTH_SOLVE (ares_tac prems 1 ORELSE hyp_subst_tac 1));
qed "dsumE";


val univ_cs =
    prod_cs addSIs [diagI, uprodI, dprodI]
            addIs  [usum_In0I, usum_In1I, dsum_In0I, dsum_In1I]
            addSEs [diagE, uprodE, dprodE, usumE, dsumE];


(*** Monotonicity ***)

goal Univ.thy "!!r s. [| r<=r';  s<=s' |] ==> r<**>s <= r'<**>s'";
by (fast_tac univ_cs 1);
qed "dprod_mono";

goal Univ.thy "!!r s. [| r<=r';  s<=s' |] ==> r<++>s <= r'<++>s'";
by (fast_tac univ_cs 1);
qed "dsum_mono";


(*** Bounding theorems ***)

goal Univ.thy "diag(A) <= Sigma A (%x.A)";
by (fast_tac univ_cs 1);
qed "diag_subset_Sigma";

goal Univ.thy "(Sigma A (%x.B) <**> Sigma C (%x.D)) <= Sigma (A<*>C) (%z. B<*>D)";
by (fast_tac univ_cs 1);
qed "dprod_Sigma";

val dprod_subset_Sigma = [dprod_mono, dprod_Sigma] MRS subset_trans |>standard;

(*Dependent version*)
goal Univ.thy
    "(Sigma A B <**> Sigma C D) <= Sigma (A<*>C) (Split(%x y. B(x)<*>D(y)))";
by (safe_tac univ_cs);
by (stac Split 1);
by (fast_tac univ_cs 1);
qed "dprod_subset_Sigma2";

goal Univ.thy "(Sigma A (%x.B) <++> Sigma C (%x.D)) <= Sigma (A<+>C) (%z. B<+>D)";
by (fast_tac univ_cs 1);
qed "dsum_Sigma";

val dsum_subset_Sigma = [dsum_mono, dsum_Sigma] MRS subset_trans |> standard;


(*** Domain ***)

goal Univ.thy "fst `` diag(A) = A";
by (fast_tac (prod_cs addIs [equalityI, diagI] addSEs [diagE]) 1);
qed "fst_image_diag";

goal Univ.thy "fst `` (r<**>s) = (fst``r) <*> (fst``s)";
by (fast_tac (prod_cs addIs [equalityI, uprodI, dprodI]
                     addSEs [uprodE, dprodE]) 1);
qed "fst_image_dprod";

goal Univ.thy "fst `` (r<++>s) = (fst``r) <+> (fst``s)";
by (fast_tac (prod_cs addIs [equalityI, usum_In0I, usum_In1I, 
                             dsum_In0I, dsum_In1I]
                     addSEs [usumE, dsumE]) 1);
qed "fst_image_dsum";

Addsimps [fst_image_diag, fst_image_dprod, fst_image_dsum];
