(*  Title:      HOL/Datatype_Universe.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

(** apfst -- can be used in similar type definitions **)

Goalw [apfst_def] "apfst f (a,b) = (f(a),b)";
by (rtac split_conv 1);
qed "apfst_conv";

val [major,minor] = Goal
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

Goalw [Push_def] "Push i f = Push j g  ==> i=j";
by (etac (fun_cong RS box_equals) 1);
by (rtac nat_case_0 1);
by (rtac nat_case_0 1);
qed "Push_inject1";

Goalw [Push_def] "Push i f = Push j g  ==> f=g";
by (rtac (ext RS box_equals) 1);
by (etac fun_cong 1);
by (rtac (nat_case_Suc RS ext) 1);
by (rtac (nat_case_Suc RS ext) 1);
qed "Push_inject2";

val [major,minor] = Goal
    "[| Push i f =Push j g;  [| i=j;  f=g |] ==> P \
\    |] ==> P";
by (rtac ((major RS Push_inject2) RS ((major RS Push_inject1) RS minor)) 1);
qed "Push_inject";

Goalw [Push_def] "Push (Inr (Suc k)) f = (%z. Inr 0) ==> P";
by (rtac Suc_neq_Zero 1);
by (etac (fun_cong RS box_equals RS Inr_inject) 1);
by (rtac nat_case_0 1);
by (rtac refl 1);
qed "Push_neq_K0";

(*** Isomorphisms ***)

Goal "inj(Rep_Node)";
by (rtac inj_inverseI 1);       (*cannot combine by RS: multiple unifiers*)
by (rtac Rep_Node_inverse 1);
qed "inj_Rep_Node";

Goal "inj_on Abs_Node Node";
by (rtac inj_on_inverseI 1);
by (etac Abs_Node_inverse 1);
qed "inj_on_Abs_Node";

bind_thm ("Abs_Node_inj", inj_on_Abs_Node RS inj_onD);


(*** Introduction rules for Node ***)

Goalw [Node_def] "(%k. Inr 0, a) : Node";
by (Blast_tac 1);
qed "Node_K0_I";

Goalw [Node_def,Push_def]
    "p: Node ==> apfst (Push i) p : Node";
by (fast_tac (claset() addSIs [apfst_conv, nat_case_Suc RS trans]) 1);
qed "Node_Push_I";


(*** Distinctness of constructors ***)

(** Scons vs Atom **)

Goalw [Atom_def,Scons_def,Push_Node_def,One_def]
 "Scons M N ~= Atom(a)";
by (rtac notI 1);
by (etac (equalityD2 RS subsetD RS UnE) 1);
by (rtac singletonI 1);
by (REPEAT (eresolve_tac [imageE, Abs_Node_inj RS apfst_convE, 
                          Pair_inject, sym RS Push_neq_K0] 1
     ORELSE resolve_tac [Node_K0_I, Rep_Node RS Node_Push_I] 1));
qed "Scons_not_Atom";
bind_thm ("Atom_not_Scons", Scons_not_Atom RS not_sym);


(*** Injectiveness ***)

(** Atomic nodes **)

Goalw [Atom_def] "inj(Atom)";
by (blast_tac (claset() addSIs [injI, Node_K0_I] addSDs [Abs_Node_inj]) 1);
qed "inj_Atom";
bind_thm ("Atom_inject", inj_Atom RS injD);

Goal "(Atom(a)=Atom(b)) = (a=b)";
by (blast_tac (claset() addSDs [Atom_inject]) 1);
qed "Atom_Atom_eq";
AddIffs [Atom_Atom_eq];

Goalw [Leaf_def,o_def] "inj(Leaf)";
by (rtac injI 1);
by (etac (Atom_inject RS Inl_inject) 1);
qed "inj_Leaf";

bind_thm ("Leaf_inject", inj_Leaf RS injD);
AddSDs [Leaf_inject];

Goalw [Numb_def,o_def] "inj(Numb)";
by (rtac injI 1);
by (etac (Atom_inject RS Inr_inject) 1);
qed "inj_Numb";

bind_thm ("Numb_inject", inj_Numb RS injD);
AddSDs [Numb_inject];

(** Injectiveness of Push_Node **)

val [major,minor] = Goalw [Push_Node_def]
    "[| Push_Node i m =Push_Node j n;  [| i=j;  m=n |] ==> P \
\    |] ==> P";
by (rtac (major RS Abs_Node_inj RS apfst_convE) 1);
by (REPEAT (resolve_tac [Rep_Node RS Node_Push_I] 1));
by (etac (sym RS apfst_convE) 1);
by (rtac minor 1);
by (etac Pair_inject 1);
by (etac (Push_inject1 RS sym) 1);
by (rtac (inj_Rep_Node RS injD) 1);
by (etac trans 1);
by (safe_tac (claset() addSEs [Push_inject,sym]));
qed "Push_Node_inject";


(** Injectiveness of Scons **)

Goalw [Scons_def,One_def] "Scons M N <= Scons M' N' ==> M<=M'";
by (blast_tac (claset() addSDs [Push_Node_inject]) 1);
qed "Scons_inject_lemma1";

Goalw [Scons_def,One_def] "Scons M N <= Scons M' N' ==> N<=N'";
by (blast_tac (claset() addSDs [Push_Node_inject]) 1);
qed "Scons_inject_lemma2";

Goal "Scons M N = Scons M' N' ==> M=M'";
by (etac equalityE 1);
by (REPEAT (ares_tac [equalityI, Scons_inject_lemma1] 1));
qed "Scons_inject1";

Goal "Scons M N = Scons M' N' ==> N=N'";
by (etac equalityE 1);
by (REPEAT (ares_tac [equalityI, Scons_inject_lemma2] 1));
qed "Scons_inject2";

val [major,minor] = Goal
    "[| Scons M N = Scons M' N';  [| M=M';  N=N' |] ==> P \
\    |] ==> P";
by (rtac ((major RS Scons_inject2) RS ((major RS Scons_inject1) RS minor)) 1);
qed "Scons_inject";

Goal "(Scons M N = Scons M' N') = (M=M' & N=N')";
by (blast_tac (claset() addSEs [Scons_inject]) 1);
qed "Scons_Scons_eq";

(*** Distinctness involving Leaf and Numb ***)

(** Scons vs Leaf **)

Goalw [Leaf_def,o_def] "Scons M N ~= Leaf(a)";
by (rtac Scons_not_Atom 1);
qed "Scons_not_Leaf";
bind_thm ("Leaf_not_Scons", Scons_not_Leaf RS not_sym);

AddIffs [Scons_not_Leaf, Leaf_not_Scons];


(** Scons vs Numb **)

Goalw [Numb_def,o_def] "Scons M N ~= Numb(k)";
by (rtac Scons_not_Atom 1);
qed "Scons_not_Numb";
bind_thm ("Numb_not_Scons", Scons_not_Numb RS not_sym);

AddIffs [Scons_not_Numb, Numb_not_Scons];


(** Leaf vs Numb **)

Goalw [Leaf_def,Numb_def] "Leaf(a) ~= Numb(k)";
by (simp_tac (simpset() addsimps [Inl_not_Inr]) 1);
qed "Leaf_not_Numb";
bind_thm ("Numb_not_Leaf", Leaf_not_Numb RS not_sym);

AddIffs [Leaf_not_Numb, Numb_not_Leaf];


(*** ndepth -- the depth of a node ***)

Addsimps [apfst_conv];
AddIffs  [Scons_not_Atom, Atom_not_Scons, Scons_Scons_eq];


Goalw [ndepth_def] "ndepth (Abs_Node(%k. Inr 0, x)) = 0";
by (EVERY1[stac (Node_K0_I RS Abs_Node_inverse), stac split_conv]);
by (rtac Least_equality 1);
by Auto_tac;  
qed "ndepth_K0";

Goal "nat_case (Inr (Suc i)) f k = Inr 0 --> Suc(LEAST x. f x = Inr 0) <= k";
by (induct_tac "k" 1);
by (ALLGOALS Simp_tac);
by (rtac impI 1); 
by (etac Least_le 1);
val lemma = result();

Goalw [ndepth_def,Push_Node_def]
    "ndepth (Push_Node (Inr (Suc i)) n) = Suc(ndepth(n))";
by (stac (Rep_Node RS Node_Push_I RS Abs_Node_inverse) 1);
by (cut_facts_tac [rewrite_rule [Node_def] Rep_Node] 1);
by Safe_tac;
by (etac ssubst 1);  (*instantiates type variables!*)
by (Simp_tac 1);
by (rtac Least_equality 1);
by (rewtac Push_def);
by (auto_tac (claset(), simpset() addsimps [lemma]));  
by (etac LeastI 1);
qed "ndepth_Push_Node";


(*** ntrunc applied to the various node sets ***)

Goalw [ntrunc_def] "ntrunc 0 M = {}";
by (Blast_tac 1);
qed "ntrunc_0";

Goalw [Atom_def,ntrunc_def] "ntrunc (Suc k) (Atom a) = Atom(a)";
by (fast_tac (claset() addss (simpset() addsimps [ndepth_K0])) 1);
qed "ntrunc_Atom";

Goalw [Leaf_def,o_def] "ntrunc (Suc k) (Leaf a) = Leaf(a)";
by (rtac ntrunc_Atom 1);
qed "ntrunc_Leaf";

Goalw [Numb_def,o_def] "ntrunc (Suc k) (Numb i) = Numb(i)";
by (rtac ntrunc_Atom 1);
qed "ntrunc_Numb";

Goalw [Scons_def,ntrunc_def,One_def]
    "ntrunc (Suc k) (Scons M N) = Scons (ntrunc k M) (ntrunc k N)";
by (safe_tac (claset() addSIs [imageI]));
by (REPEAT (stac ndepth_Push_Node 3 THEN etac Suc_mono 3));
by (REPEAT (rtac Suc_less_SucD 1 THEN 
            rtac (ndepth_Push_Node RS subst) 1 THEN 
            assume_tac 1));
qed "ntrunc_Scons";

Addsimps [ntrunc_0, ntrunc_Atom, ntrunc_Leaf, ntrunc_Numb, ntrunc_Scons];


(** Injection nodes **)

Goalw [In0_def] "ntrunc 1' (In0 M) = {}";
by (Simp_tac 1);
by (rewtac Scons_def);
by (Blast_tac 1);
qed "ntrunc_one_In0";

Goalw [In0_def]
    "ntrunc (Suc (Suc k)) (In0 M) = In0 (ntrunc (Suc k) M)";
by (Simp_tac 1);
qed "ntrunc_In0";

Goalw [In1_def] "ntrunc 1' (In1 M) = {}";
by (Simp_tac 1);
by (rewtac Scons_def);
by (Blast_tac 1);
qed "ntrunc_one_In1";

Goalw [In1_def]
    "ntrunc (Suc (Suc k)) (In1 M) = In1 (ntrunc (Suc k) M)";
by (Simp_tac 1);
qed "ntrunc_In1";

Addsimps [ntrunc_one_In0, ntrunc_In0, ntrunc_one_In1, ntrunc_In1];


(*** Cartesian Product ***)

Goalw [uprod_def] "[| M:A;  N:B |] ==> Scons M N : uprod A B";
by (REPEAT (ares_tac [singletonI,UN_I] 1));
qed "uprodI";

(*The general elimination rule*)
val major::prems = Goalw [uprod_def]
    "[| c : uprod A B;  \
\       !!x y. [| x:A;  y:B;  c = Scons x y |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac [asm_rl,singletonE,UN_E] 1
     ORELSE resolve_tac prems 1));
qed "uprodE";

(*Elimination of a pair -- introduces no eigenvariables*)
val prems = Goal
    "[| Scons M N : uprod A B;      [| M:A;  N:B |] ==> P   \
\    |] ==> P";
by (rtac uprodE 1);
by (REPEAT (ares_tac prems 1 ORELSE eresolve_tac [Scons_inject,ssubst] 1));
qed "uprodE2";


(*** Disjoint Sum ***)

Goalw [usum_def] "M:A ==> In0(M) : usum A B";
by (Blast_tac 1);
qed "usum_In0I";

Goalw [usum_def] "N:B ==> In1(N) : usum A B";
by (Blast_tac 1);
qed "usum_In1I";

val major::prems = Goalw [usum_def]
    "[| u : usum A B;  \
\       !!x. [| x:A;  u=In0(x) |] ==> P; \
\       !!y. [| y:B;  u=In1(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1 
     ORELSE eresolve_tac (prems@[imageE,ssubst]) 1));
qed "usumE";


(** Injection **)

Goalw [In0_def,In1_def,One_def] "In0(M) ~= In1(N)";
by (rtac notI 1);
by (etac (Scons_inject1 RS Numb_inject RS Zero_neq_Suc) 1);
qed "In0_not_In1";

bind_thm ("In1_not_In0", In0_not_In1 RS not_sym);

AddIffs [In0_not_In1, In1_not_In0];

Goalw [In0_def] "In0(M) = In0(N) ==>  M=N";
by (etac (Scons_inject2) 1);
qed "In0_inject";

Goalw [In1_def] "In1(M) = In1(N) ==>  M=N";
by (etac (Scons_inject2) 1);
qed "In1_inject";

Goal "(In0 M = In0 N) = (M=N)";
by (blast_tac (claset() addSDs [In0_inject]) 1);
qed "In0_eq";

Goal "(In1 M = In1 N) = (M=N)";
by (blast_tac (claset() addSDs [In1_inject]) 1);
qed "In1_eq";

AddIffs [In0_eq, In1_eq];

Goal "inj In0";
by (blast_tac (claset() addSIs [injI]) 1);
qed "inj_In0";

Goal "inj In1";
by (blast_tac (claset() addSIs [injI]) 1);
qed "inj_In1";


(*** Function spaces ***)

Goalw [Lim_def] "Lim f = Lim g ==> f = g";
by (rtac ext 1);
by (blast_tac (claset() addSEs [Push_Node_inject]) 1);
qed "Lim_inject";

Goalw [Funs_def] "S <= T ==> Funs S <= Funs T";
by (Blast_tac 1);
qed "Funs_mono";

val [prem] = Goalw [Funs_def] "(!!x. f x : S) ==> f : Funs S";
by (blast_tac (claset() addIs [prem]) 1);
qed "FunsI";

Goalw [Funs_def] "f : Funs S ==> f x : S";
by (etac CollectE 1);
by (etac subsetD 1);
by (rtac rangeI 1);
qed "FunsD";

val [p1, p2] = Goalw [o_def]
   "[| f : Funs R; !!x. x : R ==> r (a x) = x |] ==> r o (a o f) = f";
by (rtac (p2 RS ext) 1);
by (rtac (p1 RS FunsD) 1);
qed "Funs_inv";

val [p1, p2] = Goalw [o_def]
     "[| f : Funs (range g); !!h. f = g o h ==> P |] ==> P";
by (res_inst_tac [("h", "%x. @y. (f::'a=>'b) x = g y")] p2 1);
by (rtac ext 1);
by (rtac (p1 RS FunsD RS rangeE) 1);
by (etac (exI RS (some_eq_ex RS iffD2)) 1);
qed "Funs_rangeE";

Goal "a : S ==> (%x. a) : Funs S";
by (rtac FunsI 1);
by (assume_tac 1);
qed "Funs_nonempty";


(*** proving equality of sets and functions using ntrunc ***)

Goalw [ntrunc_def] "ntrunc k M <= M";
by (Blast_tac 1);
qed "ntrunc_subsetI";

val [major] = Goalw [ntrunc_def] "(!!k. ntrunc k M <= N) ==> M<=N";
by (blast_tac (claset() addIs [less_add_Suc1, less_add_Suc2, 
			       major RS subsetD]) 1);
qed "ntrunc_subsetD";

(*A generalized form of the take-lemma*)
val [major] = Goal "(!!k. ntrunc k M = ntrunc k N) ==> M=N";
by (rtac equalityI 1);
by (ALLGOALS (rtac ntrunc_subsetD));
by (ALLGOALS (rtac (ntrunc_subsetI RSN (2, subset_trans))));
by (rtac (major RS equalityD1) 1);
by (rtac (major RS equalityD2) 1);
qed "ntrunc_equality";

val [major] = Goalw [o_def]
    "[| !!k. (ntrunc(k) o h1) = (ntrunc(k) o h2) |] ==> h1=h2";
by (rtac (ntrunc_equality RS ext) 1);
by (rtac (major RS fun_cong) 1);
qed "ntrunc_o_equality";

(*** Monotonicity ***)

Goalw [uprod_def] "[| A<=A';  B<=B' |] ==> uprod A B <= uprod A' B'";
by (Blast_tac 1);
qed "uprod_mono";

Goalw [usum_def] "[| A<=A';  B<=B' |] ==> usum A B <= usum A' B'";
by (Blast_tac 1);
qed "usum_mono";

Goalw [Scons_def] "[| M<=M';  N<=N' |] ==> Scons M N <= Scons M' N'";
by (Blast_tac 1);
qed "Scons_mono";

Goalw [In0_def] "M<=N ==> In0(M) <= In0(N)";
by (REPEAT (ares_tac [subset_refl,Scons_mono] 1));
qed "In0_mono";

Goalw [In1_def] "M<=N ==> In1(M) <= In1(N)";
by (REPEAT (ares_tac [subset_refl,Scons_mono] 1));
qed "In1_mono";


(*** Split and Case ***)

Goalw [Split_def] "Split c (Scons M N) = c M N";
by (Blast_tac  1);
qed "Split";

Goalw [Case_def] "Case c d (In0 M) = c(M)";
by (Blast_tac 1);
qed "Case_In0";

Goalw [Case_def] "Case c d (In1 N) = d(N)";
by (Blast_tac 1);
qed "Case_In1";

Addsimps [Split, Case_In0, Case_In1];


(**** UN x. B(x) rules ****)

Goalw [ntrunc_def] "ntrunc k (UN x. f(x)) = (UN x. ntrunc k (f x))";
by (Blast_tac 1);
qed "ntrunc_UN1";

Goalw [Scons_def] "Scons (UN x. f x) M = (UN x. Scons (f x) M)";
by (Blast_tac 1);
qed "Scons_UN1_x";

Goalw [Scons_def] "Scons M (UN x. f x) = (UN x. Scons M (f x))";
by (Blast_tac 1);
qed "Scons_UN1_y";

Goalw [In0_def] "In0(UN x. f(x)) = (UN x. In0(f(x)))";
by (rtac Scons_UN1_y 1);
qed "In0_UN1";

Goalw [In1_def] "In1(UN x. f(x)) = (UN x. In1(f(x)))";
by (rtac Scons_UN1_y 1);
qed "In1_UN1";


(*** Equality for Cartesian Product ***)

Goalw [dprod_def]
    "[| (M,M'):r;  (N,N'):s |] ==> (Scons M N, Scons M' N') : dprod r s";
by (Blast_tac 1);
qed "dprodI";

(*The general elimination rule*)
val major::prems = Goalw [dprod_def]
    "[| c : dprod r s;  \
\       !!x y x' y'. [| (x,x') : r;  (y,y') : s;  c = (Scons x y, Scons x' y') |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT_FIRST (eresolve_tac [asm_rl, UN_E, mem_splitE, singletonE]));
by (REPEAT (ares_tac prems 1 ORELSE hyp_subst_tac 1));
qed "dprodE";


(*** Equality for Disjoint Sum ***)

Goalw [dsum_def]  "(M,M'):r ==> (In0(M), In0(M')) : dsum r s";
by (Blast_tac 1);
qed "dsum_In0I";

Goalw [dsum_def]  "(N,N'):s ==> (In1(N), In1(N')) : dsum r s";
by (Blast_tac 1);
qed "dsum_In1I";

val major::prems = Goalw [dsum_def]
    "[| w : dsum r s;  \
\       !!x x'. [| (x,x') : r;  w = (In0(x), In0(x')) |] ==> P; \
\       !!y y'. [| (y,y') : s;  w = (In1(y), In1(y')) |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT_FIRST (eresolve_tac [asm_rl, UN_E, UnE, mem_splitE, singletonE]));
by (DEPTH_SOLVE (ares_tac prems 1 ORELSE hyp_subst_tac 1));
qed "dsumE";

AddSIs [uprodI, dprodI];
AddIs  [usum_In0I, usum_In1I, dsum_In0I, dsum_In1I];
AddSEs [uprodE, dprodE, usumE, dsumE];


(*** Monotonicity ***)

Goal "[| r<=r';  s<=s' |] ==> dprod r s <= dprod r' s'";
by (Blast_tac 1);
qed "dprod_mono";

Goal "[| r<=r';  s<=s' |] ==> dsum r s <= dsum r' s'";
by (Blast_tac 1);
qed "dsum_mono";


(*** Bounding theorems ***)

Goal "(dprod (A <*> B) (C <*> D)) <= (uprod A C) <*> (uprod B D)";
by (Blast_tac 1);
qed "dprod_Sigma";

bind_thm ("dprod_subset_Sigma", [dprod_mono, dprod_Sigma] MRS subset_trans |> standard);

(*Dependent version*)
Goal "(dprod (Sigma A B) (Sigma C D)) <= Sigma (uprod A C) (Split (%x y. uprod (B x) (D y)))";
by Safe_tac;
by (stac Split 1);
by (Blast_tac 1);
qed "dprod_subset_Sigma2";

Goal "(dsum (A <*> B) (C <*> D)) <= (usum A C) <*> (usum B D)";
by (Blast_tac 1);
qed "dsum_Sigma";

bind_thm ("dsum_subset_Sigma", [dsum_mono, dsum_Sigma] MRS subset_trans |> standard);


(*** Domain ***)

Goal "Domain (dprod r s) = uprod (Domain r) (Domain s)";
by Auto_tac;
qed "Domain_dprod";

Goal "Domain (dsum r s) = usum (Domain r) (Domain s)";
by Auto_tac;
qed "Domain_dsum";

Addsimps [Domain_dprod, Domain_dsum];
