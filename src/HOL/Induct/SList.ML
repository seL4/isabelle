(*  Title: 	HOL/ex/SList.ML
    ID:         SList.ML,v 1.2 1994/12/14 10:17:48 clasohm Exp
    Author: 	B. Wolff,  based on a version of Lawrence C Paulson, 
		Cambridge University Computer Laboratory

Definition of type 'a list by a least fixed point
*)

Goalw [List_def] "x : list (range Leaf) ==> x : List";
by (Asm_simp_tac 1);
qed "ListI";

Goalw [List_def] "x : List ==> x : list (range Leaf)";
by (Asm_simp_tac 1);
qed "ListD";

val list_con_defs = [NIL_def, CONS_def];

Goal "list(A) = usum {Numb(0)} (uprod A (list(A)))";
let val rew = rewrite_rule list_con_defs in  
by (fast_tac ((claset()) addSIs (equalityI :: map rew list.intrs)
                      addEs [rew list.elim]) 1)
end;
qed "list_unfold";

(*This justifies using list in other recursive type definitions*)
Goalw list.defs "!!A B. A<=B ==> list(A) <= list(B)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "list_mono";

(*Type checking -- list creates well-founded sets*)
Goalw (list_con_defs @ list.defs) "list(sexp) <= sexp";
by (rtac lfp_lowerbound 1);
by (fast_tac (claset() addIs sexp.intrs@[sexp_In0I,sexp_In1I]) 1);
qed "list_sexp";

(* A <= sexp ==> list(A) <= sexp *)
bind_thm ("list_subset_sexp", [list_mono, list_sexp] MRS subset_trans);

fun List_simp thm = (asm_full_simplify (HOL_ss addsimps [List_def]) thm)

(*Induction for the type 'a list *)
val prems = Goalw [Nil_def, Cons_def]
    "[| P(Nil);   \
\       !!x xs. P(xs) ==> P(x # xs) |]  ==> P(l)";
by (rtac (Rep_List_inverse RS subst) 1);  
			 (*types force good instantiation*)
by (rtac ((List_simp Rep_List)  RS list.induct) 1);
by (REPEAT (ares_tac prems 1
            ORELSE eresolve_tac [rangeE, ssubst, 
                          (List_simp Abs_List_inverse) RS subst] 1));
qed "list_induct";


(*** Isomorphisms ***)

Goal "inj_on Abs_List (list(range Leaf))";
by (rtac inj_on_inverseI 1);
by (etac (List_simp Abs_List_inverse) 1);
qed "inj_on_Abs_list";

(** Distinctness of constructors **)

Goalw list_con_defs "CONS M N ~= NIL";
by (rtac In1_not_In0 1);
qed "CONS_not_NIL";
val NIL_not_CONS = CONS_not_NIL RS not_sym;

bind_thm ("CONS_neq_NIL", (CONS_not_NIL RS notE));
val NIL_neq_CONS = sym RS CONS_neq_NIL;

Goalw [Nil_def,Cons_def] "x # xs ~= Nil";
by (rtac (CONS_not_NIL RS (inj_on_Abs_list RS inj_on_contraD)) 1);
by (REPEAT (resolve_tac (list.intrs @ [rangeI,(List_simp Rep_List)])1));
qed "Cons_not_Nil";

bind_thm ("Nil_not_Cons", (Cons_not_Nil RS not_sym));

bind_thm ("Cons_neq_Nil", (Cons_not_Nil RS notE));
val Nil_neq_Cons = sym RS Cons_neq_Nil;

(** Injectiveness of CONS and Cons **)

Goalw [CONS_def] "(CONS K M)=(CONS L N) = (K=L & M=N)";
by (fast_tac (HOL_cs addSEs [Scons_inject, make_elim In1_inject]) 1);
qed "CONS_CONS_eq";

(*For reasoning about abstract list constructors*)
AddIs [Rep_List RS ListD, ListI];
AddIs list.intrs;

AddIffs [CONS_not_NIL, NIL_not_CONS, CONS_CONS_eq];

AddSDs [Leaf_inject];

Goalw [Cons_def] "(x#xs=y#ys) = (x=y & xs=ys)";
by (stac (thm "Abs_List_inject") 1);
by (auto_tac (claset(), simpset() addsimps [thm "Rep_List_inject"])); 
qed "Cons_Cons_eq";
bind_thm ("Cons_inject2", Cons_Cons_eq RS iffD1 RS conjE);

Goal "CONS M N: list(A) ==> M: A & N: list(A)";
by (etac setup_induction 1);
by (etac list.induct 1);
by (ALLGOALS Fast_tac);
qed "CONS_D";

Goalw [CONS_def,In1_def] "CONS M N: sexp ==> M: sexp & N: sexp";
by (fast_tac (claset() addSDs [Scons_D]) 1);
qed "sexp_CONS_D";


(*Reasoning about constructors and their freeness*)
Addsimps list.intrs;

AddIffs [Cons_not_Nil, Nil_not_Cons, Cons_Cons_eq];

Goal "N: list(A) ==> !M. N ~= CONS M N";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "not_CONS_self";

Goal "ALL x. l ~= x#l";
by (induct_thm_tac list_induct "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "not_Cons_self2";


Goal "(xs ~= []) = (? y ys. xs = y#ys)";
by (induct_thm_tac list_induct "xs" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
by (REPEAT(resolve_tac [exI,refl,conjI] 1));
qed "neq_Nil_conv2";

(** Conversion rules for List_case: case analysis operator **)

Goalw [List_case_def,NIL_def] "List_case c h NIL = c";
by (rtac Case_In0 1);
qed "List_case_NIL";

Goalw [List_case_def,CONS_def]  "List_case c h (CONS M N) = h M N";
by (Simp_tac 1);
qed "List_case_CONS";

Addsimps [List_case_NIL, List_case_CONS];


(*** List_rec -- by wf recursion on pred_sexp ***)

(* The trancl(pred_sexp) is essential because pred_sexp_CONS_I1,2 would not
   hold if pred_sexp^+ were changed to pred_sexp. *)

Goal "(%M. List_rec M c d) = wfrec (trancl pred_sexp) \
                           \     (%g. List_case c (%x y. d x y (g y)))";
by (simp_tac (HOL_ss addsimps [List_rec_def]) 1);
val List_rec_unfold = standard 
  ((wf_pred_sexp RS wf_trancl) RS ((result() RS eq_reflection) RS def_wfrec));


(*---------------------------------------------------------------------------
 * Old:
 * val List_rec_unfold = [List_rec_def,wf_pred_sexp RS wf_trancl] MRS def_wfrec
 *                     |> standard;
 *---------------------------------------------------------------------------*)

(** pred_sexp lemmas **)

Goalw [CONS_def,In1_def]
    "[| M: sexp;  N: sexp |] ==> (M, CONS M N) : pred_sexp^+";
by (Asm_simp_tac 1);
qed "pred_sexp_CONS_I1";

Goalw [CONS_def,In1_def]
    "[| M: sexp;  N: sexp |] ==> (N, CONS M N) : pred_sexp^+";
by (Asm_simp_tac 1);
qed "pred_sexp_CONS_I2";

Goal
    "(CONS M1 M2, N) : pred_sexp^+ ==> \
\    (M1,N) : pred_sexp^+ & (M2,N) : pred_sexp^+";
by (ftac (pred_sexp_subset_Sigma RS trancl_subset_Sigma RS subsetD) 1);
by (blast_tac (claset() addSDs [sexp_CONS_D] 
                        addIs  [pred_sexp_CONS_I1, pred_sexp_CONS_I2,
                                trans_trancl RS transD]) 1); 
qed "pred_sexp_CONS_D";


(** Conversion rules for List_rec **)

Goal "List_rec NIL c h = c";
by (rtac (List_rec_unfold RS trans) 1);
by (simp_tac (HOL_ss addsimps [List_case_NIL]) 1);
qed "List_rec_NIL"; 
Addsimps [List_rec_NIL];

Goal "[| M: sexp;  N: sexp |] ==> \
\    List_rec (CONS M N) c h = h M N (List_rec N c h)";
by (rtac (List_rec_unfold RS trans) 1);
by (asm_simp_tac (simpset() addsimps [pred_sexp_CONS_I2]) 1);
qed "List_rec_CONS";
Addsimps [List_rec_CONS];

(*** list_rec -- by List_rec ***)

val Rep_List_in_sexp =
    [range_Leaf_subset_sexp RS list_subset_sexp, Rep_List RS ListD] 
    MRS subsetD;

val list_rec_simps = [ListI RS Abs_List_inverse, Rep_List_inverse,
		      Rep_List RS ListD, rangeI, inj_Leaf, inv_f_f,
		      sexp.LeafI, Rep_List_in_sexp];


Goal "list_rec Nil c h = c";
by (simp_tac (simpset() addsimps list_rec_simps@ [list_rec_def, Nil_def]) 1);
qed "list_rec_Nil";
Addsimps [list_rec_Nil];

Goal "list_rec (a#l) c h = h a l (list_rec l c h)";
by (simp_tac (simpset() addsimps list_rec_simps@ [list_rec_def,Cons_def]) 1);
qed "list_rec_Cons";
Addsimps [list_rec_Cons];


(*Type checking.  Useful?*)
val major::A_subset_sexp::prems = 
Goal "[| M: list(A);     \
\        A<=sexp;        \
\        c: C(NIL);      \
\        !!x y r. [| x: A;  y: list(A);  r: C(y) |] ==> h x y r: C(CONS x y) \
\     |] ==> List_rec M c h : C(M :: 'a item)";
val sexp_ListA_I = A_subset_sexp RS list_subset_sexp RS subsetD;
val sexp_A_I = A_subset_sexp RS subsetD;
by (rtac (major RS list.induct) 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [sexp_A_I,sexp_ListA_I]@prems)));
qed "List_rec_type";

(** Generalized map functionals **)

Goalw [Rep_map_def] "Rep_map f Nil = NIL";
by (rtac list_rec_Nil 1);
qed "Rep_map_Nil";

Goalw [Rep_map_def]
    "Rep_map f(x#xs) = CONS(f x)(Rep_map f xs)";
by (rtac list_rec_Cons 1);
qed "Rep_map_Cons";

Goalw [Rep_map_def] "!!f. (!!x. f(x): A) ==> Rep_map f xs: list(A)";
by (rtac list_induct 1);
by Auto_tac; 
qed "Rep_map_type";

Goalw [Abs_map_def] "Abs_map g NIL = Nil";
by (rtac List_rec_NIL 1);
qed "Abs_map_NIL";

Goalw [Abs_map_def]
    "[| M: sexp;  N: sexp |] ==> Abs_map g (CONS M N) = g(M) # Abs_map g N";
by (REPEAT (ares_tac [List_rec_CONS] 1));
qed "Abs_map_CONS";

(*These 2 rules ease the use of primitive recursion.  NOTE USE OF == *)
val [rew] = goal thy
    "[| !!xs. f(xs) == list_rec xs c h  |] ==> f []  = c";
by (rewtac rew);
by (rtac list_rec_Nil 1);
qed "def_list_rec_Nil";

val [rew] = goal thy
    "[| !!xs. f(xs) == list_rec xs c h  |] ==> f(x#xs) = h x xs (f xs)";
by (rewtac rew);
by (rtac list_rec_Cons 1);
qed "def_list_rec_Cons";

Addsimps [Rep_map_Nil, Rep_map_Cons, Abs_map_NIL, Abs_map_CONS];

val [major,A_subset_sexp,minor] = 
Goal "[| M: list(A);  A<=sexp;  !!z. z: A ==> f(g(z)) = z |] \
\     ==> Rep_map f (Abs_map g M) = M";
by (rtac (major RS list.induct) 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [sexp_A_I,sexp_ListA_I,minor])));
qed "Abs_map_inverse";

(*Rep_map_inverse is obtained via Abs_Rep_map and map_ident*)

(** list_case **)

(* setting up rewrite sets *)

fun list_recs def =
      [standard (def RS def_list_rec_Nil),
       standard (def RS def_list_rec_Cons)];

val [list_case_Nil,list_case_Cons] = list_recs list_case_def;
Addsimps [list_case_Nil,list_case_Cons];

(*FIXME??
val slist_ss = (simpset()) addsimps
	  [Cons_not_Nil, Nil_not_Cons, Cons_Cons_eq,
	   list_rec_Nil, list_rec_Cons,
	   slist_case_Nil,slist_case_Cons];
*)

(** list_case **)

Goal
 "P(list_case a f xs) = ((xs=[] --> P a ) & (!y ys. xs=y#ys --> P(f y ys)))";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "expand_list_case";


(**** Function definitions ****)

fun list_recs def =
      [standard (def RS def_list_rec_Nil),
       standard (def RS def_list_rec_Cons)];

(*** Unfolding the basic combinators ***)

val [null_Nil,null_Cons] = list_recs null_def;
val [_,hd_Cons] = list_recs hd_def;
val [_,tl_Cons] = list_recs tl_def;
val [ttl_Nil,ttl_Cons] = list_recs ttl_def;
val [append_Nil,append_Cons] = list_recs append_def;
val [mem_Nil, mem_Cons] = list_recs mem_def;
val [map_Nil,map_Cons] = list_recs map_def;
val [filter_Nil,filter_Cons] = list_recs filter_def;
val [list_all_Nil,list_all_Cons] = list_recs list_all_def;

store_thm("hd_Cons",hd_Cons);
store_thm("tl_Cons",tl_Cons);
store_thm("ttl_Nil" ,ttl_Nil);
store_thm("ttl_Cons" ,ttl_Cons);
store_thm("append_Nil", append_Nil);
store_thm("append_Cons", append_Cons);
store_thm("mem_Nil" ,mem_Nil);
store_thm("mem_Cons" ,mem_Cons);
store_thm("map_Nil", map_Nil);
store_thm("map_Cons", map_Cons);
store_thm("filter_Nil", filter_Nil);
store_thm("filter_Cons", filter_Cons);
store_thm("list_all_Nil", list_all_Nil);
store_thm("list_all_Cons", list_all_Cons);


Addsimps
  [null_Nil, null_Cons, hd_Cons, tl_Cons, ttl_Nil, ttl_Cons,
   mem_Nil, mem_Cons,
   append_Nil, append_Cons,
   map_Nil, map_Cons,
   list_all_Nil, list_all_Cons,
   filter_Nil, filter_Cons];

(** nth **)

val [rew] = goal Nat.thy
    "[| !!n. f == nat_rec c h |] ==> f(0) = c";
by (rewtac rew);
by (rtac nat_rec_0 1);
qed "def_nat_rec_0_eta";

val [rew] = goal Nat.thy
    "[| !!n. f == nat_rec c h |] ==> f(Suc(n)) = h n (f n)";
by (rewtac rew);
by (rtac nat_rec_Suc 1);
qed "def_nat_rec_Suc_eta";

fun nat_recs_eta def =
      [standard (def RS def_nat_rec_0_eta),
       standard (def RS def_nat_rec_Suc_eta)];


val [nth_0,nth_Suc] = nat_recs_eta nth_def; 
store_thm("nth_0",nth_0);
store_thm("nth_Suc",nth_Suc);

Addsimps [nth_0,nth_Suc];

(** length **)

Goalw [length_def] "length([]) = 0";
by (ALLGOALS Asm_simp_tac);
qed "length_Nil";

Goalw [length_def] "length(a#xs) = Suc(length(xs))";
by (ALLGOALS Asm_simp_tac);
qed "length_Cons";

Addsimps [length_Nil,length_Cons];


(** @ - append **)

Goal "(xs@ys)@zs = xs@(ys@zs)";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Asm_simp_tac);
qed "append_assoc";

Goal "xs @ [] = xs";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_Nil2";

(** mem **)

Goal "x mem (xs@ys) = (x mem xs | x mem ys)";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "mem_append";

Goal "x mem [x:xs. P x ] = (x mem xs & P(x))";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "mem_filter";

(** list_all **)

Goal "(Alls x:xs. True) = True";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_True";

Goal "list_all p (xs@ys) = ((list_all p xs) & (list_all p ys))";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_conj";

Goal "(Alls x:xs. P(x)) = (!x. x mem xs --> P(x))";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
by (fast_tac HOL_cs 1);
qed "list_all_mem_conv";


Goal "(! n. P n) = (P 0 & (! n. P (Suc n)))";
by (Auto_tac);
by (induct_tac "n" 1);
by (Auto_tac);
qed "nat_case_dist";


val [] = Goal "(Alls u:A. P u) = (!n. n < length A --> P(nth n A))";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS Asm_simp_tac);
br trans 1;
br (nat_case_dist RS sym) 2;
by (ALLGOALS Asm_simp_tac);
qed "alls_P_eq_P_nth";


Goal "[| !x. P x --> Q x;  (Alls x:xs. P(x)) |] ==> (Alls x:xs. Q(x))";
by (asm_full_simp_tac (simpset() addsimps [list_all_mem_conv]) 1); 
qed "list_all_imp";


(** The functional "map" and the generalized functionals **)

val prems = 
Goal "(!!x. f(x): sexp) ==> \
\       Abs_map g (Rep_map f xs) = map (%t. g(f(t))) xs";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS (asm_simp_tac(simpset() addsimps
			   (prems@[Rep_map_type, list_sexp RS subsetD]))));
qed "Abs_Rep_map";


(** Additional mapping lemmas **)

Goal "map(%x. x)(xs) = xs";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident";

Goal "map f (xs@ys) = map f xs  @ map f ys";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_append";
Addsimps[map_append];

Goalw [o_def] "map(f o g)(xs) = map f (map g xs)";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose";

Addsimps
  [mem_append, mem_filter, append_assoc, append_Nil2, map_ident,
   list_all_True, list_all_conj];


Goal
"x mem (map f q) --> (? y. y mem q & x = f y)";
by (induct_thm_tac list_induct "q" 1);
by (ALLGOALS Asm_simp_tac);
by (case_tac "f xa = x" 1);
by (ALLGOALS Asm_simp_tac);
by (res_inst_tac [("x","xa")] exI 1);
by (ALLGOALS Asm_simp_tac);
br impI 1;
by (rotate_tac 1 1);
by (ALLGOALS  Asm_full_simp_tac);
be exE 1; be conjE 1;
by (res_inst_tac [("x","y")] exI 1);
by (asm_simp_tac (HOL_ss addsimps [if_cancel]) 1);
qed "mem_map_aux1";

Goal
"(? y. y mem q & x = f y) --> x mem (map f q)";
by (induct_thm_tac list_induct "q" 1);
by (Asm_simp_tac 1);
br impI 1;
be exE 1;
be conjE 1;
by (ALLGOALS Asm_simp_tac);
by (case_tac "xa = y" 1);
by (rotate_tac 2 1);
by (asm_full_simp_tac (HOL_ss addsimps [if_cancel]) 1);
be impE 1;
by (asm_simp_tac (HOL_ss addsimps [if_cancel]) 1);
by (case_tac "f xa = f y" 2);
by (res_inst_tac [("x","y")] exI 1);
by (asm_simp_tac (HOL_ss addsimps [if_cancel]) 1);
by (Auto_tac);
qed "mem_map_aux2";


Goal
"x mem (map f q) = (? y. y mem q & x = f y)";
br iffI 1;
br (mem_map_aux1 RS mp) 1;
br (mem_map_aux2 RS mp) 2;
by (ALLGOALS atac);
qed "mem_map";

Goal "A ~= [] --> hd(A @ B) = hd(A)";
by (induct_thm_tac list_induct "A" 1);
by Auto_tac; 
qed_spec_mp "hd_append";

Goal "A ~= [] --> tl(A @ B) = tl(A) @ B";
by (induct_thm_tac list_induct "A" 1);
by Auto_tac; 
qed_spec_mp "tl_append";


(* ********************************************************************* *)
(* More ...         					                 *)
(* ********************************************************************* *)


(** take **)

Goal "take [] (Suc x) = []";
by (asm_simp_tac  (simpset()) 1);
qed "take_Suc1";

Goal "take(a#xs)(Suc x) = a#take xs x";
by (asm_simp_tac (simpset()) 1);
qed "take_Suc2";


(** drop **)

Goalw [drop_def] "drop xs 0 = xs";
by (asm_simp_tac  (simpset()) 1);
qed "drop_0";

Goalw [drop_def] "drop [] (Suc x) = []";
by (induct_tac "x" 1);
by (ALLGOALS (asm_full_simp_tac ((simpset()) addsimps [ttl_Nil]) ));
qed "drop_Suc1";

Goalw [drop_def] "drop(a#xs)(Suc x) = drop xs x";
by (asm_simp_tac (simpset()) 1);
qed "drop_Suc2";


(** copy **)

Goalw [copy_def] "copy x 0 = []";
by (asm_simp_tac (simpset()) 1);
qed "copy_0";

Goalw [copy_def] "copy x (Suc y) = x # copy x y";
by (asm_simp_tac (simpset()) 1);
qed "copy_Suc";


(** fold **)

Goalw [foldl_def] "foldl f a [] = a";
by (ALLGOALS Asm_simp_tac);
qed "foldl_Nil";

Goalw [foldl_def] "foldl f a(x#xs) = foldl f (f a x) xs";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "foldl_Cons";

Goalw [foldr_def] "foldr f a [] = a";
by (ALLGOALS Asm_simp_tac);
qed "foldr_Nil";

Goalw [foldr_def] "foldr f z(x#xs)  = f x (foldr f z xs)";
by (ALLGOALS Asm_simp_tac);
qed "foldr_Cons";

Addsimps  			
		[length_Nil,length_Cons,
		 take_0, take_Suc1,take_Suc2,
		 drop_0,drop_Suc1,drop_Suc2,copy_0,copy_Suc,
		 foldl_Nil,foldl_Cons,foldr_Nil,foldr_Cons];


(** flat **)

Goalw [flat_def] 
"flat [] = []";
by (ALLGOALS Asm_simp_tac);
qed "flat_Nil";

Goalw [flat_def] 
"flat (x # xs) = x @ flat xs";
by (ALLGOALS Asm_simp_tac);
qed "flat_Cons";

Addsimps  [flat_Nil,flat_Cons];			

(** rev **)

Goalw [rev_def] 
"rev [] = []";
by (ALLGOALS Asm_simp_tac);
qed "rev_Nil";


Goalw [rev_def] 
"rev (x # xs) = rev xs @ [x]";
by (ALLGOALS Asm_simp_tac);
qed "rev_Cons";


Addsimps [rev_Nil,rev_Cons];			

(** zip **)

Goalw [zipWith_def] 
"zipWith f (a#as,b#bs)   = f(a,b) # zipWith f (as,bs)";
by (ALLGOALS Asm_simp_tac);
qed "zipWith_Cons_Cons";

Goalw [zipWith_def] 
"zipWith f ([],[])      = []";
by (ALLGOALS Asm_simp_tac);
qed "zipWith_Nil_Nil";


Goalw [zipWith_def] 
"zipWith f (x,[])  = []";
by (induct_thm_tac list_induct "x" 1);
by (ALLGOALS Asm_simp_tac);
qed "zipWith_Cons_Nil";


Goalw [zipWith_def] 
"zipWith f ([],x) = []";
by (induct_thm_tac list_induct "x" 1);
by (ALLGOALS Asm_simp_tac);
qed "zipWith_Nil_Cons";

Goalw [unzip_def] "unzip [] = ([],[])";
by (ALLGOALS Asm_simp_tac);
qed "unzip_Nil";



(** SOME LIST THEOREMS **)

(* SQUIGGOL LEMMAS *)


Goalw [o_def] "map(f o g) = ((map f) o (map g))";
br ext 1;
by (simp_tac (HOL_ss addsimps [map_compose RS sym,o_def]) 1);
qed "map_compose_ext";

Goal "map f (flat S) = flat(map (map f) S)";
by (induct_thm_tac list_induct "S" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_flat";

Goal "(Alls u:xs. f(u) = g(u)) --> map f xs = map g xs";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_all_map_eq";

Goal "filter p (map f xs) = map f (filter(p o f)(xs))";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "filter_map_d";

Goal "filter p (filter q xs) = filter(%x. p x & q x) xs";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "filter_compose";

(* "filter(p, filter(q ,xs)) = filter(q, filter(p ,xs))",
   "filter(p, filter(p ,xs)) = filter(p,xs)" BIRD's thms.*)
 
Goal "ALL B. filter p (A @ B) = (filter p A @ filter p B)";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "filter_append";
Addsimps [filter_append];

(* inits(xs) == map(fst,splits(xs)), 
 
   splits([]) = []
   splits(a # xs) = <[],xs> @ map(%x. <a # fst(x),snd(x)>, splits(xs))
   (x @ y = z) = <x,y> mem splits(z)
   x mem xs & y mem ys = <x,y> mem diag(xs,ys) *)



Goal "length(xs@ys) = length(xs)+length(ys)";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_append";

Goal "length(map f xs) = length(xs)";
by (induct_thm_tac list_induct "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_map";


Goal "take [] n = []";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "take_Nil";
Addsimps [take_Nil];

Goal "ALL n. take (take xs n) n = take xs n";
by (induct_thm_tac list_induct "xs" 1); 
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1); 
by (induct_tac "n" 1);
by Auto_tac; 
qed "take_take_eq";
Addsimps [take_take_eq];

Goal "ALL n. take (take xs(Suc(n+m))) n = take xs n";
by (induct_thm_tac list_induct "xs" 1); 
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (induct_tac "n" 1);
by Auto_tac; 
qed_spec_mp "take_take_Suc_eq1";

Delsimps [take_Suc];

Goal "take (take xs (n+m)) n = take xs n";
by (induct_tac "m" 1); 
by (ALLGOALS (asm_simp_tac (simpset() addsimps [take_take_Suc_eq1])));
qed "take_take_1";

Goal "ALL n. take (take xs n)(Suc(n+m)) = take xs n";
by (induct_thm_tac list_induct "xs" 1); 
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (induct_tac "n" 1);
by Auto_tac; 
qed_spec_mp "take_take_Suc_eq2";

Goal "take(take xs n)(n+m) = take xs n";
by (induct_tac "m" 1); 
by (ALLGOALS (asm_simp_tac (simpset() addsimps [take_take_Suc_eq2])));
qed "take_take_2";

(* length(take(xs,n)) = min(n, length(xs)) *)
(* length(drop(xs,n)) = length(xs) - n *)


Goal "drop  [] n  = []";
by (induct_tac "n" 1);
by (ALLGOALS(asm_full_simp_tac (simpset())));
qed "drop_Nil";
Addsimps [drop_Nil];


qed_goal "drop_drop" SList.thy "drop (drop xs m) n = drop xs(m+n)"
(fn _=>[res_inst_tac [("x","xs")] allE 1,
      	atac 2,
	induct_tac "m" 1,
	ALLGOALS(asm_full_simp_tac (simpset() 
				addsimps [drop_Nil])),
	rtac allI 1,
	induct_thm_tac list_induct "x" 1,
	ALLGOALS(asm_full_simp_tac (simpset() 
				addsimps [drop_Nil]))]);


qed_goal "take_drop" SList.thy  "(take xs n) @ (drop xs n) = xs"
(fn _=>[res_inst_tac [("x","xs")] allE 1,
      	atac 2,
	induct_tac "n" 1,
	ALLGOALS(asm_full_simp_tac (simpset())),
	rtac allI 1,
	induct_thm_tac list_induct "x" 1,
	ALLGOALS(asm_full_simp_tac (simpset()
					addsimps [drop_Nil,take_Nil] ))]);


qed_goal "copy_copy" SList.thy  "copy x n @ copy x m = copy x(n+m)"
(fn _=>[induct_tac "n" 1,
	ALLGOALS(asm_full_simp_tac (simpset()))]);

qed_goal "length_copy"  SList.thy  "length(copy x n)  = n"
(fn _=>[induct_tac "n" 1,
	ALLGOALS(asm_full_simp_tac (simpset()))]);


Goal "!xs. length(take xs n) = min (length xs) n";
by (induct_tac "n" 1);
 by Auto_tac;
by (induct_thm_tac list_induct "xs" 1);
 by Auto_tac;
qed_spec_mp "length_take";
Addsimps [length_take];

Goal "length(take A k) + length(drop A k)=length(A)";
by (simp_tac (HOL_ss addsimps [length_append RS sym, take_drop]) 1);
qed "length_take_drop";


Goal "ALL A. length(A) = n --> take(A@B) n = A";
by (induct_tac "n" 1);
br allI 1;
br allI 2;
by (induct_thm_tac list_induct "A" 1);
by (induct_thm_tac list_induct "A" 3);
by (ALLGOALS  Asm_full_simp_tac);
qed_spec_mp "take_append";

Goal "ALL A. length(A) = n --> take(A@B) (n+k) = A@take B k";
by (induct_tac "n" 1);
br allI 1;
br allI 2;
by (induct_thm_tac list_induct "A" 1);
by (induct_thm_tac list_induct "A" 3);
by (ALLGOALS  Asm_full_simp_tac);
qed_spec_mp "take_append2";

Goal "ALL n. take (map f A) n = map f (take A n)";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "take_map";

Goal "ALL A. length(A) = n --> drop(A@B)n = B";
by (induct_tac "n" 1);
br allI 1;
br allI 2;
by (induct_thm_tac list_induct "A" 1);
by (induct_thm_tac list_induct "A" 3);
by (ALLGOALS  Asm_full_simp_tac);
qed_spec_mp "drop_append";

Goal "ALL A. length(A) = n --> drop(A@B)(n+k) = drop B k";
by (induct_tac "n" 1);
br allI 1;
br allI 2;
by (induct_thm_tac list_induct "A" 1);
by (induct_thm_tac list_induct "A" 3);
by (ALLGOALS  Asm_full_simp_tac);
qed_spec_mp "drop_append2";


Goal "ALL A. length(A) = n --> drop A n = []";
by (induct_tac "n" 1);
br allI 1;
br allI 2;
by (induct_thm_tac list_induct "A" 1);
by (induct_thm_tac list_induct "A" 3);
by Auto_tac; 
qed_spec_mp "drop_all";

Goal "ALL n. drop (map f A) n = map f (drop A n)";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS Asm_simp_tac);
by (rtac allI 1);
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "drop_map";


Goal "ALL A. length(A) = n --> take A n = A";
by (induct_tac "n" 1);
br allI 1;
br allI 2;
by (induct_thm_tac list_induct "A" 1);
by (induct_thm_tac list_induct "A" 3);
by (ALLGOALS (simp_tac (simpset())));
by (asm_simp_tac ((simpset()) addsimps [le_eq_less_or_eq]) 1);
qed_spec_mp "take_all";

Goal "foldl f a [b] = f a b";
by (ALLGOALS Asm_simp_tac);
qed "foldl_single";


Goal "ALL a. foldl f a (A @ B) = foldl f (foldl f a A) B";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "foldl_append";
Addsimps [foldl_append];

Goal "ALL e. foldl f e (map g S) = foldl (%x y. f x (g y)) e S";
by (induct_thm_tac list_induct "S" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "foldl_map";


qed_goal "foldl_neutr_distr" SList.thy 
"[| !a. f a e = a; !a. f e a = a;          \
\   !a b c. f a (f b c) = f(f a b) c |]   \
\ ==> foldl f y A = f y (foldl f e A)"
(fn [r_neutr,l_neutr,assoc] =>
	[res_inst_tac [("x","y")] spec 1,
	induct_thm_tac list_induct "A" 1,
	ALLGOALS strip_tac,
	ALLGOALS(simp_tac (simpset() addsimps [r_neutr,l_neutr])),
	etac all_dupE 1,
	rtac trans 1,
	atac 1,
	simp_tac (HOL_ss addsimps [assoc RS spec RS spec RS spec RS sym])1,
	res_inst_tac [("f","%c. f xa c")] arg_cong 1,
	rtac sym 1,
	etac allE 1,
	atac 1]);

Goal 
"[| !a. f a e = a; !a. f e a = a;          \
\   !a b c. f a (f b c) = f(f a b) c |]   \
\ ==> foldl f e (A @ B) = f(foldl f e A)(foldl f e B)";
br trans 1;
br foldl_append 1;
br (foldl_neutr_distr) 1;
by Auto_tac; 
qed "foldl_append_sym";

Goal "ALL a. foldr f a (A @ B) = foldr f (foldr f a B) A";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "foldr_append";
Addsimps [foldr_append];

Goalw [o_def] "ALL e. foldr f e (map g S) = foldr (f o g) e S";
by (induct_thm_tac list_induct "S" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "foldr_map";

Goal "foldr op Un {} S = (UN X: {t. t mem S}.X)";
by (induct_thm_tac list_induct "S" 1);
by Auto_tac; 
qed "foldr_Un_eq_UN";


Goal "[| !a. f e a = a; !a b c. f a (f b c) = f(f a b) c |]   \
\ ==> foldr f y S = f (foldr f e S) y";
by (induct_thm_tac list_induct "S" 1);
by Auto_tac; 
qed "foldr_neutr_distr";


 Goal 
"[| !a. f e a = a; !a b c. f a (f b c) = f(f a b) c |] ==> \
\ foldr f e (A @ B) = f (foldr f e A) (foldr f e B)";
by Auto_tac;
br foldr_neutr_distr 1;
by Auto_tac; 
qed "foldr_append2";

Goal 
"[| !a. f e a = a; !a b c. f a (f b c) = f(f a b) c |] ==> \
\ foldr f e (flat S) = (foldr f e)(map (foldr f e) S)";
by (induct_thm_tac list_induct "S" 1);
by (ALLGOALS(asm_simp_tac (simpset() delsimps [foldr_append] 
                                 addsimps [foldr_append2])));
qed "foldr_flat";


Goal "(Alls x:map f xs .P(x)) = (Alls x:xs.(P o f)(x))";
by (induct_thm_tac list_induct "xs" 1);
by Auto_tac; 
qed "list_all_map";

Goal 
"(Alls x:xs. P(x)&Q(x)) = ((Alls x:xs. P(x))&(Alls x:xs. Q(x)))";
by (induct_thm_tac list_induct "xs" 1);
by Auto_tac; 
qed "list_all_and";


(* necessary to circumvent Bug in rewriter *)
val [pre] = Goal 
"(!!x. PQ(x) = (P(x) & Q(x))) ==> \
\ (Alls x:xs. PQ(x)) = ((Alls x:xs. P(x))&(Alls x:xs. Q(x)))";
by (simp_tac (HOL_ss addsimps [pre]) 1);
by (rtac list_all_and 1);
qed "list_all_and_R";


Goal "ALL i. i < length(A)  --> nth i (map f A) = f(nth i A)";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS(asm_simp_tac (simpset() delsimps [less_Suc_eq])));
br allI 1;
by (induct_tac "i" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [nth_0,nth_Suc])));
qed_spec_mp "nth_map";

Goal "ALL i. i < length(A)  --> nth i(A@B) = nth i A";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS(asm_simp_tac (simpset() delsimps [less_Suc_eq])));
br allI 1;
by (induct_tac "i" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [nth_0,nth_Suc])));
qed_spec_mp "nth_app_cancel_right";


Goal "ALL n. n = length(A) --> nth(n+i)(A@B) = nth i B";
by (induct_thm_tac list_induct "A" 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "nth_app_cancel_left";

(** flat **)

Goal  "flat(xs@ys) = flat(xs) @ flat(ys)";
by (induct_thm_tac list_induct "xs" 1);
by Auto_tac; 
qed "flat_append";
Addsimps [flat_append];

Goal "filter p (flat S) = flat(map (filter p) S)";
by (induct_thm_tac list_induct "S" 1);
by Auto_tac;
qed "filter_flat";


(** rev **)

Goal "rev(xs@ys) = rev(ys) @ rev(xs)";
by (induct_thm_tac list_induct "xs" 1);
by Auto_tac; 
qed "rev_append";
Addsimps[rev_append];

Goal "rev(rev l) = l";
by (induct_thm_tac list_induct "l" 1);
by Auto_tac; 
qed "rev_rev_ident";
Addsimps[rev_rev_ident];


Goal "rev(flat ls) = flat (map rev (rev ls))";
by (induct_thm_tac list_induct "ls" 1);
by Auto_tac;
qed "rev_flat";


Goal "rev(map f l) = map f (rev l)";
by (induct_thm_tac list_induct "l" 1);
by Auto_tac; 
qed "rev_map_distrib";

Goal "foldl f b (rev l) = foldr (%x y. f y x) b l";
by (induct_thm_tac list_induct "l" 1);
by Auto_tac; 
qed "foldl_rev";

Goal "foldr f b (rev l) = foldl (%x y. f y x) b l";
br sym 1;
br trans 1;
br foldl_rev 2;
by (simp_tac (HOL_ss addsimps [rev_rev_ident]) 1);
qed "foldr_rev";

