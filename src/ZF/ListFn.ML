(*  Title: 	ZF/list-fn.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For list-fn.thy.  Lists in Zermelo-Fraenkel Set Theory 
*)

open ListFn;

(** hd and tl **)

goalw ListFn.thy [hd_def] "hd(Cons(a,l)) = a";
by (resolve_tac List.case_eqns 1);
val hd_Cons = result();

goalw ListFn.thy [tl_def] "tl(Nil) = Nil";
by (resolve_tac List.case_eqns 1);
val tl_Nil = result();

goalw ListFn.thy [tl_def] "tl(Cons(a,l)) = l";
by (resolve_tac List.case_eqns 1);
val tl_Cons = result();

goal ListFn.thy "!!l. l: list(A) ==> tl(l) : list(A)";
by (etac List.elim 1);
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps (List.intrs @ [tl_Nil,tl_Cons]))));
val tl_type = result();

(** drop **)

goalw ListFn.thy [drop_def] "drop(0, l) = l";
by (rtac rec_0 1);
val drop_0 = result();

goalw ListFn.thy [drop_def] "!!i. i:nat ==> drop(i, Nil) = Nil";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac (nat_ss addsimps [tl_Nil])));
val drop_Nil = result();

goalw ListFn.thy [drop_def]
    "!!i. i:nat ==> drop(succ(i), Cons(a,l)) = drop(i,l)";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac (nat_ss addsimps [tl_Cons])));
val drop_succ_Cons = result();

goalw ListFn.thy [drop_def] 
    "!!i l. [| i:nat; l: list(A) |] ==> drop(i,l) : list(A)";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac (nat_ss addsimps [tl_type])));
val drop_type = result();

(** list_rec -- by Vset recursion **)

goal ListFn.thy "list_rec(Nil,c,h) = c";
by (rtac (list_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (ZF_ss addsimps List.case_eqns) 1);
val list_rec_Nil = result();

goal ListFn.thy "list_rec(Cons(a,l), c, h) = h(a, l, list_rec(l,c,h))";
by (rtac (list_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (ZF_ss addsimps (List.case_eqns @ [Vset_rankI, rank_Cons2])) 1);
val list_rec_Cons = result();

(*Type checking -- proved by induction, as usual*)
val prems = goal ListFn.thy
    "[| l: list(A);    \
\       c: C(Nil);       \
\       !!x y r. [| x:A;  y: list(A);  r: C(y) |] ==> h(x,y,r): C(Cons(x,y))  \
\    |] ==> list_rec(l,c,h) : C(l)";
by (list_ind_tac "l" prems 1);
by (ALLGOALS (asm_simp_tac
	      (ZF_ss addsimps (prems@[list_rec_Nil,list_rec_Cons]))));
val list_rec_type = result();

(** Versions for use with definitions **)

val [rew] = goal ListFn.thy
    "[| !!l. j(l)==list_rec(l, c, h) |] ==> j(Nil) = c";
by (rewtac rew);
by (rtac list_rec_Nil 1);
val def_list_rec_Nil = result();

val [rew] = goal ListFn.thy
    "[| !!l. j(l)==list_rec(l, c, h) |] ==> j(Cons(a,l)) = h(a,l,j(l))";
by (rewtac rew);
by (rtac list_rec_Cons 1);
val def_list_rec_Cons = result();

fun list_recs def = map standard
    	([def] RL [def_list_rec_Nil, def_list_rec_Cons]);

(** map **)

val [map_Nil,map_Cons] = list_recs map_def;

val prems = goalw ListFn.thy [map_def] 
    "[| l: list(A);  !!x. x: A ==> h(x): B |] ==> map(h,l) : list(B)";
by (REPEAT (ares_tac (prems@[list_rec_type, NilI, ConsI]) 1));
val map_type = result();

val [major] = goal ListFn.thy "l: list(A) ==> map(h,l) : list({h(u). u:A})";
by (rtac (major RS map_type) 1);
by (etac RepFunI 1);
val map_type2 = result();

(** length **)

val [length_Nil,length_Cons] = list_recs length_def;

goalw ListFn.thy [length_def] 
    "!!l. l: list(A) ==> length(l) : nat";
by (REPEAT (ares_tac [list_rec_type, nat_0I, nat_succI] 1));
val length_type = result();

(** app **)

val [app_Nil,app_Cons] = list_recs app_def;

goalw ListFn.thy [app_def] 
    "!!xs ys. [| xs: list(A);  ys: list(A) |] ==> xs@ys : list(A)";
by (REPEAT (ares_tac [list_rec_type, ConsI] 1));
val app_type = result();

(** rev **)

val [rev_Nil,rev_Cons] = list_recs rev_def;

val prems = goalw ListFn.thy [rev_def] 
    "xs: list(A) ==> rev(xs) : list(A)";
by (REPEAT (ares_tac (prems @ [list_rec_type, NilI, ConsI, app_type]) 1));
val rev_type = result();


(** flat **)

val [flat_Nil,flat_Cons] = list_recs flat_def;

val prems = goalw ListFn.thy [flat_def] 
    "ls: list(list(A)) ==> flat(ls) : list(A)";
by (REPEAT (ares_tac (prems @ [list_rec_type, NilI, ConsI, app_type]) 1));
val flat_type = result();


(** list_add **)

val [list_add_Nil,list_add_Cons] = list_recs list_add_def;

val prems = goalw ListFn.thy [list_add_def] 
    "xs: list(nat) ==> list_add(xs) : nat";
by (REPEAT (ares_tac (prems @ [list_rec_type, nat_0I, add_type]) 1));
val list_add_type = result();

(** ListFn simplification **)

val list_typechecks =
      [NilI, ConsI, list_rec_type,
       map_type, map_type2, app_type, length_type, rev_type, flat_type,
       list_add_type];

val list_ss = arith_ss 
    addsimps List.case_eqns
    addsimps [list_rec_Nil, list_rec_Cons, 
	     map_Nil, map_Cons,
	     app_Nil, app_Cons,
	     length_Nil, length_Cons,
	     rev_Nil, rev_Cons,
	     flat_Nil, flat_Cons,
	     list_add_Nil, list_add_Cons]
    setsolver (type_auto_tac list_typechecks);
(*Could also rewrite using the list_typechecks...*)

(*** theorems about map ***)

val prems = goal ListFn.thy
    "l: list(A) ==> map(%u.u, l) = l";
by (list_ind_tac "l" prems 1);
by (ALLGOALS (asm_simp_tac list_ss));
val map_ident = result();

val prems = goal ListFn.thy
    "l: list(A) ==> map(h, map(j,l)) = map(%u.h(j(u)), l)";
by (list_ind_tac "l" prems 1);
by (ALLGOALS (asm_simp_tac list_ss));
val map_compose = result();

val prems = goal ListFn.thy
    "xs: list(A) ==> map(h, xs@ys) = map(h,xs) @ map(h,ys)";
by (list_ind_tac "xs" prems 1);
by (ALLGOALS (asm_simp_tac list_ss));
val map_app_distrib = result();

val prems = goal ListFn.thy
    "ls: list(list(A)) ==> map(h, flat(ls)) = flat(map(map(h),ls))";
by (list_ind_tac "ls" prems 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [map_app_distrib])));
val map_flat = result();

val prems = goal ListFn.thy
    "l: list(A) ==> \
\    list_rec(map(h,l), c, d) = \
\    list_rec(l, c, %x xs r. d(h(x), map(h,xs), r))";
by (list_ind_tac "l" prems 1);
by (ALLGOALS (asm_simp_tac list_ss));
val list_rec_map = result();

(** theorems about list(Collect(A,P)) -- used in ex/term.ML **)

(* c : list(Collect(B,P)) ==> c : list(B) *)
val list_CollectD = standard (Collect_subset RS list_mono RS subsetD);

val prems = goal ListFn.thy
    "l: list({x:A. h(x)=j(x)}) ==> map(h,l) = map(j,l)";
by (list_ind_tac "l" prems 1);
by (ALLGOALS (asm_simp_tac list_ss));
val map_list_Collect = result();

(*** theorems about length ***)

val prems = goal ListFn.thy
    "xs: list(A) ==> length(map(h,xs)) = length(xs)";
by (list_ind_tac "xs" prems 1);
by (ALLGOALS (asm_simp_tac list_ss));
val length_map = result();

val prems = goal ListFn.thy
    "xs: list(A) ==> length(xs@ys) = length(xs) #+ length(ys)";
by (list_ind_tac "xs" prems 1);
by (ALLGOALS (asm_simp_tac list_ss));
val length_app = result();

(* [| m: nat; n: nat |] ==> m #+ succ(n) = succ(n) #+ m 
   Used for rewriting below*)
val add_commute_succ = nat_succI RSN (2,add_commute);

val prems = goal ListFn.thy
    "xs: list(A) ==> length(rev(xs)) = length(xs)";
by (list_ind_tac "xs" prems 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [length_app, add_commute_succ])));
val length_rev = result();

val prems = goal ListFn.thy
    "ls: list(list(A)) ==> length(flat(ls)) = list_add(map(length,ls))";
by (list_ind_tac "ls" prems 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [length_app])));
val length_flat = result();

(** Length and drop **)

(*Lemma for the inductive step of drop_length*)
goal ListFn.thy
    "!!xs. xs: list(A) ==> \
\          ALL x.  EX z zs. drop(length(xs), Cons(x,xs)) = Cons(z,zs)";
by (etac List.induct 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [drop_0,drop_succ_Cons])));
by (fast_tac ZF_cs 1);
val drop_length_Cons_lemma = result();
val drop_length_Cons = standard (drop_length_Cons_lemma RS spec);

goal ListFn.thy
    "!!l. l: list(A) ==> ALL i: length(l).  EX z zs. drop(i,l) = Cons(z,zs)";
by (etac List.induct 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps bquant_simps)));
by (rtac conjI 1);
by (etac drop_length_Cons 1);
by (rtac ballI 1);
by (rtac natE 1);
by (etac ([asm_rl, length_type, Ord_nat] MRS Ord_trans) 1);
by (assume_tac 1);
by (asm_simp_tac (list_ss addsimps [drop_0]) 1);
by (fast_tac ZF_cs 1);
by (asm_simp_tac (list_ss addsimps [drop_succ_Cons]) 1);
by (dtac bspec 1);
by (fast_tac ZF_cs 2);
by (fast_tac (ZF_cs addEs [succ_in_naturalD,length_type]) 1);
val drop_length_lemma = result();
val drop_length = standard (drop_length_lemma RS bspec);


(*** theorems about app ***)

val [major] = goal ListFn.thy "xs: list(A) ==> xs@Nil=xs";
by (rtac (major RS List.induct) 1);
by (ALLGOALS (asm_simp_tac list_ss));
val app_right_Nil = result();

val prems = goal ListFn.thy "xs: list(A) ==> (xs@ys)@zs = xs@(ys@zs)";
by (list_ind_tac "xs" prems 1);
by (ALLGOALS (asm_simp_tac list_ss));
val app_assoc = result();

val prems = goal ListFn.thy
    "ls: list(list(A)) ==> flat(ls@ms) = flat(ls)@flat(ms)";
by (list_ind_tac "ls" prems 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [app_assoc])));
val flat_app_distrib = result();

(*** theorems about rev ***)

val prems = goal ListFn.thy "l: list(A) ==> rev(map(h,l)) = map(h,rev(l))";
by (list_ind_tac "l" prems 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [map_app_distrib])));
val rev_map_distrib = result();

(*Simplifier needs the premises as assumptions because rewriting will not
  instantiate the variable ?A in the rules' typing conditions; note that
  rev_type does not instantiate ?A.  Only the premises do.
*)
goal ListFn.thy
    "!!xs. [| xs: list(A);  ys: list(A) |] ==> rev(xs@ys) = rev(ys)@rev(xs)";
by (etac List.induct 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [app_right_Nil,app_assoc])));
val rev_app_distrib = result();

val prems = goal ListFn.thy "l: list(A) ==> rev(rev(l))=l";
by (list_ind_tac "l" prems 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [rev_app_distrib])));
val rev_rev_ident = result();

val prems = goal ListFn.thy
    "ls: list(list(A)) ==> rev(flat(ls)) = flat(map(rev,rev(ls)))";
by (list_ind_tac "ls" prems 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps 
       [map_app_distrib, flat_app_distrib, rev_app_distrib, app_right_Nil])));
val rev_flat = result();


(*** theorems about list_add ***)

val prems = goal ListFn.thy
    "[| xs: list(nat);  ys: list(nat) |] ==> \
\    list_add(xs@ys) = list_add(ys) #+ list_add(xs)";
by (cut_facts_tac prems 1);
by (list_ind_tac "xs" prems 1);
by (ALLGOALS 
    (asm_simp_tac (list_ss addsimps [add_0_right, add_assoc RS sym])));
by (rtac (add_commute RS subst_context) 1);
by (REPEAT (ares_tac [refl, list_add_type] 1));
val list_add_app = result();

val prems = goal ListFn.thy
    "l: list(nat) ==> list_add(rev(l)) = list_add(l)";
by (list_ind_tac "l" prems 1);
by (ALLGOALS
    (asm_simp_tac (list_ss addsimps [list_add_app, add_0_right])));
val list_add_rev = result();

val prems = goal ListFn.thy
    "ls: list(list(nat)) ==> list_add(flat(ls)) = list_add(map(list_add,ls))";
by (list_ind_tac "ls" prems 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [list_add_app])));
by (REPEAT (ares_tac [refl, list_add_type, map_type, add_commute] 1));
val list_add_flat = result();

(** New induction rule **)

val major::prems = goal ListFn.thy
    "[| l: list(A);  \
\       P(Nil);        \
\       !!x y. [| x: A;  y: list(A);  P(y) |] ==> P(y @ [x]) \
\    |] ==> P(l)";
by (rtac (major RS rev_rev_ident RS subst) 1);
by (rtac (major RS rev_type RS List.induct) 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps prems)));
val list_append_induct = result();

