(*  Title:      ZF/List.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Datatype definition of Lists
*)

(*** Aspects of the datatype definition ***)

(*An elimination rule, for type-checking*)
val ConsE = list.mk_cases "Cons(a,l) : list(A)";

(*Proving freeness results*)
val Cons_iff     = list.mk_free "Cons(a,l)=Cons(a',l') <-> a=a' & l=l'";
val Nil_Cons_iff = list.mk_free "~ Nil=Cons(a,l)";

Goal "list(A) = {0} + (A * list(A))";
let open list;  val rew = rewrite_rule con_defs in  
by (blast_tac (claset() addSIs (map rew intrs) addEs [rew elim]) 1)
end;
qed "list_unfold";

(**  Lemmas to justify using "list" in other recursive type definitions **)

Goalw list.defs "A<=B ==> list(A) <= list(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac list.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
qed "list_mono";

(*There is a similar proof by list induction.*)
Goalw (list.defs@list.con_defs) "list(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (blast_tac (claset() addSIs [zero_in_univ, Inl_in_univ, Inr_in_univ,
				Pair_in_univ]) 1);
qed "list_univ";

(*These two theorems justify datatypes involving list(nat), list(A), ...*)
bind_thm ("list_subset_univ", [list_mono, list_univ] MRS subset_trans);

Goal "[| l: list(A);  A <= univ(B) |] ==> l: univ(B)";
by (REPEAT (ares_tac [list_subset_univ RS subsetD] 1));
qed "list_into_univ";

val major::prems = Goal
    "[| l: list(A);    \
\       c: C(Nil);       \
\       !!x y. [| x: A;  y: list(A) |] ==> h(x,y): C(Cons(x,y))  \
\    |] ==> list_case(c,h,l) : C(l)";
by (rtac (major RS list.induct) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "list_case_type";


(*** List functions ***)

Goal "l: list(A) ==> tl(l) : list(A)";
by (exhaust_tac "l" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps list.intrs)));
qed "tl_type";

(** drop **)

Goal "i:nat ==> drop(i, Nil) = Nil";
by (induct_tac "i" 1);
by (ALLGOALS Asm_simp_tac);
qed "drop_Nil";

Goal "i:nat ==> drop(succ(i), Cons(a,l)) = drop(i,l)";
by (rtac sym 1);
by (induct_tac "i" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "drop_succ_Cons";

Addsimps [drop_Nil, drop_succ_Cons];

Goal "[| i:nat; l: list(A) |] ==> drop(i,l) : list(A)";
by (induct_tac "i" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [tl_type])));
qed "drop_type";

Delsimps [drop_SUCC];


(** Type checking -- proved by induction, as usual **)

val prems = Goal
    "[| l: list(A);    \
\       c: C(Nil);       \
\       !!x y r. [| x:A;  y: list(A);  r: C(y) |] ==> h(x,y,r): C(Cons(x,y))  \
\    |] ==> list_rec(c,h,l) : C(l)";
by (cut_facts_tac prems 1);
by (induct_tac "l" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "list_rec_type";

(** map **)

val prems = Goalw [get_def thy "map_list"] 
    "[| l: list(A);  !!x. x: A ==> h(x): B |] ==> map(h,l) : list(B)";
by (REPEAT (ares_tac (prems @ list.intrs @ [list_rec_type]) 1));
qed "map_type";

Goal "l: list(A) ==> map(h,l) : list({h(u). u:A})";
by (etac map_type 1);
by (etac RepFunI 1);
qed "map_type2";

(** length **)

Goalw [get_def thy "length_list"] 
    "l: list(A) ==> length(l) : nat";
by (REPEAT (ares_tac [list_rec_type, nat_0I, nat_succI] 1));
qed "length_type";

(** app **)

Goalw [get_def thy "op @_list"] 
    "[| xs: list(A);  ys: list(A) |] ==> xs@ys : list(A)";
by (REPEAT (ares_tac [list_rec_type, list.Cons_I] 1));
qed "app_type";

(** rev **)

Goalw [get_def thy "rev_list"] 
    "xs: list(A) ==> rev(xs) : list(A)";
by (REPEAT (ares_tac (list.intrs @ [list_rec_type, app_type]) 1));
qed "rev_type";


(** flat **)

Goalw [get_def thy "flat_list"] 
    "ls: list(list(A)) ==> flat(ls) : list(A)";
by (REPEAT (ares_tac (list.intrs @ [list_rec_type, app_type]) 1));
qed "flat_type";


(** set_of_list **)

Goalw [get_def thy "set_of_list_list"] 
    "l: list(A) ==> set_of_list(l) : Pow(A)";
by (etac list_rec_type 1);
by (ALLGOALS (Blast_tac));
qed "set_of_list_type";

Goal "xs: list(A) ==> \
\         set_of_list (xs@ys) = set_of_list(xs) Un set_of_list(ys)";
by (etac list.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Un_cons])));
qed "set_of_list_append";


(** list_add **)

Goalw [get_def thy "list_add_list"] 
    "xs: list(nat) ==> list_add(xs) : nat";
by (REPEAT (ares_tac [list_rec_type, nat_0I, add_type] 1));
qed "list_add_type";

val list_typechecks =
    list.intrs @
    [list_rec_type, map_type, map_type2, app_type, length_type, 
     rev_type, flat_type, list_add_type];

AddTCs list_typechecks;


(*** theorems about map ***)

Goal "l: list(A) ==> map(%u. u, l) = l";
by (induct_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident";
Addsimps [map_ident];

Goal "l: list(A) ==> map(h, map(j,l)) = map(%u. h(j(u)), l)";
by (induct_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose";

Goal "xs: list(A) ==> map(h, xs@ys) = map(h,xs) @ map(h,ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_app_distrib";

Goal "ls: list(list(A)) ==> map(h, flat(ls)) = flat(map(map(h),ls))";
by (induct_tac "ls" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [map_app_distrib])));
qed "map_flat";

Goal "l: list(A) ==> \
\    list_rec(c, d, map(h,l)) = \
\    list_rec(c, %x xs r. d(h(x), map(h,xs), r), l)";
by (induct_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_rec_map";

(** theorems about list(Collect(A,P)) -- used in ex/term.ML **)

(* c : list(Collect(B,P)) ==> c : list(B) *)
bind_thm ("list_CollectD", Collect_subset RS list_mono RS subsetD);

Goal "l: list({x:A. h(x)=j(x)}) ==> map(h,l) = map(j,l)";
by (induct_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_list_Collect";

(*** theorems about length ***)

Goal "xs: list(A) ==> length(map(h,xs)) = length(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_map";

Goal "[| xs: list(A); ys: list(A) |] \
\     ==> length(xs@ys) = length(xs) #+ length(ys)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "length_app";

Goal "xs: list(A) ==> length(rev(xs)) = length(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [length_app])));
qed "length_rev";

Goal "ls: list(list(A)) ==> length(flat(ls)) = list_add(map(length,ls))";
by (induct_tac "ls" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [length_app])));
qed "length_flat";

(** Length and drop **)

(*Lemma for the inductive step of drop_length*)
Goal "xs: list(A) ==> \
\          ALL x.  EX z zs. drop(length(xs), Cons(x,xs)) = Cons(z,zs)";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed_spec_mp "drop_length_Cons";

Goal "l: list(A) ==> ALL i:length(l). (EX z zs. drop(i,l) = Cons(z,zs))";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
by Safe_tac;
by (etac drop_length_Cons 1);
by (rtac natE 1);
by (etac ([asm_rl, length_type, Ord_nat] MRS Ord_trans) 1);
by (assume_tac 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (blast_tac (claset() addIs [succ_in_naturalD, length_type])));
qed_spec_mp "drop_length";


(*** theorems about app ***)

Goal "xs: list(A) ==> xs@Nil=xs";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "app_right_Nil";
Addsimps [app_right_Nil];

Goal "xs: list(A) ==> (xs@ys)@zs = xs@(ys@zs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "app_assoc";

Goal "ls: list(list(A)) ==> flat(ls@ms) = flat(ls)@flat(ms)";
by (induct_tac "ls" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [app_assoc])));
qed "flat_app_distrib";

(*** theorems about rev ***)

Goal "l: list(A) ==> rev(map(h,l)) = map(h,rev(l))";
by (induct_tac "l" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [map_app_distrib])));
qed "rev_map_distrib";

(*Simplifier needs the premises as assumptions because rewriting will not
  instantiate the variable ?A in the rules' typing conditions; note that
  rev_type does not instantiate ?A.  Only the premises do.
*)
Goal "[| xs: list(A);  ys: list(A) |] ==> rev(xs@ys) = rev(ys)@rev(xs)";
by (etac list.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [app_assoc])));
qed "rev_app_distrib";

Goal "l: list(A) ==> rev(rev(l))=l";
by (induct_tac "l" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [rev_app_distrib])));
qed "rev_rev_ident";
Addsimps [rev_rev_ident];

Goal "ls: list(list(A)) ==> rev(flat(ls)) = flat(map(rev,rev(ls)))";
by (induct_tac "ls" 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps 
		   [map_app_distrib, flat_app_distrib, rev_app_distrib])));
qed "rev_flat";


(*** theorems about list_add ***)

Goal "[| xs: list(nat);  ys: list(nat) |] ==> \
\    list_add(xs@ys) = list_add(ys) #+ list_add(xs)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "list_add_app";

Goal "l: list(nat) ==> list_add(rev(l)) = list_add(l)";
by (induct_tac "l" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [list_add_app])));
qed "list_add_rev";

Goal "ls: list(list(nat)) ==> list_add(flat(ls)) = list_add(map(list_add,ls))";
by (induct_tac "ls" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [list_add_app])));
by (REPEAT (ares_tac [refl, list_add_type, map_type, add_commute] 1));
qed "list_add_flat";

(** New induction rule **)

val major::prems = Goal
    "[| l: list(A);  \
\       P(Nil);        \
\       !!x y. [| x: A;  y: list(A);  P(y) |] ==> P(y @ [x]) \
\    |] ==> P(l)";
by (rtac (major RS rev_rev_ident RS subst) 1);
by (rtac (major RS rev_type RS list.induct) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "list_append_induct";

