(*  Title:      ZF/List.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Datatype definition of Lists
*)

(*** Aspects of the datatype definition ***)

(*An elimination rule, for type-checking*)
bind_thm ("ConsE", list.mk_cases "Cons(a,l) : list(A)");

(*Proving freeness results*)
bind_thm ("Cons_iff", list.mk_free "Cons(a,l)=Cons(a',l') <-> a=a' & l=l'");
bind_thm ("Nil_Cons_iff", list.mk_free "~ Nil=Cons(a,l)");

Goal "list(A) = {0} + (A * list(A))";
by (blast_tac (claset() addSIs (map (rewrite_rule list.con_defs) list.intrs) 
                        addEs [rewrite_rule list.con_defs list.elim]) 1);
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

val prems = Goalw [thm "map_list_def"]
    "[| l: list(A);  !!x. x: A ==> h(x): B |] ==> map(h,l) : list(B)";
by (REPEAT (ares_tac (prems @ list.intrs @ [list_rec_type]) 1));
qed "map_type";

Goal "l: list(A) ==> map(h,l) : list({h(u). u:A})";
by (etac map_type 1);
by (etac RepFunI 1);
qed "map_type2";

(** length **)

Goalw [thm "length_list_def"]
    "l: list(A) ==> length(l) : nat";
by (REPEAT (ares_tac [list_rec_type, nat_0I, nat_succI] 1));
qed "length_type";

(** app **)

Goalw [thm "op @_list_def"]
    "[| xs: list(A);  ys: list(A) |] ==> xs@ys : list(A)";
by (REPEAT (ares_tac [list_rec_type, list.Cons_I] 1));
qed "app_type";

(** rev **)

Goalw [thm "rev_list_def"]
    "xs: list(A) ==> rev(xs) : list(A)";
by (REPEAT (ares_tac (list.intrs @ [list_rec_type, app_type]) 1));
qed "rev_type";


(** flat **)

Goalw [thm "flat_list_def"]
    "ls: list(list(A)) ==> flat(ls) : list(A)";
by (REPEAT (ares_tac (list.intrs @ [list_rec_type, app_type]) 1));
qed "flat_type";


(** set_of_list **)

Goalw [thm "set_of_list_list_def"]
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

Goalw [thm "list_add_list_def"] 
    "xs: list(nat) ==> list_add(xs) : nat";
by (REPEAT (ares_tac [list_rec_type, nat_0I, add_type] 1));
qed "list_add_type";

bind_thms ("list_typechecks",
    list.intrs @
    [list_rec_type, map_type, map_type2, app_type, length_type, 
     rev_type, flat_type, list_add_type]);

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


(*** Thanks to Sidi Ehmety for these results about min, take, etc. ***)

(** min **)
(* Min theorems are also true for i, j ordinals *)
Goalw [min_def] "[| i:nat; j:nat |] ==> min(i,j)=min(j,i)";
by (auto_tac (claset() addSDs [not_lt_imp_le] 
                       addDs [lt_not_sym] 
                       addIs [le_anti_sym], simpset()));
qed "min_sym";

Goalw [min_def] "[| i:nat; j:nat |] ==> min(i,j):nat";
by Auto_tac;
qed "min_type";
AddTCs [min_type];
Addsimps [min_type];

Goalw [min_def]  "i:nat ==> min(0,i) = 0";
by (auto_tac (claset() addDs [not_lt_imp_le], simpset()));
qed "min_0";
Addsimps [min_0];

Goalw [min_def] "i:nat ==> min(i, 0) = 0";
by (auto_tac (claset() addDs [not_lt_imp_le], simpset()));
qed "min_02";
Addsimps [min_02];

Goalw [min_def] "[| i:nat; j:nat; k:nat |] ==> i<min(j,k) <-> i<j & i<k";
by (auto_tac (claset() addSDs [not_lt_imp_le]
                       addIs [lt_trans2, lt_trans], simpset()));
qed "lt_min_iff";

Goalw [min_def]
     "[| i:nat; j:nat |] ==>  min(succ(i), succ(j))= succ(min(i, j))";
by Auto_tac;
qed "min_succ_succ";
Addsimps [min_succ_succ];

(*** more theorems about lists ***)

Goal "xs:list(A) ==> (xs~=Nil)<->(EX y:A. EX ys:list(A). xs=Cons(y,ys))";
by (induct_tac "xs" 1);
by Auto_tac;
qed "neq_Nil_iff";

(** filter **)

Goal "xs:list(A) ==> filter(P, xs@ys) = filter(P, xs) @ filter(P, ys)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "filter_append";
Addsimps [filter_append];

Goal "xs:list(A) ==> filter(P, xs):list(A)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "filter_type";

Goal "xs:list(A) ==> length(filter(P, xs)) le length(xs)";
by (induct_tac "xs" 1);
by Auto_tac;
by (res_inst_tac [("j", "length(l)")] le_trans 1);
by (auto_tac (claset(), simpset() addsimps [le_iff]));
qed "length_filter";

Goal "xs:list(A) ==> set_of_list(filter(P,xs)) <= set_of_list(xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "filter_is_subset";

Goal "xs:list(A) ==> filter(%p. False, xs) = Nil";
by (induct_tac "xs" 1);
by Auto_tac;
qed "filter_False";

Goal "xs:list(A) ==> filter(%p. True, xs) = xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "filter_True";
Addsimps [filter_False, filter_True];

(** length **)

Goal "xs:list(A) ==> length(xs)=0 <-> xs=Nil";
by (etac list.induct 1);
by Auto_tac;
qed "length_is_0_iff";
Addsimps [length_is_0_iff];

Goal "xs:list(A) ==> 0 = length(xs) <-> xs=Nil";
by (etac list.induct 1);
by Auto_tac;
qed "length_is_0_iff2";
Addsimps [length_is_0_iff2];

Goal "xs:list(A) ==> length(tl(xs)) = length(xs) #- 1";
by (etac list.induct 1);
by Auto_tac;
qed "length_tl";
Addsimps [length_tl];

Goal "xs:list(A) ==> 0<length(xs) <-> xs ~= Nil";
by (etac list.induct 1);
by Auto_tac;
qed "length_greater_0_iff";

Goal "xs:list(A) ==> length(xs)=succ(n) <-> (EX y ys. xs=Cons(y, ys) & length(ys)=n)";
by (etac list.induct 1);
by Auto_tac;
qed "length_succ_iff";

(** more theorems about append **)

Goal "xs:list(A) ==> (xs@ys = Nil) <-> (xs=Nil & ys = Nil)";
by (etac list.induct 1);
by Auto_tac;
qed "append_is_Nil_iff";
Addsimps [append_is_Nil_iff];

Goal "xs:list(A) ==> (Nil = xs@ys) <-> (xs=Nil & ys = Nil)";
by (etac list.induct 1);
by Auto_tac;
qed "append_is_Nil_iff2";
Addsimps [append_is_Nil_iff2];

Goal "xs:list(A) ==> (xs@ys = xs) <-> (ys = Nil)";
by (etac list.induct 1);
by Auto_tac;
qed "append_left_is_self_iff";
Addsimps [append_left_is_self_iff];

Goal "xs:list(A) ==> (xs = xs@ys) <-> (ys = Nil)";
by (etac list.induct 1);
by Auto_tac;
qed "append_left_is_self_iff2";
Addsimps [append_left_is_self_iff2];

(*TOO SLOW as a default simprule!*)
Goal "[| xs:list(A); ys:list(A); zs:list(A) |] ==> \
\  length(ys)=length(zs) --> (xs@ys=zs <-> (xs=Nil & ys=zs))";
by (etac list.induct 1);
by (auto_tac (claset(), simpset() addsimps [length_app]));
qed_spec_mp "append_left_is_Nil_iff";

(*TOO SLOW as a default simprule!*)
Goal "[| xs:list(A); ys:list(A); zs:list(A) |] ==> \
\  length(ys)=length(zs) --> (zs=ys@xs <-> (xs=Nil & ys=zs))";
by (etac list.induct 1);
by (auto_tac (claset(), simpset() addsimps [length_app]));
qed_spec_mp "append_left_is_Nil_iff2";

Goal "xs:list(A) ==> ALL ys:list(A). \
\     length(xs)=length(ys) --> (xs@us = ys@vs) <-> (xs=ys & us=vs)";
by (etac list.induct 1);
by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac [("a", "ys")] list.elim 1);
by (ALLGOALS(Asm_full_simp_tac));
qed_spec_mp "append_eq_append_iff";


Goal "xs:list(A) ==>  \
\  ALL ys:list(A). ALL us:list(A). ALL vs:list(A). \
\  length(us) = length(vs) --> (xs@us = ys@vs) --> (xs=ys & us=vs)";
by (induct_tac "xs" 1);
by (ALLGOALS(Clarify_tac));
by (asm_full_simp_tac (simpset() addsimps [length_app]) 1);
by (eres_inst_tac [("a", "ys")] list.elim 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "Cons(a, l) @ us =vs" 1);
by (dtac (rotate_prems 4 (append_left_is_Nil_iff RS iffD1)) 1);
by Auto_tac;
qed_spec_mp "append_eq_append";

Goal "[| xs:list(A); ys:list(A); us:list(A); vs:list(A); length(us)=length(vs) |] \ 
\ ==>  xs@us = ys@vs <-> (xs=ys & us=vs)";
by (rtac iffI 1);
by (rtac append_eq_append 1);
by Auto_tac;
qed "append_eq_append_iff2";
Addsimps [append_eq_append_iff, append_eq_append_iff2];

Goal "[| xs:list(A); ys:list(A); zs:list(A) |] ==> xs@ys=xs@zs <-> ys=zs";
by (Asm_simp_tac 1);
qed "append_self_iff";
Addsimps [append_self_iff];

Goal "[| xs:list(A); ys:list(A); zs:list(A) |] ==> ys@xs=zs@xs <-> ys=zs";
by (Asm_simp_tac 1);
qed "append_self_iff2";
Addsimps [append_self_iff2];

(* Can also be proved from append_eq_append_iff2,
but the proof requires two more hypotheses: x:A and y:A *)
Goal "xs:list(A) ==> ALL ys:list(A). xs@[x] = ys@[y] <-> (xs = ys & x=y)";
by (etac list.induct 1);
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(eres_inst_tac [("a", "ys")] list.elim));
by Auto_tac;
qed_spec_mp "append1_eq_iff";
Addsimps [append1_eq_iff];

Goal "[| xs:list(A); ys:list(A) |] ==> (xs@ys = ys) <-> (xs=Nil)";
by (asm_simp_tac (simpset() addsimps [append_left_is_Nil_iff]) 1);
qed "append_right_is_self_iff";
Addsimps [append_right_is_self_iff];

Goal "[| xs:list(A); ys:list(A) |] ==> (ys = xs@ys) <-> (xs=Nil)";
by (rtac iffI 1);
by (dtac sym 1);
by (ALLGOALS(Asm_full_simp_tac));
qed "append_right_is_self_iff2";
Addsimps [append_right_is_self_iff2];

Goal "xs:list(A) ==> xs ~= Nil --> hd(xs @ ys) = hd(xs)";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "hd_append";
Addsimps [hd_append];

Goal "xs:list(A) ==> xs~=Nil --> tl(xs @ ys) = tl(xs)@ys";
by (induct_tac "xs" 1);
by Auto_tac;
qed_spec_mp "tl_append";
Addsimps [tl_append];

(** rev **)
Goal "xs:list(A) ==> (rev(xs) = Nil <-> xs = Nil)";
by (etac list.induct 1);
by Auto_tac;
qed "rev_is_Nil_iff";
Addsimps [rev_is_Nil_iff];

Goal "xs:list(A) ==> (Nil = rev(xs) <-> xs = Nil)";
by (etac list.induct 1);
by Auto_tac;
qed "Nil_is_rev_iff";
Addsimps [Nil_is_rev_iff];

Goal "xs:list(A) ==> ALL ys:list(A). rev(xs)=rev(ys) <-> xs=ys";
by (etac list.induct 1);
by (Force_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac [("a", "ys")] list.elim 1);
by Auto_tac;
qed_spec_mp "rev_is_rev_iff";
Addsimps [rev_is_rev_iff];

Goal "xs:list(A) ==> \
\ (xs=Nil --> P) --> (ALL ys:list(A). ALL y:A. xs =ys@[y] -->P)-->P";
by (etac list_append_induct 1);
by Auto_tac;
qed_spec_mp "rev_list_elim_aux";

bind_thm("rev_list_elim", impI RS ballI RS ballI RSN(3, rev_list_elim_aux));

(** more theorems about drop **)

Goal "n:nat ==> ALL xs:list(A). length(drop(n, xs)) = length(xs) #- n";
by (etac nat_induct 1);
by (auto_tac (claset() addEs [list.elim], simpset()));
qed_spec_mp "length_drop";
Addsimps [length_drop];

Goal "n:nat ==> ALL xs:list(A). length(xs) le n --> drop(n, xs)=Nil";
by (etac nat_induct 1);
by (auto_tac (claset() addEs [list.elim], simpset()));
qed_spec_mp "drop_all";
Addsimps [drop_all];

Goal "n:nat ==> ALL xs:list(A). drop(n, xs@ys) = \
\ drop(n,xs) @ drop(n #- length(xs), ys)"; 
by (induct_tac "n" 1);
by (auto_tac (claset() addEs [list.elim], simpset()));
qed_spec_mp "drop_append";

Goal "m:nat ==> \
\ ALL xs:list(A). ALL n:nat. drop(n, drop(m, xs))=drop(n #+ m, xs)";
by (induct_tac "m" 1);
by (auto_tac (claset() addEs [list.elim], simpset()));
qed "drop_drop";

(** take **)

Goalw [take_def]
 "xs:list(A) ==> take(0, xs) =  Nil";
by (etac list.induct 1);
by Auto_tac;
qed "take_0";
Addsimps [take_0];

Goalw [take_def]
"n:nat ==> take(succ(n), Cons(a, xs)) = Cons(a, take(n, xs))";
by (Asm_simp_tac 1);
qed "take_succ_Cons";
Addsimps [take_succ_Cons];

(* Needed for proving take_all *)
Goalw [take_def]
 "n:nat ==> take(n, Nil) = Nil";
by Auto_tac;
qed "take_Nil";
Addsimps [take_Nil];
 
Goal "n:nat ==> ALL xs:list(A). length(xs) le n  --> take(n, xs) = xs";
by (etac nat_induct 1);
by (auto_tac (claset() addEs [list.elim], simpset()));
qed_spec_mp  "take_all";
Addsimps [take_all];

Goal "xs:list(A) ==> ALL n:nat. take(n, xs):list(A)";
by (etac list.induct 1);
by (Clarify_tac 2);
by (etac natE 2);
by Auto_tac;
qed_spec_mp "take_type";

Goal "xs:list(A) ==> \
\ ALL ys:list(A). ALL n:nat. take(n, xs @ ys) = \
\                           take(n, xs) @ take(n #- length(xs), ys)";
by (etac list.induct 1);
by (Clarify_tac 2);
by (etac natE 2);
by Auto_tac;
qed_spec_mp "take_append";
Addsimps [take_append];

Goal
"m:nat ==> \
\ ALL xs:list(A). ALL n:nat. take(n, take(m,xs))= take(min(n, m), xs)";
by (induct_tac "m" 1);
by Auto_tac;
by (eres_inst_tac [("a", "xs")] list.elim 1);
by (auto_tac (claset(), simpset() addsimps [take_Nil]));
by (rotate_tac 1 1);
by (etac natE 1);
by (auto_tac (claset() addIs [take_0, take_type], simpset()));
qed_spec_mp "take_take";

(** nth **)

Goalw [nth_def] "nth(0, Cons(a, l))= a";
by Auto_tac;
qed "nth_0";
Addsimps [nth_0];

Goalw [nth_def]  
   "n:nat ==> nth(succ(n), Cons(a, l)) = nth(n, l)";
by (Asm_simp_tac 1);
qed "nth_Cons";
Addsimps [nth_Cons];

Goal "xs:list(A) ==> ALL n:nat. n < length(xs) --> nth(n, xs):A";
by (etac list.induct 1);
by (ALLGOALS(Clarify_tac));
by (etac natE 2);
by (ALLGOALS(Asm_full_simp_tac));
qed_spec_mp "nth_type";

AddTCs [nth_type];
Addsimps [nth_type];

Goal 
"xs:list(A) ==> ALL n:nat. \
\ nth(n, xs @ ys) = (if n < length(xs) then nth(n,xs) \
\                      else nth(n #- length(xs),ys))";
by (induct_tac "xs" 1);
by (Clarify_tac 2);
by (etac natE 2);
by (ALLGOALS(Asm_full_simp_tac));
qed_spec_mp "nth_append";

Goal "xs:list(A) \
\     ==> set_of_list(xs) = {x:A. EX i:nat. i<length(xs) & x=nth(i, xs)}";
by (induct_tac "xs" 1);
by (ALLGOALS(Asm_simp_tac));
by (rtac equalityI 1);
by Auto_tac;
by (res_inst_tac [("x", "0")] bexI 1);
by Auto_tac;
by (etac natE 1);
by Auto_tac;
qed "set_of_list_conv_nth";

(* Other theorems about lists *)

Goalw [Ball_def]
 "k:nat ==> \
\ ALL xs:list(A). (ALL ys:list(A). k le length(xs) --> k le length(ys) -->  \
\     (ALL i:nat. i<k --> nth(i,xs)= nth(i,ys))--> take(k, xs) = take(k,ys))";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps 
             [lt_succ_eq_0_disj, all_conj_distrib])));
by (Clarify_tac 1);
(*Both lists must be non-empty*)
by (case_tac "xa=Nil" 1);
by (case_tac "xb=Nil" 2);
by (Clarify_tac 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [neq_Nil_iff])));
by (Clarify_tac 1);
(*prenexing's needed, not miniscoping*)
by (Asm_simp_tac 1);
by (rtac conjI 1);
by (Force_tac 1);
by (ALLGOALS (full_simp_tac (simpset() addsimps (all_simps RL [iff_sym])  
                                       delsimps (all_simps))));
by (dres_inst_tac [("x", "ys"), ("x1", "ysa")] (spec RS spec) 1);
by (Clarify_tac 1);
by Auto_tac;
qed_spec_mp "nth_take_lemma";

Goal "[| xs:list(A); ys:list(A); length(xs) = length(ys);  \
\        ALL i:nat. i < length(xs) --> nth(i,xs) = nth(i,ys) |]  \
\     ==> xs = ys";
by (subgoal_tac "length(xs) le length(ys)" 1);
by (forw_inst_tac [("ys", "ys")] (rotate_prems 1 nth_take_lemma) 1);
by (ALLGOALS(Asm_simp_tac));
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [take_all])));
qed_spec_mp "nth_equalityI";

(*The famous take-lemma*)

Goal "[| xs:list(A); ys:list(A); (ALL i:nat. take(i, xs) = take(i,ys)) |] ==> xs = ys";
by (case_tac "length(xs) le length(ys)" 1);
by (dres_inst_tac [("x", "length(ys)")] bspec 1);
by (dtac not_lt_imp_le 3);
by (subgoal_tac "length(ys) le length(xs)" 5);
by (res_inst_tac [("j", "succ(length(ys))")] le_trans 6);
by (rtac leI 6);
by (dres_inst_tac [("x", "length(xs)")] bspec 5);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [take_all])));
qed_spec_mp "take_equalityI";

Goal "n:nat ==> ALL i:nat. ALL xs:list(A). n #+ i le length(xs) \
\               --> nth(i, drop(n, xs)) = nth(n #+ i, xs)";
by (induct_tac "n" 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Clarify_tac 1);
by (case_tac "xb=Nil" 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [neq_Nil_iff])));
by (Clarify_tac 1);
by (auto_tac (claset() addSEs [ConsE], simpset()));
qed_spec_mp "nth_drop";

(** zip **)

Goal "l:list(A) ==> l:list(set_of_list(l))";
by (induct_tac "l" 1);
by Auto_tac;
by (res_inst_tac [("A1", "set_of_list(l)")] (list_mono RS subsetD) 1);
by Auto_tac;
qed "list_on_set_of_list";

Goal "A<=C ==> ziprel(A, B) <= ziprel(C,B)";
by (Clarify_tac 1);
by (forward_tac [ziprel.dom_subset RS subsetD] 1);
by (Clarify_tac 1);
by (etac ziprel.induct 1);
by (auto_tac (claset() addIs [list_mono RS subsetD]
                       addSIs ziprel.intrs, simpset()));
qed "ziprel_mono1";

Goal "B<=C ==> ziprel(A, B) <= ziprel(A,C)";
by (Clarify_tac 1);
by (forward_tac [ziprel.dom_subset RS subsetD] 1);
by (Clarify_tac 1);
by (etac ziprel.induct 1);
by (auto_tac (claset() addIs [list_mono RS subsetD]
                       addSIs ziprel.intrs, simpset()));
qed "ziprel_mono2";

Goal "[| A<=C; B<=D |] ==> ziprel(A, B) <= ziprel(C,D)";
by (rtac subset_trans 1);
by (rtac ziprel_mono1 2);
by (rtac ziprel_mono2 1);
by Auto_tac;
qed "ziprel_mono";

(* ziprel is a function *)

Goal "<xs, ys, zs>:ziprel(A,B) \
\     ==> ALL ks. <xs, ys, ks>:ziprel(A, B) --> ks=zs";
by (etac ziprel.induct 1);
by (ALLGOALS(Clarify_tac));
by (rotate_tac 1 3);
by (ALLGOALS(etac ziprel.elim));
by Safe_tac;
(* These hypotheses make Auto_tac loop! *)
by (thin_tac "ALL k. ?P(k)" 3);
by (thin_tac "ALL k. ?P(k)" 4);
by Auto_tac;
qed "ziprel_is_fun";

Goal "ys:list(B)  ==> ALL xs:list(A). EX zs. <xs, ys, zs>:ziprel(A,B)";
by (induct_tac "ys" 1);
by (auto_tac (claset() addIs ziprel.intrs, simpset()));
by (eres_inst_tac [("a", "xs")] list.elim 1);
by (auto_tac (claset() addIs ziprel.intrs, simpset()));
qed_spec_mp "ziprel_exist"; 

Goalw [zip_def]
 "[|xs:list(A); ys:list(B) |] ==> <xs, ys, zip(xs,ys)>:ziprel(A,B)";
by (rtac theI2 1);
by (asm_full_simp_tac (simpset() addsimps [set_of_list_append]) 2);
by (REPEAT(dtac set_of_list_type 2));
by (rtac (ziprel_mono RS subsetD) 2);
by (Blast_tac 3);
by (dtac list_on_set_of_list 1);
by (dtac list_on_set_of_list 1);
by (subgoal_tac "xs:list(set_of_list(xs@ys)) & \
\                ys:list(set_of_list(xs@ys))" 1);
by (auto_tac (claset() addIs [list_mono RS subsetD],
              simpset() addsimps [set_of_list_append]));
by (rtac (ziprel_is_fun RS spec RS mp) 2); 
by (rtac ziprel_exist 1);
by Auto_tac;
qed "zip_in_ziprel";

Goal
"<xs, ys, zs>:ziprel(A,B) ==> zip(xs, ys)=zs";
by (rtac (ziprel_is_fun RS spec RS mp) 1);
by (Blast_tac 1);
by (blast_tac (claset() addDs [ziprel.dom_subset RS subsetD]
                        addIs [zip_in_ziprel]) 1);
qed "zip_eq";

(* zip equations *)

Goal "ys:list(A) ==> zip(Nil, ys)=Nil";
by (res_inst_tac [("A", "A")] zip_eq 1);
by (auto_tac (claset() addIs ziprel.intrs, simpset()));
qed "zip_Nil";
Addsimps [zip_Nil];

Goal "xs:list(A) ==> zip(xs, Nil)=Nil";
by (res_inst_tac [("A", "A")] zip_eq 1);
by (auto_tac (claset() addIs ziprel.intrs, simpset()));
qed "zip_Nil2";
Addsimps [zip_Nil2];

Goal "[| xs:list(A); ys:list(B); x:A; y:B |] ==> \
\ zip(Cons(x,xs), Cons(y, ys)) = Cons(<x,y>, zip(xs, ys))";
by (res_inst_tac [("A", "A")] zip_eq 1);
by (forw_inst_tac [("ys", "ys")] zip_in_ziprel 1);
by (auto_tac (claset() addIs ziprel.intrs, simpset()));
qed "zip_Cons_Cons";
Addsimps [zip_Cons_Cons];

Goal "xs:list(A) ==> ALL ys:list(B). zip(xs, ys):list(A*B)";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac [("a", "ys")] list.elim 1);
by Auto_tac;
qed_spec_mp "zip_type";

AddTCs [zip_type];
Addsimps [zip_type];    

(* zip length *)
Goalw [min_def] "xs:list(A) ==> ALL ys:list(B). length(zip(xs,ys)) = \
\                               min(length(xs), length(ys))";
by (induct_tac "xs" 1);
by (Clarify_tac 2);
by (eres_inst_tac [("a", "ys")] list.elim 2);
by Auto_tac;
qed_spec_mp "length_zip";  
Addsimps [length_zip];

AddTCs [take_type];
Addsimps [take_type];

Goal "[| ys:list(A); zs:list(B) |] ==> ALL xs:list(A). zip(xs @ ys, zs) = \
\ zip(xs, take(length(xs), zs)) @ zip(ys, drop(length(xs),zs))";
by (induct_tac "zs" 1);
by (Clarify_tac 2);
by (eres_inst_tac [("a", "xs")] list.elim 2);
by Auto_tac;
qed_spec_mp "zip_append1";

Goal
 "[| xs:list(A); zs:list(B) |] ==> ALL ys:list(B). zip(xs, ys@zs) = \
\      zip(take(length(ys), xs), ys) @ zip(drop(length(ys), xs), zs)";
by (induct_tac "xs" 1);
by (Clarify_tac 2);
by (eres_inst_tac [("a", "ys")] list.elim 2);
by Auto_tac;
qed_spec_mp "zip_append2";

Goal
 "[| length(xs) = length(us); length(ys) = length(vs); \
\  xs:list(A); us:list(B); ys:list(A); vs:list(B) |] ==> \
\ zip(xs@ys,us@vs) = zip(xs, us) @ zip(ys, vs)";
by (asm_simp_tac (simpset() addsimps 
                  [zip_append1, drop_append, diff_self_eq_0]) 1);
qed_spec_mp "zip_append";
Addsimps [zip_append];

Goal "ys:list(B) ==> ALL xs:list(A).  \
\ length(xs) = length(ys) --> zip(rev(xs), rev(ys)) = rev(zip(xs, ys))";
by (induct_tac "ys" 1);
by (Clarify_tac 2);
by (eres_inst_tac [("a", "xs")] list.elim 2);
by (auto_tac (claset(), simpset() addsimps [length_rev]));
qed_spec_mp "zip_rev";
Addsimps [zip_rev];

Goal
"ys:list(B) ==> ALL i:nat. ALL xs:list(A). \
\                   i < length(xs) --> i < length(ys) --> \
\                   nth(i,zip(xs, ys)) = <nth(i,xs),nth(i, ys)>";
by (induct_tac "ys" 1);
by (Clarify_tac 2);
by (eres_inst_tac [("a", "xs")] list.elim 2);
by (auto_tac (claset() addEs [natE], simpset()));
qed_spec_mp "nth_zip";
Addsimps [nth_zip];

Goal "[| xs:list(A); ys:list(B); i:nat |] \
\     ==> set_of_list(zip(xs, ys)) = \
\         {<x, y>:A*B. EX i:nat. i < min(length(xs), length(ys))  \
\         & x=nth(i, xs) & y=nth(i, ys)}";
by (force_tac (claset() addSIs [Collect_cong], 
               simpset() addsimps [lt_min_iff, set_of_list_conv_nth]) 1);
qed_spec_mp "set_of_list_zip";

(** list_update **)

Goalw [list_update_def] "i:nat ==>list_update(Nil, i, v) = Nil";
by Auto_tac;
qed "list_update_Nil";
Addsimps [list_update_Nil];

Goalw [list_update_def] 
"list_update(Cons(x, xs), 0, v)= Cons(v, xs)";
by Auto_tac;
qed "list_update_Cons_0";
Addsimps [list_update_Cons_0];

Goalw [list_update_def] 
"n:nat ==>\
\ list_update(Cons(x, xs), succ(n), v)= Cons(x, list_update(xs, n, v))";
by Auto_tac;
qed "list_update_Cons_succ";
Addsimps [list_update_Cons_succ];

Goal "[| xs:list(A); v:A |] ==> ALL n:nat. list_update(xs, n, v):list(A)";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (etac natE 1);
by Auto_tac;
qed_spec_mp "list_update_type";
Addsimps [list_update_type];
AddTCs [list_update_type];

Goal "xs:list(A) ==> ALL i:nat. length(list_update(xs, i, v))=length(xs)";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (etac natE 1);
by Auto_tac;
qed_spec_mp "length_list_update";
Addsimps [length_list_update];

Goal "[| xs:list(A) |] ==> ALL i:nat. ALL j:nat. i < length(xs)  --> \
\ nth(j, list_update(xs, i, x)) = (if i=j then x else nth(j, xs))";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (etac natE 1);
by (ALLGOALS(Asm_full_simp_tac));
by (ALLGOALS(Clarify_tac));
by (etac natE 1);
by (ALLGOALS(Asm_full_simp_tac));
by Safe_tac;
by (etac natE 2);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [nth_Cons])));
qed_spec_mp "nth_list_update";

Goal "[| i < length(xs); xs:list(A); i:nat |] \
\  ==> nth(i, list_update(xs, i,x)) = x";
by (asm_simp_tac (simpset() addsimps [nth_list_update]) 1);
qed "nth_list_update_eq";
Addsimps [nth_list_update_eq];

Goal "xs:list(A) ==> ALL i:nat. ALL j:nat. i ~= j \
\ --> nth(j, list_update(xs, i,x)) = nth(j, xs)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (etac natE 1);
by (etac natE 2);
by (ALLGOALS(Asm_full_simp_tac));
by (etac natE 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [nth_Cons])));
qed_spec_mp "nth_list_update_neq";
Addsimps [nth_list_update_neq];

Goal "xs:list(A) ==> ALL i:nat. i < length(xs)\
\  --> list_update(list_update(xs, i, x), i, y) = list_update(xs, i,y)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (etac natE 1);
by Auto_tac;
qed_spec_mp "list_update_overwrite";
Addsimps [list_update_overwrite];

Goal "xs:list(A) ==> ALL i:nat. i < length(xs) --> \
\ (list_update(xs, i, x) = xs) <-> (nth(i, xs) = x)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (etac natE 1);
by Auto_tac;
qed_spec_mp "list_update_same_conv";

Goal "ys:list(B) ==> ALL i:nat. ALL xy:A*B. ALL xs:list(A). \
\ length(xs) = length(ys) --> \
\     list_update(zip(xs, ys), i, xy) = zip(list_update(xs, i, fst(xy)), \
\                                         list_update(ys, i, snd(xy)))";
by (induct_tac "ys" 1);
 by Auto_tac;
by (eres_inst_tac [("a", "xc")] list.elim 1);
by (auto_tac (claset() addEs [natE], simpset()));
qed_spec_mp "update_zip";

Goal "xs:list(A) ==> ALL i:nat. set_of_list(list_update(xs, i, x)) \
\  <= cons(x, set_of_list(xs))";
by (induct_tac "xs" 1);
 by (asm_full_simp_tac (simpset() addsimps []) 1);
by (rtac ballI 1);
by (etac natE 1);
by (ALLGOALS(Asm_full_simp_tac));
by Auto_tac;
qed_spec_mp "set_update_subset_cons";

Goal "[| set_of_list(xs) <= A; xs:list(A); x:A; i:nat|]  \
\  ==> set_of_list(list_update(xs, i,x)) <= A";
by (rtac subset_trans 1);
by (rtac set_update_subset_cons 1);
by Auto_tac;
qed "set_of_list_update_subsetI";

(** upt **)

Goal "[| i:nat; j:nat |] \
\ ==> upt(i,j) = (if i<j then Cons(i, upt(succ(i), j)) else Nil)";
by (induct_tac "j" 1);
by Auto_tac;
by (dtac not_lt_imp_le 1);
by (auto_tac (claset() addIs [le_anti_sym], simpset()));
qed "upt_rec";

Goal "[| j le i; i:nat; j:nat |] ==> upt(i,j) = Nil";
by (stac upt_rec 1);
by Auto_tac;
by (auto_tac (claset(), simpset() addsimps [le_iff]));
by (dtac (lt_asym RS notE) 1);
by Auto_tac;
qed "upt_conv_Nil";
Addsimps [upt_conv_Nil];

(*Only needed if upt_Suc is deleted from the simpset*)
Goal "[| i le j; i:nat; j:nat |] ==> upt(i,succ(j)) = upt(i, j)@[j]";
by (Asm_simp_tac 1);
qed "upt_succ_append";

Goal "[| i<j; i:nat; j:nat |]  ==> upt(i,j) = Cons(i,upt(succ(i),j))";
by (rtac trans 1);
by (stac upt_rec 1);
by (rtac refl 4);
by Auto_tac;
qed "upt_conv_Cons";

Goal "[| i:nat; j:nat |] ==> upt(i,j):list(nat)";
by (induct_tac "j" 1);
by Auto_tac;
qed "upt_type";

AddTCs [upt_type];
Addsimps [upt_type];

(*LOOPS as a simprule, since j<=j*)
Goal "[| i le j; i:nat; j:nat; k:nat |] ==> \
\ upt(i, j #+k) = upt(i,j)@upt(j,j#+k)";
by (induct_tac "k" 1);
by (auto_tac (claset(), simpset() addsimps [app_assoc, app_type]));
by (res_inst_tac [("j", "j")] le_trans 1);
by Auto_tac;
qed "upt_add_eq_append";

Goal "[| i:nat; j:nat |] ==>length(upt(i,j)) = j #- i";
by (induct_tac "j" 1);
by (rtac sym 2);
by (auto_tac (claset() addSDs [not_lt_imp_le], 
              simpset() addsimps [length_app, diff_succ, diff_is_0_iff]));
qed "length_upt";
Addsimps [length_upt];

Goal "[| i:nat; j:nat; k:nat |] ==> \
\ i #+ k < j --> nth(k, upt(i,j)) = i #+ k";
by (induct_tac "j" 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [nth_append,lt_succ_iff] 
                                 addsplits [nat_diff_split]) 1);
by Safe_tac;
by (auto_tac (claset() addSDs [not_lt_imp_le], 
              simpset() addsimps [nth_append, diff_self_eq_0, 
                                  less_diff_conv, add_commute])); 
by (dres_inst_tac [("j", "x")] lt_trans2 1);
by Auto_tac;
qed_spec_mp "nth_upt";
Addsimps [nth_upt];

Goal "[| m:nat; n:nat |] ==> \
\ ALL i:nat. i #+ m le n --> take(m, upt(i,n)) = upt(i,i#+m)";
by (induct_tac "m" 1);
by (asm_simp_tac (simpset() addsimps [take_0]) 1);
by (Clarify_tac 1);
by (stac upt_rec 1);
by (rtac sym 3);
by (stac upt_rec 3);
by (ALLGOALS(asm_full_simp_tac (simpset() delsimps (thms"upt.simps"))));
by (res_inst_tac [("j", "succ(i #+ x)")] lt_trans2 1);
by Auto_tac;
qed_spec_mp "take_upt";
Addsimps [take_upt];

Goal "[| m:nat; n:nat |] ==> map(succ, upt(m,n))= upt(succ(m), succ(n))";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [map_app_distrib]));
qed "map_succ_upt";

Goal "xs:list(A) ==> \
\ ALL n:nat. n < length(xs) --> nth(n, map(f, xs)) = f(nth(n, xs))";
by (induct_tac "xs" 1);
by (Asm_full_simp_tac 1);
by (rtac ballI 1);
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "nth_map";
Addsimps [nth_map];

Goal "[| m:nat; n:nat |] ==> \
\ ALL i:nat. i < n #- m --> nth(i, map(f, upt(m,n))) = f(m #+ i)";
by (res_inst_tac [("n", "m"), ("m", "n")] diff_induct 1);
by (stac (map_succ_upt RS sym) 5);
by (ALLGOALS(Asm_full_simp_tac));
by (ALLGOALS(Clarify_tac));
by (subgoal_tac "xa < length(upt(0, x))" 1);
by (Asm_simp_tac 2);
by (subgoal_tac "xa < length(upt(y, x))" 2);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [map_compose, 
          nth_map, add_commute, less_diff_conv])));
by (res_inst_tac [("j", "succ(xa #+ y)")] lt_trans2 1);
by Auto_tac;
qed_spec_mp "nth_map_upt";

(** sublist (a generalization of nth to sets) **)

Goalw [sublist_def] "xs:list(A) ==>sublist(xs, 0) =Nil";
by Auto_tac;
qed "sublist_0";

Goalw [sublist_def] "sublist(Nil, A) = Nil";
by Auto_tac;
qed "sublist_Nil";

AddTCs [filter_type];
Addsimps [filter_type];

Goal "[| xs:list(B); i:nat |] ==>\
\    map(fst, filter(%p. snd(p):A, zip(xs, upt(i,i #+ length(xs))))) = \
\    map(fst, filter(%p. snd(p):nat & snd(p) #+ i:A, zip(xs,upt(0,length(xs)))))";
by (etac list_append_induct  1);
by (Asm_simp_tac 1);
by (auto_tac (claset(), simpset() addsimps 
         [add_commute, length_app, filter_append, map_app_distrib]));
qed "sublist_shift_lemma";

Goalw [sublist_def]
 "xs:list(B) ==> sublist(xs, A):list(B)";
by (induct_tac "xs" 1);
by (auto_tac (claset(), simpset() addsimps [filter_append, map_app_distrib]));
by (auto_tac (claset() addIs [map_type,filter_type,zip_type], simpset()));
qed "sublist_type";

AddTCs [sublist_type];
Addsimps [sublist_type];

Goal "[| i:nat; j:nat |] ==> upt(0, i #+ j) = upt(0, i) @ upt(i, i #+ j)";
by (asm_simp_tac (simpset() addsimps 
                [inst "i" "0" upt_add_eq_append, nat_0_le]) 1);
qed "upt_add_eq_append2";

Goalw [sublist_def]
     "[| xs:list(B); ys:list(B)  |] ==> \
\ sublist(xs@ys, A) = sublist(xs, A) @ sublist(ys, {j:nat. j #+ length(xs): A})";
by (eres_inst_tac [("l", "ys")] list_append_induct 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [upt_add_eq_append2, 
                                      zip_append, length_app,  app_assoc RS sym]) 1);
by (auto_tac (claset(), simpset() addsimps [sublist_shift_lemma, 
                                           length_type, map_app_distrib, app_assoc]));
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [add_commute])));
qed "sublist_append";

Addsimps [sublist_0, sublist_Nil];

Goal "[| xs:list(B); x:B |] ==> \
\ sublist(Cons(x, xs), A) = (if 0:A then [x] else []) @ sublist(xs, {j:nat. succ(j) : A})";
by (eres_inst_tac [("l", "xs")] list_append_induct 1);
by (asm_simp_tac (simpset() addsimps [sublist_def]) 1);
by (asm_simp_tac (simpset() delsimps (thms "op @.simps") 
                 addsimps [(hd (tl (thms "op @.simps"))) RS sym, sublist_append]) 1);
by Auto_tac;
qed "sublist_Cons";

Goal "sublist([x], A) = (if 0 : A then [x] else [])";
by (simp_tac (simpset() addsimps [sublist_Cons]) 1);
qed "sublist_singleton";
Addsimps [sublist_singleton];

Goalw [less_than_def]
    "[| xs:list(A); n:nat |] ==> sublist(xs, less_than(n)) = take(n,xs)";
by (eres_inst_tac [("l", "xs")] list_append_induct 1);
 by (asm_simp_tac (simpset() addsplits [nat_diff_split]
                             addsimps [sublist_append]) 2);
by Auto_tac;
by (subgoal_tac "n #- length(y) = 0" 1);
by (Asm_simp_tac 1);
by (auto_tac (claset() addSDs [not_lt_imp_le], 
          simpset() addsimps [diff_is_0_iff]));
qed "sublist_upt_eq_take";
Addsimps [sublist_upt_eq_take];

