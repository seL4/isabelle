(*  Title:      ZF/List.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Datatype definition of Lists
*)

open List;

(*** Aspects of the datatype definition ***)

Addsimps list.case_eqns;


(*An elimination rule, for type-checking*)
val ConsE = list.mk_cases list.con_defs "Cons(a,l) : list(A)";

(*Proving freeness results*)
val Cons_iff     = list.mk_free "Cons(a,l)=Cons(a',l') <-> a=a' & l=l'";
val Nil_Cons_iff = list.mk_free "~ Nil=Cons(a,l)";

(*Perform induction on l, then prove the major premise using prems. *)
fun list_ind_tac a prems i = 
    EVERY [res_inst_tac [("x",a)] list.induct i,
           rename_last_tac a ["1"] (i+2),
           ares_tac prems i];

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
bind_thm ("list_subset_univ", ([list_mono, list_univ] MRS subset_trans));

Goal "[| l: list(A);  A <= univ(B) |] ==> l: univ(B)";
by (REPEAT (ares_tac [list_subset_univ RS subsetD] 1));
qed "list_into_univ";

val major::prems = Goal
    "[| l: list(A);    \
\       c: C(Nil);       \
\       !!x y. [| x: A;  y: list(A) |] ==> h(x,y): C(Cons(x,y))  \
\    |] ==> list_case(c,h,l) : C(l)";
by (rtac (major RS list.induct) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps list.case_eqns @ prems)));
qed "list_case_type";


(** For recursion **)

Goalw list.con_defs "rank(a) < rank(Cons(a,l))";
by (simp_tac rank_ss 1);
qed "rank_Cons1";

Goalw list.con_defs "rank(l) < rank(Cons(a,l))";
by (simp_tac rank_ss 1);
qed "rank_Cons2";


(*** List functions ***)

(** hd and tl **)

Goalw [hd_def] "hd(Cons(a,l)) = a";
by (resolve_tac list.case_eqns 1);
qed "hd_Cons";

Goalw [tl_def] "tl(Nil) = Nil";
by (resolve_tac list.case_eqns 1);
qed "tl_Nil";

Goalw [tl_def] "tl(Cons(a,l)) = l";
by (resolve_tac list.case_eqns 1);
qed "tl_Cons";

Addsimps [hd_Cons, tl_Nil, tl_Cons];

Goal "l: list(A) ==> tl(l) : list(A)";
by (etac list.elim 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps list.intrs)));
qed "tl_type";

(** drop **)

Goalw [drop_def] "drop(0, l) = l";
by (rtac rec_0 1);
qed "drop_0";

Goalw [drop_def] "i:nat ==> drop(i, Nil) = Nil";
by (etac nat_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "drop_Nil";

Goalw [drop_def]
    "i:nat ==> drop(succ(i), Cons(a,l)) = drop(i,l)";
by (rtac sym 1);
by (etac nat_induct 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "drop_succ_Cons";

Addsimps [drop_0, drop_Nil, drop_succ_Cons];

Goalw [drop_def] 
    "[| i:nat; l: list(A) |] ==> drop(i,l) : list(A)";
by (etac nat_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [tl_type])));
qed "drop_type";

(** list_rec -- by Vset recursion **)

Goal "list_rec(Nil,c,h) = c";
by (rtac (list_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (simpset() addsimps list.case_eqns) 1);
qed "list_rec_Nil";

Goal "list_rec(Cons(a,l), c, h) = h(a, l, list_rec(l,c,h))";
by (rtac (list_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (rank_ss addsimps rank_Cons2::list.case_eqns) 1);
qed "list_rec_Cons";

Addsimps [list_rec_Nil, list_rec_Cons];


(*Type checking -- proved by induction, as usual*)
val prems = Goal
    "[| l: list(A);    \
\       c: C(Nil);       \
\       !!x y r. [| x:A;  y: list(A);  r: C(y) |] ==> h(x,y,r): C(Cons(x,y))  \
\    |] ==> list_rec(l,c,h) : C(l)";
by (list_ind_tac "l" prems 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "list_rec_type";

(** Versions for use with definitions **)

val [rew] = Goal "[| !!l. j(l)==list_rec(l, c, h) |] ==> j(Nil) = c";
by (rewtac rew);
by (rtac list_rec_Nil 1);
qed "def_list_rec_Nil";

val [rew] = Goal "[| !!l. j(l)==list_rec(l, c, h) |] ==> j(Cons(a,l)) = h(a,l,j(l))";
by (rewtac rew);
by (rtac list_rec_Cons 1);
qed "def_list_rec_Cons";

fun list_recs def = map standard
        ([def] RL [def_list_rec_Nil, def_list_rec_Cons]);

(** map **)

val [map_Nil,map_Cons] = list_recs map_def;
Addsimps [map_Nil, map_Cons];

val prems = Goalw [map_def] 
    "[| l: list(A);  !!x. x: A ==> h(x): B |] ==> map(h,l) : list(B)";
by (REPEAT (ares_tac (prems @ list.intrs @ [list_rec_type]) 1));
qed "map_type";

Goal "l: list(A) ==> map(h,l) : list({h(u). u:A})";
by (etac map_type 1);
by (etac RepFunI 1);
qed "map_type2";

(** length **)

val [length_Nil,length_Cons] = list_recs length_def;
Addsimps [length_Nil,length_Cons];

Goalw [length_def] 
    "l: list(A) ==> length(l) : nat";
by (REPEAT (ares_tac [list_rec_type, nat_0I, nat_succI] 1));
qed "length_type";

(** app **)

val [app_Nil,app_Cons] = list_recs app_def;
Addsimps [app_Nil, app_Cons];

Goalw [app_def] 
    "[| xs: list(A);  ys: list(A) |] ==> xs@ys : list(A)";
by (REPEAT (ares_tac [list_rec_type, list.Cons_I] 1));
qed "app_type";

(** rev **)

val [rev_Nil,rev_Cons] = list_recs rev_def;
Addsimps [rev_Nil,rev_Cons] ;

Goalw [rev_def] 
    "xs: list(A) ==> rev(xs) : list(A)";
by (REPEAT (ares_tac (list.intrs @ [list_rec_type, app_type]) 1));
qed "rev_type";


(** flat **)

val [flat_Nil,flat_Cons] = list_recs flat_def;
Addsimps [flat_Nil,flat_Cons];

Goalw [flat_def] 
    "ls: list(list(A)) ==> flat(ls) : list(A)";
by (REPEAT (ares_tac (list.intrs @ [list_rec_type, app_type]) 1));
qed "flat_type";


(** set_of_list **)

val [set_of_list_Nil,set_of_list_Cons] = list_recs set_of_list_def;
Addsimps [set_of_list_Nil,set_of_list_Cons];

Goalw [set_of_list_def] 
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

val [list_add_Nil,list_add_Cons] = list_recs list_add_def;
Addsimps [list_add_Nil,list_add_Cons];

Goalw [list_add_def] 
    "xs: list(nat) ==> list_add(xs) : nat";
by (REPEAT (ares_tac [list_rec_type, nat_0I, add_type] 1));
qed "list_add_type";

val list_typechecks =
    list.intrs @
    [list_rec_type, map_type, map_type2, app_type, length_type, 
     rev_type, flat_type, list_add_type];

simpset_ref() := simpset() setSolver (type_auto_tac list_typechecks);


(*** theorems about map ***)

Goal "l: list(A) ==> map(%u. u, l) = l";
by (list_ind_tac "l" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident";

Goal "l: list(A) ==> map(h, map(j,l)) = map(%u. h(j(u)), l)";
by (list_ind_tac "l" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose";

Goal "xs: list(A) ==> map(h, xs@ys) = map(h,xs) @ map(h,ys)";
by (list_ind_tac "xs" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "map_app_distrib";

Goal "ls: list(list(A)) ==> map(h, flat(ls)) = flat(map(map(h),ls))";
by (list_ind_tac "ls" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [map_app_distrib])));
qed "map_flat";

Goal "l: list(A) ==> \
\    list_rec(map(h,l), c, d) = \
\    list_rec(l, c, %x xs r. d(h(x), map(h,xs), r))";
by (list_ind_tac "l" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "list_rec_map";

(** theorems about list(Collect(A,P)) -- used in ex/term.ML **)

(* c : list(Collect(B,P)) ==> c : list(B) *)
bind_thm ("list_CollectD", (Collect_subset RS list_mono RS subsetD));

Goal "l: list({x:A. h(x)=j(x)}) ==> map(h,l) = map(j,l)";
by (list_ind_tac "l" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "map_list_Collect";

(*** theorems about length ***)

Goal "xs: list(A) ==> length(map(h,xs)) = length(xs)";
by (list_ind_tac "xs" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "length_map";

Goal "xs: list(A) ==> length(xs@ys) = length(xs) #+ length(ys)";
by (list_ind_tac "xs" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "length_app";

(* [| m: nat; n: nat |] ==> m #+ succ(n) = succ(n) #+ m 
   Used for rewriting below*)
val add_commute_succ = nat_succI RSN (2,add_commute);

Goal "xs: list(A) ==> length(rev(xs)) = length(xs)";
by (list_ind_tac "xs" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [length_app, add_commute_succ])));
qed "length_rev";

Goal "ls: list(list(A)) ==> length(flat(ls)) = list_add(map(length,ls))";
by (list_ind_tac "ls" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [length_app])));
qed "length_flat";

(** Length and drop **)

(*Lemma for the inductive step of drop_length*)
Goal "xs: list(A) ==> \
\          ALL x.  EX z zs. drop(length(xs), Cons(x,xs)) = Cons(z,zs)";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "drop_length_Cons_lemma";
bind_thm ("drop_length_Cons", (drop_length_Cons_lemma RS spec));

Goal "l: list(A) ==> ALL i: length(l).  EX z zs. drop(i,l) = Cons(z,zs)";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
by (rtac conjI 1);
by (etac drop_length_Cons 1);
by (rtac ballI 1);
by (rtac natE 1);
by (etac ([asm_rl, length_type, Ord_nat] MRS Ord_trans) 1);
by (assume_tac 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (blast_tac (claset() addIs [succ_in_naturalD, length_type])));
qed "drop_length_lemma";
bind_thm ("drop_length", (drop_length_lemma RS bspec));


(*** theorems about app ***)

Goal "xs: list(A) ==> xs@Nil=xs";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "app_right_Nil";

Goal "xs: list(A) ==> (xs@ys)@zs = xs@(ys@zs)";
by (list_ind_tac "xs" [] 1);
by (ALLGOALS Asm_simp_tac);
qed "app_assoc";

Goal "ls: list(list(A)) ==> flat(ls@ms) = flat(ls)@flat(ms)";
by (list_ind_tac "ls" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [app_assoc])));
qed "flat_app_distrib";

(*** theorems about rev ***)

Goal "l: list(A) ==> rev(map(h,l)) = map(h,rev(l))";
by (list_ind_tac "l" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [map_app_distrib])));
qed "rev_map_distrib";

(*Simplifier needs the premises as assumptions because rewriting will not
  instantiate the variable ?A in the rules' typing conditions; note that
  rev_type does not instantiate ?A.  Only the premises do.
*)
Goal "[| xs: list(A);  ys: list(A) |] ==> rev(xs@ys) = rev(ys)@rev(xs)";
by (etac list.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [app_right_Nil,app_assoc])));
qed "rev_app_distrib";

Goal "l: list(A) ==> rev(rev(l))=l";
by (list_ind_tac "l" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [rev_app_distrib])));
qed "rev_rev_ident";

Goal "ls: list(list(A)) ==> rev(flat(ls)) = flat(map(rev,rev(ls)))";
by (list_ind_tac "ls" [] 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps 
       [map_app_distrib, flat_app_distrib, rev_app_distrib, app_right_Nil])));
qed "rev_flat";


(*** theorems about list_add ***)

Goal "[| xs: list(nat);  ys: list(nat) |] ==> \
\    list_add(xs@ys) = list_add(ys) #+ list_add(xs)";
by (list_ind_tac "xs" [] 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [add_0_right, add_assoc RS sym])));
by (rtac (add_commute RS subst_context) 1);
by (REPEAT (ares_tac [refl, list_add_type] 1));
qed "list_add_app";

Goal "l: list(nat) ==> list_add(rev(l)) = list_add(l)";
by (list_ind_tac "l" [] 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [list_add_app, add_0_right])));
qed "list_add_rev";

Goal "ls: list(list(nat)) ==> list_add(flat(ls)) = list_add(map(list_add,ls))";
by (list_ind_tac "ls" [] 1);
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

