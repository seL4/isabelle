(*  Title:      ZF/UNITY/ListPlus.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

More about lists 

*)

(*** more theorems about lists ***)

(** td and tl **)

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

Goal "[| xs:list(A); ys:list(A); zs:list(A) |] ==> \
\  length(ys)=length(zs) --> (xs@ys=zs <-> (xs=Nil & ys=zs))";
by (etac list.induct 1);
by (auto_tac (claset(), simpset() addsimps [length_app, length_type]));
qed_spec_mp "append_left_is_Nil_iff";
Addsimps [append_left_is_Nil_iff];

Goal "[| xs:list(A); ys:list(A); zs:list(A) |] ==> \
\  length(ys)=length(zs) --> (zs=ys@xs <-> (xs=Nil & ys=zs))";
by (etac list.induct 1);
by (auto_tac (claset(), simpset() addsimps [length_app, length_type]));
qed_spec_mp "append_left_is_Nil_iff2";
Addsimps [append_left_is_Nil_iff2];

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
by (asm_full_simp_tac (simpset() addsimps [length_type, length_app]) 1);
by (eres_inst_tac [("a", "ys")] list.elim 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "Cons(a, l) @ us =vs" 1);
by (dtac (rotate_prems 4 (append_left_is_Nil_iff RS iffD1)) 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [length_type])));
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

(* Can also be proved from append_eq_append_iff2 
   if we add two more hypotheses x:A and y:A *)
Goal "xs:list(A) ==> ALL ys:list(A). xs@[x] = ys@[y] <-> (xs = ys & x=y)";
by (etac list.induct 1);
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(eres_inst_tac [("a", "ys")] list.elim));
by Auto_tac;
qed_spec_mp "append1_eq_iff";
Addsimps [append1_eq_iff];

Goal "[| xs:list(A); ys:list(A) |] ==> (xs@ys = ys) <-> (xs=Nil)";
by (Asm_simp_tac 1);
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
by (ALLGOALS(Clarify_tac));
by (etac list.elim 2);
by Auto_tac;
qed_spec_mp "length_drop";
Addsimps [length_drop];

Goal "n:nat ==> ALL xs:list(A). length(xs) le n --> drop(n, xs)=Nil";
by (etac nat_induct 1);
by (ALLGOALS(Clarify_tac));
by (etac list.elim 2);
by Auto_tac;
qed_spec_mp "drop_all";
Addsimps [drop_all];

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
by (ALLGOALS(Clarify_tac));
by (etac list.elim 2);
by Auto_tac;
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

(** nth **)

Goalw [nth_def] "nth(0, Cons(a, l))= a";
by Auto_tac;
qed "nth_0";
AddIffs [nth_0];

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

Goal 
"xs:list(A) ==> ALL n:nat. \
\ nth(n, xs @ ys) = (if n < length(xs) then nth(n,xs) \
\                      else nth(n #- length(xs),ys))";
by (induct_tac "xs" 1);
by (Clarify_tac 2);
by (etac natE 2);
by (ALLGOALS(Asm_full_simp_tac));
qed_spec_mp "nth_append";

(* Other theorems about lists *)

Goal "xs:list(A) ==> (xs~=Nil) <-> (EX y:A. EX ys:list(A). xs=Cons(y,ys))";
by (induct_tac "xs" 1);
by Auto_tac;
qed "neq_Nil_iff";

Goalw [Ball_def]
 "k:nat ==> \
\ ALL xs:list(A). (ALL ys:list(A). k le length(xs) --> k le length(ys) -->  \
\     (ALL i:nat. i < k --> nth(i,xs)= nth(i,ys))--> take(k, xs) = take(k,ys))";
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
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [length_type,take_all])));
qed_spec_mp "take_equalityI";

(** More on lists **)

Goal
"n:nat ==> ALL i:nat. ALL xs:list(A). n #+ i le length(xs) \
\ --> nth(i, drop(n, xs)) = nth(n #+ i, xs)";
by (induct_tac "n" 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Clarify_tac 1);
by (case_tac "xb=Nil" 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [neq_Nil_iff])));
by (Clarify_tac 1);
by (auto_tac (claset() addSEs [ConsE], simpset()));
qed_spec_mp "nth_drop";




