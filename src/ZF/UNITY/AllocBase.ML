(*  Title:      ZF/UNITY/AllocBase.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Common declarations for Chandy and Charpentier's Allocator
*)

(*????remove from Union.ML:AddSEs [not_emptyE];*)
Delrules [not_emptyE];

Goal "0 < Nclients & 0 < NbT";
by (cut_facts_tac [Nclients_pos, NbT_pos] 1);
by (auto_tac (claset() addIs [Ord_0_lt], simpset()));
qed "Nclients_NbT_gt_0";
Addsimps [Nclients_NbT_gt_0 RS conjunct1, Nclients_NbT_gt_0 RS conjunct2];

Goal "Nclients ~= 0 & NbT ~= 0";
by (cut_facts_tac [Nclients_pos, NbT_pos] 1);
by Auto_tac;
qed "Nclients_NbT_not_0";
Addsimps [Nclients_NbT_not_0 RS conjunct1, Nclients_NbT_not_0  RS conjunct2];

Goal "Nclients:nat & NbT:nat";
by (cut_facts_tac [Nclients_pos, NbT_pos] 1);
by Auto_tac;
qed "Nclients_NbT_type";
Addsimps [Nclients_NbT_type RS conjunct1, Nclients_NbT_type RS conjunct2];
AddTCs [Nclients_NbT_type RS conjunct1, Nclients_NbT_type RS conjunct2];

Goal "b:Inter(RepFun(Nclients, B)) <-> (ALL x:Nclients. b:B(x))";
by (auto_tac (claset(), simpset() addsimps [INT_iff]));
by (res_inst_tac [("x", "0")] exI 1);
by (rtac ltD 1); 
by Auto_tac; 
qed "INT_Nclient_iff";
AddIffs [INT_Nclient_iff];

val succ_def = thm "succ_def";

Goal "n:nat ==> \
\     (ALL i:nat. i<n --> f(i) $<= g(i)) --> \
\     setsum(f, n) $<= setsum(g,n)";
by (induct_tac "n" 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [])));
by (subgoal_tac "succ(x)=cons(x, x) & Finite(x) & x~:x" 1);
by (Clarify_tac 1);
by (Asm_simp_tac 1);
by (subgoal_tac "ALL i:nat. i<x--> f(i) $<= g(i)" 1);
by (resolve_tac [zadd_zle_mono] 1);
by (thin_tac "succ(x)=cons(x,x)" 1);
by (ALLGOALS(Asm_simp_tac));
by (thin_tac "succ(x)=cons(x, x)" 1);
by (Clarify_tac 1);
by (dtac leI 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [nat_into_Finite,
                                      mem_not_refl, succ_def]) 1);
qed_spec_mp "setsum_fun_mono";

Goal "l:list(A) ==> tokens(l):nat";
by (etac list.induct 1);
by Auto_tac;
qed "tokens_type";
AddTCs [tokens_type];
Addsimps [tokens_type];

Goal "xs:list(A) ==> ALL ys:list(A). <xs, ys>:prefix(A) \
\  --> tokens(xs) le tokens(ys)";
by (induct_tac "xs" 1);
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD], 
              simpset() addsimps [prefix_def]));
qed_spec_mp "tokens_mono_aux";

Goal "[| <xs, ys>:prefix(A); xs:list(A); ys:list(A) |] ==> \
\     tokens(xs) le tokens(ys)";
by (blast_tac (claset() addIs [tokens_mono_aux]) 1);
qed "tokens_mono";

Goalw [mono1_def] "mono1(list(A), prefix(A), nat, Le ,tokens)";
by (auto_tac (claset() addIs [tokens_mono],
             simpset() addsimps [Le_def]));
qed "mono_tokens";
Addsimps [mono_tokens];
AddIs [mono_tokens];

Goal 
"[| xs:list(A); ys:list(A) |] ==> tokens(xs@ys) = tokens(xs) #+ tokens(ys)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "tokens_append";
Addsimps [tokens_append];

Goal "l:list(A) ==> ALL n:nat. length(take(n, l))=min(n, length(l))";
by (induct_tac "l" 1);
by Safe_tac;
by (ALLGOALS(Asm_simp_tac));
by (etac natE 1);
by (ALLGOALS(Asm_simp_tac));
qed "length_take";

(** bag_of **)

Goal "l:list(A) ==>bag_of(l):Mult(A)";
by (induct_tac "l" 1);
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "bag_of_type";
AddTCs [bag_of_type];
Addsimps [bag_of_type];

Goal "l:list(A) ==> multiset(bag_of(l)) & mset_of(bag_of(l))<=A";
by (dtac bag_of_type 1);
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "bag_of_multiset";

Goal "[| xs:list(A); ys:list(A)|] ==> bag_of(xs@ys) = bag_of(xs) +# bag_of(ys)";
by (induct_tac "xs" 1);
by (auto_tac (claset(), simpset() 
       addsimps [bag_of_multiset, munion_assoc]));
qed "bag_of_append";
Addsimps [bag_of_append];

Goal "xs:list(A) ==> ALL ys:list(A). <xs, ys>:prefix(A) \
\  --> <bag_of(xs), bag_of(ys)>:MultLe(A, r)";
by (induct_tac "xs" 1);
by (ALLGOALS(Clarify_tac));
by (ftac bag_of_multiset 1);
by (forw_inst_tac [("l", "ys")] bag_of_multiset 2);
by (auto_tac (claset() addIs [empty_le_MultLe], 
              simpset() addsimps [prefix_def]));
by (rtac munion_mono 1);
by (force_tac (claset(), simpset() addsimps 
               [MultLe_def, Mult_iff_multiset]) 1);
by (blast_tac (claset() addDs [gen_prefix.dom_subset RS subsetD]) 1);
qed_spec_mp "bag_of_mono_aux";

Goal "[|  <xs, ys>:prefix(A); xs:list(A); ys:list(A) |] ==> \
\  <bag_of(xs), bag_of(ys)>:MultLe(A, r)";
by (blast_tac (claset() addIs [bag_of_mono_aux]) 1);
qed "bag_of_mono";
AddIs [bag_of_mono];

Goalw [mono1_def]
 "mono1(list(A), prefix(A), Mult(A), MultLe(A,r), bag_of)";
by (auto_tac (claset(), simpset() addsimps [bag_of_type]));
qed "mono_bag_of";
Addsimps [mono_bag_of];


(** msetsum **)

bind_thm("nat_into_Fin", eqpoll_refl RSN (2,thm"Fin_lemma"));

Goal "l : list(A) ==> C Int length(l) : Fin(length(l))";
by (dtac length_type 1); 
by (rtac Fin_subset 1); 
by (rtac Int_lower2 1);
by (etac nat_into_Fin 1); 
qed "list_Int_length_Fin";



Goal "[|xs \\<in> list(A); k \\<in> C \\<inter> length(xs)|] ==> k < length(xs)"; 
by (asm_full_simp_tac (simpset() addsimps [ltI]) 1); 
qed "mem_Int_imp_lt_length";


Goal "[|C \\<subseteq> nat; x \\<in> A; xs \\<in> list(A)|]  \
\ ==>  msetsum(\\<lambda>i. {#nth(i, xs @ [x])#}, C \\<inter> succ(length(xs)), A) = \
\      (if length(xs) \\<in> C then \
\         {#x#} +# msetsum(\\<lambda>x. {#nth(x, xs)#}, C \\<inter> length(xs), A) \
\       else msetsum(\\<lambda>x. {#nth(x, xs)#}, C \\<inter> length(xs), A))"; 
by (asm_full_simp_tac (simpset() addsimps [subsetD, nth_append, lt_not_refl, mem_Int_imp_lt_length] addcongs [msetsum_cong]) 1); 
by (asm_full_simp_tac (simpset() addsimps [Int_succ_right]) 1);
by (asm_full_simp_tac (simpset() addsimps [lt_not_refl, mem_Int_imp_lt_length] addcongs [msetsum_cong]) 1); 
by (Clarify_tac 1);
by (stac msetsum_cons 1);
by (rtac succI1 3);  
by (blast_tac (claset() addIs [list_Int_length_Fin, subset_succI RS Fin_mono RS subsetD]) 1); 
by (asm_full_simp_tac (simpset() addsimps [mem_not_refl]) 1); 
by (asm_full_simp_tac (simpset() addsimps [nth_type, lt_not_refl]) 1); 
by (blast_tac (claset() addIs [nat_into_Ord, ltI, length_type]) 1);
by (asm_full_simp_tac (simpset() addsimps [lt_not_refl, mem_Int_imp_lt_length] addcongs [msetsum_cong]) 1); 
qed "bag_of_sublist_lemma";

Goal "l:list(A) ==> \
\ C <= nat ==> \
\ bag_of(sublist(l, C)) = \
\     msetsum(%i. {#nth(i, l)#}, C Int length(l), A)";
by (etac list_append_induct  1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [sublist_append, nth_append, 
          bag_of_sublist_lemma, munion_commute, bag_of_sublist_lemma, 
          msetsum_multiset, munion_0]) 1);  
qed "bag_of_sublist_lemma2";


Goal "l \\<in> list(A) ==> nat \\<inter> length(l) = length(l)";
by (rtac Int_absorb1 1);
by (rtac OrdmemD 1);  
by Auto_tac; 
qed "nat_Int_length_eq";

(*eliminating the assumption C<=nat*)
Goal "l:list(A) ==> \
\ bag_of(sublist(l, C)) = msetsum(%i. {#nth(i, l)#}, C Int length(l), A)";
by (subgoal_tac
      " bag_of(sublist(l, C Int nat)) = \
\     msetsum(%i. {#nth(i, l)#}, C Int length(l), A)" 1);
by (asm_full_simp_tac (simpset() addsimps [sublist_Int_eq]) 1); 
by (asm_full_simp_tac (simpset() addsimps [bag_of_sublist_lemma2, Int_lower2, Int_assoc, nat_Int_length_eq]) 1); 
qed "bag_of_sublist";

Goal 
"l:list(A) ==> \
\ bag_of(sublist(l, B Un C)) +# bag_of(sublist(l, B Int C)) = \
\     bag_of(sublist(l, B)) +# bag_of(sublist(l, C))";
by (subgoal_tac
      "B Int C Int length(l) = \
\      (B Int length(l)) Int (C Int length(l))" 1);
by (blast_tac (claset() addIs []) 2);
by (asm_simp_tac (simpset() addsimps [bag_of_sublist, 
                                      Int_Un_distrib2, msetsum_Un_Int]) 1); 
by (resolve_tac [msetsum_Un_Int] 1);
by (REPEAT (etac list_Int_length_Fin 1)); 
 by (asm_full_simp_tac (simpset() addsimps [ltI, nth_type]) 1); 
qed "bag_of_sublist_Un_Int";


Goal "[| l:list(A); B Int C = 0  |]\
\     ==> bag_of(sublist(l, B Un C)) = \
\         bag_of(sublist(l, B)) +# bag_of(sublist(l, C))"; 
by (asm_simp_tac (simpset() addsimps [bag_of_sublist_Un_Int RS sym, 
                  sublist_type,  bag_of_multiset]) 1);
qed "bag_of_sublist_Un_disjoint";

Goal "[| Finite(I); ALL i:I. ALL j:I. i~=j --> A(i) Int A(j) = 0; \
\ l:list(B) |] \
\     ==> bag_of(sublist(l, UN i:I. A(i))) =  \
\         (msetsum(%i. bag_of(sublist(l, A(i))), I, B)) ";  
by (asm_simp_tac (simpset() delsimps UN_simps addsimps (UN_simps RL [sym])
                            addsimps [bag_of_sublist]) 1);
by (stac (inst "A" "length(l)" msetsum_UN_disjoint) 1);
by (dresolve_tac [Finite_into_Fin] 1);
by (assume_tac 1);
by (Force_tac 3);
by (auto_tac (claset() addSIs [Fin_IntI2, Finite_into_Fin], 
              simpset() addsimps [ltI, nth_type, length_type, nat_into_Finite]));
qed_spec_mp "bag_of_sublist_UN_disjoint";


Goalw [part_ord_def, Lt_def, irrefl_def, trans_on_def]
  "part_ord(nat, Lt)";
by (auto_tac (claset() addIs [lt_trans], simpset()));
qed "part_ord_Lt";
Addsimps [part_ord_Lt];


(** all_distinct **)

Goalw [all_distinct_def] "all_distinct(Nil)";
by Auto_tac;
qed "all_distinct_Nil";

Goalw [all_distinct_def] 
"all_distinct(Cons(a, l)) <-> \
\ (a:set_of_list(l) --> False) & (a ~: set_of_list(l) --> all_distinct(l))";
by (auto_tac (claset() addEs [list.elim], simpset()));
qed "all_distinct_Cons";
Addsimps [all_distinct_Nil, all_distinct_Cons];

(** state_of **)
Goalw [state_of_def] "s:state ==> state_of(s)=s";
by Auto_tac;
qed "state_of_state";
Addsimps [state_of_state];


Goalw [state_of_def] "state_of(state_of(s))=state_of(s)";
by Auto_tac;
qed "state_of_idem";
Addsimps [state_of_idem];


Goalw [state_of_def] "state_of(s):state";
by Auto_tac;
qed "state_of_type";
Addsimps [state_of_type];
AddTCs [state_of_type];

Goalw [lift_def] "lift(x, s)=s`x";
by (Simp_tac 1);
qed "lift_apply";
Addsimps [lift_apply];

(** Used in ClientImp **)

Goalw [Increasing_def]
"Increasing(A, r, %s. f(state_of(s))) = \
\ Increasing(A, r, f)";
by Auto_tac;
qed "gen_Increains_state_of_eq";
bind_thm("Increasing_state_ofD1", 
gen_Increains_state_of_eq RS equalityD1 RS subsetD);
bind_thm("Increasing_state_ofD2", 
gen_Increains_state_of_eq RS equalityD2 RS subsetD);

Goalw [Follows_def, Increasing_def] 
"Follows(A, r, %s. f(state_of(s)), %s. g(state_of(s))) =  \
\ Follows(A, r, f, g)";
by Auto_tac;
qed "Follows_state_of_eq";
bind_thm("Follows_state_ofD1", Follows_state_of_eq RS equalityD1 RS subsetD);
bind_thm("Follows_state_ofD2", Follows_state_of_eq RS equalityD2 RS subsetD);

(*Splits up conjunctions & intersections: like CONJUNCTS in the HOL system*)
fun list_of_Int th = 
    (list_of_Int (th RS conjunct1) @ list_of_Int (th RS conjunct2))
    handle THM _ => (list_of_Int (th RS IntD1) @ list_of_Int (th RS IntD2))
    handle THM _ => (list_of_Int (th RS InterD))
    handle THM _ => (list_of_Int (th RS bspec))
    handle THM _ => [th];

(*Used just once, for Alloc_Increasing*)

fun normalize th = 
     normalize (th RS spec
                handle THM _ => th RS bspec
                handle THM _ => th RS (guarantees_INT_right_iff RS iffD1))
     handle THM _ => th;

Goal "n:nat ==> nat_list_inj(n):list(nat)";
by (induct_tac "n" 1);
by Auto_tac;
qed "nat_list_inj_type";

Goal "n:nat ==> length(nat_list_inj(n)) = n";
by (induct_tac "n" 1);
by Auto_tac;
qed "length_nat_list_inj";

Goalw [nat_var_inj_def]
  "(lam x:nat. nat_var_inj(x)):inj(nat, var)";
by (res_inst_tac [("d", "var_inj")] lam_injective 1); 
by (asm_simp_tac (simpset() addsimps [length_nat_list_inj]) 2);
by (auto_tac (claset(), simpset() addsimps var.intrs@[nat_list_inj_type]));
qed "var_infinite_lemma";

Goalw [lepoll_def] "nat lepoll var";
by (res_inst_tac [("x", "(lam x:nat. nat_var_inj(x))")] exI 1);
by (rtac var_infinite_lemma 1);
qed "nat_lepoll_var";

Goalw [Finite_def] "~Finite(var)";
by Auto_tac;
by (dtac eqpoll_imp_lepoll 1);
by (cut_facts_tac [nat_lepoll_var] 1);
by (subgoal_tac "nat lepoll x" 1);
by (blast_tac (claset() addIs [lepoll_trans]) 2);
by (dres_inst_tac [("i", "x"), ("A", "nat")] lepoll_cardinal_le 1);
by Auto_tac;
by (subgoal_tac "Card(nat)" 1);
by (rewrite_goal_tac [Card_def] 1);
by (dtac sym 1);
by Auto_tac;
by (dtac le_imp_subset 1);
by (dtac subsetD 1);
by (auto_tac (claset(), simpset() addsimps [Card_nat]));
by (blast_tac (claset() addEs [mem_irrefl]) 1);
qed "var_not_Finite";

Goal "~Finite(A) ==> EX x. x:A";
by (etac swap 1);
by Auto_tac;
by (subgoal_tac "A=0" 1);
by (auto_tac (claset(), simpset() addsimps [Finite_0]));
qed "not_Finite_imp_exist";

Goal "Finite(A) ==> b:(Inter(RepFun(var-A, B))) <-> (ALL x:var-A. b:B(x))";
by (subgoal_tac "EX x. x:var-A" 1);
by Auto_tac;
by (subgoal_tac "~Finite(var-A)" 1);
by (dtac not_Finite_imp_exist 1);
by Auto_tac;
by (cut_facts_tac [var_not_Finite] 1);
by (etac swap  1);
by (res_inst_tac [("B", "A")] Diff_Finite 1);
by Auto_tac;
qed "Inter_Diff_var_iff";

Goal "[| b:Inter(RepFun(var-A, B)); Finite(A); x:var-A |] ==> b:B(x)";
by (rotate_tac 1 1);
by (asm_full_simp_tac (simpset() addsimps [Inter_Diff_var_iff]) 1);
qed "Inter_var_DiffD";

(* [| Finite(A); (ALL x:var-A. b:B(x)) |] ==> b:Inter(RepFun(var-A, B)) *)
bind_thm("Inter_var_DiffI", Inter_Diff_var_iff RS iffD2);

AddSIs [Inter_var_DiffI];
Addsimps [Finite_0, Finite_cons];

Goal "Acts(F)<= A Int Pow(state*state)  <-> Acts(F)<=A";
by (cut_facts_tac [inst "F" "F" Acts_type] 1);
by Auto_tac;
qed "Acts_subset_Int_Pow_simp";
Addsimps [Acts_subset_Int_Pow_simp];

Goal "cons(x, A Int B) = cons(x, A) Int cons(x, B)";
by Auto_tac;
qed "cons_Int_distrib";


(* Currently not used, but of potential interest *)
Goal 
"[| Finite(A); ALL x:A. g(x):nat |] ==> \
\ setsum(%x. $#(g(x)), A) = $# nsetsum(%x. g(x), A)";
by (etac Finite_induct 1);
by (auto_tac (claset(), simpset() addsimps [int_of_add]));
qed "setsum_nsetsum_eq";

Goal 
"[| A=B;  ALL x:A. f(x)=g(x);  ALL x:A. g(x):nat; \
\     Finite(A) |]  ==> nsetsum(f, A) = nsetsum(g, B)";
by (subgoal_tac "$# nsetsum(f, A) = $# nsetsum(g, B)" 1);
by (rtac trans 2);
by (rtac setsum_nsetsum_eq 3);
by (rtac trans 2);
by (rtac (setsum_nsetsum_eq RS sym) 2);
by Auto_tac;
by (rtac setsum_cong 1);
by Auto_tac;
qed "nsetsum_cong";  




