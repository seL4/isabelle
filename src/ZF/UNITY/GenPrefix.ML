(*  Title:      ZF/UNITY/GenPrefix.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Charpentier's Generalized Prefix Relation
   <xs,ys>:gen_prefix(r)
     if ys = xs' @ zs where length(xs) = length(xs')
     and corresponding elements of xs, xs' are pairwise related by r

Based on Lex/Prefix
*)

Goalw [refl_def]
 "[| refl(A, r); x \\<in> A |] ==> <x,x>:r";
by Auto_tac;
qed "reflD";

(*** preliminary lemmas ***)

Goal "xs \\<in> list(A) ==> <[], xs> \\<in> gen_prefix(A, r)";
by (dtac (rotate_prems  1 gen_prefix.append) 1);
by (rtac gen_prefix.Nil 1);
by Auto_tac;
qed "Nil_gen_prefix";
Addsimps [Nil_gen_prefix];


Goal "<xs,ys> \\<in> gen_prefix(A, r) ==> length(xs) \\<le> length(ys)";
by (etac gen_prefix.induct 1);
by (subgoal_tac "ys \\<in> list(A)" 3);
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD]
                       addIs [le_trans], 
              simpset() addsimps [length_app]));
qed "gen_prefix_length_le";


Goal "[| <xs', ys'> \\<in> gen_prefix(A, r) |] \
\  ==> (\\<forall>x xs. x \\<in> A --> xs'= Cons(x,xs) --> \
\      (\\<exists>y ys. y \\<in> A & ys' = Cons(y,ys) &\
\      <x,y>:r & <xs, ys> \\<in> gen_prefix(A, r)))";
by (etac gen_prefix.induct 1);
by (force_tac (claset() addIs [gen_prefix.append],
               simpset()) 3);
by (REPEAT(Asm_simp_tac 1));
val lemma = result();

(*As usual converting it to an elimination rule is tiresome*)
val major::prems = 
Goal "[| <Cons(x,xs), zs> \\<in> gen_prefix(A, r); \
\   !!y ys. [|zs = Cons(y, ys); y \\<in> A; x \\<in> A; <x,y>:r; \
\     <xs,ys> \\<in> gen_prefix(A, r) |] ==> P \
\     |] ==> P";
by (cut_facts_tac [major] 1);
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (Clarify_tac 1);
by (etac ConsE 1);
by (cut_facts_tac [major RS lemma] 1);
by (Full_simp_tac 1);
by (dtac mp 1);
by (Asm_simp_tac 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (REPEAT (ares_tac prems 1));
qed "Cons_gen_prefixE";
AddSEs [Cons_gen_prefixE];

Goal 
"(<Cons(x,xs),Cons(y,ys)> \\<in> gen_prefix(A, r)) \
\ <-> (x \\<in> A & y \\<in> A & <x,y>:r & <xs,ys> \\<in> gen_prefix(A, r))";
by (auto_tac (claset() addIs [gen_prefix.prepend], simpset()));
qed"Cons_gen_prefix_Cons";
AddIffs [Cons_gen_prefix_Cons];

(** Monotonicity of gen_prefix **)

Goal "r<=s ==> gen_prefix(A, r) <= gen_prefix(A, s)";
by (Clarify_tac 1);
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (Clarify_tac 1);
by (etac rev_mp 1);
by (etac gen_prefix.induct 1);
by (auto_tac (claset() addIs 
         [gen_prefix.append], simpset()));
qed "gen_prefix_mono2";

Goal "A<=B ==>gen_prefix(A, r) <= gen_prefix(B, r)";
by (Clarify_tac 1);
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (Clarify_tac 1);
by (etac rev_mp 1);
by (eres_inst_tac [("P", "y \\<in> list(A)")] rev_mp 1);
by (eres_inst_tac [("P", "xa \\<in> list(A)")] rev_mp 1);
by (etac gen_prefix.induct 1);
by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (REPEAT(etac ConsE 1));
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD] 
                       addIs [gen_prefix.append, list_mono RS subsetD],
             simpset()));
qed "gen_prefix_mono1";

Goal "[| A <= B; r <= s |] ==> gen_prefix(A, r) <= gen_prefix(B, s)";
by (rtac subset_trans 1);
by (rtac gen_prefix_mono1 1);
by (rtac gen_prefix_mono2 2);
by Auto_tac;
qed "gen_prefix_mono";

(*** gen_prefix order ***)

(* reflexivity *)
Goalw [refl_def] "refl(A, r) ==> refl(list(A), gen_prefix(A, r))";
by Auto_tac;
by (induct_tac "x" 1);
by Auto_tac;
qed "refl_gen_prefix";
Addsimps [refl_gen_prefix RS reflD];

(* Transitivity *)
(* A lemma for proving gen_prefix_trans_comp *)

Goal "xs \\<in> list(A) ==> \
\  \\<forall>zs. <xs @ ys, zs> \\<in> gen_prefix(A, r) --> <xs, zs>: gen_prefix(A, r)";
by (etac list.induct 1);
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD], simpset()));
qed_spec_mp "append_gen_prefix";

(* Lemma proving transitivity and more*)

Goal "<x, y>: gen_prefix(A, r) ==> \
\  (\\<forall>z \\<in> list(A). <y,z> \\<in> gen_prefix(A, s)--><x, z> \\<in> gen_prefix(A, s O r))";
by (etac gen_prefix.induct 1);
by (auto_tac (claset() addEs [ConsE], simpset() addsimps [Nil_gen_prefix]));
by (subgoal_tac "ys \\<in> list(A)" 1);
by (blast_tac (claset() addDs [gen_prefix.dom_subset RS subsetD]) 2);
by (dres_inst_tac [("xs", "ys"), ("r", "s")] append_gen_prefix 1);
by Auto_tac;
qed_spec_mp "gen_prefix_trans_comp";

Goal "trans(r) ==> r O r <= r";
by (auto_tac (claset() addDs [transD], simpset()));
qed "trans_comp_subset";

Goal "trans(r) ==> trans(gen_prefix(A,r))";
by (simp_tac (simpset() addsimps [trans_def]) 1);
by (Clarify_tac 1);
by (rtac (impOfSubs (trans_comp_subset RS gen_prefix_mono2)) 1);
 by (assume_tac 2);
by (rtac gen_prefix_trans_comp 1);
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD], simpset()));
qed_spec_mp "trans_gen_prefix";

Goal
 "trans(r) ==> trans[list(A)](gen_prefix(A, r))";
by (dres_inst_tac [("A", "A")] trans_gen_prefix 1);
by (rewrite_goal_tac [trans_def, trans_on_def] 1);
by (Blast_tac 1);
qed "trans_on_gen_prefix";

Goalw [prefix_def]
"[| <x,y> \\<in> prefix(A); <y, z> \\<in> gen_prefix(A, r); r<=A*A |] \
\ ==>  <x, z> \\<in> gen_prefix(A, r)";
by (res_inst_tac [("P", "%r. <x,z> \\<in> gen_prefix(A, r)")]
             (right_comp_id RS subst) 1);
by (REPEAT(blast_tac (claset() addDs [gen_prefix_trans_comp, 
                  gen_prefix.dom_subset RS subsetD]) 1));
qed_spec_mp "prefix_gen_prefix_trans";


Goalw [prefix_def]
"[| <x,y> \\<in> gen_prefix(A,r); <y, z> \\<in> prefix(A); r<=A*A |] \
\ ==>  <x, z> \\<in> gen_prefix(A, r)";
by (res_inst_tac [("P", "%r. <x,z> \\<in> gen_prefix(A, r)")] (left_comp_id RS subst) 1);
by (REPEAT(blast_tac (claset() addDs [gen_prefix_trans_comp, 
                                      gen_prefix.dom_subset RS subsetD]) 1));
qed_spec_mp "gen_prefix_prefix_trans";

(** Antisymmetry **)

Goal "n \\<in> nat ==> \\<forall>b \\<in> nat. n #+ b \\<le> n --> b = 0";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "nat_le_lemma";

Goal "antisym(r) ==> antisym(gen_prefix(A, r))";
by (simp_tac (simpset() addsimps [antisym_def]) 1);
by (rtac (impI RS allI RS allI) 1);
by (etac gen_prefix.induct 1);
by (full_simp_tac (simpset() addsimps [antisym_def]) 2);
by (Blast_tac 2);
by (Blast_tac 1);
(*append case is hardest*)
by (Clarify_tac 1);
by (subgoal_tac "length(zs) = 0" 1);
by (subgoal_tac "ys \\<in> list(A)" 1);
by (blast_tac (claset() addDs [gen_prefix.dom_subset RS subsetD]) 2);
by (dres_inst_tac [("psi", "<ys @ zs, xs> \\<in> gen_prefix(A,r)")] asm_rl 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "length(ys @ zs)  = length(ys) #+ length(zs) &ys \\<in> list(A)&xs \\<in> list(A)" 1);
by (blast_tac (claset() addIs [length_app] 
                        addDs [gen_prefix.dom_subset RS subsetD]) 2);
by (REPEAT (dtac gen_prefix_length_le 1));
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("j", "length(xs)")] le_trans 1);
by (Blast_tac 1);
by (auto_tac (claset() addIs [nat_le_lemma], simpset()));
qed_spec_mp "antisym_gen_prefix";

(*** recursion equations ***)

Goal "xs \\<in> list(A) ==> <xs, []> \\<in> gen_prefix(A,r) <-> (xs = [])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "gen_prefix_Nil";
Addsimps [gen_prefix_Nil];

Goalw [refl_def]
 "[| refl(A, r);  xs \\<in> list(A) |] ==> \
\   <xs@ys, xs@zs>: gen_prefix(A, r) <-> <ys,zs> \\<in> gen_prefix(A, r)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "same_gen_prefix_gen_prefix";
Addsimps [same_gen_prefix_gen_prefix];

Goal "[| xs \\<in> list(A); ys \\<in> list(A); y \\<in> A |] ==> \
\   <xs, Cons(y,ys)> : gen_prefix(A,r)  <-> \
\     (xs=[] | (\\<exists>z zs. xs=Cons(z,zs) & z \\<in> A & <z,y>:r & <zs,ys> \\<in> gen_prefix(A,r)))";
by (induct_tac "xs" 1);
by Auto_tac;
qed "gen_prefix_Cons";

Goal "[| refl(A,r);  <xs,ys> \\<in> gen_prefix(A, r); zs \\<in> list(A) |] \
\     ==>  <xs@zs, take(length(xs), ys) @ zs> : gen_prefix(A, r)";
by (etac gen_prefix.induct 1);
by (Asm_simp_tac 1);
by (ALLGOALS(forward_tac [gen_prefix.dom_subset RS subsetD]));
by Auto_tac;
by (ftac gen_prefix_length_le 1);
by (subgoal_tac "take(length(xs), ys) \\<in> list(A)" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps 
         [diff_is_0_iff RS iffD2, take_type ])));
qed "gen_prefix_take_append";

Goal "[| refl(A, r);  <xs,ys> \\<in> gen_prefix(A,r);   \
\        length(xs) = length(ys); zs \\<in> list(A) |] \
\     ==>  <xs@zs, ys @ zs> : gen_prefix(A, r)";
by (dres_inst_tac [("zs", "zs")]  gen_prefix_take_append 1);
by (REPEAT(assume_tac 1));
by (subgoal_tac "take(length(xs), ys)=ys" 1);
by (auto_tac (claset() addSIs [take_all] 
                       addDs [gen_prefix.dom_subset RS subsetD], 
              simpset()));
qed "gen_prefix_append_both";

(*NOT suitable for rewriting since [y] has the form y#ys*)
Goal "xs \\<in> list(A) ==> xs @ Cons(y, ys) = (xs @ [y]) @ ys";
by (auto_tac (claset(), simpset() addsimps [app_assoc]));
qed "append_cons_conv";

Goal "[| <xs,ys> \\<in> gen_prefix(A, r);  refl(A, r) |] \
\     ==> length(xs) < length(ys) --> \
\         <xs @ [nth(length(xs), ys)], ys> \\<in> gen_prefix(A, r)";
by (etac gen_prefix.induct 1);
by (Blast_tac 1);
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (Clarify_tac 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [length_type])));
(* Append case is hardest *)
by (forward_tac [gen_prefix_length_le RS (le_iff RS iffD1) ] 1);
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (Clarify_tac 1);
by (subgoal_tac "length(xs):nat&length(ys):nat &length(zs):nat" 1);
by (blast_tac (claset() addIs [length_type]) 2);
by (Clarify_tac 1);
by (ALLGOALS (asm_full_simp_tac (simpset() 
            addsimps [nth_append, length_type, length_app])));
by (Clarify_tac 1);
by (rtac conjI 1);
by (blast_tac (claset() addIs [gen_prefix.append]) 1);
by (thin_tac "length(xs) < length(ys) -->?u" 1);
by (eres_inst_tac [("a","zs")] list.elim 1);
by Auto_tac;  
by (res_inst_tac [("P1", "%x. <?u(x), ?v>:?w")] (nat_diff_split RS iffD2) 1);
by Auto_tac;
by (stac append_cons_conv 1);
by (rtac gen_prefix.append 2);
by (auto_tac (claset() addEs [ConsE],
              simpset() addsimps [gen_prefix_append_both]));
val append_one_gen_prefix_lemma = result() RS mp;

Goal "[| <xs,ys>: gen_prefix(A, r);  length(xs) < length(ys);  refl(A, r) |] \
\     ==> <xs @ [nth(length(xs), ys)], ys> \\<in> gen_prefix(A, r)";
by (blast_tac (claset() addIs [append_one_gen_prefix_lemma]) 1);
qed "append_one_gen_prefix";


(** Proving the equivalence with Charpentier's definition **)

Goal "xs \\<in> list(A) ==>  \
\ \\<forall>ys \\<in> list(A). \\<forall>i \\<in> nat. i < length(xs) \
\         --> <xs, ys>: gen_prefix(A, r) --> <nth(i, xs), nth(i, ys)>:r";
by (induct_tac "xs" 1);
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(Asm_full_simp_tac));
by (etac natE 1);
by (ALLGOALS(Asm_full_simp_tac));
qed_spec_mp "gen_prefix_imp_nth_lemma";

Goal "[| <xs,ys> \\<in> gen_prefix(A,r); i < length(xs)|] \
\     ==> <nth(i, xs), nth(i, ys)>:r";
by (cut_inst_tac [("A","A")] gen_prefix.dom_subset 1); 
by (rtac gen_prefix_imp_nth_lemma 1);
by (auto_tac (claset(), simpset() addsimps [lt_nat_in_nat]));  
qed "gen_prefix_imp_nth";

Goal "xs \\<in> list(A) ==> \
\ \\<forall>ys \\<in> list(A). length(xs) \\<le> length(ys)  \
\     --> (\\<forall>i. i < length(xs) --> <nth(i, xs), nth(i,ys)>:r)  \
\     --> <xs, ys> \\<in> gen_prefix(A, r)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac); 
by (Clarify_tac 1);
by (eres_inst_tac [("a","ys")] list.elim 1);
by (asm_full_simp_tac (simpset() addsimps []) 1);  
by (force_tac (claset() addSIs [nat_0_le], simpset() addsimps [lt_nat_in_nat]) 1); 
qed_spec_mp "nth_imp_gen_prefix";

Goal "(<xs,ys> : gen_prefix(A,r)) <-> \
\     (xs \\<in> list(A) & ys \\<in> list(A) & length(xs) \\<le> length(ys) & \
\     (\\<forall>i. i < length(xs) --> <nth(i,xs), nth(i, ys)>: r))";
by (rtac iffI 1);
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (ftac gen_prefix_length_le 1);
by (ALLGOALS(Clarify_tac));
by (rtac nth_imp_gen_prefix 2);
by (dtac gen_prefix_imp_nth 1);
by (auto_tac (claset(), simpset() addsimps [lt_nat_in_nat])); 
qed "gen_prefix_iff_nth";

(** prefix is a partial order: **)

Goalw [prefix_def] 
   "refl(list(A), prefix(A))";
by (rtac refl_gen_prefix 1);
by (auto_tac (claset(), simpset() addsimps [refl_def]));
qed "refl_prefix";
Addsimps [refl_prefix RS reflD];

Goalw [prefix_def] "trans(prefix(A))";
by (rtac trans_gen_prefix 1);
by (auto_tac (claset(), simpset() addsimps [trans_def]));
qed "trans_prefix";

bind_thm("prefix_trans", trans_prefix RS transD);

Goalw [prefix_def] "trans[list(A)](prefix(A))";
by (rtac trans_on_gen_prefix 1);
by (auto_tac (claset(), simpset() addsimps [trans_def]));
qed "trans_on_prefix";

bind_thm("prefix_trans_on", trans_on_prefix RS trans_onD);

(* Monotonicity of "set" operator WRT prefix *)

Goalw [prefix_def] 
"<xs,ys> \\<in> prefix(A) ==> set_of_list(xs) <= set_of_list(ys)";
by (etac gen_prefix.induct 1);
by (subgoal_tac "xs \\<in> list(A)&ys \\<in> list(A)" 3);
by (blast_tac (claset() addDs [gen_prefix.dom_subset RS subsetD]) 4);
by (auto_tac (claset(), simpset() addsimps [set_of_list_append]));
qed "set_of_list_prefix_mono";  

(** recursion equations **)

Goalw [prefix_def] "xs \\<in> list(A) ==> <[],xs> \\<in> prefix(A)";
by (asm_simp_tac (simpset() addsimps [Nil_gen_prefix]) 1);
qed "Nil_prefix";
Addsimps[Nil_prefix];


Goalw [prefix_def] "<xs, []> \\<in> prefix(A) <-> (xs = [])";
by Auto_tac;
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (dres_inst_tac [("psi", "<xs, []> \\<in> gen_prefix(A, id(A))")] asm_rl 1);
by (asm_full_simp_tac (simpset() addsimps [gen_prefix_Nil]) 1);
qed "prefix_Nil";
AddIffs [prefix_Nil];

Goalw [prefix_def] 
"<Cons(x,xs), Cons(y,ys)> \\<in> prefix(A) <-> (x=y & <xs,ys> \\<in> prefix(A) & y \\<in> A)";
by Auto_tac;
qed"Cons_prefix_Cons";
AddIffs [Cons_prefix_Cons];

Goalw [prefix_def] 
"xs \\<in> list(A)==> <xs@ys,xs@zs> \\<in> prefix(A) <-> (<ys,zs> \\<in> prefix(A))";
by (subgoal_tac "refl(A,id(A))" 1);
by (Asm_simp_tac 1);
by (auto_tac (claset(), simpset() addsimps[refl_def]));
qed "same_prefix_prefix";
Addsimps [same_prefix_prefix];

Goal "xs \\<in> list(A) ==> <xs@ys,xs> \\<in> prefix(A) <-> (<ys,[]> \\<in> prefix(A))";
by (res_inst_tac [("P", "%x. <?u, x>:?v <-> ?w(x)")] (app_right_Nil RS subst) 1);
by (rtac same_prefix_prefix 2);
by Auto_tac;
qed "same_prefix_prefix_Nil";
Addsimps [same_prefix_prefix_Nil];

Goalw [prefix_def] 
"[| <xs,ys> \\<in> prefix(A); zs \\<in> list(A) |] ==> <xs,ys@zs> \\<in> prefix(A)";
by (etac gen_prefix.append 1);
by (assume_tac 1);
qed "prefix_appendI";
Addsimps [prefix_appendI];

Goalw [prefix_def] 
"[| xs \\<in> list(A); ys \\<in> list(A); y \\<in> A |] ==> \
\ <xs,Cons(y,ys)> \\<in> prefix(A) <-> \
\ (xs=[] | (\\<exists>zs. xs=Cons(y,zs) & <zs,ys> \\<in> prefix(A)))";
by (auto_tac (claset(), simpset() addsimps [gen_prefix_Cons]));
qed "prefix_Cons";

Goalw [prefix_def]
  "[| <xs,ys> \\<in> prefix(A); length(xs) < length(ys) |] \
\ ==> <xs @ [nth(length(xs),ys)], ys> \\<in> prefix(A)";
by (subgoal_tac "refl(A, id(A))" 1);
by (asm_simp_tac (simpset() addsimps [append_one_gen_prefix]) 1);
by (auto_tac (claset(), simpset() addsimps [refl_def]));
qed "append_one_prefix";

Goalw [prefix_def] 
"<xs,ys> \\<in> prefix(A) ==> length(xs) \\<le> length(ys)";
by (blast_tac (claset() addDs [gen_prefix_length_le]) 1);
qed "prefix_length_le";

Goalw [prefix_def] 
"<xs,ys> \\<in> prefix(A) ==> xs~=ys --> length(xs) < length(ys)";
by (etac gen_prefix.induct 1);
by (Clarify_tac 1);
by (ALLGOALS(subgoal_tac "ys \\<in> list(A)&xs \\<in> list(A)"));
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD], 
             simpset() addsimps [length_app, length_type]));
by (subgoal_tac "length(zs)=0" 1);
by (dtac not_lt_imp_le 2);
by (res_inst_tac [("j", "length(ys)")] lt_trans2 5);
by Auto_tac;
val lemma = result();

Goalw [prefix_def]
"prefix(A)<=list(A)*list(A)";
by (blast_tac (claset() addSIs [gen_prefix.dom_subset]) 1);
qed "prefix_type";

Goalw [strict_prefix_def]
"strict_prefix(A) <= list(A)*list(A)";
by (blast_tac (claset() addSIs [prefix_type RS subsetD]) 1);
qed "strict_prefix_type";

Goalw [strict_prefix_def]
 "<xs,ys>:strict_prefix(A) ==> length(xs) < length(ys)";
by (resolve_tac [lemma RS mp] 1);
by (auto_tac (claset() addDs [prefix_type RS subsetD], simpset()));
qed "strict_prefix_length_lt";

(*Equivalence to the definition used in Lex/Prefix.thy*)
Goalw [prefix_def]
    "<xs,zs> \\<in> prefix(A) <-> (\\<exists>ys \\<in> list(A). zs = xs@ys) & xs \\<in> list(A)";
by (auto_tac (claset(),
       simpset() addsimps [gen_prefix_iff_nth, lt_nat_in_nat,
                           nth_append, nth_type, app_type, length_app]));
by (subgoal_tac "drop(length(xs), zs) \\<in> list(A)" 1);
by (res_inst_tac [("x", "drop(length(xs), zs)")] bexI 1);
by (ALLGOALS(Clarify_tac));
by (asm_simp_tac (simpset() addsimps [length_type, drop_type]) 2);
by (rtac nth_equalityI 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps 
           [nth_append, app_type, drop_type, length_app, length_drop])));
by (rtac (nat_diff_split RS iffD2) 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Clarify_tac 1);
by (dres_inst_tac [("i", "length(zs)")] leI 1);
by (force_tac (claset(), simpset() addsimps [le_subset_iff]) 1);
by Safe_tac;
by (subgoal_tac "length(xs) #+ (i #- length(xs)) = i" 1);
by (stac nth_drop 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [leI] addsplits [nat_diff_split])));
qed "prefix_iff";

Goal 
"[|xs \\<in> list(A); ys \\<in> list(A); y \\<in> A |] ==> \
\  <xs, ys@[y]> \\<in> prefix(A) <-> (xs = ys@[y] | <xs,ys> \\<in> prefix(A))";
by (simp_tac (simpset() addsimps [prefix_iff]) 1);
by (rtac iffI 1);
by (Clarify_tac 1);
by (eres_inst_tac [("xs", "ysa")] rev_list_elim 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [app_type, app_assoc RS sym]) 1);
by (auto_tac (claset(), simpset() addsimps [app_assoc, app_type]));
qed "prefix_snoc";
Addsimps [prefix_snoc];

Goal "zs \\<in> list(A) ==> \\<forall>xs \\<in> list(A). \\<forall>ys \\<in> list(A). \
\  (<xs, ys@zs> \\<in> prefix(A)) <-> \
\ (<xs,ys> \\<in> prefix(A) | (\\<exists>us. xs = ys@us & <us,zs> \\<in> prefix(A)))";
by (etac list_append_induct 1);
by (Clarify_tac 2);
by (rtac iffI 2);
by (asm_full_simp_tac (simpset() addsimps [app_assoc RS sym]) 2);
by (etac disjE 2 THEN etac disjE 3);
by (rtac disjI2 2);
by (res_inst_tac [("x", "y @ [x]")] exI 2);
by (asm_full_simp_tac (simpset() addsimps [app_assoc RS sym]) 2);
by (REPEAT(Force_tac 1));
qed_spec_mp "prefix_append_iff";


(*Although the prefix ordering is not linear, the prefixes of a list
  are linearly ordered.*)
Goal "[| zs \\<in> list(A); xs \\<in> list(A); ys \\<in> list(A) |] \
\  ==> <xs, zs> \\<in> prefix(A) --> <ys,zs> \\<in> prefix(A) \
\ --><xs,ys> \\<in> prefix(A) | <ys,xs> \\<in> prefix(A)";
by (etac list_append_induct 1);
by Auto_tac;
qed_spec_mp "common_prefix_linear";


(*** pfixLe, pfixGe: properties inherited from the translations ***)



(** pfixLe **)

Goalw [refl_def] "refl(nat,Le)";
by Auto_tac;
qed "refl_Le";
Addsimps [refl_Le];

Goalw [antisym_def] "antisym(Le)";
by (auto_tac (claset() addIs [le_anti_sym], simpset()));
qed "antisym_Le";
Addsimps [antisym_Le];

Goalw [trans_on_def] "trans[nat](Le)";
by Auto_tac;
by (blast_tac (claset() addIs [le_trans]) 1);
qed "trans_on_Le";
Addsimps [trans_on_Le];

Goalw [trans_def] "trans(Le)";
by Auto_tac;
by (blast_tac (claset() addIs [le_trans]) 1);
qed "trans_Le";
Addsimps [trans_Le];

Goalw [part_order_def] "part_order(nat,Le)";
by Auto_tac;
qed "part_order_Le";
Addsimps [part_order_Le];

Goal "x \\<in> list(nat) ==> x pfixLe x";
by (blast_tac (claset() addIs [refl_gen_prefix RS reflD, refl_Le]) 1);
qed "pfixLe_refl";
Addsimps[pfixLe_refl];

Goal "[| x pfixLe y; y pfixLe z |] ==> x pfixLe z";
by (blast_tac (claset() addIs [trans_gen_prefix RS transD, trans_Le]) 1);
qed "pfixLe_trans";

Goal "[| x pfixLe y; y pfixLe x |] ==> x = y";
by (blast_tac (claset() addIs [antisym_gen_prefix RS antisymE, antisym_Le]) 1);
qed "pfixLe_antisym";


Goalw [prefix_def] 
"<xs,ys>:prefix(nat)==> xs pfixLe ys";
by (rtac (gen_prefix_mono RS subsetD) 1);
by Auto_tac;
qed "prefix_imp_pfixLe";

Goalw [refl_def, Ge_def] "refl(nat, Ge)";
by Auto_tac;
qed "refl_Ge";
AddIffs [refl_Ge];

Goalw [antisym_def, Ge_def] "antisym(Ge)";
by (auto_tac (claset() addIs [le_anti_sym], simpset()));
qed "antisym_Ge";
AddIffs [antisym_Ge];

Goalw [trans_def, Ge_def] "trans(Ge)";
by (auto_tac (claset() addIs [le_trans], simpset()));
qed "trans_Ge";
AddIffs [trans_Ge];

Goal "x \\<in> list(nat) ==> x pfixGe x";
by (blast_tac (claset() addIs [refl_gen_prefix RS reflD]) 1);
qed "pfixGe_refl";
Addsimps[pfixGe_refl];

Goal "[| x pfixGe y; y pfixGe z |] ==> x pfixGe z";
by (blast_tac (claset() addIs [trans_gen_prefix RS transD]) 1);
qed "pfixGe_trans";

Goal "[| x pfixGe y; y pfixGe x |] ==> x = y";
by (blast_tac (claset() addIs [antisym_gen_prefix RS antisymE]) 1);
qed "pfixGe_antisym";

Goalw [prefix_def, Ge_def] 
  "<xs,ys>:prefix(nat) ==> xs pfixGe ys";
by (rtac (gen_prefix_mono RS subsetD) 1);
by Auto_tac;
qed "prefix_imp_pfixGe";
(* Added by Sidi: prefix and take *)

Goalw [prefix_def]
"<xs, ys> \\<in> prefix(A) ==> xs = take(length(xs), ys)";
by (etac gen_prefix.induct 1);
by (subgoal_tac "length(xs):nat" 3);
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD],
              simpset() addsimps [length_type]));
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (forward_tac [gen_prefix_length_le] 1);
by (auto_tac (claset(), simpset() addsimps [take_append]));
by (subgoal_tac "length(xs) #- length(ys)=0" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [diff_is_0_iff])));
qed "prefix_imp_take";

Goal "[|<xs,ys> \\<in> prefix(A); length(xs)=length(ys)|] ==> xs = ys";
by (cut_inst_tac [("A","A")] prefix_type 1);
by (dtac subsetD 1);
by Auto_tac;  
by (dtac prefix_imp_take 1); 
by (etac trans 1); 
by (Asm_full_simp_tac 1); 
qed "prefix_length_equal";

Goal "[|<xs,ys> \\<in> prefix(A); length(ys) \\<le> length(xs)|] ==> xs = ys";
by (blast_tac (claset() addIs [prefix_length_equal, le_anti_sym, prefix_length_le]) 1); 
qed "prefix_length_le_equal";

Goalw [prefix_def] "xs \\<in> list(A) ==> \\<forall>n \\<in> nat. <take(n, xs), xs> \\<in> prefix(A)";
by (etac list.induct 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1); 
by (etac natE 1);
by Auto_tac;
qed_spec_mp "take_prefix";

Goal "<xs,ys> \\<in> prefix(A) <-> (xs=take(length(xs), ys) & xs \\<in> list(A) & ys \\<in> list(A))";
by (rtac iffI 1);
by (forward_tac [prefix_type RS subsetD] 1);
by (blast_tac (claset() addIs [prefix_imp_take]) 1);
by (Clarify_tac 1);
by (etac ssubst 1);
by (blast_tac (claset() addIs [take_prefix, length_type]) 1);
qed "prefix_take_iff";

Goal "[| <xs,ys> \\<in> prefix(A); i < length(xs)|] ==> nth(i,xs) = nth(i,ys)";
by (auto_tac (claset() addSDs [gen_prefix_imp_nth],
              simpset() addsimps [prefix_def])); 
qed "prefix_imp_nth";

val prems = Goal "[|xs \\<in> list(A); ys \\<in> list(A); length(xs) \\<le> length(ys);  \
\       !!i. i < length(xs) ==> nth(i, xs) = nth(i,ys)|]  \
\     ==> <xs,ys> \\<in> prefix(A)";
by (auto_tac (claset(), simpset() addsimps prems@[prefix_def, nth_imp_gen_prefix]));
by (auto_tac (claset() addSIs [nth_imp_gen_prefix], simpset() addsimps prems@[prefix_def]));
by (blast_tac (claset() addIs prems@[nth_type, lt_trans2]) 1); 
qed "nth_imp_prefix";


Goal "[|length(xs) \\<le> length(ys); \
\       <xs,zs> \\<in> prefix(A); <ys,zs> \\<in> prefix(A)|] ==> <xs,ys> \\<in> prefix(A)";
by (cut_inst_tac [("A","A")] prefix_type 1); 
by (rtac nth_imp_prefix 1); 
   by (blast_tac (claset() addIs []) 1); 
  by (blast_tac (claset() addIs []) 1); 
 by (assume_tac 1); 
by (res_inst_tac [("b","nth(i,zs)")] trans 1); 
 by (blast_tac (claset() addIs [prefix_imp_nth]) 1); 
by (blast_tac (claset() addIs [sym, prefix_imp_nth, prefix_length_le, lt_trans2]) 1); 
qed "length_le_prefix_imp_prefix";