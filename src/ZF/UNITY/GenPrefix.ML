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
 "[| refl(A, r); x:A |] ==> <x,x>:r";
by Auto_tac;
qed "reflD";

(*** preliminary lemmas ***)

Goal "xs:list(A) ==> <[], xs>:gen_prefix(A, r)";
by (dtac (rotate_prems  1 gen_prefix.append) 1);
by (rtac gen_prefix.Nil 1);
by Auto_tac;
qed "Nil_gen_prefix";
Addsimps [Nil_gen_prefix];


Goal "<xs,ys>:gen_prefix(A, r) ==> length(xs) le length(ys)";
by (etac gen_prefix.induct 1);
by (subgoal_tac "ys:list(A)" 3);
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD]
                       addIs [le_trans], 
              simpset() addsimps [length_app]));
qed "gen_prefix_length_le";


Goal "[| <xs', ys'>:gen_prefix(A, r) |] \
\  ==> (ALL x xs. x:A --> xs'= Cons(x,xs) --> \
\      (EX y ys. y:A & ys' = Cons(y,ys) &\
\      <x,y>:r & <xs, ys>:gen_prefix(A, r)))";
by (etac gen_prefix.induct 1);
by (force_tac (claset() addIs [gen_prefix.append],
               simpset()) 3);
by (REPEAT(Asm_simp_tac 1));
val lemma = result();

(*As usual converting it to an elimination rule is tiresome*)
val major::prems = 
Goal "[| <Cons(x,xs), zs>:gen_prefix(A, r); \
\   !!y ys. [|zs = Cons(y, ys); y:A; x:A; <x,y>:r; \
\     <xs,ys>:gen_prefix(A, r) |] ==> P \
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
"(<Cons(x,xs),Cons(y,ys)>:gen_prefix(A, r)) \
\ <-> (x:A & y:A & <x,y>:r & <xs,ys>:gen_prefix(A, r))";
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
by (eres_inst_tac [("P", "y:list(A)")] rev_mp 1);
by (eres_inst_tac [("P", "xa:list(A)")] rev_mp 1);
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

Goal "xs:list(A) ==> \
\  ALL zs. <xs @ ys, zs>:gen_prefix(A, r) --> <xs, zs>: gen_prefix(A, r)";
by (etac list.induct 1);
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD], simpset()));
qed_spec_mp "append_gen_prefix";

(* Lemma proving transitivity and more*)

Goal "<x, y>: gen_prefix(A, r) ==> \
\  (ALL z:list(A). <y,z>:gen_prefix(A, s)--><x, z>:gen_prefix(A, s O r))";
by (etac gen_prefix.induct 1);
by (auto_tac (claset() addEs [ConsE], simpset() addsimps [Nil_gen_prefix]));
by (subgoal_tac "ys:list(A)" 1);
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
"[| <x,y>:prefix(A); <y, z>:gen_prefix(A, r); r<=A*A |] \
\ ==>  <x, z>:gen_prefix(A, r)";
by (res_inst_tac [("P", "%r. <x,z>:gen_prefix(A, r)")]
             (right_comp_id RS subst) 1);
by (REPEAT(blast_tac (claset() addDs [gen_prefix_trans_comp, 
                  gen_prefix.dom_subset RS subsetD]) 1));
qed_spec_mp "prefix_gen_prefix_trans";


Goalw [prefix_def]
"[| <x,y>:gen_prefix(A,r); <y, z>:prefix(A); r<=A*A |] \
\ ==>  <x, z>:gen_prefix(A, r)";
by (res_inst_tac [("P", "%r. <x,z>:gen_prefix(A, r)")] (left_comp_id RS subst) 1);
by (REPEAT(blast_tac (claset() addDs [gen_prefix_trans_comp, 
                                      gen_prefix.dom_subset RS subsetD]) 1));
qed_spec_mp "gen_prefix_prefix_trans";

(** Antisymmetry **)

Goal "n:nat ==> ALL b:nat. n #+ b le n --> b = 0";
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
by (subgoal_tac "ys:list(A)" 1);
by (blast_tac (claset() addDs [gen_prefix.dom_subset RS subsetD]) 2);
by (dres_inst_tac [("psi", "<ys @ zs, xs>:gen_prefix(A,r)")] asm_rl 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "length(ys @ zs)  = length(ys) #+ length(zs) &ys:list(A)&xs:list(A)" 1);
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

Goal "xs:list(A) ==> <xs, []>:gen_prefix(A,r) <-> (xs = [])";
by (induct_tac "xs" 1);
by Auto_tac;
qed "gen_prefix_Nil";
Addsimps [gen_prefix_Nil];

Goalw [refl_def]
 "[| refl(A, r);  xs:list(A) |] ==> \
\   <xs@ys, xs@zs>: gen_prefix(A, r) <-> <ys,zs>:gen_prefix(A, r)";
by (induct_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "same_gen_prefix_gen_prefix";
Addsimps [same_gen_prefix_gen_prefix];

Goal "[| xs:list(A); ys:list(A); y:A |] ==> \
\   <xs, Cons(y,ys)> : gen_prefix(A,r)  <-> \
\     (xs=[] | (EX z zs. xs=Cons(z,zs) & z:A & <z,y>:r & <zs,ys>:gen_prefix(A,r)))";
by (induct_tac "xs" 1);
by Auto_tac;
qed "gen_prefix_Cons";

Goal "[| refl(A,r);  <xs,ys>:gen_prefix(A, r); zs:list(A) |] \
\     ==>  <xs@zs, take(length(xs), ys) @ zs> : gen_prefix(A, r)";
by (etac gen_prefix.induct 1);
by (Asm_simp_tac 1);
by (ALLGOALS(forward_tac [gen_prefix.dom_subset RS subsetD]));
by Auto_tac;
by (ftac gen_prefix_length_le 1);
by (subgoal_tac "take(length(xs), ys):list(A)" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps 
         [diff_is_0_iff RS iffD2, take_type ])));
qed "gen_prefix_take_append";

Goal "[| refl(A, r);  <xs,ys>:gen_prefix(A,r);   \
\        length(xs) = length(ys); zs:list(A) |] \
\     ==>  <xs@zs, ys @ zs> : gen_prefix(A, r)";
by (dres_inst_tac [("zs", "zs")]  gen_prefix_take_append 1);
by (REPEAT(assume_tac 1));
by (subgoal_tac "take(length(xs), ys)=ys" 1);
by (auto_tac (claset() addSIs [take_all] 
                       addDs [gen_prefix.dom_subset RS subsetD], 
              simpset()));
qed "gen_prefix_append_both";

(*NOT suitable for rewriting since [y] has the form y#ys*)
Goal "xs:list(A) ==> xs @ Cons(y, ys) = (xs @ [y]) @ ys";
by (auto_tac (claset(), simpset() addsimps [app_assoc]));
qed "append_cons_conv";

Goal "[| <xs,ys>:gen_prefix(A, r);  refl(A, r) |] \
\     ==> length(xs) < length(ys) --> \
\         <xs @ [nth(length(xs), ys)], ys>:gen_prefix(A, r)";
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
by (case_tac "zs=[]" 1);
by (auto_tac (claset(), simpset() addsimps [neq_Nil_iff]));
by (res_inst_tac [("P1", "%x. <?u(x), ?v>:?w")] (nat_diff_split RS iffD2) 1);
by Auto_tac;
by (stac append_cons_conv 1);
by (rtac   gen_prefix.append 2);
by (auto_tac (claset() addEs [ConsE],
              simpset() addsimps [gen_prefix_append_both]));
val lemma = result() RS mp;

Goal "[| <xs,ys>: gen_prefix(A, r);  length(xs) < length(ys);  refl(A, r) |] \
\     ==> <xs @ [nth(length(xs), ys)], ys>:gen_prefix(A, r)";
by (blast_tac (claset() addIs [lemma]) 1);
qed "append_one_gen_prefix";


(** Proving the equivalence with Charpentier's definition **)

Goal "xs:list(A) ==>  \
\ ALL ys:list(A). ALL i:nat. i < length(xs) \
\         --> <xs, ys>: gen_prefix(A, r) --> <nth(i, xs), nth(i, ys)>:r";
by (induct_tac "xs" 1);
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(Asm_full_simp_tac));
by (etac natE 1);
by (ALLGOALS(Asm_full_simp_tac));
by (dres_inst_tac [("x", "ysa")] bspec 1);
by (dres_inst_tac [("x", "x")] bspec 2);
by (auto_tac (claset() addDs [gen_prefix.dom_subset RS subsetD], simpset()));
qed_spec_mp "gen_prefix_imp_nth";

Goal "xs:list(A) ==> \
\ ALL ys:list(A). length(xs) le length(ys)  \
\     --> (ALL i:nat. i < length(xs)--> <nth(i, xs), nth(i,ys)>:r)  \
\     --> <xs, ys> : gen_prefix(A, r)";
by (induct_tac "xs" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lt_succ_eq_0_disj]))); 
by (Clarify_tac 1);
by (case_tac "x=[]" 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [neq_Nil_iff])));
by (Clarify_tac 1);
by (dres_inst_tac [("x", "ys")] bspec 1);
by (ALLGOALS(Clarify_tac));
by Auto_tac;
qed_spec_mp "nth_imp_gen_prefix";

Goal "(<xs,ys>: gen_prefix(A,r)) <-> \
\ (xs:list(A) & ys:list(A) & length(xs) le length(ys) & \
\ (ALL i:nat. i < length(xs) --> <nth(i,xs), nth(i, ys)>: r))";
by (rtac iffI 1);
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (ftac gen_prefix_length_le 1);
by (ALLGOALS(Clarify_tac));
by (rtac nth_imp_gen_prefix 2);
by (dtac (rotate_prems 4 gen_prefix_imp_nth) 1);
by Auto_tac;
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
"<xs,ys>:prefix(A) ==> set_of_list(xs) <= set_of_list(ys)";
by (etac gen_prefix.induct 1);
by (subgoal_tac "xs:list(A)&ys:list(A)" 3);
by (blast_tac (claset() addDs [gen_prefix.dom_subset RS subsetD]) 4);
by (auto_tac (claset(), simpset() addsimps [set_of_list_append]));
qed "set_of_list_prefix_mono";  

(** recursion equations **)

Goalw [prefix_def] "xs:list(A) ==> <[],xs>:prefix(A)";
by (asm_simp_tac (simpset() addsimps [Nil_gen_prefix]) 1);
qed "Nil_prefix";
Addsimps[Nil_prefix];


Goalw [prefix_def] "<xs, []>:prefix(A) <-> (xs = [])";
by Auto_tac;
by (forward_tac [gen_prefix.dom_subset RS subsetD] 1);
by (dres_inst_tac [("psi", "<xs, []>:gen_prefix(A, id(A))")] asm_rl 1);
by (asm_full_simp_tac (simpset() addsimps [gen_prefix_Nil]) 1);
qed "prefix_Nil";
AddIffs [prefix_Nil];

Goalw [prefix_def] 
"<Cons(x,xs), Cons(y,ys)>:prefix(A) <-> (x=y & <xs,ys>:prefix(A) & y:A)";
by Auto_tac;
qed"Cons_prefix_Cons";
AddIffs [Cons_prefix_Cons];

Goalw [prefix_def] 
"xs:list(A)==> <xs@ys,xs@zs>:prefix(A) <-> (<ys,zs>:prefix(A))";
by (subgoal_tac "refl(A,id(A))" 1);
by (Asm_simp_tac 1);
by (auto_tac (claset(), simpset() addsimps[refl_def]));
qed "same_prefix_prefix";
Addsimps [same_prefix_prefix];

Goal "xs:list(A) ==> <xs@ys,xs>:prefix(A) <-> (<ys,[]>:prefix(A))";
by (res_inst_tac [("P", "%x. <?u, x>:?v <-> ?w(x)")] (app_right_Nil RS subst) 1);
by (rtac same_prefix_prefix 2);
by Auto_tac;
qed "same_prefix_prefix_Nil";
Addsimps [same_prefix_prefix_Nil];

Goalw [prefix_def] 
"[| <xs,ys>:prefix(A); zs:list(A) |] ==> <xs,ys@zs>:prefix(A)";
by (etac gen_prefix.append 1);
by (assume_tac 1);
qed "prefix_appendI";
Addsimps [prefix_appendI];

Goalw [prefix_def] 
"[| xs:list(A); ys:list(A); y:A |] ==> \
\ <xs,Cons(y,ys)>:prefix(A) <-> \
\ (xs=[] | (EX zs. xs=Cons(y,zs) & <zs,ys>:prefix(A)))";
by (auto_tac (claset(), simpset() addsimps [gen_prefix_Cons]));
qed "prefix_Cons";

Goalw [prefix_def]
  "[| <xs,ys>:prefix(A); length(xs) < length(ys) |] \
\ ==> <xs @ [nth(length(xs),ys)], ys>:prefix(A)";
by (subgoal_tac "refl(A, id(A))" 1);
by (asm_simp_tac (simpset() addsimps [append_one_gen_prefix]) 1);
by (auto_tac (claset(), simpset() addsimps [refl_def]));
qed "append_one_prefix";

Goalw [prefix_def] 
"<xs,ys>:prefix(A) ==> length(xs) le length(ys)";
by (blast_tac (claset() addDs [gen_prefix_length_le]) 1);
qed "prefix_length_le";

Goalw [prefix_def] 
"<xs,ys>:prefix(A) ==> xs~=ys --> length(xs) < length(ys)";
by (etac gen_prefix.induct 1);
by (Clarify_tac 1);
by (ALLGOALS(subgoal_tac "ys:list(A)&xs:list(A)"));
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
"<xs,zs>:prefix(A) <-> (EX ys:list(A). zs = xs@ys) & xs:list(A)";
by (auto_tac (claset(),
       simpset() addsimps [gen_prefix_iff_nth, 
                           nth_append, nth_type, app_type, length_app]));
by (subgoal_tac "length(xs):nat&length(zs):nat & \
\                drop(length(xs), zs):list(A)" 1);
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
by (Blast_tac 1);
by (subgoal_tac "length(xs) #+ (x #- length(xs)) = x" 1);
by (stac nth_drop 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps [leI])));
by (rtac (nat_diff_split RS iffD2) 1);
by Auto_tac;
qed "prefix_iff";

Goal 
"[|xs:list(A); ys:list(A); y:A |] ==> \
\  <xs, ys@[y]>:prefix(A) <-> (xs = ys@[y] | <xs,ys>:prefix(A))";
by (simp_tac (simpset() addsimps [prefix_iff]) 1);
by (rtac iffI 1);
by (Clarify_tac 1);
by (eres_inst_tac [("xs", "ysa")] rev_list_elim 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("psi", "ya:list(A)")] asm_rl 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps
           [app_type, app_assoc RS sym] delsimps [app_assoc]) 1);
by (auto_tac (claset(), simpset() addsimps [app_assoc, app_type]));
qed "prefix_snoc";
Addsimps [prefix_snoc];


Goal "zs:list(A) ==> ALL xs:list(A). ALL ys:list(A). \
\  (<xs, ys@zs>:prefix(A)) <-> \
\ (<xs,ys>:prefix(A) | (EX us. xs = ys@us & <us,zs>:prefix(A)))";
by (etac list_append_induct 1);
by (Clarify_tac 2);
by (rtac iffI 2);
by (asm_full_simp_tac (simpset()  delsimps [app_assoc]
                                 addsimps [app_assoc RS sym]) 2);
by (etac disjE 2 THEN etac disjE 3);
by (rtac disjI2 2);
by (res_inst_tac [("x", "y @ [x]")] exI 2);
by (asm_full_simp_tac (simpset()  delsimps [app_assoc]
                                 addsimps [app_assoc RS sym]) 2);
by (REPEAT(Force_tac 1));
qed_spec_mp "prefix_append_iff";


(*Although the prefix ordering is not linear, the prefixes of a list
  are linearly ordered.*)
Goal "[| zs:list(A); xs:list(A); ys:list(A) |] \
\  ==> <xs, zs>:prefix(A) --> <ys,zs>:prefix(A) \
\ --><xs,ys>:prefix(A) | <ys,xs>:prefix(A)";
by (etac list_append_induct 1);
by Auto_tac;
qed_spec_mp "common_prefix_linear";


(*** pfixLe, pfixGe: properties inherited from the translations ***)



(** pfixLe **)

Goalw [refl_def, Le_def] "refl(nat,Le)";
by Auto_tac;
qed "refl_Le";
AddIffs [refl_Le];

Goalw [antisym_def, Le_def] "antisym(Le)";
by (auto_tac (claset() addIs [le_anti_sym], simpset()));
qed "antisym_Le";
AddIffs [antisym_Le];

Goalw [trans_def, Le_def] "trans(Le)";
by (auto_tac (claset() addIs [le_trans], simpset()));
qed "trans_Le";
AddIffs [trans_Le];

Goal "x:list(nat) ==> x pfixLe x";
by (blast_tac (claset() addIs [refl_gen_prefix RS reflD]) 1);
qed "pfixLe_refl";
Addsimps[pfixLe_refl];

Goal "[| x pfixLe y; y pfixLe z |] ==> x pfixLe z";
by (blast_tac (claset() addIs [trans_gen_prefix RS transD]) 1);
qed "pfixLe_trans";

Goal "[| x pfixLe y; y pfixLe x |] ==> x = y";
by (blast_tac (claset() addIs [antisym_gen_prefix RS antisymE]) 1);
qed "pfixLe_antisym";


Goalw [prefix_def, Le_def] 
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

Goal "x:list(nat) ==> x pfixGe x";
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






