(*  Title:      ZF/UNITY/Follows
    ID:         $Id \\<in> Follows.ML,v 1.4 2003/06/27 16:40:25 paulson Exp $
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge
 
The Follows relation of Charpentier and Sivilotte
*)
 
(*Does this hold for "invariant"?*)

val prems =
Goal "[|A=A'; r=r'; !!x. x \\<in> state ==> f(x)=f'(x); !!x. x \\<in> state ==> g(x)=g'(x)|] ==> Follows(A, r, f, g) = Follows(A', r', f', g')";
by (asm_full_simp_tac (simpset() addsimps [Increasing_def,Follows_def]@prems) 1);
qed "Follows_cong";

Goalw [mono1_def, metacomp_def] 
"[| mono1(A, r, B, s, h); \\<forall>x \\<in> state. f(x):A & g(x):A |] ==> \
\  Always({x \\<in> state. <f(x), g(x)> \\<in> r})<=Always({x \\<in> state. <(h comp f)(x), (h comp g)(x)> \\<in> s})";
by (auto_tac (claset(), simpset() addsimps 
         [Always_eq_includes_reachable]));
qed "subset_Always_comp";

Goal 
"[| F \\<in> Always({x \\<in> state. <f(x), g(x)> \\<in> r}); \
\   mono1(A, r, B, s, h); \\<forall>x \\<in> state. f(x):A & g(x):A |] ==> \
\   F \\<in> Always({x \\<in> state. <(h comp f)(x), (h comp g)(x)> \\<in> s})";
by (blast_tac (claset() addIs [subset_Always_comp RS subsetD]) 1);
qed "imp_Always_comp";

Goal 
"[| F \\<in> Always({x \\<in> state. <f1(x), f(x)> \\<in> r});  \
\   F \\<in> Always({x \\<in> state. <g1(x), g(x)> \\<in> s}); \
\   mono2(A, r, B, s, C, t, h); \
\   \\<forall>x \\<in> state. f1(x):A & f(x):A & g1(x):B & g(x):B |] \
\ ==> F \\<in> Always({x \\<in> state. <h(f1(x), g1(x)), h(f(x), g(x))> \\<in> t})";
by (auto_tac (claset(), simpset() addsimps 
         [Always_eq_includes_reachable, mono2_def]));
by (auto_tac (claset() addSDs [subsetD], simpset()));
qed "imp_Always_comp2";

(* comp LeadsTo *)

Goalw [mono1_def, metacomp_def]
"[| mono1(A, r, B, s, h); refl(A,r); trans[B](s); \
\       \\<forall>x \\<in> state. f(x):A & g(x):A |] ==> \
\ (\\<Inter>j \\<in> A. {s \\<in> state. <j, g(s)> \\<in> r} LeadsTo {s \\<in> state. <j,f(s)> \\<in> r}) <= \
\(\\<Inter>k \\<in> B. {x \\<in> state. <k, (h comp g)(x)> \\<in> s} LeadsTo {x \\<in> state. <k, (h comp f)(x)> \\<in> s})";
by (Clarify_tac 1);
by (ALLGOALS(full_simp_tac (simpset() addsimps [INT_iff])));
by Auto_tac;
by (rtac single_LeadsTo_I 1);
by (blast_tac (claset() addDs [LeadsTo_type RS subsetD]) 2);
by Auto_tac;
by (rotate_tac 5 1);
by (dres_inst_tac [("x", "g(sa)")] bspec 1);
by (etac LeadsTo_weaken 2);
by (auto_tac (claset(), simpset() addsimps [part_order_def, refl_def]));
by (res_inst_tac [("b", "h(g(sa))")] trans_onD 1);
by (Blast_tac 1);
by Auto_tac;
qed "subset_LeadsTo_comp";

Goal
"[| F:(\\<Inter>j \\<in> A. {s \\<in> state. <j, g(s)> \\<in> r} LeadsTo {s \\<in> state. <j,f(s)> \\<in> r}); \
\   mono1(A, r, B, s, h); refl(A,r); trans[B](s); \
\   \\<forall>x \\<in> state. f(x):A & g(x):A |] ==> \
\  F:(\\<Inter>k \\<in> B. {x \\<in> state. <k, (h comp g)(x)> \\<in> s} LeadsTo {x \\<in> state. <k, (h comp f)(x)> \\<in> s})";
by (rtac (subset_LeadsTo_comp RS subsetD) 1);
by Auto_tac;
qed "imp_LeadsTo_comp";

Goalw [mono2_def, Increasing_def]
"[| F \\<in> Increasing(B, s, g); \
\ \\<forall>j \\<in> A. F: {s \\<in> state. <j, f(s)> \\<in> r} LeadsTo {s \\<in> state. <j,f1(s)> \\<in> r}; \
\ mono2(A, r, B, s, C, t, h); refl(A, r); refl(B, s); trans[C](t); \
\ \\<forall>x \\<in> state. f1(x):A & f(x):A & g(x):B; k \\<in> C |] ==> \
\ F:{x \\<in> state. <k, h(f(x), g(x))> \\<in> t} LeadsTo {x \\<in> state. <k, h(f1(x), g(x))> \\<in> t}";
by (rtac single_LeadsTo_I 1);
by Auto_tac;
by (dres_inst_tac [("x", "g(sa)"), ("A","B")] bspec 1);
by Auto_tac;
by (dres_inst_tac [("x", "f(sa)"),("P","%j. F \\<in> ?X(j) \\<longmapsto>w ?Y(j)")] bspec 1);
by Auto_tac;
by (rtac (PSP_Stable RS LeadsTo_weaken) 1);
by (Blast_tac 1);
by (Blast_tac 1);
by Auto_tac;
by (force_tac (claset(), simpset() addsimps [part_order_def, refl_def]) 1);
by (force_tac (claset(), simpset() addsimps [part_order_def, refl_def]) 1);
by (dres_inst_tac [("x", "f1(x)"), ("x1", "f(sa)"), 
                   ("P2", "%x y. \\<forall>u\\<in>B. ?P(x,y,u)")] (bspec RS bspec) 1);
by (dres_inst_tac [("x", "g(x)"), ("x1", "g(sa)"), 
                 ("P2", "%x y. ?P(x,y) --> ?d(x,y) \\<in> t")] (bspec RS bspec) 3);
by Auto_tac;
by (res_inst_tac [("b", "h(f(sa), g(sa))"), ("A", "C")] trans_onD 1);
by (auto_tac (claset(), simpset() addsimps [part_order_def]));
qed "imp_LeadsTo_comp_right";

Goalw [mono2_def, Increasing_def]
"[| F \\<in> Increasing(A, r, f); \
\ \\<forall>j \\<in> B. F: {x \\<in> state. <j, g(x)> \\<in> s} LeadsTo {x \\<in> state. <j,g1(x)> \\<in> s}; \
\ mono2(A, r, B, s, C, t, h); refl(A,r); refl(B, s); trans[C](t); \
\ \\<forall>x \\<in> state. f(x):A & g1(x):B & g(x):B; k \\<in> C |] ==> \
\ F:{x \\<in> state. <k, h(f(x), g(x))> \\<in> t} LeadsTo {x \\<in> state. <k, h(f(x), g1(x))> \\<in> t}";
by (rtac single_LeadsTo_I 1);
by Auto_tac;
by (dres_inst_tac [("x", "f(sa)"),("P","%k. F \\<in> Stable(?X(k))")] bspec 1);
by Auto_tac;
by (dres_inst_tac [("x", "g(sa)")] bspec 1);
by Auto_tac;
by (rtac (PSP_Stable RS LeadsTo_weaken) 1);
by (Blast_tac 1);
by (Blast_tac 1);
by Auto_tac;
by (force_tac (claset(), simpset() addsimps [part_order_def, refl_def]) 1);
by (force_tac (claset(), simpset() addsimps [part_order_def, refl_def]) 1);
by (dres_inst_tac [("x", "f(x)"), ("x1", "f(sa)")] (bspec RS bspec) 1);
by (dres_inst_tac [("x", "g1(x)"), ("x1", "g(sa)"), 
                 ("P2", "%x y. ?P(x,y) --> ?d(x,y) \\<in> t")] (bspec RS bspec) 3);
by Auto_tac;
by (res_inst_tac [("b", "h(f(sa), g(sa))"), ("A", "C")] trans_onD 1);
by (auto_tac (claset(), simpset() addsimps [part_order_def]));
qed "imp_LeadsTo_comp_left";

(**  This general result is used to prove Follows Un, munion, etc. **)
Goal
"[| F \\<in> Increasing(A, r, f1) Int  Increasing(B, s, g); \
\ \\<forall>j \\<in> A. F: {s \\<in> state. <j, f(s)> \\<in> r} LeadsTo {s \\<in> state. <j,f1(s)> \\<in> r}; \
\ \\<forall>j \\<in> B. F: {x \\<in> state. <j, g(x)> \\<in> s} LeadsTo {x \\<in> state. <j,g1(x)> \\<in> s}; \
\ mono2(A, r, B, s, C, t, h); refl(A,r); refl(B, s); trans[C](t); \
\ \\<forall>x \\<in> state. f(x):A & g1(x):B & f1(x):A &g(x):B; k \\<in> C |]\
\ ==> F:{x \\<in> state. <k, h(f(x), g(x))> \\<in> t} LeadsTo {x \\<in> state. <k, h(f1(x), g1(x))> \\<in> t}";
by (res_inst_tac [("B", "{x \\<in> state. <k, h(f1(x), g(x))> \\<in> t}")] LeadsTo_Trans 1);
by (blast_tac (claset() addIs [imp_LeadsTo_comp_right]) 1);
by (blast_tac (claset() addIs [imp_LeadsTo_comp_left]) 1);
qed "imp_LeadsTo_comp2";

(* Follows type *)
Goalw [Follows_def] "Follows(A, r, f, g)<=program";
by (blast_tac (claset() addDs [Increasing_type RS subsetD]) 1);
qed "Follows_type";

Goal "F \\<in> Follows(A, r, f, g) ==> F \\<in> program";
by (blast_tac (claset() addDs [Follows_type RS subsetD]) 1);
qed "Follows_into_program";
AddTCs [Follows_into_program];

Goalw [Follows_def] 
"F \\<in> Follows(A, r, f, g)==> \
\ F \\<in> program & (\\<exists>a. a \\<in> A) & (\\<forall>x \\<in> state. f(x):A & g(x):A)";
by (blast_tac (claset() addDs [IncreasingD]) 1);
qed "FollowsD";

Goalw [Follows_def]
 "[| F \\<in> program; c \\<in> A; refl(A, r) |] ==> F \\<in> Follows(A, r, %x. c, %x. c)";
by Auto_tac;
by (auto_tac (claset(), simpset() addsimps [refl_def]));
qed "Follows_constantI";

Goalw [Follows_def] 
"[| mono1(A, r, B, s, h); refl(A, r); trans[B](s) |] \
\  ==> Follows(A, r, f, g) <= Follows(B, s,  h comp f, h comp g)";
by (Clarify_tac 1);
by (forw_inst_tac [("f", "g")] IncreasingD 1);
by (forw_inst_tac [("f", "f")] IncreasingD 1);
by (rtac IntI 1);
by (res_inst_tac [("h", "h")] imp_LeadsTo_comp 2);
by (assume_tac 5);
by (auto_tac (claset() addIs  [imp_Increasing_comp, imp_Always_comp], 
             simpset() delsimps INT_simps));
qed "subset_Follows_comp";

Goal
"[| F \\<in> Follows(A, r, f, g);  mono1(A, r, B, s, h); refl(A, r); trans[B](s) |] \
\ ==>  F \\<in> Follows(B, s,  h comp f, h comp g)";
by (blast_tac (claset() addIs [subset_Follows_comp RS subsetD]) 1);
qed "imp_Follows_comp";

(* 2-place monotone operation \\<in> this general result is used to prove Follows_Un, Follows_munion *)

(* 2-place monotone operation \\<in> this general result is 
   used to prove Follows_Un, Follows_munion *)
Goalw [Follows_def] 
"[| F \\<in> Follows(A, r, f1, f);  F \\<in> Follows(B, s, g1, g); \
\  mono2(A, r, B, s, C, t, h); refl(A,r); refl(B, s); trans[C](t) |] \
\  ==> F \\<in> Follows(C, t, %x. h(f1(x), g1(x)), %x. h(f(x), g(x)))";
by (Clarify_tac 1);
by (forw_inst_tac [("f", "g")] IncreasingD 1);
by (forw_inst_tac [("f", "f")] IncreasingD 1);
by (rtac IntI 1);
by (asm_full_simp_tac (simpset() addsimps [INT_iff]) 2);
by Safe_tac;
by (res_inst_tac [("h", "h")] imp_Always_comp2 3);
by (assume_tac 5);
by (res_inst_tac [("h", "h")] imp_Increasing_comp2 2);
by (assume_tac 4);
by (res_inst_tac [("h", "h")] imp_Increasing_comp2 1);
by (assume_tac 3);
by (TRYALL(assume_tac));
by (ALLGOALS(Asm_full_simp_tac)); 
by (blast_tac (claset() addSDs [IncreasingD]) 1);
by (res_inst_tac [("h", "h")] imp_LeadsTo_comp2 1);
by (assume_tac 4);
by Auto_tac;
by (rewrite_goal_tac [mono2_def] 3);
by (REPEAT(blast_tac (claset() addDs [IncreasingD]) 1));
qed "imp_Follows_comp2";

Goal "[| F \\<in> Follows(A, r, f, g);  F \\<in> Follows(A,r, g, h); \
\        trans[A](r) |] ==> F \\<in> Follows(A, r, f, h)";
by (forw_inst_tac [("f", "f")] FollowsD 1);
by (forw_inst_tac [("f", "g")] FollowsD 1);
by (rewrite_goal_tac [Follows_def] 1);
by (asm_full_simp_tac (simpset() 
                 addsimps [Always_eq_includes_reachable, INT_iff]) 1);
by Auto_tac;
by (res_inst_tac [("B", "{s \\<in> state. <k, g(s)> \\<in> r}")] LeadsTo_Trans 2);
by (res_inst_tac [("b", "g(x)")] trans_onD 1);
by (REPEAT(Blast_tac 1));
qed "Follows_trans";

(** Destruction rules for Follows **)

Goalw [Follows_def]
     "F \\<in> Follows(A, r, f,g) ==> F \\<in> Increasing(A, r, f)";
by (Blast_tac 1);
qed "Follows_imp_Increasing_left";

Goalw [Follows_def]
     "F \\<in> Follows(A, r, f,g) ==> F \\<in> Increasing(A, r, g)";
by (Blast_tac 1);
qed "Follows_imp_Increasing_right";

Goalw [Follows_def]
 "F :Follows(A, r, f, g) ==> F \\<in> Always({s \\<in> state. <f(s),g(s)> \\<in> r})";
by (Blast_tac 1);
qed "Follows_imp_Always";

Goalw [Follows_def]
 "[| F \\<in> Follows(A, r, f, g); k \\<in> A |]  ==> \
\ F: {s \\<in> state. <k,g(s)> \\<in> r } LeadsTo {s \\<in> state. <k,f(s)> \\<in> r}";
by (Blast_tac 1);
qed "Follows_imp_LeadsTo";

Goal "[| F \\<in> Follows(list(nat), gen_prefix(nat, Le), f, g); k \\<in> list(nat) |] \
\  ==> F \\<in> {s \\<in> state. k pfixLe g(s)} LeadsTo {s \\<in> state. k pfixLe f(s)}";
by (blast_tac (claset() addIs [Follows_imp_LeadsTo]) 1);
qed "Follows_LeadsTo_pfixLe";

Goal "[| F \\<in> Follows(list(nat), gen_prefix(nat, Ge), f, g); k \\<in> list(nat) |] \
\  ==> F \\<in> {s \\<in> state. k pfixGe g(s)} LeadsTo {s \\<in> state. k pfixGe f(s)}";
by (blast_tac (claset() addIs [Follows_imp_LeadsTo]) 1);
qed "Follows_LeadsTo_pfixGe";

Goalw  [Follows_def, Increasing_def, Stable_def]
"[| F \\<in> Always({s \\<in> state. f(s) = g(s)}); F \\<in> Follows(A, r, f, h);  \
\   \\<forall>x \\<in> state. g(x):A |] ==> F \\<in> Follows(A, r, g, h)";
by (asm_full_simp_tac (simpset() addsimps [INT_iff]) 1);
by Auto_tac;
by (res_inst_tac [("C", "{s \\<in> state. f(s)=g(s)}"),
                 ("A", "{s \\<in> state. <ka, h(s)> \\<in> r}"),
                 ("A'", "{s \\<in> state. <ka, f(s)> \\<in> r}")] Always_LeadsTo_weaken 3);
by (eres_inst_tac [("A", "{s \\<in> state. <ka,f(s)> \\<in> r}"), 
                   ("A'", "{s \\<in> state. <ka,f(s)> \\<in> r}")] 
                  Always_Constrains_weaken 1);
by Auto_tac;
by (dtac Always_Int_I 1);
by (assume_tac 1);
by (eres_inst_tac [("A","{s \\<in> state . f(s) = g(s)} \\<inter> {s \\<in> state . \\<langle>f(s), h(s)\\<rangle> \\<in> r}")] Always_weaken 1); 
by Auto_tac;
qed "Always_Follows1";

Goalw [Follows_def, Increasing_def, Stable_def]
"[| F \\<in> Always({s \\<in> state. g(s) = h(s)}); \
\ F \\<in> Follows(A, r, f, g); \\<forall>x \\<in> state. h(x):A |] ==> F \\<in> Follows(A, r, f, h)";
by (full_simp_tac (simpset() addsimps [INT_iff]) 1);
by Auto_tac;
by (thin_tac "k \\<in> A" 3);
by (res_inst_tac [("C", "{s \\<in> state. g(s)=h(s)}"),
                  ("A", "{s \\<in> state. <ka, g(s)> \\<in> r}"),
                  ("A'", "{s \\<in> state. <ka, f(s)> \\<in> r}")] Always_LeadsTo_weaken 3);
by (eres_inst_tac [("A", "{s \\<in> state. <ka, g(s)> \\<in> r}"), 
                   ("A'", "{s \\<in> state. <ka, g(s)> \\<in> r}")] 
                  Always_Constrains_weaken 1);
by Auto_tac;
by (dtac Always_Int_I 1);
by (assume_tac 1);
by (eres_inst_tac [("A","{s \\<in> state . g(s) = h(s)} \\<inter> {s \\<in> state . \\<langle>f(s), g(s)\\<rangle> \\<in> r}")] Always_weaken 1); 
by Auto_tac;
qed "Always_Follows2";

(** Union properties (with the subset ordering) **)

Goalw [refl_def, SetLe_def] "refl(Pow(A), SetLe(A))";
by Auto_tac;
qed "refl_SetLe";
Addsimps [refl_SetLe];

Goalw [trans_on_def, SetLe_def] "trans[Pow(A)](SetLe(A))";
by Auto_tac;
qed "trans_on_SetLe";
Addsimps [trans_on_SetLe];

Goalw [antisym_def, SetLe_def] "antisym(SetLe(A))";
by Auto_tac;
qed "antisym_SetLe";
Addsimps [antisym_SetLe];

Goalw [part_order_def] "part_order(Pow(A), SetLe(A))";
by Auto_tac;
qed "part_order_SetLe";
Addsimps [part_order_SetLe];

Goal "[| F \\<in> Increasing.increasing(Pow(A), SetLe(A), f);  \
\        F \\<in> Increasing.increasing(Pow(A), SetLe(A), g) |] \
\    ==> F \\<in> Increasing.increasing(Pow(A), SetLe(A), %x. f(x) Un g(x))";
by (res_inst_tac [("h", "op Un")] imp_increasing_comp2 1);
by Auto_tac;
qed "increasing_Un";

Goal "[| F \\<in> Increasing(Pow(A), SetLe(A), f);  \
\        F \\<in> Increasing(Pow(A), SetLe(A), g) |] \
\    ==> F \\<in> Increasing(Pow(A), SetLe(A), %x. f(x) Un g(x))";
by (res_inst_tac [("h", "op Un")] imp_Increasing_comp2 1);
by Auto_tac;
qed "Increasing_Un";

Goal "[| F \\<in> Always({s \\<in> state. f1(s) <= f(s)}); \
\    F \\<in> Always({s \\<in> state. g1(s) <= g(s)}) |] \
\     ==> F \\<in> Always({s \\<in> state. f1(s) Un g1(s) <= f(s) Un g(s)})";
by (asm_full_simp_tac (simpset() addsimps [Always_eq_includes_reachable]) 1);
by (Blast_tac 1);
qed "Always_Un";

Goal
"[| F \\<in> Follows(Pow(A), SetLe(A), f1, f); \
\    F \\<in> Follows(Pow(A), SetLe(A), g1, g) |] \
\    ==> F \\<in> Follows(Pow(A), SetLe(A), %s. f1(s) Un g1(s), %s. f(s) Un g(s))";
by (res_inst_tac [("h", "op Un")] imp_Follows_comp2 1);
by Auto_tac;
qed "Follows_Un";

(** Multiset union properties (with the MultLe ordering) **)

Goalw [MultLe_def, refl_def] "refl(Mult(A), MultLe(A,r))";
by Auto_tac;
qed "refl_MultLe";
Addsimps [refl_MultLe];

Goalw [MultLe_def, id_def, lam_def]
 "[| multiset(M); mset_of(M)<=A |] ==> <M, M> \\<in> MultLe(A, r)";
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "MultLe_refl1";
Addsimps [MultLe_refl1];

Goalw [MultLe_def, id_def, lam_def]
 "M \\<in> Mult(A) ==> <M, M> \\<in> MultLe(A, r)";
by Auto_tac;
qed "MultLe_refl2";
Addsimps [MultLe_refl2];

Goalw [MultLe_def, trans_on_def] "trans[Mult(A)](MultLe(A,r))";
by (auto_tac (claset() addIs [trancl_trans], simpset() addsimps [multirel_def]));
qed "trans_on_MultLe";
Addsimps [trans_on_MultLe];

Goalw [MultLe_def] "MultLe(A, r)<= (Mult(A) * Mult(A))";
by Auto_tac;
by (dtac (multirel_type RS subsetD) 1);
by Auto_tac;
qed "MultLe_type";

Goal "[| <M, K> \\<in> MultLe(A, r); <K, N> \\<in> MultLe(A, r) |] ==> <M, N> \\<in> MultLe(A,r)";
by (cut_facts_tac [inst "A" "A" trans_on_MultLe] 1);
by (dtac trans_onD 1);
by (assume_tac 1);
by (auto_tac (claset() addDs [MultLe_type RS subsetD], simpset()));
qed "MultLe_trans";

Goalw [part_order_def, part_ord_def]
"part_order(A, r) ==> part_ord(A, r-id(A))";
by (rewrite_goal_tac [refl_def, id_def, lam_def, irrefl_def] 1);
by Auto_tac;
by (simp_tac (simpset() addsimps [trans_on_def]) 1);
by Auto_tac;
by (blast_tac (claset() addDs [trans_onD]) 1);
by (full_simp_tac (simpset() addsimps [antisym_def]) 1);
by Auto_tac;
qed "part_order_imp_part_ord";

Goalw [MultLe_def, antisym_def]
  "part_order(A, r) ==> antisym(MultLe(A,r))";
by (dtac part_order_imp_part_ord 1);
by Auto_tac;
by (dtac irrefl_on_multirel 1);
by (forward_tac [multirel_type RS subsetD] 1);
by (dtac multirel_trans 1);
by (auto_tac (claset(), simpset() addsimps [irrefl_def]));
qed "antisym_MultLe";
Addsimps [antisym_MultLe];

Goal  "part_order(A, r) ==>  part_order(Mult(A), MultLe(A, r))";
by (ftac antisym_MultLe 1);
by (auto_tac (claset(), simpset() addsimps [part_order_def]));
qed "part_order_MultLe";
Addsimps [part_order_MultLe];

Goalw [MultLe_def]
"[| multiset(M); mset_of(M)<= A|] ==> <0, M> \\<in> MultLe(A, r)";
by (case_tac "M=0" 1);
by (auto_tac (claset(), simpset() addsimps (thms"FiniteFun.intros")));
by (subgoal_tac "<0 +# 0, 0 +# M> \\<in> multirel(A, r - id(A))" 1);
by (rtac one_step_implies_multirel 2);
by (auto_tac (claset(), simpset() addsimps [Mult_iff_multiset]));
qed "empty_le_MultLe";
Addsimps [empty_le_MultLe];

Goal "M \\<in> Mult(A) ==> <0, M> \\<in> MultLe(A, r)";
by (asm_full_simp_tac (simpset() addsimps [Mult_iff_multiset]) 1);
qed "empty_le_MultLe2";
Addsimps [empty_le_MultLe2];

Goalw [MultLe_def] 
"[| <M, N> \\<in> MultLe(A, r); <K, L> \\<in> MultLe(A, r) |] ==>\
\ <M +# K, N +# L> \\<in> MultLe(A, r)";
by (auto_tac (claset() addIs [munion_multirel_mono1, 
                              munion_multirel_mono2,
                              munion_multirel_mono,
                              multiset_into_Mult], 
               simpset() addsimps [Mult_iff_multiset]));
qed "munion_mono";

Goal "[| F \\<in> Increasing.increasing(Mult(A), MultLe(A,r), f);  \
\        F \\<in> Increasing.increasing(Mult(A), MultLe(A,r), g) |] \
\    ==> F \\<in> Increasing.increasing(Mult(A),MultLe(A,r), %x. f(x) +# g(x))";
by (res_inst_tac [("h", "munion")] imp_increasing_comp2 1);
by Auto_tac;
qed "increasing_munion";

Goal "[| F \\<in> Increasing(Mult(A), MultLe(A,r), f);  \
\        F \\<in> Increasing(Mult(A), MultLe(A,r), g)|] \
\    ==> F \\<in> Increasing(Mult(A),MultLe(A,r), %x. f(x) +# g(x))";
by (res_inst_tac [("h", "munion")] imp_Increasing_comp2 1);
by Auto_tac;
qed "Increasing_munion";

Goal
"[| F \\<in> Always({s \\<in> state. <f1(s),f(s)> \\<in> MultLe(A,r)}); \
\         F \\<in> Always({s \\<in> state. <g1(s), g(s)> \\<in> MultLe(A,r)});\
\ \\<forall>x \\<in> state. f1(x):Mult(A)&f(x):Mult(A) & g1(x):Mult(A) & g(x):Mult(A)|] \
\     ==> F \\<in> Always({s \\<in> state. <f1(s) +# g1(s), f(s) +# g(s)> \\<in> MultLe(A,r)})";
by (res_inst_tac [("h", "munion")] imp_Always_comp2 1);
by (ALLGOALS(Asm_full_simp_tac));
by (blast_tac (claset() addIs [munion_mono]) 1);
by (ALLGOALS(Asm_full_simp_tac));
qed "Always_munion";

Goal
"[| F \\<in> Follows(Mult(A), MultLe(A, r), f1, f); \
\   F \\<in> Follows(Mult(A), MultLe(A, r), g1, g) |] \
\ ==> F \\<in> Follows(Mult(A), MultLe(A, r), %s. f1(s) +# g1(s), %s. f(s) +# g(s))";
by (res_inst_tac [("h", "munion")] imp_Follows_comp2 1);
by Auto_tac;
qed "Follows_munion";

(** Used in ClientImp **)

Goal 
"!!f. [| \\<forall>i \\<in> I. F \\<in> Follows(Mult(A), MultLe(A, r), f'(i), f(i)); \
\ \\<forall>s. \\<forall>i \\<in> I. multiset(f'(i, s)) & mset_of(f'(i, s))<=A & \
\                       multiset(f(i, s)) & mset_of(f(i, s))<=A ; \
\  Finite(I); F \\<in> program |] \
\       ==> F \\<in> Follows(Mult(A), \
\                       MultLe(A, r), %x. msetsum(%i. f'(i, x), I, A), \
\                                     %x. msetsum(%i. f(i,  x), I, A))";
by (etac rev_mp 1);
by (dtac Finite_into_Fin 1);
by (etac Fin_induct 1);
by (Asm_simp_tac 1);
by (rtac Follows_constantI 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps  (thms"FiniteFun.intros"))));
by Auto_tac;
by (resolve_tac [Follows_munion] 1);
by Auto_tac;
qed "Follows_msetsum_UN";


