(*  Title:      ZF/Perm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The theory underlying permutation groups
  -- Composition of relations, the identity relation
  -- Injections, surjections, bijections
  -- Lemmas for the Schroeder-Bernstein Theorem
*)

open Perm;

(** Surjective function space **)

goalw Perm.thy [surj_def] "!!f A B. f: surj(A,B) ==> f: A->B";
by (etac CollectD1 1);
qed "surj_is_fun";

goalw Perm.thy [surj_def] "!!f A B. f : Pi(A,B) ==> f: surj(A,range(f))";
by (fast_tac (ZF_cs addIs [apply_equality] 
                    addEs [range_of_fun,domain_type]) 1);
qed "fun_is_surj";

goalw Perm.thy [surj_def] "!!f A B. f: surj(A,B) ==> range(f)=B";
by (best_tac (ZF_cs addIs [equalityI,apply_Pair] addEs [range_type]) 1);
qed "surj_range";

(** A function with a right inverse is a surjection **)

val prems = goalw Perm.thy [surj_def]
    "[| f: A->B;  !!y. y:B ==> d(y): A;  !!y. y:B ==> f`d(y) = y \
\    |] ==> f: surj(A,B)";
by (fast_tac (ZF_cs addIs prems) 1);
qed "f_imp_surjective";

val prems = goal Perm.thy
    "[| !!x. x:A ==> c(x): B;           \
\       !!y. y:B ==> d(y): A;           \
\       !!y. y:B ==> c(d(y)) = y        \
\    |] ==> (lam x:A.c(x)) : surj(A,B)";
by (res_inst_tac [("d", "d")] f_imp_surjective 1);
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps ([lam_type]@prems)) ));
qed "lam_surjective";

(*Cantor's theorem revisited*)
goalw Perm.thy [surj_def] "f ~: surj(A,Pow(A))";
by (safe_tac ZF_cs);
by (cut_facts_tac [cantor] 1);
by (fast_tac subset_cs 1);
qed "cantor_surj";


(** Injective function space **)

goalw Perm.thy [inj_def] "!!f A B. f: inj(A,B) ==> f: A->B";
by (etac CollectD1 1);
qed "inj_is_fun";

goalw Perm.thy [inj_def]
    "!!f A B. [| <a,b>:f;  <c,b>:f;  f: inj(A,B) |] ==> a=c";
by (REPEAT (eresolve_tac [asm_rl, Pair_mem_PiE, CollectE] 1));
by (fast_tac ZF_cs 1);
qed "inj_equality";

goalw thy [inj_def] "!!A B f. [| f:inj(A,B);  a:A;  b:A;  f`a=f`b |] ==> a=b";
by (fast_tac ZF_cs 1);
val inj_apply_equality = result();

(** A function with a left inverse is an injection **)

val prems = goal Perm.thy
    "[| f: A->B;  !!x. x:A ==> d(f`x)=x |] ==> f: inj(A,B)";
by (asm_simp_tac (ZF_ss addsimps ([inj_def] @ prems)) 1);
by (safe_tac ZF_cs);
by (eresolve_tac [subst_context RS box_equals] 1);
by (REPEAT (ares_tac prems 1));
qed "f_imp_injective";

val prems = goal Perm.thy
    "[| !!x. x:A ==> c(x): B;           \
\       !!x. x:A ==> d(c(x)) = x        \
\    |] ==> (lam x:A.c(x)) : inj(A,B)";
by (res_inst_tac [("d", "d")] f_imp_injective 1);
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps ([lam_type]@prems)) ));
qed "lam_injective";

(** Bijections **)

goalw Perm.thy [bij_def] "!!f A B. f: bij(A,B) ==> f: inj(A,B)";
by (etac IntD1 1);
qed "bij_is_inj";

goalw Perm.thy [bij_def] "!!f A B. f: bij(A,B) ==> f: surj(A,B)";
by (etac IntD2 1);
qed "bij_is_surj";

(* f: bij(A,B) ==> f: A->B *)
bind_thm ("bij_is_fun", (bij_is_inj RS inj_is_fun));

val prems = goalw Perm.thy [bij_def]
    "[| !!x. x:A ==> c(x): B;           \
\       !!y. y:B ==> d(y): A;           \
\       !!x. x:A ==> d(c(x)) = x;       \
\       !!y. y:B ==> c(d(y)) = y        \
\    |] ==> (lam x:A.c(x)) : bij(A,B)";
by (REPEAT (ares_tac (prems @ [IntI, lam_injective, lam_surjective]) 1));
qed "lam_bijective";


(** Identity function **)

val [prem] = goalw Perm.thy [id_def] "a:A ==> <a,a> : id(A)";  
by (rtac (prem RS lamI) 1);
qed "idI";

val major::prems = goalw Perm.thy [id_def]
    "[| p: id(A);  !!x.[| x:A; p=<x,x> |] ==> P  \
\    |] ==>  P";  
by (rtac (major RS lamE) 1);
by (REPEAT (ares_tac prems 1));
qed "idE";

goalw Perm.thy [id_def] "id(A) : A->A";  
by (rtac lam_type 1);
by (assume_tac 1);
qed "id_type";

goalw Perm.thy [id_def] "!!A x. x:A ==> id(A)`x = x";
by (asm_simp_tac ZF_ss 1);
val id_conv = result();

val [prem] = goalw Perm.thy [id_def] "A<=B ==> id(A) <= id(B)";
by (rtac (prem RS lam_mono) 1);
qed "id_mono";

goalw Perm.thy [inj_def,id_def] "!!A B. A<=B ==> id(A): inj(A,B)";
by (REPEAT (ares_tac [CollectI,lam_type] 1));
by (etac subsetD 1 THEN assume_tac 1);
by (simp_tac ZF_ss 1);
qed "id_subset_inj";

val id_inj = subset_refl RS id_subset_inj;

goalw Perm.thy [id_def,surj_def] "id(A): surj(A,A)";
by (fast_tac (ZF_cs addIs [lam_type,beta]) 1);
qed "id_surj";

goalw Perm.thy [bij_def] "id(A): bij(A,A)";
by (fast_tac (ZF_cs addIs [id_inj,id_surj]) 1);
qed "id_bij";

goalw Perm.thy [id_def] "A <= B <-> id(A) : A->B";
by (safe_tac ZF_cs);
by (fast_tac (ZF_cs addSIs [lam_type]) 1);
by (dtac apply_type 1);
by (assume_tac 1);
by (asm_full_simp_tac ZF_ss 1);
qed "subset_iff_id";


(*** Converse of a function ***)

val [prem] = goal Perm.thy "f: inj(A,B) ==> converse(f) : range(f)->A";
by (cut_facts_tac [prem] 1);
by (asm_full_simp_tac (ZF_ss addsimps [inj_def, Pi_iff, domain_converse]) 1);
by (rtac conjI 1);
by (deepen_tac ZF_cs 0 2);
by (simp_tac (ZF_ss addsimps [function_def, converse_iff]) 1);
by (fast_tac (ZF_cs addEs [prem RSN (3,inj_equality)]) 1);
qed "inj_converse_fun";

(** Equations for converse(f) **)

(*The premises are equivalent to saying that f is injective...*) 
val prems = goal Perm.thy
    "[| f: A->B;  converse(f): C->A;  a: A |] ==> converse(f)`(f`a) = a";
by (fast_tac (ZF_cs addIs (prems@[apply_Pair,apply_equality,converseI])) 1);
qed "left_inverse_lemma";

goal Perm.thy
    "!!f. [| f: inj(A,B);  a: A |] ==> converse(f)`(f`a) = a";
by (fast_tac (ZF_cs addIs [left_inverse_lemma,inj_converse_fun,inj_is_fun]) 1);
qed "left_inverse";

val left_inverse_bij = bij_is_inj RS left_inverse;

val prems = goal Perm.thy
    "[| f: A->B;  converse(f): C->A;  b: C |] ==> f`(converse(f)`b) = b";
by (rtac (apply_Pair RS (converseD RS apply_equality)) 1);
by (REPEAT (resolve_tac prems 1));
qed "right_inverse_lemma";

(*Should the premises be f:surj(A,B), b:B for symmetry with left_inverse?
  No: they would not imply that converse(f) was a function! *)
goal Perm.thy "!!f. [| f: inj(A,B);  b: range(f) |] ==> f`(converse(f)`b) = b";
by (rtac right_inverse_lemma 1);
by (REPEAT (ares_tac [inj_converse_fun,inj_is_fun] 1));
qed "right_inverse";

goalw Perm.thy [bij_def]
    "!!f. [| f: bij(A,B);  b: B |] ==> f`(converse(f)`b) = b";
by (EVERY1 [etac IntE, etac right_inverse, 
            etac (surj_range RS ssubst),
            assume_tac]);
qed "right_inverse_bij";

(** Converses of injections, surjections, bijections **)

goal Perm.thy "!!f A B. f: inj(A,B) ==> converse(f): inj(range(f), A)";
by (rtac f_imp_injective 1);
by (etac inj_converse_fun 1);
by (rtac right_inverse 1);
by (REPEAT (assume_tac 1));
qed "inj_converse_inj";

goal Perm.thy "!!f A B. f: inj(A,B) ==> converse(f): surj(range(f), A)";
by (REPEAT (ares_tac [f_imp_surjective, inj_converse_fun] 1));
by (REPEAT (ares_tac [left_inverse] 2));
by (REPEAT (ares_tac [inj_is_fun, range_of_fun RS apply_type] 1));
qed "inj_converse_surj";

goalw Perm.thy [bij_def] "!!f A B. f: bij(A,B) ==> converse(f): bij(B,A)";
by (etac IntE 1);
by (eresolve_tac [(surj_range RS subst)] 1);
by (rtac IntI 1);
by (etac inj_converse_inj 1);
by (etac inj_converse_surj 1);
qed "bij_converse_bij";


(** Composition of two relations **)

(*The inductive definition package could derive these theorems for (r O s)*)

goalw Perm.thy [comp_def] "!!r s. [| <a,b>:s; <b,c>:r |] ==> <a,c> : r O s";
by (fast_tac ZF_cs 1);
qed "compI";

val prems = goalw Perm.thy [comp_def]
    "[| xz : r O s;  \
\       !!x y z. [| xz=<x,z>;  <x,y>:s;  <y,z>:r |] ==> P \
\    |] ==> P";
by (cut_facts_tac prems 1);
by (REPEAT (eresolve_tac [CollectE, exE, conjE] 1 ORELSE ares_tac prems 1));
qed "compE";

val compEpair = 
    rule_by_tactic (REPEAT_FIRST (etac Pair_inject ORELSE' bound_hyp_subst_tac)
                    THEN prune_params_tac)
        (read_instantiate [("xz","<a,c>")] compE);

val comp_cs = ZF_cs addSIs [idI] addIs [compI] addSEs [compE,idE];

(** Domain and Range -- see Suppes, section 3.1 **)

(*Boyer et al., Set Theory in First-Order Logic, JAR 2 (1986), 287-327*)
goal Perm.thy "range(r O s) <= range(r)";
by (fast_tac comp_cs 1);
qed "range_comp";

goal Perm.thy "!!r s. domain(r) <= range(s) ==> range(r O s) = range(r)";
by (rtac (range_comp RS equalityI) 1);
by (fast_tac comp_cs 1);
qed "range_comp_eq";

goal Perm.thy "domain(r O s) <= domain(s)";
by (fast_tac comp_cs 1);
qed "domain_comp";

goal Perm.thy "!!r s. range(s) <= domain(r) ==> domain(r O s) = domain(s)";
by (rtac (domain_comp RS equalityI) 1);
by (fast_tac comp_cs 1);
qed "domain_comp_eq";

goal Perm.thy "(r O s)``A = r``(s``A)";
by (fast_tac (comp_cs addIs [equalityI]) 1);
qed "image_comp";


(** Other results **)

goal Perm.thy "!!r s. [| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)";
by (fast_tac comp_cs 1);
qed "comp_mono";

(*composition preserves relations*)
goal Perm.thy "!!r s. [| s<=A*B;  r<=B*C |] ==> (r O s) <= A*C";
by (fast_tac comp_cs 1);
qed "comp_rel";

(*associative law for composition*)
goal Perm.thy "(r O s) O t = r O (s O t)";
by (fast_tac (comp_cs addIs [equalityI]) 1);
qed "comp_assoc";

(*left identity of composition; provable inclusions are
        id(A) O r <= r       
  and   [| r<=A*B; B<=C |] ==> r <= id(C) O r *)
goal Perm.thy "!!r A B. r<=A*B ==> id(B) O r = r";
by (fast_tac (comp_cs addIs [equalityI]) 1);
qed "left_comp_id";

(*right identity of composition; provable inclusions are
        r O id(A) <= r
  and   [| r<=A*B; A<=C |] ==> r <= r O id(C) *)
goal Perm.thy "!!r A B. r<=A*B ==> r O id(A) = r";
by (fast_tac (comp_cs addIs [equalityI]) 1);
qed "right_comp_id";


(** Composition preserves functions, injections, and surjections **)

goalw Perm.thy [function_def]
    "!!f g. [| function(g);  function(f) |] ==> function(f O g)";
by (fast_tac (ZF_cs addIs [compI] addSEs [compE, Pair_inject]) 1);
qed "comp_function";

goalw Perm.thy [Pi_def]
    "!!f g. [| g: A->B;  f: B->C |] ==> (f O g) : A->C";
by (safe_tac subset_cs);
by (asm_simp_tac (ZF_ss addsimps [comp_function]) 3);
by (rtac (range_rel_subset RS domain_comp_eq RS ssubst) 2 THEN assume_tac 3);
by (fast_tac ZF_cs 2);
by (asm_simp_tac (ZF_ss addsimps [comp_rel]) 1);
qed "comp_fun";

goal Perm.thy "!!f g. [| g: A->B;  f: B->C;  a:A |] ==> (f O g)`a = f`(g`a)";
by (REPEAT (ares_tac [comp_fun,apply_equality,compI,
                      apply_Pair,apply_type] 1));
qed "comp_fun_apply";

(*Simplifies compositions of lambda-abstractions*)
val [prem] = goal Perm.thy
    "[| !!x. x:A ==> b(x): B    \
\    |] ==> (lam y:B.c(y)) O (lam x:A. b(x)) = (lam x:A. c(b(x)))";
by (rtac fun_extension 1);
by (rtac comp_fun 1);
by (rtac lam_funtype 2);
by (typechk_tac (prem::ZF_typechecks));
by (asm_simp_tac (ZF_ss addsimps [comp_fun_apply]
             setsolver type_auto_tac [lam_type, lam_funtype, prem]) 1);
qed "comp_lam";

goal Perm.thy "!!f g. [| g: inj(A,B);  f: inj(B,C) |] ==> (f O g) : inj(A,C)";
by (res_inst_tac [("d", "%y. converse(g) ` (converse(f) ` y)")]
    f_imp_injective 1);
by (REPEAT (ares_tac [comp_fun, inj_is_fun] 1));
by (asm_simp_tac (ZF_ss addsimps [comp_fun_apply, left_inverse] 
                        setsolver type_auto_tac [inj_is_fun, apply_type]) 1);
qed "comp_inj";

goalw Perm.thy [surj_def]
    "!!f g. [| g: surj(A,B);  f: surj(B,C) |] ==> (f O g) : surj(A,C)";
by (best_tac (ZF_cs addSIs [comp_fun,comp_fun_apply]) 1);
qed "comp_surj";

goalw Perm.thy [bij_def]
    "!!f g. [| g: bij(A,B);  f: bij(B,C) |] ==> (f O g) : bij(A,C)";
by (fast_tac (ZF_cs addIs [comp_inj,comp_surj]) 1);
qed "comp_bij";


(** Dual properties of inj and surj -- useful for proofs from
    D Pastre.  Automatic theorem proving in set theory. 
    Artificial Intelligence, 10:1--27, 1978. **)

goalw Perm.thy [inj_def]
    "!!f g. [| (f O g): inj(A,C);  g: A->B;  f: B->C |] ==> g: inj(A,B)";
by (safe_tac comp_cs);
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp] 1));
by (asm_simp_tac (FOL_ss addsimps [comp_fun_apply]) 1);
qed "comp_mem_injD1";

goalw Perm.thy [inj_def,surj_def]
    "!!f g. [| (f O g): inj(A,C);  g: surj(A,B);  f: B->C |] ==> f: inj(B,C)";
by (safe_tac comp_cs);
by (res_inst_tac [("x1", "x")] (bspec RS bexE) 1);
by (eres_inst_tac [("x1", "w")] (bspec RS bexE) 3);
by (REPEAT (assume_tac 1));
by (safe_tac comp_cs);
by (res_inst_tac [("t", "op `(g)")] subst_context 1);
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp] 1));
by (asm_simp_tac (FOL_ss addsimps [comp_fun_apply]) 1);
qed "comp_mem_injD2";

goalw Perm.thy [surj_def]
    "!!f g. [| (f O g): surj(A,C);  g: A->B;  f: B->C |] ==> f: surj(B,C)";
by (fast_tac (comp_cs addSIs [comp_fun_apply RS sym, apply_type]) 1);
qed "comp_mem_surjD1";

goal Perm.thy
    "!!f g. [| (f O g)`a = c;  g: A->B;  f: B->C;  a:A |] ==> f`(g`a) = c";
by (REPEAT (ares_tac [comp_fun_apply RS sym RS trans] 1));
qed "comp_fun_applyD";

goalw Perm.thy [inj_def,surj_def]
    "!!f g. [| (f O g): surj(A,C);  g: A->B;  f: inj(B,C) |] ==> g: surj(A,B)";
by (safe_tac comp_cs);
by (eres_inst_tac [("x1", "f`y")] (bspec RS bexE) 1);
by (REPEAT (ares_tac [apply_type] 1 ORELSE dtac comp_fun_applyD 1));
by (best_tac (comp_cs addSIs [apply_type]) 1);
qed "comp_mem_surjD2";


(** inverses of composition **)

(*left inverse of composition; one inclusion is
        f: A->B ==> id(A) <= converse(f) O f *)
val [prem] = goal Perm.thy
    "f: inj(A,B) ==> converse(f) O f = id(A)";
val injfD = prem RSN (3,inj_equality);
by (cut_facts_tac [prem RS inj_is_fun] 1);
by (fast_tac (comp_cs addIs [equalityI,apply_Pair] 
                      addEs [domain_type, make_elim injfD]) 1);
qed "left_comp_inverse";

(*right inverse of composition; one inclusion is
                f: A->B ==> f O converse(f) <= id(B) 
*)
val [prem] = goalw Perm.thy [surj_def]
    "f: surj(A,B) ==> f O converse(f) = id(B)";
val appfD = (prem RS CollectD1) RSN (3,apply_equality2);
by (cut_facts_tac [prem] 1);
by (rtac equalityI 1);
by (best_tac (comp_cs addEs [domain_type, range_type, make_elim appfD]) 1);
by (best_tac (comp_cs addIs [apply_Pair]) 1);
qed "right_comp_inverse";

(** Proving that a function is a bijection **)

goalw Perm.thy [id_def]
    "!!f A B. [| f: A->B;  g: B->A |] ==> \
\             f O g = id(B) <-> (ALL y:B. f`(g`y)=y)";
by (safe_tac ZF_cs);
by (dres_inst_tac [("t", "%h.h`y ")] subst_context 1);
by (asm_full_simp_tac (ZF_ss addsimps [comp_fun_apply]) 1);
by (rtac fun_extension 1);
by (REPEAT (ares_tac [comp_fun, lam_type] 1));
by (asm_simp_tac (ZF_ss addsimps [comp_fun_apply]) 1);
qed "comp_eq_id_iff";

goalw Perm.thy [bij_def]
    "!!f A B. [| f: A->B;  g: B->A;  f O g = id(B);  g O f = id(A) \
\             |] ==> f : bij(A,B)";
by (asm_full_simp_tac (ZF_ss addsimps [comp_eq_id_iff]) 1);
by (REPEAT (ares_tac [conjI, f_imp_injective, f_imp_surjective] 1
       ORELSE eresolve_tac [bspec, apply_type] 1));
qed "fg_imp_bijective";

goal Perm.thy "!!f A. [| f: A->A;  f O f = id(A) |] ==> f : bij(A,A)";
by (REPEAT (ares_tac [fg_imp_bijective] 1));
qed "nilpotent_imp_bijective";

goal Perm.thy "!!f A B. [| converse(f): B->A;  f: A->B |] ==> f : bij(A,B)";
by (asm_simp_tac (ZF_ss addsimps [fg_imp_bijective, comp_eq_id_iff, 
                                  left_inverse_lemma, right_inverse_lemma]) 1);
qed "invertible_imp_bijective";

(** Unions of functions -- cf similar theorems on func.ML **)

(*Theorem by KG, proof by LCP*)
goal Perm.thy
    "!!f g. [| f: inj(A,B);  g: inj(C,D);  B Int D = 0 |] ==> \
\           (lam a: A Un C. if(a:A, f`a, g`a)) : inj(A Un C, B Un D)";
by (res_inst_tac [("d","%z. if(z:B, converse(f)`z, converse(g)`z)")]
        lam_injective 1);
by (ALLGOALS 
    (asm_simp_tac (ZF_ss addsimps [inj_is_fun RS apply_type, left_inverse] 
                         setloop (split_tac [expand_if] ORELSE' etac UnE))));
by (fast_tac (ZF_cs addSEs [inj_is_fun RS apply_type] addDs [equals0D]) 1);
qed "inj_disjoint_Un";

goalw Perm.thy [surj_def]
    "!!f g. [| f: surj(A,B);  g: surj(C,D);  A Int C = 0 |] ==> \
\           (f Un g) : surj(A Un C, B Un D)";
by (DEPTH_SOLVE_1 (eresolve_tac [fun_disjoint_apply1, fun_disjoint_apply2] 1
            ORELSE ball_tac 1
            ORELSE (rtac trans 1 THEN atac 2)
            ORELSE step_tac (ZF_cs addIs [fun_disjoint_Un]) 1));
qed "surj_disjoint_Un";

(*A simple, high-level proof; the version for injections follows from it,
  using  f:inj(A,B) <-> f:bij(A,range(f))  *)
goal Perm.thy
    "!!f g. [| f: bij(A,B);  g: bij(C,D);  A Int C = 0;  B Int D = 0 |] ==> \
\           (f Un g) : bij(A Un C, B Un D)";
by (rtac invertible_imp_bijective 1);
by (rtac (converse_Un RS ssubst) 1);
by (REPEAT (ares_tac [fun_disjoint_Un, bij_is_fun, bij_converse_bij] 1));
qed "bij_disjoint_Un";


(** Restrictions as surjections and bijections *)

val prems = goalw Perm.thy [surj_def]
    "f: Pi(A,B) ==> f: surj(A, f``A)";
val rls = apply_equality :: (prems RL [apply_Pair,Pi_type]);
by (fast_tac (ZF_cs addIs rls) 1);
qed "surj_image";

goal Perm.thy "!!f. [| f: Pi(C,B);  A<=C |] ==> restrict(f,A)``A = f``A";
by (rtac equalityI 1);
by (SELECT_GOAL (rewtac restrict_def) 2);
by (REPEAT (eresolve_tac [imageE, apply_equality RS subst] 2
     ORELSE ares_tac [subsetI,lamI,imageI] 2));
by (REPEAT (ares_tac [image_mono,restrict_subset,subset_refl] 1));
qed "restrict_image";

goalw Perm.thy [inj_def]
    "!!f. [| f: inj(A,B);  C<=A |] ==> restrict(f,C): inj(C,B)";
by (safe_tac (ZF_cs addSEs [restrict_type2]));
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp, subsetD,
                          box_equals, restrict] 1));
qed "restrict_inj";

val prems = goal Perm.thy 
    "[| f: Pi(A,B);  C<=A |] ==> restrict(f,C): surj(C, f``C)";
by (rtac (restrict_image RS subst) 1);
by (rtac (restrict_type2 RS surj_image) 3);
by (REPEAT (resolve_tac prems 1));
qed "restrict_surj";

goalw Perm.thy [inj_def,bij_def]
    "!!f. [| f: inj(A,B);  C<=A |] ==> restrict(f,C): bij(C, f``C)";
by (safe_tac ZF_cs);
by (REPEAT (eresolve_tac [bspec RS bspec RS mp, subsetD,
                          box_equals, restrict] 1
     ORELSE ares_tac [surj_is_fun,restrict_surj] 1));
qed "restrict_bij";


(*** Lemmas for Ramsey's Theorem ***)

goalw Perm.thy [inj_def] "!!f. [| f: inj(A,B);  B<=D |] ==> f: inj(A,D)";
by (fast_tac (ZF_cs addSEs [fun_weaken_type]) 1);
qed "inj_weaken_type";

val [major] = goal Perm.thy  
    "[| f: inj(succ(m), A) |] ==> restrict(f,m) : inj(m, A-{f`m})";
by (rtac (major RS restrict_bij RS bij_is_inj RS inj_weaken_type) 1);
by (fast_tac ZF_cs 1);
by (cut_facts_tac [major] 1);
by (rewtac inj_def);
by (fast_tac (ZF_cs addEs [range_type, mem_irrefl] addDs [apply_equality]) 1);
qed "inj_succ_restrict";

goalw Perm.thy [inj_def]
    "!!f. [| f: inj(A,B);  a~:A;  b~:B |]  ==> \
\         cons(<a,b>,f) : inj(cons(a,A), cons(b,B))";
(*cannot use safe_tac: must preserve the implication*)
by (etac CollectE 1);
by (rtac CollectI 1);
by (etac fun_extend 1);
by (REPEAT (ares_tac [ballI] 1));
by (REPEAT_FIRST (eresolve_tac [consE,ssubst]));
(*Assumption ALL w:A. ALL x:A. f`w = f`x --> w=x would make asm_simp_tac loop
  using ZF_ss!  But FOL_ss ignores the assumption...*)
by (ALLGOALS (asm_simp_tac 
              (FOL_ss addsimps [fun_extend_apply2,fun_extend_apply1])));
by (ALLGOALS (fast_tac (ZF_cs addIs [apply_type])));
qed "inj_extend";
