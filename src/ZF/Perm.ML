(*  Title:      ZF/Perm.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The theory underlying permutation groups
  -- Composition of relations, the identity relation
  -- Injections, surjections, bijections
  -- Lemmas for the Schroeder-Bernstein Theorem
*)

(** Surjective function space **)

Goalw [surj_def] "f: surj(A,B) ==> f: A->B";
by (etac CollectD1 1);
qed "surj_is_fun";

Goalw [surj_def] "f : Pi(A,B) ==> f: surj(A,range(f))";
by (blast_tac (claset() addIs [apply_equality, range_of_fun, domain_type]) 1);
qed "fun_is_surj";

Goalw [surj_def] "f: surj(A,B) ==> range(f)=B";
by (best_tac (claset() addIs [apply_Pair] addEs [range_type]) 1);
qed "surj_range";

(** A function with a right inverse is a surjection **)

val prems = goalw Perm.thy [surj_def]
    "[| f: A->B;  !!y. y:B ==> d(y): A;  !!y. y:B ==> f`d(y) = y \
\    |] ==> f: surj(A,B)";
by (blast_tac (claset() addIs prems) 1);
qed "f_imp_surjective";

val prems = Goal
    "[| !!x. x:A ==> c(x): B;           \
\       !!y. y:B ==> d(y): A;           \
\       !!y. y:B ==> c(d(y)) = y        \
\    |] ==> (lam x:A. c(x)) : surj(A,B)";
by (res_inst_tac [("d", "d")] f_imp_surjective 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lam_type]@prems) ));
qed "lam_surjective";

(*Cantor's theorem revisited*)
Goalw [surj_def] "f ~: surj(A,Pow(A))";
by Safe_tac;
by (cut_facts_tac [cantor] 1);
by (fast_tac subset_cs 1);
qed "cantor_surj";


(** Injective function space **)

Goalw [inj_def] "f: inj(A,B) ==> f: A->B";
by (etac CollectD1 1);
qed "inj_is_fun";

(*Good for dealing with sets of pairs, but a bit ugly in use [used in AC]*)
Goalw [inj_def]
    "[| <a,b>:f;  <c,b>:f;  f: inj(A,B) |] ==> a=c";
by (REPEAT (eresolve_tac [asm_rl, Pair_mem_PiE, CollectE] 1));
by (Blast_tac 1);
qed "inj_equality";

Goalw [inj_def] "[| f:inj(A,B);  a:A;  b:A;  f`a=f`b |] ==> a=b";
by (Blast_tac 1);
val inj_apply_equality = result();

(** A function with a left inverse is an injection **)

Goal "[| f: A->B;  ALL x:A. d(f`x)=x |] ==> f: inj(A,B)";
by (asm_simp_tac (simpset() addsimps [inj_def]) 1);
by (blast_tac (claset() addIs [subst_context RS box_equals]) 1);
bind_thm ("f_imp_injective", ballI RSN (2,result()));

val prems = Goal
    "[| !!x. x:A ==> c(x): B;           \
\       !!x. x:A ==> d(c(x)) = x        \
\    |] ==> (lam x:A. c(x)) : inj(A,B)";
by (res_inst_tac [("d", "d")] f_imp_injective 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lam_type]@prems)));
qed "lam_injective";

(** Bijections **)

Goalw [bij_def] "f: bij(A,B) ==> f: inj(A,B)";
by (etac IntD1 1);
qed "bij_is_inj";

Goalw [bij_def] "f: bij(A,B) ==> f: surj(A,B)";
by (etac IntD2 1);
qed "bij_is_surj";

(* f: bij(A,B) ==> f: A->B *)
bind_thm ("bij_is_fun", bij_is_inj RS inj_is_fun);

val prems = goalw Perm.thy [bij_def]
    "[| !!x. x:A ==> c(x): B;           \
\       !!y. y:B ==> d(y): A;           \
\       !!x. x:A ==> d(c(x)) = x;       \
\       !!y. y:B ==> c(d(y)) = y        \
\    |] ==> (lam x:A. c(x)) : bij(A,B)";
by (REPEAT (ares_tac (prems @ [IntI, lam_injective, lam_surjective]) 1));
qed "lam_bijective";

Goal "(ALL y : x. EX! y'. f(y') = f(y))  \
\     ==> (lam z:{f(y). y:x}. THE y. f(y) = z) : bij({f(y). y:x}, x)";
by (res_inst_tac [("d","f")] lam_bijective 1);
by (auto_tac (claset(),
	      simpset() addsimps [the_equality2]));
qed "RepFun_bijective";


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

Goalw [id_def] "id(A) : A->A";  
by (rtac lam_type 1);
by (assume_tac 1);
qed "id_type";

Goalw [id_def] "x:A ==> id(A)`x = x";
by (Asm_simp_tac 1);
qed "id_conv";

Addsimps [id_conv];

val [prem] = goalw Perm.thy [id_def] "A<=B ==> id(A) <= id(B)";
by (rtac (prem RS lam_mono) 1);
qed "id_mono";

Goalw [inj_def,id_def] "A<=B ==> id(A): inj(A,B)";
by (REPEAT (ares_tac [CollectI,lam_type] 1));
by (etac subsetD 1 THEN assume_tac 1);
by (Simp_tac 1);
qed "id_subset_inj";

val id_inj = subset_refl RS id_subset_inj;

Goalw [id_def,surj_def] "id(A): surj(A,A)";
by (blast_tac (claset() addIs [lam_type, beta]) 1);
qed "id_surj";

Goalw [bij_def] "id(A): bij(A,A)";
by (blast_tac (claset() addIs [id_inj, id_surj]) 1);
qed "id_bij";

Goalw [id_def] "A <= B <-> id(A) : A->B";
by (fast_tac (claset() addSIs [lam_type] addDs [apply_type] 
                      addss (simpset())) 1);
qed "subset_iff_id";


(*** Converse of a function ***)

Goalw [inj_def] "f: inj(A,B) ==> converse(f) : range(f)->A";
by (asm_simp_tac (simpset() addsimps [Pi_iff, function_def]) 1);
by (etac CollectE 1);
by (asm_simp_tac (simpset() addsimps [apply_iff]) 1);
by (blast_tac (claset() addDs [fun_is_rel]) 1);
qed "inj_converse_fun";

(** Equations for converse(f) **)

(*The premises are equivalent to saying that f is injective...*) 
Goal "[| f: A->B;  converse(f): C->A;  a: A |] ==> converse(f)`(f`a) = a";
by (blast_tac (claset() addIs [apply_Pair, apply_equality, converseI]) 1);
qed "left_inverse_lemma";

Goal "[| f: inj(A,B);  a: A |] ==> converse(f)`(f`a) = a";
by (blast_tac (claset() addIs [left_inverse_lemma, inj_converse_fun,
			       inj_is_fun]) 1);
qed "left_inverse";

val left_inverse_bij = bij_is_inj RS left_inverse;

Goal "[| f: A->B;  converse(f): C->A;  b: C |] ==> f`(converse(f)`b) = b";
by (rtac (apply_Pair RS (converseD RS apply_equality)) 1);
by (REPEAT (assume_tac 1));
qed "right_inverse_lemma";

(*Should the premises be f:surj(A,B), b:B for symmetry with left_inverse?
  No: they would not imply that converse(f) was a function! *)
Goal "[| f: inj(A,B);  b: range(f) |] ==> f`(converse(f)`b) = b";
by (rtac right_inverse_lemma 1);
by (REPEAT (ares_tac [inj_converse_fun,inj_is_fun] 1));
qed "right_inverse";

Addsimps [left_inverse, right_inverse];


Goal "[| f: bij(A,B);  b: B |] ==> f`(converse(f)`b) = b";
by (force_tac (claset(), simpset() addsimps [bij_def, surj_range]) 1);
qed "right_inverse_bij";

(** Converses of injections, surjections, bijections **)

Goal "f: inj(A,B) ==> converse(f): inj(range(f), A)";
by (rtac f_imp_injective 1);
by (etac inj_converse_fun 1);
by (rtac right_inverse 1);
by (REPEAT (assume_tac 1));
qed "inj_converse_inj";

Goal "f: inj(A,B) ==> converse(f): surj(range(f), A)";
by (blast_tac (claset() addIs [f_imp_surjective, inj_converse_fun, 
			       left_inverse,
			       inj_is_fun, range_of_fun RS apply_type]) 1);
qed "inj_converse_surj";

Goalw [bij_def] "f: bij(A,B) ==> converse(f): bij(B,A)";
by (fast_tac (claset() addEs [surj_range RS subst, inj_converse_inj,
			      inj_converse_surj]) 1);
qed "bij_converse_bij";
(*Adding this as an SI seems to cause looping*)

AddTCs [bij_converse_bij];


(** Composition of two relations **)

(*The inductive definition package could derive these theorems for (r O s)*)

Goalw [comp_def] "[| <a,b>:s; <b,c>:r |] ==> <a,c> : r O s";
by (Blast_tac 1);
qed "compI";

val prems = goalw Perm.thy [comp_def]
    "[| xz : r O s;  \
\       !!x y z. [| xz=<x,z>;  <x,y>:s;  <y,z>:r |] ==> P \
\    |] ==> P";
by (cut_facts_tac prems 1);
by (REPEAT (eresolve_tac [CollectE, exE, conjE] 1 ORELSE ares_tac prems 1));
qed "compE";

bind_thm ("compEpair", 
    rule_by_tactic (REPEAT_FIRST (etac Pair_inject ORELSE' bound_hyp_subst_tac)
                    THEN prune_params_tac)
        (read_instantiate [("xz","<a,c>")] compE));

AddSIs [idI];
AddIs  [compI];
AddSEs [compE,idE];

Goal "converse(R O S) = converse(S) O converse(R)";
by (Blast_tac 1);
qed "converse_comp";


(** Domain and Range -- see Suppes, section 3.1 **)

(*Boyer et al., Set Theory in First-Order Logic, JAR 2 (1986), 287-327*)
Goal "range(r O s) <= range(r)";
by (Blast_tac 1);
qed "range_comp";

Goal "domain(r) <= range(s) ==> range(r O s) = range(r)";
by (rtac (range_comp RS equalityI) 1);
by (Blast_tac 1);
qed "range_comp_eq";

Goal "domain(r O s) <= domain(s)";
by (Blast_tac 1);
qed "domain_comp";

Goal "range(s) <= domain(r) ==> domain(r O s) = domain(s)";
by (rtac (domain_comp RS equalityI) 1);
by (Blast_tac 1);
qed "domain_comp_eq";

Goal "(r O s)``A = r``(s``A)";
by (Blast_tac 1);
qed "image_comp";


(** Other results **)

Goal "[| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)";
by (Blast_tac 1);
qed "comp_mono";

(*composition preserves relations*)
Goal "[| s<=A*B;  r<=B*C |] ==> (r O s) <= A*C";
by (Blast_tac 1);
qed "comp_rel";

(*associative law for composition*)
Goal "(r O s) O t = r O (s O t)";
by (Blast_tac 1);
qed "comp_assoc";

(*left identity of composition; provable inclusions are
        id(A) O r <= r       
  and   [| r<=A*B; B<=C |] ==> r <= id(C) O r *)
Goal "r<=A*B ==> id(B) O r = r";
by (Blast_tac 1);
qed "left_comp_id";

(*right identity of composition; provable inclusions are
        r O id(A) <= r
  and   [| r<=A*B; A<=C |] ==> r <= r O id(C) *)
Goal "r<=A*B ==> r O id(A) = r";
by (Blast_tac 1);
qed "right_comp_id";


(** Composition preserves functions, injections, and surjections **)

Goalw [function_def]
    "[| function(g);  function(f) |] ==> function(f O g)";
by (Blast_tac 1);
qed "comp_function";

Goal "[| g: A->B;  f: B->C |] ==> (f O g) : A->C";
by (asm_full_simp_tac
    (simpset() addsimps [Pi_def, comp_function, Pow_iff, comp_rel]
           setloop etac conjE) 1);
by (stac (range_rel_subset RS domain_comp_eq) 1 THEN assume_tac 2);
by (Blast_tac 1);
qed "comp_fun";

Goal "[| g: A->B;  f: B->C;  a:A |] ==> (f O g)`a = f`(g`a)";
by (REPEAT (ares_tac [comp_fun,apply_equality,compI,
                      apply_Pair,apply_type] 1));
qed "comp_fun_apply";

Addsimps [comp_fun_apply];

(*Simplifies compositions of lambda-abstractions*)
val [prem] = Goal
    "[| !!x. x:A ==> b(x): B    \
\    |] ==> (lam y:B. c(y)) O (lam x:A. b(x)) = (lam x:A. c(b(x)))";
by (rtac fun_extension 1);
by (rtac comp_fun 1);
by (rtac lam_funtype 2);
by (typecheck_tac (tcset() addTCs [prem]));
by (asm_simp_tac (simpset() 
                   setSolver 
                   type_solver_tac (tcset() addTCs [prem, lam_funtype])) 1);
qed "comp_lam";

Goal "[| g: inj(A,B);  f: inj(B,C) |] ==> (f O g) : inj(A,C)";
by (res_inst_tac [("d", "%y. converse(g) ` (converse(f) ` y)")]
    f_imp_injective 1);
by (REPEAT (ares_tac [comp_fun, inj_is_fun] 1));
by (asm_simp_tac (simpset()  
		  setSolver
		  type_solver_tac (tcset() addTCs [inj_is_fun])) 1);
qed "comp_inj";

Goalw [surj_def]
    "[| g: surj(A,B);  f: surj(B,C) |] ==> (f O g) : surj(A,C)";
by (blast_tac (claset() addSIs [comp_fun,comp_fun_apply]) 1);
qed "comp_surj";

Goalw [bij_def]
    "[| g: bij(A,B);  f: bij(B,C) |] ==> (f O g) : bij(A,C)";
by (blast_tac (claset() addIs [comp_inj,comp_surj]) 1);
qed "comp_bij";


(** Dual properties of inj and surj -- useful for proofs from
    D Pastre.  Automatic theorem proving in set theory. 
    Artificial Intelligence, 10:1--27, 1978. **)

Goalw [inj_def]
    "[| (f O g): inj(A,C);  g: A->B;  f: B->C |] ==> g: inj(A,B)";
by Safe_tac;
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp] 1));
by (asm_simp_tac (simpset() ) 1);
qed "comp_mem_injD1";

Goalw [inj_def,surj_def]
    "[| (f O g): inj(A,C);  g: surj(A,B);  f: B->C |] ==> f: inj(B,C)";
by Safe_tac;
by (res_inst_tac [("x1", "x")] (bspec RS bexE) 1);
by (eres_inst_tac [("x1", "w")] (bspec RS bexE) 3);
by (REPEAT (assume_tac 1));
by Safe_tac;
by (res_inst_tac [("t", "op `(g)")] subst_context 1);
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp] 1));
by (asm_simp_tac (simpset() ) 1);
qed "comp_mem_injD2";

Goalw [surj_def]
    "[| (f O g): surj(A,C);  g: A->B;  f: B->C |] ==> f: surj(B,C)";
by (blast_tac (claset() addSIs [comp_fun_apply RS sym, apply_funtype]) 1);
qed "comp_mem_surjD1";

Goal "[| (f O g)`a = c;  g: A->B;  f: B->C;  a:A |] ==> f`(g`a) = c";
by (REPEAT (ares_tac [comp_fun_apply RS sym RS trans] 1));
qed "comp_fun_applyD";

Goalw [inj_def,surj_def]
    "[| (f O g): surj(A,C);  g: A->B;  f: inj(B,C) |] ==> g: surj(A,B)";
by Safe_tac;
by (eres_inst_tac [("x1", "f`y")] (bspec RS bexE) 1);
by (REPEAT (ares_tac [apply_type] 1 ORELSE dtac comp_fun_applyD 1));
by (blast_tac (claset() addSIs [apply_funtype]) 1);
qed "comp_mem_surjD2";


(** inverses of composition **)

(*left inverse of composition; one inclusion is
        f: A->B ==> id(A) <= converse(f) O f *)
Goalw [inj_def] "f: inj(A,B) ==> converse(f) O f = id(A)";
by (fast_tac (claset() addIs [apply_Pair] 
                      addEs [domain_type]
               addss (simpset() addsimps [apply_iff])) 1);
qed "left_comp_inverse";

(*right inverse of composition; one inclusion is
                f: A->B ==> f O converse(f) <= id(B) 
*)
val [prem] = goalw Perm.thy [surj_def]
    "f: surj(A,B) ==> f O converse(f) = id(B)";
val appfD = (prem RS CollectD1) RSN (3,apply_equality2);
by (cut_facts_tac [prem] 1);
by (rtac equalityI 1);
by (best_tac (claset() addEs [domain_type, range_type, make_elim appfD]) 1);
by (blast_tac (claset() addIs [apply_Pair]) 1);
qed "right_comp_inverse";

(** Proving that a function is a bijection **)

Goalw [id_def]
    "[| f: A->B;  g: B->A |] ==> f O g = id(B) <-> (ALL y:B. f`(g`y)=y)";
by Safe_tac;
by (dres_inst_tac [("t", "%h. h`y ")] subst_context 1);
by (Asm_full_simp_tac 1);
by (rtac fun_extension 1);
by (REPEAT (ares_tac [comp_fun, lam_type] 1));
by Auto_tac;
qed "comp_eq_id_iff";

Goalw [bij_def]
    "[| f: A->B;  g: B->A;  f O g = id(B);  g O f = id(A) |] ==> f : bij(A,B)";
by (asm_full_simp_tac (simpset() addsimps [comp_eq_id_iff]) 1);
by (REPEAT (ares_tac [conjI, f_imp_injective, f_imp_surjective] 1
       ORELSE eresolve_tac [bspec, apply_type] 1));
qed "fg_imp_bijective";

Goal "[| f: A->A;  f O f = id(A) |] ==> f : bij(A,A)";
by (REPEAT (ares_tac [fg_imp_bijective] 1));
qed "nilpotent_imp_bijective";

Goal "[| converse(f): B->A;  f: A->B |] ==> f : bij(A,B)";
by (asm_simp_tac (simpset() addsimps [fg_imp_bijective, comp_eq_id_iff, 
                                  left_inverse_lemma, right_inverse_lemma]) 1);
qed "invertible_imp_bijective";

(** Unions of functions -- cf similar theorems on func.ML **)

(*Theorem by KG, proof by LCP*)
Goal "[| f: inj(A,B);  g: inj(C,D);  B Int D = 0 |] \
\     ==> (lam a: A Un C. if a:A then f`a else g`a) : inj(A Un C, B Un D)";
by (res_inst_tac [("d","%z. if z:B then converse(f)`z else converse(g)`z")]
        lam_injective 1);
by (auto_tac (claset(),
	      simpset() addsimps [inj_is_fun RS apply_type]));
by (blast_tac (claset() addIs [inj_is_fun RS apply_type]) 1);
qed "inj_disjoint_Un";

Goalw [surj_def]
    "[| f: surj(A,B);  g: surj(C,D);  A Int C = 0 |]  \
\    ==> (f Un g) : surj(A Un C, B Un D)";
by (blast_tac (claset() addIs [fun_disjoint_apply1, fun_disjoint_apply2,
			      fun_disjoint_Un, trans]) 1);
qed "surj_disjoint_Un";

(*A simple, high-level proof; the version for injections follows from it,
  using  f:inj(A,B) <-> f:bij(A,range(f))  *)
Goal "[| f: bij(A,B);  g: bij(C,D);  A Int C = 0;  B Int D = 0 |] \
\     ==> (f Un g) : bij(A Un C, B Un D)";
by (rtac invertible_imp_bijective 1);
by (stac converse_Un 1);
by (REPEAT (ares_tac [fun_disjoint_Un, bij_is_fun, bij_converse_bij] 1));
qed "bij_disjoint_Un";


(** Restrictions as surjections and bijections *)

val prems = goalw Perm.thy [surj_def]
    "f: Pi(A,B) ==> f: surj(A, f``A)";
val rls = apply_equality :: (prems RL [apply_Pair,Pi_type]);
by (fast_tac (claset() addIs rls) 1);
qed "surj_image";

Goal "[| f: Pi(C,B);  A<=C |] ==> restrict(f,A)``A = f``A";
by (rtac equalityI 1);
by (SELECT_GOAL (rewtac restrict_def) 2);
by (REPEAT (eresolve_tac [imageE, apply_equality RS subst] 2
     ORELSE ares_tac [subsetI,lamI,imageI] 2));
by (REPEAT (ares_tac [image_mono,restrict_subset,subset_refl] 1));
qed "restrict_image";

Goalw [inj_def]
    "[| f: inj(A,B);  C<=A |] ==> restrict(f,C): inj(C,B)";
by (safe_tac (claset() addSEs [restrict_type2]));
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp, subsetD,
                          box_equals, restrict] 1));
qed "restrict_inj";

Goal "[| f: Pi(A,B);  C<=A |] ==> restrict(f,C): surj(C, f``C)";
by (rtac (restrict_image RS subst) 1);
by (rtac (restrict_type2 RS surj_image) 3);
by (REPEAT (assume_tac 1));
qed "restrict_surj";

Goalw [inj_def,bij_def]
    "[| f: inj(A,B);  C<=A |] ==> restrict(f,C): bij(C, f``C)";
by (blast_tac (claset() addSIs [restrict, restrict_surj]
		       addIs [box_equals, surj_is_fun]) 1);
qed "restrict_bij";


(*** Lemmas for Ramsey's Theorem ***)

Goalw [inj_def] "[| f: inj(A,B);  B<=D |] ==> f: inj(A,D)";
by (blast_tac (claset() addIs [fun_weaken_type]) 1);
qed "inj_weaken_type";

val [major] = goal Perm.thy  
    "[| f: inj(succ(m), A) |] ==> restrict(f,m) : inj(m, A-{f`m})";
by (rtac (major RS restrict_bij RS bij_is_inj RS inj_weaken_type) 1);
by (Blast_tac 1);
by (cut_facts_tac [major] 1);
by (rewtac inj_def);
by (fast_tac (claset() addEs [range_type, mem_irrefl] 
	              addDs [apply_equality]) 1);
qed "inj_succ_restrict";

Goalw [inj_def]
    "[| f: inj(A,B);  a~:A;  b~:B |] \
\    ==> cons(<a,b>,f) : inj(cons(a,A), cons(b,B))";
by (force_tac (claset() addIs [apply_type],
               simpset() addsimps [fun_extend, fun_extend_apply2,
						fun_extend_apply1]) 1);
qed "inj_extend";

