(*  Title: 	ZF/perm.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For perm.thy.  The theory underlying permutation groups
  -- Composition of relations, the identity relation
  -- Injections, surjections, bijections
  -- Lemmas for the Schroeder-Bernstein Theorem
*)

open Perm;

(** Surjective function space **)

goalw Perm.thy [surj_def] "!!f A B. f: surj(A,B) ==> f: A->B";
by (etac CollectD1 1);
val surj_is_fun = result();

goalw Perm.thy [surj_def] "!!f A B. f : Pi(A,B) ==> f: surj(A,range(f))";
by (fast_tac (ZF_cs addIs [apply_equality] 
		    addEs [range_of_fun,domain_type]) 1);
val fun_is_surj = result();

goalw Perm.thy [surj_def] "!!f A B. f: surj(A,B) ==> range(f)=B";
by (best_tac (ZF_cs addIs [equalityI,apply_Pair] addEs [range_type]) 1);
val surj_range = result();


(** Injective function space **)

goalw Perm.thy [inj_def] "!!f A B. f: inj(A,B) ==> f: A->B";
by (etac CollectD1 1);
val inj_is_fun = result();

goalw Perm.thy [inj_def]
    "!!f A B. [| <a,b>:f;  <c,b>:f;  f: inj(A,B) |] ==> a=c";
by (REPEAT (eresolve_tac [asm_rl, Pair_mem_PiE, CollectE] 1));
by (fast_tac ZF_cs 1);
val inj_equality = result();

(** Bijections -- simple lemmas but no intro/elim rules -- use unfolding **)

goalw Perm.thy [bij_def] "!!f A B. f: bij(A,B) ==> f: inj(A,B)";
by (etac IntD1 1);
val bij_is_inj = result();

goalw Perm.thy [bij_def] "!!f A B. f: bij(A,B) ==> f: surj(A,B)";
by (etac IntD2 1);
val bij_is_surj = result();

(* f: bij(A,B) ==> f: A->B *)
val bij_is_fun = standard (bij_is_inj RS inj_is_fun);

(** Identity function **)

val [prem] = goalw Perm.thy [id_def] "a:A ==> <a,a> : id(A)";  
by (rtac (prem RS lamI) 1);
val idI = result();

val major::prems = goalw Perm.thy [id_def]
    "[| p: id(A);  !!x.[| x:A; p=<x,x> |] ==> P  \
\    |] ==>  P";  
by (rtac (major RS lamE) 1);
by (REPEAT (ares_tac prems 1));
val idE = result();

goalw Perm.thy [id_def] "id(A) : A->A";  
by (rtac lam_type 1);
by (assume_tac 1);
val id_type = result();

val [prem] = goalw Perm.thy [id_def] "A<=B ==> id(A) <= id(B)";
by (rtac (prem RS lam_mono) 1);
val id_mono = result();

goalw Perm.thy [inj_def,id_def] "id(A): inj(A,A)";
by (REPEAT (ares_tac [CollectI,lam_type] 1));
by (SIMP_TAC ZF_ss 1);
val id_inj = result();

goalw Perm.thy [id_def,surj_def] "id(A): surj(A,A)";
by (fast_tac (ZF_cs addIs [lam_type,beta]) 1);
val id_surj = result();

goalw Perm.thy [bij_def] "id(A): bij(A,A)";
by (fast_tac (ZF_cs addIs [id_inj,id_surj]) 1);
val id_bij = result();


(** Converse of a relation **)

val [prem] = goal Perm.thy "f: inj(A,B) ==> converse(f) : range(f)->A";
by (rtac (prem RS inj_is_fun RS PiE) 1);
by (rtac (converse_type RS PiI) 1);
by (fast_tac ZF_cs 1);
by (fast_tac (ZF_cs addEs [prem RSN (3,inj_equality)]) 1);
by flexflex_tac;
val inj_converse_fun = result();

val prems = goalw Perm.thy [surj_def]
    "f: inj(A,B) ==> converse(f): surj(range(f), A)";
by (fast_tac (ZF_cs addIs (prems@[inj_converse_fun,apply_Pair,apply_equality,
			 converseI,inj_is_fun])) 1);
val inj_converse_surj = result();

(*The premises are equivalent to saying that f is injective...*) 
val prems = goal Perm.thy
    "[| f: A->B;  converse(f): C->A;  a: A |] ==> converse(f)`(f`a) = a";
by (fast_tac (ZF_cs addIs (prems@[apply_Pair,apply_equality,converseI])) 1);
val left_inverse_lemma = result();

val prems = goal Perm.thy
    "[| f: inj(A,B);  a: A |] ==> converse(f)`(f`a) = a";
by (fast_tac (ZF_cs addIs (prems@
       [left_inverse_lemma,inj_converse_fun,inj_is_fun])) 1);
val left_inverse = result();

val prems = goal Perm.thy
    "[| f: A->B;  converse(f): C->A;  b: C |] ==> f`(converse(f)`b) = b";
by (rtac (apply_Pair RS (converseD RS apply_equality)) 1);
by (REPEAT (resolve_tac prems 1));
val right_inverse_lemma = result();

val prems = goal Perm.thy
    "[| f: inj(A,B);  b: range(f) |] ==> f`(converse(f)`b) = b";
by (rtac right_inverse_lemma 1);
by (REPEAT (resolve_tac (prems@ [inj_converse_fun,inj_is_fun]) 1));
val right_inverse = result();

val prems = goal Perm.thy
    "f: inj(A,B) ==> converse(f): inj(range(f), A)";
bw inj_def;  (*rewrite subgoal but not prems!!*)
by (cut_facts_tac prems 1);
by (safe_tac ZF_cs);
(*apply f to both sides and simplify using right_inverse
  -- could also use  etac[subst_context RS box_equals]  in this proof *)
by (rtac simp_equals 2);
by (REPEAT (eresolve_tac [inj_converse_fun, right_inverse RS sym, ssubst] 1
     ORELSE ares_tac [refl,rangeI] 1));
val inj_converse_inj = result();

goalw Perm.thy [bij_def] "!!f A B. f: bij(A,B) ==> converse(f): bij(B,A)";
by (etac IntE 1);
by (eresolve_tac [(surj_range RS subst)] 1);
by (rtac IntI 1);
by (etac inj_converse_inj 1);
by (etac inj_converse_surj 1);
val bij_converse_bij = result();


(** Composition of two relations **)

(*The inductive definition package could derive these theorems for R o S*)

goalw Perm.thy [comp_def] "!!r s. [| <a,b>:s; <b,c>:r |] ==> <a,c> : r O s";
by (fast_tac ZF_cs 1);
val compI = result();

val prems = goalw Perm.thy [comp_def]
    "[| xz : r O s;  \
\       !!x y z. [| xz=<x,z>;  <x,y>:s;  <y,z>:r |] ==> P \
\    |] ==> P";
by (cut_facts_tac prems 1);
by (REPEAT (eresolve_tac [CollectE, exE, conjE] 1 ORELSE ares_tac prems 1));
val compE = result();

val compEpair = 
    rule_by_tactic (REPEAT_FIRST (etac Pair_inject ORELSE' bound_hyp_subst_tac)
		    THEN prune_params_tac)
	(read_instantiate [("xz","<a,c>")] compE);

val comp_cs = ZF_cs addIs [compI,idI] addSEs [compE,idE];

(** Domain and Range -- see Suppes, section 3.1 **)

(*Boyer et al., Set Theory in First-Order Logic, JAR 2 (1986), 287-327*)
goal Perm.thy "range(r O s) <= range(r)";
by (fast_tac comp_cs 1);
val range_comp = result();

goal Perm.thy "!!r s. domain(r) <= range(s) ==> range(r O s) = range(r)";
by (rtac (range_comp RS equalityI) 1);
by (fast_tac comp_cs 1);
val range_comp_eq = result();

goal Perm.thy "domain(r O s) <= domain(s)";
by (fast_tac comp_cs 1);
val domain_comp = result();

goal Perm.thy "!!r s. range(s) <= domain(r) ==> domain(r O s) = domain(s)";
by (rtac (domain_comp RS equalityI) 1);
by (fast_tac comp_cs 1);
val domain_comp_eq = result();

(** Other results **)

goal Perm.thy "!!r s. [| r'<=r; s'<=s |] ==> (r' O s') <= (r O s)";
by (fast_tac comp_cs 1);
val comp_mono = result();

(*composition preserves relations*)
goal Perm.thy "!!r s. [| s<=A*B;  r<=B*C |] ==> (r O s) <= A*C";
by (fast_tac comp_cs 1);
val comp_rel = result();

(*associative law for composition*)
goal Perm.thy "(r O s) O t = r O (s O t)";
by (fast_tac (comp_cs addIs [equalityI]) 1);
val comp_assoc = result();

(*left identity of composition; provable inclusions are
        id(A) O r <= r       
  and   [| r<=A*B; B<=C |] ==> r <= id(C) O r *)
goal Perm.thy "!!r A B. r<=A*B ==> id(B) O r = r";
by (fast_tac (comp_cs addIs [equalityI]) 1);
val left_comp_id = result();

(*right identity of composition; provable inclusions are
        r O id(A) <= r
  and   [| r<=A*B; A<=C |] ==> r <= r O id(C) *)
goal Perm.thy "!!r A B. r<=A*B ==> r O id(A) = r";
by (fast_tac (comp_cs addIs [equalityI]) 1);
val right_comp_id = result();


(** Composition preserves functions, injections, and surjections **)

goal Perm.thy "!!f g. [| g: A->B;  f: B->C |] ==> (f O g) : A->C";
by (REPEAT (ares_tac [PiI,comp_rel,ex1I,compI] 1
     ORELSE eresolve_tac [fun_is_rel,apply_Pair,apply_type] 1));
by (fast_tac (comp_cs addDs [apply_equality]) 1);
val comp_func = result();

goal Perm.thy "!!f g. [| g: A->B;  f: B->C;  a:A |] ==> (f O g)`a = f`(g`a)";
by (REPEAT (ares_tac [comp_func,apply_equality,compI,
		      apply_Pair,apply_type] 1));
val comp_func_apply = result();

goalw Perm.thy [inj_def]
    "!!f g. [| g: inj(A,B);  f: inj(B,C) |] ==> (f O g) : inj(A,C)";
by (REPEAT (eresolve_tac [bspec RS bspec RS mp, box_equals] 1
     ORELSE step_tac (ZF_cs addSIs [comp_func,apply_type,comp_func_apply]) 1));
val comp_inj = result();

goalw Perm.thy [surj_def]
    "!!f g. [| g: surj(A,B);  f: surj(B,C) |] ==> (f O g) : surj(A,C)";
by (best_tac (ZF_cs addSIs [comp_func,comp_func_apply]) 1);
val comp_surj = result();

goalw Perm.thy [bij_def]
    "!!f g. [| g: bij(A,B);  f: bij(B,C) |] ==> (f O g) : bij(A,C)";
by (fast_tac (ZF_cs addIs [comp_inj,comp_surj]) 1);
val comp_bij = result();


(** Dual properties of inj and surj -- useful for proofs from
    D Pastre.  Automatic theorem proving in set theory. 
    Artificial Intelligence, 10:1--27, 1978. **)

goalw Perm.thy [inj_def]
    "!!f g. [| (f O g): inj(A,C);  g: A->B;  f: B->C |] ==> g: inj(A,B)";
by (safe_tac comp_cs);
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp] 1));
by (ASM_SIMP_TAC (ZF_ss addrews [comp_func_apply]) 1);
val comp_mem_injD1 = result();

goalw Perm.thy [inj_def,surj_def]
    "!!f g. [| (f O g): inj(A,C);  g: surj(A,B);  f: B->C |] ==> f: inj(B,C)";
by (safe_tac comp_cs);
by (res_inst_tac [("x1", "x")] (bspec RS bexE) 1);
by (eres_inst_tac [("x1", "w")] (bspec RS bexE) 3);
by (REPEAT (assume_tac 1));
by (safe_tac (comp_cs addSIs ZF_congs));
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp] 1));
by (ASM_SIMP_TAC (ZF_ss addrews [comp_func_apply]) 1);
val comp_mem_injD2 = result();

goalw Perm.thy [surj_def]
    "!!f g. [| (f O g): surj(A,C);  g: A->B;  f: B->C |] ==> f: surj(B,C)";
by (fast_tac (comp_cs addSIs [comp_func_apply RS sym, apply_type]) 1);
val comp_mem_surjD1 = result();

goal Perm.thy
    "!!f g. [| (f O g)`a = c;  g: A->B;  f: B->C;  a:A |] ==> f`(g`a) = c";
by (REPEAT (ares_tac [comp_func_apply RS sym RS trans] 1));
val comp_func_applyD = result();

goalw Perm.thy [inj_def,surj_def]
    "!!f g. [| (f O g): surj(A,C);  g: A->B;  f: inj(B,C) |] ==> g: surj(A,B)";
by (safe_tac comp_cs);
by (eres_inst_tac [("x1", "f`y")] (bspec RS bexE) 1);
by (REPEAT (ares_tac [apply_type] 1 ORELSE dtac comp_func_applyD 1));
by (best_tac (comp_cs addSIs [apply_type]) 1);
val comp_mem_surjD2 = result();


(** inverses of composition **)

(*left inverse of composition; one inclusion is
        f: A->B ==> id(A) <= converse(f) O f *)
val [prem] = goal Perm.thy
    "f: inj(A,B) ==> converse(f) O f = id(A)";
val injfD = prem RSN (3,inj_equality);
by (cut_facts_tac [prem RS inj_is_fun] 1);
by (fast_tac (comp_cs addIs [equalityI,apply_Pair] 
		      addEs [domain_type, make_elim injfD]) 1);
val left_comp_inverse = result();

(*right inverse of composition; one inclusion is
        f: A->B ==> f O converse(f) <= id(B) *)
val [prem] = goalw Perm.thy [surj_def]
    "f: surj(A,B) ==> f O converse(f) = id(B)";
val appfD = (prem RS CollectD1) RSN (3,apply_equality2);
by (cut_facts_tac [prem] 1);
by (rtac equalityI 1);
by (best_tac (comp_cs addEs [domain_type, range_type, make_elim appfD]) 1);
by (best_tac (comp_cs addIs [apply_Pair]) 1);
val right_comp_inverse = result();

(*Injective case applies converse(f) to both sides then simplifies
    using left_inverse_lemma*)
goalw Perm.thy [bij_def,inj_def,surj_def]
    "!!f A B. [| converse(f): B->A;  f: A->B |] ==> f : bij(A,B)";
val cf_cong = read_instantiate_sg (sign_of Perm.thy)
                [("t","%x.?f`x")]   subst_context;
by (fast_tac (ZF_cs addIs [left_inverse_lemma, right_inverse_lemma, apply_type]
		    addEs [cf_cong RS box_equals]) 1);
val invertible_imp_bijective = result();

(** Unions of functions -- cf similar theorems on func.ML **)

goal Perm.thy "converse(r Un s) = converse(r) Un converse(s)";
by (rtac equalityI 1);
by (DEPTH_SOLVE_1 
      (resolve_tac [Un_least,converse_mono, Un_upper1,Un_upper2] 2));
by (fast_tac ZF_cs 1);
val converse_of_Un = result();

goalw Perm.thy [surj_def]
    "!!f g. [| f: surj(A,B);  g: surj(C,D);  A Int C = 0 |] ==> \
\           (f Un g) : surj(A Un C, B Un D)";
by (DEPTH_SOLVE_1 (eresolve_tac [fun_disjoint_apply1, fun_disjoint_apply2] 1
	    ORELSE ball_tac 1
	    ORELSE (rtac trans 1 THEN atac 2)
	    ORELSE step_tac (ZF_cs addIs [fun_disjoint_Un]) 1));
val surj_disjoint_Un = result();

(*A simple, high-level proof; the version for injections follows from it,
  using  f:inj(A,B)<->f:bij(A,range(f))  *)
goal Perm.thy
    "!!f g. [| f: bij(A,B);  g: bij(C,D);  A Int C = 0;  B Int D = 0 |] ==> \
\           (f Un g) : bij(A Un C, B Un D)";
by (rtac invertible_imp_bijective 1);
by (rtac (converse_of_Un RS ssubst) 1);
by (REPEAT (ares_tac [fun_disjoint_Un, bij_is_fun, bij_converse_bij] 1));
val bij_disjoint_Un = result();


(** Restrictions as surjections and bijections *)

val prems = goalw Perm.thy [surj_def]
    "f: Pi(A,B) ==> f: surj(A, f``A)";
val rls = apply_equality :: (prems RL [apply_Pair,Pi_type]);
by (fast_tac (ZF_cs addIs rls) 1);
val surj_image = result();

goal Perm.thy 
    "!!f. [| f: Pi(C,B);  A<=C |] ==> restrict(f,A)``A = f``A";
by (rtac equalityI 1);
by (SELECT_GOAL (rewtac restrict_def) 2);
by (REPEAT (eresolve_tac [imageE, apply_equality RS subst] 2
     ORELSE ares_tac [subsetI,lamI,imageI] 2));
by (REPEAT (ares_tac [image_mono,restrict_subset,subset_refl] 1));
val restrict_image = result();

goalw Perm.thy [inj_def]
    "!!f. [| f: inj(A,B);  C<=A |] ==> restrict(f,C): inj(C,B)";
by (safe_tac (ZF_cs addSEs [restrict_type2]));
by (REPEAT (eresolve_tac [asm_rl, bspec RS bspec RS mp, subsetD,
                          box_equals, restrict] 1));
val restrict_inj = result();

val prems = goal Perm.thy 
    "[| f: Pi(A,B);  C<=A |] ==> restrict(f,C): surj(C, f``C)";
by (rtac (restrict_image RS subst) 1);
by (rtac (restrict_type2 RS surj_image) 3);
by (REPEAT (resolve_tac prems 1));
val restrict_surj = result();

goalw Perm.thy [inj_def,bij_def]
    "!!f. [| f: inj(A,B);  C<=A |] ==> restrict(f,C): bij(C, f``C)";
by (safe_tac ZF_cs);
by (REPEAT (eresolve_tac [bspec RS bspec RS mp, subsetD,
                          box_equals, restrict] 1
     ORELSE ares_tac [surj_is_fun,restrict_surj] 1));
val restrict_bij = result();


(*** Lemmas for Ramsey's Theorem ***)

goalw Perm.thy [inj_def] "!!f. [| f: inj(A,B);  B<=D |] ==> f: inj(A,D)";
by (fast_tac (ZF_cs addSEs [fun_weaken_type]) 1);
val inj_weaken_type = result();

val [major] = goal Perm.thy  
    "[| f: inj(succ(m), A) |] ==> restrict(f,m) : inj(m, A-{f`m})";
by (rtac (major RS restrict_bij RS bij_is_inj RS inj_weaken_type) 1);
by (fast_tac ZF_cs 1);
by (cut_facts_tac [major] 1);
by (rewtac inj_def);
by (safe_tac ZF_cs);
by (etac range_type 1);
by (assume_tac 1);
by (dtac apply_equality 1);
by (assume_tac 1);
by (res_inst_tac [("a","m")] mem_anti_refl 1);
by (fast_tac ZF_cs 1);
val inj_succ_restrict = result();

goalw Perm.thy [inj_def]
    "!!f. [| f: inj(A,B);  ~ a:A;  ~ b:B |]  ==> \
\         cons(<a,b>,f) : inj(cons(a,A), cons(b,B))";
(*cannot use safe_tac: must preserve the implication*)
by (etac CollectE 1);
by (rtac CollectI 1);
by (etac fun_extend 1);
by (REPEAT (ares_tac [ballI] 1));
by (REPEAT_FIRST (eresolve_tac [consE,ssubst]));
(*Assumption ALL w:A. ALL x:A. f`w = f`x --> w=x makes ASM_SIMP_TAC loop!*)
by (ALLGOALS (SIMP_TAC (ZF_ss addrews [fun_extend_apply2,fun_extend_apply1])));
by (ALLGOALS (fast_tac (ZF_cs addIs [apply_type])));
val inj_extend = result();
