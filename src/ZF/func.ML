(*  Title:      ZF/func
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Functions in Zermelo-Fraenkel Set Theory
*)

(*** The Pi operator -- dependent function space ***)

Goalw [Pi_def]
    "f: Pi(A,B) <-> function(f) & f<=Sigma(A,B) & A<=domain(f)";
by (Blast_tac 1);
qed "Pi_iff";

(*For upward compatibility with the former definition*)
Goalw [Pi_def, function_def]
    "f: Pi(A,B) <-> f<=Sigma(A,B) & (ALL x:A. EX! y. <x,y>: f)";
by (Blast_tac 1);
qed "Pi_iff_old";

Goal "f: Pi(A,B) ==> function(f)";
by (asm_full_simp_tac (FOL_ss addsimps [Pi_iff]) 1);
qed "fun_is_function";

(**Two "destruct" rules for Pi **)

Goalw [Pi_def] "f: Pi(A,B) ==> f <= Sigma(A,B)";  
by (Blast_tac 1);
qed "fun_is_rel";

Goal "[| f: Pi(A,B);  a:A |] ==> EX! y. <a,y>: f";  
by (blast_tac (claset() addSDs [Pi_iff_old RS iffD1]) 1);
qed "fun_unique_Pair";

val prems = Goalw [Pi_def]
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> Pi(A,B) = Pi(A',B')";
by (simp_tac (FOL_ss addsimps prems addcongs [Sigma_cong]) 1);
qed "Pi_cong";

(*Sigma_cong, Pi_cong NOT given to Addcongs: they cause
  flex-flex pairs and the "Check your prover" error.  Most
  Sigmas and Pis are abbreviated as * or -> *)

(*Weakening one function type to another; see also Pi_type*)
Goalw [Pi_def] "[| f: A->B;  B<=D |] ==> f: A->D";
by (Best_tac 1);
qed "fun_weaken_type";

(*** Function Application ***)

Goalw [Pi_def, function_def] "[| <a,b>: f;  <a,c>: f;  f: Pi(A,B) |] ==> b=c";
by (Blast_tac 1);
qed "apply_equality2";

Goalw [apply_def, function_def] "[| <a,b>: f;  function(f) |] ==> f`a = b";
by (Blast_tac 1);
qed "function_apply_equality";

Goalw [Pi_def] "[| <a,b>: f;  f: Pi(A,B) |] ==> f`a = b";
by (blast_tac (claset() addIs [function_apply_equality]) 1);
qed "apply_equality";

(*Applying a function outside its domain yields 0*)
Goalw [apply_def] "a ~: domain(f) ==> f`a = 0";
by (rtac the_0 1);
by (Blast_tac 1);
qed "apply_0";

Goal "[| f: Pi(A,B);  c: f |] ==> EX x:A.  c = <x,f`x>";
by (ftac fun_is_rel 1);
by (blast_tac (claset() addDs [apply_equality]) 1);
qed "Pi_memberD";

Goal "[| f: Pi(A,B);  a:A |] ==> <a,f`a>: f";
by (rtac (fun_unique_Pair RS ex1E) 1);
by (resolve_tac [apply_equality RS ssubst] 3);
by (REPEAT (assume_tac 1));
qed "apply_Pair";

(*Conclusion is flexible -- use res_inst_tac or else apply_funtype below!*)
Goal "[| f: Pi(A,B);  a:A |] ==> f`a : B(a)"; 
by (rtac (fun_is_rel RS subsetD RS SigmaE2) 1);
by (REPEAT (ares_tac [apply_Pair] 1));
qed "apply_type";
AddTCs [apply_type];

(*This version is acceptable to the simplifier*)
Goal "[| f: A->B;  a:A |] ==> f`a : B"; 
by (REPEAT (ares_tac [apply_type] 1));
qed "apply_funtype";

Goal "f: Pi(A,B) ==> <a,b>: f <-> a:A & f`a = b";
by (ftac fun_is_rel 1);
by (blast_tac (claset() addSIs [apply_Pair, apply_equality]) 1);
qed "apply_iff";

(*Refining one Pi type to another*)
val pi_prem::prems = Goal
    "[| f: Pi(A,C);  !!x. x:A ==> f`x : B(x) |] ==> f : Pi(A,B)";
by (cut_facts_tac [pi_prem] 1);
by (asm_full_simp_tac (FOL_ss addsimps [Pi_iff]) 1);
by (blast_tac (claset() addIs prems addSDs [pi_prem RS Pi_memberD]) 1);
qed "Pi_type";

(*Such functions arise in non-standard datatypes, ZF/ex/Ntree for instance*)
Goal "(f : Pi(A, %x. {y:B(x). P(x,y)})) \
\     <->  f : Pi(A,B) & (ALL x: A. P(x, f`x))";
by (blast_tac (claset() addIs [Pi_type] addDs [apply_type]) 1);
qed "Pi_Collect_iff";

val [major,minor] = Goal 
        "[| f : Pi(A,B);  !!x. x:A ==> B(x)<=C(x) |] ==> f : Pi(A,C)";
by (fast_tac (claset() addSIs [major RS Pi_type, minor RS subsetD,
                major RS apply_type]) 1);
qed "Pi_weaken_type";


(** Elimination of membership in a function **)

Goal "[| <a,b> : f;  f: Pi(A,B) |] ==> a : A";
by (REPEAT (ares_tac [fun_is_rel RS subsetD RS SigmaD1] 1));
qed "domain_type";

Goal "[| <a,b> : f;  f: Pi(A,B) |] ==> b : B(a)";
by (etac (fun_is_rel RS subsetD RS SigmaD2) 1);
by (assume_tac 1);
qed "range_type";

Goal "[| <a,b>: f;  f: Pi(A,B) |] ==> a:A & b:B(a) & f`a = b";
by (blast_tac (claset() addIs [domain_type, range_type, apply_equality]) 1);
qed "Pair_mem_PiD";

(*** Lambda Abstraction ***)

Goalw [lam_def] "a:A ==> <a,b(a)> : (lam x:A. b(x))";  
by (etac RepFunI 1);
qed "lamI";

val major::prems = Goalw [lam_def]
    "[| p: (lam x:A. b(x));  !!x.[| x:A; p=<x,b(x)> |] ==> P  \
\    |] ==>  P";  
by (rtac (major RS RepFunE) 1);
by (REPEAT (ares_tac prems 1));
qed "lamE";

Goal "[| <a,c>: (lam x:A. b(x)) |] ==> c = b(a)";  
by (REPEAT (eresolve_tac [asm_rl,lamE,Pair_inject,ssubst] 1));
qed "lamD";

val prems = Goalw [lam_def, Pi_def, function_def]
    "[| !!x. x:A ==> b(x): B(x) |] ==> (lam x:A. b(x)) : Pi(A,B)";  
by (blast_tac (claset() addIs prems) 1);
qed "lam_type";
AddTCs [lam_type];

Goal "(lam x:A. b(x)) : A -> {b(x). x:A}";
by (REPEAT (ares_tac [refl,lam_type,RepFunI] 1));
qed "lam_funtype";

Goal "a : A ==> (lam x:A. b(x)) ` a = b(a)";
by (REPEAT (ares_tac [apply_equality,lam_funtype,lamI] 1));
qed "beta";

Goalw [lam_def] "(lam x:0. b(x)) = 0";
by (Simp_tac 1);
qed "lam_empty";

Goalw [lam_def] "domain(Lambda(A,b)) = A";
by (Blast_tac 1);
qed "domain_lam";

Addsimps [beta, lam_empty, domain_lam];

(*congruence rule for lambda abstraction*)
val prems = Goalw [lam_def] 
    "[| A=A';  !!x. x:A' ==> b(x)=b'(x) |] ==> Lambda(A,b) = Lambda(A',b')";
by (simp_tac (FOL_ss addsimps prems addcongs [RepFun_cong]) 1);
qed "lam_cong";

Addcongs [lam_cong];

val [major] = Goal
    "(!!x. x:A ==> EX! y. Q(x,y)) ==> EX f. ALL x:A. Q(x, f`x)";
by (res_inst_tac [("x", "lam x: A. THE y. Q(x,y)")] exI 1);
by (rtac ballI 1);
by (stac beta 1);
by (assume_tac 1);
by (etac (major RS theI) 1);
qed "lam_theI";

Goal "[| (lam x:A. f(x)) = (lam x:A. g(x));  a:A |] ==> f(a)=g(a)";
by (fast_tac (claset() addSIs [lamI] addEs [equalityE, lamE]) 1);
qed "lam_eqE";


(*Empty function spaces*)
Goalw [Pi_def, function_def] "Pi(0,A) = {0}";
by (Blast_tac 1);
qed "Pi_empty1";
Addsimps [Pi_empty1];

(*The singleton function*)
Goalw [Pi_def, function_def] "{<a,b>} : {a} -> {b}";
by (Blast_tac 1);
qed "singleton_fun";
Addsimps [singleton_fun];

Goalw [Pi_def, function_def] "(A->0) = (if A=0 then {0} else 0)";
by (Force_tac 1);
qed "Pi_empty2";
Addsimps [Pi_empty2];

Goal "(A->X)=0 \\<longleftrightarrow> X=0 & (A \\<noteq> 0)";
by Auto_tac;  
by (fast_tac (claset() addSIs [equals0I] addIs [lam_type]) 1);
qed "fun_space_empty_iff";
AddIffs [fun_space_empty_iff];


(** Extensionality **)

(*Semi-extensionality!*)
val prems = Goal
    "[| f : Pi(A,B);  g: Pi(C,D);  A<=C; \
\       !!x. x:A ==> f`x = g`x       |] ==> f<=g";
by (rtac subsetI 1);
by (eresolve_tac (prems RL [Pi_memberD RS bexE]) 1);
by (etac ssubst 1);
by (resolve_tac (prems RL [ssubst]) 1);
by (REPEAT (ares_tac (prems@[apply_Pair,subsetD]) 1));
qed "fun_subset";

val prems = Goal
    "[| f : Pi(A,B);  g: Pi(A,D);  \
\       !!x. x:A ==> f`x = g`x       |] ==> f=g";
by (REPEAT (ares_tac (prems @ (prems RL [sym]) @
                      [subset_refl,equalityI,fun_subset]) 1));
qed "fun_extension";

Goal "f : Pi(A,B) ==> (lam x:A. f`x) = f";
by (rtac fun_extension 1);
by (REPEAT (ares_tac [lam_type,apply_type,beta] 1));
qed "eta";

Addsimps [eta];

Goal "[| f:Pi(A,B); g:Pi(A,C) |] ==> (ALL a:A. f`a = g`a) <-> f=g";
by (blast_tac (claset() addIs [fun_extension]) 1);
qed "fun_extension_iff";

(*thanks to Mark Staples*)
Goal "[| f:Pi(A,B); g:Pi(A,C) |] ==> f <= g <-> (f = g)";
by (rtac iffI 1);
by (asm_full_simp_tac ZF_ss 2);
by (rtac fun_extension 1);
by (REPEAT (atac 1));
by (dtac (apply_Pair RSN (2,subsetD)) 1);
by (REPEAT (atac 1));
by (rtac (apply_equality RS sym) 1);
by (REPEAT (atac 1)) ;
qed "fun_subset_eq";


(*Every element of Pi(A,B) may be expressed as a lambda abstraction!*)
val prems = Goal
    "[| f: Pi(A,B);        \
\       !!b. [| ALL x:A. b(x):B(x);  f = (lam x:A. b(x)) |] ==> P   \
\    |] ==> P";
by (resolve_tac prems 1);
by (rtac (eta RS sym) 2);
by (REPEAT (ares_tac (prems@[ballI,apply_type]) 1));
qed "Pi_lamE";


(** Images of functions **)

Goalw [lam_def] "C <= A ==> (lam x:A. b(x)) `` C = {b(x). x:C}";
by (Blast_tac 1);
qed "image_lam";

Goal "[| f : Pi(A,B);  C <= A |] ==> f``C = {f`x. x:C}";
by (etac (eta RS subst) 1);
by (asm_full_simp_tac (simpset() addsimps [image_lam, subset_iff]) 1);
qed "image_fun";

Goal "[| f: Pi(A,B);  x: A |] ==> f `` cons(x,y) = cons(f`x, f``y)";
by (blast_tac (claset() addDs [apply_equality, apply_Pair]) 1);
qed "Pi_image_cons";


(*** properties of "restrict" ***)

Goalw [restrict_def,lam_def]
    "[| f: Pi(C,B);  A<=C |] ==> restrict(f,A) <= f";
by (blast_tac (claset() addIs [apply_Pair]) 1);
qed "restrict_subset";

val prems = Goalw [restrict_def]
    "[| !!x. x:A ==> f`x: B(x) |] ==> restrict(f,A) : Pi(A,B)";  
by (rtac lam_type 1);
by (eresolve_tac prems 1);
qed "restrict_type";

Goal "[| f: Pi(C,B);  A<=C |] ==> restrict(f,A) : Pi(A,B)";  
by (blast_tac (claset() addIs [apply_type, restrict_type]) 1);
qed "restrict_type2";

Goalw [restrict_def] "a : A ==> restrict(f,A) ` a = f`a";
by (etac beta 1);
qed "restrict";

Goalw [restrict_def] "restrict(f,0) = 0";
by (Simp_tac 1);
qed "restrict_empty";

Addsimps [restrict, restrict_empty];

(*NOT SAFE as a congruence rule for the simplifier!  Can cause it to fail!*)
val prems = Goalw [restrict_def]
    "[| A=B;  !!x. x:B ==> f`x=g`x |] ==> restrict(f,A) = restrict(g,B)";
by (REPEAT (ares_tac (prems@[lam_cong]) 1));
qed "restrict_eqI";

Goalw [restrict_def, lam_def] "domain(restrict(f,C)) = C";
by (Blast_tac 1);
qed "domain_restrict";
Addsimps [domain_restrict];

Goalw [restrict_def]
    "A<=C ==> restrict(lam x:C. b(x), A) = (lam x:A. b(x))";
by (rtac (refl RS lam_cong) 1);
by (set_mp_tac 1);
by (Asm_simp_tac 1);
qed "restrict_lam_eq";

Goal "f : cons(a, b) -> B ==> f = cons(<a, f ` a>, restrict(f, b))";
by (rtac equalityI 1);
by (blast_tac (claset() addIs [apply_Pair, impOfSubs restrict_subset]) 2);
by (auto_tac (claset() addSDs [Pi_memberD],
	       simpset() addsimps [restrict_def, lam_def]));
qed "fun_cons_restrict_eq";


(*** Unions of functions ***)

(** The Union of a set of COMPATIBLE functions is a function **)

Goalw [function_def]
    "[| ALL x:S. function(x); \
\            ALL x:S. ALL y:S. x<=y | y<=x  |] ==>  \
\         function(Union(S))";
by (fast_tac (ZF_cs addSDs [bspec RS bspec]) 1);
	(*by (Blast_tac 1);  takes too long...*)
qed "function_Union";

Goalw [Pi_def]
    "[| ALL f:S. EX C D. f:C->D; \
\            ALL f:S. ALL y:S. f<=y | y<=f  |] ==>  \
\         Union(S) : domain(Union(S)) -> range(Union(S))";
by (blast_tac (subset_cs addSIs [rel_Union, function_Union]) 1);
qed "fun_Union";


(** The Union of 2 disjoint functions is a function **)

bind_thms ("Un_rls", [Un_subset_iff, SUM_Un_distrib1, prod_Un_distrib2, 
              Un_upper1 RSN (2, subset_trans), 
              Un_upper2 RSN (2, subset_trans)]);

Goal "[| f: A->B;  g: C->D;  A Int C = 0  |]  \
\                 ==> (f Un g) : (A Un C) -> (B Un D)";
(*Prove the product and domain subgoals using distributive laws*)
by (asm_full_simp_tac (simpset() addsimps [Pi_iff,extension]@Un_rls) 1);
by (rewtac function_def);
by (Blast_tac 1);
qed "fun_disjoint_Un";

Goal "[| a:A;  f: A->B;  g: C->D;  A Int C = 0 |] ==>  \
\             (f Un g)`a = f`a";
by (rtac (apply_Pair RS UnI1 RS apply_equality) 1);
by (REPEAT (ares_tac [fun_disjoint_Un] 1));
qed "fun_disjoint_apply1";

Goal "[| c:C;  f: A->B;  g: C->D;  A Int C = 0 |] ==>  \
\             (f Un g)`c = g`c";
by (rtac (apply_Pair RS UnI2 RS apply_equality) 1);
by (REPEAT (ares_tac [fun_disjoint_Un] 1));
qed "fun_disjoint_apply2";

(** Domain and range of a function/relation **)

Goalw [Pi_def] "f : Pi(A,B) ==> domain(f)=A";
by (Blast_tac 1);
qed "domain_of_fun";

Goal "[| f : Pi(A,B);  a: A |] ==> f`a : range(f)";
by (etac (apply_Pair RS rangeI) 1);
by (assume_tac 1);
qed "apply_rangeI";

Goal "f : Pi(A,B) ==> f : A->range(f)";
by (REPEAT (ares_tac [Pi_type, apply_rangeI] 1));
qed "range_of_fun";

(*** Extensions of functions ***)

Goal "[| f: A->B;  c~:A |] ==> cons(<c,b>,f) : cons(c,A) -> cons(b,B)";
by (forward_tac [singleton_fun RS fun_disjoint_Un] 1);
by (asm_full_simp_tac (FOL_ss addsimps [cons_eq]) 2);
by (Blast_tac 1);
qed "fun_extend";

Goal "[| f: A->B;  c~:A;  b: B |] ==> cons(<c,b>,f) : cons(c,A) -> B";
by (blast_tac (claset() addIs [fun_extend RS fun_weaken_type]) 1);
qed "fun_extend3";

Goal "[| f: A->B;  a:A;  c~:A |] ==> cons(<c,b>,f)`a = f`a";
by (rtac (apply_Pair RS consI2 RS apply_equality) 1);
by (rtac fun_extend 3);
by (REPEAT (assume_tac 1));
qed "fun_extend_apply1";

Goal "[| f: A->B;  c~:A |] ==> cons(<c,b>,f)`c = b";
by (rtac (consI1 RS apply_equality) 1);
by (rtac fun_extend 1);
by (REPEAT (assume_tac 1));
qed "fun_extend_apply2";

bind_thm ("singleton_apply", [singletonI, singleton_fun] MRS apply_equality);
Addsimps [singleton_apply];

(*For Finite.ML.  Inclusion of right into left is easy*)
Goal "c ~: A ==> cons(c,A) -> B = (UN f: A->B. UN b:B. {cons(<c,b>, f)})";
by (rtac equalityI 1);
by (safe_tac (claset() addSEs [fun_extend3]));
(*Inclusion of left into right*)
by (subgoal_tac "restrict(x, A) : A -> B" 1);
by (blast_tac (claset() addIs [restrict_type2]) 2);
by (rtac UN_I 1 THEN assume_tac 1);
by (rtac (apply_funtype RS UN_I) 1 THEN REPEAT (ares_tac [consI1] 1));
by (Simp_tac 1);
by (rtac fun_extension 1 THEN REPEAT (ares_tac [fun_extend] 1));
by (etac consE 1);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [restrict, fun_extend_apply1, 
                                      fun_extend_apply2])));
qed "cons_fun_eq";

