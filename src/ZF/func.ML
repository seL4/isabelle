(*  Title: 	ZF/func
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Functions in Zermelo-Fraenkel Set Theory
*)

(*** The Pi operator -- dependent function space ***)

goalw ZF.thy [Pi_def]
    "f: Pi(A,B) <-> function(f) & f<=Sigma(A,B) & A<=domain(f)";
by (fast_tac ZF_cs 1);
val Pi_iff = result();

(*For upward compatibility with the former definition*)
goalw ZF.thy [Pi_def, function_def]
    "f: Pi(A,B) <-> f<=Sigma(A,B) & (ALL x:A. EX! y. <x,y>: f)";
by (safe_tac ZF_cs);
by (best_tac ZF_cs 1);
by (best_tac ZF_cs 1);
by (set_mp_tac 1);
by (deepen_tac ZF_cs 3 1);
val Pi_iff_old = result();

goal ZF.thy "!!f. f: Pi(A,B) ==> function(f)";
by (asm_full_simp_tac (FOL_ss addsimps [Pi_iff]) 1);
val fun_is_function = result();

(**Two "destruct" rules for Pi **)

val [major] = goalw ZF.thy [Pi_def] "f: Pi(A,B) ==> f <= Sigma(A,B)";  
by (rtac (major RS CollectD1 RS PowD) 1);
val fun_is_rel = result();

goal ZF.thy "!!f. [| f: Pi(A,B);  a:A |] ==> EX! y. <a,y>: f";  
by (fast_tac (ZF_cs addSDs [Pi_iff_old RS iffD1]) 1);
val fun_unique_Pair = result();

val prems = goalw ZF.thy [Pi_def]
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> Pi(A,B) = Pi(A',B')";
by (simp_tac (FOL_ss addsimps prems addcongs [Sigma_cong]) 1);
val Pi_cong = result();

(*Weakening one function type to another; see also Pi_type*)
goalw ZF.thy [Pi_def] "!!f. [| f: A->B;  B<=D |] ==> f: A->D";
by (best_tac ZF_cs 1);
val fun_weaken_type = result();

(*Empty function spaces*)
goalw ZF.thy [Pi_def, function_def] "Pi(0,A) = {0}";
by (fast_tac eq_cs 1);
val Pi_empty1 = result();

goalw ZF.thy [Pi_def] "!!A a. a:A ==> A->0 = 0";
by (fast_tac eq_cs 1);
val Pi_empty2 = result();

(*The empty function*)
goalw ZF.thy [Pi_def, function_def] "0: 0->A";
by (fast_tac ZF_cs 1);
val empty_fun = result();

(*The singleton function*)
goalw ZF.thy [Pi_def, function_def] "{<a,b>} : {a} -> {b}";
by (fast_tac eq_cs 1);
val single_fun = result();

(*** Function Application ***)

goalw ZF.thy [Pi_def, function_def]
     "!!a b f. [| <a,b>: f;  <a,c>: f;  f: Pi(A,B) |] ==> b=c";
by (deepen_tac ZF_cs 3 1);
val apply_equality2 = result();

goalw ZF.thy [apply_def] "!!a b f. [| <a,b>: f;  f: Pi(A,B) |] ==> f`a = b";
by (rtac the_equality 1);
by (rtac apply_equality2 2);
by (REPEAT (assume_tac 1));
val apply_equality = result();

(*Applying a function outside its domain yields 0*)
goalw ZF.thy [apply_def]
    "!!a b f. [| a ~: domain(f);  f: Pi(A,B) |] ==> f`a = 0";
by (rtac the_0 1);
by (fast_tac ZF_cs 1);
val apply_0 = result();

goal ZF.thy "!!f. [| f: Pi(A,B);  c: f |] ==> EX x:A.  c = <x,f`x>";
by (forward_tac [fun_is_rel] 1);
by (fast_tac (ZF_cs addDs [apply_equality]) 1);
val Pi_memberD = result();

goal ZF.thy "!!f. [| f: Pi(A,B);  a:A |] ==> <a,f`a>: f";
by (rtac (fun_unique_Pair RS ex1E) 1);
by (resolve_tac [apply_equality RS ssubst] 3);
by (REPEAT (assume_tac 1));
val apply_Pair = result();

(*Conclusion is flexible -- use res_inst_tac or else apply_funtype below!*)
goal ZF.thy "!!f. [| f: Pi(A,B);  a:A |] ==> f`a : B(a)"; 
by (rtac (fun_is_rel RS subsetD RS SigmaE2) 1);
by (REPEAT (ares_tac [apply_Pair] 1));
val apply_type = result();

(*This version is acceptable to the simplifier*)
goal ZF.thy "!!f. [| f: A->B;  a:A |] ==> f`a : B"; 
by (REPEAT (ares_tac [apply_type] 1));
val apply_funtype = result();

val [major] = goal ZF.thy
    "f: Pi(A,B) ==> <a,b>: f <-> a:A & f`a = b";
by (cut_facts_tac [major RS fun_is_rel] 1);
by (fast_tac (ZF_cs addSIs [major RS apply_Pair, 
			    major RSN (2,apply_equality)]) 1);
val apply_iff = result();

(*Refining one Pi type to another*)
val pi_prem::prems = goal ZF.thy
    "[| f: Pi(A,C);  !!x. x:A ==> f`x : B(x) |] ==> f : Pi(A,B)";
by (cut_facts_tac [pi_prem] 1);
by (asm_full_simp_tac (FOL_ss addsimps [Pi_iff]) 1);
by (fast_tac (ZF_cs addIs prems addSDs [pi_prem RS Pi_memberD]) 1);
val Pi_type = result();


(** Elimination of membership in a function **)

goal ZF.thy "!!a A. [| <a,b> : f;  f: Pi(A,B) |] ==> a : A";
by (REPEAT (ares_tac [fun_is_rel RS subsetD RS SigmaD1] 1));
val domain_type = result();

goal ZF.thy "!!b B a. [| <a,b> : f;  f: Pi(A,B) |] ==> b : B(a)";
by (etac (fun_is_rel RS subsetD RS SigmaD2) 1);
by (assume_tac 1);
val range_type = result();

val prems = goal ZF.thy
    "[| <a,b>: f;  f: Pi(A,B);       \
\       [| a:A;  b:B(a);  f`a = b |] ==> P  \
\    |] ==> P";
by (cut_facts_tac prems 1);
by (resolve_tac prems 1);
by (REPEAT (eresolve_tac [asm_rl,domain_type,range_type,apply_equality] 1));
val Pair_mem_PiE = result();

(*** Lambda Abstraction ***)

goalw ZF.thy [lam_def] "!!A b. a:A ==> <a,b(a)> : (lam x:A. b(x))";  
by (etac RepFunI 1);
val lamI = result();

val major::prems = goalw ZF.thy [lam_def]
    "[| p: (lam x:A. b(x));  !!x.[| x:A; p=<x,b(x)> |] ==> P  \
\    |] ==>  P";  
by (rtac (major RS RepFunE) 1);
by (REPEAT (ares_tac prems 1));
val lamE = result();

goal ZF.thy "!!a b c. [| <a,c>: (lam x:A. b(x)) |] ==> c = b(a)";  
by (REPEAT (eresolve_tac [asm_rl,lamE,Pair_inject,ssubst] 1));
val lamD = result();

val prems = goalw ZF.thy [lam_def, Pi_def, function_def]
    "[| !!x. x:A ==> b(x): B(x) |] ==> (lam x:A.b(x)) : Pi(A,B)";  
by (fast_tac (ZF_cs addIs prems) 1);
val lam_type = result();

goal ZF.thy "(lam x:A.b(x)) : A -> {b(x). x:A}";
by (REPEAT (ares_tac [refl,lam_type,RepFunI] 1));
val lam_funtype = result();

goal ZF.thy "!!a A. a : A ==> (lam x:A.b(x)) ` a = b(a)";
by (REPEAT (ares_tac [apply_equality,lam_funtype,lamI] 1));
val beta = result();

(*congruence rule for lambda abstraction*)
val prems = goalw ZF.thy [lam_def] 
    "[| A=A';  !!x. x:A' ==> b(x)=b'(x) |] ==> Lambda(A,b) = Lambda(A',b')";
by (simp_tac (FOL_ss addsimps prems addcongs [RepFun_cong]) 1);
val lam_cong = result();

val [major] = goal ZF.thy
    "(!!x. x:A ==> EX! y. Q(x,y)) ==> EX f. ALL x:A. Q(x, f`x)";
by (res_inst_tac [("x", "lam x: A. THE y. Q(x,y)")] exI 1);
by (rtac ballI 1);
by (rtac (beta RS ssubst) 1);
by (assume_tac 1);
by (etac (major RS theI) 1);
val lam_theI = result();


(** Extensionality **)

(*Semi-extensionality!*)
val prems = goal ZF.thy
    "[| f : Pi(A,B);  g: Pi(C,D);  A<=C; \
\       !!x. x:A ==> f`x = g`x       |] ==> f<=g";
by (rtac subsetI 1);
by (eresolve_tac (prems RL [Pi_memberD RS bexE]) 1);
by (etac ssubst 1);
by (resolve_tac (prems RL [ssubst]) 1);
by (REPEAT (ares_tac (prems@[apply_Pair,subsetD]) 1));
val fun_subset = result();

val prems = goal ZF.thy
    "[| f : Pi(A,B);  g: Pi(A,D);  \
\       !!x. x:A ==> f`x = g`x       |] ==> f=g";
by (REPEAT (ares_tac (prems @ (prems RL [sym]) @
		      [subset_refl,equalityI,fun_subset]) 1));
val fun_extension = result();

goal ZF.thy "!!f A B. f : Pi(A,B) ==> (lam x:A. f`x) = f";
by (rtac fun_extension 1);
by (REPEAT (ares_tac [lam_type,apply_type,beta] 1));
val eta = result();

(*Every element of Pi(A,B) may be expressed as a lambda abstraction!*)
val prems = goal ZF.thy
    "[| f: Pi(A,B);        \
\       !!b. [| ALL x:A. b(x):B(x);  f = (lam x:A.b(x)) |] ==> P   \
\    |] ==> P";
by (resolve_tac prems 1);
by (rtac (eta RS sym) 2);
by (REPEAT (ares_tac (prems@[ballI,apply_type]) 1));
val Pi_lamE = result();


(** Images of functions **)

goalw ZF.thy [lam_def] "!!C A. C <= A ==> (lam x:A.b(x)) `` C = {b(x). x:C}";
by (fast_tac eq_cs 1);
val image_lam = result();

goal ZF.thy "!!C A. [| f : Pi(A,B);  C <= A |] ==> f``C = {f`x. x:C}";
by (etac (eta RS subst) 1);
by (asm_full_simp_tac (FOL_ss addsimps [beta, image_lam, subset_iff]
                              addcongs [RepFun_cong]) 1);
val image_fun = result();


(*** properties of "restrict" ***)

goalw ZF.thy [restrict_def,lam_def]
    "!!f A. [| f: Pi(C,B);  A<=C |] ==> restrict(f,A) <= f";
by (fast_tac (ZF_cs addIs [apply_Pair]) 1);
val restrict_subset = result();

val prems = goalw ZF.thy [restrict_def]
    "[| !!x. x:A ==> f`x: B(x) |] ==> restrict(f,A) : Pi(A,B)";  
by (rtac lam_type 1);
by (eresolve_tac prems 1);
val restrict_type = result();

val [pi,subs] = goal ZF.thy 
    "[| f: Pi(C,B);  A<=C |] ==> restrict(f,A) : Pi(A,B)";  
by (rtac (pi RS apply_type RS restrict_type) 1);
by (etac (subs RS subsetD) 1);
val restrict_type2 = result();

goalw ZF.thy [restrict_def] "!!a A. a : A ==> restrict(f,A) ` a = f`a";
by (etac beta 1);
val restrict = result();

(*NOT SAFE as a congruence rule for the simplifier!  Can cause it to fail!*)
val prems = goalw ZF.thy [restrict_def]
    "[| A=B;  !!x. x:B ==> f`x=g`x |] ==> restrict(f,A) = restrict(g,B)";
by (REPEAT (ares_tac (prems@[lam_cong]) 1));
val restrict_eqI = result();

goalw ZF.thy [restrict_def, lam_def] "domain(restrict(f,C)) = C";
by (fast_tac eq_cs 1);
val domain_restrict = result();

val [prem] = goalw ZF.thy [restrict_def]
    "A<=C ==> restrict(lam x:C. b(x), A) = (lam x:A. b(x))";
by (rtac (refl RS lam_cong) 1);
by (etac (prem RS subsetD RS beta) 1);	(*easier than calling simp_tac*)
val restrict_lam_eq = result();



(*** Unions of functions ***)

(** The Union of a set of COMPATIBLE functions is a function **)

goalw ZF.thy [function_def]
    "!!S. [| ALL x:S. function(x); \
\            ALL x:S. ALL y:S. x<=y | y<=x  |] ==>  \
\         function(Union(S))";
by (fast_tac (ZF_cs addSDs [bspec RS bspec]) 1);
val function_Union = result();

goalw ZF.thy [Pi_def]
    "!!S. [| ALL f:S. EX C D. f:C->D; \
\            ALL f:S. ALL y:S. f<=y | y<=f  |] ==>  \
\         Union(S) : domain(Union(S)) -> range(Union(S))";
by (fast_tac (subset_cs addSIs [rel_Union, function_Union]) 1);
val fun_Union = result();


(** The Union of 2 disjoint functions is a function **)

val Un_rls = [Un_subset_iff, domain_Un_eq, SUM_Un_distrib1, prod_Un_distrib2, 
	      Un_upper1 RSN (2, subset_trans), 
	      Un_upper2 RSN (2, subset_trans)];

goal ZF.thy
    "!!f. [| f: A->B;  g: C->D;  A Int C = 0  |] ==>  \
\         (f Un g) : (A Un C) -> (B Un D)";
(*Solve the product and domain subgoals using distributive laws*)
by (asm_full_simp_tac (FOL_ss addsimps [Pi_iff,extension]@Un_rls) 1);
by (asm_simp_tac (FOL_ss addsimps [function_def]) 1);
by (safe_tac ZF_cs);
(*Solve the two cases that contradict A Int C = 0*)
by (deepen_tac ZF_cs 2 2);
by (deepen_tac ZF_cs 2 2);
bw function_def;
by (REPEAT_FIRST (dtac (spec RS spec)));
by (deepen_tac ZF_cs 1 1);
by (deepen_tac ZF_cs 1 1);
val fun_disjoint_Un = result();

goal ZF.thy
    "!!f g a. [| a:A;  f: A->B;  g: C->D;  A Int C = 0 |] ==>  \
\             (f Un g)`a = f`a";
by (rtac (apply_Pair RS UnI1 RS apply_equality) 1);
by (REPEAT (ares_tac [fun_disjoint_Un] 1));
val fun_disjoint_apply1 = result();

goal ZF.thy
    "!!f g c. [| c:C;  f: A->B;  g: C->D;  A Int C = 0 |] ==>  \
\             (f Un g)`c = g`c";
by (rtac (apply_Pair RS UnI2 RS apply_equality) 1);
by (REPEAT (ares_tac [fun_disjoint_Un] 1));
val fun_disjoint_apply2 = result();

(** Domain and range of a function/relation **)

goalw ZF.thy [Pi_def] "!!f. f : Pi(A,B) ==> domain(f)=A";
by (fast_tac eq_cs 1);
val domain_of_fun = result();

goal ZF.thy "!!f. [| f : Pi(A,B);  a: A |] ==> f`a : range(f)";
by (etac (apply_Pair RS rangeI) 1);
by (assume_tac 1);
val apply_rangeI = result();

val [major] = goal ZF.thy "f : Pi(A,B) ==> f : A->range(f)";
by (rtac (major RS Pi_type) 1);
by (etac (major RS apply_rangeI) 1);
val range_of_fun = result();

(*** Extensions of functions ***)

goal ZF.thy
    "!!f A B. [| f: A->B;  c~:A |] ==> cons(<c,b>,f) : cons(c,A) -> cons(b,B)";
by (forward_tac [single_fun RS fun_disjoint_Un] 1);
by (asm_full_simp_tac (FOL_ss addsimps [cons_eq]) 2);
by (fast_tac eq_cs 1);
val fun_extend = result();

goal ZF.thy
    "!!f A B. [| f: A->B;  c~:A;  b: B |] ==> cons(<c,b>,f) : cons(c,A) -> B";
by (fast_tac (ZF_cs addEs [fun_extend RS fun_weaken_type]) 1);
val fun_extend3 = result();

goal ZF.thy "!!f A B. [| f: A->B;  a:A;  c~:A |] ==> cons(<c,b>,f)`a = f`a";
by (rtac (apply_Pair RS consI2 RS apply_equality) 1);
by (rtac fun_extend 3);
by (REPEAT (assume_tac 1));
val fun_extend_apply1 = result();

goal ZF.thy "!!f A B. [| f: A->B;  c~:A |] ==> cons(<c,b>,f)`c = b";
by (rtac (consI1 RS apply_equality) 1);
by (rtac fun_extend 1);
by (REPEAT (assume_tac 1));
val fun_extend_apply2 = result();

(*For Finite.ML.  Inclusion of right into left is easy*)
goal ZF.thy
    "!!c. c ~: A ==> cons(c,A) -> B = (UN f: A->B. UN b:B. {cons(<c,b>, f)})";
by (safe_tac (eq_cs addSEs [fun_extend3]));
(*Inclusion of left into right*)
by (subgoal_tac "restrict(x, A) : A -> B" 1);
by (fast_tac (ZF_cs addEs [restrict_type2]) 2);
by (rtac UN_I 1 THEN assume_tac 1);
by (rtac UN_I 1 THEN fast_tac (ZF_cs addEs [apply_type]) 1);
by (simp_tac (FOL_ss addsimps cons_iff::mem_simps) 1);
by (resolve_tac [fun_extension] 1 THEN REPEAT (ares_tac [fun_extend] 1));
by (etac consE 1);
by (ALLGOALS 
    (asm_simp_tac (FOL_ss addsimps [restrict, fun_extend_apply1, 
				    fun_extend_apply2])));
val cons_fun_eq = result();

