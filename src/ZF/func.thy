(*  Title:      ZF/func.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Functions in Zermelo-Fraenkel Set Theory
*)

theory func = equalities:

lemma subset_Sigma_imp_relation: "r <= Sigma(A,B) ==> relation(r)"
by (simp add: relation_def, blast)

lemma relation_converse_converse [simp]:
     "relation(r) ==> converse(converse(r)) = r"
by (simp add: relation_def, blast) 

lemma relation_restrict [simp]:  "relation(restrict(r,A))"
by (simp add: restrict_def relation_def, blast) 

(*** The Pi operator -- dependent function space ***)

lemma Pi_iff:
    "f: Pi(A,B) <-> function(f) & f<=Sigma(A,B) & A<=domain(f)"
by (unfold Pi_def, blast)

(*For upward compatibility with the former definition*)
lemma Pi_iff_old:
    "f: Pi(A,B) <-> f<=Sigma(A,B) & (ALL x:A. EX! y. <x,y>: f)"
by (unfold Pi_def function_def, blast)

lemma fun_is_function: "f: Pi(A,B) ==> function(f)"
by (simp only: Pi_iff)

lemma function_imp_Pi:
     "[|function(f); relation(f)|] ==> f \<in> domain(f) -> range(f)"
by (simp add: Pi_iff relation_def, blast) 

lemma functionI: 
     "[| !!x y y'. [| <x,y>:r; <x,y'>:r |] ==> y=y' |] ==> function(r)"
by (simp add: function_def, blast) 

(*Functions are relations*)
lemma fun_is_rel: "f: Pi(A,B) ==> f <= Sigma(A,B)"
by (unfold Pi_def, blast)

lemma Pi_cong:
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==> Pi(A,B) = Pi(A',B')"
by (simp add: Pi_def cong add: Sigma_cong)

(*Sigma_cong, Pi_cong NOT given to Addcongs: they cause
  flex-flex pairs and the "Check your prover" error.  Most
  Sigmas and Pis are abbreviated as * or -> *)

(*Weakening one function type to another; see also Pi_type*)
lemma fun_weaken_type: "[| f: A->B;  B<=D |] ==> f: A->D"
by (unfold Pi_def, best)

(*** Function Application ***)

lemma apply_equality2: "[| <a,b>: f;  <a,c>: f;  f: Pi(A,B) |] ==> b=c"
by (unfold Pi_def function_def, blast)

lemma function_apply_equality: "[| <a,b>: f;  function(f) |] ==> f`a = b"
by (unfold apply_def function_def, blast)

lemma apply_equality: "[| <a,b>: f;  f: Pi(A,B) |] ==> f`a = b"
apply (unfold Pi_def)
apply (blast intro: function_apply_equality)
done

(*Applying a function outside its domain yields 0*)
lemma apply_0: "a ~: domain(f) ==> f`a = 0"
by (unfold apply_def, blast)

lemma Pi_memberD: "[| f: Pi(A,B);  c: f |] ==> EX x:A.  c = <x,f`x>"
apply (frule fun_is_rel)
apply (blast dest: apply_equality)
done

lemma function_apply_Pair: "[| function(f);  a : domain(f)|] ==> <a,f`a>: f"
apply (simp add: function_def, clarify) 
apply (subgoal_tac "f`a = y", blast) 
apply (simp add: apply_def, blast) 
done

lemma apply_Pair: "[| f: Pi(A,B);  a:A |] ==> <a,f`a>: f"
apply (simp add: Pi_iff)
apply (blast intro: function_apply_Pair)
done

(*Conclusion is flexible -- use res_inst_tac or else apply_funtype below!*)
lemma apply_type [TC]: "[| f: Pi(A,B);  a:A |] ==> f`a : B(a)"
by (blast intro: apply_Pair dest: fun_is_rel)

(*This version is acceptable to the simplifier*)
lemma apply_funtype: "[| f: A->B;  a:A |] ==> f`a : B"
by (blast dest: apply_type)

lemma apply_iff: "f: Pi(A,B) ==> <a,b>: f <-> a:A & f`a = b"
apply (frule fun_is_rel)
apply (blast intro!: apply_Pair apply_equality)
done

(*Refining one Pi type to another*)
lemma Pi_type: "[| f: Pi(A,C);  !!x. x:A ==> f`x : B(x) |] ==> f : Pi(A,B)"
apply (simp only: Pi_iff)
apply (blast dest: function_apply_equality)
done

(*Such functions arise in non-standard datatypes, ZF/ex/Ntree for instance*)
lemma Pi_Collect_iff:
     "(f : Pi(A, %x. {y:B(x). P(x,y)}))
      <->  f : Pi(A,B) & (ALL x: A. P(x, f`x))"
by (blast intro: Pi_type dest: apply_type)

lemma Pi_weaken_type:
        "[| f : Pi(A,B);  !!x. x:A ==> B(x)<=C(x) |] ==> f : Pi(A,C)"
by (blast intro: Pi_type dest: apply_type)


(** Elimination of membership in a function **)

lemma domain_type: "[| <a,b> : f;  f: Pi(A,B) |] ==> a : A"
by (blast dest: fun_is_rel)

lemma range_type: "[| <a,b> : f;  f: Pi(A,B) |] ==> b : B(a)"
by (blast dest: fun_is_rel)

lemma Pair_mem_PiD: "[| <a,b>: f;  f: Pi(A,B) |] ==> a:A & b:B(a) & f`a = b"
by (blast intro: domain_type range_type apply_equality)

(*** Lambda Abstraction ***)

lemma lamI: "a:A ==> <a,b(a)> : (lam x:A. b(x))"
apply (unfold lam_def)
apply (erule RepFunI)
done

lemma lamE:
    "[| p: (lam x:A. b(x));  !!x.[| x:A; p=<x,b(x)> |] ==> P
     |] ==>  P"
by (simp add: lam_def, blast)

lemma lamD: "[| <a,c>: (lam x:A. b(x)) |] ==> c = b(a)"
by (simp add: lam_def)

lemma lam_type [TC]:
    "[| !!x. x:A ==> b(x): B(x) |] ==> (lam x:A. b(x)) : Pi(A,B)"
by (simp add: lam_def Pi_def function_def, blast)

lemma lam_funtype: "(lam x:A. b(x)) : A -> {b(x). x:A}"
by (blast intro: lam_type)

lemma function_lam: "function (lam x:A. b(x))"
by (simp add: function_def lam_def) 

lemma relation_lam: "relation (lam x:A. b(x))"  
by (simp add: relation_def lam_def) 

lemma beta_if [simp]: "(lam x:A. b(x)) ` a = (if a : A then b(a) else 0)"
by (simp add: apply_def lam_def, blast)

lemma beta: "a : A ==> (lam x:A. b(x)) ` a = b(a)"
by (simp add: apply_def lam_def, blast)

lemma lam_empty [simp]: "(lam x:0. b(x)) = 0"
by (simp add: lam_def)

lemma domain_lam [simp]: "domain(Lambda(A,b)) = A"
by (simp add: lam_def, blast)

(*congruence rule for lambda abstraction*)
lemma lam_cong [cong]:
    "[| A=A';  !!x. x:A' ==> b(x)=b'(x) |] ==> Lambda(A,b) = Lambda(A',b')"
by (simp only: lam_def cong add: RepFun_cong)

lemma lam_theI:
    "(!!x. x:A ==> EX! y. Q(x,y)) ==> EX f. ALL x:A. Q(x, f`x)"
apply (rule_tac x = "lam x: A. THE y. Q (x,y)" in exI)
apply simp 
apply (blast intro: theI)
done

lemma lam_eqE: "[| (lam x:A. f(x)) = (lam x:A. g(x));  a:A |] ==> f(a)=g(a)"
by (fast intro!: lamI elim: equalityE lamE)


(*Empty function spaces*)
lemma Pi_empty1 [simp]: "Pi(0,A) = {0}"
by (unfold Pi_def function_def, blast)

(*The singleton function*)
lemma singleton_fun [simp]: "{<a,b>} : {a} -> {b}"
by (unfold Pi_def function_def, blast)

lemma Pi_empty2 [simp]: "(A->0) = (if A=0 then {0} else 0)"
by (unfold Pi_def function_def, force)

lemma  fun_space_empty_iff [iff]: "(A->X)=0 \<longleftrightarrow> X=0 & (A \<noteq> 0)"
apply auto
apply (fast intro!: equals0I intro: lam_type)
done


(** Extensionality **)

(*Semi-extensionality!*)

lemma fun_subset:
    "[| f : Pi(A,B);  g: Pi(C,D);  A<=C;
        !!x. x:A ==> f`x = g`x       |] ==> f<=g"
by (force dest: Pi_memberD intro: apply_Pair)

lemma fun_extension:
    "[| f : Pi(A,B);  g: Pi(A,D);
        !!x. x:A ==> f`x = g`x       |] ==> f=g"
by (blast del: subsetI intro: subset_refl sym fun_subset)

lemma eta [simp]: "f : Pi(A,B) ==> (lam x:A. f`x) = f"
apply (rule fun_extension)
apply (auto simp add: lam_type apply_type beta)
done

lemma fun_extension_iff:
     "[| f:Pi(A,B); g:Pi(A,C) |] ==> (ALL a:A. f`a = g`a) <-> f=g"
by (blast intro: fun_extension)

(*thm by Mark Staples, proof by lcp*)
lemma fun_subset_eq: "[| f:Pi(A,B); g:Pi(A,C) |] ==> f <= g <-> (f = g)"
by (blast dest: apply_Pair
	  intro: fun_extension apply_equality [symmetric])


(*Every element of Pi(A,B) may be expressed as a lambda abstraction!*)
lemma Pi_lamE:
  assumes major: "f: Pi(A,B)"
      and minor: "!!b. [| ALL x:A. b(x):B(x);  f = (lam x:A. b(x)) |] ==> P"
  shows "P"
apply (rule minor)
apply (rule_tac [2] eta [symmetric])
apply (blast intro: major apply_type)+
done


(** Images of functions **)

lemma image_lam: "C <= A ==> (lam x:A. b(x)) `` C = {b(x). x:C}"
by (unfold lam_def, blast)

lemma Repfun_function_if:
     "function(f) 
      ==> {f`x. x:C} = (if C <= domain(f) then f``C else cons(0,f``C))";
apply simp
apply (intro conjI impI)  
 apply (blast dest: function_apply_equality intro: function_apply_Pair) 
apply (rule equalityI)
 apply (blast intro!: function_apply_Pair apply_0) 
apply (blast dest: function_apply_equality intro: apply_0 [symmetric]) 
done

(*For this lemma and the next, the right-hand side could equivalently 
  be written UN x:C. {f`x} *)
lemma image_function:
     "[| function(f);  C <= domain(f) |] ==> f``C = {f`x. x:C}";
by (simp add: Repfun_function_if) 

lemma image_fun: "[| f : Pi(A,B);  C <= A |] ==> f``C = {f`x. x:C}"
apply (simp add: Pi_iff) 
apply (blast intro: image_function) 
done

lemma Pi_image_cons:
     "[| f: Pi(A,B);  x: A |] ==> f `` cons(x,y) = cons(f`x, f``y)"
by (blast dest: apply_equality apply_Pair)


(*** properties of "restrict" ***)

lemma restrict_subset: "restrict(f,A) <= f"
by (unfold restrict_def, blast)

lemma function_restrictI:
    "function(f) ==> function(restrict(f,A))"
by (unfold restrict_def function_def, blast)

lemma restrict_type2: "[| f: Pi(C,B);  A<=C |] ==> restrict(f,A) : Pi(A,B)"
by (simp add: Pi_iff function_def restrict_def, blast)

lemma restrict: "restrict(f,A) ` a = (if a : A then f`a else 0)"
by (simp add: apply_def restrict_def, blast)

lemma restrict_empty [simp]: "restrict(f,0) = 0"
by (unfold restrict_def, simp)

lemma restrict_iff: "z \<in> restrict(r,A) \<longleftrightarrow> z \<in> r & (\<exists>x\<in>A. \<exists>y. z = \<langle>x, y\<rangle>)"
by (simp add: restrict_def) 

lemma restrict_restrict [simp]:
     "restrict(restrict(r,A),B) = restrict(r, A Int B)"
by (unfold restrict_def, blast)

lemma domain_restrict [simp]: "domain(restrict(f,C)) = domain(f) Int C"
apply (unfold restrict_def)
apply (auto simp add: domain_def)
done

lemma restrict_idem: "f <= Sigma(A,B) ==> restrict(f,A) = f"
by (simp add: restrict_def, blast)


(*converse probably holds too*)
lemma domain_restrict_idem:
     "[| domain(r) <= A; relation(r) |] ==> restrict(r,A) = r"
by (simp add: restrict_def relation_def, blast)

lemma domain_restrict_lam [simp]: "domain(restrict(Lambda(A,f),C)) = A Int C"
apply (unfold restrict_def lam_def)
apply (rule equalityI)
apply (auto simp add: domain_iff)
done

lemma restrict_if [simp]: "restrict(f,A) ` a = (if a : A then f`a else 0)"
by (simp add: restrict apply_0)

lemma restrict_lam_eq:
    "A<=C ==> restrict(lam x:C. b(x), A) = (lam x:A. b(x))"
by (unfold restrict_def lam_def, auto)

lemma fun_cons_restrict_eq:
     "f : cons(a, b) -> B ==> f = cons(<a, f ` a>, restrict(f, b))"
apply (rule equalityI)
 prefer 2 apply (blast intro: apply_Pair restrict_subset [THEN subsetD])
apply (auto dest!: Pi_memberD simp add: restrict_def lam_def)
done


(*** Unions of functions ***)

(** The Union of a set of COMPATIBLE functions is a function **)

lemma function_Union:
    "[| ALL x:S. function(x);
        ALL x:S. ALL y:S. x<=y | y<=x  |]
     ==> function(Union(S))"
by (unfold function_def, blast) 

lemma fun_Union:
    "[| ALL f:S. EX C D. f:C->D;
             ALL f:S. ALL y:S. f<=y | y<=f  |] ==>
          Union(S) : domain(Union(S)) -> range(Union(S))"
apply (unfold Pi_def)
apply (blast intro!: rel_Union function_Union)
done

lemma gen_relation_Union [rule_format]:
     "\<forall>f\<in>F. relation(f) \<Longrightarrow> relation(Union(F))"
by (simp add: relation_def) 


(** The Union of 2 disjoint functions is a function **)

lemmas Un_rls = Un_subset_iff SUM_Un_distrib1 prod_Un_distrib2
                subset_trans [OF _ Un_upper1]
                subset_trans [OF _ Un_upper2]

lemma fun_disjoint_Un:
     "[| f: A->B;  g: C->D;  A Int C = 0  |]
      ==> (f Un g) : (A Un C) -> (B Un D)"
(*Prove the product and domain subgoals using distributive laws*)
apply (simp add: Pi_iff extension Un_rls)
apply (unfold function_def, blast)
done

lemma fun_disjoint_apply1: "a \<notin> domain(g) ==> (f Un g)`a = f`a"
by (simp add: apply_def, blast) 

lemma fun_disjoint_apply2: "c \<notin> domain(f) ==> (f Un g)`c = g`c"
by (simp add: apply_def, blast) 

(** Domain and range of a function/relation **)

lemma domain_of_fun: "f : Pi(A,B) ==> domain(f)=A"
by (unfold Pi_def, blast)

lemma apply_rangeI: "[| f : Pi(A,B);  a: A |] ==> f`a : range(f)"
by (erule apply_Pair [THEN rangeI], assumption)

lemma range_of_fun: "f : Pi(A,B) ==> f : A->range(f)"
by (blast intro: Pi_type apply_rangeI)

(*** Extensions of functions ***)

lemma fun_extend:
     "[| f: A->B;  c~:A |] ==> cons(<c,b>,f) : cons(c,A) -> cons(b,B)"
apply (frule singleton_fun [THEN fun_disjoint_Un], blast)
apply (simp add: cons_eq) 
done

lemma fun_extend3:
     "[| f: A->B;  c~:A;  b: B |] ==> cons(<c,b>,f) : cons(c,A) -> B"
by (blast intro: fun_extend [THEN fun_weaken_type])

lemma extend_apply:
     "c ~: domain(f) ==> cons(<c,b>,f)`a = (if a=c then b else f`a)"
by (auto simp add: apply_def) 

lemma fun_extend_apply [simp]:
     "[| f: A->B;  c~:A |] ==> cons(<c,b>,f)`a = (if a=c then b else f`a)" 
apply (rule extend_apply) 
apply (simp add: Pi_def, blast) 
done

lemmas singleton_apply = apply_equality [OF singletonI singleton_fun, simp]

(*For Finite.ML.  Inclusion of right into left is easy*)
lemma cons_fun_eq:
     "c ~: A ==> cons(c,A) -> B = (UN f: A->B. UN b:B. {cons(<c,b>, f)})"
apply (rule equalityI)
apply (safe elim!: fun_extend3)
(*Inclusion of left into right*)
apply (subgoal_tac "restrict (x, A) : A -> B")
 prefer 2 apply (blast intro: restrict_type2)
apply (rule UN_I, assumption)
apply (rule apply_funtype [THEN UN_I]) 
  apply assumption
 apply (rule consI1) 
apply (simp (no_asm))
apply (rule fun_extension) 
  apply assumption
 apply (blast intro: fun_extend) 
apply (erule consE, simp_all)
done

ML
{*
val Pi_iff = thm "Pi_iff";
val Pi_iff_old = thm "Pi_iff_old";
val fun_is_function = thm "fun_is_function";
val fun_is_rel = thm "fun_is_rel";
val Pi_cong = thm "Pi_cong";
val fun_weaken_type = thm "fun_weaken_type";
val apply_equality2 = thm "apply_equality2";
val function_apply_equality = thm "function_apply_equality";
val apply_equality = thm "apply_equality";
val apply_0 = thm "apply_0";
val Pi_memberD = thm "Pi_memberD";
val function_apply_Pair = thm "function_apply_Pair";
val apply_Pair = thm "apply_Pair";
val apply_type = thm "apply_type";
val apply_funtype = thm "apply_funtype";
val apply_iff = thm "apply_iff";
val Pi_type = thm "Pi_type";
val Pi_Collect_iff = thm "Pi_Collect_iff";
val Pi_weaken_type = thm "Pi_weaken_type";
val domain_type = thm "domain_type";
val range_type = thm "range_type";
val Pair_mem_PiD = thm "Pair_mem_PiD";
val lamI = thm "lamI";
val lamE = thm "lamE";
val lamD = thm "lamD";
val lam_type = thm "lam_type";
val lam_funtype = thm "lam_funtype";
val beta = thm "beta";
val lam_empty = thm "lam_empty";
val domain_lam = thm "domain_lam";
val lam_cong = thm "lam_cong";
val lam_theI = thm "lam_theI";
val lam_eqE = thm "lam_eqE";
val Pi_empty1 = thm "Pi_empty1";
val singleton_fun = thm "singleton_fun";
val Pi_empty2 = thm "Pi_empty2";
val fun_space_empty_iff = thm "fun_space_empty_iff";
val fun_subset = thm "fun_subset";
val fun_extension = thm "fun_extension";
val eta = thm "eta";
val fun_extension_iff = thm "fun_extension_iff";
val fun_subset_eq = thm "fun_subset_eq";
val Pi_lamE = thm "Pi_lamE";
val image_lam = thm "image_lam";
val image_fun = thm "image_fun";
val Pi_image_cons = thm "Pi_image_cons";
val restrict_subset = thm "restrict_subset";
val function_restrictI = thm "function_restrictI";
val restrict_type2 = thm "restrict_type2";
val restrict = thm "restrict";
val restrict_empty = thm "restrict_empty";
val domain_restrict_lam = thm "domain_restrict_lam";
val restrict_restrict = thm "restrict_restrict";
val domain_restrict = thm "domain_restrict";
val restrict_idem = thm "restrict_idem";
val restrict_if = thm "restrict_if";
val restrict_lam_eq = thm "restrict_lam_eq";
val fun_cons_restrict_eq = thm "fun_cons_restrict_eq";
val function_Union = thm "function_Union";
val fun_Union = thm "fun_Union";
val fun_disjoint_Un = thm "fun_disjoint_Un";
val fun_disjoint_apply1 = thm "fun_disjoint_apply1";
val fun_disjoint_apply2 = thm "fun_disjoint_apply2";
val domain_of_fun = thm "domain_of_fun";
val apply_rangeI = thm "apply_rangeI";
val range_of_fun = thm "range_of_fun";
val fun_extend = thm "fun_extend";
val fun_extend3 = thm "fun_extend3";
val fun_extend_apply = thm "fun_extend_apply";
val singleton_apply = thm "singleton_apply";
val cons_fun_eq = thm "cons_fun_eq";
*}

end
