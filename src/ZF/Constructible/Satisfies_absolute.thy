(*  Title:      ZF/Constructible/Satisfies_absolute.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
*)

theory Satisfies_absolute = Datatype_absolute + Rec_Separation: 


subsection{*More Internalizations*}

lemma and_reflection:
     "REFLECTS[\<lambda>x. is_and(L,f(x),g(x),h(x)),
               \<lambda>i x. is_and(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_and_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done

lemma not_reflection:
     "REFLECTS[\<lambda>x. is_not(L,f(x),g(x)),
               \<lambda>i x. is_not(**Lset(i),f(x),g(x))]"
apply (simp only: is_not_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done

subsubsection{*The Operator @{term is_lambda}*}

text{*The two arguments of @{term p} are always 1, 0. Remember that
 @{term p} will be enclosed by three quantifiers.*}

(* is_lambda :: "[i=>o, i, [i,i]=>o, i] => o"
    "is_lambda(M, A, is_b, z) == 
       \<forall>p[M]. p \<in> z <->
        (\<exists>u[M]. \<exists>v[M]. u\<in>A & pair(M,u,v,p) & is_b(u,v))" *)
constdefs lambda_fm :: "[i, i, i]=>i"
 "lambda_fm(p,A,z) == 
    Forall(Iff(Member(0,succ(z)),
            Exists(Exists(And(Member(1,A#+3),
                           And(pair_fm(1,0,2), p))))))"

text{*We call @{term p} with arguments x, y by equating them with 
  the corresponding quantified variables with de Bruijn indices 1, 0.*}

lemma is_lambda_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat |] 
      ==> lambda_fm(p,x,y) \<in> formula"
by (simp add: lambda_fm_def) 

lemma sats_lambda_fm:
  assumes is_b_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|] 
        ==> is_b(a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,env))))"
  shows 
      "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
       ==> sats(A, lambda_fm(p,x,y), env) <-> 
           is_lambda(**A, nth(x,env), is_b, nth(y,env))"
by (simp add: lambda_fm_def sats_is_recfun_fm is_lambda_def is_b_iff_sats [THEN iff_sym]) 


lemma is_lambda_iff_sats:
  assumes is_b_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|] 
        ==> is_b(a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,env))))"
  shows
  "[|nth(i,env) = x; nth(j,env) = y; 
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_lambda(**A, x, is_b, y) <-> sats(A, lambda_fm(p,i,j), env)" 
by (simp add: sats_lambda_fm [OF is_b_iff_sats])

theorem is_lambda_reflection:
  assumes is_b_reflection:
    "!!f' f g h. REFLECTS[\<lambda>x. is_b(L, f'(x), f(x), g(x)), 
                     \<lambda>i x. is_b(**Lset(i), f'(x), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_lambda(L, A(x), is_b(L,x), f(x)), 
               \<lambda>i x. is_lambda(**Lset(i), A(x), is_b(**Lset(i),x), f(x))]"
apply (simp (no_asm_use) only: is_lambda_def setclass_simps)
apply (intro FOL_reflections is_b_reflection pair_reflection)
done


subsubsection{*The Operator @{term is_Member}, Internalized*}

(*    "is_Member(M,x,y,Z) ==
	\<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inl(M,p,u) & is_Inl(M,u,Z)" *)
constdefs Member_fm :: "[i,i,i]=>i"
    "Member_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inl_fm(1,0), Inl_fm(0,Z#+2)))))"

lemma is_Member_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Member_fm(x,y,z) \<in> formula"
by (simp add: Member_fm_def)

lemma sats_Member_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Member_fm(x,y,z), env) <->
        is_Member(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Member_fm_def is_Member_def)

lemma Member_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Member(**A, x, y, z) <-> sats(A, Member_fm(i,j,k), env)"
by (simp add: sats_Member_fm)

theorem Member_reflection:
     "REFLECTS[\<lambda>x. is_Member(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Member(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Member_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inl_reflection)
done

subsubsection{*The Operator @{term is_Equal}, Internalized*}

(*    "is_Equal(M,x,y,Z) ==
	\<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inr(M,p,u) & is_Inl(M,u,Z)" *)
constdefs Equal_fm :: "[i,i,i]=>i"
    "Equal_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inr_fm(1,0), Inl_fm(0,Z#+2)))))"

lemma is_Equal_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Equal_fm(x,y,z) \<in> formula"
by (simp add: Equal_fm_def)

lemma sats_Equal_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Equal_fm(x,y,z), env) <->
        is_Equal(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Equal_fm_def is_Equal_def)

lemma Equal_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Equal(**A, x, y, z) <-> sats(A, Equal_fm(i,j,k), env)"
by (simp add: sats_Equal_fm)

theorem Equal_reflection:
     "REFLECTS[\<lambda>x. is_Equal(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Equal(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Equal_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inl_reflection Inr_reflection)
done

subsubsection{*The Operator @{term is_Nand}, Internalized*}

(*    "is_Nand(M,x,y,Z) ==
	\<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inl(M,p,u) & is_Inr(M,u,Z)" *)
constdefs Nand_fm :: "[i,i,i]=>i"
    "Nand_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inl_fm(1,0), Inr_fm(0,Z#+2)))))"

lemma is_Nand_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Nand_fm(x,y,z) \<in> formula"
by (simp add: Nand_fm_def)

lemma sats_Nand_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Nand_fm(x,y,z), env) <->
        is_Nand(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Nand_fm_def is_Nand_def)

lemma Nand_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Nand(**A, x, y, z) <-> sats(A, Nand_fm(i,j,k), env)"
by (simp add: sats_Nand_fm)

theorem Nand_reflection:
     "REFLECTS[\<lambda>x. is_Nand(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Nand(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Nand_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inl_reflection Inr_reflection)
done

subsubsection{*The Operator @{term is_Forall}, Internalized*}

(* "is_Forall(M,p,Z) == \<exists>u[M]. is_Inr(M,p,u) & is_Inr(M,u,Z)" *)
constdefs Forall_fm :: "[i,i]=>i"
    "Forall_fm(x,Z) ==
       Exists(And(Inr_fm(succ(x),0), Inr_fm(0,succ(Z))))"

lemma is_Forall_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> Forall_fm(x,y) \<in> formula"
by (simp add: Forall_fm_def)

lemma sats_Forall_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, Forall_fm(x,y), env) <->
        is_Forall(**A, nth(x,env), nth(y,env))"
by (simp add: Forall_fm_def is_Forall_def)

lemma Forall_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_Forall(**A, x, y) <-> sats(A, Forall_fm(i,j), env)"
by (simp add: sats_Forall_fm)

theorem Forall_reflection:
     "REFLECTS[\<lambda>x. is_Forall(L,f(x),g(x)),
               \<lambda>i x. is_Forall(**Lset(i),f(x),g(x))]"
apply (simp only: is_Forall_def setclass_simps)
apply (intro FOL_reflections pair_reflection Inr_reflection)
done


subsubsection{*The Formula @{term is_formula_N}, Internalized*}

(* "is_nth(M,n,l,Z) == 
      \<exists>X[M]. \<exists>sn[M]. \<exists>msn[M]. 
       2       1       0
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_tl(M), l), msn, n, X) &
       is_hd(M,X,Z)" *)

(* "is_formula_N(M,n,Z) == 
      \<exists>zero[M]. \<exists>sn[M]. \<exists>msn[M]. 
          2       1       0
       empty(M,zero) & 
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_formula_functor(M),zero), msn, n, Z)" *) 
constdefs formula_N_fm :: "[i,i]=>i"
  "formula_N_fm(n,Z) == 
     Exists(Exists(Exists(
       And(empty_fm(2),
         And(succ_fm(n#+3,1),
          And(Memrel_fm(1,0),
              is_wfrec_fm(iterates_MH_fm(formula_functor_fm(1,0),7,2,1,0), 
                           0, n#+3, Z#+3)))))))"

lemma formula_N_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat |] ==> formula_N_fm(x,y) \<in> formula"
by (simp add: formula_N_fm_def)

lemma sats_formula_N_fm [simp]:
   "[| x < length(env); y < length(env); env \<in> list(A)|]
    ==> sats(A, formula_N_fm(x,y), env) <->
        is_formula_N(**A, nth(x,env), nth(y,env))"
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: formula_N_fm_def is_formula_N_def sats_is_wfrec_fm sats_iterates_MH_fm) 
done

lemma formula_N_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i < length(env); j < length(env); env \<in> list(A)|]
       ==> is_formula_N(**A, x, y) <-> sats(A, formula_N_fm(i,j), env)"
by (simp add: sats_formula_N_fm)

theorem formula_N_reflection:
     "REFLECTS[\<lambda>x. is_formula_N(L, f(x), g(x)),  
               \<lambda>i x. is_formula_N(**Lset(i), f(x), g(x))]"
apply (simp only: is_formula_N_def setclass_simps)
apply (intro FOL_reflections function_reflections is_wfrec_reflection 
             iterates_MH_reflection formula_functor_reflection) 
done



subsubsection{*The Predicate ``Is A Formula''*}

(*  mem_formula(M,p) == 
      \<exists>n[M]. \<exists>formn[M]. 
       finite_ordinal(M,n) & is_formula_N(M,n,formn) & p \<in> formn *)
constdefs mem_formula_fm :: "i=>i"
    "mem_formula_fm(x) ==
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(formula_N_fm(1,0), Member(x#+2,0)))))"

lemma mem_formula_type [TC]:
     "x \<in> nat ==> mem_formula_fm(x) \<in> formula"
by (simp add: mem_formula_fm_def)

lemma sats_mem_formula_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, mem_formula_fm(x), env) <-> mem_formula(**A, nth(x,env))"
by (simp add: mem_formula_fm_def mem_formula_def)

lemma mem_formula_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> mem_formula(**A, x) <-> sats(A, mem_formula_fm(i), env)"
by simp

theorem mem_formula_reflection:
     "REFLECTS[\<lambda>x. mem_formula(L,f(x)),
               \<lambda>i x. mem_formula(**Lset(i),f(x))]"
apply (simp only: mem_formula_def setclass_simps)
apply (intro FOL_reflections finite_ordinal_reflection formula_N_reflection)
done



subsubsection{*The Formula @{term is_depth}, Internalized*}

(*    "is_depth(M,p,n) == 
       \<exists>sn[M]. \<exists>formula_n[M]. \<exists>formula_sn[M]. 
         2          1                0
        is_formula_N(M,n,formula_n) & p \<notin> formula_n &
        successor(M,n,sn) & is_formula_N(M,sn,formula_sn) & p \<in> formula_sn" *)
constdefs depth_fm :: "[i,i]=>i"
  "depth_fm(p,n) == 
     Exists(Exists(Exists(
       And(formula_N_fm(n#+3,1),
         And(Neg(Member(p#+3,1)),
          And(succ_fm(n#+3,2),
           And(formula_N_fm(2,0), Member(p#+3,0))))))))"

lemma depth_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat |] ==> depth_fm(x,y) \<in> formula"
by (simp add: depth_fm_def)

lemma sats_depth_fm [simp]:
   "[| x \<in> nat; y < length(env); env \<in> list(A)|]
    ==> sats(A, depth_fm(x,y), env) <->
        is_depth(**A, nth(x,env), nth(y,env))"
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: depth_fm_def is_depth_def) 
done

lemma depth_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j < length(env); env \<in> list(A)|]
       ==> is_depth(**A, x, y) <-> sats(A, depth_fm(i,j), env)"
by (simp add: sats_depth_fm)

theorem depth_reflection:
     "REFLECTS[\<lambda>x. is_depth(L, f(x), g(x)),  
               \<lambda>i x. is_depth(**Lset(i), f(x), g(x))]"
apply (simp only: is_depth_def setclass_simps)
apply (intro FOL_reflections function_reflections formula_N_reflection) 
done



subsubsection{*The Operator @{term is_formula_case}*}

text{*The arguments of @{term is_a} are always 2, 1, 0, and the formula
      will be enclosed by three quantifiers.*}

(* is_formula_case :: 
    "[i=>o, [i,i,i]=>o, [i,i,i]=>o, [i,i,i]=>o, [i,i]=>o, i, i] => o"
  "is_formula_case(M, is_a, is_b, is_c, is_d, v, z) == 
      (\<forall>x[M]. \<forall>y[M]. x\<in>nat --> y\<in>nat --> is_Member(M,x,y,v) --> is_a(x,y,z)) &
      (\<forall>x[M]. \<forall>y[M]. x\<in>nat --> y\<in>nat --> is_Equal(M,x,y,v) --> is_b(x,y,z)) &
      (\<forall>x[M]. \<forall>y[M]. x\<in>formula --> y\<in>formula --> 
                     is_Nand(M,x,y,v) --> is_c(x,y,z)) &
      (\<forall>x[M]. x\<in>formula --> is_Forall(M,x,v) --> is_d(x,z))" *)

constdefs formula_case_fm :: "[i, i, i, i, i, i]=>i"
 "formula_case_fm(is_a, is_b, is_c, is_d, v, z) == 
        And(Forall(Forall(Implies(finite_ordinal_fm(1), 
                           Implies(finite_ordinal_fm(0), 
                            Implies(Member_fm(1,0,v#+2), 
                             Forall(Implies(Equal(0,z#+3), is_a))))))),
        And(Forall(Forall(Implies(finite_ordinal_fm(1), 
                           Implies(finite_ordinal_fm(0), 
                            Implies(Equal_fm(1,0,v#+2), 
                             Forall(Implies(Equal(0,z#+3), is_b))))))),
        And(Forall(Forall(Implies(mem_formula_fm(1), 
                           Implies(mem_formula_fm(0), 
                            Implies(Nand_fm(1,0,v#+2), 
                             Forall(Implies(Equal(0,z#+3), is_c))))))),
        Forall(Implies(mem_formula_fm(0), 
                       Implies(Forall_fm(0,succ(v)), 
                             Forall(Implies(Equal(0,z#+2), is_d))))))))"


lemma is_formula_case_type [TC]:
     "[| is_a \<in> formula;  is_b \<in> formula;  is_c \<in> formula;  is_d \<in> formula;  
         x \<in> nat; y \<in> nat |] 
      ==> formula_case_fm(is_a, is_b, is_c, is_d, x, y) \<in> formula"
by (simp add: formula_case_fm_def)

lemma sats_formula_case_fm:
  assumes is_a_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|]  
        ==> ISA(a2, a1, a0) <-> sats(A, is_a, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_b_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|]  
        ==> ISB(a2, a1, a0) <-> sats(A, is_b, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_c_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|]  
        ==> ISC(a2, a1, a0) <-> sats(A, is_c, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_d_iff_sats: 
      "!!a0 a1. 
        [|a0\<in>A; a1\<in>A|]  
        ==> ISD(a1, a0) <-> sats(A, is_d, Cons(a0,Cons(a1,env)))"
  shows 
      "[|x \<in> nat; y < length(env); env \<in> list(A)|]
       ==> sats(A, formula_case_fm(is_a,is_b,is_c,is_d,x,y), env) <->
           is_formula_case(**A, ISA, ISB, ISC, ISD, nth(x,env), nth(y,env))"
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: formula_case_fm_def is_formula_case_def 
                 is_a_iff_sats [THEN iff_sym] is_b_iff_sats [THEN iff_sym]
                 is_c_iff_sats [THEN iff_sym] is_d_iff_sats [THEN iff_sym])
done

lemma formula_case_iff_sats:
  assumes is_a_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|]  
        ==> ISA(a2, a1, a0) <-> sats(A, is_a, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_b_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|]  
        ==> ISB(a2, a1, a0) <-> sats(A, is_b, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_c_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|]  
        ==> ISC(a2, a1, a0) <-> sats(A, is_c, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_d_iff_sats: 
      "!!a0 a1. 
        [|a0\<in>A; a1\<in>A|]  
        ==> ISD(a1, a0) <-> sats(A, is_d, Cons(a0,Cons(a1,env)))"
  shows 
      "[|nth(i,env) = x; nth(j,env) = y; 
      i \<in> nat; j < length(env); env \<in> list(A)|]
       ==> is_formula_case(**A, ISA, ISB, ISC, ISD, x, y) <->
           sats(A, formula_case_fm(is_a,is_b,is_c,is_d,i,j), env)"
by (simp add: sats_formula_case_fm [OF is_a_iff_sats is_b_iff_sats 
                                       is_c_iff_sats is_d_iff_sats])


text{*The second argument of @{term is_a} gives it direct access to @{term x},
  which is essential for handling free variable references.  Treatment is
  based on that of @{text is_nat_case_reflection}.*}
theorem is_formula_case_reflection:
  assumes is_a_reflection:
    "!!h f g g'. REFLECTS[\<lambda>x. is_a(L, h(x), f(x), g(x), g'(x)),
                     \<lambda>i x. is_a(**Lset(i), h(x), f(x), g(x), g'(x))]"
  and is_b_reflection:
    "!!h f g g'. REFLECTS[\<lambda>x. is_b(L, h(x), f(x), g(x), g'(x)),
                     \<lambda>i x. is_b(**Lset(i), h(x), f(x), g(x), g'(x))]"
  and is_c_reflection:
    "!!h f g g'. REFLECTS[\<lambda>x. is_c(L, h(x), f(x), g(x), g'(x)),
                     \<lambda>i x. is_c(**Lset(i), h(x), f(x), g(x), g'(x))]"
  and is_d_reflection:
    "!!h f g g'. REFLECTS[\<lambda>x. is_d(L, h(x), f(x), g(x)),
                     \<lambda>i x. is_d(**Lset(i), h(x), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_formula_case(L, is_a(L,x), is_b(L,x), is_c(L,x), is_d(L,x), g(x), h(x)),
               \<lambda>i x. is_formula_case(**Lset(i), is_a(**Lset(i), x), is_b(**Lset(i), x), is_c(**Lset(i), x), is_d(**Lset(i), x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_formula_case_def setclass_simps)
apply (intro FOL_reflections function_reflections finite_ordinal_reflection
         mem_formula_reflection
         Member_reflection Equal_reflection Nand_reflection Forall_reflection
         is_a_reflection is_b_reflection is_c_reflection is_d_reflection)
done



subsection {*Absoluteness for @{term formula_rec}*}

constdefs

  formula_rec_case :: "[[i,i]=>i, [i,i]=>i, [i,i,i,i]=>i, [i,i]=>i, i, i] => i"
    --{* the instance of @{term formula_case} in @{term formula_rec}*}
   "formula_rec_case(a,b,c,d,h) ==
        formula_case (a, b,
                \<lambda>u v. c(u, v, h ` succ(depth(u)) ` u, 
                              h ` succ(depth(v)) ` v),
                \<lambda>u. d(u, h ` succ(depth(u)) ` u))"

  is_formula_rec :: "[i=>o, [i,i,i]=>o, 
                      [i,i]=>i, [i,i]=>i, [i,i,i,i]=>i, [i,i]=>i, 
                      i, i] => o"
    --{* predicate to relative the functional @{term formula_rec}*}
   "is_formula_rec(M,MH,a,b,c,d,p,z)  ==
    \<exists>i[M]. \<exists>f[M]. i = succ(depth(p)) & fun_apply(M,f,p,z) &
                  is_transrec(M,MH,i,f)"

text{*Unfold @{term formula_rec} to @{term formula_rec_case}*}
lemma (in M_triv_axioms) formula_rec_eq2:
  "p \<in> formula ==>
   formula_rec(a,b,c,d,p) = 
   transrec (succ(depth(p)),
             \<lambda>x h. Lambda (formula, formula_rec_case(a,b,c,d,h))) ` p"
by (simp add: formula_rec_eq  formula_rec_case_def)


text{*Sufficient conditions to relative the instance of @{term formula_case}
      in @{term formula_rec}*}
lemma (in M_datatypes) Relativize1_formula_rec_case:
     "[|Relativize2(M, nat, nat, is_a, a);
        Relativize2(M, nat, nat, is_b, b);
        Relativize2 (M, formula, formula, 
           is_c, \<lambda>u v. c(u, v, h`succ(depth(u))`u, h`succ(depth(v))`v));
        Relativize1(M, formula, 
           is_d, \<lambda>u. d(u, h ` succ(depth(u)) ` u));
 	M(h) |] 
      ==> Relativize1(M, formula,
                         is_formula_case (M, is_a, is_b, is_c, is_d),
                         formula_rec_case(a, b, c, d, h))"
apply (simp (no_asm) add: formula_rec_case_def Relativize1_def) 
apply (simp add: formula_case_abs) 
done


text{*This locale packages the premises of the following theorems,
      which is the normal purpose of locales.  It doesn't accumulate
      constraints on the class @{term M}, as in most of this deveopment.*}
locale M_formula_rec = M_eclose +
  fixes a and is_a and b and is_b and c and is_c and d and is_d and MH
  defines
      "MH(u::i,f,z) ==
	is_lambda
	 (M, formula, is_formula_case (M, is_a, is_b, is_c(f), is_d(f)), z)"

  assumes a_closed: "[|x\<in>nat; y\<in>nat|] ==> M(a(x,y))"
      and a_rel:    "Relativize2(M, nat, nat, is_a, a)"
      and b_closed: "[|x\<in>nat; y\<in>nat|] ==> M(b(x,y))"
      and b_rel:    "Relativize2(M, nat, nat, is_b, b)"
      and c_closed: "[|x \<in> formula; y \<in> formula; M(gx); M(gy)|]
                     ==> M(c(x, y, gx, gy))"
      and c_rel:
         "M(f) ==> 
          Relativize2 (M, formula, formula, is_c(f),
             \<lambda>u v. c(u, v, f ` succ(depth(u)) ` u, f ` succ(depth(v)) ` v))"
      and d_closed: "[|x \<in> formula; M(gx)|] ==> M(d(x, gx))"
      and d_rel:
         "M(f) ==> 
          Relativize1(M, formula, is_d(f), \<lambda>u. d(u, f ` succ(depth(u)) ` u))"
      and fr_replace: "n \<in> nat ==> transrec_replacement(M,MH,n)"
      and fr_lam_replace:
           "M(g) ==>
            strong_replacement
	      (M, \<lambda>x y. x \<in> formula &
		  y = \<langle>x, formula_rec_case(a,b,c,d,g,x)\<rangle>)";

lemma (in M_formula_rec) formula_rec_case_closed:
    "[|M(g); p \<in> formula|] ==> M(formula_rec_case(a, b, c, d, g, p))"
by (simp add: formula_rec_case_def a_closed b_closed c_closed d_closed) 

lemma (in M_formula_rec) formula_rec_lam_closed:
    "M(g) ==> M(Lambda (formula, formula_rec_case(a,b,c,d,g)))"
by (simp add: lam_closed2 fr_lam_replace formula_rec_case_closed)

lemma (in M_formula_rec) MH_rel2:
     "relativize2 (M, MH,
             \<lambda>x h. Lambda (formula, formula_rec_case(a,b,c,d,h)))"
apply (simp add: relativize2_def MH_def, clarify) 
apply (rule lambda_abs2) 
apply (rule fr_lam_replace, assumption)
apply (rule Relativize1_formula_rec_case)  
apply (simp_all add: a_rel b_rel c_rel d_rel formula_rec_case_closed) 
done

lemma (in M_formula_rec) fr_transrec_closed:
    "n \<in> nat
     ==> M(transrec
          (n, \<lambda>x h. Lambda(formula, formula_rec_case(a, b, c, d, h))))"
by (simp add: transrec_closed [OF fr_replace MH_rel2]  
              nat_into_M formula_rec_lam_closed) 

text{*The main two results: @{term formula_rec} is absolute for @{term M}.*}
theorem (in M_formula_rec) formula_rec_closed:
    "p \<in> formula ==> M(formula_rec(a,b,c,d,p))"
by (simp add: formula_rec_eq2 fr_transrec_closed 
              transM [OF _ formula_closed])

theorem (in M_formula_rec) formula_rec_abs:
  "[| p \<in> formula; M(z)|] 
   ==> is_formula_rec(M,MH,a,b,c,d,p,z) <-> z = formula_rec(a,b,c,d,p)" 
by (simp add: is_formula_rec_def formula_rec_eq2 transM [OF _ formula_closed]
              transrec_abs [OF fr_replace MH_rel2] 
              fr_transrec_closed formula_rec_lam_closed eq_commute)


subsection {*Absoluteness for the Function @{term satisfies}*}

constdefs
  is_depth_apply :: "[i=>o,i,i,i] => o"
   --{*Merely a useful abbreviation for the sequel.*}
   "is_depth_apply(M,h,p,z) ==
    \<exists>dp[M]. \<exists>sdp[M]. \<exists>hsdp[M]. 
	dp \<in> nat & is_depth(M,p,dp) & successor(M,dp,sdp) &
	fun_apply(M,h,sdp,hsdp) & fun_apply(M,hsdp,p,z)"

lemma (in M_datatypes) is_depth_apply_abs [simp]:
     "[|M(h); p \<in> formula; M(z)|] 
      ==> is_depth_apply(M,h,p,z) <-> z = h ` succ(depth(p)) ` p"
by (simp add: is_depth_apply_def formula_into_M depth_type eq_commute)

lemma depth_apply_reflection:
     "REFLECTS[\<lambda>x. is_depth_apply(L,f(x),g(x),h(x)),
               \<lambda>i x. is_depth_apply(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_depth_apply_def setclass_simps)
apply (intro FOL_reflections function_reflections depth_reflection)
done


text{*There is at present some redundancy between the relativizations in
 e.g. @{text satisfies_is_a} and those in e.g. @{text Member_replacement}.*}

text{*These constants let us instantiate the parameters @{term a}, @{term b},
      @{term c}, @{term d}, etc., of the locale @{text M_formula_rec}.*}
constdefs
  satisfies_a :: "[i,i,i]=>i"
   "satisfies_a(A) == 
    \<lambda>x y. \<lambda>env \<in> list(A). bool_of_o (nth(x,env) \<in> nth(y,env))"

  satisfies_is_a :: "[i=>o,i,i,i,i]=>o"
   "satisfies_is_a(M,A) == 
    \<lambda>x y. is_lambda(M, list(A), 
        \<lambda>env z. is_bool_of_o(M, \<exists>nx[M]. \<exists>ny[M]. 
                  is_nth(M,x,env,nx) & is_nth(M,y,env,ny) & nx \<in> ny, z))"

  satisfies_b :: "[i,i,i]=>i"
   "satisfies_b(A) ==
    \<lambda>x y. \<lambda>env \<in> list(A). bool_of_o (nth(x,env) = nth(y,env))"

  satisfies_is_b :: "[i=>o,i,i,i,i]=>o"
   --{*We simplify the formula to have just @{term nx} rather than 
       introducing @{term ny} with  @{term "nx=ny"} *}
   "satisfies_is_b(M,A) == 
    \<lambda>x y. is_lambda(M, list(A), 
         \<lambda>env z. 
         is_bool_of_o(M, \<exists>nx[M]. is_nth(M,x,env,nx) & is_nth(M,y,env,nx), z))"
 
  satisfies_c :: "[i,i,i,i,i]=>i"
   "satisfies_c(A,p,q,rp,rq) == \<lambda>env \<in> list(A). not(rp ` env and rq ` env)"

  satisfies_is_c :: "[i=>o,i,i,i,i,i]=>o"
   "satisfies_is_c(M,A,h) == 
    \<lambda>p q. is_lambda(M, list(A), 
        \<lambda>env z. \<exists>hp[M]. \<exists>hq[M]. 
		 (\<exists>rp[M]. is_depth_apply(M,h,p,rp) & fun_apply(M,rp,env,hp)) & 
		 (\<exists>rq[M]. is_depth_apply(M,h,q,rq) & fun_apply(M,rq,env,hq)) & 
                 (\<exists>pq[M]. is_and(M,hp,hq,pq) & is_not(M,pq,z)))"

  satisfies_d :: "[i,i,i]=>i"
   "satisfies_d(A) 
    == \<lambda>p rp. \<lambda>env \<in> list(A). bool_of_o (\<forall>x\<in>A. rp ` (Cons(x,env)) = 1)"

  satisfies_is_d :: "[i=>o,i,i,i,i]=>o"
   "satisfies_is_d(M,A,h) == 
    \<lambda>p. is_lambda(M, list(A), 
        \<lambda>env z. \<exists>rp[M]. is_depth_apply(M,h,p,rp) & 
           is_bool_of_o(M, 
                \<forall>x[M]. \<forall>xenv[M]. \<forall>hp[M]. 
                       x\<in>A --> is_Cons(M,x,env,xenv) --> 
                       fun_apply(M,rp,xenv,hp) --> number1(M,hp),
                  z))"

  satisfies_MH :: "[i=>o,i,i,i,i]=>o"
   "satisfies_MH == 
    \<lambda>M A u f. is_lambda
	 (M, formula, 
          is_formula_case (M, satisfies_is_a(M,A), 
                           satisfies_is_b(M,A), 
                           satisfies_is_c(M,A,f), satisfies_is_d(M,A,f)))"


text{*Further constraints on the class @{term M} in order to prove
      absoluteness for the constants defined above.  The ultimate goal
      is the absoluteness of the function @{term satisfies}. *}
locale M_satisfies = M_datatypes +
 assumes 
   Member_replacement:
    "[|M(A); x \<in> nat; y \<in> nat|]
     ==> strong_replacement
	 (M, \<lambda>env z. \<exists>bo[M]. \<exists>nx[M]. \<exists>ny[M]. 
              env \<in> list(A) & is_nth(M,x,env,nx) & is_nth(M,y,env,ny) & 
              is_bool_of_o(M, nx \<in> ny, bo) &
              pair(M, env, bo, z))"
 and
   Equal_replacement:
    "[|M(A); x \<in> nat; y \<in> nat|]
     ==> strong_replacement
	 (M, \<lambda>env z. \<exists>bo[M]. \<exists>nx[M]. \<exists>ny[M]. 
              env \<in> list(A) & is_nth(M,x,env,nx) & is_nth(M,y,env,ny) & 
              is_bool_of_o(M, nx = ny, bo) &
              pair(M, env, bo, z))"
 and
   Nand_replacement:
    "[|M(A); M(rp); M(rq)|]
     ==> strong_replacement
	 (M, \<lambda>env z. \<exists>rpe[M]. \<exists>rqe[M]. \<exists>andpq[M]. \<exists>notpq[M]. 
               fun_apply(M,rp,env,rpe) & fun_apply(M,rq,env,rqe) & 
               is_and(M,rpe,rqe,andpq) & is_not(M,andpq,notpq) & 
               env \<in> list(A) & pair(M, env, notpq, z))"
 and
  Forall_replacement:
   "[|M(A); M(rp)|]
    ==> strong_replacement
	(M, \<lambda>env z. \<exists>bo[M]. 
	      env \<in> list(A) & 
	      is_bool_of_o (M, 
			    \<forall>a[M]. \<forall>co[M]. \<forall>rpco[M]. 
			       a\<in>A --> is_Cons(M,a,env,co) -->
			       fun_apply(M,rp,co,rpco) --> number1(M, rpco), 
                            bo) &
	      pair(M,env,bo,z))"
 and
  formula_rec_replacement: 
      --{*For the @{term transrec}*}
   "[|n \<in> nat; M(A)|] ==> transrec_replacement(M, satisfies_MH(M,A), n)"
(*NEEDS RELATIVIZATION?*)
 and
  formula_rec_lambda_replacement:  
      --{*For the @{text "\<lambda>-abstraction"} in the @{term transrec} body*}
   "M(g) ==>
    strong_replacement (M, \<lambda>x y. x \<in> formula &
            y = \<langle>x, 
                 formula_rec_case(satisfies_a(A),
                                  satisfies_b(A),
                                  satisfies_c(A),
                                  satisfies_d(A), g, x)\<rangle>)"


lemma (in M_satisfies) Member_replacement':
    "[|M(A); x \<in> nat; y \<in> nat|]
     ==> strong_replacement
	 (M, \<lambda>env z. env \<in> list(A) &
		     z = \<langle>env, bool_of_o(nth(x, env) \<in> nth(y, env))\<rangle>)"
by (insert Member_replacement, simp) 

lemma (in M_satisfies) Equal_replacement':
    "[|M(A); x \<in> nat; y \<in> nat|]
     ==> strong_replacement
	 (M, \<lambda>env z. env \<in> list(A) &
		     z = \<langle>env, bool_of_o(nth(x, env) = nth(y, env))\<rangle>)"
by (insert Equal_replacement, simp) 

lemma (in M_satisfies) Nand_replacement':
    "[|M(A); M(rp); M(rq)|]
     ==> strong_replacement
	 (M, \<lambda>env z. env \<in> list(A) & z = \<langle>env, not(rp`env and rq`env)\<rangle>)"
by (insert Nand_replacement, simp) 

lemma (in M_satisfies) Forall_replacement':
   "[|M(A); M(rp)|]
    ==> strong_replacement
	(M, \<lambda>env z.
	       env \<in> list(A) &
	       z = \<langle>env, bool_of_o (\<forall>a\<in>A. rp ` Cons(a,env) = 1)\<rangle>)"
by (insert Forall_replacement, simp) 

lemma (in M_satisfies) a_closed:
     "[|M(A); x\<in>nat; y\<in>nat|] ==> M(satisfies_a(A,x,y))"
apply (simp add: satisfies_a_def) 
apply (blast intro: lam_closed2 Member_replacement') 
done

lemma (in M_satisfies) a_rel:
     "M(A) ==> Relativize2(M, nat, nat, satisfies_is_a(M,A), satisfies_a(A))"
apply (simp add: Relativize2_def satisfies_is_a_def satisfies_a_def)
apply (simp add: lambda_abs2 [OF Member_replacement'] Relativize1_def)
done

lemma (in M_satisfies) b_closed:
     "[|M(A); x\<in>nat; y\<in>nat|] ==> M(satisfies_b(A,x,y))"
apply (simp add: satisfies_b_def) 
apply (blast intro: lam_closed2 Equal_replacement') 
done

lemma (in M_satisfies) b_rel:
     "M(A) ==> Relativize2(M, nat, nat, satisfies_is_b(M,A), satisfies_b(A))"
apply (simp add: Relativize2_def satisfies_is_b_def satisfies_b_def)
apply (simp add: lambda_abs2 [OF Equal_replacement'] Relativize1_def)
done

lemma (in M_satisfies) c_closed:
     "[|M(A); x \<in> formula; y \<in> formula; M(rx); M(ry)|] 
      ==> M(satisfies_c(A,x,y,rx,ry))"
apply (simp add: satisfies_c_def) 
apply (rule lam_closed2) 
apply (rule Nand_replacement') 
apply (simp_all add: formula_into_M list_into_M [of _ A])
done

lemma (in M_satisfies) c_rel:
 "[|M(A); M(f)|] ==> 
  Relativize2 (M, formula, formula, 
               satisfies_is_c(M,A,f),
	       \<lambda>u v. satisfies_c(A, u, v, f ` succ(depth(u)) ` u, 
					  f ` succ(depth(v)) ` v))"
apply (simp add: Relativize2_def satisfies_is_c_def satisfies_c_def)
apply (simp add: lambda_abs2 [OF Nand_replacement' triv_Relativize1] 
                 formula_into_M)
done

lemma (in M_satisfies) d_closed:
     "[|M(A); x \<in> formula; M(rx)|] ==> M(satisfies_d(A,x,rx))"
apply (simp add: satisfies_d_def) 
apply (rule lam_closed2) 
apply (rule Forall_replacement') 
apply (simp_all add: formula_into_M list_into_M [of _ A])
done

lemma (in M_satisfies) d_rel:
 "[|M(A); M(f)|] ==> 
  Relativize1(M, formula, satisfies_is_d(M,A,f), 
     \<lambda>u. satisfies_d(A, u, f ` succ(depth(u)) ` u))"
apply (simp del: rall_abs 
            add: Relativize1_def satisfies_is_d_def satisfies_d_def)
apply (simp add: lambda_abs2 [OF Forall_replacement' triv_Relativize1] 
                 formula_into_M)
done


lemma (in M_satisfies) fr_replace:
      "[|n \<in> nat; M(A)|] ==> transrec_replacement(M,satisfies_MH(M,A),n)" 
by (blast intro: formula_rec_replacement) 

lemma (in M_satisfies) fr_lam_replace:
   "M(g) ==>
    strong_replacement (M, \<lambda>x y. x \<in> formula &
            y = \<langle>x, 
                 formula_rec_case(satisfies_a(A),
                                  satisfies_b(A),
                                  satisfies_c(A),
                                  satisfies_d(A), g, x)\<rangle>)"
by (blast intro: formula_rec_lambda_replacement)



subsection{*Instantiating the Locale @{text "M_satisfies"}*}


subsubsection{*The @{term "Member"} Case*}

lemma Member_Reflects:
 "REFLECTS[\<lambda>u. \<exists>v[L]. v \<in> B \<and> (\<exists>bo[L]. \<exists>nx[L]. \<exists>ny[L].
          v \<in> lstA \<and> is_nth(L,x,v,nx) \<and> is_nth(L,y,v,ny) \<and>
          is_bool_of_o(L, nx \<in> ny, bo) \<and> pair(L,v,bo,u)),
   \<lambda>i u. \<exists>v \<in> Lset(i). v \<in> B \<and> (\<exists>bo \<in> Lset(i). \<exists>nx \<in> Lset(i). \<exists>ny \<in> Lset(i).
             v \<in> lstA \<and> is_nth(**Lset(i), x, v, nx) \<and> 
             is_nth(**Lset(i), y, v, ny) \<and>
          is_bool_of_o(**Lset(i), nx \<in> ny, bo) \<and> pair(**Lset(i), v, bo, u))]"
by (intro FOL_reflections function_reflections nth_reflection 
          bool_of_o_reflection)


lemma Member_replacement:
    "[|L(A); x \<in> nat; y \<in> nat|]
     ==> strong_replacement
	 (L, \<lambda>env z. \<exists>bo[L]. \<exists>nx[L]. \<exists>ny[L]. 
              env \<in> list(A) & is_nth(L,x,env,nx) & is_nth(L,y,env,ny) & 
              is_bool_of_o(L, nx \<in> ny, bo) &
              pair(L, env, bo, z))"
apply (frule list_closed) 
apply (rule strong_replacementI) 
apply (rule rallI)
apply (rename_tac B)  
apply (rule separation_CollectI) 
apply (rule_tac A="{list(A),B,x,y,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF Member_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (simp add: is_nth_def is_wfrec_def is_bool_of_o_def)
apply (rule DPow_LsetI)
apply (rename_tac u) 
apply (rule bex_iff_sats conj_iff_sats conj_iff_sats)+
apply (rule_tac env = "[v,u,list(A),B,x,y,z]" in mem_iff_sats) 
apply (rule sep_rules is_nat_case_iff_sats iterates_MH_iff_sats
            is_recfun_iff_sats hd_iff_sats tl_iff_sats quasinat_iff_sats
     | simp)+
done


subsubsection{*The @{term "Equal"} Case*}

lemma Equal_Reflects:
 "REFLECTS[\<lambda>u. \<exists>v[L]. v \<in> B \<and> (\<exists>bo[L]. \<exists>nx[L]. \<exists>ny[L].
          v \<in> lstA \<and> is_nth(L, x, v, nx) \<and> is_nth(L, y, v, ny) \<and>
          is_bool_of_o(L, nx = ny, bo) \<and> pair(L, v, bo, u)),
   \<lambda>i u. \<exists>v \<in> Lset(i). v \<in> B \<and> (\<exists>bo \<in> Lset(i). \<exists>nx \<in> Lset(i). \<exists>ny \<in> Lset(i).
             v \<in> lstA \<and> is_nth(**Lset(i), x, v, nx) \<and> 
             is_nth(**Lset(i), y, v, ny) \<and>
          is_bool_of_o(**Lset(i), nx = ny, bo) \<and> pair(**Lset(i), v, bo, u))]"
by (intro FOL_reflections function_reflections nth_reflection 
          bool_of_o_reflection)


lemma Equal_replacement:
    "[|L(A); x \<in> nat; y \<in> nat|]
     ==> strong_replacement
	 (L, \<lambda>env z. \<exists>bo[L]. \<exists>nx[L]. \<exists>ny[L]. 
              env \<in> list(A) & is_nth(L,x,env,nx) & is_nth(L,y,env,ny) & 
              is_bool_of_o(L, nx = ny, bo) &
              pair(L, env, bo, z))"
apply (frule list_closed) 
apply (rule strong_replacementI) 
apply (rule rallI)
apply (rename_tac B)  
apply (rule separation_CollectI) 
apply (rule_tac A="{list(A),B,x,y,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF Equal_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (simp add: is_nth_def is_wfrec_def is_bool_of_o_def)
apply (rule DPow_LsetI)
apply (rename_tac u) 
apply (rule bex_iff_sats conj_iff_sats conj_iff_sats)+
apply (rule_tac env = "[v,u,list(A),B,x,y,z]" in mem_iff_sats) 
apply (rule sep_rules is_nat_case_iff_sats iterates_MH_iff_sats
            is_recfun_iff_sats hd_iff_sats tl_iff_sats quasinat_iff_sats
     | simp)+
done

subsubsection{*The @{term "Nand"} Case*}

lemma Nand_Reflects:
    "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B \<and>
	       (\<exists>rpe[L]. \<exists>rqe[L]. \<exists>andpq[L]. \<exists>notpq[L].
		 fun_apply(L, rp, u, rpe) \<and> fun_apply(L, rq, u, rqe) \<and>
		 is_and(L, rpe, rqe, andpq) \<and> is_not(L, andpq, notpq) \<and>
		 u \<in> list(A) \<and> pair(L, u, notpq, x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and>
     (\<exists>rpe \<in> Lset(i). \<exists>rqe \<in> Lset(i). \<exists>andpq \<in> Lset(i). \<exists>notpq \<in> Lset(i).
       fun_apply(**Lset(i), rp, u, rpe) \<and> fun_apply(**Lset(i), rq, u, rqe) \<and>
       is_and(**Lset(i), rpe, rqe, andpq) \<and> is_not(**Lset(i), andpq, notpq) \<and>
       u \<in> list(A) \<and> pair(**Lset(i), u, notpq, x))]"
apply (unfold is_and_def is_not_def) 
apply (intro FOL_reflections function_reflections)
done

lemma Nand_replacement:
    "[|L(A); L(rp); L(rq)|]
     ==> strong_replacement
	 (L, \<lambda>env z. \<exists>rpe[L]. \<exists>rqe[L]. \<exists>andpq[L]. \<exists>notpq[L]. 
               fun_apply(L,rp,env,rpe) & fun_apply(L,rq,env,rqe) & 
               is_and(L,rpe,rqe,andpq) & is_not(L,andpq,notpq) & 
               env \<in> list(A) & pair(L, env, notpq, z))"
apply (frule list_closed) 
apply (rule strong_replacementI) 
apply (rule rallI)
apply (rename_tac B)  
apply (rule separation_CollectI) 
apply (rule_tac A="{list(A),B,rp,rq,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF Nand_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (simp add: is_and_def is_not_def)
apply (rule DPow_LsetI)
apply (rename_tac v) 
apply (rule bex_iff_sats conj_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,list(A),B,rp,rq,z]" in mem_iff_sats) 
apply (rule sep_rules | simp)+
done


subsubsection{*The @{term "Forall"} Case*}

lemma Forall_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>bo[L]. u \<in> list(A) \<and>
                 is_bool_of_o (L,
     \<forall>a[L]. \<forall>co[L]. \<forall>rpco[L]. a \<in> A \<longrightarrow>
                is_Cons(L,a,u,co) \<longrightarrow> fun_apply(L,rp,co,rpco) \<longrightarrow> 
                number1(L,rpco),
                           bo) \<and> pair(L,u,bo,x)),
 \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>bo \<in> Lset(i). u \<in> list(A) \<and>
        is_bool_of_o (**Lset(i),
 \<forall>a \<in> Lset(i). \<forall>co \<in> Lset(i). \<forall>rpco \<in> Lset(i). a \<in> A \<longrightarrow>
	    is_Cons(**Lset(i),a,u,co) \<longrightarrow> fun_apply(**Lset(i),rp,co,rpco) \<longrightarrow> 
	    number1(**Lset(i),rpco),
		       bo) \<and> pair(**Lset(i),u,bo,x))]"
apply (unfold is_bool_of_o_def) 
apply (intro FOL_reflections function_reflections Cons_reflection)
done

lemma Forall_replacement:
   "[|L(A); L(rp)|]
    ==> strong_replacement
	(L, \<lambda>env z. \<exists>bo[L]. 
	      env \<in> list(A) & 
	      is_bool_of_o (L, 
			    \<forall>a[L]. \<forall>co[L]. \<forall>rpco[L]. 
			       a\<in>A --> is_Cons(L,a,env,co) -->
			       fun_apply(L,rp,co,rpco) --> number1(L, rpco), 
                            bo) &
	      pair(L,env,bo,z))"
apply (frule list_closed) 
apply (rule strong_replacementI) 
apply (rule rallI)
apply (rename_tac B)  
apply (rule separation_CollectI) 
apply (rule_tac A="{A,list(A),B,rp,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF Forall_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (simp add: is_bool_of_o_def)
apply (rule DPow_LsetI)
apply (rename_tac v) 
apply (rule bex_iff_sats conj_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,list(A),B,rp,z]" in mem_iff_sats)
apply (rule sep_rules Cons_iff_sats | simp)+
done

subsubsection{*The @{term "transrec_replacement"} Case*}



theorem satisfies_is_a_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_a(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_a(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold satisfies_is_a_def) 
apply (intro FOL_reflections is_lambda_reflection bool_of_o_reflection 
             nth_reflection)
done


theorem satisfies_is_b_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_b(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_b(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold satisfies_is_b_def) 
apply (intro FOL_reflections is_lambda_reflection bool_of_o_reflection 
             nth_reflection)
done

theorem satisfies_is_c_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_c(L,f(x),g(x),h(x),g'(x),h'(x)),
               \<lambda>i x. satisfies_is_c(**Lset(i),f(x),g(x),h(x),g'(x),h'(x))]"
apply (unfold satisfies_is_c_def ) 
apply (intro FOL_reflections function_reflections is_lambda_reflection
             bool_of_o_reflection not_reflection and_reflection
             nth_reflection depth_apply_reflection)
done

theorem satisfies_is_d_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_d(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_d(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold satisfies_is_d_def ) 
apply (intro FOL_reflections function_reflections is_lambda_reflection
             bool_of_o_reflection not_reflection and_reflection
             nth_reflection depth_apply_reflection Cons_reflection)
done


lemma formula_rec_replacement_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L, u, y, x) \<and>
             is_wfrec (L, satisfies_MH(L,A), mesa, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
             is_wfrec (**Lset(i), satisfies_MH(**Lset(i),A), mesa, u, y))]"
apply (unfold satisfies_MH_def) 
apply (intro FOL_reflections function_reflections is_wfrec_reflection
             is_lambda_reflection) 
apply (simp only: is_formula_case_def) 
apply (intro FOL_reflections finite_ordinal_reflection mem_formula_reflection
          Member_reflection Equal_reflection Nand_reflection Forall_reflection
          satisfies_is_a_reflection satisfies_is_b_reflection 
          satisfies_is_c_reflection satisfies_is_d_reflection)
done

end



