(*  Title:      ZF/Constructible/Satisfies_absolute.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
*)

header {*Absoluteness for the Satisfies Relation on Formulas*}

theory Satisfies_absolute = Datatype_absolute + Rec_Separation: 



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

  is_formula_rec :: "[i=>o, [i,i,i]=>o, i, i] => o"
    --{* predicate to relativize the functional @{term formula_rec}*}
   "is_formula_rec(M,MH,p,z)  ==
      \<exists>dp[M]. \<exists>i[M]. \<exists>f[M]. finite_ordinal(M,dp) & is_depth(M,p,dp) & 
             successor(M,dp,i) & fun_apply(M,f,p,z) & is_transrec(M,MH,i,f)"

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
locale Formula_Rec = M_eclose +
  fixes a and is_a and b and is_b and c and is_c and d and is_d and MH
  defines
      "MH(u::i,f,z) ==
	\<forall>fml[M]. is_formula(M,fml) -->
             is_lambda
	 (M, fml, is_formula_case (M, is_a, is_b, is_c(f), is_d(f)), z)"

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

lemma (in Formula_Rec) formula_rec_case_closed:
    "[|M(g); p \<in> formula|] ==> M(formula_rec_case(a, b, c, d, g, p))"
by (simp add: formula_rec_case_def a_closed b_closed c_closed d_closed) 

lemma (in Formula_Rec) formula_rec_lam_closed:
    "M(g) ==> M(Lambda (formula, formula_rec_case(a,b,c,d,g)))"
by (simp add: lam_closed2 fr_lam_replace formula_rec_case_closed)

lemma (in Formula_Rec) MH_rel2:
     "relativize2 (M, MH,
             \<lambda>x h. Lambda (formula, formula_rec_case(a,b,c,d,h)))"
apply (simp add: relativize2_def MH_def, clarify) 
apply (rule lambda_abs2) 
apply (rule fr_lam_replace, assumption)
apply (rule Relativize1_formula_rec_case)  
apply (simp_all add: a_rel b_rel c_rel d_rel formula_rec_case_closed) 
done

lemma (in Formula_Rec) fr_transrec_closed:
    "n \<in> nat
     ==> M(transrec
          (n, \<lambda>x h. Lambda(formula, formula_rec_case(a, b, c, d, h))))"
by (simp add: transrec_closed [OF fr_replace MH_rel2]  
              nat_into_M formula_rec_lam_closed) 

text{*The main two results: @{term formula_rec} is absolute for @{term M}.*}
theorem (in Formula_Rec) formula_rec_closed:
    "p \<in> formula ==> M(formula_rec(a,b,c,d,p))"
by (simp add: formula_rec_eq2 fr_transrec_closed 
              transM [OF _ formula_closed])

theorem (in Formula_Rec) formula_rec_abs:
  "[| p \<in> formula; M(z)|] 
   ==> is_formula_rec(M,MH,p,z) <-> z = formula_rec(a,b,c,d,p)" 
by (simp add: is_formula_rec_def formula_rec_eq2 transM [OF _ formula_closed]
              transrec_abs [OF fr_replace MH_rel2] depth_type
              fr_transrec_closed formula_rec_lam_closed eq_commute)


subsection {*Absoluteness for the Function @{term satisfies}*}

constdefs
  is_depth_apply :: "[i=>o,i,i,i] => o"
   --{*Merely a useful abbreviation for the sequel.*}
   "is_depth_apply(M,h,p,z) ==
    \<exists>dp[M]. \<exists>sdp[M]. \<exists>hsdp[M]. 
	finite_ordinal(M,dp) & is_depth(M,p,dp) & successor(M,dp,sdp) &
	fun_apply(M,h,sdp,hsdp) & fun_apply(M,hsdp,p,z)"

lemma (in M_datatypes) is_depth_apply_abs [simp]:
     "[|M(h); p \<in> formula; M(z)|] 
      ==> is_depth_apply(M,h,p,z) <-> z = h ` succ(depth(p)) ` p"
by (simp add: is_depth_apply_def formula_into_M depth_type eq_commute)



text{*There is at present some redundancy between the relativizations in
 e.g. @{text satisfies_is_a} and those in e.g. @{text Member_replacement}.*}

text{*These constants let us instantiate the parameters @{term a}, @{term b},
      @{term c}, @{term d}, etc., of the locale @{text Formula_Rec}.*}
constdefs
  satisfies_a :: "[i,i,i]=>i"
   "satisfies_a(A) == 
    \<lambda>x y. \<lambda>env \<in> list(A). bool_of_o (nth(x,env) \<in> nth(y,env))"

  satisfies_is_a :: "[i=>o,i,i,i,i]=>o"
   "satisfies_is_a(M,A) == 
    \<lambda>x y zz. \<forall>lA[M]. is_list(M,A,lA) -->
             is_lambda(M, lA, 
		\<lambda>env z. is_bool_of_o(M, 
                      \<exists>nx[M]. \<exists>ny[M]. 
 		       is_nth(M,x,env,nx) & is_nth(M,y,env,ny) & nx \<in> ny, z),
                zz)"

  satisfies_b :: "[i,i,i]=>i"
   "satisfies_b(A) ==
    \<lambda>x y. \<lambda>env \<in> list(A). bool_of_o (nth(x,env) = nth(y,env))"

  satisfies_is_b :: "[i=>o,i,i,i,i]=>o"
   --{*We simplify the formula to have just @{term nx} rather than 
       introducing @{term ny} with  @{term "nx=ny"} *}
   "satisfies_is_b(M,A) == 
    \<lambda>x y zz. \<forall>lA[M]. is_list(M,A,lA) -->
             is_lambda(M, lA, 
                \<lambda>env z. is_bool_of_o(M, 
                      \<exists>nx[M]. is_nth(M,x,env,nx) & is_nth(M,y,env,nx), z),
                zz)"
 
  satisfies_c :: "[i,i,i,i,i]=>i"
   "satisfies_c(A) == \<lambda>p q rp rq. \<lambda>env \<in> list(A). not(rp ` env and rq ` env)"

  satisfies_is_c :: "[i=>o,i,i,i,i,i]=>o"
   "satisfies_is_c(M,A,h) == 
    \<lambda>p q zz. \<forall>lA[M]. is_list(M,A,lA) -->
             is_lambda(M, lA, \<lambda>env z. \<exists>hp[M]. \<exists>hq[M]. 
		 (\<exists>rp[M]. is_depth_apply(M,h,p,rp) & fun_apply(M,rp,env,hp)) & 
		 (\<exists>rq[M]. is_depth_apply(M,h,q,rq) & fun_apply(M,rq,env,hq)) & 
                 (\<exists>pq[M]. is_and(M,hp,hq,pq) & is_not(M,pq,z)),
                zz)"

  satisfies_d :: "[i,i,i]=>i"
   "satisfies_d(A) 
    == \<lambda>p rp. \<lambda>env \<in> list(A). bool_of_o (\<forall>x\<in>A. rp ` (Cons(x,env)) = 1)"

  satisfies_is_d :: "[i=>o,i,i,i,i]=>o"
   "satisfies_is_d(M,A,h) == 
    \<lambda>p zz. \<forall>lA[M]. is_list(M,A,lA) -->
             is_lambda(M, lA, 
                \<lambda>env z. \<exists>rp[M]. is_depth_apply(M,h,p,rp) & 
                    is_bool_of_o(M, 
                           \<forall>x[M]. \<forall>xenv[M]. \<forall>hp[M]. 
                              x\<in>A --> is_Cons(M,x,env,xenv) --> 
                              fun_apply(M,rp,xenv,hp) --> number1(M,hp),
                  z),
               zz)"

  satisfies_MH :: "[i=>o,i,i,i,i]=>o"
    --{*The variable @{term u} is unused, but gives @{term satisfies_MH} 
        the correct arity.*}
   "satisfies_MH == 
    \<lambda>M A u f z. 
         \<forall>fml[M]. is_formula(M,fml) -->
             is_lambda (M, fml, 
               is_formula_case (M, satisfies_is_a(M,A), 
                                satisfies_is_b(M,A), 
                                satisfies_is_c(M,A,f), satisfies_is_d(M,A,f)),
               z)"

  is_satisfies :: "[i=>o,i,i,i]=>o"
   "is_satisfies(M,A) == is_formula_rec (M, satisfies_MH(M,A))"


text{*This lemma relates the fragments defined above to the original primitive
      recursion in @{term satisfies}.
      Induction is not required: the definitions are directly equal!*}
lemma satisfies_eq:
  "satisfies(A,p) = 
   formula_rec (satisfies_a(A), satisfies_b(A), 
                satisfies_c(A), satisfies_d(A), p)"
by (simp add: satisfies_formula_def satisfies_a_def satisfies_b_def 
              satisfies_c_def satisfies_d_def) 

text{*Further constraints on the class @{term M} in order to prove
      absoluteness for the constants defined above.  The ultimate goal
      is the absoluteness of the function @{term satisfies}. *}
locale M_satisfies = M_eclose +
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
 and
  formula_rec_lambda_replacement:  
      --{*For the @{text "\<lambda>-abstraction"} in the @{term transrec} body*}
   "[|M(g); M(A)|] ==>
    strong_replacement (M, 
       \<lambda>x y. mem_formula(M,x) &
             (\<exists>c[M]. is_formula_case(M, satisfies_is_a(M,A),
                                  satisfies_is_b(M,A),
                                  satisfies_is_c(M,A,g),
                                  satisfies_is_d(M,A,g), x, c) &
             pair(M, x, c, y)))"


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

lemma (in M_satisfies) formula_case_satisfies_closed:
 "[|M(g); M(A); x \<in> formula|] ==>
  M(formula_case (satisfies_a(A), satisfies_b(A),
       \<lambda>u v. satisfies_c(A, u, v, 
                         g ` succ(depth(u)) ` u, g ` succ(depth(v)) ` v),
       \<lambda>u. satisfies_d (A, u, g ` succ(depth(u)) ` u),
       x))"
by (blast intro: formula_case_closed a_closed b_closed c_closed d_closed) 

lemma (in M_satisfies) fr_lam_replace:
   "[|M(g); M(A)|] ==>
    strong_replacement (M, \<lambda>x y. x \<in> formula &
            y = \<langle>x, 
                 formula_rec_case(satisfies_a(A),
                                  satisfies_b(A),
                                  satisfies_c(A),
                                  satisfies_d(A), g, x)\<rangle>)"
apply (insert formula_rec_lambda_replacement) 
apply (simp add: formula_rec_case_def formula_case_satisfies_closed
                 formula_case_abs [OF a_rel b_rel c_rel d_rel]) 
done



text{*Instantiate locale @{text Formula_Rec} for the 
      Function @{term satisfies}*}

lemma (in M_satisfies) Formula_Rec_axioms_M:
   "M(A) ==>
    Formula_Rec_axioms(M, satisfies_a(A), satisfies_is_a(M,A), 
			  satisfies_b(A), satisfies_is_b(M,A), 
			  satisfies_c(A), satisfies_is_c(M,A), 
			  satisfies_d(A), satisfies_is_d(M,A))"
apply (rule Formula_Rec_axioms.intro)
apply (assumption | 
       rule a_closed a_rel b_closed b_rel c_closed c_rel d_closed d_rel
       fr_replace [unfolded satisfies_MH_def]
       fr_lam_replace) +
done


theorem (in M_satisfies) Formula_Rec_M: 
    "M(A) ==>
     PROP Formula_Rec(M, satisfies_a(A), satisfies_is_a(M,A), 
			 satisfies_b(A), satisfies_is_b(M,A), 
			 satisfies_c(A), satisfies_is_c(M,A), 
			 satisfies_d(A), satisfies_is_d(M,A))"
apply (rule Formula_Rec.intro, assumption+)
apply (erule Formula_Rec_axioms_M) 
done

lemmas (in M_satisfies) 
    satisfies_closed = Formula_Rec.formula_rec_closed [OF Formula_Rec_M]
and satisfies_abs    = Formula_Rec.formula_rec_abs [OF Formula_Rec_M]


lemma (in M_satisfies) satisfies_closed:
  "[|M(A); p \<in> formula|] ==> M(satisfies(A,p))"
by (simp add: Formula_Rec.formula_rec_closed [OF Formula_Rec_M]  
              satisfies_eq) 

lemma (in M_satisfies) satisfies_abs:
  "[|M(A); M(z); p \<in> formula|] 
   ==> is_satisfies(M,A,p,z) <-> z = satisfies(A,p)"
by (simp only: Formula_Rec.formula_rec_abs [OF Formula_Rec_M]  
               satisfies_eq is_satisfies_def satisfies_MH_def)


subsection{*Internalizations Needed to Instantiate @{text "M_satisfies"}*}

subsubsection{*The Operator @{term is_depth_apply}, Internalized*}

(* is_depth_apply(M,h,p,z) ==
    \<exists>dp[M]. \<exists>sdp[M]. \<exists>hsdp[M]. 
      2        1         0
	finite_ordinal(M,dp) & is_depth(M,p,dp) & successor(M,dp,sdp) &
	fun_apply(M,h,sdp,hsdp) & fun_apply(M,hsdp,p,z) *)
constdefs depth_apply_fm :: "[i,i,i]=>i"
    "depth_apply_fm(h,p,z) ==
       Exists(Exists(Exists(
        And(finite_ordinal_fm(2),
         And(depth_fm(p#+3,2),
          And(succ_fm(2,1),
           And(fun_apply_fm(h#+3,1,0), fun_apply_fm(0,p#+3,z#+3))))))))"

lemma depth_apply_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> depth_apply_fm(x,y,z) \<in> formula"
by (simp add: depth_apply_fm_def)

lemma sats_depth_apply_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, depth_apply_fm(x,y,z), env) <->
        is_depth_apply(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: depth_apply_fm_def is_depth_apply_def)

lemma depth_apply_iff_sats:
    "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
        i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
     ==> is_depth_apply(**A, x, y, z) <-> sats(A, depth_apply_fm(i,j,k), env)"
by simp

lemma depth_apply_reflection:
     "REFLECTS[\<lambda>x. is_depth_apply(L,f(x),g(x),h(x)),
               \<lambda>i x. is_depth_apply(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_depth_apply_def setclass_simps)
apply (intro FOL_reflections function_reflections depth_reflection 
             finite_ordinal_reflection)
done


subsubsection{*The Operator @{term satisfies_is_a}, Internalized*}

(* satisfies_is_a(M,A) == 
    \<lambda>x y zz. \<forall>lA[M]. is_list(M,A,lA) -->
             is_lambda(M, lA, 
		\<lambda>env z. is_bool_of_o(M, 
                      \<exists>nx[M]. \<exists>ny[M]. 
 		       is_nth(M,x,env,nx) & is_nth(M,y,env,ny) & nx \<in> ny, z),
                zz)  *)

constdefs satisfies_is_a_fm :: "[i,i,i,i]=>i"
 "satisfies_is_a_fm(A,x,y,z) ==
   Forall(
     Implies(is_list_fm(succ(A),0),
       lambda_fm(
         bool_of_o_fm(Exists(
                       Exists(And(nth_fm(x#+6,3,1), 
                               And(nth_fm(y#+6,3,0), 
                                   Member(1,0))))), 0), 
         0, succ(z))))"

lemma satisfies_is_a_type [TC]:
     "[| A \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> satisfies_is_a_fm(A,x,y,z) \<in> formula"
by (simp add: satisfies_is_a_fm_def)

lemma sats_satisfies_is_a_fm [simp]:
   "[| u \<in> nat; x < length(env); y < length(env); z \<in> nat; env \<in> list(A)|]
    ==> sats(A, satisfies_is_a_fm(u,x,y,z), env) <->
        satisfies_is_a(**A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=x in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: satisfies_is_a_fm_def satisfies_is_a_def sats_lambda_fm 
                 sats_bool_of_o_fm)
done

lemma satisfies_is_a_iff_sats:
  "[| nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x < length(env); y < length(env); z \<in> nat; env \<in> list(A)|]
   ==> satisfies_is_a(**A,nu,nx,ny,nz) <->
       sats(A, satisfies_is_a_fm(u,x,y,z), env)"
by simp

theorem satisfies_is_a_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_a(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_a(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold satisfies_is_a_def) 
apply (intro FOL_reflections is_lambda_reflection bool_of_o_reflection 
             nth_reflection is_list_reflection)
done


subsubsection{*The Operator @{term satisfies_is_b}, Internalized*}

(* satisfies_is_b(M,A) == 
    \<lambda>x y zz. \<forall>lA[M]. is_list(M,A,lA) -->
             is_lambda(M, lA, 
                \<lambda>env z. is_bool_of_o(M, 
                      \<exists>nx[M]. is_nth(M,x,env,nx) & is_nth(M,y,env,nx), z),
                zz) *)

constdefs satisfies_is_b_fm :: "[i,i,i,i]=>i"
 "satisfies_is_b_fm(A,x,y,z) ==
   Forall(
     Implies(is_list_fm(succ(A),0),
       lambda_fm(
         bool_of_o_fm(Exists(And(nth_fm(x#+5,2,0), nth_fm(y#+5,2,0))), 0), 
         0, succ(z))))"

lemma satisfies_is_b_type [TC]:
     "[| A \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> satisfies_is_b_fm(A,x,y,z) \<in> formula"
by (simp add: satisfies_is_b_fm_def)

lemma sats_satisfies_is_b_fm [simp]:
   "[| u \<in> nat; x < length(env); y < length(env); z \<in> nat; env \<in> list(A)|]
    ==> sats(A, satisfies_is_b_fm(u,x,y,z), env) <->
        satisfies_is_b(**A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=x in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: satisfies_is_b_fm_def satisfies_is_b_def sats_lambda_fm 
                 sats_bool_of_o_fm)
done

lemma satisfies_is_b_iff_sats:
  "[| nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x < length(env); y < length(env); z \<in> nat; env \<in> list(A)|]
   ==> satisfies_is_b(**A,nu,nx,ny,nz) <->
       sats(A, satisfies_is_b_fm(u,x,y,z), env)"
by simp

theorem satisfies_is_b_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_b(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_b(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold satisfies_is_b_def) 
apply (intro FOL_reflections is_lambda_reflection bool_of_o_reflection 
             nth_reflection is_list_reflection)
done


subsubsection{*The Operator @{term satisfies_is_c}, Internalized*}

(* satisfies_is_c(M,A,h) == 
    \<lambda>p q zz. \<forall>lA[M]. is_list(M,A,lA) -->
             is_lambda(M, lA, \<lambda>env z. \<exists>hp[M]. \<exists>hq[M]. 
		 (\<exists>rp[M]. is_depth_apply(M,h,p,rp) & fun_apply(M,rp,env,hp)) & 
		 (\<exists>rq[M]. is_depth_apply(M,h,q,rq) & fun_apply(M,rq,env,hq)) & 
                 (\<exists>pq[M]. is_and(M,hp,hq,pq) & is_not(M,pq,z)),
                zz) *)

constdefs satisfies_is_c_fm :: "[i,i,i,i,i]=>i"
 "satisfies_is_c_fm(A,h,p,q,zz) ==
   Forall(
     Implies(is_list_fm(succ(A),0),
       lambda_fm(
         Exists(Exists(
          And(Exists(And(depth_apply_fm(h#+7,p#+7,0), fun_apply_fm(0,4,2))),
          And(Exists(And(depth_apply_fm(h#+7,q#+7,0), fun_apply_fm(0,4,1))),
              Exists(And(and_fm(2,1,0), not_fm(0,3))))))),
         0, succ(zz))))"

lemma satisfies_is_c_type [TC]:
     "[| A \<in> nat; h \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> satisfies_is_c_fm(A,h,x,y,z) \<in> formula"
by (simp add: satisfies_is_c_fm_def)

lemma sats_satisfies_is_c_fm [simp]:
   "[| u \<in> nat; v \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, satisfies_is_c_fm(u,v,x,y,z), env) <->
        satisfies_is_c(**A, nth(u,env), nth(v,env), nth(x,env), 
                            nth(y,env), nth(z,env))"  
by (simp add: satisfies_is_c_fm_def satisfies_is_c_def sats_lambda_fm)

lemma satisfies_is_c_iff_sats:
  "[| nth(u,env) = nu; nth(v,env) = nv; nth(x,env) = nx; nth(y,env) = ny; 
      nth(z,env) = nz;
      u \<in> nat; v \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
   ==> satisfies_is_c(**A,nu,nv,nx,ny,nz) <->
       sats(A, satisfies_is_c_fm(u,v,x,y,z), env)"
by simp

theorem satisfies_is_c_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_c(L,f(x),g(x),h(x),g'(x),h'(x)),
               \<lambda>i x. satisfies_is_c(**Lset(i),f(x),g(x),h(x),g'(x),h'(x))]"
apply (unfold satisfies_is_c_def) 
apply (intro FOL_reflections function_reflections is_lambda_reflection
             extra_reflections nth_reflection depth_apply_reflection 
             is_list_reflection)
done

subsubsection{*The Operator @{term satisfies_is_d}, Internalized*}

(* satisfies_is_d(M,A,h) == 
    \<lambda>p zz. \<forall>lA[M]. is_list(M,A,lA) -->
             is_lambda(M, lA, 
                \<lambda>env z. \<exists>rp[M]. is_depth_apply(M,h,p,rp) & 
                    is_bool_of_o(M, 
                           \<forall>x[M]. \<forall>xenv[M]. \<forall>hp[M]. 
                              x\<in>A --> is_Cons(M,x,env,xenv) --> 
                              fun_apply(M,rp,xenv,hp) --> number1(M,hp),
                  z),
               zz) *)

constdefs satisfies_is_d_fm :: "[i,i,i,i]=>i"
 "satisfies_is_d_fm(A,h,p,zz) ==
   Forall(
     Implies(is_list_fm(succ(A),0),
       lambda_fm(
         Exists(
           And(depth_apply_fm(h#+5,p#+5,0),
               bool_of_o_fm(
                Forall(Forall(Forall(
                 Implies(Member(2,A#+8),
                  Implies(Cons_fm(2,5,1),
                   Implies(fun_apply_fm(3,1,0), number1_fm(0))))))), 1))),
         0, succ(zz))))"

lemma satisfies_is_d_type [TC]:
     "[| A \<in> nat; h \<in> nat; x \<in> nat; z \<in> nat |]
      ==> satisfies_is_d_fm(A,h,x,z) \<in> formula"
by (simp add: satisfies_is_d_fm_def)

lemma sats_satisfies_is_d_fm [simp]:
   "[| u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, satisfies_is_d_fm(u,x,y,z), env) <->
        satisfies_is_d(**A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"  
by (simp add: satisfies_is_d_fm_def satisfies_is_d_def sats_lambda_fm
              sats_bool_of_o_fm)

lemma satisfies_is_d_iff_sats:
  "[| nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
   ==> satisfies_is_d(**A,nu,nx,ny,nz) <->
       sats(A, satisfies_is_d_fm(u,x,y,z), env)"
by simp

theorem satisfies_is_d_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_d(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_d(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold satisfies_is_d_def ) 
apply (intro FOL_reflections function_reflections is_lambda_reflection
             extra_reflections nth_reflection depth_apply_reflection 
             is_list_reflection)
done


subsubsection{*The Operator @{term satisfies_MH}, Internalized*}

(* satisfies_MH == 
    \<lambda>M A u f zz. 
         \<forall>fml[M]. is_formula(M,fml) -->
             is_lambda (M, fml, 
               is_formula_case (M, satisfies_is_a(M,A), 
                                satisfies_is_b(M,A), 
                                satisfies_is_c(M,A,f), satisfies_is_d(M,A,f)),
               zz) *)

constdefs satisfies_MH_fm :: "[i,i,i,i]=>i"
 "satisfies_MH_fm(A,u,f,zz) ==
   Forall(
     Implies(is_formula_fm(0),
       lambda_fm(
         formula_case_fm(satisfies_is_a_fm(A#+7,2,1,0), 
                         satisfies_is_b_fm(A#+7,2,1,0), 
                         satisfies_is_c_fm(A#+7,f#+7,2,1,0), 
                         satisfies_is_d_fm(A#+6,f#+6,1,0), 
                         1, 0),
         0, succ(zz))))"

lemma satisfies_MH_type [TC]:
     "[| A \<in> nat; u \<in> nat; x \<in> nat; z \<in> nat |]
      ==> satisfies_MH_fm(A,u,x,z) \<in> formula"
by (simp add: satisfies_MH_fm_def)

lemma sats_satisfies_MH_fm [simp]:
   "[| u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, satisfies_MH_fm(u,x,y,z), env) <->
        satisfies_MH(**A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"  
by (simp add: satisfies_MH_fm_def satisfies_MH_def sats_lambda_fm
              sats_formula_case_fm)

lemma satisfies_MH_iff_sats:
  "[| nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
   ==> satisfies_MH(**A,nu,nx,ny,nz) <->
       sats(A, satisfies_MH_fm(u,x,y,z), env)"
by simp 

lemmas satisfies_reflections =
       is_lambda_reflection is_formula_reflection 
       is_formula_case_reflection
       satisfies_is_a_reflection satisfies_is_b_reflection 
       satisfies_is_c_reflection satisfies_is_d_reflection

theorem satisfies_MH_reflection:
     "REFLECTS[\<lambda>x. satisfies_MH(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_MH(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold satisfies_MH_def) 
apply (intro FOL_reflections satisfies_reflections)
done


subsection{*Lemmas for Instantiating the Locale @{text "M_satisfies"}*}


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

lemma formula_rec_replacement_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L, u, y, x) \<and>
             is_wfrec (L, satisfies_MH(L,A), mesa, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
             is_wfrec (**Lset(i), satisfies_MH(**Lset(i),A), mesa, u, y))]"
by (intro FOL_reflections function_reflections satisfies_MH_reflection 
          is_wfrec_reflection) 

lemma formula_rec_replacement: 
      --{*For the @{term transrec}*}
   "[|n \<in> nat; L(A)|] ==> transrec_replacement(L, satisfies_MH(L,A), n)"
apply (subgoal_tac "L(Memrel(eclose({n})))")
 prefer 2 apply (simp add: nat_into_M) 
apply (rule transrec_replacementI) 
apply (simp add: nat_into_M) 
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (rule_tac A="{B,A,n,z,Memrel(eclose({n}))}" in subset_LsetE, blast )
apply (rule ReflectsE [OF formula_rec_replacement_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (elim conjE)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,n,B,Memrel(eclose({n}))]" in mem_iff_sats)
apply (rule sep_rules satisfies_MH_iff_sats is_wfrec_iff_sats | simp)+
done


subsubsection{*The Lambda Replacement Case*}

lemma formula_rec_lambda_replacement_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B &
     mem_formula(L,u) &
     (\<exists>c[L].
	 is_formula_case
	  (L, satisfies_is_a(L,A), satisfies_is_b(L,A),
	   satisfies_is_c(L,A,g), satisfies_is_d(L,A,g),
	   u, c) &
	 pair(L,u,c,x)),
  \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B & mem_formula(**Lset(i),u) &
     (\<exists>c \<in> Lset(i).
	 is_formula_case
	  (**Lset(i), satisfies_is_a(**Lset(i),A), satisfies_is_b(**Lset(i),A),
	   satisfies_is_c(**Lset(i),A,g), satisfies_is_d(**Lset(i),A,g),
	   u, c) &
	 pair(**Lset(i),u,c,x))]"
by (intro FOL_reflections function_reflections mem_formula_reflection
          is_formula_case_reflection satisfies_is_a_reflection
          satisfies_is_b_reflection satisfies_is_c_reflection
          satisfies_is_d_reflection)  

lemma formula_rec_lambda_replacement: 
      --{*For the @{term transrec}*}
   "[|L(g); L(A)|] ==>
    strong_replacement (L, 
       \<lambda>x y. mem_formula(L,x) &
             (\<exists>c[L]. is_formula_case(L, satisfies_is_a(L,A),
                                  satisfies_is_b(L,A),
                                  satisfies_is_c(L,A,g),
                                  satisfies_is_d(L,A,g), x, c) &
             pair(L, x, c, y)))" 
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (rule_tac A="{B,A,g,z}" in subset_LsetE, blast)
apply (rule ReflectsE [OF formula_rec_lambda_replacement_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (elim conjE)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,g,B]" in mem_iff_sats)
apply (rule sep_rules mem_formula_iff_sats
          formula_case_iff_sats satisfies_is_a_iff_sats
          satisfies_is_b_iff_sats satisfies_is_c_iff_sats
          satisfies_is_d_iff_sats | simp)+
done


subsection{*Instantiating @{text M_satisfies}*}

lemma M_satisfies_axioms_L: "M_satisfies_axioms(L)"
  apply (rule M_satisfies_axioms.intro)
       apply (assumption | rule
	 Member_replacement Equal_replacement 
         Nand_replacement Forall_replacement
         formula_rec_replacement formula_rec_lambda_replacement)+
  done

theorem M_satisfies_L: "PROP M_satisfies(L)"
apply (rule M_satisfies.intro) 
     apply (rule M_eclose.axioms [OF M_eclose_L])+
apply (rule M_satisfies_axioms_L) 
done

text{*Finally: the point of the whole theory!*}
lemmas satisfies_closed = M_satisfies.satisfies_closed [OF M_satisfies_L]
   and satisfies_abs = M_satisfies.satisfies_abs [OF M_satisfies_L]

end
