(*  Title:      ZF/Constructible/DPow_absolute.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header {*Absoluteness for the Definable Powerset Function*}


theory DPow_absolute = Satisfies_absolute:


subsection{*Preliminary Internalizations*}

subsubsection{*The Operator @{term is_formula_rec}*}

text{*The three arguments of @{term p} are always 2, 1, 0.  It is buried
   within 11 quantifiers!!*}

(* is_formula_rec :: "[i=>o, [i,i,i]=>o, i, i] => o"
   "is_formula_rec(M,MH,p,z)  ==
      \<exists>dp[M]. \<exists>i[M]. \<exists>f[M]. finite_ordinal(M,dp) & is_depth(M,p,dp) & 
       2       1      0
             successor(M,dp,i) & fun_apply(M,f,p,z) & is_transrec(M,MH,i,f)"
*)

constdefs formula_rec_fm :: "[i, i, i]=>i"
 "formula_rec_fm(mh,p,z) == 
    Exists(Exists(Exists(
      And(finite_ordinal_fm(2),
       And(depth_fm(p#+3,2),
        And(succ_fm(2,1), 
          And(fun_apply_fm(0,p#+3,z#+3), is_transrec_fm(mh,1,0))))))))"

lemma is_formula_rec_type [TC]:
     "[| p \<in> formula; x \<in> nat; z \<in> nat |] 
      ==> formula_rec_fm(p,x,z) \<in> formula"
by (simp add: formula_rec_fm_def) 

lemma sats_formula_rec_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A; a5\<in>A; a6\<in>A; a7\<in>A; a8\<in>A; a9\<in>A; a10\<in>A|]
        ==> MH(a2, a1, a0) <-> 
            sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,
                          Cons(a4,Cons(a5,Cons(a6,Cons(a7,
                                  Cons(a8,Cons(a9,Cons(a10,env))))))))))))"
  shows 
      "[|x \<in> nat; z \<in> nat; env \<in> list(A)|]
       ==> sats(A, formula_rec_fm(p,x,z), env) <-> 
           is_formula_rec(**A, MH, nth(x,env), nth(z,env))"
by (simp add: formula_rec_fm_def sats_is_transrec_fm is_formula_rec_def 
              MH_iff_sats [THEN iff_sym])

lemma formula_rec_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A; a5\<in>A; a6\<in>A; a7\<in>A; a8\<in>A; a9\<in>A; a10\<in>A|]
        ==> MH(a2, a1, a0) <-> 
            sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,
                          Cons(a4,Cons(a5,Cons(a6,Cons(a7,
                                  Cons(a8,Cons(a9,Cons(a10,env))))))))))))"
  shows
  "[|nth(i,env) = x; nth(k,env) = z; 
      i \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> is_formula_rec(**A, MH, x, z) <-> sats(A, formula_rec_fm(p,i,k), env)" 
by (simp add: sats_formula_rec_fm [OF MH_iff_sats])

theorem formula_rec_reflection:
  assumes MH_reflection:
    "!!f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(**Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_formula_rec(L, MH(L,x), f(x), h(x)), 
               \<lambda>i x. is_formula_rec(**Lset(i), MH(**Lset(i),x), f(x), h(x))]"
apply (simp (no_asm_use) only: is_formula_rec_def)
apply (intro FOL_reflections function_reflections fun_plus_reflections
             depth_reflection is_transrec_reflection MH_reflection)
done


subsubsection{*The Operator @{term is_satisfies}*}

(* is_satisfies(M,A,p,z) == is_formula_rec (M, satisfies_MH(M,A), p, z) *)
constdefs satisfies_fm :: "[i,i,i]=>i"
    "satisfies_fm(x) == formula_rec_fm (satisfies_MH_fm(x#+5#+6, 2, 1, 0))"

lemma is_satisfies_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> satisfies_fm(x,y,z) \<in> formula"
by (simp add: satisfies_fm_def)

lemma sats_satisfies_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, satisfies_fm(x,y,z), env) <->
        is_satisfies(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: satisfies_fm_def is_satisfies_def sats_satisfies_MH_fm
              sats_formula_rec_fm)

lemma satisfies_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_satisfies(**A, x, y, z) <-> sats(A, satisfies_fm(i,j,k), env)"
by (simp add: sats_satisfies_fm)

theorem satisfies_reflection:
     "REFLECTS[\<lambda>x. is_satisfies(L,f(x),g(x),h(x)),
               \<lambda>i x. is_satisfies(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_satisfies_def)
apply (intro formula_rec_reflection satisfies_MH_reflection)
done


subsection {*Relativization of the Operator @{term DPow'}*}

lemma DPow'_eq: 
  "DPow'(A) = {z . ep \<in> list(A) * formula, 
                    \<exists>env \<in> list(A). \<exists>p \<in> formula. 
                       ep = <env,p> & z = {x\<in>A. sats(A, p, Cons(x,env))}}"
by (simp add: DPow'_def, blast) 


text{*Relativize the use of @{term sats} within @{term DPow'}
(the comprehension).*}
constdefs
  is_DPow_sats :: "[i=>o,i,i,i,i] => o"
   "is_DPow_sats(M,A,env,p,x) ==
      \<forall>n1[M]. \<forall>e[M]. \<forall>sp[M]. 
             is_satisfies(M,A,p,sp) --> is_Cons(M,x,env,e) --> 
             fun_apply(M, sp, e, n1) --> number1(M, n1)"

lemma (in M_satisfies) DPow_sats_abs:
    "[| M(A); env \<in> list(A); p \<in> formula; M(x) |]
    ==> is_DPow_sats(M,A,env,p,x) <-> sats(A, p, Cons(x,env))"
apply (subgoal_tac "M(env)") 
 apply (simp add: is_DPow_sats_def satisfies_closed satisfies_abs) 
apply (blast dest: transM) 
done

lemma (in M_satisfies) Collect_DPow_sats_abs:
    "[| M(A); env \<in> list(A); p \<in> formula |]
    ==> Collect(A, is_DPow_sats(M,A,env,p)) = 
        {x \<in> A. sats(A, p, Cons(x,env))}"
by (simp add: DPow_sats_abs transM [of _ A])


subsubsection{*The Operator @{term is_DPow_sats}, Internalized*}

(* is_DPow_sats(M,A,env,p,x) ==
      \<forall>n1[M]. \<forall>e[M]. \<forall>sp[M]. 
             is_satisfies(M,A,p,sp) --> is_Cons(M,x,env,e) --> 
             fun_apply(M, sp, e, n1) --> number1(M, n1) *)

constdefs DPow_sats_fm :: "[i,i,i,i]=>i"
 "DPow_sats_fm(A,env,p,x) ==
   Forall(Forall(Forall(
     Implies(satisfies_fm(A#+3,p#+3,0), 
       Implies(Cons_fm(x#+3,env#+3,1), 
         Implies(fun_apply_fm(0,1,2), number1_fm(2)))))))"

lemma is_DPow_sats_type [TC]:
     "[| A \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> DPow_sats_fm(A,x,y,z) \<in> formula"
by (simp add: DPow_sats_fm_def)

lemma sats_DPow_sats_fm [simp]:
   "[| u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, DPow_sats_fm(u,x,y,z), env) <->
        is_DPow_sats(**A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"
by (simp add: DPow_sats_fm_def is_DPow_sats_def)

lemma DPow_sats_iff_sats:
  "[| nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
   ==> is_DPow_sats(**A,nu,nx,ny,nz) <->
       sats(A, DPow_sats_fm(u,x,y,z), env)"
by simp

theorem DPow_sats_reflection:
     "REFLECTS[\<lambda>x. is_DPow_sats(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. is_DPow_sats(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold is_DPow_sats_def) 
apply (intro FOL_reflections function_reflections extra_reflections
             satisfies_reflection)
done


subsection{*A Locale for Relativizing the Operator @{term DPow'}*}

locale M_DPow = M_satisfies +
 assumes sep:
   "[| M(A); env \<in> list(A); p \<in> formula |]
    ==> separation(M, \<lambda>x. is_DPow_sats(M,A,env,p,x))"
 and rep: 
    "M(A)
    ==> strong_replacement (M, 
         \<lambda>ep z. \<exists>env[M]. \<exists>p[M]. mem_formula(M,p) & mem_list(M,A,env) &
                  pair(M,env,p,ep) & 
                  is_Collect(M, A, \<lambda>x. is_DPow_sats(M,A,env,p,x), z))"

lemma (in M_DPow) sep':
   "[| M(A); env \<in> list(A); p \<in> formula |]
    ==> separation(M, \<lambda>x. sats(A, p, Cons(x,env)))"
by (insert sep [of A env p], simp add: DPow_sats_abs)

lemma (in M_DPow) rep':
   "M(A)
    ==> strong_replacement (M, 
         \<lambda>ep z. \<exists>env\<in>list(A). \<exists>p\<in>formula.
                  ep = <env,p> & z = {x \<in> A . sats(A, p, Cons(x, env))})" 
by (insert rep [of A], simp add: Collect_DPow_sats_abs) 


lemma univalent_pair_eq:
     "univalent (M, A, \<lambda>xy z. \<exists>x\<in>B. \<exists>y\<in>C. xy = \<langle>x,y\<rangle> \<and> z = f(x,y))"
by (simp add: univalent_def, blast) 

lemma (in M_DPow) DPow'_closed: "M(A) ==> M(DPow'(A))"
apply (simp add: DPow'_eq)
apply (fast intro: rep' sep' univalent_pair_eq)  
done

text{*Relativization of the Operator @{term DPow'}*}
constdefs 
  is_DPow' :: "[i=>o,i,i] => o"
    "is_DPow'(M,A,Z) == 
       \<forall>X[M]. X \<in> Z <-> 
         subset(M,X,A) & 
           (\<exists>env[M]. \<exists>p[M]. mem_formula(M,p) & mem_list(M,A,env) &
                    is_Collect(M, A, is_DPow_sats(M,A,env,p), X))"

lemma (in M_DPow) DPow'_abs:
    "[|M(A); M(Z)|] ==> is_DPow'(M,A,Z) <-> Z = DPow'(A)"
apply (rule iffI)
 prefer 2 apply (simp add: is_DPow'_def DPow'_def Collect_DPow_sats_abs) 
apply (rule M_equalityI) 
apply (simp add: is_DPow'_def DPow'_def Collect_DPow_sats_abs, assumption)
apply (erule DPow'_closed)
done


subsection{*Instantiating the Locale @{text M_DPow}*}

subsubsection{*The Instance of Separation*}

lemma DPow_separation:
    "[| L(A); env \<in> list(A); p \<in> formula |]
     ==> separation(L, \<lambda>x. is_DPow_sats(L,A,env,p,x))"
apply (rule gen_separation_multi [OF DPow_sats_reflection, of "{A,env,p}"], 
       auto intro: transL)
apply (rule_tac env="[A,env,p]" in DPow_LsetI)
apply (rule DPow_sats_iff_sats sep_rules | simp)+
done



subsubsection{*The Instance of Replacement*}

lemma DPow_replacement_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B &
             (\<exists>env[L]. \<exists>p[L].
               mem_formula(L,p) & mem_list(L,A,env) & pair(L,env,p,u) &
               is_Collect (L, A, is_DPow_sats(L,A,env,p), x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B &
             (\<exists>env \<in> Lset(i). \<exists>p \<in> Lset(i).
               mem_formula(**Lset(i),p) & mem_list(**Lset(i),A,env) & 
               pair(**Lset(i),env,p,u) &
               is_Collect (**Lset(i), A, is_DPow_sats(**Lset(i),A,env,p), x))]"
apply (unfold is_Collect_def) 
apply (intro FOL_reflections function_reflections mem_formula_reflection
          mem_list_reflection DPow_sats_reflection)
done

lemma DPow_replacement:
    "L(A)
    ==> strong_replacement (L, 
         \<lambda>ep z. \<exists>env[L]. \<exists>p[L]. mem_formula(L,p) & mem_list(L,A,env) &
                  pair(L,env,p,ep) & 
                  is_Collect(L, A, \<lambda>x. is_DPow_sats(L,A,env,p,x), z))"
apply (rule strong_replacementI)
apply (rule_tac u="{A,B}" 
         in gen_separation_multi [OF DPow_replacement_Reflects], 
       auto)
apply (unfold is_Collect_def) 
apply (rule_tac env="[A,B]" in DPow_LsetI)
apply (rule sep_rules mem_formula_iff_sats mem_list_iff_sats 
            DPow_sats_iff_sats | simp)+
done


subsubsection{*Actually Instantiating the Locale*}

lemma M_DPow_axioms_L: "M_DPow_axioms(L)"
  apply (rule M_DPow_axioms.intro)
   apply (assumption | rule DPow_separation DPow_replacement)+
  done

theorem M_DPow_L: "PROP M_DPow(L)"
  apply (rule M_DPow.intro)
       apply (rule M_satisfies.axioms [OF M_satisfies_L])+
  apply (rule M_DPow_axioms_L)
  done

lemmas DPow'_closed [intro, simp] = M_DPow.DPow'_closed [OF M_DPow_L]
  and DPow'_abs [intro, simp] = M_DPow.DPow'_abs [OF M_DPow_L]


subsubsection{*The Operator @{term is_Collect}*}

text{*The formula @{term is_P} has one free variable, 0, and it is
enclosed within a single quantifier.*}

(* is_Collect :: "[i=>o,i,i=>o,i] => o"
    "is_Collect(M,A,P,z) == \<forall>x[M]. x \<in> z <-> x \<in> A & P(x)" *)

constdefs Collect_fm :: "[i, i, i]=>i"
 "Collect_fm(A,is_P,z) == 
        Forall(Iff(Member(0,succ(z)),
                   And(Member(0,succ(A)), is_P)))"

lemma is_Collect_type [TC]:
     "[| is_P \<in> formula; x \<in> nat; y \<in> nat |] 
      ==> Collect_fm(x,is_P,y) \<in> formula"
by (simp add: Collect_fm_def)

lemma sats_Collect_fm:
  assumes is_P_iff_sats: 
      "!!a. a \<in> A ==> is_P(a) <-> sats(A, p, Cons(a, env))"
  shows 
      "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
       ==> sats(A, Collect_fm(x,p,y), env) <->
           is_Collect(**A, nth(x,env), is_P, nth(y,env))"
by (simp add: Collect_fm_def is_Collect_def is_P_iff_sats [THEN iff_sym])

lemma Collect_iff_sats:
  assumes is_P_iff_sats: 
      "!!a. a \<in> A ==> is_P(a) <-> sats(A, p, Cons(a, env))"
  shows 
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_Collect(**A, x, is_P, y) <-> sats(A, Collect_fm(i,p,j), env)"
by (simp add: sats_Collect_fm [OF is_P_iff_sats])


text{*The second argument of @{term is_P} gives it direct access to @{term x},
  which is essential for handling free variable references.*}
theorem Collect_reflection:
  assumes is_P_reflection:
    "!!h f g. REFLECTS[\<lambda>x. is_P(L, f(x), g(x)),
                     \<lambda>i x. is_P(**Lset(i), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_Collect(L, f(x), is_P(L,x), g(x)),
               \<lambda>i x. is_Collect(**Lset(i), f(x), is_P(**Lset(i), x), g(x))]"
apply (simp (no_asm_use) only: is_Collect_def)
apply (intro FOL_reflections is_P_reflection)
done


subsubsection{*The Operator @{term is_Replace}*}

text{*BEWARE!  The formula @{term is_P} has free variables 0, 1
 and not the usual 1, 0!  It is enclosed within two quantifiers.*}

(*  is_Replace :: "[i=>o,i,[i,i]=>o,i] => o"
    "is_Replace(M,A,P,z) == \<forall>u[M]. u \<in> z <-> (\<exists>x[M]. x\<in>A & P(x,u))" *)

constdefs Replace_fm :: "[i, i, i]=>i"
 "Replace_fm(A,is_P,z) == 
        Forall(Iff(Member(0,succ(z)),
                   Exists(And(Member(0,A#+2), is_P))))"

lemma is_Replace_type [TC]:
     "[| is_P \<in> formula; x \<in> nat; y \<in> nat |] 
      ==> Replace_fm(x,is_P,y) \<in> formula"
by (simp add: Replace_fm_def)

lemma sats_Replace_fm:
  assumes is_P_iff_sats: 
      "!!a b. [|a \<in> A; b \<in> A|] 
              ==> is_P(a,b) <-> sats(A, p, Cons(a,Cons(b,env)))"
  shows 
      "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
       ==> sats(A, Replace_fm(x,p,y), env) <->
           is_Replace(**A, nth(x,env), is_P, nth(y,env))"
by (simp add: Replace_fm_def is_Replace_def is_P_iff_sats [THEN iff_sym])

lemma Replace_iff_sats:
  assumes is_P_iff_sats: 
      "!!a b. [|a \<in> A; b \<in> A|] 
              ==> is_P(a,b) <-> sats(A, p, Cons(a,Cons(b,env)))"
  shows 
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_Replace(**A, x, is_P, y) <-> sats(A, Replace_fm(i,p,j), env)"
by (simp add: sats_Replace_fm [OF is_P_iff_sats])


text{*The second argument of @{term is_P} gives it direct access to @{term x},
  which is essential for handling free variable references.*}
theorem Replace_reflection:
  assumes is_P_reflection:
    "!!h f g. REFLECTS[\<lambda>x. is_P(L, f(x), g(x), h(x)),
                     \<lambda>i x. is_P(**Lset(i), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_Replace(L, f(x), is_P(L,x), g(x)),
               \<lambda>i x. is_Replace(**Lset(i), f(x), is_P(**Lset(i), x), g(x))]"
apply (simp (no_asm_use) only: is_Replace_def)
apply (intro FOL_reflections is_P_reflection)
done



subsubsection{*The Operator @{term is_DPow'}, Internalized*}

(*  "is_DPow'(M,A,Z) == 
       \<forall>X[M]. X \<in> Z <-> 
         subset(M,X,A) & 
           (\<exists>env[M]. \<exists>p[M]. mem_formula(M,p) & mem_list(M,A,env) &
                    is_Collect(M, A, is_DPow_sats(M,A,env,p), X))" *)

constdefs DPow'_fm :: "[i,i]=>i"
    "DPow'_fm(A,Z) == 
      Forall(
       Iff(Member(0,succ(Z)),
        And(subset_fm(0,succ(A)),
         Exists(Exists(
          And(mem_formula_fm(0),
           And(mem_list_fm(A#+3,1),
            Collect_fm(A#+3, 
                       DPow_sats_fm(A#+4, 2, 1, 0), 2))))))))"

lemma is_DPow'_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> DPow'_fm(x,y) \<in> formula"
by (simp add: DPow'_fm_def)

lemma sats_DPow'_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, DPow'_fm(x,y), env) <->
        is_DPow'(**A, nth(x,env), nth(y,env))"
by (simp add: DPow'_fm_def is_DPow'_def sats_subset_fm' sats_Collect_fm)

lemma DPow'_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_DPow'(**A, x, y) <-> sats(A, DPow'_fm(i,j), env)"
by (simp add: sats_DPow'_fm)

theorem DPow'_reflection:
     "REFLECTS[\<lambda>x. is_DPow'(L,f(x),g(x)),
               \<lambda>i x. is_DPow'(**Lset(i),f(x),g(x))]"
apply (simp only: is_DPow'_def)
apply (intro FOL_reflections function_reflections mem_formula_reflection
             mem_list_reflection Collect_reflection DPow_sats_reflection)
done


subsection{*A Locale for Relativizing the Operator @{term Lset}*}

constdefs
  transrec_body :: "[i=>o,i,i,i,i] => o"
    "transrec_body(M,g,x) ==
      \<lambda>y z. \<exists>gy[M]. y \<in> x & fun_apply(M,g,y,gy) & is_DPow'(M,gy,z)"

lemma (in M_DPow) transrec_body_abs:
     "[|M(x); M(g); M(z)|]
    ==> transrec_body(M,g,x,y,z) <-> y \<in> x & z = DPow'(g`y)"
by (simp add: transrec_body_def DPow'_abs transM [of _ x])

locale M_Lset = M_DPow +
 assumes strong_rep:
   "[|M(x); M(g)|] ==> strong_replacement(M, \<lambda>y z. transrec_body(M,g,x,y,z))"
 and transrec_rep: 
    "M(i) ==> transrec_replacement(M, \<lambda>x f u. 
              \<exists>r[M]. is_Replace(M, x, transrec_body(M,f,x), r) & 
                     big_union(M, r, u), i)"


lemma (in M_Lset) strong_rep':
   "[|M(x); M(g)|]
    ==> strong_replacement(M, \<lambda>y z. y \<in> x & z = DPow'(g`y))"
by (insert strong_rep [of x g], simp add: transrec_body_abs)

lemma (in M_Lset) DPow_apply_closed:
   "[|M(f); M(x); y\<in>x|] ==> M(DPow'(f`y))"
by (blast intro: DPow'_closed dest: transM) 

lemma (in M_Lset) RepFun_DPow_apply_closed:
   "[|M(f); M(x)|] ==> M({DPow'(f`y). y\<in>x})"
by (blast intro: DPow_apply_closed RepFun_closed2 strong_rep') 

lemma (in M_Lset) RepFun_DPow_abs:
     "[|M(x); M(f); M(r) |]
      ==> is_Replace(M, x, \<lambda>y z. transrec_body(M,f,x,y,z), r) <->
          r =  {DPow'(f`y). y\<in>x}"
apply (simp add: transrec_body_abs RepFun_def) 
apply (rule iff_trans) 
apply (rule Replace_abs) 
apply (simp_all add: DPow_apply_closed strong_rep') 
done

lemma (in M_Lset) transrec_rep':
   "M(i) ==> transrec_replacement(M, \<lambda>x f u. u = (\<Union>y\<in>x. DPow'(f ` y)), i)"
apply (insert transrec_rep [of i]) 
apply (simp add: RepFun_DPow_apply_closed RepFun_DPow_abs 
       transrec_replacement_def) 
done


text{*Relativization of the Operator @{term Lset}*}

constdefs
  is_Lset :: "[i=>o, i, i] => o"
   --{*We can use the term language below because @{term is_Lset} will
       not have to be internalized: it isn't used in any instance of
       separation.*}
   "is_Lset(M,a,z) == is_transrec(M, %x f u. u = (\<Union>y\<in>x. DPow'(f`y)), a, z)"

lemma (in M_Lset) Lset_abs:
  "[|Ord(i);  M(i);  M(z)|] 
   ==> is_Lset(M,i,z) <-> z = Lset(i)"
apply (simp add: is_Lset_def Lset_eq_transrec_DPow') 
apply (rule transrec_abs)  
apply (simp_all add: transrec_rep' relation2_def RepFun_DPow_apply_closed)
done

lemma (in M_Lset) Lset_closed:
  "[|Ord(i);  M(i)|] ==> M(Lset(i))"
apply (simp add: Lset_eq_transrec_DPow') 
apply (rule transrec_closed [OF transrec_rep']) 
apply (simp_all add: relation2_def RepFun_DPow_apply_closed)
done


subsection{*Instantiating the Locale @{text M_Lset}*}

subsubsection{*The First Instance of Replacement*}

lemma strong_rep_Reflects:
 "REFLECTS [\<lambda>u. \<exists>v[L]. v \<in> B & (\<exists>gy[L].
                          v \<in> x & fun_apply(L,g,v,gy) & is_DPow'(L,gy,u)),
   \<lambda>i u. \<exists>v \<in> Lset(i). v \<in> B & (\<exists>gy \<in> Lset(i).
            v \<in> x & fun_apply(**Lset(i),g,v,gy) & is_DPow'(**Lset(i),gy,u))]"
by (intro FOL_reflections function_reflections DPow'_reflection)

lemma strong_rep:
   "[|L(x); L(g)|] ==> strong_replacement(L, \<lambda>y z. transrec_body(L,g,x,y,z))"
apply (unfold transrec_body_def)  
apply (rule strong_replacementI) 
apply (rule_tac u="{x,g,B}" 
         in gen_separation_multi [OF strong_rep_Reflects], auto)
apply (rule_tac env="[x,g,B]" in DPow_LsetI)
apply (rule sep_rules DPow'_iff_sats | simp)+
done


subsubsection{*The Second Instance of Replacement*}

lemma transrec_rep_Reflects:
 "REFLECTS [\<lambda>x. \<exists>v[L]. v \<in> B &
              (\<exists>y[L]. pair(L,v,y,x) &
             is_wfrec (L, \<lambda>x f u. \<exists>r[L].
                is_Replace (L, x, \<lambda>y z. 
                     \<exists>gy[L]. y \<in> x & fun_apply(L,f,y,gy) & 
                      is_DPow'(L,gy,z), r) & big_union(L,r,u), mr, v, y)),
    \<lambda>i x. \<exists>v \<in> Lset(i). v \<in> B &
              (\<exists>y \<in> Lset(i). pair(**Lset(i),v,y,x) &
             is_wfrec (**Lset(i), \<lambda>x f u. \<exists>r \<in> Lset(i).
                is_Replace (**Lset(i), x, \<lambda>y z. 
                     \<exists>gy \<in> Lset(i). y \<in> x & fun_apply(**Lset(i),f,y,gy) & 
                      is_DPow'(**Lset(i),gy,z), r) & 
                      big_union(**Lset(i),r,u), mr, v, y))]" 
apply (simp only: rex_setclass_is_bex [symmetric])
  --{*Convert @{text "\<exists>y\<in>Lset(i)"} to @{text "\<exists>y[**Lset(i)]"} within the body
       of the @{term is_wfrec} application. *}
apply (intro FOL_reflections function_reflections 
          is_wfrec_reflection Replace_reflection DPow'_reflection) 
done


lemma transrec_rep: 
    "[|L(j)|]
    ==> transrec_replacement(L, \<lambda>x f u. 
              \<exists>r[L]. is_Replace(L, x, transrec_body(L,f,x), r) & 
                     big_union(L, r, u), j)"
apply (rule transrec_replacementI, assumption)
apply (unfold transrec_body_def)  
apply (rule strong_replacementI)
apply (rule_tac u="{j,B,Memrel(eclose({j}))}" 
         in gen_separation_multi [OF transrec_rep_Reflects], auto)
apply (rule_tac env="[j,B,Memrel(eclose({j}))]" in DPow_LsetI)
apply (rule sep_rules is_wfrec_iff_sats Replace_iff_sats DPow'_iff_sats | 
       simp)+
done


subsubsection{*Actually Instantiating @{text M_Lset}*}

lemma M_Lset_axioms_L: "M_Lset_axioms(L)"
  apply (rule M_Lset_axioms.intro)
       apply (assumption | rule strong_rep transrec_rep)+
  done

theorem M_Lset_L: "PROP M_Lset(L)"
apply (rule M_Lset.intro) 
     apply (rule M_DPow.axioms [OF M_DPow_L])+
apply (rule M_Lset_axioms_L) 
done

text{*Finally: the point of the whole theory!*}
lemmas Lset_closed = M_Lset.Lset_closed [OF M_Lset_L]
   and Lset_abs = M_Lset.Lset_abs [OF M_Lset_L]


subsection{*The Notion of Constructible Set*}


constdefs
  constructible :: "[i=>o,i] => o"
    "constructible(M,x) ==
       \<exists>i[M]. \<exists>Li[M]. ordinal(M,i) & is_Lset(M,i,Li) & x \<in> Li"

theorem V_equals_L_in_L:
  "L(x) ==> constructible(L,x)"
apply (simp add: constructible_def Lset_abs Lset_closed) 
apply (simp add: L_def)
apply (blast intro: Ord_in_L) 
done

end
