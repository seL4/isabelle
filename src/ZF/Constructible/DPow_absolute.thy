(*  Title:      ZF/Constructible/DPow_absolute.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
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
apply (simp (no_asm_use) only: is_formula_rec_def setclass_simps)
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
apply (simp only: is_satisfies_def setclass_simps)
apply (intro formula_rec_reflection satisfies_MH_reflection)
done


subsection {*Relativization of the Operator @{term DPow'}*}

lemma DPow'_eq: 
  "DPow'(A) = Replace(list(A) * formula,
              %ep z. \<exists>env \<in> list(A). \<exists>p \<in> formula. 
                     ep = <env,p> & z = {x\<in>A. sats(A, p, Cons(x,env))})"
apply (simp add: DPow'_def, blast) 
done


constdefs
  is_DPow_body :: "[i=>o,i,i,i,i] => o"
   "is_DPow_body(M,A,env,p,x) ==
      \<forall>n1[M]. \<forall>e[M]. \<forall>sp[M]. 
             is_satisfies(M,A,p,sp) --> is_Cons(M,x,env,e) --> 
             fun_apply(M, sp, e, n1) --> number1(M, n1)"

lemma (in M_satisfies) DPow_body_abs:
    "[| M(A); env \<in> list(A); p \<in> formula; M(x) |]
    ==> is_DPow_body(M,A,env,p,x) <-> sats(A, p, Cons(x,env))"
apply (subgoal_tac "M(env)") 
 apply (simp add: is_DPow_body_def satisfies_closed satisfies_abs) 
apply (blast dest: transM) 
done

lemma (in M_satisfies) Collect_DPow_body_abs:
    "[| M(A); env \<in> list(A); p \<in> formula |]
    ==> Collect(A, is_DPow_body(M,A,env,p)) = 
        {x \<in> A. sats(A, p, Cons(x,env))}"
by (simp add: DPow_body_abs transM [of _ A])


subsubsection{*The Operator @{term is_DPow_body}, Internalized*}

(* is_DPow_body(M,A,env,p,x) ==
      \<forall>n1[M]. \<forall>e[M]. \<forall>sp[M]. 
             is_satisfies(M,A,p,sp) --> is_Cons(M,x,env,e) --> 
             fun_apply(M, sp, e, n1) --> number1(M, n1) *)

constdefs DPow_body_fm :: "[i,i,i,i]=>i"
 "DPow_body_fm(A,env,p,x) ==
   Forall(Forall(Forall(
     Implies(satisfies_fm(A#+3,p#+3,0), 
       Implies(Cons_fm(x#+3,env#+3,1), 
         Implies(fun_apply_fm(0,1,2), number1_fm(2)))))))"

lemma is_DPow_body_type [TC]:
     "[| A \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> DPow_body_fm(A,x,y,z) \<in> formula"
by (simp add: DPow_body_fm_def)

lemma sats_DPow_body_fm [simp]:
   "[| u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, DPow_body_fm(u,x,y,z), env) <->
        is_DPow_body(**A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"
by (simp add: DPow_body_fm_def is_DPow_body_def)

lemma DPow_body_iff_sats:
  "[| nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
   ==> is_DPow_body(**A,nu,nx,ny,nz) <->
       sats(A, DPow_body_fm(u,x,y,z), env)"
by simp

theorem DPow_body_reflection:
     "REFLECTS[\<lambda>x. is_DPow_body(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. is_DPow_body(**Lset(i),f(x),g(x),h(x),g'(x))]"
apply (unfold is_DPow_body_def) 
apply (intro FOL_reflections function_reflections extra_reflections
             satisfies_reflection)
done


subsection{*Additional Constraints on the Class Model @{term M}*}

locale M_DPow = M_satisfies +
 assumes sep:
   "[| M(A); env \<in> list(A); p \<in> formula |]
    ==> separation(M, \<lambda>x. is_DPow_body(M,A,env,p,x))"
 and rep: 
    "M(A)
    ==> strong_replacement (M, 
         \<lambda>ep z. \<exists>env[M]. \<exists>p[M]. mem_formula(M,p) & mem_list(M,A,env) &
                  pair(M,env,p,ep) & 
                  is_Collect(M, A, \<lambda>x. is_DPow_body(M,A,env,p,x), z))"

lemma (in M_DPow) sep':
   "[| M(A); env \<in> list(A); p \<in> formula |]
    ==> separation(M, \<lambda>x. sats(A, p, Cons(x,env)))"
by (insert sep [of A env p], simp add: DPow_body_abs)

lemma (in M_DPow) rep':
   "M(A)
    ==> strong_replacement (M, 
         \<lambda>ep z. \<exists>env\<in>list(A). \<exists>p\<in>formula.
                  ep = <env,p> & z = {x \<in> A . sats(A, p, Cons(x, env))})"
by (insert rep [of A], simp add: Collect_DPow_body_abs) 


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
                    is_Collect(M, A, is_DPow_body(M,A,env,p), X))"

lemma (in M_DPow) DPow'_abs:
    "[|M(A); M(Z)|] ==> is_DPow'(M,A,Z) <-> Z = DPow'(A)"
apply (rule iffI)
 prefer 2 apply (simp add: is_DPow'_def DPow'_def Collect_DPow_body_abs) 
apply (rule M_equalityI) 
apply (simp add: is_DPow'_def DPow'_def Collect_DPow_body_abs, assumption)
apply (erule DPow'_closed)
done


subsection{*Instantiating the Locale @{text M_DPow}*}

subsubsection{*The Instance of Separation*}

lemma DPow_separation:
    "[| L(A); env \<in> list(A); p \<in> formula |]
     ==> separation(L, \<lambda>x. is_DPow_body(L,A,env,p,x))"
apply (subgoal_tac "L(env) & L(p)") 
 prefer 2 apply (blast intro: transL) 
apply (rule separation_CollectI)
apply (rule_tac A="{A,env,p,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF DPow_body_reflection], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rule_tac env = "[x,A,env,p]" in DPow_body_iff_sats)
apply (rule sep_rules | simp)+
done



subsubsection{*The Instance of Replacement*}

lemma DPow_replacement_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B &
             (\<exists>env[L]. \<exists>p[L].
               mem_formula(L,p) & mem_list(L,A,env) & pair(L,env,p,u) &
               is_Collect (L, A, is_DPow_body(L,A,env,p), x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B &
             (\<exists>env \<in> Lset(i). \<exists>p \<in> Lset(i).
               mem_formula(**Lset(i),p) & mem_list(**Lset(i),A,env) & 
               pair(**Lset(i),env,p,u) &
               is_Collect (**Lset(i), A, is_DPow_body(**Lset(i),A,env,p), x))]"
apply (unfold is_Collect_def) 
apply (intro FOL_reflections function_reflections mem_formula_reflection
          mem_list_reflection DPow_body_reflection)
done

lemma DPow_replacement:
    "L(A)
    ==> strong_replacement (L, 
         \<lambda>ep z. \<exists>env[L]. \<exists>p[L]. mem_formula(L,p) & mem_list(L,A,env) &
                  pair(L,env,p,ep) & 
                  is_Collect(L, A, \<lambda>x. is_DPow_body(L,A,env,p,x), z))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (rule_tac A="{A,B,z}" in subset_LsetE, blast)
apply (rule ReflectsE [OF DPow_replacement_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (unfold is_Collect_def) 
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,B]" in mem_iff_sats)
apply (rule sep_rules mem_formula_iff_sats mem_list_iff_sats 
            DPow_body_iff_sats | simp)+
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

end
