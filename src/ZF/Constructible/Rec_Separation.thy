(*  Title:      ZF/Constructible/Rec_Separation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
*)

header {*Separation for Facts About Recursion*}

theory Rec_Separation = Separation + Internalize:

text{*This theory proves all instances needed for locales @{text
"M_trancl"}, @{text "M_wfrank"} and @{text "M_datatypes"}*}

lemma eq_succ_imp_lt: "[|i = succ(j); Ord(i)|] ==> j<i"
by simp


subsection{*The Locale @{text "M_trancl"}*}

subsubsection{*Separation for Reflexive/Transitive Closure*}

text{*First, The Defining Formula*}

(* "rtran_closure_mem(M,A,r,p) ==
      \<exists>nnat[M]. \<exists>n[M]. \<exists>n'[M].
       omega(M,nnat) & n\<in>nnat & successor(M,n,n') &
       (\<exists>f[M]. typed_function(M,n',A,f) &
        (\<exists>x[M]. \<exists>y[M]. \<exists>zero[M]. pair(M,x,y,p) & empty(M,zero) &
          fun_apply(M,f,zero,x) & fun_apply(M,f,n,y)) &
        (\<forall>j[M]. j\<in>n -->
          (\<exists>fj[M]. \<exists>sj[M]. \<exists>fsj[M]. \<exists>ffp[M].
            fun_apply(M,f,j,fj) & successor(M,j,sj) &
            fun_apply(M,f,sj,fsj) & pair(M,fj,fsj,ffp) & ffp \<in> r)))"*)
constdefs rtran_closure_mem_fm :: "[i,i,i]=>i"
 "rtran_closure_mem_fm(A,r,p) ==
   Exists(Exists(Exists(
    And(omega_fm(2),
     And(Member(1,2),
      And(succ_fm(1,0),
       Exists(And(typed_function_fm(1, A#+4, 0),
        And(Exists(Exists(Exists(
              And(pair_fm(2,1,p#+7),
               And(empty_fm(0),
                And(fun_apply_fm(3,0,2), fun_apply_fm(3,5,1))))))),
            Forall(Implies(Member(0,3),
             Exists(Exists(Exists(Exists(
              And(fun_apply_fm(5,4,3),
               And(succ_fm(4,2),
                And(fun_apply_fm(5,2,1),
                 And(pair_fm(3,1,0), Member(0,r#+9))))))))))))))))))))"


lemma rtran_closure_mem_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> rtran_closure_mem_fm(x,y,z) \<in> formula"
by (simp add: rtran_closure_mem_fm_def)

lemma arity_rtran_closure_mem_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> arity(rtran_closure_mem_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: rtran_closure_mem_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_rtran_closure_mem_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, rtran_closure_mem_fm(x,y,z), env) <->
        rtran_closure_mem(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: rtran_closure_mem_fm_def rtran_closure_mem_def)

lemma rtran_closure_mem_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> rtran_closure_mem(**A, x, y, z) <-> sats(A, rtran_closure_mem_fm(i,j,k), env)"
by (simp add: sats_rtran_closure_mem_fm)

theorem rtran_closure_mem_reflection:
     "REFLECTS[\<lambda>x. rtran_closure_mem(L,f(x),g(x),h(x)),
               \<lambda>i x. rtran_closure_mem(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: rtran_closure_mem_def setclass_simps)
apply (intro FOL_reflections function_reflections fun_plus_reflections)
done

text{*Separation for @{term "rtrancl(r)"}.*}
lemma rtrancl_separation:
     "[| L(r); L(A) |] ==> separation (L, rtran_closure_mem(L,A,r))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,A,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF rtran_closure_mem_reflection], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule_tac env = "[u,r,A]" in rtran_closure_mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsubsection{*Reflexive/Transitive Closure, Internalized*}

(*  "rtran_closure(M,r,s) ==
        \<forall>A[M]. is_field(M,r,A) -->
         (\<forall>p[M]. p \<in> s <-> rtran_closure_mem(M,A,r,p))" *)
constdefs rtran_closure_fm :: "[i,i]=>i"
 "rtran_closure_fm(r,s) ==
   Forall(Implies(field_fm(succ(r),0),
                  Forall(Iff(Member(0,succ(succ(s))),
                             rtran_closure_mem_fm(1,succ(succ(r)),0)))))"

lemma rtran_closure_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> rtran_closure_fm(x,y) \<in> formula"
by (simp add: rtran_closure_fm_def)

lemma arity_rtran_closure_fm [simp]:
     "[| x \<in> nat; y \<in> nat |]
      ==> arity(rtran_closure_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: rtran_closure_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_rtran_closure_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, rtran_closure_fm(x,y), env) <->
        rtran_closure(**A, nth(x,env), nth(y,env))"
by (simp add: rtran_closure_fm_def rtran_closure_def)

lemma rtran_closure_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> rtran_closure(**A, x, y) <-> sats(A, rtran_closure_fm(i,j), env)"
by simp

theorem rtran_closure_reflection:
     "REFLECTS[\<lambda>x. rtran_closure(L,f(x),g(x)),
               \<lambda>i x. rtran_closure(**Lset(i),f(x),g(x))]"
apply (simp only: rtran_closure_def setclass_simps)
apply (intro FOL_reflections function_reflections rtran_closure_mem_reflection)
done


subsubsection{*Transitive Closure of a Relation, Internalized*}

(*  "tran_closure(M,r,t) ==
         \<exists>s[M]. rtran_closure(M,r,s) & composition(M,r,s,t)" *)
constdefs tran_closure_fm :: "[i,i]=>i"
 "tran_closure_fm(r,s) ==
   Exists(And(rtran_closure_fm(succ(r),0), composition_fm(succ(r),0,succ(s))))"

lemma tran_closure_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> tran_closure_fm(x,y) \<in> formula"
by (simp add: tran_closure_fm_def)

lemma arity_tran_closure_fm [simp]:
     "[| x \<in> nat; y \<in> nat |]
      ==> arity(tran_closure_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: tran_closure_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_tran_closure_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, tran_closure_fm(x,y), env) <->
        tran_closure(**A, nth(x,env), nth(y,env))"
by (simp add: tran_closure_fm_def tran_closure_def)

lemma tran_closure_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> tran_closure(**A, x, y) <-> sats(A, tran_closure_fm(i,j), env)"
by simp

theorem tran_closure_reflection:
     "REFLECTS[\<lambda>x. tran_closure(L,f(x),g(x)),
               \<lambda>i x. tran_closure(**Lset(i),f(x),g(x))]"
apply (simp only: tran_closure_def setclass_simps)
apply (intro FOL_reflections function_reflections
             rtran_closure_reflection composition_reflection)
done


subsection{*Separation for the Proof of @{text "wellfounded_on_trancl"}*}

lemma wellfounded_trancl_reflects:
  "REFLECTS[\<lambda>x. \<exists>w[L]. \<exists>wx[L]. \<exists>rp[L].
                 w \<in> Z & pair(L,w,x,wx) & tran_closure(L,r,rp) & wx \<in> rp,
   \<lambda>i x. \<exists>w \<in> Lset(i). \<exists>wx \<in> Lset(i). \<exists>rp \<in> Lset(i).
       w \<in> Z & pair(**Lset(i),w,x,wx) & tran_closure(**Lset(i),r,rp) &
       wx \<in> rp]"
by (intro FOL_reflections function_reflections fun_plus_reflections
          tran_closure_reflection)


lemma wellfounded_trancl_separation:
         "[| L(r); L(Z) |] ==>
          separation (L, \<lambda>x.
              \<exists>w[L]. \<exists>wx[L]. \<exists>rp[L].
               w \<in> Z & pair(L,w,x,wx) & tran_closure(L,r,rp) & wx \<in> rp)"
apply (rule separation_CollectI)
apply (rule_tac A="{r,Z,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF wellfounded_trancl_reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[w,u,r,Z]" in mem_iff_sats)
apply (rule sep_rules tran_closure_iff_sats | simp)+
done


subsubsection{*Instantiating the locale @{text M_trancl}*}

lemma M_trancl_axioms_L: "M_trancl_axioms(L)"
  apply (rule M_trancl_axioms.intro)
   apply (assumption | rule rtrancl_separation wellfounded_trancl_separation)+
  done

theorem M_trancl_L: "PROP M_trancl(L)"
by (rule M_trancl.intro
         [OF M_triv_axioms_L M_axioms_axioms_L M_trancl_axioms_L])

lemmas iterates_abs = M_trancl.iterates_abs [OF M_trancl_L]
  and rtran_closure_rtrancl = M_trancl.rtran_closure_rtrancl [OF M_trancl_L]
  and rtrancl_closed = M_trancl.rtrancl_closed [OF M_trancl_L]
  and rtrancl_abs = M_trancl.rtrancl_abs [OF M_trancl_L]
  and trancl_closed = M_trancl.trancl_closed [OF M_trancl_L]
  and trancl_abs = M_trancl.trancl_abs [OF M_trancl_L]
  and wellfounded_on_trancl = M_trancl.wellfounded_on_trancl [OF M_trancl_L]
  and wellfounded_trancl = M_trancl.wellfounded_trancl [OF M_trancl_L]
  and wfrec_relativize = M_trancl.wfrec_relativize [OF M_trancl_L]
  and trans_wfrec_relativize = M_trancl.trans_wfrec_relativize [OF M_trancl_L]
  and trans_wfrec_abs = M_trancl.trans_wfrec_abs [OF M_trancl_L]
  and trans_eq_pair_wfrec_iff = M_trancl.trans_eq_pair_wfrec_iff [OF M_trancl_L]
  and eq_pair_wfrec_iff = M_trancl.eq_pair_wfrec_iff [OF M_trancl_L]

declare rtrancl_closed [intro,simp]
declare rtrancl_abs [simp]
declare trancl_closed [intro,simp]
declare trancl_abs [simp]


subsection{*Well-Founded Recursion!*}


text{*Alternative definition, minimizing nesting of quantifiers around MH*}
lemma M_is_recfun_iff:
   "M_is_recfun(M,MH,r,a,f) <->
    (\<forall>z[M]. z \<in> f <-> 
     (\<exists>x[M]. \<exists>f_r_sx[M]. \<exists>y[M]. 
             MH(x, f_r_sx, y) & pair(M,x,y,z) &
             (\<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. 
                pair(M,x,a,xa) & upair(M,x,x,sx) &
               pre_image(M,r,sx,r_sx) & restriction(M,f,r_sx,f_r_sx) &
               xa \<in> r)))"
apply (simp add: M_is_recfun_def)
apply (rule rall_cong, blast) 
done


(* M_is_recfun :: "[i=>o, [i,i,i]=>o, i, i, i] => o"
   "M_is_recfun(M,MH,r,a,f) ==
     \<forall>z[M]. z \<in> f <->
               2      1           0
new def     (\<exists>x[M]. \<exists>f_r_sx[M]. \<exists>y[M]. 
             MH(x, f_r_sx, y) & pair(M,x,y,z) &
             (\<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. 
                pair(M,x,a,xa) & upair(M,x,x,sx) &
               pre_image(M,r,sx,r_sx) & restriction(M,f,r_sx,f_r_sx) &
               xa \<in> r)"
*)

text{*The three arguments of @{term p} are always 2, 1, 0 and z*}
constdefs is_recfun_fm :: "[i, i, i, i]=>i"
 "is_recfun_fm(p,r,a,f) == 
   Forall(Iff(Member(0,succ(f)),
    Exists(Exists(Exists(
     And(p, 
      And(pair_fm(2,0,3),
       Exists(Exists(Exists(
	And(pair_fm(5,a#+7,2),
	 And(upair_fm(5,5,1),
	  And(pre_image_fm(r#+7,1,0),
	   And(restriction_fm(f#+7,0,4), Member(2,r#+7)))))))))))))))"

lemma is_recfun_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_recfun_fm(p,x,y,z) \<in> formula"
by (simp add: is_recfun_fm_def)


lemma sats_is_recfun_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A|] 
        ==> MH(a2, a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,env)))))"
  shows 
      "[|x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
       ==> sats(A, is_recfun_fm(p,x,y,z), env) <->
           M_is_recfun(**A, MH, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: is_recfun_fm_def M_is_recfun_iff MH_iff_sats [THEN iff_sym])

lemma is_recfun_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A|] 
        ==> MH(a2, a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,env)))))"
  shows
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> M_is_recfun(**A, MH, x, y, z) <-> sats(A, is_recfun_fm(p,i,j,k), env)"
by (simp add: sats_is_recfun_fm [OF MH_iff_sats]) 

text{*The additional variable in the premise, namely @{term f'}, is essential.
It lets @{term MH} depend upon @{term x}, which seems often necessary.
The same thing occurs in @{text is_wfrec_reflection}.*}
theorem is_recfun_reflection:
  assumes MH_reflection:
    "!!f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(**Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. M_is_recfun(L, MH(L,x), f(x), g(x), h(x)), 
             \<lambda>i x. M_is_recfun(**Lset(i), MH(**Lset(i),x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: M_is_recfun_def setclass_simps)
apply (intro FOL_reflections function_reflections
             restriction_reflection MH_reflection)
done

subsubsection{*The Operator @{term is_wfrec}*}

text{*The three arguments of @{term p} are always 2, 1, 0*}

(* is_wfrec :: "[i=>o, i, [i,i,i]=>o, i, i] => o"
    "is_wfrec(M,MH,r,a,z) == 
      \<exists>f[M]. M_is_recfun(M,MH,r,a,f) & MH(a,f,z)" *)
constdefs is_wfrec_fm :: "[i, i, i, i]=>i"
 "is_wfrec_fm(p,r,a,z) == 
    Exists(And(is_recfun_fm(p, succ(r), succ(a), 0),
           Exists(Exists(Exists(Exists(
             And(Equal(2,a#+5), And(Equal(1,4), And(Equal(0,z#+5), p)))))))))"

text{*We call @{term p} with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.*}

text{*There's an additional existential quantifier to ensure that the
      environments in both calls to MH have the same length.*}

lemma is_wfrec_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_wfrec_fm(p,x,y,z) \<in> formula"
by (simp add: is_wfrec_fm_def) 

lemma sats_is_wfrec_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A|] 
        ==> MH(a2, a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows 
      "[|x \<in> nat; y < length(env); z < length(env); env \<in> list(A)|]
       ==> sats(A, is_wfrec_fm(p,x,y,z), env) <-> 
           is_wfrec(**A, MH, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: is_wfrec_fm_def sats_is_recfun_fm is_wfrec_def MH_iff_sats [THEN iff_sym], blast) 
done


lemma is_wfrec_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A|] 
        ==> MH(a2, a1, a0) <-> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows
  "[|nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j < length(env); k < length(env); env \<in> list(A)|]
   ==> is_wfrec(**A, MH, x, y, z) <-> sats(A, is_wfrec_fm(p,i,j,k), env)" 
by (simp add: sats_is_wfrec_fm [OF MH_iff_sats])

theorem is_wfrec_reflection:
  assumes MH_reflection:
    "!!f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(**Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_wfrec(L, MH(L,x), f(x), g(x), h(x)), 
               \<lambda>i x. is_wfrec(**Lset(i), MH(**Lset(i),x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_wfrec_def setclass_simps)
apply (intro FOL_reflections MH_reflection is_recfun_reflection)
done

subsection{*The Locale @{text "M_wfrank"}*}

subsubsection{*Separation for @{term "wfrank"}*}

lemma wfrank_Reflects:
 "REFLECTS[\<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) -->
              ~ (\<exists>f[L]. M_is_recfun(L, %x f y. is_range(L,f,y), rplus, x, f)),
      \<lambda>i x. \<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) -->
         ~ (\<exists>f \<in> Lset(i).
            M_is_recfun(**Lset(i), %x f y. is_range(**Lset(i),f,y),
                        rplus, x, f))]"
by (intro FOL_reflections function_reflections is_recfun_reflection tran_closure_reflection)

lemma wfrank_separation:
     "L(r) ==>
      separation (L, \<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) -->
         ~ (\<exists>f[L]. M_is_recfun(L, %x f y. is_range(L,f,y), rplus, x, f)))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF wfrank_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule ball_iff_sats imp_iff_sats)+
apply (rule_tac env="[rplus,u,r]" in tran_closure_iff_sats)
apply (rule sep_rules | simp)+
apply (rule sep_rules is_recfun_iff_sats | simp)+
done


subsubsection{*Replacement for @{term "wfrank"}*}

lemma wfrank_replacement_Reflects:
 "REFLECTS[\<lambda>z. \<exists>x[L]. x \<in> A &
        (\<forall>rplus[L]. tran_closure(L,r,rplus) -->
         (\<exists>y[L]. \<exists>f[L]. pair(L,x,y,z)  &
                        M_is_recfun(L, %x f y. is_range(L,f,y), rplus, x, f) &
                        is_range(L,f,y))),
 \<lambda>i z. \<exists>x \<in> Lset(i). x \<in> A &
      (\<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) -->
       (\<exists>y \<in> Lset(i). \<exists>f \<in> Lset(i). pair(**Lset(i),x,y,z)  &
         M_is_recfun(**Lset(i), %x f y. is_range(**Lset(i),f,y), rplus, x, f) &
         is_range(**Lset(i),f,y)))]"
by (intro FOL_reflections function_reflections fun_plus_reflections
             is_recfun_reflection tran_closure_reflection)


lemma wfrank_strong_replacement:
     "L(r) ==>
      strong_replacement(L, \<lambda>x z.
         \<forall>rplus[L]. tran_closure(L,r,rplus) -->
         (\<exists>y[L]. \<exists>f[L]. pair(L,x,y,z)  &
                        M_is_recfun(L, %x f y. is_range(L,f,y), rplus, x, f) &
                        is_range(L,f,y)))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (rule_tac A="{B,r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF wfrank_replacement_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats ball_iff_sats conj_iff_sats)+
apply (rule_tac env = "[x,u,B,r]" in mem_iff_sats)
apply (rule sep_rules list.intros app_type tran_closure_iff_sats is_recfun_iff_sats | simp)+
done


subsubsection{*Separation for Proving @{text Ord_wfrank_range}*}

lemma Ord_wfrank_Reflects:
 "REFLECTS[\<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) -->
          ~ (\<forall>f[L]. \<forall>rangef[L].
             is_range(L,f,rangef) -->
             M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f) -->
             ordinal(L,rangef)),
      \<lambda>i x. \<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) -->
          ~ (\<forall>f \<in> Lset(i). \<forall>rangef \<in> Lset(i).
             is_range(**Lset(i),f,rangef) -->
             M_is_recfun(**Lset(i), \<lambda>x f y. is_range(**Lset(i),f,y),
                         rplus, x, f) -->
             ordinal(**Lset(i),rangef))]"
by (intro FOL_reflections function_reflections is_recfun_reflection
          tran_closure_reflection ordinal_reflection)

lemma  Ord_wfrank_separation:
     "L(r) ==>
      separation (L, \<lambda>x.
         \<forall>rplus[L]. tran_closure(L,r,rplus) -->
          ~ (\<forall>f[L]. \<forall>rangef[L].
             is_range(L,f,rangef) -->
             M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f) -->
             ordinal(L,rangef)))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF Ord_wfrank_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule ball_iff_sats imp_iff_sats)+
apply (rule_tac env="[rplus,u,r]" in tran_closure_iff_sats)
apply (rule sep_rules is_recfun_iff_sats | simp)+
done


subsubsection{*Instantiating the locale @{text M_wfrank}*}

lemma M_wfrank_axioms_L: "M_wfrank_axioms(L)"
  apply (rule M_wfrank_axioms.intro)
   apply (assumption | rule
     wfrank_separation wfrank_strong_replacement Ord_wfrank_separation)+
  done

theorem M_wfrank_L: "PROP M_wfrank(L)"
  apply (rule M_wfrank.intro)
     apply (rule M_trancl.axioms [OF M_trancl_L])+
  apply (rule M_wfrank_axioms_L) 
  done

lemmas iterates_closed = M_wfrank.iterates_closed [OF M_wfrank_L]
  and exists_wfrank = M_wfrank.exists_wfrank [OF M_wfrank_L]
  and M_wellfoundedrank = M_wfrank.M_wellfoundedrank [OF M_wfrank_L]
  and Ord_wfrank_range = M_wfrank.Ord_wfrank_range [OF M_wfrank_L]
  and Ord_range_wellfoundedrank = M_wfrank.Ord_range_wellfoundedrank [OF M_wfrank_L]
  and function_wellfoundedrank = M_wfrank.function_wellfoundedrank [OF M_wfrank_L]
  and domain_wellfoundedrank = M_wfrank.domain_wellfoundedrank [OF M_wfrank_L]
  and wellfoundedrank_type = M_wfrank.wellfoundedrank_type [OF M_wfrank_L]
  and Ord_wellfoundedrank = M_wfrank.Ord_wellfoundedrank [OF M_wfrank_L]
  and wellfoundedrank_eq = M_wfrank.wellfoundedrank_eq [OF M_wfrank_L]
  and wellfoundedrank_lt = M_wfrank.wellfoundedrank_lt [OF M_wfrank_L]
  and wellfounded_imp_subset_rvimage = M_wfrank.wellfounded_imp_subset_rvimage [OF M_wfrank_L]
  and wellfounded_imp_wf = M_wfrank.wellfounded_imp_wf [OF M_wfrank_L]
  and wellfounded_on_imp_wf_on = M_wfrank.wellfounded_on_imp_wf_on [OF M_wfrank_L]
  and wf_abs = M_wfrank.wf_abs [OF M_wfrank_L]
  and wf_on_abs = M_wfrank.wf_on_abs [OF M_wfrank_L]
  and wfrec_replacement_iff = M_wfrank.wfrec_replacement_iff [OF M_wfrank_L]
  and trans_wfrec_closed = M_wfrank.trans_wfrec_closed [OF M_wfrank_L]
  and wfrec_closed = M_wfrank.wfrec_closed [OF M_wfrank_L]

declare iterates_closed [intro,simp]
declare Ord_wfrank_range [rule_format]
declare wf_abs [simp]
declare wf_on_abs [simp]


subsection{*For Datatypes*}

subsubsection{*Binary Products, Internalized*}

constdefs cartprod_fm :: "[i,i,i]=>i"
(* "cartprod(M,A,B,z) ==
        \<forall>u[M]. u \<in> z <-> (\<exists>x[M]. x\<in>A & (\<exists>y[M]. y\<in>B & pair(M,x,y,u)))" *)
    "cartprod_fm(A,B,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(A))),
                         Exists(And(Member(0,succ(succ(succ(B)))),
                                    pair_fm(1,0,2)))))))"

lemma cartprod_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> cartprod_fm(x,y,z) \<in> formula"
by (simp add: cartprod_fm_def)

lemma arity_cartprod_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> arity(cartprod_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: cartprod_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_cartprod_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, cartprod_fm(x,y,z), env) <->
        cartprod(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: cartprod_fm_def cartprod_def)

lemma cartprod_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> cartprod(**A, x, y, z) <-> sats(A, cartprod_fm(i,j,k), env)"
by (simp add: sats_cartprod_fm)

theorem cartprod_reflection:
     "REFLECTS[\<lambda>x. cartprod(L,f(x),g(x),h(x)),
               \<lambda>i x. cartprod(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: cartprod_def setclass_simps)
apply (intro FOL_reflections pair_reflection)
done


subsubsection{*Binary Sums, Internalized*}

(* "is_sum(M,A,B,Z) ==
       \<exists>A0[M]. \<exists>n1[M]. \<exists>s1[M]. \<exists>B1[M].
         3      2       1        0
       number1(M,n1) & cartprod(M,n1,A,A0) & upair(M,n1,n1,s1) &
       cartprod(M,s1,B,B1) & union(M,A0,B1,Z)"  *)
constdefs sum_fm :: "[i,i,i]=>i"
    "sum_fm(A,B,Z) ==
       Exists(Exists(Exists(Exists(
        And(number1_fm(2),
            And(cartprod_fm(2,A#+4,3),
                And(upair_fm(2,2,1),
                    And(cartprod_fm(1,B#+4,0), union_fm(3,0,Z#+4)))))))))"

lemma sum_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> sum_fm(x,y,z) \<in> formula"
by (simp add: sum_fm_def)

lemma arity_sum_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> arity(sum_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: sum_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_sum_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, sum_fm(x,y,z), env) <->
        is_sum(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: sum_fm_def is_sum_def)

lemma sum_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_sum(**A, x, y, z) <-> sats(A, sum_fm(i,j,k), env)"
by simp

theorem sum_reflection:
     "REFLECTS[\<lambda>x. is_sum(L,f(x),g(x),h(x)),
               \<lambda>i x. is_sum(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_sum_def setclass_simps)
apply (intro FOL_reflections function_reflections cartprod_reflection)
done


subsubsection{*The Operator @{term quasinat}*}

(* "is_quasinat(M,z) == empty(M,z) | (\<exists>m[M]. successor(M,m,z))" *)
constdefs quasinat_fm :: "i=>i"
    "quasinat_fm(z) == Or(empty_fm(z), Exists(succ_fm(0,succ(z))))"

lemma quasinat_type [TC]:
     "x \<in> nat ==> quasinat_fm(x) \<in> formula"
by (simp add: quasinat_fm_def)

lemma arity_quasinat_fm [simp]:
     "x \<in> nat ==> arity(quasinat_fm(x)) = succ(x)"
by (simp add: quasinat_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_quasinat_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, quasinat_fm(x), env) <-> is_quasinat(**A, nth(x,env))"
by (simp add: quasinat_fm_def is_quasinat_def)

lemma quasinat_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> is_quasinat(**A, x) <-> sats(A, quasinat_fm(i), env)"
by simp

theorem quasinat_reflection:
     "REFLECTS[\<lambda>x. is_quasinat(L,f(x)),
               \<lambda>i x. is_quasinat(**Lset(i),f(x))]"
apply (simp only: is_quasinat_def setclass_simps)
apply (intro FOL_reflections function_reflections)
done


subsubsection{*The Operator @{term is_nat_case}*}
text{*I could not get it to work with the more natural assumption that 
 @{term is_b} takes two arguments.  Instead it must be a formula where 1 and 0
 stand for @{term m} and @{term b}, respectively.*}

(* is_nat_case :: "[i=>o, i, [i,i]=>o, i, i] => o"
    "is_nat_case(M, a, is_b, k, z) ==
       (empty(M,k) --> z=a) &
       (\<forall>m[M]. successor(M,m,k) --> is_b(m,z)) &
       (is_quasinat(M,k) | empty(M,z))" *)
text{*The formula @{term is_b} has free variables 1 and 0.*}
constdefs is_nat_case_fm :: "[i, i, i, i]=>i"
 "is_nat_case_fm(a,is_b,k,z) == 
    And(Implies(empty_fm(k), Equal(z,a)),
        And(Forall(Implies(succ_fm(0,succ(k)), 
                   Forall(Implies(Equal(0,succ(succ(z))), is_b)))),
            Or(quasinat_fm(k), empty_fm(z))))"

lemma is_nat_case_type [TC]:
     "[| is_b \<in> formula;  
         x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_nat_case_fm(x,is_b,y,z) \<in> formula"
by (simp add: is_nat_case_fm_def)

lemma sats_is_nat_case_fm:
  assumes is_b_iff_sats: 
      "!!a. a \<in> A ==> is_b(a,nth(z, env)) <-> 
                      sats(A, p, Cons(nth(z,env), Cons(a, env)))"
  shows 
      "[|x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A)|]
       ==> sats(A, is_nat_case_fm(x,p,y,z), env) <->
           is_nat_case(**A, nth(x,env), is_b, nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)
apply (simp add: is_nat_case_fm_def is_nat_case_def is_b_iff_sats [THEN iff_sym])
done

lemma is_nat_case_iff_sats:
  "[| (!!a. a \<in> A ==> is_b(a,z) <->
                      sats(A, p, Cons(z, Cons(a,env))));
      nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k < length(env); env \<in> list(A)|]
   ==> is_nat_case(**A, x, is_b, y, z) <-> sats(A, is_nat_case_fm(i,p,j,k), env)"
by (simp add: sats_is_nat_case_fm [of A is_b])


text{*The second argument of @{term is_b} gives it direct access to @{term x},
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for @{term iterates_MH}.*}
theorem is_nat_case_reflection:
  assumes is_b_reflection:
    "!!h f g. REFLECTS[\<lambda>x. is_b(L, h(x), f(x), g(x)),
                     \<lambda>i x. is_b(**Lset(i), h(x), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_nat_case(L, f(x), is_b(L,x), g(x), h(x)),
               \<lambda>i x. is_nat_case(**Lset(i), f(x), is_b(**Lset(i), x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_nat_case_def setclass_simps)
apply (intro FOL_reflections function_reflections
             restriction_reflection is_b_reflection quasinat_reflection)
done



subsection{*The Operator @{term iterates_MH}, Needed for Iteration*}

(*  iterates_MH :: "[i=>o, [i,i]=>o, i, i, i, i] => o"
   "iterates_MH(M,isF,v,n,g,z) ==
        is_nat_case(M, v, \<lambda>m u. \<exists>gm[M]. fun_apply(M,g,m,gm) & isF(gm,u),
                    n, z)" *)
constdefs iterates_MH_fm :: "[i, i, i, i, i]=>i"
 "iterates_MH_fm(isF,v,n,g,z) == 
    is_nat_case_fm(v, 
      Exists(And(fun_apply_fm(succ(succ(succ(g))),2,0), 
                     Forall(Implies(Equal(0,2), isF)))), 
      n, z)"

lemma iterates_MH_type [TC]:
     "[| p \<in> formula;  
         v \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> iterates_MH_fm(p,v,x,y,z) \<in> formula"
by (simp add: iterates_MH_fm_def)

lemma sats_iterates_MH_fm:
  assumes is_F_iff_sats:
      "!!a b c d. [| a \<in> A; b \<in> A; c \<in> A; d \<in> A|]
              ==> is_F(a,b) <->
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d,env)))))"
  shows 
      "[|v \<in> nat; x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A)|]
       ==> sats(A, iterates_MH_fm(p,v,x,y,z), env) <->
           iterates_MH(**A, is_F, nth(v,env), nth(x,env), nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: iterates_MH_fm_def iterates_MH_def sats_is_nat_case_fm 
              is_F_iff_sats [symmetric])
apply (rule is_nat_case_cong) 
apply (simp_all add: setclass_def)
done

lemma iterates_MH_iff_sats:
  assumes is_F_iff_sats:
      "!!a b c d. [| a \<in> A; b \<in> A; c \<in> A; d \<in> A|]
              ==> is_F(a,b) <->
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d,env)))))"
  shows 
  "[| nth(i',env) = v; nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i' \<in> nat; i \<in> nat; j \<in> nat; k < length(env); env \<in> list(A)|]
   ==> iterates_MH(**A, is_F, v, x, y, z) <->
       sats(A, iterates_MH_fm(p,i',i,j,k), env)"
by (simp add: sats_iterates_MH_fm [OF is_F_iff_sats]) 

text{*The second argument of @{term p} gives it direct access to @{term x},
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for @{term list_N}.*}
theorem iterates_MH_reflection:
  assumes p_reflection:
    "!!f g h. REFLECTS[\<lambda>x. p(L, h(x), f(x), g(x)),
                     \<lambda>i x. p(**Lset(i), h(x), f(x), g(x))]"
 shows "REFLECTS[\<lambda>x. iterates_MH(L, p(L,x), e(x), f(x), g(x), h(x)),
               \<lambda>i x. iterates_MH(**Lset(i), p(**Lset(i),x), e(x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: iterates_MH_def)
txt{*Must be careful: simplifying with @{text setclass_simps} above would
     change @{text "\<exists>gm[**Lset(i)]"} into @{text "\<exists>gm \<in> Lset(i)"}, when
     it would no longer match rule @{text is_nat_case_reflection}. *}
apply (rule is_nat_case_reflection)
apply (simp (no_asm_use) only: setclass_simps)
apply (intro FOL_reflections function_reflections is_nat_case_reflection
             restriction_reflection p_reflection)
done



subsection{*@{term L} is Closed Under the Operator @{term list}*}

subsubsection{*The List Functor, Internalized*}

constdefs list_functor_fm :: "[i,i,i]=>i"
(* "is_list_functor(M,A,X,Z) ==
        \<exists>n1[M]. \<exists>AX[M].
         number1(M,n1) & cartprod(M,A,X,AX) & is_sum(M,n1,AX,Z)" *)
    "list_functor_fm(A,X,Z) ==
       Exists(Exists(
        And(number1_fm(1),
            And(cartprod_fm(A#+2,X#+2,0), sum_fm(1,0,Z#+2)))))"

lemma list_functor_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> list_functor_fm(x,y,z) \<in> formula"
by (simp add: list_functor_fm_def)

lemma arity_list_functor_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> arity(list_functor_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: list_functor_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_list_functor_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, list_functor_fm(x,y,z), env) <->
        is_list_functor(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: list_functor_fm_def is_list_functor_def)

lemma list_functor_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> is_list_functor(**A, x, y, z) <-> sats(A, list_functor_fm(i,j,k), env)"
by simp

theorem list_functor_reflection:
     "REFLECTS[\<lambda>x. is_list_functor(L,f(x),g(x),h(x)),
               \<lambda>i x. is_list_functor(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_list_functor_def setclass_simps)
apply (intro FOL_reflections number1_reflection
             cartprod_reflection sum_reflection)
done


subsubsection{*Instances of Replacement for Lists*}

lemma list_replacement1_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L,u,y,x) \<and>
         is_wfrec(L, iterates_MH(L, is_list_functor(L,A), 0), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i),
                          is_list_functor(**Lset(i), A), 0), memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection list_functor_reflection)


lemma list_replacement1:
   "L(A) ==> iterates_replacement(L, is_list_functor(L,A), 0)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (insert nonempty)
apply (subgoal_tac "L(Memrel(succ(n)))")
apply (rule_tac A="{B,A,n,z,0,Memrel(succ(n))}" in subset_LsetE, blast )
apply (rule ReflectsE [OF list_replacement1_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (elim conjE)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,n,B,0,Memrel(succ(n))]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats list_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done


lemma list_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn[L]. \<exists>msn[L]. successor(L, u, sn) \<and> membership(L, sn, msn) \<and>
           is_wfrec (L, iterates_MH (L, is_list_functor(L, A), 0),
                              msn, u, x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn \<in> Lset(i). \<exists>msn \<in> Lset(i).
          successor(**Lset(i), u, sn) \<and> membership(**Lset(i), sn, msn) \<and>
           is_wfrec (**Lset(i),
                 iterates_MH (**Lset(i), is_list_functor(**Lset(i), A), 0),
                     msn, u, x))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection list_functor_reflection)


lemma list_replacement2:
   "L(A) ==> strong_replacement(L,
         \<lambda>n y. n\<in>nat &
               (\<exists>sn[L]. \<exists>msn[L]. successor(L,n,sn) & membership(L,sn,msn) &
               is_wfrec(L, iterates_MH(L,is_list_functor(L,A), 0),
                        msn, n, y)))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (insert nonempty)
apply (rule_tac A="{A,B,z,0,nat}" in subset_LsetE)
apply (blast intro: L_nat)
apply (rule ReflectsE [OF list_replacement2_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,B,0,nat]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats list_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done


subsection{*@{term L} is Closed Under the Operator @{term formula}*}

subsubsection{*The Formula Functor, Internalized*}

constdefs formula_functor_fm :: "[i,i]=>i"
(*     "is_formula_functor(M,X,Z) ==
        \<exists>nat'[M]. \<exists>natnat[M]. \<exists>natnatsum[M]. \<exists>XX[M]. \<exists>X3[M].
           4           3               2       1       0
          omega(M,nat') & cartprod(M,nat',nat',natnat) &
          is_sum(M,natnat,natnat,natnatsum) &
          cartprod(M,X,X,XX) & is_sum(M,XX,X,X3) &
          is_sum(M,natnatsum,X3,Z)" *)
    "formula_functor_fm(X,Z) ==
       Exists(Exists(Exists(Exists(Exists(
        And(omega_fm(4),
         And(cartprod_fm(4,4,3),
          And(sum_fm(3,3,2),
           And(cartprod_fm(X#+5,X#+5,1),
            And(sum_fm(1,X#+5,0), sum_fm(2,0,Z#+5)))))))))))"

lemma formula_functor_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> formula_functor_fm(x,y) \<in> formula"
by (simp add: formula_functor_fm_def)

lemma sats_formula_functor_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, formula_functor_fm(x,y), env) <->
        is_formula_functor(**A, nth(x,env), nth(y,env))"
by (simp add: formula_functor_fm_def is_formula_functor_def)

lemma formula_functor_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_formula_functor(**A, x, y) <-> sats(A, formula_functor_fm(i,j), env)"
by simp

theorem formula_functor_reflection:
     "REFLECTS[\<lambda>x. is_formula_functor(L,f(x),g(x)),
               \<lambda>i x. is_formula_functor(**Lset(i),f(x),g(x))]"
apply (simp only: is_formula_functor_def setclass_simps)
apply (intro FOL_reflections omega_reflection
             cartprod_reflection sum_reflection)
done

subsubsection{*Instances of Replacement for Formulas*}

lemma formula_replacement1_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L,u,y,x) \<and>
         is_wfrec(L, iterates_MH(L, is_formula_functor(L), 0), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i),
                          is_formula_functor(**Lset(i)), 0), memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection formula_functor_reflection)

lemma formula_replacement1:
   "iterates_replacement(L, is_formula_functor(L), 0)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (insert nonempty)
apply (subgoal_tac "L(Memrel(succ(n)))")
apply (rule_tac A="{B,n,z,0,Memrel(succ(n))}" in subset_LsetE, blast )
apply (rule ReflectsE [OF formula_replacement1_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,n,B,0,Memrel(succ(n))]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats formula_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done

lemma formula_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn[L]. \<exists>msn[L]. successor(L, u, sn) \<and> membership(L, sn, msn) \<and>
           is_wfrec (L, iterates_MH (L, is_formula_functor(L), 0),
                              msn, u, x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn \<in> Lset(i). \<exists>msn \<in> Lset(i).
          successor(**Lset(i), u, sn) \<and> membership(**Lset(i), sn, msn) \<and>
           is_wfrec (**Lset(i),
                 iterates_MH (**Lset(i), is_formula_functor(**Lset(i)), 0),
                     msn, u, x))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection formula_functor_reflection)


lemma formula_replacement2:
   "strong_replacement(L,
         \<lambda>n y. n\<in>nat &
               (\<exists>sn[L]. \<exists>msn[L]. successor(L,n,sn) & membership(L,sn,msn) &
               is_wfrec(L, iterates_MH(L,is_formula_functor(L), 0),
                        msn, n, y)))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (insert nonempty)
apply (rule_tac A="{B,z,0,nat}" in subset_LsetE)
apply (blast intro: L_nat)
apply (rule ReflectsE [OF formula_replacement2_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,B,0,nat]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats formula_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done

text{*NB The proofs for type @{term formula} are virtually identical to those
for @{term "list(A)"}.  It was a cut-and-paste job! *}


subsubsection{*The Formula @{term is_nth}, Internalized*}

(* "is_nth(M,n,l,Z) == 
      \<exists>X[M]. \<exists>sn[M]. \<exists>msn[M]. 
       2       1       0
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_tl(M), l), msn, n, X) &
       is_hd(M,X,Z)" *)
constdefs nth_fm :: "[i,i,i]=>i"
    "nth_fm(n,l,Z) == 
       Exists(Exists(Exists(
         And(succ_fm(n#+3,1),
          And(Memrel_fm(1,0),
           And(is_wfrec_fm(iterates_MH_fm(tl_fm(1,0),l#+8,2,1,0), 0, n#+3, 2), hd_fm(2,Z#+3)))))))"

lemma nth_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> nth_fm(x,y,z) \<in> formula"
by (simp add: nth_fm_def)

lemma sats_nth_fm [simp]:
   "[| x < length(env); y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, nth_fm(x,y,z), env) <->
        is_nth(**A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: nth_fm_def is_nth_def sats_is_wfrec_fm sats_iterates_MH_fm) 
done

lemma nth_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i < length(env); j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_nth(**A, x, y, z) <-> sats(A, nth_fm(i,j,k), env)"
by (simp add: sats_nth_fm)

theorem nth_reflection:
     "REFLECTS[\<lambda>x. is_nth(L, f(x), g(x), h(x)),  
               \<lambda>i x. is_nth(**Lset(i), f(x), g(x), h(x))]"
apply (simp only: is_nth_def setclass_simps)
apply (intro FOL_reflections function_reflections is_wfrec_reflection 
             iterates_MH_reflection hd_reflection tl_reflection) 
done


subsubsection{*An Instance of Replacement for @{term nth}*}

lemma nth_replacement_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L,u,y,x) \<and>
         is_wfrec(L, iterates_MH(L, is_tl(L), z), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i),
                          is_tl(**Lset(i)), z), memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection list_functor_reflection tl_reflection)

lemma nth_replacement:
   "L(w) ==> iterates_replacement(L, %l t. is_tl(L,l,t), w)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule rallI)
apply (rule separation_CollectI)
apply (subgoal_tac "L(Memrel(succ(n)))")
apply (rule_tac A="{A,n,w,z,Memrel(succ(n))}" in subset_LsetE, blast )
apply (rule ReflectsE [OF nth_replacement_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (elim conjE)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,z,w,Memrel(succ(n))]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats tl_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done



subsubsection{*Instantiating the locale @{text M_datatypes}*}

lemma M_datatypes_axioms_L: "M_datatypes_axioms(L)"
  apply (rule M_datatypes_axioms.intro)
      apply (assumption | rule
        list_replacement1 list_replacement2
        formula_replacement1 formula_replacement2
        nth_replacement)+
  done

theorem M_datatypes_L: "PROP M_datatypes(L)"
  apply (rule M_datatypes.intro)
      apply (rule M_wfrank.axioms [OF M_wfrank_L])+
 apply (rule M_datatypes_axioms_L) 
 done

lemmas list_closed = M_datatypes.list_closed [OF M_datatypes_L]
  and formula_closed = M_datatypes.formula_closed [OF M_datatypes_L]
  and list_abs = M_datatypes.list_abs [OF M_datatypes_L]
  and formula_abs = M_datatypes.formula_abs [OF M_datatypes_L]
  and nth_abs = M_datatypes.nth_abs [OF M_datatypes_L]

declare list_closed [intro,simp]
declare formula_closed [intro,simp]
declare list_abs [simp]
declare formula_abs [simp]
declare nth_abs [simp]


subsection{*@{term L} is Closed Under the Operator @{term eclose}*}

subsubsection{*Instances of Replacement for @{term eclose}*}

lemma eclose_replacement1_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L,u,y,x) \<and>
         is_wfrec(L, iterates_MH(L, big_union(L), A), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i), big_union(**Lset(i)), A),
                  memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection)

lemma eclose_replacement1:
   "L(A) ==> iterates_replacement(L, big_union(L), A)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (subgoal_tac "L(Memrel(succ(n)))")
apply (rule_tac A="{B,A,n,z,Memrel(succ(n))}" in subset_LsetE, blast )
apply (rule ReflectsE [OF eclose_replacement1_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (elim conjE)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,n,B,Memrel(succ(n))]" in mem_iff_sats)
apply (rule sep_rules iterates_MH_iff_sats is_nat_case_iff_sats
             is_wfrec_iff_sats big_union_iff_sats quasinat_iff_sats | simp)+
done


lemma eclose_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn[L]. \<exists>msn[L]. successor(L, u, sn) \<and> membership(L, sn, msn) \<and>
           is_wfrec (L, iterates_MH (L, big_union(L), A),
                              msn, u, x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn \<in> Lset(i). \<exists>msn \<in> Lset(i).
          successor(**Lset(i), u, sn) \<and> membership(**Lset(i), sn, msn) \<and>
           is_wfrec (**Lset(i),
                 iterates_MH (**Lset(i), big_union(**Lset(i)), A),
                     msn, u, x))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection)


lemma eclose_replacement2:
   "L(A) ==> strong_replacement(L,
         \<lambda>n y. n\<in>nat &
               (\<exists>sn[L]. \<exists>msn[L]. successor(L,n,sn) & membership(L,sn,msn) &
               is_wfrec(L, iterates_MH(L,big_union(L), A),
                        msn, n, y)))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (rule_tac A="{A,B,z,nat}" in subset_LsetE)
apply (blast intro: L_nat)
apply (rule ReflectsE [OF eclose_replacement2_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,B,nat]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats iterates_MH_iff_sats
              is_wfrec_iff_sats big_union_iff_sats quasinat_iff_sats | simp)+
done


subsubsection{*Instantiating the locale @{text M_eclose}*}

lemma M_eclose_axioms_L: "M_eclose_axioms(L)"
  apply (rule M_eclose_axioms.intro)
   apply (assumption | rule eclose_replacement1 eclose_replacement2)+
  done

theorem M_eclose_L: "PROP M_eclose(L)"
  apply (rule M_eclose.intro)
       apply (rule M_datatypes.axioms [OF M_datatypes_L])+
  apply (rule M_eclose_axioms_L)
  done

lemmas eclose_closed [intro, simp] = M_eclose.eclose_closed [OF M_eclose_L]
  and eclose_abs [intro, simp] = M_eclose.eclose_abs [OF M_eclose_L]
  and transrec_replacementI = M_eclose.transrec_replacementI [OF M_eclose_L]

end
