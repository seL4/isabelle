header{*Separation for the Absoluteness of Recursion*}

theory Rec_Separation = Separation:

text{*This theory proves all instances needed for locales @{text
"M_trancl"}, @{text "M_wfrank"} and @{text "M_datatypes"}*}

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
apply (rule DPowI2)
apply (rename_tac u)
apply (rule_tac env = "[u,r,A]" in rtran_closure_mem_iff_sats)
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[w,u,r,Z]" in mem_iff_sats) 
apply (rule sep_rules tran_closure_iff_sats | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
done

subsection{*Well-Founded Recursion!*}

(* M_is_recfun :: "[i=>o, i, i, [i,i,i]=>o, i] => o"
   "M_is_recfun(M,r,a,MH,f) == 
     \<forall>z[M]. z \<in> f <-> 
            5      4       3       2       1           0
            (\<exists>x[M]. \<exists>y[M]. \<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. \<exists>f_r_sx[M]. 
	       pair(M,x,y,z) & pair(M,x,a,xa) & upair(M,x,x,sx) &
               pre_image(M,r,sx,r_sx) & restriction(M,f,r_sx,f_r_sx) &
               xa \<in> r & MH(x, f_r_sx, y))"
*)

constdefs is_recfun_fm :: "[[i,i,i]=>i, i, i, i]=>i"
 "is_recfun_fm(p,r,a,f) == 
   Forall(Iff(Member(0,succ(f)),
    Exists(Exists(Exists(Exists(Exists(Exists(
     And(pair_fm(5,4,6),
      And(pair_fm(5,a#+7,3),
       And(upair_fm(5,5,2),
        And(pre_image_fm(r#+7,2,1),
         And(restriction_fm(f#+7,1,0),
          And(Member(3,r#+7), p(5,0,4)))))))))))))))"


lemma is_recfun_type_0:
     "[| !!x y z. [| x \<in> nat; y \<in> nat; z \<in> nat |] ==> p(x,y,z) \<in> formula;  
         x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_recfun_fm(p,x,y,z) \<in> formula"
apply (unfold is_recfun_fm_def)
(*FIXME: FIND OUT why simp loops!*)
apply typecheck
by simp 

lemma is_recfun_type [TC]:
     "[| p(5,0,4) \<in> formula;  
         x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_recfun_fm(p,x,y,z) \<in> formula"
by (simp add: is_recfun_fm_def) 

lemma arity_is_recfun_fm [simp]:
     "[| arity(p(5,0,4)) le 8; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(is_recfun_fm(p,x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
apply (frule lt_nat_in_nat, simp) 
apply (simp add: is_recfun_fm_def succ_Un_distrib [symmetric] ) 
apply (subst subset_Un_iff2 [of "arity(p(5,0,4))", THEN iffD1]) 
apply (rule le_imp_subset) 
apply (erule le_trans, simp) 
apply (simp add: succ_Un_distrib [symmetric] Un_ac) 
done

lemma sats_is_recfun_fm:
  assumes MH_iff_sats: 
      "!!x y z env. 
	 [| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
	 ==> MH(nth(x,env), nth(y,env), nth(z,env)) <-> sats(A, p(x,y,z), env)"
  shows 
      "[|x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
       ==> sats(A, is_recfun_fm(p,x,y,z), env) <-> 
           M_is_recfun(**A, nth(x,env), nth(y,env), MH, nth(z,env))"
by (simp add: is_recfun_fm_def M_is_recfun_def MH_iff_sats [THEN iff_sym])

lemma is_recfun_iff_sats:
  "[| (!!x y z env. [| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
                    ==> MH(nth(x,env), nth(y,env), nth(z,env)) <->
                        sats(A, p(x,y,z), env));
      nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> M_is_recfun(**A, x, y, MH, z) <-> sats(A, is_recfun_fm(p,i,j,k), env)" 
by (simp add: sats_is_recfun_fm [of A MH])

theorem is_recfun_reflection:
  assumes MH_reflection:
    "!!f g h. REFLECTS[\<lambda>x. MH(L, f(x), g(x), h(x)), 
                     \<lambda>i x. MH(**Lset(i), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. M_is_recfun(L, f(x), g(x), MH(L), h(x)), 
               \<lambda>i x. M_is_recfun(**Lset(i), f(x), g(x), MH(**Lset(i)), h(x))]"
apply (simp (no_asm_use) only: M_is_recfun_def setclass_simps)
apply (intro FOL_reflections function_reflections 
             restriction_reflection MH_reflection)  
done

subsection{*Separation for  @{term "wfrank"}*}

lemma wfrank_Reflects:
 "REFLECTS[\<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) -->
              ~ (\<exists>f[L]. M_is_recfun(L, rplus, x, %x f y. is_range(L,f,y), f)),
      \<lambda>i x. \<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) -->
         ~ (\<exists>f \<in> Lset(i). M_is_recfun(**Lset(i), rplus, x, %x f y. is_range(**Lset(i),f,y), f))]"
by (intro FOL_reflections function_reflections is_recfun_reflection tran_closure_reflection)  

lemma wfrank_separation:
     "L(r) ==>
      separation (L, \<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) -->
         ~ (\<exists>f[L]. M_is_recfun(L, rplus, x, %x f y. is_range(L,f,y), f)))"
apply (rule separation_CollectI) 
apply (rule_tac A="{r,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF wfrank_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPowI2)
apply (rename_tac u)  
apply (rule ball_iff_sats imp_iff_sats)+
apply (rule_tac env="[rplus,u,r]" in tran_closure_iff_sats)
apply (rule sep_rules is_recfun_iff_sats | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
done


subsection{*Replacement for @{term "wfrank"}*}

lemma wfrank_replacement_Reflects:
 "REFLECTS[\<lambda>z. \<exists>x[L]. x \<in> A & 
        (\<forall>rplus[L]. tran_closure(L,r,rplus) -->
         (\<exists>y[L]. \<exists>f[L]. pair(L,x,y,z)  & 
                        M_is_recfun(L, rplus, x, %x f y. is_range(L,f,y), f) &
                        is_range(L,f,y))),
 \<lambda>i z. \<exists>x \<in> Lset(i). x \<in> A & 
      (\<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) -->
       (\<exists>y \<in> Lset(i). \<exists>f \<in> Lset(i). pair(**Lset(i),x,y,z)  & 
         M_is_recfun(**Lset(i), rplus, x, %x f y. is_range(**Lset(i),f,y), f) &
         is_range(**Lset(i),f,y)))]"
by (intro FOL_reflections function_reflections fun_plus_reflections
             is_recfun_reflection tran_closure_reflection)


lemma wfrank_strong_replacement:
     "L(r) ==>
      strong_replacement(L, \<lambda>x z. 
         \<forall>rplus[L]. tran_closure(L,r,rplus) -->
         (\<exists>y[L]. \<exists>f[L]. pair(L,x,y,z)  & 
                        M_is_recfun(L, rplus, x, %x f y. is_range(L,f,y), f) &
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats ball_iff_sats conj_iff_sats)+
apply (rule_tac env = "[x,u,B,r]" in mem_iff_sats) 
apply (rule sep_rules tran_closure_iff_sats is_recfun_iff_sats | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
done


subsection{*Separation for  @{term "wfrank"}*}

lemma Ord_wfrank_Reflects:
 "REFLECTS[\<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) --> 
          ~ (\<forall>f[L]. \<forall>rangef[L]. 
             is_range(L,f,rangef) -->
             M_is_recfun(L, rplus, x, \<lambda>x f y. is_range(L,f,y), f) -->
             ordinal(L,rangef)),
      \<lambda>i x. \<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) --> 
          ~ (\<forall>f \<in> Lset(i). \<forall>rangef \<in> Lset(i). 
             is_range(**Lset(i),f,rangef) -->
             M_is_recfun(**Lset(i), rplus, x, \<lambda>x f y. is_range(**Lset(i),f,y), f) -->
             ordinal(**Lset(i),rangef))]"
by (intro FOL_reflections function_reflections is_recfun_reflection 
          tran_closure_reflection ordinal_reflection)

lemma  Ord_wfrank_separation:
     "L(r) ==>
      separation (L, \<lambda>x.
         \<forall>rplus[L]. tran_closure(L,r,rplus) --> 
          ~ (\<forall>f[L]. \<forall>rangef[L]. 
             is_range(L,f,rangef) -->
             M_is_recfun(L, rplus, x, \<lambda>x f y. is_range(L,f,y), f) -->
             ordinal(L,rangef)))" 
apply (rule separation_CollectI) 
apply (rule_tac A="{r,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF Ord_wfrank_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPowI2)
apply (rename_tac u)  
apply (rule ball_iff_sats imp_iff_sats)+
apply (rule_tac env="[rplus,u,r]" in tran_closure_iff_sats)
apply (rule sep_rules is_recfun_iff_sats | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
done


end
