(*  Title:      ZF/Constructible/Rec_Separation.thy
    ID:   $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header {*Separation for Facts About Recursion*}

theory Rec_Separation = Separation + Internalize:

text{*This theory proves all instances needed for locales @{text
"M_trancl"} and @{text "M_datatypes"}*}

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

lemma rtran_closure_mem_reflection:
     "REFLECTS[\<lambda>x. rtran_closure_mem(L,f(x),g(x),h(x)),
               \<lambda>i x. rtran_closure_mem(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: rtran_closure_mem_def)
apply (intro FOL_reflections function_reflections fun_plus_reflections)
done

text{*Separation for @{term "rtrancl(r)"}.*}
lemma rtrancl_separation:
     "[| L(r); L(A) |] ==> separation (L, rtran_closure_mem(L,A,r))"
apply (rule gen_separation_multi [OF rtran_closure_mem_reflection, of "{r,A}"],
       auto)
apply (rule_tac env="[r,A]" in DPow_LsetI)
apply (rule rtran_closure_mem_iff_sats sep_rules | simp)+
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
apply (simp only: rtran_closure_def)
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
apply (simp only: tran_closure_def)
apply (intro FOL_reflections function_reflections
             rtran_closure_reflection composition_reflection)
done


subsubsection{*Separation for the Proof of @{text "wellfounded_on_trancl"}*}

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
apply (rule gen_separation_multi [OF wellfounded_trancl_reflects, of "{r,Z}"],
       auto)
apply (rule_tac env="[r,Z]" in DPow_LsetI)
apply (rule sep_rules tran_closure_iff_sats | simp)+
done


subsubsection{*Instantiating the locale @{text M_trancl}*}

lemma M_trancl_axioms_L: "M_trancl_axioms(L)"
  apply (rule M_trancl_axioms.intro)
   apply (assumption | rule rtrancl_separation wellfounded_trancl_separation)+
  done

theorem M_trancl_L: "PROP M_trancl(L)"
by (rule M_trancl.intro
         [OF M_trivial_L M_basic_axioms_L M_trancl_axioms_L])

lemmas iterates_abs = M_trancl.iterates_abs [OF M_trancl_L]
  and rtran_closure_rtrancl = M_trancl.rtran_closure_rtrancl [OF M_trancl_L]
  and trans_wfrec_abs = M_trancl.trans_wfrec_abs [OF M_trancl_L]
  and eq_pair_wfrec_iff = M_trancl.eq_pair_wfrec_iff [OF M_trancl_L]



subsection{*@{term L} is Closed Under the Operator @{term list}*}

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
apply (rule_tac u="{B,A,n,0,Memrel(succ(n))}" 
         in gen_separation_multi [OF list_replacement1_Reflects], 
       auto simp add: nonempty)
apply (rule_tac env="[B,A,n,0,Memrel(succ(n))]" in DPow_LsetI)
apply (rule sep_rules is_nat_case_iff_sats list_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done


lemma list_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B & u \<in> nat &
                is_iterates(L, is_list_functor(L, A), 0, u, x),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B & u \<in> nat &
               is_iterates(**Lset(i), is_list_functor(**Lset(i), A), 0, u, x)]"
by (intro FOL_reflections 
          is_iterates_reflection list_functor_reflection)

lemma list_replacement2:
   "L(A) ==> strong_replacement(L,
         \<lambda>n y. n\<in>nat & is_iterates(L, is_list_functor(L,A), 0, n, y))"
apply (rule strong_replacementI)
apply (rule_tac u="{A,B,0,nat}" 
         in gen_separation_multi [OF list_replacement2_Reflects], 
       auto simp add: L_nat nonempty)
apply (rule_tac env="[A,B,0,nat]" in DPow_LsetI)
apply (rule sep_rules list_functor_iff_sats is_iterates_iff_sats | simp)+
done


subsection{*@{term L} is Closed Under the Operator @{term formula}*}

subsubsection{*Instances of Replacement for Formulas*}

(*FIXME: could prove a lemma iterates_replacementI to eliminate the 
need to expand iterates_replacement and wfrec_replacement*)
lemma formula_replacement1_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B & (\<exists>y[L]. pair(L,u,y,x) &
         is_wfrec(L, iterates_MH(L, is_formula_functor(L), 0), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B & (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) &
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i),
                          is_formula_functor(**Lset(i)), 0), memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection formula_functor_reflection)

lemma formula_replacement1:
   "iterates_replacement(L, is_formula_functor(L), 0)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule_tac u="{B,n,0,Memrel(succ(n))}" 
         in gen_separation_multi [OF formula_replacement1_Reflects], 
       auto simp add: nonempty)
apply (rule_tac env="[n,B,0,Memrel(succ(n))]" in DPow_LsetI)
apply (rule sep_rules is_nat_case_iff_sats formula_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done

lemma formula_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B & u \<in> nat &
                is_iterates(L, is_formula_functor(L), 0, u, x),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B & u \<in> nat &
               is_iterates(**Lset(i), is_formula_functor(**Lset(i)), 0, u, x)]"
by (intro FOL_reflections 
          is_iterates_reflection formula_functor_reflection)

lemma formula_replacement2:
   "strong_replacement(L,
         \<lambda>n y. n\<in>nat & is_iterates(L, is_formula_functor(L), 0, n, y))"
apply (rule strong_replacementI)
apply (rule_tac u="{B,0,nat}" 
         in gen_separation_multi [OF formula_replacement2_Reflects], 
       auto simp add: nonempty L_nat)
apply (rule_tac env="[B,0,nat]" in DPow_LsetI)
apply (rule sep_rules formula_functor_iff_sats is_iterates_iff_sats | simp)+
done

text{*NB The proofs for type @{term formula} are virtually identical to those
for @{term "list(A)"}.  It was a cut-and-paste job! *}


subsubsection{*The Formula @{term is_nth}, Internalized*}

(* "is_nth(M,n,l,Z) ==
      \<exists>X[M]. is_iterates(M, is_tl(M), l, n, X) & is_hd(M,X,Z)" *)
constdefs nth_fm :: "[i,i,i]=>i"
    "nth_fm(n,l,Z) == 
       Exists(And(is_iterates_fm(tl_fm(1,0), succ(l), succ(n), 0), 
              hd_fm(0,succ(Z))))"

lemma nth_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> nth_fm(x,y,z) \<in> formula"
by (simp add: nth_fm_def)

lemma sats_nth_fm [simp]:
   "[| x < length(env); y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, nth_fm(x,y,z), env) <->
        is_nth(**A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: nth_fm_def is_nth_def sats_is_iterates_fm) 
done

lemma nth_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i < length(env); j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_nth(**A, x, y, z) <-> sats(A, nth_fm(i,j,k), env)"
by (simp add: sats_nth_fm)

theorem nth_reflection:
     "REFLECTS[\<lambda>x. is_nth(L, f(x), g(x), h(x)),  
               \<lambda>i x. is_nth(**Lset(i), f(x), g(x), h(x))]"
apply (simp only: is_nth_def)
apply (intro FOL_reflections is_iterates_reflection
             hd_reflection tl_reflection) 
done


subsubsection{*An Instance of Replacement for @{term nth}*}

(*FIXME: could prove a lemma iterates_replacementI to eliminate the 
need to expand iterates_replacement and wfrec_replacement*)
lemma nth_replacement_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B & (\<exists>y[L]. pair(L,u,y,x) &
         is_wfrec(L, iterates_MH(L, is_tl(L), z), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B & (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) &
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i),
                          is_tl(**Lset(i)), z), memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection tl_reflection)

lemma nth_replacement:
   "L(w) ==> iterates_replacement(L, is_tl(L), w)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule_tac u="{B,w,Memrel(succ(n))}" 
         in gen_separation_multi [OF nth_replacement_Reflects], 
       auto)
apply (rule_tac env="[B,w,Memrel(succ(n))]" in DPow_LsetI)
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
      apply (rule M_trancl.axioms [OF M_trancl_L])+
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
   [\<lambda>x. \<exists>u[L]. u \<in> B & (\<exists>y[L]. pair(L,u,y,x) &
         is_wfrec(L, iterates_MH(L, big_union(L), A), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B & (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) &
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i), big_union(**Lset(i)), A),
                  memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection)

lemma eclose_replacement1:
   "L(A) ==> iterates_replacement(L, big_union(L), A)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule_tac u="{B,A,n,Memrel(succ(n))}" 
         in gen_separation_multi [OF eclose_replacement1_Reflects], auto)
apply (rule_tac env="[B,A,n,Memrel(succ(n))]" in DPow_LsetI)
apply (rule sep_rules iterates_MH_iff_sats is_nat_case_iff_sats
             is_wfrec_iff_sats big_union_iff_sats quasinat_iff_sats | simp)+
done


lemma eclose_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B & u \<in> nat &
                is_iterates(L, big_union(L), A, u, x),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B & u \<in> nat &
               is_iterates(**Lset(i), big_union(**Lset(i)), A, u, x)]"
by (intro FOL_reflections function_reflections is_iterates_reflection)

lemma eclose_replacement2:
   "L(A) ==> strong_replacement(L,
         \<lambda>n y. n\<in>nat & is_iterates(L, big_union(L), A, n, y))"
apply (rule strong_replacementI)
apply (rule_tac u="{A,B,nat}" 
         in gen_separation_multi [OF eclose_replacement2_Reflects],
       auto simp add: L_nat)
apply (rule_tac env="[A,B,nat]" in DPow_LsetI)
apply (rule sep_rules is_iterates_iff_sats big_union_iff_sats | simp)+
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
