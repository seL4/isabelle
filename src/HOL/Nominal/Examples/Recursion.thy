(* $Id$ *)

theory Recursion
imports "Iteration" 
begin

types 'a f1_ty' = "name\<Rightarrow>('a::pt_name)"
      'a f2_ty' = "lam\<Rightarrow>lam\<Rightarrow>'a\<Rightarrow>'a\<Rightarrow>('a::pt_name)"
      'a f3_ty' = "lam\<Rightarrow>name\<Rightarrow>'a\<Rightarrow>('a::pt_name)"

constdefs
  rfun' :: "'a f1_ty' \<Rightarrow> 'a f2_ty' \<Rightarrow> 'a f3_ty' \<Rightarrow> lam \<Rightarrow> (lam\<times>'a::pt_name)" 
  "rfun' f1 f2 f3 t \<equiv> 
      (itfun 
        (\<lambda>a. (Var a,f1 a)) 
        (\<lambda>r1 r2. (App (fst r1) (fst r2), f2 (fst r1) (fst r2) (snd r1) (snd r2))) 
        (\<lambda>a r. (Lam [a].(fst r),f3 (fst r) a (snd r)))
       t)"

  rfun :: "'a f1_ty' \<Rightarrow> 'a f2_ty' \<Rightarrow> 'a f3_ty' \<Rightarrow> lam \<Rightarrow> 'a::pt_name" 
  "rfun f1 f2 f3 t \<equiv> snd (rfun' f1 f2 f3 t)"

lemma fcb': 
  fixes f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows  "\<exists>a.  a \<sharp> (\<lambda>a r. (Lam [a].fst r, f3 (fst r) a (snd r))) \<and>
               (\<forall>y.  a \<sharp> (Lam [a].fst y, f3 (fst y) a (snd y)))"
using c f
apply(auto)
apply(rule_tac x="a" in exI)
apply(auto simp add: abs_fresh fresh_prod)
apply(rule_tac S="supp f3" in supports_fresh)
apply(supports_simp add: perm_fst perm_snd)
apply(simp add: supp_prod)
apply(simp add: fresh_def)
done

lemma fsupp':
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  shows "finite((supp
          (\<lambda>a. (Var a, f1 a),
           \<lambda>r1 r2. (App (fst r1) (fst r2), f2 (fst r1) (fst r2) (snd r1) (snd r2)),
           \<lambda>a r. (Lam [a].fst r, f3 (fst r) a (snd r))))::name set)"
using f by (finite_guess add: perm_fst perm_snd fs_name1 supp_prod)

lemma rfun'_fst:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)" 
  and     c: "(\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y))"
  shows "fst (rfun' f1 f2 f3 t) = t"
apply(rule lam.induct'[of "\<lambda>_. ((supp (f1,f2,f3))::name set)" "\<lambda>_ t. fst (rfun' f1 f2 f3 t) = t"])
apply(fold fresh_def)
apply(simp add: f)
apply(unfold rfun'_def)
apply(simp only: itfun_Var[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(simp)
apply(simp only: itfun_App[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(simp)
apply(auto)
apply(rule trans)
apply(rule_tac f="fst" in arg_cong)
apply(rule itfun_Lam[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(auto simp add: fresh_prod)
apply(rule_tac S="supp f1" in supports_fresh)
apply(supports_simp)
apply(subgoal_tac "finite ((supp (f1,f2,f3))::name set)")
apply(simp add: supp_prod)
apply(rule f)
apply(simp add: fresh_def)
apply(rule_tac S="supp f2" in supports_fresh)
apply(supports_simp add: perm_fst perm_snd)
apply(subgoal_tac "finite ((supp (f1,f2,f3))::name set)")
apply(simp add: supp_prod)
apply(rule f)
apply(simp add: fresh_def)
apply(rule_tac S="supp f3" in supports_fresh)
apply(supports_simp add: perm_fst perm_snd)
apply(subgoal_tac "finite ((supp (f1,f2,f3))::name set)")
apply(simp add: supp_prod)
apply(rule f)
apply(simp add: fresh_def)
done

lemma rfun'_Var:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows "rfun' f1 f2 f3 (Var c) = (Var c, f1 c)"
apply(simp add: rfun'_def)
apply(simp add: itfun_Var[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
done

lemma rfun'_App:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows "rfun' f1 f2 f3 (App t1 t2) = 
                (App t1 t2, f2 t1 t2 (rfun f1 f2 f3 t1) (rfun f1 f2 f3 t2))"
apply(simp add: rfun'_def)
apply(rule trans)
apply(rule itfun_App[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(fold rfun'_def)
apply(simp_all add: rfun'_fst[OF f, OF c])
apply(simp_all add: rfun_def)
done

lemma rfun'_Lam:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  and     a: "b\<sharp>(f1,f2,f3)"
  shows "rfun' f1 f2 f3 (Lam [b].t) = (Lam [b].t, f3 t b (rfun f1 f2 f3 t))"
using a f
apply(simp add: rfun'_def)
apply(rule trans)
apply(rule itfun_Lam[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(auto simp add: fresh_prod)
apply(rule_tac S="supp f1" in supports_fresh)
apply(supports_simp)
apply(simp add: supp_prod)
apply(simp add: fresh_def)
apply(rule_tac S="supp f2" in supports_fresh)
apply(supports_simp add: perm_fst perm_snd)
apply(simp add: supp_prod)
apply(simp add: fresh_def)
apply(rule_tac S="supp f3" in supports_fresh)
apply(supports_simp add: perm_snd perm_fst)
apply(simp add: supp_prod)
apply(simp add: fresh_def)
apply(fold rfun'_def)
apply(simp_all add: rfun'_fst[OF f, OF c])
apply(simp_all add: rfun_def)
done

lemma rfun_Var:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows "rfun f1 f2 f3 (Var c) = f1 c"
apply(unfold rfun_def)
apply(simp add: rfun'_Var[OF f, OF c])
done

lemma rfun_App:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows "rfun f1 f2 f3 (App t1 t2) = f2 t1 t2 (rfun f1 f2 f3 t1) (rfun f1 f2 f3 t2)"
apply(unfold rfun_def)
apply(simp add: rfun'_App[OF f, OF c])
apply(simp add: rfun_def)
done

lemma rfun_Lam:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  and     a: "b\<sharp>(f1,f2,f3)"
  shows "rfun f1 f2 f3 (Lam [b].t) = f3 t b (rfun f1 f2 f3 t)"
using a
apply(unfold rfun_def)
apply(simp add: rfun'_Lam[OF f, OF c])
apply(simp add: rfun_def)
done

end