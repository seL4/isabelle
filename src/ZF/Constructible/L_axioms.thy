header {* The class L satisfies the axioms of ZF*}

theory L_axioms = Formula + Relative:


text {* The class L satisfies the premises of locale @{text M_axioms} *}

lemma transL: "[| y\<in>x; L(x) |] ==> L(y)"
apply (insert Transset_Lset) 
apply (simp add: Transset_def L_def, blast) 
done

lemma nonempty: "L(0)"
apply (simp add: L_def) 
apply (blast intro: zero_in_Lset) 
done

lemma upair_ax: "upair_ax(L)"
apply (simp add: upair_ax_def upair_def, clarify)
apply (rule_tac x="{x,y}" in exI)  
apply (simp add: doubleton_in_L) 
done

lemma Union_ax: "Union_ax(L)"
apply (simp add: Union_ax_def big_union_def, clarify)
apply (rule_tac x="Union(x)" in exI)  
apply (simp add: Union_in_L, auto) 
apply (blast intro: transL) 
done

lemma power_ax: "power_ax(L)"
apply (simp add: power_ax_def powerset_def Relative.subset_def, clarify)
apply (rule_tac x="{y \<in> Pow(x). L(y)}" in exI)  
apply (simp add: LPow_in_L, auto)
apply (blast intro: transL) 
done

subsubsection{*For L to satisfy Replacement *}

(*Can't move these to Formula unless the definition of univalent is moved
there too!*)

lemma LReplace_in_Lset:
     "[|X \<in> Lset(i); univalent(L,X,Q); Ord(i)|] 
      ==> \<exists>j. Ord(j) & Replace(X, %x y. Q(x,y) & L(y)) \<subseteq> Lset(j)"
apply (rule_tac x="\<Union>y \<in> Replace(X, %x y. Q(x,y) & L(y)). succ(lrank(y))" 
       in exI)
apply simp
apply clarify 
apply (rule_tac a="x" in UN_I)  
 apply (simp_all add: Replace_iff univalent_def) 
apply (blast dest: transL L_I) 
done

lemma LReplace_in_L: 
     "[|L(X); univalent(L,X,Q)|] 
      ==> \<exists>Y. L(Y) & Replace(X, %x y. Q(x,y) & L(y)) \<subseteq> Y"
apply (drule L_D, clarify) 
apply (drule LReplace_in_Lset, assumption+)
apply (blast intro: L_I Lset_in_Lset_succ)
done

lemma replacement: "replacement(L,P)"
apply (simp add: replacement_def, clarify)
apply (frule LReplace_in_L, assumption+)
apply clarify 
apply (rule_tac x=Y in exI)   
apply (simp add: Replace_iff univalent_def, blast) 
done

end

(*

  and Inter_separation:
     "L(A) ==> separation(M, \<lambda>x. \<forall>y\<in>A. L(y) --> x\<in>y)"
  and cartprod_separation:
     "[| L(A); L(B) |] 
      ==> separation(M, \<lambda>z. \<exists>x\<in>A. \<exists>y\<in>B. L(x) & L(y) & pair(M,x,y,z))"
  and image_separation:
     "[| L(A); L(r) |] 
      ==> separation(M, \<lambda>y. \<exists>p\<in>r. L(p) & (\<exists>x\<in>A. L(x) & pair(M,x,y,p)))"
  and vimage_separation:
     "[| L(A); L(r) |] 
      ==> separation(M, \<lambda>x. \<exists>p\<in>r. L(p) & (\<exists>y\<in>A. L(x) & pair(M,x,y,p)))"
  and converse_separation:
     "L(r) ==> separation(M, \<lambda>z. \<exists>p\<in>r. L(p) & (\<exists>x y. L(x) & L(y) & 
				     pair(M,x,y,p) & pair(M,y,x,z)))"
  and restrict_separation:
     "L(A) 
      ==> separation(M, \<lambda>z. \<exists>x\<in>A. L(x) & (\<exists>y. L(y) & pair(M,x,y,z)))"
  and comp_separation:
     "[| L(r); L(s) |]
      ==> separation(M, \<lambda>xz. \<exists>x y z. L(x) & L(y) & L(z) &
			   (\<exists>xy\<in>s. \<exists>yz\<in>r. L(xy) & L(yz) & 
		  pair(M,x,z,xz) & pair(M,x,y,xy) & pair(M,y,z,yz)))"
  and pred_separation:
     "[| L(r); L(x) |] ==> separation(M, \<lambda>y. \<exists>p\<in>r. L(p) & pair(M,y,x,p))"
  and Memrel_separation:
     "separation(M, \<lambda>z. \<exists>x y. L(x) & L(y) & pair(M,x,y,z) \<and> x \<in> y)"
  and obase_separation:
     --{*part of the order type formalization*}
     "[| L(A); L(r) |] 
      ==> separation(M, \<lambda>a. \<exists>x g mx par. L(x) & L(g) & L(mx) & L(par) & 
	     ordinal(M,x) & membership(M,x,mx) & pred_set(M,A,a,r,par) &
	     order_isomorphism(M,par,r,x,mx,g))"
  and well_ord_iso_separation:
     "[| L(A); L(f); L(r) |] 
      ==> separation (M, \<lambda>x. x\<in>A --> (\<exists>y. L(y) \<and> (\<exists>p. L(p) \<and> 
		     fun_apply(M,f,x,y) \<and> pair(M,y,x,p) \<and> p \<in> r)))"
  and obase_equals_separation:
     "[| L(A); L(r) |] 
      ==> separation
      (M, \<lambda>x. x\<in>A --> ~(\<exists>y. L(y) & (\<exists>g. L(g) &
	      ordinal(M,y) & (\<exists>my pxr. L(my) & L(pxr) &
	      membership(M,y,my) & pred_set(M,A,x,r,pxr) &
	      order_isomorphism(M,pxr,r,y,my,g)))))"
  and is_recfun_separation:
     --{*for well-founded recursion.  NEEDS RELATIVIZATION*}
     "[| L(A); L(f); L(g); L(a); L(b) |] 
     ==> separation(M, \<lambda>x. x \<in> A --> \<langle>x,a\<rangle> \<in> r \<and> \<langle>x,b\<rangle> \<in> r \<and> f`x \<noteq> g`x)"
  and omap_replacement:
     "[| L(A); L(r) |] 
      ==> strong_replacement(M,
             \<lambda>a z. \<exists>x g mx par. L(x) & L(g) & L(mx) & L(par) &
	     ordinal(M,x) & pair(M,a,x,z) & membership(M,x,mx) & 
	     pred_set(M,A,a,r,par) & order_isomorphism(M,par,r,x,mx,g))"

*)