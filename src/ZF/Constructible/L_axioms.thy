header {* The class L satisfies the axioms of ZF*}

theory L_axioms = Formula + Relative + Reflection:


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
apply (frule LReplace_in_L, assumption+, clarify) 
apply (rule_tac x=Y in exI)   
apply (simp add: Replace_iff univalent_def, blast) 
done

subsection{*Instantiation of the locale @{text M_triv_axioms}*}

lemma Lset_mono_le: "mono_le_subset(Lset)"
by (simp add: mono_le_subset_def le_imp_subset Lset_mono) 

lemma Lset_cont: "cont_Ord(Lset)"
by (simp add: cont_Ord_def Limit_Lset_eq OUnion_def Limit_is_Ord) 

lemmas Pair_in_Lset = Formula.Pair_in_LLimit;

lemmas L_nat = Ord_in_L [OF Ord_nat];

ML
{*
val transL = thm "transL";
val nonempty = thm "nonempty";
val upair_ax = thm "upair_ax";
val Union_ax = thm "Union_ax";
val power_ax = thm "power_ax";
val replacement = thm "replacement";
val L_nat = thm "L_nat";

fun kill_flex_triv_prems st = Seq.hd ((REPEAT_FIRST assume_tac) st);

fun trivaxL th =
    kill_flex_triv_prems 
       ([transL, nonempty, upair_ax, Union_ax, power_ax, replacement, L_nat] 
        MRS (inst "M" "L" th));

bind_thm ("ball_abs", trivaxL (thm "M_triv_axioms.ball_abs"));
bind_thm ("rall_abs", trivaxL (thm "M_triv_axioms.rall_abs"));
bind_thm ("bex_abs", trivaxL (thm "M_triv_axioms.bex_abs"));
bind_thm ("rex_abs", trivaxL (thm "M_triv_axioms.rex_abs"));
bind_thm ("ball_iff_equiv", trivaxL (thm "M_triv_axioms.ball_iff_equiv"));
bind_thm ("M_equalityI", trivaxL (thm "M_triv_axioms.M_equalityI"));
bind_thm ("empty_abs", trivaxL (thm "M_triv_axioms.empty_abs"));
bind_thm ("subset_abs", trivaxL (thm "M_triv_axioms.subset_abs"));
bind_thm ("upair_abs", trivaxL (thm "M_triv_axioms.upair_abs"));
bind_thm ("upair_in_M_iff", trivaxL (thm "M_triv_axioms.upair_in_M_iff"));
bind_thm ("singleton_in_M_iff", trivaxL (thm "M_triv_axioms.singleton_in_M_iff"));
bind_thm ("pair_abs", trivaxL (thm "M_triv_axioms.pair_abs"));
bind_thm ("pair_in_M_iff", trivaxL (thm "M_triv_axioms.pair_in_M_iff"));
bind_thm ("pair_components_in_M", trivaxL (thm "M_triv_axioms.pair_components_in_M"));
bind_thm ("cartprod_abs", trivaxL (thm "M_triv_axioms.cartprod_abs"));
bind_thm ("union_abs", trivaxL (thm "M_triv_axioms.union_abs"));
bind_thm ("inter_abs", trivaxL (thm "M_triv_axioms.inter_abs"));
bind_thm ("setdiff_abs", trivaxL (thm "M_triv_axioms.setdiff_abs"));
bind_thm ("Union_abs", trivaxL (thm "M_triv_axioms.Union_abs"));
bind_thm ("Union_closed", trivaxL (thm "M_triv_axioms.Union_closed"));
bind_thm ("Un_closed", trivaxL (thm "M_triv_axioms.Un_closed"));
bind_thm ("cons_closed", trivaxL (thm "M_triv_axioms.cons_closed"));
bind_thm ("successor_abs", trivaxL (thm "M_triv_axioms.successor_abs"));
bind_thm ("succ_in_M_iff", trivaxL (thm "M_triv_axioms.succ_in_M_iff"));
bind_thm ("separation_closed", trivaxL (thm "M_triv_axioms.separation_closed"));
bind_thm ("strong_replacementI", trivaxL (thm "M_triv_axioms.strong_replacementI"));
bind_thm ("strong_replacement_closed", trivaxL (thm "M_triv_axioms.strong_replacement_closed"));
bind_thm ("RepFun_closed", trivaxL (thm "M_triv_axioms.RepFun_closed"));
bind_thm ("lam_closed", trivaxL (thm "M_triv_axioms.lam_closed"));
bind_thm ("image_abs", trivaxL (thm "M_triv_axioms.image_abs"));
bind_thm ("powerset_Pow", trivaxL (thm "M_triv_axioms.powerset_Pow"));
bind_thm ("powerset_imp_subset_Pow", trivaxL (thm "M_triv_axioms.powerset_imp_subset_Pow"));
bind_thm ("nat_into_M", trivaxL (thm "M_triv_axioms.nat_into_M"));
bind_thm ("nat_case_closed", trivaxL (thm "M_triv_axioms.nat_case_closed"));
bind_thm ("Inl_in_M_iff", trivaxL (thm "M_triv_axioms.Inl_in_M_iff"));
bind_thm ("Inr_in_M_iff", trivaxL (thm "M_triv_axioms.Inr_in_M_iff"));
bind_thm ("lt_closed", trivaxL (thm "M_triv_axioms.lt_closed"));
bind_thm ("transitive_set_abs", trivaxL (thm "M_triv_axioms.transitive_set_abs"));
bind_thm ("ordinal_abs", trivaxL (thm "M_triv_axioms.ordinal_abs"));
bind_thm ("limit_ordinal_abs", trivaxL (thm "M_triv_axioms.limit_ordinal_abs"));
bind_thm ("successor_ordinal_abs", trivaxL (thm "M_triv_axioms.successor_ordinal_abs"));
bind_thm ("finite_ordinal_abs", trivaxL (thm "M_triv_axioms.finite_ordinal_abs"));
bind_thm ("omega_abs", trivaxL (thm "M_triv_axioms.omega_abs"));
bind_thm ("number1_abs", trivaxL (thm "M_triv_axioms.number1_abs"));
bind_thm ("number1_abs", trivaxL (thm "M_triv_axioms.number1_abs"));
bind_thm ("number3_abs", trivaxL (thm "M_triv_axioms.number3_abs"));
*}

declare ball_abs [simp] 
declare rall_abs [simp] 
declare bex_abs [simp] 
declare rex_abs [simp] 
declare empty_abs [simp] 
declare subset_abs [simp] 
declare upair_abs [simp] 
declare upair_in_M_iff [iff]
declare singleton_in_M_iff [iff]
declare pair_abs [simp] 
declare pair_in_M_iff [iff]
declare cartprod_abs [simp] 
declare union_abs [simp] 
declare inter_abs [simp] 
declare setdiff_abs [simp] 
declare Union_abs [simp] 
declare Union_closed [intro,simp]
declare Un_closed [intro,simp]
declare cons_closed [intro,simp]
declare successor_abs [simp] 
declare succ_in_M_iff [iff]
declare separation_closed [intro,simp]
declare strong_replacementI [rule_format]
declare strong_replacement_closed [intro,simp]
declare RepFun_closed [intro,simp]
declare lam_closed [intro,simp]
declare image_abs [simp] 
declare nat_into_M [intro]
declare Inl_in_M_iff [iff]
declare Inr_in_M_iff [iff]
declare transitive_set_abs [simp] 
declare ordinal_abs [simp] 
declare limit_ordinal_abs [simp] 
declare successor_ordinal_abs [simp] 
declare finite_ordinal_abs [simp] 
declare omega_abs [simp] 
declare number1_abs [simp] 
declare number1_abs [simp] 
declare number3_abs [simp]


subsection{*Instantiation of the locale @{text reflection}*}

text{*instances of locale constants*}
constdefs
  L_Reflects :: "[i=>o,i=>o,[i,i]=>o] => o"
    "L_Reflects(Cl,P,Q) == Closed_Unbounded(Cl) &
                           (\<forall>a. Cl(a) --> (\<forall>x \<in> Lset(a). P(x) <-> Q(a,x)))"

  L_F0 :: "[i=>o,i] => i"
    "L_F0(P,y) == \<mu>b. (\<exists>z. L(z) \<and> P(<y,z>)) --> (\<exists>z\<in>Lset(b). P(<y,z>))"

  L_FF :: "[i=>o,i] => i"
    "L_FF(P)   == \<lambda>a. \<Union>y\<in>Lset(a). L_F0(P,y)"

  L_ClEx :: "[i=>o,i] => o"
    "L_ClEx(P) == \<lambda>a. Limit(a) \<and> normalize(L_FF(P),a) = a"

theorem Triv_reflection [intro]:
     "L_Reflects(Ord, P, \<lambda>a x. P(x))"
by (simp add: L_Reflects_def)

theorem Not_reflection [intro]:
     "L_Reflects(Cl,P,Q) ==> L_Reflects(Cl, \<lambda>x. ~P(x), \<lambda>a x. ~Q(a,x))"
by (simp add: L_Reflects_def) 

theorem And_reflection [intro]:
     "[| L_Reflects(Cl,P,Q); L_Reflects(C',P',Q') |] 
      ==> L_Reflects(\<lambda>a. Cl(a) \<and> C'(a), \<lambda>x. P(x) \<and> P'(x), 
                                      \<lambda>a x. Q(a,x) \<and> Q'(a,x))"
by (simp add: L_Reflects_def Closed_Unbounded_Int, blast)

theorem Or_reflection [intro]:
     "[| L_Reflects(Cl,P,Q); L_Reflects(C',P',Q') |] 
      ==> L_Reflects(\<lambda>a. Cl(a) \<and> C'(a), \<lambda>x. P(x) \<or> P'(x), 
                                      \<lambda>a x. Q(a,x) \<or> Q'(a,x))"
by (simp add: L_Reflects_def Closed_Unbounded_Int, blast)

theorem Imp_reflection [intro]:
     "[| L_Reflects(Cl,P,Q); L_Reflects(C',P',Q') |] 
      ==> L_Reflects(\<lambda>a. Cl(a) \<and> C'(a), 
                   \<lambda>x. P(x) --> P'(x), 
                   \<lambda>a x. Q(a,x) --> Q'(a,x))"
by (simp add: L_Reflects_def Closed_Unbounded_Int, blast)

theorem Iff_reflection [intro]:
     "[| L_Reflects(Cl,P,Q); L_Reflects(C',P',Q') |] 
      ==> L_Reflects(\<lambda>a. Cl(a) \<and> C'(a), 
                   \<lambda>x. P(x) <-> P'(x), 
                   \<lambda>a x. Q(a,x) <-> Q'(a,x))"
by (simp add: L_Reflects_def Closed_Unbounded_Int, blast) 


theorem Ex_reflection [intro]:
     "L_Reflects(Cl, \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))) 
      ==> L_Reflects(\<lambda>a. Cl(a) \<and> L_ClEx(\<lambda>x. P(fst(x),snd(x)), a), 
                   \<lambda>x. \<exists>z. L(z) \<and> P(x,z), 
                   \<lambda>a x. \<exists>z\<in>Lset(a). Q(a,x,z))"
apply (unfold L_Reflects_def L_ClEx_def L_FF_def L_F0_def L_def) 
apply (rule reflection.Ex_reflection [OF Lset_mono_le Lset_cont Pair_in_Lset],
       assumption+)
done

theorem All_reflection [intro]:
     "L_Reflects(Cl,  \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x)))
      ==> L_Reflects(\<lambda>a. Cl(a) \<and> L_ClEx(\<lambda>x. ~P(fst(x),snd(x)), a), 
                   \<lambda>x. \<forall>z. L(z) --> P(x,z), 
                   \<lambda>a x. \<forall>z\<in>Lset(a). Q(a,x,z))" 
apply (unfold L_Reflects_def L_ClEx_def L_FF_def L_F0_def L_def) 
apply (rule reflection.All_reflection [OF Lset_mono_le Lset_cont Pair_in_Lset],
       assumption+)
done

theorem Rex_reflection [intro]:
     "L_Reflects(Cl, \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))) 
      ==> L_Reflects(\<lambda>a. Cl(a) \<and> L_ClEx(\<lambda>x. P(fst(x),snd(x)), a), 
                   \<lambda>x. \<exists>z[L]. P(x,z), 
                   \<lambda>a x. \<exists>z\<in>Lset(a). Q(a,x,z))"
by (unfold rex_def, blast) 

theorem Rall_reflection [intro]:
     "L_Reflects(Cl,  \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x)))
      ==> L_Reflects(\<lambda>a. Cl(a) \<and> L_ClEx(\<lambda>x. ~P(fst(x),snd(x)), a), 
                   \<lambda>x. \<forall>z[L]. P(x,z), 
                   \<lambda>a x. \<forall>z\<in>Lset(a). Q(a,x,z))" 
by (unfold rall_def, blast) 

lemma ReflectsD:
     "[|L_Reflects(Cl,P,Q); Ord(i)|] 
      ==> \<exists>j. i<j & (\<forall>x \<in> Lset(j). P(x) <-> Q(j,x))"
apply (simp add: L_Reflects_def Closed_Unbounded_def, clarify)
apply (blast dest!: UnboundedD) 
done

lemma ReflectsE:
     "[| L_Reflects(Cl,P,Q); Ord(i);
         !!j. [|i<j;  \<forall>x \<in> Lset(j). P(x) <-> Q(j,x)|] ==> R |]
      ==> R"
by (blast dest!: ReflectsD) 

lemma Collect_mem_eq: "{x\<in>A. x\<in>B} = A \<inter> B";
by blast


end

(*

  and cartprod_separation:
     "[| L(A); L(B) |] 
      ==> separation(L, \<lambda>z. \<exists>x\<in>A. \<exists>y\<in>B. L(x) & L(y) & pair(L,x,y,z))"
  and image_separation:
     "[| L(A); L(r) |] 
      ==> separation(L, \<lambda>y. \<exists>p\<in>r. L(p) & (\<exists>x\<in>A. L(x) & pair(L,x,y,p)))"
  and vimage_separation:
     "[| L(A); L(r) |] 
      ==> separation(L, \<lambda>x. \<exists>p\<in>r. L(p) & (\<exists>y\<in>A. L(x) & pair(L,x,y,p)))"
  and converse_separation:
     "L(r) ==> separation(L, \<lambda>z. \<exists>p\<in>r. L(p) & (\<exists>x y. L(x) & L(y) & 
				     pair(L,x,y,p) & pair(L,y,x,z)))"
  and restrict_separation:
     "L(A) 
      ==> separation(L, \<lambda>z. \<exists>x\<in>A. L(x) & (\<exists>y. L(y) & pair(L,x,y,z)))"
  and comp_separation:
     "[| L(r); L(s) |]
      ==> separation(L, \<lambda>xz. \<exists>x y z. L(x) & L(y) & L(z) &
			   (\<exists>xy\<in>s. \<exists>yz\<in>r. L(xy) & L(yz) & 
		  pair(L,x,z,xz) & pair(L,x,y,xy) & pair(L,y,z,yz)))"
  and pred_separation:
     "[| L(r); L(x) |] ==> separation(L, \<lambda>y. \<exists>p\<in>r. L(p) & pair(L,y,x,p))"
  and Memrel_separation:
     "separation(L, \<lambda>z. \<exists>x y. L(x) & L(y) & pair(L,x,y,z) \<and> x \<in> y)"
  and obase_separation:
     --{*part of the order type formalization*}
     "[| L(A); L(r) |] 
      ==> separation(L, \<lambda>a. \<exists>x g mx par. L(x) & L(g) & L(mx) & L(par) & 
	     ordinal(L,x) & membership(L,x,mx) & pred_set(L,A,a,r,par) &
	     order_isomorphism(L,par,r,x,mx,g))"
  and well_ord_iso_separation:
     "[| L(A); L(f); L(r) |] 
      ==> separation (L, \<lambda>x. x\<in>A --> (\<exists>y. L(y) \<and> (\<exists>p. L(p) \<and> 
		     fun_apply(L,f,x,y) \<and> pair(L,y,x,p) \<and> p \<in> r)))"
  and obase_equals_separation:
     "[| L(A); L(r) |] 
      ==> separation
      (L, \<lambda>x. x\<in>A --> ~(\<exists>y. L(y) & (\<exists>g. L(g) &
	      ordinal(L,y) & (\<exists>my pxr. L(my) & L(pxr) &
	      membership(L,y,my) & pred_set(L,A,x,r,pxr) &
	      order_isomorphism(L,pxr,r,y,my,g)))))"
  and is_recfun_separation:
     --{*for well-founded recursion.  NEEDS RELATIVIZATION*}
     "[| L(A); L(f); L(g); L(a); L(b) |] 
     ==> separation(L, \<lambda>x. x \<in> A --> \<langle>x,a\<rangle> \<in> r \<and> \<langle>x,b\<rangle> \<in> r \<and> f`x \<noteq> g`x)"
  and omap_replacement:
     "[| L(A); L(r) |] 
      ==> strong_replacement(L,
             \<lambda>a z. \<exists>x g mx par. L(x) & L(g) & L(mx) & L(par) &
	     ordinal(L,x) & pair(L,a,x,z) & membership(L,x,mx) & 
	     pred_set(L,A,a,r,par) & order_isomorphism(L,par,r,x,mx,g))"

*)