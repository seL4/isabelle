header {*The ZF Axioms (Except Separation) in L*}

theory L_axioms = Formula + Relative + Reflection + MetaExists:

text {* The class L satisfies the premises of locale @{text M_triv_axioms} *}

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
apply (rule_tac x="{x,y}" in rexI)  
apply (simp_all add: doubleton_in_L) 
done

lemma Union_ax: "Union_ax(L)"
apply (simp add: Union_ax_def big_union_def, clarify)
apply (rule_tac x="Union(x)" in rexI)  
apply (simp_all add: Union_in_L, auto) 
apply (blast intro: transL) 
done

lemma power_ax: "power_ax(L)"
apply (simp add: power_ax_def powerset_def Relative.subset_def, clarify)
apply (rule_tac x="{y \<in> Pow(x). L(y)}" in rexI)  
apply (simp_all add: LPow_in_L, auto)
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
apply (rule_tac a=x in UN_I)  
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
apply (rule_tac x=Y in rexI)   
apply (simp_all add: Replace_iff univalent_def, blast) 
done

subsection{*Instantiating the locale @{text M_triv_axioms}*}
text{*No instances of Separation yet.*}

lemma Lset_mono_le: "mono_le_subset(Lset)"
by (simp add: mono_le_subset_def le_imp_subset Lset_mono) 

lemma Lset_cont: "cont_Ord(Lset)"
by (simp add: cont_Ord_def Limit_Lset_eq OUnion_def Limit_is_Ord) 

lemmas Pair_in_Lset = Formula.Pair_in_LLimit

lemmas L_nat = Ord_in_L [OF Ord_nat]

theorem M_triv_axioms_L: "PROP M_triv_axioms(L)"
  apply (rule M_triv_axioms.intro)
        apply (erule (1) transL)
       apply (rule nonempty)
      apply (rule upair_ax)
     apply (rule Union_ax)
    apply (rule power_ax)
   apply (rule replacement)
  apply (rule L_nat)
  done

lemmas rall_abs [simp] = M_triv_axioms.rall_abs [OF M_triv_axioms_L]
  and rex_abs [simp] = M_triv_axioms.rex_abs [OF M_triv_axioms_L]
  and ball_iff_equiv = M_triv_axioms.ball_iff_equiv [OF M_triv_axioms_L]
  and M_equalityI = M_triv_axioms.M_equalityI [OF M_triv_axioms_L]
  and empty_abs [simp] = M_triv_axioms.empty_abs [OF M_triv_axioms_L]
  and subset_abs [simp] = M_triv_axioms.subset_abs [OF M_triv_axioms_L]
  and upair_abs [simp] = M_triv_axioms.upair_abs [OF M_triv_axioms_L]
  and upair_in_M_iff [iff] = M_triv_axioms.upair_in_M_iff [OF M_triv_axioms_L]
  and singleton_in_M_iff [iff] = M_triv_axioms.singleton_in_M_iff [OF M_triv_axioms_L]
  and pair_abs [simp] = M_triv_axioms.pair_abs [OF M_triv_axioms_L]
  and pair_in_M_iff [iff] = M_triv_axioms.pair_in_M_iff [OF M_triv_axioms_L]
  and pair_components_in_M = M_triv_axioms.pair_components_in_M [OF M_triv_axioms_L]
  and cartprod_abs [simp] = M_triv_axioms.cartprod_abs [OF M_triv_axioms_L]
  and union_abs [simp] = M_triv_axioms.union_abs [OF M_triv_axioms_L]
  and inter_abs [simp] = M_triv_axioms.inter_abs [OF M_triv_axioms_L]
  and setdiff_abs [simp] = M_triv_axioms.setdiff_abs [OF M_triv_axioms_L]
  and Union_abs [simp] = M_triv_axioms.Union_abs [OF M_triv_axioms_L]
  and Union_closed [intro, simp] = M_triv_axioms.Union_closed [OF M_triv_axioms_L]
  and Un_closed [intro, simp] = M_triv_axioms.Un_closed [OF M_triv_axioms_L]
  and cons_closed [intro, simp] = M_triv_axioms.cons_closed [OF M_triv_axioms_L]
  and successor_abs [simp] = M_triv_axioms.successor_abs [OF M_triv_axioms_L]
  and succ_in_M_iff [iff] = M_triv_axioms.succ_in_M_iff [OF M_triv_axioms_L]
  and separation_closed [intro, simp] = M_triv_axioms.separation_closed [OF M_triv_axioms_L]
  and strong_replacementI = M_triv_axioms.strong_replacementI [OF M_triv_axioms_L]
  and strong_replacement_closed [intro, simp] = M_triv_axioms.strong_replacement_closed [OF M_triv_axioms_L]
  and RepFun_closed [intro, simp] = M_triv_axioms.RepFun_closed [OF M_triv_axioms_L]
  and lam_closed [intro, simp] = M_triv_axioms.lam_closed [OF M_triv_axioms_L]
  and image_abs [simp] = M_triv_axioms.image_abs [OF M_triv_axioms_L]
  and powerset_Pow = M_triv_axioms.powerset_Pow [OF M_triv_axioms_L]
  and powerset_imp_subset_Pow = M_triv_axioms.powerset_imp_subset_Pow [OF M_triv_axioms_L]
  and nat_into_M [intro] = M_triv_axioms.nat_into_M [OF M_triv_axioms_L]
  and nat_case_closed = M_triv_axioms.nat_case_closed [OF M_triv_axioms_L]
  and Inl_in_M_iff [iff] = M_triv_axioms.Inl_in_M_iff [OF M_triv_axioms_L]
  and Inr_in_M_iff [iff] = M_triv_axioms.Inr_in_M_iff [OF M_triv_axioms_L]
  and lt_closed = M_triv_axioms.lt_closed [OF M_triv_axioms_L]
  and transitive_set_abs [simp] = M_triv_axioms.transitive_set_abs [OF M_triv_axioms_L]
  and ordinal_abs [simp] = M_triv_axioms.ordinal_abs [OF M_triv_axioms_L]
  and limit_ordinal_abs [simp] = M_triv_axioms.limit_ordinal_abs [OF M_triv_axioms_L]
  and successor_ordinal_abs [simp] = M_triv_axioms.successor_ordinal_abs [OF M_triv_axioms_L]
  and finite_ordinal_abs = M_triv_axioms.finite_ordinal_abs [OF M_triv_axioms_L]
  and omega_abs [simp] = M_triv_axioms.omega_abs [OF M_triv_axioms_L]
  and number1_abs [simp] = M_triv_axioms.number1_abs [OF M_triv_axioms_L]
  and number2_abs [simp] = M_triv_axioms.number2_abs [OF M_triv_axioms_L]
  and number3_abs [simp] = M_triv_axioms.number3_abs [OF M_triv_axioms_L]


subsection{*Instantiation of the locale @{text reflection}*}

text{*instances of locale constants*}
constdefs
  L_F0 :: "[i=>o,i] => i"
    "L_F0(P,y) == \<mu>b. (\<exists>z. L(z) \<and> P(<y,z>)) --> (\<exists>z\<in>Lset(b). P(<y,z>))"

  L_FF :: "[i=>o,i] => i"
    "L_FF(P)   == \<lambda>a. \<Union>y\<in>Lset(a). L_F0(P,y)"

  L_ClEx :: "[i=>o,i] => o"
    "L_ClEx(P) == \<lambda>a. Limit(a) \<and> normalize(L_FF(P),a) = a"


text{*We must use the meta-existential quantifier; otherwise the reflection
      terms become enormous!*} 
constdefs
  L_Reflects :: "[i=>o,[i,i]=>o] => prop"      ("(3REFLECTS/ [_,/ _])")
    "REFLECTS[P,Q] == (??Cl. Closed_Unbounded(Cl) &
                           (\<forall>a. Cl(a) --> (\<forall>x \<in> Lset(a). P(x) <-> Q(a,x))))"


theorem Triv_reflection:
     "REFLECTS[P, \<lambda>a x. P(x)]"
apply (simp add: L_Reflects_def) 
apply (rule meta_exI) 
apply (rule Closed_Unbounded_Ord) 
done

theorem Not_reflection:
     "REFLECTS[P,Q] ==> REFLECTS[\<lambda>x. ~P(x), \<lambda>a x. ~Q(a,x)]"
apply (unfold L_Reflects_def) 
apply (erule meta_exE) 
apply (rule_tac x=Cl in meta_exI, simp) 
done

theorem And_reflection:
     "[| REFLECTS[P,Q]; REFLECTS[P',Q'] |] 
      ==> REFLECTS[\<lambda>x. P(x) \<and> P'(x), \<lambda>a x. Q(a,x) \<and> Q'(a,x)]"
apply (unfold L_Reflects_def) 
apply (elim meta_exE) 
apply (rule_tac x="\<lambda>a. Cl(a) \<and> Cla(a)" in meta_exI) 
apply (simp add: Closed_Unbounded_Int, blast) 
done

theorem Or_reflection:
     "[| REFLECTS[P,Q]; REFLECTS[P',Q'] |] 
      ==> REFLECTS[\<lambda>x. P(x) \<or> P'(x), \<lambda>a x. Q(a,x) \<or> Q'(a,x)]"
apply (unfold L_Reflects_def) 
apply (elim meta_exE) 
apply (rule_tac x="\<lambda>a. Cl(a) \<and> Cla(a)" in meta_exI) 
apply (simp add: Closed_Unbounded_Int, blast) 
done

theorem Imp_reflection:
     "[| REFLECTS[P,Q]; REFLECTS[P',Q'] |] 
      ==> REFLECTS[\<lambda>x. P(x) --> P'(x), \<lambda>a x. Q(a,x) --> Q'(a,x)]"
apply (unfold L_Reflects_def) 
apply (elim meta_exE) 
apply (rule_tac x="\<lambda>a. Cl(a) \<and> Cla(a)" in meta_exI) 
apply (simp add: Closed_Unbounded_Int, blast) 
done

theorem Iff_reflection:
     "[| REFLECTS[P,Q]; REFLECTS[P',Q'] |] 
      ==> REFLECTS[\<lambda>x. P(x) <-> P'(x), \<lambda>a x. Q(a,x) <-> Q'(a,x)]"
apply (unfold L_Reflects_def) 
apply (elim meta_exE) 
apply (rule_tac x="\<lambda>a. Cl(a) \<and> Cla(a)" in meta_exI) 
apply (simp add: Closed_Unbounded_Int, blast) 
done


theorem Ex_reflection:
     "REFLECTS[\<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      ==> REFLECTS[\<lambda>x. \<exists>z. L(z) \<and> P(x,z), \<lambda>a x. \<exists>z\<in>Lset(a). Q(a,x,z)]"
apply (unfold L_Reflects_def L_ClEx_def L_FF_def L_F0_def L_def) 
apply (elim meta_exE) 
apply (rule meta_exI)
apply (rule reflection.Ex_reflection
  [OF reflection.intro, OF Lset_mono_le Lset_cont Pair_in_Lset],
  assumption+)
done

theorem All_reflection:
     "REFLECTS[\<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      ==> REFLECTS[\<lambda>x. \<forall>z. L(z) --> P(x,z), \<lambda>a x. \<forall>z\<in>Lset(a). Q(a,x,z)]" 
apply (unfold L_Reflects_def L_ClEx_def L_FF_def L_F0_def L_def) 
apply (elim meta_exE) 
apply (rule meta_exI)
apply (rule reflection.All_reflection
  [OF reflection.intro, OF Lset_mono_le Lset_cont Pair_in_Lset],
       assumption+)
done

theorem Rex_reflection:
     "REFLECTS[ \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      ==> REFLECTS[\<lambda>x. \<exists>z[L]. P(x,z), \<lambda>a x. \<exists>z\<in>Lset(a). Q(a,x,z)]"
apply (unfold rex_def) 
apply (intro And_reflection Ex_reflection, assumption)
done

theorem Rall_reflection:
     "REFLECTS[\<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      ==> REFLECTS[\<lambda>x. \<forall>z[L]. P(x,z), \<lambda>a x. \<forall>z\<in>Lset(a). Q(a,x,z)]" 
apply (unfold rall_def) 
apply (intro Imp_reflection All_reflection, assumption)
done

lemmas FOL_reflections = 
        Triv_reflection Not_reflection And_reflection Or_reflection
        Imp_reflection Iff_reflection Ex_reflection All_reflection
        Rex_reflection Rall_reflection

lemma ReflectsD:
     "[|REFLECTS[P,Q]; Ord(i)|] 
      ==> \<exists>j. i<j & (\<forall>x \<in> Lset(j). P(x) <-> Q(j,x))"
apply (unfold L_Reflects_def Closed_Unbounded_def) 
apply (elim meta_exE, clarify) 
apply (blast dest!: UnboundedD) 
done

lemma ReflectsE:
     "[| REFLECTS[P,Q]; Ord(i);
         !!j. [|i<j;  \<forall>x \<in> Lset(j). P(x) <-> Q(j,x)|] ==> R |]
      ==> R"
apply (drule ReflectsD, assumption, blast) 
done

lemma Collect_mem_eq: "{x\<in>A. x\<in>B} = A \<inter> B"
by blast


subsection{*Internalized Formulas for some Set-Theoretic Concepts*}

lemmas setclass_simps = rall_setclass_is_ball rex_setclass_is_bex

subsubsection{*Some numbers to help write de Bruijn indices*}

syntax
    "3" :: i   ("3")
    "4" :: i   ("4")
    "5" :: i   ("5")
    "6" :: i   ("6")
    "7" :: i   ("7")
    "8" :: i   ("8")
    "9" :: i   ("9")

translations
   "3"  == "succ(2)"
   "4"  == "succ(3)"
   "5"  == "succ(4)"
   "6"  == "succ(5)"
   "7"  == "succ(6)"
   "8"  == "succ(7)"
   "9"  == "succ(8)"


subsubsection{*The Empty Set, Internalized*}

constdefs empty_fm :: "i=>i"
    "empty_fm(x) == Forall(Neg(Member(0,succ(x))))"

lemma empty_type [TC]:
     "x \<in> nat ==> empty_fm(x) \<in> formula"
by (simp add: empty_fm_def) 

lemma arity_empty_fm [simp]:
     "x \<in> nat ==> arity(empty_fm(x)) = succ(x)"
by (simp add: empty_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_empty_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, empty_fm(x), env) <-> empty(**A, nth(x,env))"
by (simp add: empty_fm_def empty_def)

lemma empty_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; env \<in> list(A)|]
       ==> empty(**A, x) <-> sats(A, empty_fm(i), env)"
by simp

theorem empty_reflection:
     "REFLECTS[\<lambda>x. empty(L,f(x)), 
               \<lambda>i x. empty(**Lset(i),f(x))]"
apply (simp only: empty_def setclass_simps)
apply (intro FOL_reflections)  
done

text{*Not used.  But maybe useful?*}
lemma Transset_sats_empty_fm_eq_0:
   "[| n \<in> nat; env \<in> list(A); Transset(A)|]
    ==> sats(A, empty_fm(n), env) <-> nth(n,env) = 0"
apply (simp add: empty_fm_def empty_def Transset_def, auto)
apply (case_tac "n < length(env)") 
apply (frule nth_type, assumption+, blast)  
apply (simp_all add: not_lt_iff_le nth_eq_0) 
done


subsubsection{*Unordered Pairs, Internalized*}

constdefs upair_fm :: "[i,i,i]=>i"
    "upair_fm(x,y,z) == 
       And(Member(x,z), 
           And(Member(y,z),
               Forall(Implies(Member(0,succ(z)), 
                              Or(Equal(0,succ(x)), Equal(0,succ(y)))))))"

lemma upair_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> upair_fm(x,y,z) \<in> formula"
by (simp add: upair_fm_def) 

lemma arity_upair_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(upair_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: upair_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_upair_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, upair_fm(x,y,z), env) <-> 
            upair(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: upair_fm_def upair_def)

lemma upair_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> upair(**A, x, y, z) <-> sats(A, upair_fm(i,j,k), env)"
by (simp add: sats_upair_fm)

text{*Useful? At least it refers to "real" unordered pairs*}
lemma sats_upair_fm2 [simp]:
   "[| x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A); Transset(A)|]
    ==> sats(A, upair_fm(x,y,z), env) <-> 
        nth(z,env) = {nth(x,env), nth(y,env)}"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: upair_fm_def Transset_def, auto) 
apply (blast intro: nth_type) 
done

theorem upair_reflection:
     "REFLECTS[\<lambda>x. upair(L,f(x),g(x),h(x)), 
               \<lambda>i x. upair(**Lset(i),f(x),g(x),h(x))]" 
apply (simp add: upair_def)
apply (intro FOL_reflections)  
done

subsubsection{*Ordered pairs, Internalized*}

constdefs pair_fm :: "[i,i,i]=>i"
    "pair_fm(x,y,z) == 
       Exists(And(upair_fm(succ(x),succ(x),0),
              Exists(And(upair_fm(succ(succ(x)),succ(succ(y)),0),
                         upair_fm(1,0,succ(succ(z)))))))"

lemma pair_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> pair_fm(x,y,z) \<in> formula"
by (simp add: pair_fm_def) 

lemma arity_pair_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(pair_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: pair_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_pair_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, pair_fm(x,y,z), env) <-> 
        pair(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: pair_fm_def pair_def)

lemma pair_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> pair(**A, x, y, z) <-> sats(A, pair_fm(i,j,k), env)"
by (simp add: sats_pair_fm)

theorem pair_reflection:
     "REFLECTS[\<lambda>x. pair(L,f(x),g(x),h(x)), 
               \<lambda>i x. pair(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: pair_def setclass_simps)
apply (intro FOL_reflections upair_reflection)  
done


subsubsection{*Binary Unions, Internalized*}

constdefs union_fm :: "[i,i,i]=>i"
    "union_fm(x,y,z) == 
       Forall(Iff(Member(0,succ(z)),
                  Or(Member(0,succ(x)),Member(0,succ(y)))))"

lemma union_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> union_fm(x,y,z) \<in> formula"
by (simp add: union_fm_def) 

lemma arity_union_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(union_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: union_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_union_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, union_fm(x,y,z), env) <-> 
        union(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: union_fm_def union_def)

lemma union_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> union(**A, x, y, z) <-> sats(A, union_fm(i,j,k), env)"
by (simp add: sats_union_fm)

theorem union_reflection:
     "REFLECTS[\<lambda>x. union(L,f(x),g(x),h(x)), 
               \<lambda>i x. union(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: union_def setclass_simps)
apply (intro FOL_reflections)  
done


subsubsection{*Set ``Cons,'' Internalized*}

constdefs cons_fm :: "[i,i,i]=>i"
    "cons_fm(x,y,z) == 
       Exists(And(upair_fm(succ(x),succ(x),0),
                  union_fm(0,succ(y),succ(z))))"


lemma cons_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> cons_fm(x,y,z) \<in> formula"
by (simp add: cons_fm_def) 

lemma arity_cons_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(cons_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: cons_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_cons_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, cons_fm(x,y,z), env) <-> 
        is_cons(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: cons_fm_def is_cons_def)

lemma cons_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_cons(**A, x, y, z) <-> sats(A, cons_fm(i,j,k), env)"
by simp

theorem cons_reflection:
     "REFLECTS[\<lambda>x. is_cons(L,f(x),g(x),h(x)), 
               \<lambda>i x. is_cons(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_cons_def setclass_simps)
apply (intro FOL_reflections upair_reflection union_reflection)  
done


subsubsection{*Successor Function, Internalized*}

constdefs succ_fm :: "[i,i]=>i"
    "succ_fm(x,y) == cons_fm(x,x,y)"

lemma succ_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> succ_fm(x,y) \<in> formula"
by (simp add: succ_fm_def) 

lemma arity_succ_fm [simp]:
     "[| x \<in> nat; y \<in> nat |] 
      ==> arity(succ_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: succ_fm_def)

lemma sats_succ_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, succ_fm(x,y), env) <-> 
        successor(**A, nth(x,env), nth(y,env))"
by (simp add: succ_fm_def successor_def)

lemma successor_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> successor(**A, x, y) <-> sats(A, succ_fm(i,j), env)"
by simp

theorem successor_reflection:
     "REFLECTS[\<lambda>x. successor(L,f(x),g(x)), 
               \<lambda>i x. successor(**Lset(i),f(x),g(x))]"
apply (simp only: successor_def setclass_simps)
apply (intro cons_reflection)  
done


subsubsection{*The Number 1, Internalized*}

(* "number1(M,a) == (\<exists>x[M]. empty(M,x) & successor(M,x,a))" *)
constdefs number1_fm :: "i=>i"
    "number1_fm(a) == Exists(And(empty_fm(0), succ_fm(0,succ(a))))"

lemma number1_type [TC]:
     "x \<in> nat ==> number1_fm(x) \<in> formula"
by (simp add: number1_fm_def) 

lemma arity_number1_fm [simp]:
     "x \<in> nat ==> arity(number1_fm(x)) = succ(x)"
by (simp add: number1_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_number1_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, number1_fm(x), env) <-> number1(**A, nth(x,env))"
by (simp add: number1_fm_def number1_def)

lemma number1_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; env \<in> list(A)|]
       ==> number1(**A, x) <-> sats(A, number1_fm(i), env)"
by simp

theorem number1_reflection:
     "REFLECTS[\<lambda>x. number1(L,f(x)), 
               \<lambda>i x. number1(**Lset(i),f(x))]"
apply (simp only: number1_def setclass_simps)
apply (intro FOL_reflections empty_reflection successor_reflection)
done


subsubsection{*Big Union, Internalized*}

(*  "big_union(M,A,z) == \<forall>x[M]. x \<in> z <-> (\<exists>y[M]. y\<in>A & x \<in> y)" *)
constdefs big_union_fm :: "[i,i]=>i"
    "big_union_fm(A,z) == 
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(A))), Member(1,0)))))"

lemma big_union_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> big_union_fm(x,y) \<in> formula"
by (simp add: big_union_fm_def) 

lemma arity_big_union_fm [simp]:
     "[| x \<in> nat; y \<in> nat |] 
      ==> arity(big_union_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: big_union_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_big_union_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, big_union_fm(x,y), env) <-> 
        big_union(**A, nth(x,env), nth(y,env))"
by (simp add: big_union_fm_def big_union_def)

lemma big_union_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> big_union(**A, x, y) <-> sats(A, big_union_fm(i,j), env)"
by simp

theorem big_union_reflection:
     "REFLECTS[\<lambda>x. big_union(L,f(x),g(x)), 
               \<lambda>i x. big_union(**Lset(i),f(x),g(x))]"
apply (simp only: big_union_def setclass_simps)
apply (intro FOL_reflections)  
done


subsubsection{*Variants of Satisfaction Definitions for Ordinals, etc.*}

text{*Differs from the one in Formula by using "ordinal" rather than "Ord"*}


lemma sats_subset_fm':
   "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, subset_fm(x,y), env) <-> subset(**A, nth(x,env), nth(y,env))" 
by (simp add: subset_fm_def Relative.subset_def) 

theorem subset_reflection:
     "REFLECTS[\<lambda>x. subset(L,f(x),g(x)), 
               \<lambda>i x. subset(**Lset(i),f(x),g(x))]" 
apply (simp only: Relative.subset_def setclass_simps)
apply (intro FOL_reflections)  
done

lemma sats_transset_fm':
   "[|x \<in> nat; env \<in> list(A)|]
    ==> sats(A, transset_fm(x), env) <-> transitive_set(**A, nth(x,env))"
by (simp add: sats_subset_fm' transset_fm_def transitive_set_def) 

theorem transitive_set_reflection:
     "REFLECTS[\<lambda>x. transitive_set(L,f(x)),
               \<lambda>i x. transitive_set(**Lset(i),f(x))]"
apply (simp only: transitive_set_def setclass_simps)
apply (intro FOL_reflections subset_reflection)  
done

lemma sats_ordinal_fm':
   "[|x \<in> nat; env \<in> list(A)|]
    ==> sats(A, ordinal_fm(x), env) <-> ordinal(**A,nth(x,env))"
by (simp add: sats_transset_fm' ordinal_fm_def ordinal_def)

lemma ordinal_iff_sats:
      "[| nth(i,env) = x;  i \<in> nat; env \<in> list(A)|]
       ==> ordinal(**A, x) <-> sats(A, ordinal_fm(i), env)"
by (simp add: sats_ordinal_fm')

theorem ordinal_reflection:
     "REFLECTS[\<lambda>x. ordinal(L,f(x)), \<lambda>i x. ordinal(**Lset(i),f(x))]"
apply (simp only: ordinal_def setclass_simps)
apply (intro FOL_reflections transitive_set_reflection)  
done


subsubsection{*Membership Relation, Internalized*}

constdefs Memrel_fm :: "[i,i]=>i"
    "Memrel_fm(A,r) == 
       Forall(Iff(Member(0,succ(r)),
                  Exists(And(Member(0,succ(succ(A))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
                                        And(Member(1,0),
                                            pair_fm(1,0,2))))))))"

lemma Memrel_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> Memrel_fm(x,y) \<in> formula"
by (simp add: Memrel_fm_def) 

lemma arity_Memrel_fm [simp]:
     "[| x \<in> nat; y \<in> nat |] 
      ==> arity(Memrel_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: Memrel_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_Memrel_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, Memrel_fm(x,y), env) <-> 
        membership(**A, nth(x,env), nth(y,env))"
by (simp add: Memrel_fm_def membership_def)

lemma Memrel_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> membership(**A, x, y) <-> sats(A, Memrel_fm(i,j), env)"
by simp

theorem membership_reflection:
     "REFLECTS[\<lambda>x. membership(L,f(x),g(x)), 
               \<lambda>i x. membership(**Lset(i),f(x),g(x))]"
apply (simp only: membership_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done

subsubsection{*Predecessor Set, Internalized*}

constdefs pred_set_fm :: "[i,i,i,i]=>i"
    "pred_set_fm(A,x,r,B) == 
       Forall(Iff(Member(0,succ(B)),
                  Exists(And(Member(0,succ(succ(r))),
                             And(Member(1,succ(succ(A))),
                                 pair_fm(1,succ(succ(x)),0))))))"


lemma pred_set_type [TC]:
     "[| A \<in> nat; x \<in> nat; r \<in> nat; B \<in> nat |] 
      ==> pred_set_fm(A,x,r,B) \<in> formula"
by (simp add: pred_set_fm_def) 

lemma arity_pred_set_fm [simp]:
   "[| A \<in> nat; x \<in> nat; r \<in> nat; B \<in> nat |] 
    ==> arity(pred_set_fm(A,x,r,B)) = succ(A) \<union> succ(x) \<union> succ(r) \<union> succ(B)"
by (simp add: pred_set_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_pred_set_fm [simp]:
   "[| U \<in> nat; x \<in> nat; r \<in> nat; B \<in> nat; env \<in> list(A)|]
    ==> sats(A, pred_set_fm(U,x,r,B), env) <-> 
        pred_set(**A, nth(U,env), nth(x,env), nth(r,env), nth(B,env))"
by (simp add: pred_set_fm_def pred_set_def)

lemma pred_set_iff_sats:
      "[| nth(i,env) = U; nth(j,env) = x; nth(k,env) = r; nth(l,env) = B; 
          i \<in> nat; j \<in> nat; k \<in> nat; l \<in> nat; env \<in> list(A)|]
       ==> pred_set(**A,U,x,r,B) <-> sats(A, pred_set_fm(i,j,k,l), env)"
by (simp add: sats_pred_set_fm)

theorem pred_set_reflection:
     "REFLECTS[\<lambda>x. pred_set(L,f(x),g(x),h(x),b(x)), 
               \<lambda>i x. pred_set(**Lset(i),f(x),g(x),h(x),b(x))]" 
apply (simp only: pred_set_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done



subsubsection{*Domain of a Relation, Internalized*}

(* "is_domain(M,r,z) == 
	\<forall>x[M]. (x \<in> z <-> (\<exists>w[M]. w\<in>r & (\<exists>y[M]. pair(M,x,y,w))))" *)
constdefs domain_fm :: "[i,i]=>i"
    "domain_fm(r,z) == 
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(pair_fm(2,0,1))))))"

lemma domain_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> domain_fm(x,y) \<in> formula"
by (simp add: domain_fm_def) 

lemma arity_domain_fm [simp]:
     "[| x \<in> nat; y \<in> nat |] 
      ==> arity(domain_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: domain_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_domain_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, domain_fm(x,y), env) <-> 
        is_domain(**A, nth(x,env), nth(y,env))"
by (simp add: domain_fm_def is_domain_def)

lemma domain_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_domain(**A, x, y) <-> sats(A, domain_fm(i,j), env)"
by simp

theorem domain_reflection:
     "REFLECTS[\<lambda>x. is_domain(L,f(x),g(x)), 
               \<lambda>i x. is_domain(**Lset(i),f(x),g(x))]"
apply (simp only: is_domain_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done


subsubsection{*Range of a Relation, Internalized*}

(* "is_range(M,r,z) == 
	\<forall>y[M]. (y \<in> z <-> (\<exists>w[M]. w\<in>r & (\<exists>x[M]. pair(M,x,y,w))))" *)
constdefs range_fm :: "[i,i]=>i"
    "range_fm(r,z) == 
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(pair_fm(0,2,1))))))"

lemma range_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> range_fm(x,y) \<in> formula"
by (simp add: range_fm_def) 

lemma arity_range_fm [simp]:
     "[| x \<in> nat; y \<in> nat |] 
      ==> arity(range_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: range_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_range_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, range_fm(x,y), env) <-> 
        is_range(**A, nth(x,env), nth(y,env))"
by (simp add: range_fm_def is_range_def)

lemma range_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_range(**A, x, y) <-> sats(A, range_fm(i,j), env)"
by simp

theorem range_reflection:
     "REFLECTS[\<lambda>x. is_range(L,f(x),g(x)), 
               \<lambda>i x. is_range(**Lset(i),f(x),g(x))]"
apply (simp only: is_range_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done

 
subsubsection{*Field of a Relation, Internalized*}

(* "is_field(M,r,z) == 
	\<exists>dr[M]. is_domain(M,r,dr) & 
            (\<exists>rr[M]. is_range(M,r,rr) & union(M,dr,rr,z))" *)
constdefs field_fm :: "[i,i]=>i"
    "field_fm(r,z) == 
       Exists(And(domain_fm(succ(r),0), 
              Exists(And(range_fm(succ(succ(r)),0), 
                         union_fm(1,0,succ(succ(z)))))))"

lemma field_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> field_fm(x,y) \<in> formula"
by (simp add: field_fm_def) 

lemma arity_field_fm [simp]:
     "[| x \<in> nat; y \<in> nat |] 
      ==> arity(field_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: field_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_field_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, field_fm(x,y), env) <-> 
        is_field(**A, nth(x,env), nth(y,env))"
by (simp add: field_fm_def is_field_def)

lemma field_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_field(**A, x, y) <-> sats(A, field_fm(i,j), env)"
by simp

theorem field_reflection:
     "REFLECTS[\<lambda>x. is_field(L,f(x),g(x)), 
               \<lambda>i x. is_field(**Lset(i),f(x),g(x))]"
apply (simp only: is_field_def setclass_simps)
apply (intro FOL_reflections domain_reflection range_reflection
             union_reflection)
done


subsubsection{*Image under a Relation, Internalized*}

(* "image(M,r,A,z) == 
        \<forall>y[M]. (y \<in> z <-> (\<exists>w[M]. w\<in>r & (\<exists>x[M]. x\<in>A & pair(M,x,y,w))))" *)
constdefs image_fm :: "[i,i,i]=>i"
    "image_fm(r,A,z) == 
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
	 			        pair_fm(0,2,1)))))))"

lemma image_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> image_fm(x,y,z) \<in> formula"
by (simp add: image_fm_def) 

lemma arity_image_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(image_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: image_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_image_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, image_fm(x,y,z), env) <-> 
        image(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: image_fm_def Relative.image_def)

lemma image_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> image(**A, x, y, z) <-> sats(A, image_fm(i,j,k), env)"
by (simp add: sats_image_fm)

theorem image_reflection:
     "REFLECTS[\<lambda>x. image(L,f(x),g(x),h(x)), 
               \<lambda>i x. image(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: Relative.image_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done


subsubsection{*Pre-Image under a Relation, Internalized*}

(* "pre_image(M,r,A,z) == 
	\<forall>x[M]. x \<in> z <-> (\<exists>w[M]. w\<in>r & (\<exists>y[M]. y\<in>A & pair(M,x,y,w)))" *)
constdefs pre_image_fm :: "[i,i,i]=>i"
    "pre_image_fm(r,A,z) == 
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
	 			        pair_fm(2,0,1)))))))"

lemma pre_image_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> pre_image_fm(x,y,z) \<in> formula"
by (simp add: pre_image_fm_def) 

lemma arity_pre_image_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(pre_image_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: pre_image_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_pre_image_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, pre_image_fm(x,y,z), env) <-> 
        pre_image(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: pre_image_fm_def Relative.pre_image_def)

lemma pre_image_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> pre_image(**A, x, y, z) <-> sats(A, pre_image_fm(i,j,k), env)"
by (simp add: sats_pre_image_fm)

theorem pre_image_reflection:
     "REFLECTS[\<lambda>x. pre_image(L,f(x),g(x),h(x)), 
               \<lambda>i x. pre_image(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: Relative.pre_image_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done


subsubsection{*Function Application, Internalized*}

(* "fun_apply(M,f,x,y) == 
        (\<exists>xs[M]. \<exists>fxs[M]. 
         upair(M,x,x,xs) & image(M,f,xs,fxs) & big_union(M,fxs,y))" *)
constdefs fun_apply_fm :: "[i,i,i]=>i"
    "fun_apply_fm(f,x,y) == 
       Exists(Exists(And(upair_fm(succ(succ(x)), succ(succ(x)), 1),
                         And(image_fm(succ(succ(f)), 1, 0), 
                             big_union_fm(0,succ(succ(y)))))))"

lemma fun_apply_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> fun_apply_fm(x,y,z) \<in> formula"
by (simp add: fun_apply_fm_def) 

lemma arity_fun_apply_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(fun_apply_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: fun_apply_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_fun_apply_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, fun_apply_fm(x,y,z), env) <-> 
        fun_apply(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: fun_apply_fm_def fun_apply_def)

lemma fun_apply_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> fun_apply(**A, x, y, z) <-> sats(A, fun_apply_fm(i,j,k), env)"
by simp

theorem fun_apply_reflection:
     "REFLECTS[\<lambda>x. fun_apply(L,f(x),g(x),h(x)), 
               \<lambda>i x. fun_apply(**Lset(i),f(x),g(x),h(x))]" 
apply (simp only: fun_apply_def setclass_simps)
apply (intro FOL_reflections upair_reflection image_reflection
             big_union_reflection)  
done


subsubsection{*The Concept of Relation, Internalized*}

(* "is_relation(M,r) == 
        (\<forall>z[M]. z\<in>r --> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,z)))" *)
constdefs relation_fm :: "i=>i"
    "relation_fm(r) == 
       Forall(Implies(Member(0,succ(r)), Exists(Exists(pair_fm(1,0,2)))))"

lemma relation_type [TC]:
     "[| x \<in> nat |] ==> relation_fm(x) \<in> formula"
by (simp add: relation_fm_def) 

lemma arity_relation_fm [simp]:
     "x \<in> nat ==> arity(relation_fm(x)) = succ(x)"
by (simp add: relation_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_relation_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, relation_fm(x), env) <-> is_relation(**A, nth(x,env))"
by (simp add: relation_fm_def is_relation_def)

lemma relation_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; env \<in> list(A)|]
       ==> is_relation(**A, x) <-> sats(A, relation_fm(i), env)"
by simp

theorem is_relation_reflection:
     "REFLECTS[\<lambda>x. is_relation(L,f(x)), 
               \<lambda>i x. is_relation(**Lset(i),f(x))]"
apply (simp only: is_relation_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done


subsubsection{*The Concept of Function, Internalized*}

(* "is_function(M,r) == 
	\<forall>x[M]. \<forall>y[M]. \<forall>y'[M]. \<forall>p[M]. \<forall>p'[M]. 
           pair(M,x,y,p) --> pair(M,x,y',p') --> p\<in>r --> p'\<in>r --> y=y'" *)
constdefs function_fm :: "i=>i"
    "function_fm(r) == 
       Forall(Forall(Forall(Forall(Forall(
         Implies(pair_fm(4,3,1),
                 Implies(pair_fm(4,2,0),
                         Implies(Member(1,r#+5),
                                 Implies(Member(0,r#+5), Equal(3,2))))))))))"

lemma function_type [TC]:
     "[| x \<in> nat |] ==> function_fm(x) \<in> formula"
by (simp add: function_fm_def) 

lemma arity_function_fm [simp]:
     "x \<in> nat ==> arity(function_fm(x)) = succ(x)"
by (simp add: function_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_function_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, function_fm(x), env) <-> is_function(**A, nth(x,env))"
by (simp add: function_fm_def is_function_def)

lemma function_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; env \<in> list(A)|]
       ==> is_function(**A, x) <-> sats(A, function_fm(i), env)"
by simp

theorem is_function_reflection:
     "REFLECTS[\<lambda>x. is_function(L,f(x)), 
               \<lambda>i x. is_function(**Lset(i),f(x))]"
apply (simp only: is_function_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done


subsubsection{*Typed Functions, Internalized*}

(* "typed_function(M,A,B,r) == 
        is_function(M,r) & is_relation(M,r) & is_domain(M,r,A) &
        (\<forall>u[M]. u\<in>r --> (\<forall>x[M]. \<forall>y[M]. pair(M,x,y,u) --> y\<in>B))" *)

constdefs typed_function_fm :: "[i,i,i]=>i"
    "typed_function_fm(A,B,r) == 
       And(function_fm(r),
         And(relation_fm(r),
           And(domain_fm(r,A),
             Forall(Implies(Member(0,succ(r)),
                  Forall(Forall(Implies(pair_fm(1,0,2),Member(0,B#+3)))))))))"

lemma typed_function_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> typed_function_fm(x,y,z) \<in> formula"
by (simp add: typed_function_fm_def) 

lemma arity_typed_function_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(typed_function_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: typed_function_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_typed_function_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, typed_function_fm(x,y,z), env) <-> 
        typed_function(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: typed_function_fm_def typed_function_def)

lemma typed_function_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> typed_function(**A, x, y, z) <-> sats(A, typed_function_fm(i,j,k), env)"
by simp

lemmas function_reflections = 
        empty_reflection number1_reflection
	upair_reflection pair_reflection union_reflection
	big_union_reflection cons_reflection successor_reflection 
        fun_apply_reflection subset_reflection
	transitive_set_reflection membership_reflection
	pred_set_reflection domain_reflection range_reflection field_reflection
        image_reflection pre_image_reflection
	is_relation_reflection is_function_reflection

lemmas function_iff_sats = 
        empty_iff_sats number1_iff_sats 
	upair_iff_sats pair_iff_sats union_iff_sats
	cons_iff_sats successor_iff_sats
        fun_apply_iff_sats  Memrel_iff_sats
	pred_set_iff_sats domain_iff_sats range_iff_sats field_iff_sats
        image_iff_sats pre_image_iff_sats 
	relation_iff_sats function_iff_sats


theorem typed_function_reflection:
     "REFLECTS[\<lambda>x. typed_function(L,f(x),g(x),h(x)), 
               \<lambda>i x. typed_function(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: typed_function_def setclass_simps)
apply (intro FOL_reflections function_reflections)  
done


subsubsection{*Composition of Relations, Internalized*}

(* "composition(M,r,s,t) == 
        \<forall>p[M]. p \<in> t <-> 
               (\<exists>x[M]. \<exists>y[M]. \<exists>z[M]. \<exists>xy[M]. \<exists>yz[M]. 
                pair(M,x,z,p) & pair(M,x,y,xy) & pair(M,y,z,yz) & 
                xy \<in> s & yz \<in> r)" *)
constdefs composition_fm :: "[i,i,i]=>i"
  "composition_fm(r,s,t) == 
     Forall(Iff(Member(0,succ(t)),
             Exists(Exists(Exists(Exists(Exists( 
              And(pair_fm(4,2,5),
               And(pair_fm(4,3,1),
                And(pair_fm(3,2,0),
                 And(Member(1,s#+6), Member(0,r#+6))))))))))))"

lemma composition_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> composition_fm(x,y,z) \<in> formula"
by (simp add: composition_fm_def) 

lemma arity_composition_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(composition_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: composition_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_composition_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, composition_fm(x,y,z), env) <-> 
        composition(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: composition_fm_def composition_def)

lemma composition_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> composition(**A, x, y, z) <-> sats(A, composition_fm(i,j,k), env)"
by simp

theorem composition_reflection:
     "REFLECTS[\<lambda>x. composition(L,f(x),g(x),h(x)), 
               \<lambda>i x. composition(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: composition_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done


subsubsection{*Injections, Internalized*}

(* "injection(M,A,B,f) == 
	typed_function(M,A,B,f) &
        (\<forall>x[M]. \<forall>x'[M]. \<forall>y[M]. \<forall>p[M]. \<forall>p'[M]. 
          pair(M,x,y,p) --> pair(M,x',y,p') --> p\<in>f --> p'\<in>f --> x=x')" *)
constdefs injection_fm :: "[i,i,i]=>i"
 "injection_fm(A,B,f) == 
    And(typed_function_fm(A,B,f),
       Forall(Forall(Forall(Forall(Forall(
         Implies(pair_fm(4,2,1),
                 Implies(pair_fm(3,2,0),
                         Implies(Member(1,f#+5),
                                 Implies(Member(0,f#+5), Equal(4,3)))))))))))"


lemma injection_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> injection_fm(x,y,z) \<in> formula"
by (simp add: injection_fm_def) 

lemma arity_injection_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(injection_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: injection_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_injection_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, injection_fm(x,y,z), env) <-> 
        injection(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: injection_fm_def injection_def)

lemma injection_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> injection(**A, x, y, z) <-> sats(A, injection_fm(i,j,k), env)"
by simp

theorem injection_reflection:
     "REFLECTS[\<lambda>x. injection(L,f(x),g(x),h(x)), 
               \<lambda>i x. injection(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: injection_def setclass_simps)
apply (intro FOL_reflections function_reflections typed_function_reflection)  
done


subsubsection{*Surjections, Internalized*}

(*  surjection :: "[i=>o,i,i,i] => o"
    "surjection(M,A,B,f) == 
        typed_function(M,A,B,f) &
        (\<forall>y[M]. y\<in>B --> (\<exists>x[M]. x\<in>A & fun_apply(M,f,x,y)))" *)
constdefs surjection_fm :: "[i,i,i]=>i"
 "surjection_fm(A,B,f) == 
    And(typed_function_fm(A,B,f),
       Forall(Implies(Member(0,succ(B)),
                      Exists(And(Member(0,succ(succ(A))),
                                 fun_apply_fm(succ(succ(f)),0,1))))))"

lemma surjection_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> surjection_fm(x,y,z) \<in> formula"
by (simp add: surjection_fm_def) 

lemma arity_surjection_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(surjection_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: surjection_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_surjection_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, surjection_fm(x,y,z), env) <-> 
        surjection(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: surjection_fm_def surjection_def)

lemma surjection_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> surjection(**A, x, y, z) <-> sats(A, surjection_fm(i,j,k), env)"
by simp

theorem surjection_reflection:
     "REFLECTS[\<lambda>x. surjection(L,f(x),g(x),h(x)), 
               \<lambda>i x. surjection(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: surjection_def setclass_simps)
apply (intro FOL_reflections function_reflections typed_function_reflection)  
done



subsubsection{*Bijections, Internalized*}

(*   bijection :: "[i=>o,i,i,i] => o"
    "bijection(M,A,B,f) == injection(M,A,B,f) & surjection(M,A,B,f)" *)
constdefs bijection_fm :: "[i,i,i]=>i"
 "bijection_fm(A,B,f) == And(injection_fm(A,B,f), surjection_fm(A,B,f))"

lemma bijection_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> bijection_fm(x,y,z) \<in> formula"
by (simp add: bijection_fm_def) 

lemma arity_bijection_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(bijection_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: bijection_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_bijection_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, bijection_fm(x,y,z), env) <-> 
        bijection(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: bijection_fm_def bijection_def)

lemma bijection_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> bijection(**A, x, y, z) <-> sats(A, bijection_fm(i,j,k), env)"
by simp

theorem bijection_reflection:
     "REFLECTS[\<lambda>x. bijection(L,f(x),g(x),h(x)), 
               \<lambda>i x. bijection(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: bijection_def setclass_simps)
apply (intro And_reflection injection_reflection surjection_reflection)  
done


subsubsection{*Restriction of a Relation, Internalized*}


(* "restriction(M,r,A,z) == 
	\<forall>x[M]. x \<in> z <-> (x \<in> r & (\<exists>u[M]. u\<in>A & (\<exists>v[M]. pair(M,u,v,x))))" *)
constdefs restriction_fm :: "[i,i,i]=>i"
    "restriction_fm(r,A,z) == 
       Forall(Iff(Member(0,succ(z)),
                  And(Member(0,succ(r)),
                      Exists(And(Member(0,succ(succ(A))),
                                 Exists(pair_fm(1,0,2)))))))"

lemma restriction_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> restriction_fm(x,y,z) \<in> formula"
by (simp add: restriction_fm_def) 

lemma arity_restriction_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> arity(restriction_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: restriction_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_restriction_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, restriction_fm(x,y,z), env) <-> 
        restriction(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: restriction_fm_def restriction_def)

lemma restriction_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> restriction(**A, x, y, z) <-> sats(A, restriction_fm(i,j,k), env)"
by simp

theorem restriction_reflection:
     "REFLECTS[\<lambda>x. restriction(L,f(x),g(x),h(x)), 
               \<lambda>i x. restriction(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: restriction_def setclass_simps)
apply (intro FOL_reflections pair_reflection)  
done

subsubsection{*Order-Isomorphisms, Internalized*}

(*  order_isomorphism :: "[i=>o,i,i,i,i,i] => o"
   "order_isomorphism(M,A,r,B,s,f) == 
        bijection(M,A,B,f) & 
        (\<forall>x[M]. x\<in>A --> (\<forall>y[M]. y\<in>A -->
          (\<forall>p[M]. \<forall>fx[M]. \<forall>fy[M]. \<forall>q[M].
            pair(M,x,y,p) --> fun_apply(M,f,x,fx) --> fun_apply(M,f,y,fy) --> 
            pair(M,fx,fy,q) --> (p\<in>r <-> q\<in>s))))"
  *)

constdefs order_isomorphism_fm :: "[i,i,i,i,i]=>i"
 "order_isomorphism_fm(A,r,B,s,f) == 
   And(bijection_fm(A,B,f), 
     Forall(Implies(Member(0,succ(A)),
       Forall(Implies(Member(0,succ(succ(A))),
         Forall(Forall(Forall(Forall(
           Implies(pair_fm(5,4,3),
             Implies(fun_apply_fm(f#+6,5,2),
               Implies(fun_apply_fm(f#+6,4,1),
                 Implies(pair_fm(2,1,0), 
                   Iff(Member(3,r#+6), Member(0,s#+6)))))))))))))))"

lemma order_isomorphism_type [TC]:
     "[| A \<in> nat; r \<in> nat; B \<in> nat; s \<in> nat; f \<in> nat |]  
      ==> order_isomorphism_fm(A,r,B,s,f) \<in> formula"
by (simp add: order_isomorphism_fm_def) 

lemma arity_order_isomorphism_fm [simp]:
     "[| A \<in> nat; r \<in> nat; B \<in> nat; s \<in> nat; f \<in> nat |] 
      ==> arity(order_isomorphism_fm(A,r,B,s,f)) = 
          succ(A) \<union> succ(r) \<union> succ(B) \<union> succ(s) \<union> succ(f)" 
by (simp add: order_isomorphism_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_order_isomorphism_fm [simp]:
   "[| U \<in> nat; r \<in> nat; B \<in> nat; s \<in> nat; f \<in> nat; env \<in> list(A)|]
    ==> sats(A, order_isomorphism_fm(U,r,B,s,f), env) <-> 
        order_isomorphism(**A, nth(U,env), nth(r,env), nth(B,env), 
                               nth(s,env), nth(f,env))"
by (simp add: order_isomorphism_fm_def order_isomorphism_def)

lemma order_isomorphism_iff_sats:
  "[| nth(i,env) = U; nth(j,env) = r; nth(k,env) = B; nth(j',env) = s; 
      nth(k',env) = f; 
      i \<in> nat; j \<in> nat; k \<in> nat; j' \<in> nat; k' \<in> nat; env \<in> list(A)|]
   ==> order_isomorphism(**A,U,r,B,s,f) <-> 
       sats(A, order_isomorphism_fm(i,j,k,j',k'), env)" 
by simp

theorem order_isomorphism_reflection:
     "REFLECTS[\<lambda>x. order_isomorphism(L,f(x),g(x),h(x),g'(x),h'(x)), 
               \<lambda>i x. order_isomorphism(**Lset(i),f(x),g(x),h(x),g'(x),h'(x))]"
apply (simp only: order_isomorphism_def setclass_simps)
apply (intro FOL_reflections function_reflections bijection_reflection)  
done

subsubsection{*Limit Ordinals, Internalized*}

text{*A limit ordinal is a non-empty, successor-closed ordinal*}

(* "limit_ordinal(M,a) == 
	ordinal(M,a) & ~ empty(M,a) & 
        (\<forall>x[M]. x\<in>a --> (\<exists>y[M]. y\<in>a & successor(M,x,y)))" *)

constdefs limit_ordinal_fm :: "i=>i"
    "limit_ordinal_fm(x) == 
        And(ordinal_fm(x),
            And(Neg(empty_fm(x)),
	        Forall(Implies(Member(0,succ(x)),
                               Exists(And(Member(0,succ(succ(x))),
                                          succ_fm(1,0)))))))"

lemma limit_ordinal_type [TC]:
     "x \<in> nat ==> limit_ordinal_fm(x) \<in> formula"
by (simp add: limit_ordinal_fm_def) 

lemma arity_limit_ordinal_fm [simp]:
     "x \<in> nat ==> arity(limit_ordinal_fm(x)) = succ(x)"
by (simp add: limit_ordinal_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_limit_ordinal_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, limit_ordinal_fm(x), env) <-> limit_ordinal(**A, nth(x,env))"
by (simp add: limit_ordinal_fm_def limit_ordinal_def sats_ordinal_fm')

lemma limit_ordinal_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; env \<in> list(A)|]
       ==> limit_ordinal(**A, x) <-> sats(A, limit_ordinal_fm(i), env)"
by simp

theorem limit_ordinal_reflection:
     "REFLECTS[\<lambda>x. limit_ordinal(L,f(x)), 
               \<lambda>i x. limit_ordinal(**Lset(i),f(x))]"
apply (simp only: limit_ordinal_def setclass_simps)
apply (intro FOL_reflections ordinal_reflection 
             empty_reflection successor_reflection)  
done

subsubsection{*Omega: The Set of Natural Numbers*}

(* omega(M,a) == limit_ordinal(M,a) & (\<forall>x[M]. x\<in>a --> ~ limit_ordinal(M,x)) *)
constdefs omega_fm :: "i=>i"
    "omega_fm(x) == 
       And(limit_ordinal_fm(x),
           Forall(Implies(Member(0,succ(x)),
                          Neg(limit_ordinal_fm(0)))))"

lemma omega_type [TC]:
     "x \<in> nat ==> omega_fm(x) \<in> formula"
by (simp add: omega_fm_def) 

lemma arity_omega_fm [simp]:
     "x \<in> nat ==> arity(omega_fm(x)) = succ(x)"
by (simp add: omega_fm_def succ_Un_distrib [symmetric] Un_ac) 

lemma sats_omega_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, omega_fm(x), env) <-> omega(**A, nth(x,env))"
by (simp add: omega_fm_def omega_def)

lemma omega_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; env \<in> list(A)|]
       ==> omega(**A, x) <-> sats(A, omega_fm(i), env)"
by simp

theorem omega_reflection:
     "REFLECTS[\<lambda>x. omega(L,f(x)), 
               \<lambda>i x. omega(**Lset(i),f(x))]"
apply (simp only: omega_def setclass_simps)
apply (intro FOL_reflections limit_ordinal_reflection)  
done


lemmas fun_plus_reflections =
        typed_function_reflection composition_reflection
        injection_reflection surjection_reflection
        bijection_reflection restriction_reflection
        order_isomorphism_reflection
        ordinal_reflection limit_ordinal_reflection omega_reflection

lemmas fun_plus_iff_sats = 
	typed_function_iff_sats composition_iff_sats
        injection_iff_sats surjection_iff_sats 
        bijection_iff_sats restriction_iff_sats 
        order_isomorphism_iff_sats
        ordinal_iff_sats limit_ordinal_iff_sats omega_iff_sats

end
