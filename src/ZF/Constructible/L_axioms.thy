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
apply (rule_tac x=Y in rexI)   
apply (simp_all add: Replace_iff univalent_def, blast) 
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


subsection{*Internalized formulas for some relativized ones*}

subsubsection{*Unordered pairs*}

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

subsubsection{*Ordered pairs*}

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



subsection{*Proving instances of Separation using Reflection!*}

text{*Helps us solve for de Bruijn indices!*}
lemma nth_ConsI: "[|nth(n,l) = x; n \<in> nat|] ==> nth(succ(n), Cons(a,l)) = x"
by simp


lemma Collect_conj_in_DPow:
     "[| {x\<in>A. P(x)} \<in> DPow(A);  {x\<in>A. Q(x)} \<in> DPow(A) |] 
      ==> {x\<in>A. P(x) & Q(x)} \<in> DPow(A)"
by (simp add: Int_in_DPow Collect_Int_Collect_eq [symmetric]) 

lemma Collect_conj_in_DPow_Lset:
     "[|z \<in> Lset(j); {x \<in> Lset(j). P(x)} \<in> DPow(Lset(j))|]
      ==> {x \<in> Lset(j). x \<in> z & P(x)} \<in> DPow(Lset(j))"
apply (frule mem_Lset_imp_subset_Lset)
apply (simp add: Collect_conj_in_DPow Collect_mem_eq 
                 subset_Int_iff2 elem_subset_in_DPow)
done

lemma separation_CollectI:
     "(\<And>z. L(z) ==> L({x \<in> z . P(x)})) ==> separation(L, \<lambda>x. P(x))"
apply (unfold separation_def, clarify) 
apply (rule_tac x="{x\<in>z. P(x)}" in rexI) 
apply simp_all
done

text{*Reduces the original comprehension to the reflected one*}
lemma reflection_imp_L_separation:
      "[| \<forall>x\<in>Lset(j). P(x) <-> Q(x);
          {x \<in> Lset(j) . Q(x)} \<in> DPow(Lset(j)); 
          Ord(j);  z \<in> Lset(j)|] ==> L({x \<in> z . P(x)})"
apply (rule_tac i = "succ(j)" in L_I)
 prefer 2 apply simp
apply (subgoal_tac "{x \<in> z. P(x)} = {x \<in> Lset(j). x \<in> z & (Q(x))}")
 prefer 2
 apply (blast dest: mem_Lset_imp_subset_Lset) 
apply (simp add: Lset_succ Collect_conj_in_DPow_Lset)
done


subsubsection{*Separation for Intersection*}

lemma Inter_Reflects:
     "L_Reflects(?Cl, \<lambda>x. \<forall>y[L]. y\<in>A --> x \<in> y, 
               \<lambda>i x. \<forall>y\<in>Lset(i). y\<in>A --> x \<in> y)"
by fast

lemma Inter_separation:
     "L(A) ==> separation(L, \<lambda>x. \<forall>y[L]. y\<in>A --> x\<in>y)"
apply (rule separation_CollectI) 
apply (rule_tac A="{A,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF Inter_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPowI2) 
apply (rule ball_iff_sats) 
apply (rule imp_iff_sats)
apply (rule_tac [2] i=1 and j=0 and env="[y,x,A]" in mem_iff_sats)
apply (rule_tac i=0 and j=2 in mem_iff_sats)
apply (simp_all add: succ_Un_distrib [symmetric])
done

subsubsection{*Separation for Cartesian Product*}

text{*The @{text simplified} attribute tidies up the reflecting class.*}
theorem upair_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. upair(L,f(x),g(x),h(x)), 
                    \<lambda>i x. upair(**Lset(i),f(x),g(x),h(x)))" 
by (simp add: upair_def, fast) 

theorem pair_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. pair(L,f(x),g(x),h(x)), 
                    \<lambda>i x. pair(**Lset(i),f(x),g(x),h(x)))"
by (simp only: pair_def rex_setclass_is_bex, fast) 

lemma cartprod_Reflects [simplified]:
     "L_Reflects(?Cl, \<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. y\<in>B & pair(L,x,y,z)),
                \<lambda>i z. \<exists>x\<in>Lset(i). x\<in>A & (\<exists>y\<in>Lset(i). y\<in>B & 
                               pair(**Lset(i),x,y,z)))"
by fast

lemma cartprod_separation:
     "[| L(A); L(B) |] 
      ==> separation(L, \<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. y\<in>B & pair(L,x,y,z)))"
apply (rule separation_CollectI) 
apply (rule_tac A="{A,B,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF cartprod_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify) 
apply (rule DPowI2)
apply (rename_tac u)  
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j=2 and env="[x,u,A,B]" in mem_iff_sats, simp_all)
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule mem_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp_all)
apply (rule_tac i=1 and j=0 and k=2 in pair_iff_sats)
apply (simp_all add: succ_Un_distrib [symmetric])
done

subsubsection{*Separation for Image*}

text{*No @{text simplified} here: it simplifies the occurrence of 
      the predicate @{term pair}!*}
lemma image_Reflects:
     "L_Reflects(?Cl, \<lambda>y. \<exists>p[L]. p\<in>r & (\<exists>x[L]. x\<in>A & pair(L,x,y,p)),
           \<lambda>i y. \<exists>p\<in>Lset(i). p\<in>r & (\<exists>x\<in>Lset(i). x\<in>A & pair(**Lset(i),x,y,p)))"
by fast


lemma image_separation:
     "[| L(A); L(r) |] 
      ==> separation(L, \<lambda>y. \<exists>p[L]. p\<in>r & (\<exists>x[L]. x\<in>A & pair(L,x,y,p)))"
apply (rule separation_CollectI) 
apply (rule_tac A="{A,r,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF image_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPowI2)
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac env="[p,y,A,r]" in mem_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp_all)
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule mem_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp_all)
apply (rule pair_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI)
apply (simp_all add: succ_Un_distrib [symmetric])
done


subsubsection{*Separation for Converse*}

lemma converse_Reflects:
     "L_Reflects(?Cl, 
        \<lambda>z. \<exists>p[L]. p\<in>r & (\<exists>x[L]. \<exists>y[L]. pair(L,x,y,p) & pair(L,y,x,z)),
     \<lambda>i z. \<exists>p\<in>Lset(i). p\<in>r & (\<exists>x\<in>Lset(i). \<exists>y\<in>Lset(i). 
                     pair(**Lset(i),x,y,p) & pair(**Lset(i),y,x,z)))"
by fast

lemma converse_separation:
     "L(r) ==> separation(L, 
         \<lambda>z. \<exists>p[L]. p\<in>r & (\<exists>x[L]. \<exists>y[L]. pair(L,x,y,p) & pair(L,y,x,z)))"
apply (rule separation_CollectI) 
apply (rule_tac A="{r,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF converse_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j="2" and env="[p,u,r]" in mem_iff_sats, simp_all)
apply (rule bex_iff_sats) 
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac i=1 and j=0 and k=2 in pair_iff_sats, simp_all)
apply (rule pair_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI)
apply (simp_all add: succ_Un_distrib [symmetric])
done


subsubsection{*Separation for Restriction*}

lemma restrict_Reflects:
     "L_Reflects(?Cl, \<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. pair(L,x,y,z)),
        \<lambda>i z. \<exists>x\<in>Lset(i). x\<in>A & (\<exists>y\<in>Lset(i). pair(**Lset(i),x,y,z)))"
by fast

lemma restrict_separation:
   "L(A) ==> separation(L, \<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. pair(L,x,y,z)))"
apply (rule separation_CollectI) 
apply (rule_tac A="{A,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF restrict_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j="2" and env="[x,u,A]" in mem_iff_sats, simp_all)
apply (rule bex_iff_sats) 
apply (rule_tac i=1 and j=0 and k=2 in pair_iff_sats)
apply (simp_all add: succ_Un_distrib [symmetric])
done


subsubsection{*Separation for Composition*}

lemma comp_Reflects:
     "L_Reflects(?Cl, \<lambda>xz. \<exists>x[L]. \<exists>y[L]. \<exists>z[L]. \<exists>xy[L]. \<exists>yz[L]. 
		  pair(L,x,z,xz) & pair(L,x,y,xy) & pair(L,y,z,yz) & 
                  xy\<in>s & yz\<in>r,
        \<lambda>i xz. \<exists>x\<in>Lset(i). \<exists>y\<in>Lset(i). \<exists>z\<in>Lset(i). \<exists>xy\<in>Lset(i). \<exists>yz\<in>Lset(i). 
		  pair(**Lset(i),x,z,xz) & pair(**Lset(i),x,y,xy) & 
                  pair(**Lset(i),y,z,yz) & xy\<in>s & yz\<in>r)"
by fast

lemma comp_separation:
     "[| L(r); L(s) |]
      ==> separation(L, \<lambda>xz. \<exists>x[L]. \<exists>y[L]. \<exists>z[L]. \<exists>xy[L]. \<exists>yz[L]. 
		  pair(L,x,z,xz) & pair(L,x,y,xy) & pair(L,y,z,yz) & 
                  xy\<in>s & yz\<in>r)"
apply (rule separation_CollectI) 
apply (rule_tac A="{r,s,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF comp_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats)+
apply (rename_tac x y z)  
apply (rule conj_iff_sats)
apply (rule_tac env="[z,y,x,u,r,s]" in pair_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp_all)
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule pair_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp_all)
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule pair_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp_all) 
apply (rule conj_iff_sats)
apply (rule mem_iff_sats) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp) 
apply (rule mem_iff_sats) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI)
apply (simp_all add: succ_Un_distrib [symmetric])
done

subsubsection{*Separation for Predecessors in an Order*}

lemma pred_Reflects:
     "L_Reflects(?Cl, \<lambda>y. \<exists>p[L]. p\<in>r & pair(L,y,x,p),
                    \<lambda>i y. \<exists>p \<in> Lset(i). p\<in>r & pair(**Lset(i),y,x,p))"
by fast

lemma pred_separation:
     "[| L(r); L(x) |] ==> separation(L, \<lambda>y. \<exists>p[L]. p\<in>r & pair(L,y,x,p))"
apply (rule separation_CollectI) 
apply (rule_tac A="{r,x,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF pred_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac env = "[p,u,r,x]" in mem_iff_sats) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp) 
apply (rule pair_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp_all)
apply (simp_all add: succ_Un_distrib [symmetric])
done


subsubsection{*Separation for the Membership Relation*}

lemma Memrel_Reflects:
     "L_Reflects(?Cl, \<lambda>z. \<exists>x[L]. \<exists>y[L]. pair(L,x,y,z) & x \<in> y,
            \<lambda>i z. \<exists>x \<in> Lset(i). \<exists>y \<in> Lset(i). pair(**Lset(i),x,y,z) & x \<in> y)"
by fast

lemma Memrel_separation:
     "separation(L, \<lambda>z. \<exists>x[L]. \<exists>y[L]. pair(L,x,y,z) & x \<in> y)"
apply (rule separation_CollectI) 
apply (rule_tac A="{z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF Memrel_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats)+
apply (rule conj_iff_sats)
apply (rule_tac env = "[y,x,u]" in pair_iff_sats) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI, simp_all) 
apply (rule mem_iff_sats)
apply (blast intro: nth_0 nth_ConsI) 
apply (blast intro: nth_0 nth_ConsI)
apply (simp_all add: succ_Un_distrib [symmetric])
done





end
