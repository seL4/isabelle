header {*The Class L Satisfies the ZF Axioms*}

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
declare strong_replacementI
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

text{*The @{text simplified} attribute tidies up the reflecting class.*}
theorem upair_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. upair(L,f(x),g(x),h(x)), 
                    \<lambda>i x. upair(**Lset(i),f(x),g(x),h(x)))" 
by (simp add: upair_def, fast) 

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

theorem pair_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. pair(L,f(x),g(x),h(x)), 
                    \<lambda>i x. pair(**Lset(i),f(x),g(x),h(x)))"
by (simp only: pair_def setclass_simps, fast) 


subsubsection{*Binary Unions*}

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

theorem union_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. union(L,f(x),g(x),h(x)), 
                    \<lambda>i x. union(**Lset(i),f(x),g(x),h(x)))" 
by (simp add: union_def, fast) 


subsubsection{*`Cons' for sets*}

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

theorem cons_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. is_cons(L,f(x),g(x),h(x)), 
                    \<lambda>i x. is_cons(**Lset(i),f(x),g(x),h(x)))"
by (simp only: is_cons_def setclass_simps, fast)


subsubsection{*Function Applications*}

constdefs fun_apply_fm :: "[i,i,i]=>i"
    "fun_apply_fm(f,x,y) == 
       Forall(Iff(Exists(And(Member(0,succ(succ(f))),
                             pair_fm(succ(succ(x)), 1, 0))),
                  Equal(succ(y),0)))"

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

theorem fun_apply_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. fun_apply(L,f(x),g(x),h(x)), 
                    \<lambda>i x. fun_apply(**Lset(i),f(x),g(x),h(x)))" 
by (simp only: fun_apply_def setclass_simps, fast)


subsubsection{*Variants of Satisfaction Definitions for Ordinals, etc.*}

text{*Differs from the one in Formula by using "ordinal" rather than "Ord"*}


lemma sats_subset_fm':
   "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, subset_fm(x,y), env) <-> subset(**A, nth(x,env), nth(y,env))" 
by (simp add: subset_fm_def subset_def) 

theorem subset_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. subset(L,f(x),g(x)), 
                    \<lambda>i x. subset(**Lset(i),f(x),g(x)))" 
by (simp add: subset_def, fast) 

lemma sats_transset_fm':
   "[|x \<in> nat; env \<in> list(A)|]
    ==> sats(A, transset_fm(x), env) <-> transitive_set(**A, nth(x,env))"
by (simp add: sats_subset_fm' transset_fm_def transitive_set_def) 

theorem transitive_set_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. transitive_set(L,f(x)),
                    \<lambda>i x. transitive_set(**Lset(i),f(x)))"
by (simp only: transitive_set_def setclass_simps, fast)

lemma sats_ordinal_fm':
   "[|x \<in> nat; env \<in> list(A)|]
    ==> sats(A, ordinal_fm(x), env) <-> ordinal(**A,nth(x,env))"
by (simp add: sats_transset_fm' ordinal_fm_def ordinal_def)

lemma ordinal_iff_sats:
      "[| nth(i,env) = x;  i \<in> nat; env \<in> list(A)|]
       ==> ordinal(**A, x) <-> sats(A, ordinal_fm(i), env)"
by (simp add: sats_ordinal_fm')

theorem ordinal_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. ordinal(L,f(x)),
                    \<lambda>i x. ordinal(**Lset(i),f(x)))"
by (simp only: ordinal_def setclass_simps, fast)


subsubsection{*Membership Relation*}

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

theorem membership_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. membership(L,f(x),g(x)), 
                    \<lambda>i x. membership(**Lset(i),f(x),g(x)))"
by (simp only: membership_def setclass_simps, fast)


subsubsection{*Predecessor Set*}

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

theorem pred_set_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. pred_set(L,f(x),g(x),h(x),b(x)), 
                    \<lambda>i x. pred_set(**Lset(i),f(x),g(x),h(x),b(x)))" 
by (simp only: pred_set_def setclass_simps, fast) 



subsubsection{*Domain*}

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

theorem domain_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. is_domain(L,f(x),g(x)), 
                    \<lambda>i x. is_domain(**Lset(i),f(x),g(x)))"
by (simp only: is_domain_def setclass_simps, fast)


subsubsection{*Range*}

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

theorem range_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. is_range(L,f(x),g(x)), 
                    \<lambda>i x. is_range(**Lset(i),f(x),g(x)))"
by (simp only: is_range_def setclass_simps, fast)



 

subsubsection{*Image*}

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
by (simp add: image_fm_def image_def)

lemma image_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> image(**A, x, y, z) <-> sats(A, image_fm(i,j,k), env)"
by (simp add: sats_image_fm)

theorem image_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. image(L,f(x),g(x),h(x)), 
                    \<lambda>i x. image(**Lset(i),f(x),g(x),h(x)))" 
by (simp only: image_def setclass_simps, fast)


subsubsection{*The Concept of Relation*}

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

theorem is_relation_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. is_relation(L,f(x)), 
                    \<lambda>i x. is_relation(**Lset(i),f(x)))"
by (simp only: is_relation_def setclass_simps, fast)


subsubsection{*The Concept of Function*}

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

theorem is_function_reflection [simplified,intro]:
     "L_Reflects(?Cl, \<lambda>x. is_function(L,f(x)), 
                    \<lambda>i x. is_function(**Lset(i),f(x)))"
by (simp only: is_function_def setclass_simps, fast)


end
