header {* The Reflection Theorem*}

theory Reflection = Normal:

lemma all_iff_not_ex_not: "(\<forall>x. P(x)) <-> (~ (\<exists>x. ~ P(x)))";
by blast

lemma ball_iff_not_bex_not: "(\<forall>x\<in>A. P(x)) <-> (~ (\<exists>x\<in>A. ~ P(x)))";
by blast

text{*From the notes of A. S. Kechris, page 6, and from 
      Andrzej Mostowski, \emph{Constructible Sets with Applications},
      North-Holland, 1969, page 23.*}


subsection{*Basic Definitions*}

text{*First part: the cumulative hierarchy defining the class @{text M}.  
To avoid handling multiple arguments, we assume that @{text "Mset(l)"} is
closed under ordered pairing provided @{text l} is limit.  Possibly this
could be avoided: the induction hypothesis @{term Cl_reflects} 
(in locale @{text ex_reflection}) could be weakened to
@{term "\<forall>y\<in>Mset(a). \<forall>z\<in>Mset(a). P(<y,z>) <-> Q(a,<y,z>)"}, removing most
uses of @{term Pair_in_Mset}.  But there isn't much point in doing so, since 
ultimately the @{text ex_reflection} proof is packaged up using the
predicate @{text Reflects}.
*}
locale reflection =
  fixes Mset and M and Reflects
  assumes Mset_mono_le : "mono_le_subset(Mset)"
      and Mset_cont    : "cont_Ord(Mset)"
      and Pair_in_Mset : "[| x \<in> Mset(a); y \<in> Mset(a); Limit(a) |] 
                          ==> <x,y> \<in> Mset(a)"
  defines "M(x) == \<exists>a. Ord(a) \<and> x \<in> Mset(a)"
      and "Reflects(Cl,P,Q) == Closed_Unbounded(Cl) \<and>
                              (\<forall>a. Cl(a) --> (\<forall>x\<in>Mset(a). P(x) <-> Q(a,x)))"
  fixes F0 --{*ordinal for a specific value @{term y}*}
  fixes FF --{*sup over the whole level, @{term "y\<in>Mset(a)"}*}
  fixes ClEx --{*Reflecting ordinals for the formula @{term "\<exists>z. P"}*}
  defines "F0(P,y) == \<mu>b. (\<exists>z. M(z) \<and> P(<y,z>)) --> 
                               (\<exists>z\<in>Mset(b). P(<y,z>))"
      and "FF(P)   == \<lambda>a. \<Union>y\<in>Mset(a). F0(P,y)"
      and "ClEx(P) == \<lambda>a. Limit(a) \<and> normalize(FF(P),a) = a"

lemma (in reflection) Mset_mono: "i\<le>j ==> Mset(i) <= Mset(j)"
apply (insert Mset_mono_le) 
apply (simp add: mono_le_subset_def leI) 
done

subsection{*Easy Cases of the Reflection Theorem*}

theorem (in reflection) Triv_reflection [intro]:
     "Reflects(Ord, P, \<lambda>a x. P(x))"
by (simp add: Reflects_def)

theorem (in reflection) Not_reflection [intro]:
     "Reflects(Cl,P,Q) ==> Reflects(Cl, \<lambda>x. ~P(x), \<lambda>a x. ~Q(a,x))"
by (simp add: Reflects_def); 

theorem (in reflection) And_reflection [intro]:
     "[| Reflects(Cl,P,Q); Reflects(C',P',Q') |] 
      ==> Reflects(\<lambda>a. Cl(a) \<and> C'(a), \<lambda>x. P(x) \<and> P'(x), 
                                      \<lambda>a x. Q(a,x) \<and> Q'(a,x))"
by (simp add: Reflects_def Closed_Unbounded_Int, blast)

theorem (in reflection) Or_reflection [intro]:
     "[| Reflects(Cl,P,Q); Reflects(C',P',Q') |] 
      ==> Reflects(\<lambda>a. Cl(a) \<and> C'(a), \<lambda>x. P(x) \<or> P'(x), 
                                      \<lambda>a x. Q(a,x) \<or> Q'(a,x))"
by (simp add: Reflects_def Closed_Unbounded_Int, blast)

theorem (in reflection) Imp_reflection [intro]:
     "[| Reflects(Cl,P,Q); Reflects(C',P',Q') |] 
      ==> Reflects(\<lambda>a. Cl(a) \<and> C'(a), 
                   \<lambda>x. P(x) --> P'(x), 
                   \<lambda>a x. Q(a,x) --> Q'(a,x))"
by (simp add: Reflects_def Closed_Unbounded_Int, blast)

theorem (in reflection) Iff_reflection [intro]:
     "[| Reflects(Cl,P,Q); Reflects(C',P',Q') |] 
      ==> Reflects(\<lambda>a. Cl(a) \<and> C'(a), 
                   \<lambda>x. P(x) <-> P'(x), 
                   \<lambda>a x. Q(a,x) <-> Q'(a,x))"
by (simp add: Reflects_def Closed_Unbounded_Int, blast) 

subsection{*Reflection for Existential Quantifiers*}

lemma (in reflection) F0_works:
     "[| y\<in>Mset(a); Ord(a); M(z); P(<y,z>) |] ==> \<exists>z\<in>Mset(F0(P,y)). P(<y,z>)"
apply (unfold F0_def M_def, clarify)
apply (rule LeastI2)
  apply (blast intro: Mset_mono [THEN subsetD])
 apply (blast intro: lt_Ord2, blast)
done

lemma (in reflection) Ord_F0 [intro,simp]: "Ord(F0(P,y))"
by (simp add: F0_def)

lemma (in reflection) Ord_FF [intro,simp]: "Ord(FF(P,y))"
by (simp add: FF_def)

lemma (in reflection) cont_Ord_FF: "cont_Ord(FF(P))"
apply (insert Mset_cont)
apply (simp add: cont_Ord_def FF_def, blast)
done

text{*Recall that @{term F0} depends upon @{term "y\<in>Mset(a)"}, 
while @{term FF} depends only upon @{term a}. *}
lemma (in reflection) FF_works:
     "[| M(z); y\<in>Mset(a); P(<y,z>); Ord(a) |] ==> \<exists>z\<in>Mset(FF(P,a)). P(<y,z>)"
apply (simp add: FF_def)
apply (simp_all add: cont_Ord_Union [of concl: Mset] 
                     Mset_cont Mset_mono_le not_emptyI Ord_F0)
apply (blast intro: F0_works)  
done

lemma (in reflection) FFN_works:
     "[| M(z); y\<in>Mset(a); P(<y,z>); Ord(a) |] 
      ==> \<exists>z\<in>Mset(normalize(FF(P),a)). P(<y,z>)"
apply (drule FF_works [of concl: P], assumption+) 
apply (blast intro: cont_Ord_FF le_normalize [THEN Mset_mono, THEN subsetD])
done


text{*Locale for the induction hypothesis*}

locale ex_reflection = reflection +
  fixes P  --"the original formula"
  fixes Q  --"the reflected formula"
  fixes Cl --"the class of reflecting ordinals"
  assumes Cl_reflects: "[| Cl(a); Ord(a) |] ==> \<forall>x\<in>Mset(a). P(x) <-> Q(a,x)"

lemma (in ex_reflection) ClEx_downward:
     "[| M(z); y\<in>Mset(a); P(<y,z>); Cl(a); ClEx(P,a) |] 
      ==> \<exists>z\<in>Mset(a). Q(a,<y,z>)"
apply (simp add: ClEx_def, clarify) 
apply (frule Limit_is_Ord) 
apply (frule FFN_works [of concl: P], assumption+) 
apply (drule Cl_reflects, assumption+) 
apply (auto simp add: Limit_is_Ord Pair_in_Mset)
done

lemma (in ex_reflection) ClEx_upward:
     "[| z\<in>Mset(a); y\<in>Mset(a); Q(a,<y,z>); Cl(a); ClEx(P,a) |] 
      ==> \<exists>z. M(z) \<and> P(<y,z>)"
apply (simp add: ClEx_def M_def)
apply (blast dest: Cl_reflects
	     intro: Limit_is_Ord Pair_in_Mset)
done

text{*Class @{text ClEx} indeed consists of reflecting ordinals...*}
lemma (in ex_reflection) ZF_ClEx_iff:
     "[| y\<in>Mset(a); Cl(a); ClEx(P,a) |] 
      ==> (\<exists>z. M(z) \<and> P(<y,z>)) <-> (\<exists>z\<in>Mset(a). Q(a,<y,z>))"
by (blast intro: dest: ClEx_downward ClEx_upward) 

text{*...and it is closed and unbounded*}
lemma (in ex_reflection) ZF_Closed_Unbounded_ClEx:
     "Closed_Unbounded(ClEx(P))"
apply (simp add: ClEx_def)
apply (fast intro: Closed_Unbounded_Int Normal_imp_fp_Closed_Unbounded
                   Closed_Unbounded_Limit Normal_normalize)
done

text{*The same two theorems, exported to locale @{text reflection}.*}

text{*Class @{text ClEx} indeed consists of reflecting ordinals...*}
lemma (in reflection) ClEx_iff:
     "[| y\<in>Mset(a); Cl(a); ClEx(P,a);
        !!a. [| Cl(a); Ord(a) |] ==> \<forall>x\<in>Mset(a). P(x) <-> Q(a,x) |] 
      ==> (\<exists>z. M(z) \<and> P(<y,z>)) <-> (\<exists>z\<in>Mset(a). Q(a,<y,z>))"
apply (unfold ClEx_def FF_def F0_def M_def)
apply (rule Reflection.ZF_ClEx_iff [of Mset Cl], 
       simp_all add: Mset_mono_le Mset_cont Pair_in_Mset)
done

lemma (in reflection) Closed_Unbounded_ClEx:
     "(!!a. [| Cl(a); Ord(a) |] ==> \<forall>x\<in>Mset(a). P(x) <-> Q(a,x))
      ==> Closed_Unbounded(ClEx(P))"
apply (unfold ClEx_def FF_def F0_def M_def)
apply (rule Reflection.ZF_Closed_Unbounded_ClEx, 
       simp_all add: Mset_mono_le Mset_cont Pair_in_Mset) 
done

lemma (in reflection) Ex_reflection_0:
     "Reflects(Cl,P0,Q0) 
      ==> Reflects(\<lambda>a. Cl(a) \<and> ClEx(P0,a), 
                   \<lambda>x. \<exists>z. M(z) \<and> P0(<x,z>), 
                   \<lambda>a x. \<exists>z\<in>Mset(a). Q0(a,<x,z>))" 
apply (simp add: Reflects_def) 
apply (intro conjI Closed_Unbounded_Int)
  apply blast 
 apply (rule reflection.Closed_Unbounded_ClEx [of Cl P0 Q0], blast, clarify) 
apply (rule_tac Cl=Cl in  ClEx_iff, assumption+, blast) 
done

lemma (in reflection) All_reflection_0:
     "Reflects(Cl,P0,Q0) 
      ==> Reflects(\<lambda>a. Cl(a) \<and> ClEx(\<lambda>x.~P0(x), a), 
                   \<lambda>x. \<forall>z. M(z) --> P0(<x,z>), 
                   \<lambda>a x. \<forall>z\<in>Mset(a). Q0(a,<x,z>))" 
apply (simp only: all_iff_not_ex_not ball_iff_not_bex_not) 
apply (rule Not_reflection, drule Not_reflection, simp) 
apply (erule Ex_reflection_0)
done

theorem (in reflection) Ex_reflection [intro]:
     "Reflects(Cl, \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))) 
      ==> Reflects(\<lambda>a. Cl(a) \<and> ClEx(\<lambda>x. P(fst(x),snd(x)), a), 
                   \<lambda>x. \<exists>z. M(z) \<and> P(x,z), 
                   \<lambda>a x. \<exists>z\<in>Mset(a). Q(a,x,z))"
by (rule Ex_reflection_0 [of _ " \<lambda>x. P(fst(x),snd(x))" 
                               "\<lambda>a x. Q(a,fst(x),snd(x))", simplified])

theorem (in reflection) All_reflection [intro]:
     "Reflects(Cl,  \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x)))
      ==> Reflects(\<lambda>a. Cl(a) \<and> ClEx(\<lambda>x. ~P(fst(x),snd(x)), a), 
                   \<lambda>x. \<forall>z. M(z) --> P(x,z), 
                   \<lambda>a x. \<forall>z\<in>Mset(a). Q(a,x,z))" 
by (rule All_reflection_0 [of _ "\<lambda>x. P(fst(x),snd(x))" 
                                "\<lambda>a x. Q(a,fst(x),snd(x))", simplified])

text{*No point considering bounded quantifiers, where reflection is trivial.*}


subsection{*Simple Examples of Reflection*}

text{*Example 1: reflecting a simple formula.  The reflecting class is first
given as the variable @{text ?Cl} and later retrieved from the final 
proof state.*}
lemma (in reflection) 
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> x \<in> y, 
               \<lambda>a x. \<exists>y\<in>Mset(a). x \<in> y)"
by fast

text{*Problem here: there needs to be a conjunction (class intersection)
in the class of reflecting ordinals.  The @{term "Ord(a)"} is redundant,
though harmless.*}
lemma (in reflection) 
     "Reflects(\<lambda>a. Ord(a) \<and> ClEx(\<lambda>x. fst(x) \<in> snd(x), a),   
               \<lambda>x. \<exists>y. M(y) \<and> x \<in> y, 
               \<lambda>a x. \<exists>y\<in>Mset(a). x \<in> y)" 
by fast


text{*Example 2*}
lemma (in reflection) 
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) --> z \<subseteq> x --> z \<in> y), 
               \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). z \<subseteq> x --> z \<in> y)" 
by fast

text{*Example 2'.  We give the reflecting class explicitly. *}
lemma (in reflection) 
  "Reflects
    (\<lambda>a. (Ord(a) \<and>
          ClEx(\<lambda>x. ~ (snd(x) \<subseteq> fst(fst(x)) --> snd(x) \<in> snd(fst(x))), a)) \<and>
          ClEx(\<lambda>x. \<forall>z. M(z) --> z \<subseteq> fst(x) --> z \<in> snd(x), a),
	    \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) --> z \<subseteq> x --> z \<in> y), 
	    \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). z \<subseteq> x --> z \<in> y)" 
by fast

text{*Example 2''.  We expand the subset relation.*}
lemma (in reflection) 
  "Reflects(?Cl,
        \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) --> (\<forall>w. M(w) --> w\<in>z --> w\<in>x) --> z\<in>y),
        \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). (\<forall>w\<in>Mset(a). w\<in>z --> w\<in>x) --> z\<in>y)"
by fast

text{*Example 2'''.  Single-step version, to reveal the reflecting class.*}
lemma (in reflection) 
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) --> z \<subseteq> x --> z \<in> y), 
               \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). z \<subseteq> x --> z \<in> y)" 
apply (rule Ex_reflection) 
txt{*
@{goals[display,indent=0,margin=60]}
*}
apply (rule All_reflection) 
txt{*
@{goals[display,indent=0,margin=60]}
*}
apply (rule Triv_reflection) 
txt{*
@{goals[display,indent=0,margin=60]}
*}
done

text{*Example 3.  Warning: the following examples make sense only
if @{term P} is quantifier-free, since it is not being relativized.*}
lemma (in reflection) 
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) --> z \<in> y <-> z \<in> x \<and> P(z)), 
               \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). z \<in> y <-> z \<in> x \<and> P(z))"
by fast

text{*Example 3'*}
lemma (in reflection) 
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> y = Collect(x,P),
               \<lambda>a x. \<exists>y\<in>Mset(a). y = Collect(x,P))";
by fast

text{*Example 3''*}
lemma (in reflection) 
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> y = Replace(x,P),
               \<lambda>a x. \<exists>y\<in>Mset(a). y = Replace(x,P))";
by fast

text{*Example 4: Axiom of Choice.  Possibly wrong, since @{text \<Pi>} needs
to be relativized.*}
lemma (in reflection) 
     "Reflects(?Cl,
               \<lambda>A. 0\<notin>A --> (\<exists>f. M(f) \<and> f \<in> (\<Pi>X \<in> A. X)),
               \<lambda>a A. 0\<notin>A --> (\<exists>f\<in>Mset(a). f \<in> (\<Pi>X \<in> A. X)))"
by fast

end

