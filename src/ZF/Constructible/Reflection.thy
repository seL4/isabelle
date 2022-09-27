(*  Title:      ZF/Constructible/Reflection.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>The Reflection Theorem\<close>

theory Reflection imports Normal begin

lemma all_iff_not_ex_not: "(\<forall>x. P(x)) \<longleftrightarrow> (\<not> (\<exists>x. \<not> P(x)))"
  by blast

lemma ball_iff_not_bex_not: "(\<forall>x\<in>A. P(x)) \<longleftrightarrow> (\<not> (\<exists>x\<in>A. \<not> P(x)))"
  by blast

text\<open>From the notes of A. S. Kechris, page 6, and from
      Andrzej Mostowski, \emph{Constructible Sets with Applications},
      North-Holland, 1969, page 23.\<close>


subsection\<open>Basic Definitions\<close>

text\<open>First part: the cumulative hierarchy defining the class \<open>M\<close>.
To avoid handling multiple arguments, we assume that \<open>Mset(l)\<close> is
closed under ordered pairing provided \<open>l\<close> is limit.  Possibly this
could be avoided: the induction hypothesis \<^term>\<open>Cl_reflects\<close>
(in locale \<open>ex_reflection\<close>) could be weakened to
\<^term>\<open>\<forall>y\<in>Mset(a). \<forall>z\<in>Mset(a). P(<y,z>) \<longleftrightarrow> Q(a,<y,z>)\<close>, removing most
uses of \<^term>\<open>Pair_in_Mset\<close>.  But there isn't much point in doing so, since
ultimately the \<open>ex_reflection\<close> proof is packaged up using the
predicate \<open>Reflects\<close>.
\<close>
locale reflection =
  fixes Mset and M and Reflects
  assumes Mset_mono_le : "mono_le_subset(Mset)"
      and Mset_cont    : "cont_Ord(Mset)"
      and Pair_in_Mset : "\<lbrakk>x \<in> Mset(a); y \<in> Mset(a); Limit(a)\<rbrakk>
                          \<Longrightarrow> <x,y> \<in> Mset(a)"
  defines "M(x) \<equiv> \<exists>a. Ord(a) \<and> x \<in> Mset(a)"
      and "Reflects(Cl,P,Q) \<equiv> Closed_Unbounded(Cl) \<and>
                              (\<forall>a. Cl(a) \<longrightarrow> (\<forall>x\<in>Mset(a). P(x) \<longleftrightarrow> Q(a,x)))"
  fixes F0 \<comment> \<open>ordinal for a specific value \<^term>\<open>y\<close>\<close>
  fixes FF \<comment> \<open>sup over the whole level, \<^term>\<open>y\<in>Mset(a)\<close>\<close>
  fixes ClEx \<comment> \<open>Reflecting ordinals for the formula \<^term>\<open>\<exists>z. P\<close>\<close>
  defines "F0(P,y) \<equiv> \<mu> b. (\<exists>z. M(z) \<and> P(<y,z>)) \<longrightarrow>
                               (\<exists>z\<in>Mset(b). P(<y,z>))"
      and "FF(P)   \<equiv> \<lambda>a. \<Union>y\<in>Mset(a). F0(P,y)"
      and "ClEx(P,a) \<equiv> Limit(a) \<and> normalize(FF(P),a) = a"

begin 

lemma Mset_mono: "i\<le>j \<Longrightarrow> Mset(i) \<subseteq> Mset(j)"
  using Mset_mono_le by (simp add: mono_le_subset_def leI)

text\<open>Awkward: we need a version of \<open>ClEx_def\<close> as an equality
      at the level of classes, which do not really exist\<close>
lemma ClEx_eq:
     "ClEx(P) \<equiv> \<lambda>a. Limit(a) \<and> normalize(FF(P),a) = a"
by (simp add: ClEx_def [symmetric])


subsection\<open>Easy Cases of the Reflection Theorem\<close>

theorem Triv_reflection [intro]:
  "Reflects(Ord, P, \<lambda>a x. P(x))"
  by (simp add: Reflects_def)

theorem Not_reflection [intro]:
  "Reflects(Cl,P,Q) \<Longrightarrow> Reflects(Cl, \<lambda>x. \<not>P(x), \<lambda>a x. \<not>Q(a,x))"
  by (simp add: Reflects_def)

theorem And_reflection [intro]:
  "\<lbrakk>Reflects(Cl,P,Q); Reflects(C',P',Q')\<rbrakk>
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> C'(a), \<lambda>x. P(x) \<and> P'(x),
                                      \<lambda>a x. Q(a,x) \<and> Q'(a,x))"
  by (simp add: Reflects_def Closed_Unbounded_Int, blast)

theorem Or_reflection [intro]:
     "\<lbrakk>Reflects(Cl,P,Q); Reflects(C',P',Q')\<rbrakk>
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> C'(a), \<lambda>x. P(x) \<or> P'(x),
                                      \<lambda>a x. Q(a,x) \<or> Q'(a,x))"
by (simp add: Reflects_def Closed_Unbounded_Int, blast)

theorem Imp_reflection [intro]:
     "\<lbrakk>Reflects(Cl,P,Q); Reflects(C',P',Q')\<rbrakk>
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> C'(a),
                   \<lambda>x. P(x) \<longrightarrow> P'(x),
                   \<lambda>a x. Q(a,x) \<longrightarrow> Q'(a,x))"
by (simp add: Reflects_def Closed_Unbounded_Int, blast)

theorem Iff_reflection [intro]:
     "\<lbrakk>Reflects(Cl,P,Q); Reflects(C',P',Q')\<rbrakk>
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> C'(a),
                   \<lambda>x. P(x) \<longleftrightarrow> P'(x),
                   \<lambda>a x. Q(a,x) \<longleftrightarrow> Q'(a,x))"
by (simp add: Reflects_def Closed_Unbounded_Int, blast)

subsection\<open>Reflection for Existential Quantifiers\<close>

lemma F0_works:
  "\<lbrakk>y\<in>Mset(a); Ord(a); M(z); P(<y,z>)\<rbrakk> \<Longrightarrow> \<exists>z\<in>Mset(F0(P,y)). P(<y,z>)"
  unfolding F0_def M_def
  apply clarify
  apply (rule LeastI2)
    apply (blast intro: Mset_mono [THEN subsetD])
   apply (blast intro: lt_Ord2, blast)
  done

lemma Ord_F0 [intro,simp]: "Ord(F0(P,y))"
  by (simp add: F0_def)

lemma Ord_FF [intro,simp]: "Ord(FF(P,y))"
  by (simp add: FF_def)

lemma cont_Ord_FF: "cont_Ord(FF(P))"
  using Mset_cont by (simp add: cont_Ord_def FF_def, blast)

text\<open>Recall that \<^term>\<open>F0\<close> depends upon \<^term>\<open>y\<in>Mset(a)\<close>,
while \<^term>\<open>FF\<close> depends only upon \<^term>\<open>a\<close>.\<close>
lemma FF_works:
  "\<lbrakk>M(z); y\<in>Mset(a); P(<y,z>); Ord(a)\<rbrakk> \<Longrightarrow> \<exists>z\<in>Mset(FF(P,a)). P(<y,z>)"
  apply (simp add: FF_def)
  apply (simp_all add: cont_Ord_Union [of concl: Mset]
      Mset_cont Mset_mono_le not_emptyI)
  apply (blast intro: F0_works)
  done

lemma FFN_works:
     "\<lbrakk>M(z); y\<in>Mset(a); P(<y,z>); Ord(a)\<rbrakk>
      \<Longrightarrow> \<exists>z\<in>Mset(normalize(FF(P),a)). P(<y,z>)"
apply (drule FF_works [of concl: P], assumption+)
apply (blast intro: cont_Ord_FF le_normalize [THEN Mset_mono, THEN subsetD])
done

end

text\<open>Locale for the induction hypothesis\<close>

locale ex_reflection = reflection +
  fixes P  \<comment> \<open>the original formula\<close>
  fixes Q  \<comment> \<open>the reflected formula\<close>
  fixes Cl \<comment> \<open>the class of reflecting ordinals\<close>
  assumes Cl_reflects: "\<lbrakk>Cl(a); Ord(a)\<rbrakk> \<Longrightarrow> \<forall>x\<in>Mset(a). P(x) \<longleftrightarrow> Q(a,x)"

begin

lemma ClEx_downward:
     "\<lbrakk>M(z); y\<in>Mset(a); P(<y,z>); Cl(a); ClEx(P,a)\<rbrakk>
      \<Longrightarrow> \<exists>z\<in>Mset(a). Q(a,<y,z>)"
apply (simp add: ClEx_def, clarify)
apply (frule Limit_is_Ord)
apply (frule FFN_works [of concl: P], assumption+)
apply (drule Cl_reflects, assumption+)
apply (auto simp add: Limit_is_Ord Pair_in_Mset)
done

lemma ClEx_upward:
     "\<lbrakk>z\<in>Mset(a); y\<in>Mset(a); Q(a,<y,z>); Cl(a); ClEx(P,a)\<rbrakk>
      \<Longrightarrow> \<exists>z. M(z) \<and> P(<y,z>)"
apply (simp add: ClEx_def M_def)
apply (blast dest: Cl_reflects
             intro: Limit_is_Ord Pair_in_Mset)
done

text\<open>Class \<open>ClEx\<close> indeed consists of reflecting ordinals...\<close>
lemma ZF_ClEx_iff:
     "\<lbrakk>y\<in>Mset(a); Cl(a); ClEx(P,a)\<rbrakk>
      \<Longrightarrow> (\<exists>z. M(z) \<and> P(<y,z>)) \<longleftrightarrow> (\<exists>z\<in>Mset(a). Q(a,<y,z>))"
by (blast intro: dest: ClEx_downward ClEx_upward)

text\<open>...and it is closed and unbounded\<close>
lemma ZF_Closed_Unbounded_ClEx:
     "Closed_Unbounded(ClEx(P))"
apply (simp add: ClEx_eq)
apply (fast intro: Closed_Unbounded_Int Normal_imp_fp_Closed_Unbounded
                   Closed_Unbounded_Limit Normal_normalize)
done

end

text\<open>The same two theorems, exported to locale \<open>reflection\<close>.\<close>

context reflection
begin

text\<open>Class \<open>ClEx\<close> indeed consists of reflecting ordinals...\<close>
lemma ClEx_iff:
     "\<lbrakk>y\<in>Mset(a); Cl(a); ClEx(P,a);
        \<And>a. \<lbrakk>Cl(a); Ord(a)\<rbrakk> \<Longrightarrow> \<forall>x\<in>Mset(a). P(x) \<longleftrightarrow> Q(a,x)\<rbrakk>
      \<Longrightarrow> (\<exists>z. M(z) \<and> P(<y,z>)) \<longleftrightarrow> (\<exists>z\<in>Mset(a). Q(a,<y,z>))"
apply (unfold ClEx_def FF_def F0_def M_def)
apply (rule ex_reflection.ZF_ClEx_iff
  [OF ex_reflection.intro, OF reflection.intro ex_reflection_axioms.intro,
    of Mset Cl])
apply (simp_all add: Mset_mono_le Mset_cont Pair_in_Mset)
done

(*Alternative proof, less unfolding:
apply (rule Reflection.ZF_ClEx_iff [of Mset _ _ Cl, folded M_def])
apply (fold ClEx_def FF_def F0_def)
apply (rule ex_reflection.intro, assumption)
apply (simp add: ex_reflection_axioms.intro, assumption+)
*)

lemma Closed_Unbounded_ClEx:
     "(\<And>a. \<lbrakk>Cl(a); Ord(a)\<rbrakk> \<Longrightarrow> \<forall>x\<in>Mset(a). P(x) \<longleftrightarrow> Q(a,x))
      \<Longrightarrow> Closed_Unbounded(ClEx(P))"
apply (unfold ClEx_eq FF_def F0_def M_def)
apply (rule ex_reflection.ZF_Closed_Unbounded_ClEx [of Mset _ _ Cl])
apply (rule ex_reflection.intro, rule reflection_axioms)
apply (blast intro: ex_reflection_axioms.intro)
done

subsection\<open>Packaging the Quantifier Reflection Rules\<close>

lemma Ex_reflection_0:
     "Reflects(Cl,P0,Q0)
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> ClEx(P0,a),
                   \<lambda>x. \<exists>z. M(z) \<and> P0(<x,z>),
                   \<lambda>a x. \<exists>z\<in>Mset(a). Q0(a,<x,z>))"
apply (simp add: Reflects_def)
apply (intro conjI Closed_Unbounded_Int)
  apply blast
 apply (rule Closed_Unbounded_ClEx [of Cl P0 Q0], blast, clarify)
apply (rule_tac Cl=Cl in  ClEx_iff, assumption+, blast)
done

lemma All_reflection_0:
     "Reflects(Cl,P0,Q0)
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> ClEx(\<lambda>x.\<not>P0(x), a),
                   \<lambda>x. \<forall>z. M(z) \<longrightarrow> P0(<x,z>),
                   \<lambda>a x. \<forall>z\<in>Mset(a). Q0(a,<x,z>))"
apply (simp only: all_iff_not_ex_not ball_iff_not_bex_not)
apply (rule Not_reflection, drule Not_reflection, simp)
apply (erule Ex_reflection_0)
done

theorem Ex_reflection [intro]:
     "Reflects(Cl, \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x)))
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> ClEx(\<lambda>x. P(fst(x),snd(x)), a),
                   \<lambda>x. \<exists>z. M(z) \<and> P(x,z),
                   \<lambda>a x. \<exists>z\<in>Mset(a). Q(a,x,z))"
by (rule Ex_reflection_0 [of _ " \<lambda>x. P(fst(x),snd(x))"
                               "\<lambda>a x. Q(a,fst(x),snd(x))", simplified])

theorem All_reflection [intro]:
     "Reflects(Cl,  \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x)))
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> ClEx(\<lambda>x. \<not>P(fst(x),snd(x)), a),
                   \<lambda>x. \<forall>z. M(z) \<longrightarrow> P(x,z),
                   \<lambda>a x. \<forall>z\<in>Mset(a). Q(a,x,z))"
by (rule All_reflection_0 [of _ "\<lambda>x. P(fst(x),snd(x))"
                                "\<lambda>a x. Q(a,fst(x),snd(x))", simplified])

text\<open>And again, this time using class-bounded quantifiers\<close>

theorem Rex_reflection [intro]:
     "Reflects(Cl, \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x)))
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> ClEx(\<lambda>x. P(fst(x),snd(x)), a),
                   \<lambda>x. \<exists>z[M]. P(x,z),
                   \<lambda>a x. \<exists>z\<in>Mset(a). Q(a,x,z))"
by (unfold rex_def, blast)

theorem Rall_reflection [intro]:
     "Reflects(Cl,  \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x)))
      \<Longrightarrow> Reflects(\<lambda>a. Cl(a) \<and> ClEx(\<lambda>x. \<not>P(fst(x),snd(x)), a),
                   \<lambda>x. \<forall>z[M]. P(x,z),
                   \<lambda>a x. \<forall>z\<in>Mset(a). Q(a,x,z))"
by (unfold rall_def, blast)


text\<open>No point considering bounded quantifiers, where reflection is trivial.\<close>


subsection\<open>Simple Examples of Reflection\<close>

text\<open>Example 1: reflecting a simple formula.  The reflecting class is first
given as the variable \<open>?Cl\<close> and later retrieved from the final
proof state.\<close>
schematic_goal
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> x \<in> y,
               \<lambda>a x. \<exists>y\<in>Mset(a). x \<in> y)"
by fast

text\<open>Problem here: there needs to be a conjunction (class intersection)
in the class of reflecting ordinals.  The \<^term>\<open>Ord(a)\<close> is redundant,
though harmless.\<close>
lemma
     "Reflects(\<lambda>a. Ord(a) \<and> ClEx(\<lambda>x. fst(x) \<in> snd(x), a),
               \<lambda>x. \<exists>y. M(y) \<and> x \<in> y,
               \<lambda>a x. \<exists>y\<in>Mset(a). x \<in> y)"
by fast


text\<open>Example 2\<close>
schematic_goal
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) \<longrightarrow> z \<subseteq> x \<longrightarrow> z \<in> y),
               \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). z \<subseteq> x \<longrightarrow> z \<in> y)"
by fast

text\<open>Example 2'.  We give the reflecting class explicitly.\<close>
lemma
  "Reflects
    (\<lambda>a. (Ord(a) \<and>
          ClEx(\<lambda>x. \<not> (snd(x) \<subseteq> fst(fst(x)) \<longrightarrow> snd(x) \<in> snd(fst(x))), a)) \<and>
          ClEx(\<lambda>x. \<forall>z. M(z) \<longrightarrow> z \<subseteq> fst(x) \<longrightarrow> z \<in> snd(x), a),
            \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) \<longrightarrow> z \<subseteq> x \<longrightarrow> z \<in> y),
            \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). z \<subseteq> x \<longrightarrow> z \<in> y)"
by fast

text\<open>Example 2''.  We expand the subset relation.\<close>
schematic_goal
  "Reflects(?Cl,
        \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) \<longrightarrow> (\<forall>w. M(w) \<longrightarrow> w\<in>z \<longrightarrow> w\<in>x) \<longrightarrow> z\<in>y),
        \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). (\<forall>w\<in>Mset(a). w\<in>z \<longrightarrow> w\<in>x) \<longrightarrow> z\<in>y)"
by fast

text\<open>Example 2'''.  Single-step version, to reveal the reflecting class.\<close>
schematic_goal
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) \<longrightarrow> z \<subseteq> x \<longrightarrow> z \<in> y),
               \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). z \<subseteq> x \<longrightarrow> z \<in> y)"
apply (rule Ex_reflection)
txt\<open>
@{goals[display,indent=0,margin=60]}
\<close>
apply (rule All_reflection)
txt\<open>
@{goals[display,indent=0,margin=60]}
\<close>
apply (rule Triv_reflection)
txt\<open>
@{goals[display,indent=0,margin=60]}
\<close>
done

text\<open>Example 3.  Warning: the following examples make sense only
if \<^term>\<open>P\<close> is quantifier-free, since it is not being relativized.\<close>
schematic_goal
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> (\<forall>z. M(z) \<longrightarrow> z \<in> y \<longleftrightarrow> z \<in> x \<and> P(z)),
               \<lambda>a x. \<exists>y\<in>Mset(a). \<forall>z\<in>Mset(a). z \<in> y \<longleftrightarrow> z \<in> x \<and> P(z))"
by fast

text\<open>Example 3'\<close>
schematic_goal
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> y = Collect(x,P),
               \<lambda>a x. \<exists>y\<in>Mset(a). y = Collect(x,P))"
by fast

text\<open>Example 3''\<close>
schematic_goal
     "Reflects(?Cl,
               \<lambda>x. \<exists>y. M(y) \<and> y = Replace(x,P),
               \<lambda>a x. \<exists>y\<in>Mset(a). y = Replace(x,P))"
by fast

text\<open>Example 4: Axiom of Choice.  Possibly wrong, since \<open>\<Pi>\<close> needs
to be relativized.\<close>
schematic_goal
     "Reflects(?Cl,
               \<lambda>A. 0\<notin>A \<longrightarrow> (\<exists>f. M(f) \<and> f \<in> (\<Prod>X \<in> A. X)),
               \<lambda>a A. 0\<notin>A \<longrightarrow> (\<exists>f\<in>Mset(a). f \<in> (\<Prod>X \<in> A. X)))"
by fast

end

end

