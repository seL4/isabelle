(*  Title:      ZF/Constructible/L_axioms.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>The ZF Axioms (Except Separation) in L\<close>

theory L_axioms imports Formula Relative Reflection MetaExists begin

text \<open>The class L satisfies the premises of locale \<open>M_trivial\<close>\<close>

lemma transL: "\<lbrakk>y\<in>x; L(x)\<rbrakk> \<Longrightarrow> L(y)"
apply (insert Transset_Lset)
apply (simp add: Transset_def L_def, blast)
done

lemma nonempty: "L(0)"
apply (simp add: L_def)
apply (blast intro: zero_in_Lset)
done

theorem upair_ax: "upair_ax(L)"
apply (simp add: upair_ax_def upair_def, clarify)
apply (rule_tac x="{x,y}" in rexI)
apply (simp_all add: doubleton_in_L)
done

theorem Union_ax: "Union_ax(L)"
apply (simp add: Union_ax_def big_union_def, clarify)
apply (rule_tac x="\<Union>(x)" in rexI)
apply (simp_all add: Union_in_L, auto)
apply (blast intro: transL)
done

theorem power_ax: "power_ax(L)"
apply (simp add: power_ax_def powerset_def Relative.subset_def, clarify)
apply (rule_tac x="{y \<in> Pow(x). L(y)}" in rexI)
apply (simp_all add: LPow_in_L, auto)
apply (blast intro: transL)
done

text\<open>We don't actually need \<^term>\<open>L\<close> to satisfy the foundation axiom.\<close>
theorem foundation_ax: "foundation_ax(L)"
apply (simp add: foundation_ax_def)
apply (rule rallI) 
apply (cut_tac A=x in foundation)
apply (blast intro: transL)
done

subsection\<open>For L to satisfy Replacement\<close>

(*Can't move these to Formula unless the definition of univalent is moved
there too!*)

lemma LReplace_in_Lset:
     "\<lbrakk>X \<in> Lset(i); univalent(L,X,Q); Ord(i)\<rbrakk>
      \<Longrightarrow> \<exists>j. Ord(j) \<and> Replace(X, \<lambda>x y. Q(x,y) \<and> L(y)) \<subseteq> Lset(j)"
apply (rule_tac x="\<Union>y \<in> Replace(X, \<lambda>x y. Q(x,y) \<and> L(y)). succ(lrank(y))"
       in exI)
apply simp
apply clarify
apply (rule_tac a=x in UN_I)
 apply (simp_all add: Replace_iff univalent_def)
apply (blast dest: transL L_I)
done

lemma LReplace_in_L:
     "\<lbrakk>L(X); univalent(L,X,Q)\<rbrakk>
      \<Longrightarrow> \<exists>Y. L(Y) \<and> Replace(X, \<lambda>x y. Q(x,y) \<and> L(y)) \<subseteq> Y"
apply (drule L_D, clarify)
apply (drule LReplace_in_Lset, assumption+)
apply (blast intro: L_I Lset_in_Lset_succ)
done

theorem replacement: "replacement(L,P)"
apply (simp add: replacement_def, clarify)
apply (frule LReplace_in_L, assumption+, clarify)
apply (rule_tac x=Y in rexI)
apply (simp_all add: Replace_iff univalent_def, blast)
done

lemma strong_replacementI [rule_format]:
    "\<lbrakk>\<forall>B[L]. separation(L, \<lambda>u. \<exists>x[L]. x\<in>B \<and> P(x,u))\<rbrakk>
     \<Longrightarrow> strong_replacement(L,P)"
apply (simp add: strong_replacement_def, clarify)
apply (frule replacementD [OF replacement], assumption, clarify)
apply (drule_tac x=A in rspec, clarify)
apply (drule_tac z=Y in separationD, assumption, clarify)
apply (rule_tac x=y in rexI, force, assumption)
done


subsection\<open>Instantiating the locale \<open>M_trivial\<close>\<close>
text\<open>No instances of Separation yet.\<close>

lemma Lset_mono_le: "mono_le_subset(Lset)"
by (simp add: mono_le_subset_def le_imp_subset Lset_mono)

lemma Lset_cont: "cont_Ord(Lset)"
by (simp add: cont_Ord_def Limit_Lset_eq OUnion_def Limit_is_Ord)

lemmas L_nat = Ord_in_L [OF Ord_nat]

theorem M_trivial_L: "M_trivial(L)"
  apply (rule M_trivial.intro)
  apply (rule M_trans.intro)
    apply (erule (1) transL)
   apply(rule exI,rule  nonempty)
  apply (rule M_trivial_axioms.intro)
      apply (rule upair_ax)
   apply (rule Union_ax)
  done

interpretation L: M_trivial L by (rule M_trivial_L)

(* Replaces the following declarations...
lemmas rall_abs = M_trivial.rall_abs [OF M_trivial_L]
  and rex_abs = M_trivial.rex_abs [OF M_trivial_L]
...
declare rall_abs [simp]
declare rex_abs [simp]
...and dozens of similar ones.
*)

subsection\<open>Instantiation of the locale \<open>reflection\<close>\<close>

text\<open>instances of locale constants\<close>

definition
  L_F0 :: "[i\<Rightarrow>o,i] \<Rightarrow> i" where
    "L_F0(P,y) \<equiv> \<mu> b. (\<exists>z. L(z) \<and> P(\<langle>y,z\<rangle>)) \<longrightarrow> (\<exists>z\<in>Lset(b). P(\<langle>y,z\<rangle>))"

definition
  L_FF :: "[i\<Rightarrow>o,i] \<Rightarrow> i" where
    "L_FF(P)   \<equiv> \<lambda>a. \<Union>y\<in>Lset(a). L_F0(P,y)"

definition
  L_ClEx :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "L_ClEx(P) \<equiv> \<lambda>a. Limit(a) \<and> normalize(L_FF(P),a) = a"


text\<open>We must use the meta-existential quantifier; otherwise the reflection
      terms become enormous!\<close>
definition
  L_Reflects :: "[i\<Rightarrow>o,[i,i]\<Rightarrow>o] \<Rightarrow> prop"  (\<open>(3REFLECTS/ [_,/ _])\<close>) where
    "REFLECTS[P,Q] \<equiv> (\<Or>Cl. Closed_Unbounded(Cl) \<and>
                           (\<forall>a. Cl(a) \<longrightarrow> (\<forall>x \<in> Lset(a). P(x) \<longleftrightarrow> Q(a,x))))"


theorem Triv_reflection:
     "REFLECTS[P, \<lambda>a x. P(x)]"
apply (simp add: L_Reflects_def)
apply (rule meta_exI)
apply (rule Closed_Unbounded_Ord)
done

theorem Not_reflection:
     "REFLECTS[P,Q] \<Longrightarrow> REFLECTS[\<lambda>x. \<not>P(x), \<lambda>a x. \<not>Q(a,x)]"
apply (unfold L_Reflects_def)
apply (erule meta_exE)
apply (rule_tac x=Cl in meta_exI, simp)
done

theorem And_reflection:
     "\<lbrakk>REFLECTS[P,Q]; REFLECTS[P',Q']\<rbrakk>
      \<Longrightarrow> REFLECTS[\<lambda>x. P(x) \<and> P'(x), \<lambda>a x. Q(a,x) \<and> Q'(a,x)]"
apply (unfold L_Reflects_def)
apply (elim meta_exE)
apply (rule_tac x="\<lambda>a. Cl(a) \<and> Cla(a)" in meta_exI)
apply (simp add: Closed_Unbounded_Int, blast)
done

theorem Or_reflection:
     "\<lbrakk>REFLECTS[P,Q]; REFLECTS[P',Q']\<rbrakk>
      \<Longrightarrow> REFLECTS[\<lambda>x. P(x) \<or> P'(x), \<lambda>a x. Q(a,x) \<or> Q'(a,x)]"
apply (unfold L_Reflects_def)
apply (elim meta_exE)
apply (rule_tac x="\<lambda>a. Cl(a) \<and> Cla(a)" in meta_exI)
apply (simp add: Closed_Unbounded_Int, blast)
done

theorem Imp_reflection:
     "\<lbrakk>REFLECTS[P,Q]; REFLECTS[P',Q']\<rbrakk>
      \<Longrightarrow> REFLECTS[\<lambda>x. P(x) \<longrightarrow> P'(x), \<lambda>a x. Q(a,x) \<longrightarrow> Q'(a,x)]"
apply (unfold L_Reflects_def)
apply (elim meta_exE)
apply (rule_tac x="\<lambda>a. Cl(a) \<and> Cla(a)" in meta_exI)
apply (simp add: Closed_Unbounded_Int, blast)
done

theorem Iff_reflection:
     "\<lbrakk>REFLECTS[P,Q]; REFLECTS[P',Q']\<rbrakk>
      \<Longrightarrow> REFLECTS[\<lambda>x. P(x) \<longleftrightarrow> P'(x), \<lambda>a x. Q(a,x) \<longleftrightarrow> Q'(a,x)]"
apply (unfold L_Reflects_def)
apply (elim meta_exE)
apply (rule_tac x="\<lambda>a. Cl(a) \<and> Cla(a)" in meta_exI)
apply (simp add: Closed_Unbounded_Int, blast)
done


lemma reflection_Lset: "reflection(Lset)"
by (blast intro: reflection.intro Lset_mono_le Lset_cont 
                 Formula.Pair_in_LLimit)+


theorem Ex_reflection:
     "REFLECTS[\<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      \<Longrightarrow> REFLECTS[\<lambda>x. \<exists>z. L(z) \<and> P(x,z), \<lambda>a x. \<exists>z\<in>Lset(a). Q(a,x,z)]"
apply (unfold L_Reflects_def L_ClEx_def L_FF_def L_F0_def L_def)
apply (elim meta_exE)
apply (rule meta_exI)
apply (erule reflection.Ex_reflection [OF reflection_Lset])
done

theorem All_reflection:
     "REFLECTS[\<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      \<Longrightarrow> REFLECTS[\<lambda>x. \<forall>z. L(z) \<longrightarrow> P(x,z), \<lambda>a x. \<forall>z\<in>Lset(a). Q(a,x,z)]"
apply (unfold L_Reflects_def L_ClEx_def L_FF_def L_F0_def L_def)
apply (elim meta_exE)
apply (rule meta_exI)
apply (erule reflection.All_reflection [OF reflection_Lset])
done

theorem Rex_reflection:
     "REFLECTS[ \<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      \<Longrightarrow> REFLECTS[\<lambda>x. \<exists>z[L]. P(x,z), \<lambda>a x. \<exists>z\<in>Lset(a). Q(a,x,z)]"
apply (unfold rex_def)
apply (intro And_reflection Ex_reflection, assumption)
done

theorem Rall_reflection:
     "REFLECTS[\<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      \<Longrightarrow> REFLECTS[\<lambda>x. \<forall>z[L]. P(x,z), \<lambda>a x. \<forall>z\<in>Lset(a). Q(a,x,z)]"
apply (unfold rall_def)
apply (intro Imp_reflection All_reflection, assumption)
done

text\<open>This version handles an alternative form of the bounded quantifier
      in the second argument of \<open>REFLECTS\<close>.\<close>
theorem Rex_reflection':
     "REFLECTS[\<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      \<Longrightarrow> REFLECTS[\<lambda>x. \<exists>z[L]. P(x,z), \<lambda>a x. \<exists>z[##Lset(a)]. Q(a,x,z)]"
apply (unfold setclass_def rex_def)
apply (erule Rex_reflection [unfolded rex_def Bex_def]) 
done

text\<open>As above.\<close>
theorem Rall_reflection':
     "REFLECTS[\<lambda>x. P(fst(x),snd(x)), \<lambda>a x. Q(a,fst(x),snd(x))]
      \<Longrightarrow> REFLECTS[\<lambda>x. \<forall>z[L]. P(x,z), \<lambda>a x. \<forall>z[##Lset(a)]. Q(a,x,z)]"
apply (unfold setclass_def rall_def)
apply (erule Rall_reflection [unfolded rall_def Ball_def]) 
done

lemmas FOL_reflections =
        Triv_reflection Not_reflection And_reflection Or_reflection
        Imp_reflection Iff_reflection Ex_reflection All_reflection
        Rex_reflection Rall_reflection Rex_reflection' Rall_reflection'

lemma ReflectsD:
     "\<lbrakk>REFLECTS[P,Q]; Ord(i)\<rbrakk>
      \<Longrightarrow> \<exists>j. i<j \<and> (\<forall>x \<in> Lset(j). P(x) \<longleftrightarrow> Q(j,x))"
apply (unfold L_Reflects_def Closed_Unbounded_def)
apply (elim meta_exE, clarify)
apply (blast dest!: UnboundedD)
done

lemma ReflectsE:
     "\<lbrakk>REFLECTS[P,Q]; Ord(i);
         \<And>j. \<lbrakk>i<j;  \<forall>x \<in> Lset(j). P(x) \<longleftrightarrow> Q(j,x)\<rbrakk> \<Longrightarrow> R\<rbrakk>
      \<Longrightarrow> R"
by (drule ReflectsD, assumption, blast)

lemma Collect_mem_eq: "{x\<in>A. x\<in>B} = A \<inter> B"
by blast


subsection\<open>Internalized Formulas for some Set-Theoretic Concepts\<close>

subsubsection\<open>Some numbers to help write de Bruijn indices\<close>

abbreviation
  digit3 :: i   (\<open>3\<close>) where "3 \<equiv> succ(2)"

abbreviation
  digit4 :: i   (\<open>4\<close>) where "4 \<equiv> succ(3)"

abbreviation
  digit5 :: i   (\<open>5\<close>) where "5 \<equiv> succ(4)"

abbreviation
  digit6 :: i   (\<open>6\<close>) where "6 \<equiv> succ(5)"

abbreviation
  digit7 :: i   (\<open>7\<close>) where "7 \<equiv> succ(6)"

abbreviation
  digit8 :: i   (\<open>8\<close>) where "8 \<equiv> succ(7)"

abbreviation
  digit9 :: i   (\<open>9\<close>) where "9 \<equiv> succ(8)"


subsubsection\<open>The Empty Set, Internalized\<close>

definition
  empty_fm :: "i\<Rightarrow>i" where
    "empty_fm(x) \<equiv> Forall(Neg(Member(0,succ(x))))"

lemma empty_type [TC]:
     "x \<in> nat \<Longrightarrow> empty_fm(x) \<in> formula"
by (simp add: empty_fm_def)

lemma sats_empty_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, empty_fm(x), env) \<longleftrightarrow> empty(##A, nth(x,env))"
by (simp add: empty_fm_def empty_def)

lemma empty_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> empty(##A, x) \<longleftrightarrow> sats(A, empty_fm(i), env)"
by simp

theorem empty_reflection:
     "REFLECTS[\<lambda>x. empty(L,f(x)),
               \<lambda>i x. empty(##Lset(i),f(x))]"
apply (simp only: empty_def)
apply (intro FOL_reflections)
done

text\<open>Not used.  But maybe useful?\<close>
lemma Transset_sats_empty_fm_eq_0:
   "\<lbrakk>n \<in> nat; env \<in> list(A); Transset(A)\<rbrakk>
    \<Longrightarrow> sats(A, empty_fm(n), env) \<longleftrightarrow> nth(n,env) = 0"
apply (simp add: empty_fm_def empty_def Transset_def, auto)
apply (case_tac "n < length(env)")
apply (frule nth_type, assumption+, blast)
apply (simp_all add: not_lt_iff_le nth_eq_0)
done


subsubsection\<open>Unordered Pairs, Internalized\<close>

definition
  upair_fm :: "[i,i,i]\<Rightarrow>i" where
    "upair_fm(x,y,z) \<equiv>
       And(Member(x,z),
           And(Member(y,z),
               Forall(Implies(Member(0,succ(z)),
                              Or(Equal(0,succ(x)), Equal(0,succ(y)))))))"

lemma upair_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> upair_fm(x,y,z) \<in> formula"
by (simp add: upair_fm_def)

lemma sats_upair_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, upair_fm(x,y,z), env) \<longleftrightarrow>
            upair(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: upair_fm_def upair_def)

lemma upair_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> upair(##A, x, y, z) \<longleftrightarrow> sats(A, upair_fm(i,j,k), env)"
by (simp)

text\<open>Useful? At least it refers to "real" unordered pairs\<close>
lemma sats_upair_fm2 [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A); Transset(A)\<rbrakk>
    \<Longrightarrow> sats(A, upair_fm(x,y,z), env) \<longleftrightarrow>
        nth(z,env) = {nth(x,env), nth(y,env)}"
apply (frule lt_length_in_nat, assumption)
apply (simp add: upair_fm_def Transset_def, auto)
apply (blast intro: nth_type)
done

theorem upair_reflection:
     "REFLECTS[\<lambda>x. upair(L,f(x),g(x),h(x)),
               \<lambda>i x. upair(##Lset(i),f(x),g(x),h(x))]"
apply (simp add: upair_def)
apply (intro FOL_reflections)
done

subsubsection\<open>Ordered pairs, Internalized\<close>

definition
  pair_fm :: "[i,i,i]\<Rightarrow>i" where
    "pair_fm(x,y,z) \<equiv>
       Exists(And(upair_fm(succ(x),succ(x),0),
              Exists(And(upair_fm(succ(succ(x)),succ(succ(y)),0),
                         upair_fm(1,0,succ(succ(z)))))))"

lemma pair_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> pair_fm(x,y,z) \<in> formula"
by (simp add: pair_fm_def)

lemma sats_pair_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, pair_fm(x,y,z), env) \<longleftrightarrow>
        pair(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: pair_fm_def pair_def)

lemma pair_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> pair(##A, x, y, z) \<longleftrightarrow> sats(A, pair_fm(i,j,k), env)"
by (simp)

theorem pair_reflection:
     "REFLECTS[\<lambda>x. pair(L,f(x),g(x),h(x)),
               \<lambda>i x. pair(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: pair_def)
apply (intro FOL_reflections upair_reflection)
done


subsubsection\<open>Binary Unions, Internalized\<close>

definition
  union_fm :: "[i,i,i]\<Rightarrow>i" where
    "union_fm(x,y,z) \<equiv>
       Forall(Iff(Member(0,succ(z)),
                  Or(Member(0,succ(x)),Member(0,succ(y)))))"

lemma union_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> union_fm(x,y,z) \<in> formula"
by (simp add: union_fm_def)

lemma sats_union_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, union_fm(x,y,z), env) \<longleftrightarrow>
        union(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: union_fm_def union_def)

lemma union_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> union(##A, x, y, z) \<longleftrightarrow> sats(A, union_fm(i,j,k), env)"
by (simp)

theorem union_reflection:
     "REFLECTS[\<lambda>x. union(L,f(x),g(x),h(x)),
               \<lambda>i x. union(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: union_def)
apply (intro FOL_reflections)
done


subsubsection\<open>Set ``Cons,'' Internalized\<close>

definition
  cons_fm :: "[i,i,i]\<Rightarrow>i" where
    "cons_fm(x,y,z) \<equiv>
       Exists(And(upair_fm(succ(x),succ(x),0),
                  union_fm(0,succ(y),succ(z))))"


lemma cons_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> cons_fm(x,y,z) \<in> formula"
by (simp add: cons_fm_def)

lemma sats_cons_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, cons_fm(x,y,z), env) \<longleftrightarrow>
        is_cons(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: cons_fm_def is_cons_def)

lemma cons_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_cons(##A, x, y, z) \<longleftrightarrow> sats(A, cons_fm(i,j,k), env)"
by simp

theorem cons_reflection:
     "REFLECTS[\<lambda>x. is_cons(L,f(x),g(x),h(x)),
               \<lambda>i x. is_cons(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_cons_def)
apply (intro FOL_reflections upair_reflection union_reflection)
done


subsubsection\<open>Successor Function, Internalized\<close>

definition
  succ_fm :: "[i,i]\<Rightarrow>i" where
    "succ_fm(x,y) \<equiv> cons_fm(x,x,y)"

lemma succ_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> succ_fm(x,y) \<in> formula"
by (simp add: succ_fm_def)

lemma sats_succ_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, succ_fm(x,y), env) \<longleftrightarrow>
        successor(##A, nth(x,env), nth(y,env))"
by (simp add: succ_fm_def successor_def)

lemma successor_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> successor(##A, x, y) \<longleftrightarrow> sats(A, succ_fm(i,j), env)"
by simp

theorem successor_reflection:
     "REFLECTS[\<lambda>x. successor(L,f(x),g(x)),
               \<lambda>i x. successor(##Lset(i),f(x),g(x))]"
apply (simp only: successor_def)
apply (intro cons_reflection)
done


subsubsection\<open>The Number 1, Internalized\<close>

(* "number1(M,a) \<equiv> (\<exists>x[M]. empty(M,x) \<and> successor(M,x,a))" *)
definition
  number1_fm :: "i\<Rightarrow>i" where
    "number1_fm(a) \<equiv> Exists(And(empty_fm(0), succ_fm(0,succ(a))))"

lemma number1_type [TC]:
     "x \<in> nat \<Longrightarrow> number1_fm(x) \<in> formula"
by (simp add: number1_fm_def)

lemma sats_number1_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, number1_fm(x), env) \<longleftrightarrow> number1(##A, nth(x,env))"
by (simp add: number1_fm_def number1_def)

lemma number1_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> number1(##A, x) \<longleftrightarrow> sats(A, number1_fm(i), env)"
by simp

theorem number1_reflection:
     "REFLECTS[\<lambda>x. number1(L,f(x)),
               \<lambda>i x. number1(##Lset(i),f(x))]"
apply (simp only: number1_def)
apply (intro FOL_reflections empty_reflection successor_reflection)
done


subsubsection\<open>Big Union, Internalized\<close>

(*  "big_union(M,A,z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>y[M]. y\<in>A \<and> x \<in> y)" *)
definition
  big_union_fm :: "[i,i]\<Rightarrow>i" where
    "big_union_fm(A,z) \<equiv>
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(A))), Member(1,0)))))"

lemma big_union_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> big_union_fm(x,y) \<in> formula"
by (simp add: big_union_fm_def)

lemma sats_big_union_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, big_union_fm(x,y), env) \<longleftrightarrow>
        big_union(##A, nth(x,env), nth(y,env))"
by (simp add: big_union_fm_def big_union_def)

lemma big_union_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> big_union(##A, x, y) \<longleftrightarrow> sats(A, big_union_fm(i,j), env)"
by simp

theorem big_union_reflection:
     "REFLECTS[\<lambda>x. big_union(L,f(x),g(x)),
               \<lambda>i x. big_union(##Lset(i),f(x),g(x))]"
apply (simp only: big_union_def)
apply (intro FOL_reflections)
done


subsubsection\<open>Variants of Satisfaction Definitions for Ordinals, etc.\<close>

text\<open>The \<open>sats\<close> theorems below are standard versions of the ones proved
in theory \<open>Formula\<close>.  They relate elements of type \<^term>\<open>formula\<close> to
relativized concepts such as \<^term>\<open>subset\<close> or \<^term>\<open>ordinal\<close> rather than to
real concepts such as \<^term>\<open>Ord\<close>.  Now that we have instantiated the locale
\<open>M_trivial\<close>, we no longer require the earlier versions.\<close>

lemma sats_subset_fm':
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, subset_fm(x,y), env) \<longleftrightarrow> subset(##A, nth(x,env), nth(y,env))"
by (simp add: subset_fm_def Relative.subset_def)

theorem subset_reflection:
     "REFLECTS[\<lambda>x. subset(L,f(x),g(x)),
               \<lambda>i x. subset(##Lset(i),f(x),g(x))]"
apply (simp only: Relative.subset_def)
apply (intro FOL_reflections)
done

lemma sats_transset_fm':
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, transset_fm(x), env) \<longleftrightarrow> transitive_set(##A, nth(x,env))"
by (simp add: sats_subset_fm' transset_fm_def transitive_set_def)

theorem transitive_set_reflection:
     "REFLECTS[\<lambda>x. transitive_set(L,f(x)),
               \<lambda>i x. transitive_set(##Lset(i),f(x))]"
apply (simp only: transitive_set_def)
apply (intro FOL_reflections subset_reflection)
done

lemma sats_ordinal_fm':
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, ordinal_fm(x), env) \<longleftrightarrow> ordinal(##A,nth(x,env))"
by (simp add: sats_transset_fm' ordinal_fm_def ordinal_def)

lemma ordinal_iff_sats:
      "\<lbrakk>nth(i,env) = x;  i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> ordinal(##A, x) \<longleftrightarrow> sats(A, ordinal_fm(i), env)"
by (simp add: sats_ordinal_fm')

theorem ordinal_reflection:
     "REFLECTS[\<lambda>x. ordinal(L,f(x)), \<lambda>i x. ordinal(##Lset(i),f(x))]"
apply (simp only: ordinal_def)
apply (intro FOL_reflections transitive_set_reflection)
done


subsubsection\<open>Membership Relation, Internalized\<close>

definition
  Memrel_fm :: "[i,i]\<Rightarrow>i" where
    "Memrel_fm(A,r) \<equiv>
       Forall(Iff(Member(0,succ(r)),
                  Exists(And(Member(0,succ(succ(A))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
                                        And(Member(1,0),
                                            pair_fm(1,0,2))))))))"

lemma Memrel_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> Memrel_fm(x,y) \<in> formula"
by (simp add: Memrel_fm_def)

lemma sats_Memrel_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Memrel_fm(x,y), env) \<longleftrightarrow>
        membership(##A, nth(x,env), nth(y,env))"
by (simp add: Memrel_fm_def membership_def)

lemma Memrel_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> membership(##A, x, y) \<longleftrightarrow> sats(A, Memrel_fm(i,j), env)"
by simp

theorem membership_reflection:
     "REFLECTS[\<lambda>x. membership(L,f(x),g(x)),
               \<lambda>i x. membership(##Lset(i),f(x),g(x))]"
apply (simp only: membership_def)
apply (intro FOL_reflections pair_reflection)
done

subsubsection\<open>Predecessor Set, Internalized\<close>

definition
  pred_set_fm :: "[i,i,i,i]\<Rightarrow>i" where
    "pred_set_fm(A,x,r,B) \<equiv>
       Forall(Iff(Member(0,succ(B)),
                  Exists(And(Member(0,succ(succ(r))),
                             And(Member(1,succ(succ(A))),
                                 pair_fm(1,succ(succ(x)),0))))))"


lemma pred_set_type [TC]:
     "\<lbrakk>A \<in> nat; x \<in> nat; r \<in> nat; B \<in> nat\<rbrakk>
      \<Longrightarrow> pred_set_fm(A,x,r,B) \<in> formula"
by (simp add: pred_set_fm_def)

lemma sats_pred_set_fm [simp]:
   "\<lbrakk>U \<in> nat; x \<in> nat; r \<in> nat; B \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, pred_set_fm(U,x,r,B), env) \<longleftrightarrow>
        pred_set(##A, nth(U,env), nth(x,env), nth(r,env), nth(B,env))"
by (simp add: pred_set_fm_def pred_set_def)

lemma pred_set_iff_sats:
      "\<lbrakk>nth(i,env) = U; nth(j,env) = x; nth(k,env) = r; nth(l,env) = B;
          i \<in> nat; j \<in> nat; k \<in> nat; l \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> pred_set(##A,U,x,r,B) \<longleftrightarrow> sats(A, pred_set_fm(i,j,k,l), env)"
by (simp)

theorem pred_set_reflection:
     "REFLECTS[\<lambda>x. pred_set(L,f(x),g(x),h(x),b(x)),
               \<lambda>i x. pred_set(##Lset(i),f(x),g(x),h(x),b(x))]"
apply (simp only: pred_set_def)
apply (intro FOL_reflections pair_reflection)
done



subsubsection\<open>Domain of a Relation, Internalized\<close>

(* "is_domain(M,r,z) \<equiv>
        \<forall>x[M]. (x \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r \<and> (\<exists>y[M]. pair(M,x,y,w))))" *)
definition
  domain_fm :: "[i,i]\<Rightarrow>i" where
    "domain_fm(r,z) \<equiv>
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(pair_fm(2,0,1))))))"

lemma domain_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> domain_fm(x,y) \<in> formula"
by (simp add: domain_fm_def)

lemma sats_domain_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, domain_fm(x,y), env) \<longleftrightarrow>
        is_domain(##A, nth(x,env), nth(y,env))"
by (simp add: domain_fm_def is_domain_def)

lemma domain_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_domain(##A, x, y) \<longleftrightarrow> sats(A, domain_fm(i,j), env)"
by simp

theorem domain_reflection:
     "REFLECTS[\<lambda>x. is_domain(L,f(x),g(x)),
               \<lambda>i x. is_domain(##Lset(i),f(x),g(x))]"
apply (simp only: is_domain_def)
apply (intro FOL_reflections pair_reflection)
done


subsubsection\<open>Range of a Relation, Internalized\<close>

(* "is_range(M,r,z) \<equiv>
        \<forall>y[M]. (y \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r \<and> (\<exists>x[M]. pair(M,x,y,w))))" *)
definition
  range_fm :: "[i,i]\<Rightarrow>i" where
    "range_fm(r,z) \<equiv>
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(pair_fm(0,2,1))))))"

lemma range_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> range_fm(x,y) \<in> formula"
by (simp add: range_fm_def)

lemma sats_range_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, range_fm(x,y), env) \<longleftrightarrow>
        is_range(##A, nth(x,env), nth(y,env))"
by (simp add: range_fm_def is_range_def)

lemma range_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_range(##A, x, y) \<longleftrightarrow> sats(A, range_fm(i,j), env)"
by simp

theorem range_reflection:
     "REFLECTS[\<lambda>x. is_range(L,f(x),g(x)),
               \<lambda>i x. is_range(##Lset(i),f(x),g(x))]"
apply (simp only: is_range_def)
apply (intro FOL_reflections pair_reflection)
done


subsubsection\<open>Field of a Relation, Internalized\<close>

(* "is_field(M,r,z) \<equiv>
        \<exists>dr[M]. is_domain(M,r,dr) \<and>
            (\<exists>rr[M]. is_range(M,r,rr) \<and> union(M,dr,rr,z))" *)
definition
  field_fm :: "[i,i]\<Rightarrow>i" where
    "field_fm(r,z) \<equiv>
       Exists(And(domain_fm(succ(r),0),
              Exists(And(range_fm(succ(succ(r)),0),
                         union_fm(1,0,succ(succ(z)))))))"

lemma field_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> field_fm(x,y) \<in> formula"
by (simp add: field_fm_def)

lemma sats_field_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, field_fm(x,y), env) \<longleftrightarrow>
        is_field(##A, nth(x,env), nth(y,env))"
by (simp add: field_fm_def is_field_def)

lemma field_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_field(##A, x, y) \<longleftrightarrow> sats(A, field_fm(i,j), env)"
by simp

theorem field_reflection:
     "REFLECTS[\<lambda>x. is_field(L,f(x),g(x)),
               \<lambda>i x. is_field(##Lset(i),f(x),g(x))]"
apply (simp only: is_field_def)
apply (intro FOL_reflections domain_reflection range_reflection
             union_reflection)
done


subsubsection\<open>Image under a Relation, Internalized\<close>

(* "image(M,r,A,z) \<equiv>
        \<forall>y[M]. (y \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r \<and> (\<exists>x[M]. x\<in>A \<and> pair(M,x,y,w))))" *)
definition
  image_fm :: "[i,i,i]\<Rightarrow>i" where
    "image_fm(r,A,z) \<equiv>
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
                                        pair_fm(0,2,1)))))))"

lemma image_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> image_fm(x,y,z) \<in> formula"
by (simp add: image_fm_def)

lemma sats_image_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, image_fm(x,y,z), env) \<longleftrightarrow>
        image(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: image_fm_def Relative.image_def)

lemma image_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> image(##A, x, y, z) \<longleftrightarrow> sats(A, image_fm(i,j,k), env)"
by (simp)

theorem image_reflection:
     "REFLECTS[\<lambda>x. image(L,f(x),g(x),h(x)),
               \<lambda>i x. image(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: Relative.image_def)
apply (intro FOL_reflections pair_reflection)
done


subsubsection\<open>Pre-Image under a Relation, Internalized\<close>

(* "pre_image(M,r,A,z) \<equiv>
        \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r \<and> (\<exists>y[M]. y\<in>A \<and> pair(M,x,y,w)))" *)
definition
  pre_image_fm :: "[i,i,i]\<Rightarrow>i" where
    "pre_image_fm(r,A,z) \<equiv>
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
                                        pair_fm(2,0,1)))))))"

lemma pre_image_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> pre_image_fm(x,y,z) \<in> formula"
by (simp add: pre_image_fm_def)

lemma sats_pre_image_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, pre_image_fm(x,y,z), env) \<longleftrightarrow>
        pre_image(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: pre_image_fm_def Relative.pre_image_def)

lemma pre_image_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> pre_image(##A, x, y, z) \<longleftrightarrow> sats(A, pre_image_fm(i,j,k), env)"
by (simp)

theorem pre_image_reflection:
     "REFLECTS[\<lambda>x. pre_image(L,f(x),g(x),h(x)),
               \<lambda>i x. pre_image(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: Relative.pre_image_def)
apply (intro FOL_reflections pair_reflection)
done


subsubsection\<open>Function Application, Internalized\<close>

(* "fun_apply(M,f,x,y) \<equiv>
        (\<exists>xs[M]. \<exists>fxs[M].
         upair(M,x,x,xs) \<and> image(M,f,xs,fxs) \<and> big_union(M,fxs,y))" *)
definition
  fun_apply_fm :: "[i,i,i]\<Rightarrow>i" where
    "fun_apply_fm(f,x,y) \<equiv>
       Exists(Exists(And(upair_fm(succ(succ(x)), succ(succ(x)), 1),
                         And(image_fm(succ(succ(f)), 1, 0),
                             big_union_fm(0,succ(succ(y)))))))"

lemma fun_apply_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> fun_apply_fm(x,y,z) \<in> formula"
by (simp add: fun_apply_fm_def)

lemma sats_fun_apply_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, fun_apply_fm(x,y,z), env) \<longleftrightarrow>
        fun_apply(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: fun_apply_fm_def fun_apply_def)

lemma fun_apply_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> fun_apply(##A, x, y, z) \<longleftrightarrow> sats(A, fun_apply_fm(i,j,k), env)"
by simp

theorem fun_apply_reflection:
     "REFLECTS[\<lambda>x. fun_apply(L,f(x),g(x),h(x)),
               \<lambda>i x. fun_apply(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: fun_apply_def)
apply (intro FOL_reflections upair_reflection image_reflection
             big_union_reflection)
done


subsubsection\<open>The Concept of Relation, Internalized\<close>

(* "is_relation(M,r) \<equiv>
        (\<forall>z[M]. z\<in>r \<longrightarrow> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,z)))" *)
definition
  relation_fm :: "i\<Rightarrow>i" where
    "relation_fm(r) \<equiv>
       Forall(Implies(Member(0,succ(r)), Exists(Exists(pair_fm(1,0,2)))))"

lemma relation_type [TC]:
     "\<lbrakk>x \<in> nat\<rbrakk> \<Longrightarrow> relation_fm(x) \<in> formula"
by (simp add: relation_fm_def)

lemma sats_relation_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, relation_fm(x), env) \<longleftrightarrow> is_relation(##A, nth(x,env))"
by (simp add: relation_fm_def is_relation_def)

lemma relation_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_relation(##A, x) \<longleftrightarrow> sats(A, relation_fm(i), env)"
by simp

theorem is_relation_reflection:
     "REFLECTS[\<lambda>x. is_relation(L,f(x)),
               \<lambda>i x. is_relation(##Lset(i),f(x))]"
apply (simp only: is_relation_def)
apply (intro FOL_reflections pair_reflection)
done


subsubsection\<open>The Concept of Function, Internalized\<close>

(* "is_function(M,r) \<equiv>
        \<forall>x[M]. \<forall>y[M]. \<forall>y'[M]. \<forall>p[M]. \<forall>p'[M].
           pair(M,x,y,p) \<longrightarrow> pair(M,x,y',p') \<longrightarrow> p\<in>r \<longrightarrow> p'\<in>r \<longrightarrow> y=y'" *)
definition
  function_fm :: "i\<Rightarrow>i" where
    "function_fm(r) \<equiv>
       Forall(Forall(Forall(Forall(Forall(
         Implies(pair_fm(4,3,1),
                 Implies(pair_fm(4,2,0),
                         Implies(Member(1,r#+5),
                                 Implies(Member(0,r#+5), Equal(3,2))))))))))"

lemma function_type [TC]:
     "\<lbrakk>x \<in> nat\<rbrakk> \<Longrightarrow> function_fm(x) \<in> formula"
by (simp add: function_fm_def)

lemma sats_function_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, function_fm(x), env) \<longleftrightarrow> is_function(##A, nth(x,env))"
by (simp add: function_fm_def is_function_def)

lemma is_function_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_function(##A, x) \<longleftrightarrow> sats(A, function_fm(i), env)"
by simp

theorem is_function_reflection:
     "REFLECTS[\<lambda>x. is_function(L,f(x)),
               \<lambda>i x. is_function(##Lset(i),f(x))]"
apply (simp only: is_function_def)
apply (intro FOL_reflections pair_reflection)
done


subsubsection\<open>Typed Functions, Internalized\<close>

(* "typed_function(M,A,B,r) \<equiv>
        is_function(M,r) \<and> is_relation(M,r) \<and> is_domain(M,r,A) \<and>
        (\<forall>u[M]. u\<in>r \<longrightarrow> (\<forall>x[M]. \<forall>y[M]. pair(M,x,y,u) \<longrightarrow> y\<in>B))" *)

definition
  typed_function_fm :: "[i,i,i]\<Rightarrow>i" where
    "typed_function_fm(A,B,r) \<equiv>
       And(function_fm(r),
         And(relation_fm(r),
           And(domain_fm(r,A),
             Forall(Implies(Member(0,succ(r)),
                  Forall(Forall(Implies(pair_fm(1,0,2),Member(0,B#+3)))))))))"

lemma typed_function_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> typed_function_fm(x,y,z) \<in> formula"
by (simp add: typed_function_fm_def)

lemma sats_typed_function_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, typed_function_fm(x,y,z), env) \<longleftrightarrow>
        typed_function(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: typed_function_fm_def typed_function_def)

lemma typed_function_iff_sats:
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> typed_function(##A, x, y, z) \<longleftrightarrow> sats(A, typed_function_fm(i,j,k), env)"
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
        big_union_iff_sats cons_iff_sats successor_iff_sats
        fun_apply_iff_sats  Memrel_iff_sats
        pred_set_iff_sats domain_iff_sats range_iff_sats field_iff_sats
        image_iff_sats pre_image_iff_sats
        relation_iff_sats is_function_iff_sats


theorem typed_function_reflection:
     "REFLECTS[\<lambda>x. typed_function(L,f(x),g(x),h(x)),
               \<lambda>i x. typed_function(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: typed_function_def)
apply (intro FOL_reflections function_reflections)
done


subsubsection\<open>Composition of Relations, Internalized\<close>

(* "composition(M,r,s,t) \<equiv>
        \<forall>p[M]. p \<in> t \<longleftrightarrow>
               (\<exists>x[M]. \<exists>y[M]. \<exists>z[M]. \<exists>xy[M]. \<exists>yz[M].
                pair(M,x,z,p) \<and> pair(M,x,y,xy) \<and> pair(M,y,z,yz) \<and>
                xy \<in> s \<and> yz \<in> r)" *)
definition
  composition_fm :: "[i,i,i]\<Rightarrow>i" where
  "composition_fm(r,s,t) \<equiv>
     Forall(Iff(Member(0,succ(t)),
             Exists(Exists(Exists(Exists(Exists(
              And(pair_fm(4,2,5),
               And(pair_fm(4,3,1),
                And(pair_fm(3,2,0),
                 And(Member(1,s#+6), Member(0,r#+6))))))))))))"

lemma composition_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> composition_fm(x,y,z) \<in> formula"
by (simp add: composition_fm_def)

lemma sats_composition_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, composition_fm(x,y,z), env) \<longleftrightarrow>
        composition(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: composition_fm_def composition_def)

lemma composition_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> composition(##A, x, y, z) \<longleftrightarrow> sats(A, composition_fm(i,j,k), env)"
by simp

theorem composition_reflection:
     "REFLECTS[\<lambda>x. composition(L,f(x),g(x),h(x)),
               \<lambda>i x. composition(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: composition_def)
apply (intro FOL_reflections pair_reflection)
done


subsubsection\<open>Injections, Internalized\<close>

(* "injection(M,A,B,f) \<equiv>
        typed_function(M,A,B,f) \<and>
        (\<forall>x[M]. \<forall>x'[M]. \<forall>y[M]. \<forall>p[M]. \<forall>p'[M].
          pair(M,x,y,p) \<longrightarrow> pair(M,x',y,p') \<longrightarrow> p\<in>f \<longrightarrow> p'\<in>f \<longrightarrow> x=x')" *)
definition
  injection_fm :: "[i,i,i]\<Rightarrow>i" where
  "injection_fm(A,B,f) \<equiv>
    And(typed_function_fm(A,B,f),
       Forall(Forall(Forall(Forall(Forall(
         Implies(pair_fm(4,2,1),
                 Implies(pair_fm(3,2,0),
                         Implies(Member(1,f#+5),
                                 Implies(Member(0,f#+5), Equal(4,3)))))))))))"


lemma injection_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> injection_fm(x,y,z) \<in> formula"
by (simp add: injection_fm_def)

lemma sats_injection_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, injection_fm(x,y,z), env) \<longleftrightarrow>
        injection(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: injection_fm_def injection_def)

lemma injection_iff_sats:
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> injection(##A, x, y, z) \<longleftrightarrow> sats(A, injection_fm(i,j,k), env)"
by simp

theorem injection_reflection:
     "REFLECTS[\<lambda>x. injection(L,f(x),g(x),h(x)),
               \<lambda>i x. injection(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: injection_def)
apply (intro FOL_reflections function_reflections typed_function_reflection)
done


subsubsection\<open>Surjections, Internalized\<close>

(*  surjection :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o"
    "surjection(M,A,B,f) \<equiv>
        typed_function(M,A,B,f) \<and>
        (\<forall>y[M]. y\<in>B \<longrightarrow> (\<exists>x[M]. x\<in>A \<and> fun_apply(M,f,x,y)))" *)
definition
  surjection_fm :: "[i,i,i]\<Rightarrow>i" where
  "surjection_fm(A,B,f) \<equiv>
    And(typed_function_fm(A,B,f),
       Forall(Implies(Member(0,succ(B)),
                      Exists(And(Member(0,succ(succ(A))),
                                 fun_apply_fm(succ(succ(f)),0,1))))))"

lemma surjection_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> surjection_fm(x,y,z) \<in> formula"
by (simp add: surjection_fm_def)

lemma sats_surjection_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, surjection_fm(x,y,z), env) \<longleftrightarrow>
        surjection(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: surjection_fm_def surjection_def)

lemma surjection_iff_sats:
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> surjection(##A, x, y, z) \<longleftrightarrow> sats(A, surjection_fm(i,j,k), env)"
by simp

theorem surjection_reflection:
     "REFLECTS[\<lambda>x. surjection(L,f(x),g(x),h(x)),
               \<lambda>i x. surjection(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: surjection_def)
apply (intro FOL_reflections function_reflections typed_function_reflection)
done



subsubsection\<open>Bijections, Internalized\<close>

(*   bijection :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o"
    "bijection(M,A,B,f) \<equiv> injection(M,A,B,f) \<and> surjection(M,A,B,f)" *)
definition
  bijection_fm :: "[i,i,i]\<Rightarrow>i" where
  "bijection_fm(A,B,f) \<equiv> And(injection_fm(A,B,f), surjection_fm(A,B,f))"

lemma bijection_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> bijection_fm(x,y,z) \<in> formula"
by (simp add: bijection_fm_def)

lemma sats_bijection_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, bijection_fm(x,y,z), env) \<longleftrightarrow>
        bijection(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: bijection_fm_def bijection_def)

lemma bijection_iff_sats:
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> bijection(##A, x, y, z) \<longleftrightarrow> sats(A, bijection_fm(i,j,k), env)"
by simp

theorem bijection_reflection:
     "REFLECTS[\<lambda>x. bijection(L,f(x),g(x),h(x)),
               \<lambda>i x. bijection(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: bijection_def)
apply (intro And_reflection injection_reflection surjection_reflection)
done


subsubsection\<open>Restriction of a Relation, Internalized\<close>


(* "restriction(M,r,A,z) \<equiv>
        \<forall>x[M]. x \<in> z \<longleftrightarrow> (x \<in> r \<and> (\<exists>u[M]. u\<in>A \<and> (\<exists>v[M]. pair(M,u,v,x))))" *)
definition
  restriction_fm :: "[i,i,i]\<Rightarrow>i" where
    "restriction_fm(r,A,z) \<equiv>
       Forall(Iff(Member(0,succ(z)),
                  And(Member(0,succ(r)),
                      Exists(And(Member(0,succ(succ(A))),
                                 Exists(pair_fm(1,0,2)))))))"

lemma restriction_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> restriction_fm(x,y,z) \<in> formula"
by (simp add: restriction_fm_def)

lemma sats_restriction_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, restriction_fm(x,y,z), env) \<longleftrightarrow>
        restriction(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: restriction_fm_def restriction_def)

lemma restriction_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> restriction(##A, x, y, z) \<longleftrightarrow> sats(A, restriction_fm(i,j,k), env)"
by simp

theorem restriction_reflection:
     "REFLECTS[\<lambda>x. restriction(L,f(x),g(x),h(x)),
               \<lambda>i x. restriction(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: restriction_def)
apply (intro FOL_reflections pair_reflection)
done

subsubsection\<open>Order-Isomorphisms, Internalized\<close>

(*  order_isomorphism :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o"
   "order_isomorphism(M,A,r,B,s,f) \<equiv>
        bijection(M,A,B,f) \<and>
        (\<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. y\<in>A \<longrightarrow>
          (\<forall>p[M]. \<forall>fx[M]. \<forall>fy[M]. \<forall>q[M].
            pair(M,x,y,p) \<longrightarrow> fun_apply(M,f,x,fx) \<longrightarrow> fun_apply(M,f,y,fy) \<longrightarrow>
            pair(M,fx,fy,q) \<longrightarrow> (p\<in>r \<longleftrightarrow> q\<in>s))))"
  *)

definition
  order_isomorphism_fm :: "[i,i,i,i,i]\<Rightarrow>i" where
 "order_isomorphism_fm(A,r,B,s,f) \<equiv>
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
     "\<lbrakk>A \<in> nat; r \<in> nat; B \<in> nat; s \<in> nat; f \<in> nat\<rbrakk>
      \<Longrightarrow> order_isomorphism_fm(A,r,B,s,f) \<in> formula"
by (simp add: order_isomorphism_fm_def)

lemma sats_order_isomorphism_fm [simp]:
   "\<lbrakk>U \<in> nat; r \<in> nat; B \<in> nat; s \<in> nat; f \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, order_isomorphism_fm(U,r,B,s,f), env) \<longleftrightarrow>
        order_isomorphism(##A, nth(U,env), nth(r,env), nth(B,env),
                               nth(s,env), nth(f,env))"
by (simp add: order_isomorphism_fm_def order_isomorphism_def)

lemma order_isomorphism_iff_sats:
  "\<lbrakk>nth(i,env) = U; nth(j,env) = r; nth(k,env) = B; nth(j',env) = s;
      nth(k',env) = f;
      i \<in> nat; j \<in> nat; k \<in> nat; j' \<in> nat; k' \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> order_isomorphism(##A,U,r,B,s,f) \<longleftrightarrow>
       sats(A, order_isomorphism_fm(i,j,k,j',k'), env)"
by simp

theorem order_isomorphism_reflection:
     "REFLECTS[\<lambda>x. order_isomorphism(L,f(x),g(x),h(x),g'(x),h'(x)),
               \<lambda>i x. order_isomorphism(##Lset(i),f(x),g(x),h(x),g'(x),h'(x))]"
apply (simp only: order_isomorphism_def)
apply (intro FOL_reflections function_reflections bijection_reflection)
done

subsubsection\<open>Limit Ordinals, Internalized\<close>

text\<open>A limit ordinal is a non-empty, successor-closed ordinal\<close>

(* "limit_ordinal(M,a) \<equiv>
        ordinal(M,a) \<and> \<not> empty(M,a) \<and>
        (\<forall>x[M]. x\<in>a \<longrightarrow> (\<exists>y[M]. y\<in>a \<and> successor(M,x,y)))" *)

definition
  limit_ordinal_fm :: "i\<Rightarrow>i" where
    "limit_ordinal_fm(x) \<equiv>
        And(ordinal_fm(x),
            And(Neg(empty_fm(x)),
                Forall(Implies(Member(0,succ(x)),
                               Exists(And(Member(0,succ(succ(x))),
                                          succ_fm(1,0)))))))"

lemma limit_ordinal_type [TC]:
     "x \<in> nat \<Longrightarrow> limit_ordinal_fm(x) \<in> formula"
by (simp add: limit_ordinal_fm_def)

lemma sats_limit_ordinal_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, limit_ordinal_fm(x), env) \<longleftrightarrow> limit_ordinal(##A, nth(x,env))"
by (simp add: limit_ordinal_fm_def limit_ordinal_def sats_ordinal_fm')

lemma limit_ordinal_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> limit_ordinal(##A, x) \<longleftrightarrow> sats(A, limit_ordinal_fm(i), env)"
by simp

theorem limit_ordinal_reflection:
     "REFLECTS[\<lambda>x. limit_ordinal(L,f(x)),
               \<lambda>i x. limit_ordinal(##Lset(i),f(x))]"
apply (simp only: limit_ordinal_def)
apply (intro FOL_reflections ordinal_reflection
             empty_reflection successor_reflection)
done

subsubsection\<open>Finite Ordinals: The Predicate ``Is A Natural Number''\<close>

(*     "finite_ordinal(M,a) \<equiv> 
        ordinal(M,a) \<and> \<not> limit_ordinal(M,a) \<and> 
        (\<forall>x[M]. x\<in>a \<longrightarrow> \<not> limit_ordinal(M,x))" *)
definition
  finite_ordinal_fm :: "i\<Rightarrow>i" where
    "finite_ordinal_fm(x) \<equiv>
       And(ordinal_fm(x),
          And(Neg(limit_ordinal_fm(x)),
           Forall(Implies(Member(0,succ(x)),
                          Neg(limit_ordinal_fm(0))))))"

lemma finite_ordinal_type [TC]:
     "x \<in> nat \<Longrightarrow> finite_ordinal_fm(x) \<in> formula"
by (simp add: finite_ordinal_fm_def)

lemma sats_finite_ordinal_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, finite_ordinal_fm(x), env) \<longleftrightarrow> finite_ordinal(##A, nth(x,env))"
by (simp add: finite_ordinal_fm_def sats_ordinal_fm' finite_ordinal_def)

lemma finite_ordinal_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> finite_ordinal(##A, x) \<longleftrightarrow> sats(A, finite_ordinal_fm(i), env)"
by simp

theorem finite_ordinal_reflection:
     "REFLECTS[\<lambda>x. finite_ordinal(L,f(x)),
               \<lambda>i x. finite_ordinal(##Lset(i),f(x))]"
apply (simp only: finite_ordinal_def)
apply (intro FOL_reflections ordinal_reflection limit_ordinal_reflection)
done


subsubsection\<open>Omega: The Set of Natural Numbers\<close>

(* omega(M,a) \<equiv> limit_ordinal(M,a) \<and> (\<forall>x[M]. x\<in>a \<longrightarrow> \<not> limit_ordinal(M,x)) *)
definition
  omega_fm :: "i\<Rightarrow>i" where
    "omega_fm(x) \<equiv>
       And(limit_ordinal_fm(x),
           Forall(Implies(Member(0,succ(x)),
                          Neg(limit_ordinal_fm(0)))))"

lemma omega_type [TC]:
     "x \<in> nat \<Longrightarrow> omega_fm(x) \<in> formula"
by (simp add: omega_fm_def)

lemma sats_omega_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, omega_fm(x), env) \<longleftrightarrow> omega(##A, nth(x,env))"
by (simp add: omega_fm_def omega_def)

lemma omega_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> omega(##A, x) \<longleftrightarrow> sats(A, omega_fm(i), env)"
by simp

theorem omega_reflection:
     "REFLECTS[\<lambda>x. omega(L,f(x)),
               \<lambda>i x. omega(##Lset(i),f(x))]"
apply (simp only: omega_def)
apply (intro FOL_reflections limit_ordinal_reflection)
done


lemmas fun_plus_reflections =
        typed_function_reflection composition_reflection
        injection_reflection surjection_reflection
        bijection_reflection restriction_reflection
        order_isomorphism_reflection finite_ordinal_reflection 
        ordinal_reflection limit_ordinal_reflection omega_reflection

lemmas fun_plus_iff_sats =
        typed_function_iff_sats composition_iff_sats
        injection_iff_sats surjection_iff_sats
        bijection_iff_sats restriction_iff_sats
        order_isomorphism_iff_sats finite_ordinal_iff_sats
        ordinal_iff_sats limit_ordinal_iff_sats omega_iff_sats

end
