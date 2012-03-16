(*  Title:      ZF/Constructible/Normal.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header {*Closed Unbounded Classes and Normal Functions*}

theory Normal imports Main begin

text{*
One source is the book

Frank R. Drake.
\emph{Set Theory: An Introduction to Large Cardinals}.
North-Holland, 1974.
*}


subsection {*Closed and Unbounded (c.u.) Classes of Ordinals*}

definition
  Closed :: "(i=>o) => o" where
    "Closed(P) == \<forall>I. I \<noteq> 0 \<longrightarrow> (\<forall>i\<in>I. Ord(i) \<and> P(i)) \<longrightarrow> P(\<Union>(I))"

definition
  Unbounded :: "(i=>o) => o" where
    "Unbounded(P) == \<forall>i. Ord(i) \<longrightarrow> (\<exists>j. i<j \<and> P(j))"

definition
  Closed_Unbounded :: "(i=>o) => o" where
    "Closed_Unbounded(P) == Closed(P) \<and> Unbounded(P)"


subsubsection{*Simple facts about c.u. classes*}

lemma ClosedI:
     "[| !!I. [| I \<noteq> 0; \<forall>i\<in>I. Ord(i) \<and> P(i) |] ==> P(\<Union>(I)) |] 
      ==> Closed(P)"
by (simp add: Closed_def)

lemma ClosedD:
     "[| Closed(P); I \<noteq> 0; !!i. i\<in>I ==> Ord(i); !!i. i\<in>I ==> P(i) |] 
      ==> P(\<Union>(I))"
by (simp add: Closed_def)

lemma UnboundedD:
     "[| Unbounded(P);  Ord(i) |] ==> \<exists>j. i<j \<and> P(j)"
by (simp add: Unbounded_def)

lemma Closed_Unbounded_imp_Unbounded: "Closed_Unbounded(C) ==> Unbounded(C)"
by (simp add: Closed_Unbounded_def) 


text{*The universal class, V, is closed and unbounded.
      A bit odd, since C. U. concerns only ordinals, but it's used below!*}
theorem Closed_Unbounded_V [simp]: "Closed_Unbounded(\<lambda>x. True)"
by (unfold Closed_Unbounded_def Closed_def Unbounded_def, blast)

text{*The class of ordinals, @{term Ord}, is closed and unbounded.*}
theorem Closed_Unbounded_Ord   [simp]: "Closed_Unbounded(Ord)"
by (unfold Closed_Unbounded_def Closed_def Unbounded_def, blast)

text{*The class of limit ordinals, @{term Limit}, is closed and unbounded.*}
theorem Closed_Unbounded_Limit [simp]: "Closed_Unbounded(Limit)"
apply (simp add: Closed_Unbounded_def Closed_def Unbounded_def Limit_Union, 
       clarify)
apply (rule_tac x="i++nat" in exI)  
apply (blast intro: oadd_lt_self oadd_LimitI Limit_nat Limit_has_0) 
done

text{*The class of cardinals, @{term Card}, is closed and unbounded.*}
theorem Closed_Unbounded_Card  [simp]: "Closed_Unbounded(Card)"
apply (simp add: Closed_Unbounded_def Closed_def Unbounded_def Card_Union)
apply (blast intro: lt_csucc Card_csucc)
done


subsubsection{*The intersection of any set-indexed family of c.u. classes is
      c.u.*}

text{*The constructions below come from Kunen, \emph{Set Theory}, page 78.*}
locale cub_family =
  fixes P and A
  fixes next_greater -- "the next ordinal satisfying class @{term A}"
  fixes sup_greater  -- "sup of those ordinals over all @{term A}"
  assumes closed:    "a\<in>A ==> Closed(P(a))"
      and unbounded: "a\<in>A ==> Unbounded(P(a))"
      and A_non0: "A\<noteq>0"
  defines "next_greater(a,x) == \<mu> y. x<y \<and> P(a,y)"
      and "sup_greater(x) == \<Union>a\<in>A. next_greater(a,x)"
 

text{*Trivial that the intersection is closed.*}
lemma (in cub_family) Closed_INT: "Closed(\<lambda>x. \<forall>i\<in>A. P(i,x))"
by (blast intro: ClosedI ClosedD [OF closed])

text{*All remaining effort goes to show that the intersection is unbounded.*}

lemma (in cub_family) Ord_sup_greater:
     "Ord(sup_greater(x))"
by (simp add: sup_greater_def next_greater_def)

lemma (in cub_family) Ord_next_greater:
     "Ord(next_greater(a,x))"
by (simp add: next_greater_def Ord_Least)

text{*@{term next_greater} works as expected: it returns a larger value
and one that belongs to class @{term "P(a)"}. *}
lemma (in cub_family) next_greater_lemma:
     "[| Ord(x); a\<in>A |] ==> P(a, next_greater(a,x)) \<and> x < next_greater(a,x)"
apply (simp add: next_greater_def)
apply (rule exE [OF UnboundedD [OF unbounded]])
  apply assumption+
apply (blast intro: LeastI2 lt_Ord2) 
done

lemma (in cub_family) next_greater_in_P:
     "[| Ord(x); a\<in>A |] ==> P(a, next_greater(a,x))"
by (blast dest: next_greater_lemma)

lemma (in cub_family) next_greater_gt:
     "[| Ord(x); a\<in>A |] ==> x < next_greater(a,x)"
by (blast dest: next_greater_lemma)

lemma (in cub_family) sup_greater_gt:
     "Ord(x) ==> x < sup_greater(x)"
apply (simp add: sup_greater_def)
apply (insert A_non0)
apply (blast intro: UN_upper_lt next_greater_gt Ord_next_greater)
done

lemma (in cub_family) next_greater_le_sup_greater:
     "a\<in>A ==> next_greater(a,x) \<le> sup_greater(x)"
apply (simp add: sup_greater_def) 
apply (blast intro: UN_upper_le Ord_next_greater)
done

lemma (in cub_family) omega_sup_greater_eq_UN:
     "[| Ord(x); a\<in>A |] 
      ==> sup_greater^\<omega> (x) = 
          (\<Union>n\<in>nat. next_greater(a, sup_greater^n (x)))"
apply (simp add: iterates_omega_def)
apply (rule le_anti_sym)
apply (rule le_implies_UN_le_UN) 
apply (blast intro: leI next_greater_gt Ord_iterates Ord_sup_greater)  
txt{*Opposite bound:
@{subgoals[display,indent=0,margin=65]}
*}
apply (rule UN_least_le) 
apply (blast intro: Ord_UN Ord_iterates Ord_sup_greater)  
apply (rule_tac a="succ(n)" in UN_upper_le)
apply (simp_all add: next_greater_le_sup_greater) 
apply (blast intro: Ord_UN Ord_iterates Ord_sup_greater)  
done

lemma (in cub_family) P_omega_sup_greater:
     "[| Ord(x); a\<in>A |] ==> P(a, sup_greater^\<omega> (x))"
apply (simp add: omega_sup_greater_eq_UN)
apply (rule ClosedD [OF closed]) 
apply (blast intro: ltD, auto)
apply (blast intro: Ord_iterates Ord_next_greater Ord_sup_greater)
apply (blast intro: next_greater_in_P Ord_iterates Ord_sup_greater)
done

lemma (in cub_family) omega_sup_greater_gt:
     "Ord(x) ==> x < sup_greater^\<omega> (x)"
apply (simp add: iterates_omega_def)
apply (rule UN_upper_lt [of 1], simp_all) 
 apply (blast intro: sup_greater_gt) 
apply (blast intro: Ord_UN Ord_iterates Ord_sup_greater)
done

lemma (in cub_family) Unbounded_INT: "Unbounded(\<lambda>x. \<forall>a\<in>A. P(a,x))"
apply (unfold Unbounded_def)  
apply (blast intro!: omega_sup_greater_gt P_omega_sup_greater) 
done

lemma (in cub_family) Closed_Unbounded_INT: 
     "Closed_Unbounded(\<lambda>x. \<forall>a\<in>A. P(a,x))"
by (simp add: Closed_Unbounded_def Closed_INT Unbounded_INT)


theorem Closed_Unbounded_INT:
    "(!!a. a\<in>A ==> Closed_Unbounded(P(a)))
     ==> Closed_Unbounded(\<lambda>x. \<forall>a\<in>A. P(a, x))"
apply (case_tac "A=0", simp)
apply (rule cub_family.Closed_Unbounded_INT [OF cub_family.intro])
apply (simp_all add: Closed_Unbounded_def)
done

lemma Int_iff_INT2:
     "P(x) \<and> Q(x)  \<longleftrightarrow>  (\<forall>i\<in>2. (i=0 \<longrightarrow> P(x)) \<and> (i=1 \<longrightarrow> Q(x)))"
by auto

theorem Closed_Unbounded_Int:
     "[| Closed_Unbounded(P); Closed_Unbounded(Q) |] 
      ==> Closed_Unbounded(\<lambda>x. P(x) \<and> Q(x))"
apply (simp only: Int_iff_INT2)
apply (rule Closed_Unbounded_INT, auto) 
done


subsection {*Normal Functions*} 

definition
  mono_le_subset :: "(i=>i) => o" where
    "mono_le_subset(M) == \<forall>i j. i\<le>j \<longrightarrow> M(i) \<subseteq> M(j)"

definition
  mono_Ord :: "(i=>i) => o" where
    "mono_Ord(F) == \<forall>i j. i<j \<longrightarrow> F(i) < F(j)"

definition
  cont_Ord :: "(i=>i) => o" where
    "cont_Ord(F) == \<forall>l. Limit(l) \<longrightarrow> F(l) = (\<Union>i<l. F(i))"

definition
  Normal :: "(i=>i) => o" where
    "Normal(F) == mono_Ord(F) \<and> cont_Ord(F)"


subsubsection{*Immediate properties of the definitions*}

lemma NormalI:
     "[|!!i j. i<j ==> F(i) < F(j);  !!l. Limit(l) ==> F(l) = (\<Union>i<l. F(i))|]
      ==> Normal(F)"
by (simp add: Normal_def mono_Ord_def cont_Ord_def)

lemma mono_Ord_imp_Ord: "[| Ord(i); mono_Ord(F) |] ==> Ord(F(i))"
apply (auto simp add: mono_Ord_def)
apply (blast intro: lt_Ord) 
done

lemma mono_Ord_imp_mono: "[| i<j; mono_Ord(F) |] ==> F(i) < F(j)"
by (simp add: mono_Ord_def)

lemma Normal_imp_Ord [simp]: "[| Normal(F); Ord(i) |] ==> Ord(F(i))"
by (simp add: Normal_def mono_Ord_imp_Ord) 

lemma Normal_imp_cont: "[| Normal(F); Limit(l) |] ==> F(l) = (\<Union>i<l. F(i))"
by (simp add: Normal_def cont_Ord_def)

lemma Normal_imp_mono: "[| i<j; Normal(F) |] ==> F(i) < F(j)"
by (simp add: Normal_def mono_Ord_def)

lemma Normal_increasing:
  assumes i: "Ord(i)" and F: "Normal(F)" shows"i \<le> F(i)"
using i
proof (induct i rule: trans_induct3)
  case 0 thus ?case by (simp add: subset_imp_le F)
next
  case (succ i) 
  hence "F(i) < F(succ(i))" using F
    by (simp add: Normal_def mono_Ord_def)
  thus ?case using succ.hyps
    by (blast intro: lt_trans1)
next
  case (limit l) 
  hence "l = (\<Union>y<l. y)" 
    by (simp add: Limit_OUN_eq)
  also have "... \<le> (\<Union>y<l. F(y))" using limit
    by (blast intro: ltD le_implies_OUN_le_OUN)
  finally have "l \<le> (\<Union>y<l. F(y))" .
  moreover have "(\<Union>y<l. F(y)) \<le> F(l)" using limit F
    by (simp add: Normal_imp_cont lt_Ord)
  ultimately show ?case
    by (blast intro: le_trans) 
qed


subsubsection{*The class of fixedpoints is closed and unbounded*}

text{*The proof is from Drake, pages 113--114.*}

lemma mono_Ord_imp_le_subset: "mono_Ord(F) ==> mono_le_subset(F)"
apply (simp add: mono_le_subset_def, clarify)
apply (subgoal_tac "F(i)\<le>F(j)", blast dest: le_imp_subset) 
apply (simp add: le_iff) 
apply (blast intro: lt_Ord2 mono_Ord_imp_Ord mono_Ord_imp_mono) 
done

text{*The following equation is taken for granted in any set theory text.*}
lemma cont_Ord_Union:
     "[| cont_Ord(F); mono_le_subset(F); X=0 \<longrightarrow> F(0)=0; \<forall>x\<in>X. Ord(x) |] 
      ==> F(\<Union>(X)) = (\<Union>y\<in>X. F(y))"
apply (frule Ord_set_cases)
apply (erule disjE, force) 
apply (thin_tac "X=0 \<longrightarrow> ?Q", auto)
 txt{*The trival case of @{term "\<Union>X \<in> X"}*}
 apply (rule equalityI, blast intro: Ord_Union_eq_succD) 
 apply (simp add: mono_le_subset_def UN_subset_iff le_subset_iff) 
 apply (blast elim: equalityE)
txt{*The limit case, @{term "Limit(\<Union>X)"}:
@{subgoals[display,indent=0,margin=65]}
*}
apply (simp add: OUN_Union_eq cont_Ord_def)
apply (rule equalityI) 
txt{*First inclusion:*}
 apply (rule UN_least [OF OUN_least])
 apply (simp add: mono_le_subset_def, blast intro: leI) 
txt{*Second inclusion:*}
apply (rule UN_least) 
apply (frule Union_upper_le, blast, blast intro: Ord_Union)
apply (erule leE, drule ltD, elim UnionE)
 apply (simp add: OUnion_def)
 apply blast+
done

lemma Normal_Union:
     "[| X\<noteq>0; \<forall>x\<in>X. Ord(x); Normal(F) |] ==> F(\<Union>(X)) = (\<Union>y\<in>X. F(y))"
apply (simp add: Normal_def) 
apply (blast intro: mono_Ord_imp_le_subset cont_Ord_Union) 
done

lemma Normal_imp_fp_Closed: "Normal(F) ==> Closed(\<lambda>i. F(i) = i)"
apply (simp add: Closed_def ball_conj_distrib, clarify)
apply (frule Ord_set_cases)
apply (auto simp add: Normal_Union)
done


lemma iterates_Normal_increasing:
     "[| n\<in>nat;  x < F(x);  Normal(F) |] 
      ==> F^n (x) < F^(succ(n)) (x)"  
apply (induct n rule: nat_induct)
apply (simp_all add: Normal_imp_mono)
done

lemma Ord_iterates_Normal:
     "[| n\<in>nat;  Normal(F);  Ord(x) |] ==> Ord(F^n (x))"  
by (simp add: Ord_iterates) 

text{*THIS RESULT IS UNUSED*}
lemma iterates_omega_Limit:
     "[| Normal(F);  x < F(x) |] ==> Limit(F^\<omega> (x))"  
apply (frule lt_Ord) 
apply (simp add: iterates_omega_def)
apply (rule increasing_LimitI) 
   --"this lemma is @{thm increasing_LimitI [no_vars]}"
 apply (blast intro: UN_upper_lt [of "1"]   Normal_imp_Ord
                     Ord_UN Ord_iterates lt_imp_0_lt
                     iterates_Normal_increasing, clarify)
apply (rule bexI) 
 apply (blast intro: Ord_in_Ord [OF Ord_iterates_Normal]) 
apply (rule UN_I, erule nat_succI) 
apply (blast intro:  iterates_Normal_increasing Ord_iterates_Normal
                     ltD [OF lt_trans1, OF succ_leI, OF ltI]) 
done

lemma iterates_omega_fixedpoint:
     "[| Normal(F); Ord(a) |] ==> F(F^\<omega> (a)) = F^\<omega> (a)" 
apply (frule Normal_increasing, assumption)
apply (erule leE) 
 apply (simp_all add: iterates_omega_triv [OF sym])  (*for subgoal 2*)
apply (simp add:  iterates_omega_def Normal_Union) 
apply (rule equalityI, force simp add: nat_succI) 
txt{*Opposite inclusion:
@{subgoals[display,indent=0,margin=65]}
*}
apply clarify
apply (rule UN_I, assumption) 
apply (frule iterates_Normal_increasing, assumption, assumption, simp)
apply (blast intro: Ord_trans ltD Ord_iterates_Normal Normal_imp_Ord [of F]) 
done

lemma iterates_omega_increasing:
     "[| Normal(F); Ord(a) |] ==> a \<le> F^\<omega> (a)"   
apply (unfold iterates_omega_def)
apply (rule UN_upper_le [of 0], simp_all)
done

lemma Normal_imp_fp_Unbounded: "Normal(F) ==> Unbounded(\<lambda>i. F(i) = i)"
apply (unfold Unbounded_def, clarify)
apply (rule_tac x="F^\<omega> (succ(i))" in exI)
apply (simp add: iterates_omega_fixedpoint) 
apply (blast intro: lt_trans2 [OF _ iterates_omega_increasing])
done


theorem Normal_imp_fp_Closed_Unbounded: 
     "Normal(F) ==> Closed_Unbounded(\<lambda>i. F(i) = i)"
by (simp add: Closed_Unbounded_def Normal_imp_fp_Closed
              Normal_imp_fp_Unbounded)


subsubsection{*Function @{text normalize}*}

text{*Function @{text normalize} maps a function @{text F} to a 
      normal function that bounds it above.  The result is normal if and
      only if @{text F} is continuous: succ is not bounded above by any 
      normal function, by @{thm [source] Normal_imp_fp_Unbounded}.
*}
definition
  normalize :: "[i=>i, i] => i" where
    "normalize(F,a) == transrec2(a, F(0), \<lambda>x r. F(succ(x)) \<union> succ(r))"


lemma Ord_normalize [simp, intro]:
     "[| Ord(a); !!x. Ord(x) ==> Ord(F(x)) |] ==> Ord(normalize(F, a))"
apply (induct a rule: trans_induct3)
apply (simp_all add: ltD def_transrec2 [OF normalize_def])
done

lemma normalize_increasing:
  assumes ab: "a < b" and F: "!!x. Ord(x) ==> Ord(F(x))"
  shows "normalize(F,a) < normalize(F,b)"
proof -
  { fix x
    have "Ord(b)" using ab by (blast intro: lt_Ord2) 
    hence "x < b \<Longrightarrow> normalize(F,x) < normalize(F,b)"
    proof (induct b arbitrary: x rule: trans_induct3)
      case 0 thus ?case by simp
    next
      case (succ b)
      thus ?case
        by (auto simp add: le_iff def_transrec2 [OF normalize_def] intro: Un_upper2_lt F)
    next
      case (limit l)
      hence sc: "succ(x) < l" 
        by (blast intro: Limit_has_succ) 
      hence "normalize(F,x) < normalize(F,succ(x))" 
        by (blast intro: limit elim: ltE) 
      hence "normalize(F,x) < (\<Union>j<l. normalize(F,j))"
        by (blast intro: OUN_upper_lt lt_Ord F sc) 
      thus ?case using limit
        by (simp add: def_transrec2 [OF normalize_def])
    qed
  } thus ?thesis using ab .
qed

theorem Normal_normalize:
     "(!!x. Ord(x) ==> Ord(F(x))) ==> Normal(normalize(F))"
apply (rule NormalI) 
apply (blast intro!: normalize_increasing)
apply (simp add: def_transrec2 [OF normalize_def])
done

theorem le_normalize:
  assumes a: "Ord(a)" and coF: "cont_Ord(F)" and F: "!!x. Ord(x) ==> Ord(F(x))"
  shows "F(a) \<le> normalize(F,a)"
using a
proof (induct a rule: trans_induct3)
  case 0 thus ?case by (simp add: F def_transrec2 [OF normalize_def])
next
  case (succ a)
  thus ?case
    by (simp add: def_transrec2 [OF normalize_def] Un_upper1_le F )
next
  case (limit l) 
  thus ?case using F coF [unfolded cont_Ord_def]
    by (simp add: def_transrec2 [OF normalize_def] le_implies_OUN_le_OUN ltD) 
qed


subsection {*The Alephs*}
text {*This is the well-known transfinite enumeration of the cardinal 
numbers.*}

definition
  Aleph :: "i => i" where
    "Aleph(a) == transrec2(a, nat, \<lambda>x r. csucc(r))"

notation (xsymbols)
  Aleph  ("\<aleph>_" [90] 90)

lemma Card_Aleph [simp, intro]:
     "Ord(a) ==> Card(Aleph(a))"
apply (erule trans_induct3) 
apply (simp_all add: Card_csucc Card_nat Card_is_Ord
                     def_transrec2 [OF Aleph_def])
done

lemma Aleph_increasing:
  assumes ab: "a < b" shows "Aleph(a) < Aleph(b)"
proof -
  { fix x
    have "Ord(b)" using ab by (blast intro: lt_Ord2) 
    hence "x < b \<Longrightarrow> Aleph(x) < Aleph(b)"
    proof (induct b arbitrary: x rule: trans_induct3)
      case 0 thus ?case by simp
    next
      case (succ b)
      thus ?case
        by (force simp add: le_iff def_transrec2 [OF Aleph_def] 
                  intro: lt_trans lt_csucc Card_is_Ord)
    next
      case (limit l)
      hence sc: "succ(x) < l" 
        by (blast intro: Limit_has_succ) 
      hence "\<aleph> x < (\<Union>j<l. \<aleph>j)" using limit
        by (blast intro: OUN_upper_lt Card_is_Ord ltD lt_Ord)
      thus ?case using limit
        by (simp add: def_transrec2 [OF Aleph_def])
    qed
  } thus ?thesis using ab .
qed

theorem Normal_Aleph: "Normal(Aleph)"
apply (rule NormalI) 
apply (blast intro!: Aleph_increasing)
apply (simp add: def_transrec2 [OF Aleph_def])
done

end
