(*  Title:      ZF/EquivClass.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Equivalence Relations\<close>

theory EquivClass imports Trancl Perm begin

definition
  quotient   :: "[i,i]\<Rightarrow>i"    (infixl \<open>'/'/\<close> 90)  (*set of equiv classes*)  where
      "A//r \<equiv> {r``{x} . x \<in> A}"

definition
  congruent  :: "[i,i\<Rightarrow>i]\<Rightarrow>o"  where
      "congruent(r,b) \<equiv> \<forall>y z. \<langle>y,z\<rangle>:r \<longrightarrow> b(y)=b(z)"

definition
  congruent2 :: "[i,i,[i,i]\<Rightarrow>i]\<Rightarrow>o"  where
      "congruent2(r1,r2,b) \<equiv> \<forall>y1 z1 y2 z2.
           \<langle>y1,z1\<rangle>:r1 \<longrightarrow> \<langle>y2,z2\<rangle>:r2 \<longrightarrow> b(y1,y2) = b(z1,z2)"

abbreviation
  RESPECTS ::"[i\<Rightarrow>i, i] \<Rightarrow> o"  (infixr \<open>respects\<close> 80) where
  "f respects r \<equiv> congruent(r,f)"

abbreviation
  RESPECTS2 ::"[i\<Rightarrow>i\<Rightarrow>i, i] \<Rightarrow> o"  (infixr \<open>respects2 \<close> 80) where
  "f respects2 r \<equiv> congruent2(r,r,f)"
    \<comment> \<open>Abbreviation for the common case where the relations are identical\<close>


subsection\<open>Suppes, Theorem 70:
    \<^term>\<open>r\<close> is an equiv relation iff \<^term>\<open>converse(r) O r = r\<close>\<close>

(** first half: equiv(A,r) \<Longrightarrow> converse(r) O r = r **)

lemma sym_trans_comp_subset:
    "\<lbrakk>sym(r); trans(r)\<rbrakk> \<Longrightarrow> converse(r) O r \<subseteq> r"
by (unfold trans_def sym_def, blast)

lemma refl_comp_subset:
    "\<lbrakk>refl(A,r); r \<subseteq> A*A\<rbrakk> \<Longrightarrow> r \<subseteq> converse(r) O r"
by (unfold refl_def, blast)

lemma equiv_comp_eq:
    "equiv(A,r) \<Longrightarrow> converse(r) O r = r"
  unfolding equiv_def
apply (blast del: subsetI intro!: sym_trans_comp_subset refl_comp_subset)
done

(*second half*)
lemma comp_equivI:
    "\<lbrakk>converse(r) O r = r;  domain(r) = A\<rbrakk> \<Longrightarrow> equiv(A,r)"
apply (unfold equiv_def refl_def sym_def trans_def)
apply (erule equalityE)
apply (subgoal_tac "\<forall>x y. \<langle>x,y\<rangle> \<in> r \<longrightarrow> \<langle>y,x\<rangle> \<in> r", blast+)
done

(** Equivalence classes **)

(*Lemma for the next result*)
lemma equiv_class_subset:
    "\<lbrakk>sym(r);  trans(r);  \<langle>a,b\<rangle>: r\<rbrakk> \<Longrightarrow> r``{a} \<subseteq> r``{b}"
by (unfold trans_def sym_def, blast)

lemma equiv_class_eq:
    "\<lbrakk>equiv(A,r);  \<langle>a,b\<rangle>: r\<rbrakk> \<Longrightarrow> r``{a} = r``{b}"
  unfolding equiv_def
apply (safe del: subsetI intro!: equalityI equiv_class_subset)
apply (unfold sym_def, blast)
done

lemma equiv_class_self:
    "\<lbrakk>equiv(A,r);  a \<in> A\<rbrakk> \<Longrightarrow> a \<in> r``{a}"
by (unfold equiv_def refl_def, blast)

(*Lemma for the next result*)
lemma subset_equiv_class:
    "\<lbrakk>equiv(A,r);  r``{b} \<subseteq> r``{a};  b \<in> A\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle>: r"
by (unfold equiv_def refl_def, blast)

lemma eq_equiv_class: "\<lbrakk>r``{a} = r``{b};  equiv(A,r);  b \<in> A\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle>: r"
by (assumption | rule equalityD2 subset_equiv_class)+

(*thus r``{a} = r``{b} as well*)
lemma equiv_class_nondisjoint:
    "\<lbrakk>equiv(A,r);  x: (r``{a} \<inter> r``{b})\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle>: r"
by (unfold equiv_def trans_def sym_def, blast)

lemma equiv_type: "equiv(A,r) \<Longrightarrow> r \<subseteq> A*A"
by (unfold equiv_def, blast)

lemma equiv_class_eq_iff:
     "equiv(A,r) \<Longrightarrow> \<langle>x,y\<rangle>: r \<longleftrightarrow> r``{x} = r``{y} \<and> x \<in> A \<and> y \<in> A"
by (blast intro: eq_equiv_class equiv_class_eq dest: equiv_type)

lemma eq_equiv_class_iff:
     "\<lbrakk>equiv(A,r);  x \<in> A;  y \<in> A\<rbrakk> \<Longrightarrow> r``{x} = r``{y} \<longleftrightarrow> \<langle>x,y\<rangle>: r"
by (blast intro: eq_equiv_class equiv_class_eq dest: equiv_type)

(*** Quotients ***)

(** Introduction/elimination rules -- needed? **)

lemma quotientI [TC]: "x \<in> A \<Longrightarrow> r``{x}: A//r"
  unfolding quotient_def
apply (erule RepFunI)
done

lemma quotientE:
    "\<lbrakk>X \<in> A//r;  \<And>x. \<lbrakk>X = r``{x};  x \<in> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (unfold quotient_def, blast)

lemma Union_quotient:
    "equiv(A,r) \<Longrightarrow> \<Union>(A//r) = A"
by (unfold equiv_def refl_def quotient_def, blast)

lemma quotient_disj:
    "\<lbrakk>equiv(A,r);  X \<in> A//r;  Y \<in> A//r\<rbrakk> \<Longrightarrow> X=Y | (X \<inter> Y \<subseteq> 0)"
  unfolding quotient_def
apply (safe intro!: equiv_class_eq, assumption)
apply (unfold equiv_def trans_def sym_def, blast)
done

subsection\<open>Defining Unary Operations upon Equivalence Classes\<close>

(** Could have a locale with the premises equiv(A,r)  and  congruent(r,b)
**)

(*Conversion rule*)
lemma UN_equiv_class:
    "\<lbrakk>equiv(A,r);  b respects r;  a \<in> A\<rbrakk> \<Longrightarrow> (\<Union>x\<in>r``{a}. b(x)) = b(a)"
apply (subgoal_tac "\<forall>x \<in> r``{a}. b(x) = b(a)")
 apply simp
 apply (blast intro: equiv_class_self)
apply (unfold equiv_def sym_def congruent_def, blast)
done

(*type checking of  @{term"\<Union>x\<in>r``{a}. b(x)"} *)
lemma UN_equiv_class_type:
    "\<lbrakk>equiv(A,r);  b respects r;  X \<in> A//r;  \<And>x.  x \<in> A \<Longrightarrow> b(x) \<in> B\<rbrakk>
     \<Longrightarrow> (\<Union>x\<in>X. b(x)) \<in> B"
apply (unfold quotient_def, safe)
apply (simp (no_asm_simp) add: UN_equiv_class)
done

(*Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; bcong could be \<And>y. y \<in> A \<Longrightarrow> b(y):B
*)
lemma UN_equiv_class_inject:
    "\<lbrakk>equiv(A,r);   b respects r;
        (\<Union>x\<in>X. b(x))=(\<Union>y\<in>Y. b(y));  X \<in> A//r;  Y \<in> A//r;
        \<And>x y. \<lbrakk>x \<in> A; y \<in> A; b(x)=b(y)\<rbrakk> \<Longrightarrow> \<langle>x,y\<rangle>:r\<rbrakk>
     \<Longrightarrow> X=Y"
apply (unfold quotient_def, safe)
apply (rule equiv_class_eq, assumption)
apply (simp add: UN_equiv_class [of A r b])
done


subsection\<open>Defining Binary Operations upon Equivalence Classes\<close>

lemma congruent2_implies_congruent:
    "\<lbrakk>equiv(A,r1);  congruent2(r1,r2,b);  a \<in> A\<rbrakk> \<Longrightarrow> congruent(r2,b(a))"
by (unfold congruent_def congruent2_def equiv_def refl_def, blast)

lemma congruent2_implies_congruent_UN:
    "\<lbrakk>equiv(A1,r1);  equiv(A2,r2);  congruent2(r1,r2,b);  a \<in> A2\<rbrakk> \<Longrightarrow>
     congruent(r1, \<lambda>x1. \<Union>x2 \<in> r2``{a}. b(x1,x2))"
apply (unfold congruent_def, safe)
apply (frule equiv_type [THEN subsetD], assumption)
apply clarify
apply (simp add: UN_equiv_class congruent2_implies_congruent)
apply (unfold congruent2_def equiv_def refl_def, blast)
done

lemma UN_equiv_class2:
    "\<lbrakk>equiv(A1,r1);  equiv(A2,r2);  congruent2(r1,r2,b);  a1: A1;  a2: A2\<rbrakk>
     \<Longrightarrow> (\<Union>x1 \<in> r1``{a1}. \<Union>x2 \<in> r2``{a2}. b(x1,x2)) = b(a1,a2)"
by (simp add: UN_equiv_class congruent2_implies_congruent
              congruent2_implies_congruent_UN)

(*type checking*)
lemma UN_equiv_class_type2:
    "\<lbrakk>equiv(A,r);  b respects2 r;
        X1: A//r;  X2: A//r;
        \<And>x1 x2.  \<lbrakk>x1: A; x2: A\<rbrakk> \<Longrightarrow> b(x1,x2) \<in> B
\<rbrakk> \<Longrightarrow> (\<Union>x1\<in>X1. \<Union>x2\<in>X2. b(x1,x2)) \<in> B"
apply (unfold quotient_def, safe)
apply (blast intro: UN_equiv_class_type congruent2_implies_congruent_UN
                    congruent2_implies_congruent quotientI)
done


(*Suggested by John Harrison -- the two subproofs may be MUCH simpler
  than the direct proof*)
lemma congruent2I:
    "\<lbrakk>equiv(A1,r1);  equiv(A2,r2);
        \<And>y z w. \<lbrakk>w \<in> A2;  \<langle>y,z\<rangle> \<in> r1\<rbrakk> \<Longrightarrow> b(y,w) = b(z,w);
        \<And>y z w. \<lbrakk>w \<in> A1;  \<langle>y,z\<rangle> \<in> r2\<rbrakk> \<Longrightarrow> b(w,y) = b(w,z)
\<rbrakk> \<Longrightarrow> congruent2(r1,r2,b)"
apply (unfold congruent2_def equiv_def refl_def, safe)
apply (blast intro: trans)
done

lemma congruent2_commuteI:
 assumes equivA: "equiv(A,r)"
     and commute: "\<And>y z. \<lbrakk>y \<in> A;  z \<in> A\<rbrakk> \<Longrightarrow> b(y,z) = b(z,y)"
     and congt:   "\<And>y z w. \<lbrakk>w \<in> A;  \<langle>y,z\<rangle>: r\<rbrakk> \<Longrightarrow> b(w,y) = b(w,z)"
 shows "b respects2 r"
apply (insert equivA [THEN equiv_type, THEN subsetD])
apply (rule congruent2I [OF equivA equivA])
apply (rule commute [THEN trans])
apply (rule_tac [3] commute [THEN trans, symmetric])
apply (rule_tac [5] sym)
apply (blast intro: congt)+
done

(*Obsolete?*)
lemma congruent_commuteI:
    "\<lbrakk>equiv(A,r);  Z \<in> A//r;
        \<And>w. \<lbrakk>w \<in> A\<rbrakk> \<Longrightarrow> congruent(r, \<lambda>z. b(w,z));
        \<And>x y. \<lbrakk>x \<in> A;  y \<in> A\<rbrakk> \<Longrightarrow> b(y,x) = b(x,y)
\<rbrakk> \<Longrightarrow> congruent(r, \<lambda>w. \<Union>z\<in>Z. b(w,z))"
apply (simp (no_asm) add: congruent_def)
apply (safe elim!: quotientE)
apply (frule equiv_type [THEN subsetD], assumption)
apply (simp add: UN_equiv_class [of A r])
apply (simp add: congruent_def)
done

end
