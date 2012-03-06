(*  Title:      ZF/EquivClass.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header{*Equivalence Relations*}

theory EquivClass imports Trancl Perm begin

definition
  quotient   :: "[i,i]=>i"    (infixl "'/'/" 90)  (*set of equiv classes*)  where
      "A//r == {r``{x} . x:A}"

definition
  congruent  :: "[i,i=>i]=>o"  where
      "congruent(r,b) == \<forall>y z. <y,z>:r \<longrightarrow> b(y)=b(z)"

definition
  congruent2 :: "[i,i,[i,i]=>i]=>o"  where
      "congruent2(r1,r2,b) == \<forall>y1 z1 y2 z2.
           <y1,z1>:r1 \<longrightarrow> <y2,z2>:r2 \<longrightarrow> b(y1,y2) = b(z1,z2)"

abbreviation
  RESPECTS ::"[i=>i, i] => o"  (infixr "respects" 80) where
  "f respects r == congruent(r,f)"

abbreviation
  RESPECTS2 ::"[i=>i=>i, i] => o"  (infixr "respects2 " 80) where
  "f respects2 r == congruent2(r,r,f)"
    --{*Abbreviation for the common case where the relations are identical*}


subsection{*Suppes, Theorem 70:
    @{term r} is an equiv relation iff @{term "converse(r) O r = r"}*}

(** first half: equiv(A,r) ==> converse(r) O r = r **)

lemma sym_trans_comp_subset:
    "[| sym(r); trans(r) |] ==> converse(r) O r \<subseteq> r"
by (unfold trans_def sym_def, blast)

lemma refl_comp_subset:
    "[| refl(A,r); r \<subseteq> A*A |] ==> r \<subseteq> converse(r) O r"
by (unfold refl_def, blast)

lemma equiv_comp_eq:
    "equiv(A,r) ==> converse(r) O r = r"
apply (unfold equiv_def)
apply (blast del: subsetI intro!: sym_trans_comp_subset refl_comp_subset)
done

(*second half*)
lemma comp_equivI:
    "[| converse(r) O r = r;  domain(r) = A |] ==> equiv(A,r)"
apply (unfold equiv_def refl_def sym_def trans_def)
apply (erule equalityE)
apply (subgoal_tac "\<forall>x y. <x,y> \<in> r \<longrightarrow> <y,x> \<in> r", blast+)
done

(** Equivalence classes **)

(*Lemma for the next result*)
lemma equiv_class_subset:
    "[| sym(r);  trans(r);  <a,b>: r |] ==> r``{a} \<subseteq> r``{b}"
by (unfold trans_def sym_def, blast)

lemma equiv_class_eq:
    "[| equiv(A,r);  <a,b>: r |] ==> r``{a} = r``{b}"
apply (unfold equiv_def)
apply (safe del: subsetI intro!: equalityI equiv_class_subset)
apply (unfold sym_def, blast)
done

lemma equiv_class_self:
    "[| equiv(A,r);  a: A |] ==> a: r``{a}"
by (unfold equiv_def refl_def, blast)

(*Lemma for the next result*)
lemma subset_equiv_class:
    "[| equiv(A,r);  r``{b} \<subseteq> r``{a};  b: A |] ==> <a,b>: r"
by (unfold equiv_def refl_def, blast)

lemma eq_equiv_class: "[| r``{a} = r``{b};  equiv(A,r);  b: A |] ==> <a,b>: r"
by (assumption | rule equalityD2 subset_equiv_class)+

(*thus r``{a} = r``{b} as well*)
lemma equiv_class_nondisjoint:
    "[| equiv(A,r);  x: (r``{a} \<inter> r``{b}) |] ==> <a,b>: r"
by (unfold equiv_def trans_def sym_def, blast)

lemma equiv_type: "equiv(A,r) ==> r \<subseteq> A*A"
by (unfold equiv_def, blast)

lemma equiv_class_eq_iff:
     "equiv(A,r) ==> <x,y>: r <-> r``{x} = r``{y} & x:A & y:A"
by (blast intro: eq_equiv_class equiv_class_eq dest: equiv_type)

lemma eq_equiv_class_iff:
     "[| equiv(A,r);  x: A;  y: A |] ==> r``{x} = r``{y} <-> <x,y>: r"
by (blast intro: eq_equiv_class equiv_class_eq dest: equiv_type)

(*** Quotients ***)

(** Introduction/elimination rules -- needed? **)

lemma quotientI [TC]: "x:A ==> r``{x}: A//r"
apply (unfold quotient_def)
apply (erule RepFunI)
done

lemma quotientE:
    "[| X: A//r;  !!x. [| X = r``{x};  x:A |] ==> P |] ==> P"
by (unfold quotient_def, blast)

lemma Union_quotient:
    "equiv(A,r) ==> \<Union>(A//r) = A"
by (unfold equiv_def refl_def quotient_def, blast)

lemma quotient_disj:
    "[| equiv(A,r);  X: A//r;  Y: A//r |] ==> X=Y | (X \<inter> Y \<subseteq> 0)"
apply (unfold quotient_def)
apply (safe intro!: equiv_class_eq, assumption)
apply (unfold equiv_def trans_def sym_def, blast)
done

subsection{*Defining Unary Operations upon Equivalence Classes*}

(** Could have a locale with the premises equiv(A,r)  and  congruent(r,b)
**)

(*Conversion rule*)
lemma UN_equiv_class:
    "[| equiv(A,r);  b respects r;  a: A |] ==> (\<Union>x\<in>r``{a}. b(x)) = b(a)"
apply (subgoal_tac "\<forall>x \<in> r``{a}. b(x) = b(a)")
 apply simp
 apply (blast intro: equiv_class_self)
apply (unfold equiv_def sym_def congruent_def, blast)
done

(*type checking of  @{term"\<Union>x\<in>r``{a}. b(x)"} *)
lemma UN_equiv_class_type:
    "[| equiv(A,r);  b respects r;  X: A//r;  !!x.  x \<in> A ==> b(x) \<in> B |]
     ==> (\<Union>x\<in>X. b(x)) \<in> B"
apply (unfold quotient_def, safe)
apply (simp (no_asm_simp) add: UN_equiv_class)
done

(*Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; bcong could be !!y. y:A ==> b(y):B
*)
lemma UN_equiv_class_inject:
    "[| equiv(A,r);   b respects r;
        (\<Union>x\<in>X. b(x))=(\<Union>y\<in>Y. b(y));  X: A//r;  Y: A//r;
        !!x y. [| x:A; y:A; b(x)=b(y) |] ==> <x,y>:r |]
     ==> X=Y"
apply (unfold quotient_def, safe)
apply (rule equiv_class_eq, assumption)
apply (simp add: UN_equiv_class [of A r b])
done


subsection{*Defining Binary Operations upon Equivalence Classes*}

lemma congruent2_implies_congruent:
    "[| equiv(A,r1);  congruent2(r1,r2,b);  a: A |] ==> congruent(r2,b(a))"
by (unfold congruent_def congruent2_def equiv_def refl_def, blast)

lemma congruent2_implies_congruent_UN:
    "[| equiv(A1,r1);  equiv(A2,r2);  congruent2(r1,r2,b);  a: A2 |] ==>
     congruent(r1, %x1. \<Union>x2 \<in> r2``{a}. b(x1,x2))"
apply (unfold congruent_def, safe)
apply (frule equiv_type [THEN subsetD], assumption)
apply clarify
apply (simp add: UN_equiv_class congruent2_implies_congruent)
apply (unfold congruent2_def equiv_def refl_def, blast)
done

lemma UN_equiv_class2:
    "[| equiv(A1,r1);  equiv(A2,r2);  congruent2(r1,r2,b);  a1: A1;  a2: A2 |]
     ==> (\<Union>x1 \<in> r1``{a1}. \<Union>x2 \<in> r2``{a2}. b(x1,x2)) = b(a1,a2)"
by (simp add: UN_equiv_class congruent2_implies_congruent
              congruent2_implies_congruent_UN)

(*type checking*)
lemma UN_equiv_class_type2:
    "[| equiv(A,r);  b respects2 r;
        X1: A//r;  X2: A//r;
        !!x1 x2.  [| x1: A; x2: A |] ==> b(x1,x2) \<in> B
     |] ==> (\<Union>x1\<in>X1. \<Union>x2\<in>X2. b(x1,x2)) \<in> B"
apply (unfold quotient_def, safe)
apply (blast intro: UN_equiv_class_type congruent2_implies_congruent_UN
                    congruent2_implies_congruent quotientI)
done


(*Suggested by John Harrison -- the two subproofs may be MUCH simpler
  than the direct proof*)
lemma congruent2I:
    "[|  equiv(A1,r1);  equiv(A2,r2);
        !! y z w. [| w \<in> A2;  <y,z> \<in> r1 |] ==> b(y,w) = b(z,w);
        !! y z w. [| w \<in> A1;  <y,z> \<in> r2 |] ==> b(w,y) = b(w,z)
     |] ==> congruent2(r1,r2,b)"
apply (unfold congruent2_def equiv_def refl_def, safe)
apply (blast intro: trans)
done

lemma congruent2_commuteI:
 assumes equivA: "equiv(A,r)"
     and commute: "!! y z. [| y: A;  z: A |] ==> b(y,z) = b(z,y)"
     and congt:   "!! y z w. [| w: A;  <y,z>: r |] ==> b(w,y) = b(w,z)"
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
    "[| equiv(A,r);  Z: A//r;
        !!w. [| w: A |] ==> congruent(r, %z. b(w,z));
        !!x y. [| x: A;  y: A |] ==> b(y,x) = b(x,y)
     |] ==> congruent(r, %w. \<Union>z\<in>Z. b(w,z))"
apply (simp (no_asm) add: congruent_def)
apply (safe elim!: quotientE)
apply (frule equiv_type [THEN subsetD], assumption)
apply (simp add: UN_equiv_class [of A r])
apply (simp add: congruent_def)
done

end
