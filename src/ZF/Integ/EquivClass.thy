(*  Title:      ZF/EquivClass.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

*)

header{*Equivalence Relations*}

theory EquivClass = Trancl + Perm:

constdefs

  quotient   :: "[i,i]=>i"    (infixl "'/'/" 90)  (*set of equiv classes*)
      "A//r == {r``{x} . x:A}"

  congruent  :: "[i,i=>i]=>o"
      "congruent(r,b) == ALL y z. <y,z>:r --> b(y)=b(z)"

  congruent2 :: "[i,[i,i]=>i]=>o"
      "congruent2(r,b) == ALL y1 z1 y2 z2.
           <y1,z1>:r --> <y2,z2>:r --> b(y1,y2) = b(z1,z2)"

subsection{*Suppes, Theorem 70:
    @{term r} is an equiv relation iff @{term "converse(r) O r = r"}*}

(** first half: equiv(A,r) ==> converse(r) O r = r **)

lemma sym_trans_comp_subset:
    "[| sym(r); trans(r) |] ==> converse(r) O r <= r"
apply (unfold trans_def sym_def, blast)
done

lemma refl_comp_subset:
    "[| refl(A,r); r <= A*A |] ==> r <= converse(r) O r"
apply (unfold refl_def, blast)
done

lemma equiv_comp_eq:
    "equiv(A,r) ==> converse(r) O r = r"
apply (unfold equiv_def)
apply (blast del: subsetI
             intro!: sym_trans_comp_subset refl_comp_subset)
done

(*second half*)
lemma comp_equivI:
    "[| converse(r) O r = r;  domain(r) = A |] ==> equiv(A,r)"
apply (unfold equiv_def refl_def sym_def trans_def)
apply (erule equalityE)
apply (subgoal_tac "ALL x y. <x,y> : r --> <y,x> : r", blast+)
done

(** Equivalence classes **)

(*Lemma for the next result*)
lemma equiv_class_subset:
    "[| sym(r);  trans(r);  <a,b>: r |] ==> r``{a} <= r``{b}"
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
    "[| equiv(A,r);  r``{b} <= r``{a};  b: A |] ==> <a,b>: r"
by (unfold equiv_def refl_def, blast)

lemma eq_equiv_class: "[| r``{a} = r``{b};  equiv(A,r);  b: A |] ==> <a,b>: r"
by (assumption | rule equalityD2 subset_equiv_class)+

(*thus r``{a} = r``{b} as well*)
lemma equiv_class_nondisjoint:
    "[| equiv(A,r);  x: (r``{a} Int r``{b}) |] ==> <a,b>: r"
by (unfold equiv_def trans_def sym_def, blast)

lemma equiv_type: "equiv(A,r) ==> r <= A*A"
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
    "equiv(A,r) ==> Union(A//r) = A"
by (unfold equiv_def refl_def quotient_def, blast)

lemma quotient_disj:
    "[| equiv(A,r);  X: A//r;  Y: A//r |] ==> X=Y | (X Int Y <= 0)"
apply (unfold quotient_def)
apply (safe intro!: equiv_class_eq, assumption)
apply (unfold equiv_def trans_def sym_def, blast)
done

subsection{*Defining Unary Operations upon Equivalence Classes*}

(** Could have a locale with the premises equiv(A,r)  and  congruent(r,b)
**)

(*Conversion rule*)
lemma UN_equiv_class:
    "[| equiv(A,r);  congruent(r,b);  a: A |] ==> (UN x:r``{a}. b(x)) = b(a)"
apply (rule trans [OF refl [THEN UN_cong] UN_constant])
apply (erule_tac [2] equiv_class_self)
prefer 2 apply assumption
apply (unfold equiv_def sym_def congruent_def, blast)
done

(*type checking of  UN x:r``{a}. b(x) *)
lemma UN_equiv_class_type:
    "[| equiv(A,r);  congruent(r,b);  X: A//r;  !!x.  x : A ==> b(x) : B |]
     ==> (UN x:X. b(x)) : B"
apply (unfold quotient_def, safe)
apply (simp (no_asm_simp) add: UN_equiv_class)
done

(*Sufficient conditions for injectiveness.  Could weaken premises!
  major premise could be an inclusion; bcong could be !!y. y:A ==> b(y):B
*)
lemma UN_equiv_class_inject:
    "[| equiv(A,r);   congruent(r,b);
        (UN x:X. b(x))=(UN y:Y. b(y));  X: A//r;  Y: A//r;
        !!x y. [| x:A; y:A; b(x)=b(y) |] ==> <x,y>:r |]
     ==> X=Y"
apply (unfold quotient_def, safe)
apply (rule equiv_class_eq, assumption)
apply (rotate_tac -2) 
apply (simp add: UN_equiv_class [of A r b])  
done


subsection{*Defining Binary Operations upon Equivalence Classes*}


lemma congruent2_implies_congruent:
    "[| equiv(A,r);  congruent2(r,b);  a: A |] ==> congruent(r,b(a))"
apply (unfold congruent_def congruent2_def equiv_def refl_def, blast)
done

lemma congruent2_implies_congruent_UN:
    "[| equiv(A,r);  congruent2(r,b);  a: A |] ==>
     congruent(r, %x1. UN x2:r``{a}. b(x1,x2))"
apply (unfold congruent_def, safe)
apply (frule equiv_type [THEN subsetD], assumption)
apply clarify 
apply (simp add: UN_equiv_class [of A r] congruent2_implies_congruent)
apply (unfold congruent2_def equiv_def refl_def, blast)
done

lemma UN_equiv_class2:
    "[| equiv(A,r);  congruent2(r,b);  a1: A;  a2: A |]
     ==> (UN x1:r``{a1}. UN x2:r``{a2}. b(x1,x2)) = b(a1,a2)"
by (simp add: UN_equiv_class [of A r] congruent2_implies_congruent
              congruent2_implies_congruent_UN)

(*type checking*)
lemma UN_equiv_class_type2:
    "[| equiv(A,r);  congruent2(r,b);
        X1: A//r;  X2: A//r;
        !!x1 x2.  [| x1: A; x2: A |] ==> b(x1,x2) : B
     |] ==> (UN x1:X1. UN x2:X2. b(x1,x2)) : B"
apply (unfold quotient_def, safe)
apply (blast intro: UN_equiv_class_type congruent2_implies_congruent_UN 
                    congruent2_implies_congruent quotientI)
done


(*Suggested by John Harrison -- the two subproofs may be MUCH simpler
  than the direct proof*)
lemma congruent2I:
    "[| equiv(A,r);
        !! y z w. [| w: A;  <y,z> : r |] ==> b(y,w) = b(z,w);
        !! y z w. [| w: A;  <y,z> : r |] ==> b(w,y) = b(w,z)
     |] ==> congruent2(r,b)"
apply (unfold congruent2_def equiv_def refl_def, safe)
apply (blast intro: trans) 
done

lemma congruent2_commuteI:
 assumes equivA: "equiv(A,r)"
     and commute: "!! y z. [| y: A;  z: A |] ==> b(y,z) = b(z,y)"
     and congt:   "!! y z w. [| w: A;  <y,z>: r |] ==> b(w,y) = b(w,z)"
 shows "congruent2(r,b)"
apply (insert equivA [THEN equiv_type, THEN subsetD]) 
apply (rule congruent2I [OF equivA])
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
     |] ==> congruent(r, %w. UN z: Z. b(w,z))"
apply (simp (no_asm) add: congruent_def)
apply (safe elim!: quotientE)
apply (frule equiv_type [THEN subsetD], assumption)
apply (simp add: UN_equiv_class [of A r]) 
apply (simp add: congruent_def) 
done

ML
{*
val sym_trans_comp_subset = thm "sym_trans_comp_subset";
val refl_comp_subset = thm "refl_comp_subset";
val equiv_comp_eq = thm "equiv_comp_eq";
val comp_equivI = thm "comp_equivI";
val equiv_class_subset = thm "equiv_class_subset";
val equiv_class_eq = thm "equiv_class_eq";
val equiv_class_self = thm "equiv_class_self";
val subset_equiv_class = thm "subset_equiv_class";
val eq_equiv_class = thm "eq_equiv_class";
val equiv_class_nondisjoint = thm "equiv_class_nondisjoint";
val equiv_type = thm "equiv_type";
val equiv_class_eq_iff = thm "equiv_class_eq_iff";
val eq_equiv_class_iff = thm "eq_equiv_class_iff";
val quotientI = thm "quotientI";
val quotientE = thm "quotientE";
val Union_quotient = thm "Union_quotient";
val quotient_disj = thm "quotient_disj";
val UN_equiv_class = thm "UN_equiv_class";
val UN_equiv_class_type = thm "UN_equiv_class_type";
val UN_equiv_class_inject = thm "UN_equiv_class_inject";
val congruent2_implies_congruent = thm "congruent2_implies_congruent";
val congruent2_implies_congruent_UN = thm "congruent2_implies_congruent_UN";
val congruent_commuteI = thm "congruent_commuteI";
val UN_equiv_class2 = thm "UN_equiv_class2";
val UN_equiv_class_type2 = thm "UN_equiv_class_type2";
val congruent2I = thm "congruent2I";
val congruent2_commuteI = thm "congruent2_commuteI";
val congruent_commuteI = thm "congruent_commuteI";
*}

end
