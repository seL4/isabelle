(*  Title:      HOLCF/Sprod0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Strict product with typedef.
*)

theory Sprod0 = Cfun3:

constdefs
  Spair_Rep     :: "['a,'b] => ['a,'b] => bool"
 "Spair_Rep == (%a b. %x y.(~a=UU & ~b=UU --> x=a  & y=b ))"

typedef (Sprod)  ('a, 'b) "**" (infixr 20) = "{f. ? a b. f = Spair_Rep (a::'a) (b::'b)}"
by auto

syntax (xsymbols)
  "**"		:: "[type, type] => type"	 ("(_ \<otimes>/ _)" [21,20] 20)
syntax (HTML output)
  "**"		:: "[type, type] => type"	 ("(_ \<otimes>/ _)" [21,20] 20)

consts
  Ispair        :: "['a,'b] => ('a ** 'b)"
  Isfst         :: "('a ** 'b) => 'a"
  Issnd         :: "('a ** 'b) => 'b"  

defs
   (*defining the abstract constants*)

  Ispair_def:    "Ispair a b == Abs_Sprod(Spair_Rep a b)"

  Isfst_def:     "Isfst(p) == @z.        (p=Ispair UU UU --> z=UU)
                &(! a b. ~a=UU & ~b=UU & p=Ispair a b   --> z=a)"  

  Issnd_def:     "Issnd(p) == @z.        (p=Ispair UU UU  --> z=UU)
                &(! a b. ~a=UU & ~b=UU & p=Ispair a b    --> z=b)"  

(*  Title:      HOLCF/Sprod0
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Strict product with typedef.
*)

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Sprod                                         *)
(* ------------------------------------------------------------------------ *)

lemma SprodI: "(Spair_Rep a b):Sprod"
apply (unfold Sprod_def)
apply (rule CollectI, rule exI, rule exI, rule refl)
done

lemma inj_on_Abs_Sprod: "inj_on Abs_Sprod Sprod"
apply (rule inj_on_inverseI)
apply (erule Abs_Sprod_inverse)
done

(* ------------------------------------------------------------------------ *)
(* Strictness and definedness of Spair_Rep                                  *)
(* ------------------------------------------------------------------------ *)

lemma strict_Spair_Rep: 
 "(a=UU | b=UU) ==> (Spair_Rep a b) = (Spair_Rep UU UU)"
apply (unfold Spair_Rep_def)
apply (rule ext)
apply (rule ext)
apply (rule iffI)
apply fast
apply fast
done

lemma defined_Spair_Rep_rev: 
 "(Spair_Rep a b) = (Spair_Rep UU UU) ==> (a=UU | b=UU)"
apply (unfold Spair_Rep_def)
apply (case_tac "a=UU|b=UU")
apply assumption
apply (fast dest: fun_cong)
done

(* ------------------------------------------------------------------------ *)
(* injectivity of Spair_Rep and Ispair                                      *)
(* ------------------------------------------------------------------------ *)

lemma inject_Spair_Rep: 
"[|~aa=UU ; ~ba=UU ; Spair_Rep a b = Spair_Rep aa ba |] ==> a=aa & b=ba"

apply (unfold Spair_Rep_def)
apply (drule fun_cong)
apply (drule fun_cong)
apply (erule iffD1 [THEN mp])
apply auto
done


lemma inject_Ispair: 
        "[|~aa=UU ; ~ba=UU ; Ispair a b = Ispair aa ba |] ==> a=aa & b=ba"
apply (unfold Ispair_def)
apply (erule inject_Spair_Rep)
apply assumption
apply (erule inj_on_Abs_Sprod [THEN inj_onD])
apply (rule SprodI)
apply (rule SprodI)
done


(* ------------------------------------------------------------------------ *)
(* strictness and definedness of Ispair                                     *)
(* ------------------------------------------------------------------------ *)

lemma strict_Ispair: 
 "(a=UU | b=UU) ==> Ispair a b = Ispair UU UU"
apply (unfold Ispair_def)
apply (erule strict_Spair_Rep [THEN arg_cong])
done

lemma strict_Ispair1: 
        "Ispair UU b  = Ispair UU UU"
apply (unfold Ispair_def)
apply (rule strict_Spair_Rep [THEN arg_cong])
apply (rule disjI1)
apply (rule refl)
done

lemma strict_Ispair2: 
        "Ispair a UU = Ispair UU UU"
apply (unfold Ispair_def)
apply (rule strict_Spair_Rep [THEN arg_cong])
apply (rule disjI2)
apply (rule refl)
done

lemma strict_Ispair_rev: "~Ispair x y = Ispair UU UU ==> ~x=UU & ~y=UU"
apply (rule de_Morgan_disj [THEN subst])
apply (erule contrapos_nn)
apply (erule strict_Ispair)
done

lemma defined_Ispair_rev: 
        "Ispair a b  = Ispair UU UU ==> (a = UU | b = UU)"
apply (unfold Ispair_def)
apply (rule defined_Spair_Rep_rev)
apply (rule inj_on_Abs_Sprod [THEN inj_onD])
apply assumption
apply (rule SprodI)
apply (rule SprodI)
done

lemma defined_Ispair: "[|a~=UU; b~=UU|] ==> (Ispair a b) ~= (Ispair UU UU)"
apply (rule contrapos_nn)
apply (erule_tac [2] defined_Ispair_rev)
apply (rule de_Morgan_disj [THEN iffD2])
apply (erule conjI)
apply assumption
done


(* ------------------------------------------------------------------------ *)
(* Exhaustion of the strict product **                                      *)
(* ------------------------------------------------------------------------ *)

lemma Exh_Sprod:
        "z=Ispair UU UU | (? a b. z=Ispair a b & a~=UU & b~=UU)"
apply (unfold Ispair_def)
apply (rule Rep_Sprod[unfolded Sprod_def, THEN CollectE])
apply (erule exE)
apply (erule exE)
apply (rule excluded_middle [THEN disjE])
apply (rule disjI2)
apply (rule exI)
apply (rule exI)
apply (rule conjI)
apply (rule Rep_Sprod_inverse [symmetric, THEN trans])
apply (erule arg_cong)
apply (rule de_Morgan_disj [THEN subst])
apply assumption
apply (rule disjI1)
apply (rule Rep_Sprod_inverse [symmetric, THEN trans])
apply (rule_tac f = "Abs_Sprod" in arg_cong)
apply (erule trans)
apply (erule strict_Spair_Rep)
done

(* ------------------------------------------------------------------------ *)
(* general elimination rule for strict product                              *)
(* ------------------------------------------------------------------------ *)

lemma IsprodE:
assumes prem1: "p=Ispair UU UU ==> Q"
assumes prem2: "!!x y. [|p=Ispair x y; x~=UU ; y~=UU|] ==> Q"
shows "Q"
apply (rule Exh_Sprod [THEN disjE])
apply (erule prem1)
apply (erule exE)
apply (erule exE)
apply (erule conjE)
apply (erule conjE)
apply (erule prem2)
apply assumption
apply assumption
done


(* ------------------------------------------------------------------------ *)
(* some results about the selectors Isfst, Issnd                            *)
(* ------------------------------------------------------------------------ *)

lemma strict_Isfst: "p=Ispair UU UU ==> Isfst p = UU"
apply (unfold Isfst_def)
apply (rule some_equality)
apply (rule conjI)
apply fast
apply (intro strip)
apply (rule_tac P = "Ispair UU UU = Ispair a b" in notE)
apply (rule not_sym)
apply (rule defined_Ispair)
apply (fast+)
done


lemma strict_Isfst1: "Isfst(Ispair UU y) = UU"
apply (subst strict_Ispair1)
apply (rule strict_Isfst)
apply (rule refl)
done

declare strict_Isfst1 [simp]

lemma strict_Isfst2: "Isfst(Ispair x UU) = UU"
apply (subst strict_Ispair2)
apply (rule strict_Isfst)
apply (rule refl)
done

declare strict_Isfst2 [simp]


lemma strict_Issnd: "p=Ispair UU UU ==>Issnd p=UU"

apply (unfold Issnd_def)
apply (rule some_equality)
apply (rule conjI)
apply fast
apply (intro strip)
apply (rule_tac P = "Ispair UU UU = Ispair a b" in notE)
apply (rule not_sym)
apply (rule defined_Ispair)
apply (fast+)
done

lemma strict_Issnd1: "Issnd(Ispair UU y) = UU"
apply (subst strict_Ispair1)
apply (rule strict_Issnd)
apply (rule refl)
done

declare strict_Issnd1 [simp]

lemma strict_Issnd2: "Issnd(Ispair x UU) = UU"
apply (subst strict_Ispair2)
apply (rule strict_Issnd)
apply (rule refl)
done

declare strict_Issnd2 [simp]

lemma Isfst: "[|x~=UU ;y~=UU |] ==> Isfst(Ispair x y) = x"
apply (unfold Isfst_def)
apply (rule some_equality)
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "Ispair x y = Ispair UU UU" in notE)
apply (erule defined_Ispair)
apply assumption
apply assumption
apply (intro strip)
apply (rule inject_Ispair [THEN conjunct1])
prefer 3 apply fast
apply (fast+)
done

lemma Issnd: "[|x~=UU ;y~=UU |] ==> Issnd(Ispair x y) = y"
apply (unfold Issnd_def)
apply (rule some_equality)
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "Ispair x y = Ispair UU UU" in notE)
apply (erule defined_Ispair)
apply assumption
apply assumption
apply (intro strip)
apply (rule inject_Ispair [THEN conjunct2])
prefer 3 apply fast
apply (fast+)
done

lemma Isfst2: "y~=UU ==>Isfst(Ispair x y)=x"
apply (rule_tac Q = "x=UU" in excluded_middle [THEN disjE])
apply (erule Isfst)
apply assumption
apply (erule ssubst)
apply (rule strict_Isfst1)
done

lemma Issnd2: "~x=UU ==>Issnd(Ispair x y)=y"
apply (rule_tac Q = "y=UU" in excluded_middle [THEN disjE])
apply (erule Issnd)
apply assumption
apply (erule ssubst)
apply (rule strict_Issnd2)
done


(* ------------------------------------------------------------------------ *)
(* instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

lemmas Sprod0_ss = strict_Isfst1 strict_Isfst2 strict_Issnd1 strict_Issnd2
                 Isfst2 Issnd2

declare Isfst2 [simp] Issnd2 [simp]

lemma defined_IsfstIssnd: "p~=Ispair UU UU ==> Isfst p ~= UU & Issnd p ~= UU"
apply (rule_tac p = "p" in IsprodE)
apply simp
apply (erule ssubst)
apply (rule conjI)
apply (simp add: Sprod0_ss)
apply (simp add: Sprod0_ss)
done


(* ------------------------------------------------------------------------ *)
(* Surjective pairing: equivalent to Exh_Sprod                              *)
(* ------------------------------------------------------------------------ *)

lemma surjective_pairing_Sprod: "z = Ispair(Isfst z)(Issnd z)"
apply (rule_tac z1 = "z" in Exh_Sprod [THEN disjE])
apply (simp add: Sprod0_ss)
apply (erule exE)
apply (erule exE)
apply (simp add: Sprod0_ss)
done

lemma Sel_injective_Sprod: "[|Isfst x = Isfst y; Issnd x = Issnd y|] ==> x = y"
apply (subgoal_tac "Ispair (Isfst x) (Issnd x) =Ispair (Isfst y) (Issnd y) ")
apply (simp (no_asm_use) add: surjective_pairing_Sprod[symmetric])
apply simp
done

end
