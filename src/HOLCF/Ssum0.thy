(*  Title:      HOLCF/Ssum0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Strict sum with typedef
*)

theory Ssum0 = Cfun3:

constdefs
  Sinl_Rep      :: "['a,'a,'b,bool]=>bool"
 "Sinl_Rep == (%a.%x y p. (a~=UU --> x=a & p))"
  Sinr_Rep      :: "['b,'a,'b,bool]=>bool"
 "Sinr_Rep == (%b.%x y p.(b~=UU --> y=b & ~p))"

typedef (Ssum)  ('a, 'b) "++" (infixr 10) = 
	"{f.(? a. f=Sinl_Rep(a::'a))|(? b. f=Sinr_Rep(b::'b))}"
by auto

syntax (xsymbols)
  "++"		:: "[type, type] => type"	("(_ \<oplus>/ _)" [21, 20] 20)
syntax (HTML output)
  "++"		:: "[type, type] => type"	("(_ \<oplus>/ _)" [21, 20] 20)

consts
  Isinl         :: "'a => ('a ++ 'b)"
  Isinr         :: "'b => ('a ++ 'b)"
  Iwhen         :: "('a->'c)=>('b->'c)=>('a ++ 'b)=> 'c"

defs   (*defining the abstract constants*)
  Isinl_def:     "Isinl(a) == Abs_Ssum(Sinl_Rep(a))"
  Isinr_def:     "Isinr(b) == Abs_Ssum(Sinr_Rep(b))"

  Iwhen_def:     "Iwhen(f)(g)(s) == @z.
                                    (s=Isinl(UU) --> z=UU)
                        &(!a. a~=UU & s=Isinl(a) --> z=f$a)  
                        &(!b. b~=UU & s=Isinr(b) --> z=g$b)"  

(*  Title:      HOLCF/Ssum0.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Strict sum with typedef
*)

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Sssum                                         *)
(* ------------------------------------------------------------------------ *)

lemma SsumIl: "Sinl_Rep(a):Ssum"
apply (unfold Ssum_def)
apply blast
done

lemma SsumIr: "Sinr_Rep(a):Ssum"
apply (unfold Ssum_def)
apply blast
done

lemma inj_on_Abs_Ssum: "inj_on Abs_Ssum Ssum"
apply (rule inj_on_inverseI)
apply (erule Abs_Ssum_inverse)
done

(* ------------------------------------------------------------------------ *)
(* Strictness of Sinr_Rep, Sinl_Rep and Isinl, Isinr                        *)
(* ------------------------------------------------------------------------ *)

lemma strict_SinlSinr_Rep: 
 "Sinl_Rep(UU) = Sinr_Rep(UU)"

apply (unfold Sinr_Rep_def Sinl_Rep_def)
apply (rule ext)
apply (rule ext)
apply (rule ext)
apply fast
done

lemma strict_IsinlIsinr: 
 "Isinl(UU) = Isinr(UU)"
apply (unfold Isinl_def Isinr_def)
apply (rule strict_SinlSinr_Rep [THEN arg_cong])
done


(* ------------------------------------------------------------------------ *)
(* distinctness of  Sinl_Rep, Sinr_Rep and Isinl, Isinr                     *)
(* ------------------------------------------------------------------------ *)

lemma noteq_SinlSinr_Rep: 
        "(Sinl_Rep(a) = Sinr_Rep(b)) ==> a=UU & b=UU"

apply (unfold Sinl_Rep_def Sinr_Rep_def)
apply (blast dest!: fun_cong)
done


lemma noteq_IsinlIsinr: 
        "Isinl(a)=Isinr(b) ==> a=UU & b=UU"

apply (unfold Isinl_def Isinr_def)
apply (rule noteq_SinlSinr_Rep)
apply (erule inj_on_Abs_Ssum [THEN inj_onD])
apply (rule SsumIl)
apply (rule SsumIr)
done



(* ------------------------------------------------------------------------ *)
(* injectivity of Sinl_Rep, Sinr_Rep and Isinl, Isinr                       *)
(* ------------------------------------------------------------------------ *)

lemma inject_Sinl_Rep1: "(Sinl_Rep(a) = Sinl_Rep(UU)) ==> a=UU"
apply (unfold Sinl_Rep_def)
apply (blast dest!: fun_cong)
done

lemma inject_Sinr_Rep1: "(Sinr_Rep(b) = Sinr_Rep(UU)) ==> b=UU"
apply (unfold Sinr_Rep_def)
apply (blast dest!: fun_cong)
done

lemma inject_Sinl_Rep2: 
"[| a1~=UU ; a2~=UU ; Sinl_Rep(a1)=Sinl_Rep(a2) |] ==> a1=a2"
apply (unfold Sinl_Rep_def)
apply (blast dest!: fun_cong)
done

lemma inject_Sinr_Rep2: 
"[|b1~=UU ; b2~=UU ; Sinr_Rep(b1)=Sinr_Rep(b2) |] ==> b1=b2"
apply (unfold Sinr_Rep_def)
apply (blast dest!: fun_cong)
done

lemma inject_Sinl_Rep: "Sinl_Rep(a1)=Sinl_Rep(a2) ==> a1=a2"
apply (case_tac "a1=UU")
apply simp
apply (rule inject_Sinl_Rep1 [symmetric])
apply (erule sym)
apply (case_tac "a2=UU")
apply simp
apply (drule inject_Sinl_Rep1)
apply simp
apply (erule inject_Sinl_Rep2)
apply assumption
apply assumption
done

lemma inject_Sinr_Rep: "Sinr_Rep(b1)=Sinr_Rep(b2) ==> b1=b2"
apply (case_tac "b1=UU")
apply simp
apply (rule inject_Sinr_Rep1 [symmetric])
apply (erule sym)
apply (case_tac "b2=UU")
apply simp
apply (drule inject_Sinr_Rep1)
apply simp
apply (erule inject_Sinr_Rep2)
apply assumption
apply assumption
done

lemma inject_Isinl: "Isinl(a1)=Isinl(a2)==> a1=a2"
apply (unfold Isinl_def)
apply (rule inject_Sinl_Rep)
apply (erule inj_on_Abs_Ssum [THEN inj_onD])
apply (rule SsumIl)
apply (rule SsumIl)
done

lemma inject_Isinr: "Isinr(b1)=Isinr(b2) ==> b1=b2"
apply (unfold Isinr_def)
apply (rule inject_Sinr_Rep)
apply (erule inj_on_Abs_Ssum [THEN inj_onD])
apply (rule SsumIr)
apply (rule SsumIr)
done

declare inject_Isinl [dest!] inject_Isinr [dest!]

lemma inject_Isinl_rev: "a1~=a2 ==> Isinl(a1) ~= Isinl(a2)"
apply blast
done

lemma inject_Isinr_rev: "b1~=b2 ==> Isinr(b1) ~= Isinr(b2)"
apply blast
done

(* ------------------------------------------------------------------------ *)
(* Exhaustion of the strict sum ++                                          *)
(* choice of the bottom representation is arbitrary                         *)
(* ------------------------------------------------------------------------ *)

lemma Exh_Ssum: 
        "z=Isinl(UU) | (? a. z=Isinl(a) & a~=UU) | (? b. z=Isinr(b) & b~=UU)"
apply (unfold Isinl_def Isinr_def)
apply (rule Rep_Ssum[unfolded Ssum_def, THEN CollectE])
apply (erule disjE)
apply (erule exE)
apply (case_tac "z= Abs_Ssum (Sinl_Rep (UU))")
apply (erule disjI1)
apply (rule disjI2)
apply (rule disjI1)
apply (rule exI)
apply (rule conjI)
apply (rule Rep_Ssum_inverse [symmetric, THEN trans])
apply (erule arg_cong)
apply (rule_tac Q = "Sinl_Rep (a) =Sinl_Rep (UU) " in contrapos_nn)
apply (erule_tac [2] arg_cong)
apply (erule contrapos_nn)
apply (rule Rep_Ssum_inverse [symmetric, THEN trans])
apply (rule trans)
apply (erule arg_cong)
apply (erule arg_cong)
apply (erule exE)
apply (case_tac "z= Abs_Ssum (Sinl_Rep (UU))")
apply (erule disjI1)
apply (rule disjI2)
apply (rule disjI2)
apply (rule exI)
apply (rule conjI)
apply (rule Rep_Ssum_inverse [symmetric, THEN trans])
apply (erule arg_cong)
apply (rule_tac Q = "Sinr_Rep (b) =Sinl_Rep (UU) " in contrapos_nn)
prefer 2 apply simp
apply (rule strict_SinlSinr_Rep [symmetric])
apply (erule contrapos_nn)
apply (rule Rep_Ssum_inverse [symmetric, THEN trans])
apply (rule trans)
apply (erule arg_cong)
apply (erule arg_cong)
done

(* ------------------------------------------------------------------------ *)
(* elimination rules for the strict sum ++                                  *)
(* ------------------------------------------------------------------------ *)

lemma IssumE:
        "[|p=Isinl(UU) ==> Q ; 
        !!x.[|p=Isinl(x); x~=UU |] ==> Q; 
        !!y.[|p=Isinr(y); y~=UU |] ==> Q|] ==> Q"
apply (rule Exh_Ssum [THEN disjE])
apply auto
done

lemma IssumE2:
"[| !!x. [| p = Isinl(x) |] ==> Q;   !!y. [| p = Isinr(y) |] ==> Q |] ==>Q"
apply (rule IssumE)
apply auto
done




(* ------------------------------------------------------------------------ *)
(* rewrites for Iwhen                                                       *)
(* ------------------------------------------------------------------------ *)

lemma Iwhen1: 
        "Iwhen f g (Isinl UU) = UU"
apply (unfold Iwhen_def)
apply (rule some_equality)
apply (rule conjI)
apply fast
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "a=UU" in notE)
apply fast
apply (rule inject_Isinl)
apply (rule sym)
apply fast
apply (intro strip)
apply (rule_tac P = "b=UU" in notE)
apply fast
apply (rule inject_Isinr)
apply (rule sym)
apply (rule strict_IsinlIsinr [THEN subst])
apply fast
apply fast
done


lemma Iwhen2: 
        "x~=UU ==> Iwhen f g (Isinl x) = f$x"

apply (unfold Iwhen_def)
apply (rule some_equality)
prefer 2 apply fast
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "x=UU" in notE)
apply assumption
apply (rule inject_Isinl)
apply assumption
apply (rule conjI)
apply (intro strip)
apply (rule cfun_arg_cong)
apply (rule inject_Isinl)
apply fast
apply (intro strip)
apply (rule_tac P = "Isinl (x) = Isinr (b) " in notE)
prefer 2 apply fast
apply (rule contrapos_nn)
apply (erule_tac [2] noteq_IsinlIsinr)
apply fast
done

lemma Iwhen3: 
        "y~=UU ==> Iwhen f g (Isinr y) = g$y"
apply (unfold Iwhen_def)
apply (rule some_equality)
prefer 2 apply fast
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "y=UU" in notE)
apply assumption
apply (rule inject_Isinr)
apply (rule strict_IsinlIsinr [THEN subst])
apply assumption
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "Isinr (y) = Isinl (a) " in notE)
prefer 2 apply fast
apply (rule contrapos_nn)
apply (erule_tac [2] sym [THEN noteq_IsinlIsinr])
apply fast
apply (intro strip)
apply (rule cfun_arg_cong)
apply (rule inject_Isinr)
apply fast
done

(* ------------------------------------------------------------------------ *)
(* instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

lemmas Ssum0_ss = strict_IsinlIsinr[symmetric] Iwhen1 Iwhen2 Iwhen3

declare Ssum0_ss [simp]

end
