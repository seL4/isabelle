(*  Title:      HOLCF/ssum2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance ++::(pcpo,pcpo)po
*)

theory Ssum2 = Ssum1:

instance "++"::(pcpo,pcpo)po
apply (intro_classes)
apply (rule refl_less_ssum)
apply (rule antisym_less_ssum, assumption+)
apply (rule trans_less_ssum, assumption+)
done

(*  Title:      HOLCF/Ssum2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance ++::(pcpo,pcpo)po
*)

(* for compatibility with old HOLCF-Version *)
lemma inst_ssum_po: "(op <<)=(%s1 s2.@z.
         (! u x. s1=Isinl u & s2=Isinl x --> z = u << x)
        &(! v y. s1=Isinr v & s2=Isinr y --> z = v << y)
        &(! u y. s1=Isinl u & s2=Isinr y --> z = (u = UU))
        &(! v x. s1=Isinr v & s2=Isinl x --> z = (v = UU)))"
apply (fold less_ssum_def)
apply (rule refl)
done

(* ------------------------------------------------------------------------ *)
(* access to less_ssum in class po                                          *)
(* ------------------------------------------------------------------------ *)

lemma less_ssum3a: "Isinl x << Isinl y = x << y"
apply (simp (no_asm) add: less_ssum2a)
done

lemma less_ssum3b: "Isinr x << Isinr y = x << y"
apply (simp (no_asm) add: less_ssum2b)
done

lemma less_ssum3c: "Isinl x << Isinr y = (x = UU)"
apply (simp (no_asm) add: less_ssum2c)
done

lemma less_ssum3d: "Isinr x << Isinl y = (x = UU)"
apply (simp (no_asm) add: less_ssum2d)
done

(* ------------------------------------------------------------------------ *)
(* type ssum ++ is pointed                                                  *)
(* ------------------------------------------------------------------------ *)

lemma minimal_ssum: "Isinl UU << s"
apply (rule_tac p = "s" in IssumE2)
apply simp
apply (rule less_ssum3a [THEN iffD2])
apply (rule minimal)
apply simp
apply (subst strict_IsinlIsinr)
apply (rule less_ssum3b [THEN iffD2])
apply (rule minimal)
done

lemmas UU_ssum_def = minimal_ssum [THEN minimal2UU, symmetric, standard]

lemma least_ssum: "? x::'a++'b.!y. x<<y"
apply (rule_tac x = "Isinl UU" in exI)
apply (rule minimal_ssum [THEN allI])
done

(* ------------------------------------------------------------------------ *)
(* Isinl, Isinr are monotone                                                *)
(* ------------------------------------------------------------------------ *)

lemma monofun_Isinl: "monofun(Isinl)"

apply (unfold monofun)
apply (intro strip)
apply (erule less_ssum3a [THEN iffD2])
done

lemma monofun_Isinr: "monofun(Isinr)"
apply (unfold monofun)
apply (intro strip)
apply (erule less_ssum3b [THEN iffD2])
done


(* ------------------------------------------------------------------------ *)
(* Iwhen is monotone in all arguments                                       *)
(* ------------------------------------------------------------------------ *)


lemma monofun_Iwhen1: "monofun(Iwhen)"


apply (unfold monofun)
apply (intro strip)
apply (rule less_fun [THEN iffD2])
apply (intro strip)
apply (rule less_fun [THEN iffD2])
apply (intro strip)
apply (rule_tac p = "xb" in IssumE)
apply simp
apply simp
apply (erule monofun_cfun_fun)
apply simp
done

lemma monofun_Iwhen2: "monofun(Iwhen(f))"
apply (unfold monofun)
apply (intro strip)
apply (rule less_fun [THEN iffD2])
apply (intro strip)
apply (rule_tac p = "xa" in IssumE)
apply simp
apply simp
apply simp
apply (erule monofun_cfun_fun)
done

lemma monofun_Iwhen3: "monofun(Iwhen(f)(g))"
apply (unfold monofun)
apply (intro strip)
apply (rule_tac p = "x" in IssumE)
apply simp
apply (rule_tac p = "y" in IssumE)
apply simp
apply (rule_tac P = "xa=UU" in notE)
apply assumption
apply (rule UU_I)
apply (rule less_ssum3a [THEN iffD1])
apply assumption
apply simp
apply (rule monofun_cfun_arg)
apply (erule less_ssum3a [THEN iffD1])
apply (simp del: Iwhen2)
apply (rule_tac s = "UU" and t = "xa" in subst)
apply (erule less_ssum3c [THEN iffD1, symmetric])
apply simp
apply (rule_tac p = "y" in IssumE)
apply simp
apply (simp only: less_ssum3d)
apply (simp only: less_ssum3d)
apply simp
apply (rule monofun_cfun_arg)
apply (erule less_ssum3b [THEN iffD1])
done


(* ------------------------------------------------------------------------ *)
(* some kind of exhaustion rules for chains in 'a ++ 'b                     *)
(* ------------------------------------------------------------------------ *)

lemma ssum_lemma1: "[|~(!i.? x. Y(i::nat)=Isinl(x))|] ==> (? i.! x. Y(i)~=Isinl(x))"
apply fast
done

lemma ssum_lemma2: "[|(? i.!x.(Y::nat => 'a++'b)(i::nat)~=Isinl(x::'a))|]   
      ==> (? i y. (Y::nat => 'a++'b)(i::nat)=Isinr(y::'b) & y~=UU)"
apply (erule exE)
apply (rule_tac p = "Y (i) " in IssumE)
apply (drule spec)
apply (erule notE, assumption)
apply (drule spec)
apply (erule notE, assumption)
apply fast
done


lemma ssum_lemma3: "[|chain(Y);(? i x. Y(i)=Isinr(x::'b) & (x::'b)~=UU)|]  
      ==> (!i.? y. Y(i)=Isinr(y))"
apply (erule exE)
apply (erule exE)
apply (rule allI)
apply (rule_tac p = "Y (ia) " in IssumE)
apply (rule exI)
apply (rule trans)
apply (rule_tac [2] strict_IsinlIsinr)
apply assumption
apply (erule_tac [2] exI)
apply (erule conjE)
apply (rule_tac m = "i" and n = "ia" in nat_less_cases)
prefer 2 apply simp
apply (rule exI, rule refl)
apply (erule_tac P = "x=UU" in notE)
apply (rule less_ssum3d [THEN iffD1])
apply (erule_tac s = "Y (i) " and t = "Isinr (x) ::'a++'b" in subst)
apply (erule_tac s = "Y (ia) " and t = "Isinl (xa) ::'a++'b" in subst)
apply (erule chain_mono)
apply assumption
apply (erule_tac P = "xa=UU" in notE)
apply (rule less_ssum3c [THEN iffD1])
apply (erule_tac s = "Y (i) " and t = "Isinr (x) ::'a++'b" in subst)
apply (erule_tac s = "Y (ia) " and t = "Isinl (xa) ::'a++'b" in subst)
apply (erule chain_mono)
apply assumption
done

lemma ssum_lemma4: "chain(Y) ==> (!i.? x. Y(i)=Isinl(x))|(!i.? y. Y(i)=Isinr(y))"
apply (rule case_split_thm)
apply (erule disjI1)
apply (rule disjI2)
apply (erule ssum_lemma3)
apply (rule ssum_lemma2)
apply (erule ssum_lemma1)
done


(* ------------------------------------------------------------------------ *)
(* restricted surjectivity of Isinl                                         *)
(* ------------------------------------------------------------------------ *)

lemma ssum_lemma5: "z=Isinl(x)==> Isinl((Iwhen (LAM x. x) (LAM y. UU))(z)) = z"
apply simp
apply (case_tac "x=UU")
apply simp
apply simp
done

(* ------------------------------------------------------------------------ *)
(* restricted surjectivity of Isinr                                         *)
(* ------------------------------------------------------------------------ *)

lemma ssum_lemma6: "z=Isinr(x)==> Isinr((Iwhen (LAM y. UU) (LAM x. x))(z)) = z"
apply simp
apply (case_tac "x=UU")
apply simp
apply simp
done

(* ------------------------------------------------------------------------ *)
(* technical lemmas                                                         *)
(* ------------------------------------------------------------------------ *)

lemma ssum_lemma7: "[|Isinl(x) << z; x~=UU|] ==> ? y. z=Isinl(y) & y~=UU"
apply (rule_tac p = "z" in IssumE)
apply simp
apply (erule notE)
apply (rule antisym_less)
apply (erule less_ssum3a [THEN iffD1])
apply (rule minimal)
apply fast
apply simp
apply (rule notE)
apply (erule_tac [2] less_ssum3c [THEN iffD1])
apply assumption
done

lemma ssum_lemma8: "[|Isinr(x) << z; x~=UU|] ==> ? y. z=Isinr(y) & y~=UU"
apply (rule_tac p = "z" in IssumE)
apply simp
apply (erule notE)
apply (erule less_ssum3d [THEN iffD1])
apply simp
apply (rule notE)
apply (erule_tac [2] less_ssum3d [THEN iffD1])
apply assumption
apply fast
done

(* ------------------------------------------------------------------------ *)
(* the type 'a ++ 'b is a cpo in three steps                                *)
(* ------------------------------------------------------------------------ *)

lemma lub_ssum1a: "[|chain(Y);(!i.? x. Y(i)=Isinl(x))|] ==> 
      range(Y) <<| Isinl(lub(range(%i.(Iwhen (LAM x. x) (LAM y. UU))(Y i))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (erule allE)
apply (erule exE)
apply (rule_tac t = "Y (i) " in ssum_lemma5 [THEN subst])
apply assumption
apply (rule monofun_Isinl [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply (rule is_ub_thelub)
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (rule_tac p = "u" in IssumE2)
apply (rule_tac t = "u" in ssum_lemma5 [THEN subst])
apply assumption
apply (rule monofun_Isinl [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply (rule is_lub_thelub)
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (erule monofun_Iwhen3 [THEN ub2ub_monofun])
apply simp
apply (rule less_ssum3c [THEN iffD2])
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (rule_tac p = "Y (i) " in IssumE)
apply simp
apply simp
apply (erule notE)
apply (rule less_ssum3c [THEN iffD1])
apply (rule_tac t = "Isinl (x) " in subst)
apply assumption
apply (erule ub_rangeD)
apply simp
done


lemma lub_ssum1b: "[|chain(Y);(!i.? x. Y(i)=Isinr(x))|] ==> 
      range(Y) <<| Isinr(lub(range(%i.(Iwhen (LAM y. UU) (LAM x. x))(Y i))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (erule allE)
apply (erule exE)
apply (rule_tac t = "Y (i) " in ssum_lemma6 [THEN subst])
apply assumption
apply (rule monofun_Isinr [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply (rule is_ub_thelub)
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (rule_tac p = "u" in IssumE2)
apply simp
apply (rule less_ssum3d [THEN iffD2])
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (rule_tac p = "Y (i) " in IssumE)
apply simp
apply simp
apply (erule notE)
apply (rule less_ssum3d [THEN iffD1])
apply (rule_tac t = "Isinr (y) " in subst)
apply assumption
apply (erule ub_rangeD)
apply (rule_tac t = "u" in ssum_lemma6 [THEN subst])
apply assumption
apply (rule monofun_Isinr [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply (rule is_lub_thelub)
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (erule monofun_Iwhen3 [THEN ub2ub_monofun])
done


lemmas thelub_ssum1a = lub_ssum1a [THEN thelubI, standard]
(*
[| chain ?Y1; ! i. ? x. ?Y1 i = Isinl x |] ==>
 lub (range ?Y1) = Isinl
 (lub (range (%i. Iwhen (LAM x. x) (LAM y. UU) (?Y1 i))))
*)

lemmas thelub_ssum1b = lub_ssum1b [THEN thelubI, standard]
(*
[| chain ?Y1; ! i. ? x. ?Y1 i = Isinr x |] ==>
 lub (range ?Y1) = Isinr
 (lub (range (%i. Iwhen (LAM y. UU) (LAM x. x) (?Y1 i))))
*)

lemma cpo_ssum: "chain(Y::nat=>'a ++'b) ==> ? x. range(Y) <<|x"
apply (rule ssum_lemma4 [THEN disjE])
apply assumption
apply (rule exI)
apply (erule lub_ssum1a)
apply assumption
apply (rule exI)
apply (erule lub_ssum1b)
apply assumption
done

end



