(*  Title:      HOLCF/Ssum1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Partial ordering for the strict sum ++
*)

theory Ssum1 = Ssum0:

instance "++"::(pcpo,pcpo)sq_ord ..

defs (overloaded)
  less_ssum_def: "(op <<) == (%s1 s2.@z.
         (! u x. s1=Isinl u & s2=Isinl x --> z = u << x)
        &(! v y. s1=Isinr v & s2=Isinr y --> z = v << y)
        &(! u y. s1=Isinl u & s2=Isinr y --> z = (u = UU))
        &(! v x. s1=Isinr v & s2=Isinl x --> z = (v = UU)))"

(*  Title:      HOLCF/Ssum1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Partial ordering for the strict sum ++
*)

lemma less_ssum1a: 
"[|s1=Isinl(x::'a); s2=Isinl(y::'a)|] ==> s1 << s2 = (x << y)"
apply (unfold less_ssum_def)
apply (rule some_equality)
apply (drule_tac [2] conjunct1)
apply (drule_tac [2] spec)
apply (drule_tac [2] spec)
apply (erule_tac [2] mp)
prefer 2 apply fast
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule inject_Isinl)
apply (drule inject_Isinl)
apply simp
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr[OF sym])
apply simp
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule inject_Isinl)
apply (drule noteq_IsinlIsinr[OF sym])
apply simp
apply (rule eq_UU_iff[symmetric])
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr[OF sym])
apply simp
done


lemma less_ssum1b: 
"[|s1=Isinr(x::'b); s2=Isinr(y::'b)|] ==> s1 << s2 = (x << y)"

apply (unfold less_ssum_def)
apply (rule some_equality)
apply (drule_tac [2] conjunct2)
apply (drule_tac [2] conjunct1)
apply (drule_tac [2] spec)
apply (drule_tac [2] spec)
apply (erule_tac [2] mp)
prefer 2 apply fast
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr)
apply (drule noteq_IsinlIsinr)
apply simp
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule inject_Isinr)
apply (drule inject_Isinr)
apply simp
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr)
apply (drule inject_Isinr)
apply simp
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule inject_Isinr)
apply (drule noteq_IsinlIsinr)
apply simp
apply (rule eq_UU_iff[symmetric])
done


lemma less_ssum1c: 
"[|s1=Isinl(x::'a); s2=Isinr(y::'b)|] ==> s1 << s2 = ((x::'a) = UU)"

apply (unfold less_ssum_def)
apply (rule some_equality)
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule inject_Isinl)
apply (drule noteq_IsinlIsinr)
apply simp
apply (rule eq_UU_iff)
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr[OF sym])
apply (drule inject_Isinr)
apply simp
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule inject_Isinl)
apply (drule inject_Isinr)
apply simp
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr[OF sym])
apply (drule noteq_IsinlIsinr)
apply simp
apply (drule conjunct2)
apply (drule conjunct2)
apply (drule conjunct1)
apply (drule spec)
apply (drule spec)
apply (erule mp)
apply fast
done


lemma less_ssum1d: 
"[|s1=Isinr(x); s2=Isinl(y)|] ==> s1 << s2 = (x = UU)"

apply (unfold less_ssum_def)
apply (rule some_equality)
apply (drule_tac [2] conjunct2)
apply (drule_tac [2] conjunct2)
apply (drule_tac [2] conjunct2)
apply (drule_tac [2] spec)
apply (drule_tac [2] spec)
apply (erule_tac [2] mp)
prefer 2 apply fast
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr)
apply (drule inject_Isinl)
apply simp
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr[OF sym])
apply (drule inject_Isinr)
apply simp
apply (rule eq_UU_iff)
apply (rule conjI)
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule noteq_IsinlIsinr)
apply (drule noteq_IsinlIsinr[OF sym])
apply simp
apply (intro strip)
apply (erule conjE)
apply simp
apply (drule inject_Isinr)
apply simp
done


(* ------------------------------------------------------------------------ *)
(* optimize lemmas about less_ssum                                          *)
(* ------------------------------------------------------------------------ *)

lemma less_ssum2a: "(Isinl x) << (Isinl y) = (x << y)"
apply (rule less_ssum1a)
apply (rule refl)
apply (rule refl)
done

lemma less_ssum2b: "(Isinr x) << (Isinr y) = (x << y)"
apply (rule less_ssum1b)
apply (rule refl)
apply (rule refl)
done

lemma less_ssum2c: "(Isinl x) << (Isinr y) = (x = UU)"
apply (rule less_ssum1c)
apply (rule refl)
apply (rule refl)
done

lemma less_ssum2d: "(Isinr x) << (Isinl y) = (x = UU)"
apply (rule less_ssum1d)
apply (rule refl)
apply (rule refl)
done


(* ------------------------------------------------------------------------ *)
(* less_ssum is a partial order on ++                                     *)
(* ------------------------------------------------------------------------ *)

lemma refl_less_ssum: "(p::'a++'b) << p"
apply (rule_tac p = "p" in IssumE2)
apply (erule ssubst)
apply (rule less_ssum2a [THEN iffD2])
apply (rule refl_less)
apply (erule ssubst)
apply (rule less_ssum2b [THEN iffD2])
apply (rule refl_less)
done

lemma antisym_less_ssum: "[|(p1::'a++'b) << p2; p2 << p1|] ==> p1=p2"
apply (rule_tac p = "p1" in IssumE2)
apply simp
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (rule_tac f = "Isinl" in arg_cong)
apply (rule antisym_less)
apply (erule less_ssum2a [THEN iffD1])
apply (erule less_ssum2a [THEN iffD1])
apply simp
apply (erule less_ssum2d [THEN iffD1, THEN ssubst])
apply (erule less_ssum2c [THEN iffD1, THEN ssubst])
apply (rule strict_IsinlIsinr)
apply simp
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (erule less_ssum2c [THEN iffD1, THEN ssubst])
apply (erule less_ssum2d [THEN iffD1, THEN ssubst])
apply (rule strict_IsinlIsinr [symmetric])
apply simp
apply (rule_tac f = "Isinr" in arg_cong)
apply (rule antisym_less)
apply (erule less_ssum2b [THEN iffD1])
apply (erule less_ssum2b [THEN iffD1])
done

lemma trans_less_ssum: "[|(p1::'a++'b) << p2; p2 << p3|] ==> p1 << p3"
apply (rule_tac p = "p1" in IssumE2)
apply simp
apply (rule_tac p = "p3" in IssumE2)
apply simp
apply (rule less_ssum2a [THEN iffD2])
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (rule trans_less)
apply (erule less_ssum2a [THEN iffD1])
apply (erule less_ssum2a [THEN iffD1])
apply simp
apply (erule less_ssum2c [THEN iffD1, THEN ssubst])
apply (rule minimal)
apply simp
apply (rule less_ssum2c [THEN iffD2])
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (rule UU_I)
apply (rule trans_less)
apply (erule less_ssum2a [THEN iffD1])
apply (rule antisym_less_inverse [THEN conjunct1])
apply (erule less_ssum2c [THEN iffD1])
apply simp
apply (erule less_ssum2c [THEN iffD1])
apply simp
apply (rule_tac p = "p3" in IssumE2)
apply simp
apply (rule less_ssum2d [THEN iffD2])
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (erule less_ssum2d [THEN iffD1])
apply simp
apply (rule UU_I)
apply (rule trans_less)
apply (erule less_ssum2b [THEN iffD1])
apply (rule antisym_less_inverse [THEN conjunct1])
apply (erule less_ssum2d [THEN iffD1])
apply simp
apply (rule less_ssum2b [THEN iffD2])
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (erule less_ssum2d [THEN iffD1, THEN ssubst])
apply (rule minimal)
apply simp
apply (rule trans_less)
apply (erule less_ssum2b [THEN iffD1])
apply (erule less_ssum2b [THEN iffD1])
done

end


