(*  Title:      HOL/HOLCF/ex/Hoare.thy
    Author:     Franz Regensburger

Theory for an example by C.A.R. Hoare

p x = if b1 x
         then p (g x)
         else x fi

q x = if b1 x orelse b2 x
         then q (g x)
         else x fi

Prove: for all b1 b2 g .
            q o p  = q

In order to get a nice notation we fix the functions b1,b2 and g in the
signature of this example

*)

theory Hoare
imports HOLCF
begin

axiomatization
  b1 :: "'a -> tr" and
  b2 :: "'a -> tr" and
  g :: "'a -> 'a"

definition
  p :: "'a -> 'a" where
  "p = fix$(LAM f. LAM x. If b1$x then f$(g$x) else x)"

definition
  q :: "'a -> 'a" where
  "q = fix$(LAM f. LAM x. If b1$x orelse b2$x then f$(g$x) else x)"


(* --------- pure HOLCF logic, some little lemmas ------ *)

lemma hoare_lemma2: "b~=TT ==> b=FF | b=UU"
apply (rule Exh_tr [THEN disjE])
apply blast+
done

lemma hoare_lemma3: " (ALL k. b1$(iterate k$g$x) = TT) | (EX k. b1$(iterate k$g$x)~=TT)"
apply blast
done

lemma hoare_lemma4: "(EX k. b1$(iterate k$g$x) ~= TT) ==>  
  EX k. b1$(iterate k$g$x) = FF | b1$(iterate k$g$x) = UU"
apply (erule exE)
apply (rule exI)
apply (rule hoare_lemma2)
apply assumption
done

lemma hoare_lemma5: "[|(EX k. b1$(iterate k$g$x) ~= TT); 
    k=Least(%n. b1$(iterate n$g$x) ~= TT)|] ==>  
  b1$(iterate k$g$x)=FF | b1$(iterate k$g$x)=UU"
apply hypsubst
apply (rule hoare_lemma2)
apply (erule exE)
apply (erule LeastI)
done

lemma hoare_lemma6: "b=UU ==> b~=TT"
apply hypsubst
apply (rule dist_eq_tr)
done

lemma hoare_lemma7: "b=FF ==> b~=TT"
apply hypsubst
apply (rule dist_eq_tr)
done

lemma hoare_lemma8: "[|(EX k. b1$(iterate k$g$x) ~= TT); 
    k=Least(%n. b1$(iterate n$g$x) ~= TT)|] ==>  
  ALL m. m < k --> b1$(iterate m$g$x)=TT"
apply hypsubst
apply (erule exE)
apply (intro strip)
apply (rule_tac p = "b1$ (iterate m$g$x) " in trE)
prefer 2 apply (assumption)
apply (rule le_less_trans [THEN less_irrefl [THEN notE]])
prefer 2 apply (assumption)
apply (rule Least_le)
apply (erule hoare_lemma6)
apply (rule le_less_trans [THEN less_irrefl [THEN notE]])
prefer 2 apply (assumption)
apply (rule Least_le)
apply (erule hoare_lemma7)
done


lemma hoare_lemma28: "f$(y::'a)=(UU::tr) ==> f$UU = UU"
by (rule strictI)


(* ----- access to definitions ----- *)

lemma p_def3: "p$x = If b1$x then p$(g$x) else x"
apply (rule trans)
apply (rule p_def [THEN eq_reflection, THEN fix_eq3])
apply simp
done

lemma q_def3: "q$x = If b1$x orelse b2$x then q$(g$x) else x"
apply (rule trans)
apply (rule q_def [THEN eq_reflection, THEN fix_eq3])
apply simp
done

(** --------- proofs about iterations of p and q ---------- **)

lemma hoare_lemma9: "(ALL m. m< Suc k --> b1$(iterate m$g$x)=TT) --> 
   p$(iterate k$g$x)=p$x"
apply (induct_tac k)
apply (simp (no_asm))
apply (simp (no_asm))
apply (intro strip)
apply (rule_tac s = "p$ (iterate n$g$x) " in trans)
apply (rule trans)
apply (rule_tac [2] p_def3 [symmetric])
apply (rule_tac s = "TT" and t = "b1$ (iterate n$g$x) " in ssubst)
apply (rule mp)
apply (erule spec)
apply (simp (no_asm) add: less_Suc_eq)
apply simp
apply (erule mp)
apply (intro strip)
apply (rule mp)
apply (erule spec)
apply (erule less_trans)
apply simp
done

lemma hoare_lemma24: "(ALL m. m< Suc k --> b1$(iterate m$g$x)=TT) -->  
  q$(iterate k$g$x)=q$x"
apply (induct_tac k)
apply (simp (no_asm))
apply (simp (no_asm) add: less_Suc_eq)
apply (intro strip)
apply (rule_tac s = "q$ (iterate n$g$x) " in trans)
apply (rule trans)
apply (rule_tac [2] q_def3 [symmetric])
apply (rule_tac s = "TT" and t = "b1$ (iterate n$g$x) " in ssubst)
apply blast
apply simp
apply (erule mp)
apply (intro strip)
apply (fast dest!: less_Suc_eq [THEN iffD1])
done

(* -------- results about p for case (EX k. b1$(iterate k$g$x)~=TT) ------- *)

lemma hoare_lemma10:
  "EX k. b1$(iterate k$g$x) ~= TT
    ==> Suc k = (LEAST n. b1$(iterate n$g$x) ~= TT) ==> p$(iterate k$g$x) = p$x"
  by (rule hoare_lemma8 [THEN hoare_lemma9 [THEN mp]])

lemma hoare_lemma11: "(EX n. b1$(iterate n$g$x) ~= TT) ==> 
  k=(LEAST n. b1$(iterate n$g$x) ~= TT) & b1$(iterate k$g$x)=FF  
  --> p$x = iterate k$g$x"
apply (case_tac "k")
apply hypsubst
apply (simp (no_asm))
apply (intro strip)
apply (erule conjE)
apply (rule trans)
apply (rule p_def3)
apply simp
apply hypsubst
apply (intro strip)
apply (erule conjE)
apply (rule trans)
apply (erule hoare_lemma10 [symmetric])
apply assumption
apply (rule trans)
apply (rule p_def3)
apply (rule_tac s = "TT" and t = "b1$ (iterate nat$g$x) " in ssubst)
apply (rule hoare_lemma8 [THEN spec, THEN mp])
apply assumption
apply assumption
apply (simp (no_asm))
apply (simp (no_asm))
apply (rule trans)
apply (rule p_def3)
apply (simp (no_asm) del: iterate_Suc add: iterate_Suc [symmetric])
apply (erule_tac s = "FF" in ssubst)
apply simp
done

lemma hoare_lemma12: "(EX n. b1$(iterate n$g$x) ~= TT) ==> 
  k=Least(%n. b1$(iterate n$g$x)~=TT) & b1$(iterate k$g$x)=UU  
  --> p$x = UU"
apply (case_tac "k")
apply hypsubst
apply (simp (no_asm))
apply (intro strip)
apply (erule conjE)
apply (rule trans)
apply (rule p_def3)
apply simp
apply hypsubst
apply (simp (no_asm))
apply (intro strip)
apply (erule conjE)
apply (rule trans)
apply (rule hoare_lemma10 [symmetric])
apply assumption
apply assumption
apply (rule trans)
apply (rule p_def3)
apply (rule_tac s = "TT" and t = "b1$ (iterate nat$g$x) " in ssubst)
apply (rule hoare_lemma8 [THEN spec, THEN mp])
apply assumption
apply assumption
apply (simp (no_asm))
apply (simp)
apply (rule trans)
apply (rule p_def3)
apply simp
done

(* -------- results about p for case  (ALL k. b1$(iterate k$g$x)=TT) ------- *)

lemma fernpass_lemma: "(ALL k. b1$(iterate k$g$x)=TT) ==> ALL k. p$(iterate k$g$x) = UU"
apply (rule p_def [THEN eq_reflection, THEN def_fix_ind])
apply simp
apply simp
apply (simp (no_asm))
apply (rule allI)
apply (rule_tac s = "TT" and t = "b1$ (iterate k$g$x) " in ssubst)
apply (erule spec)
apply (simp)
apply (rule iterate_Suc [THEN subst])
apply (erule spec)
done

lemma hoare_lemma16: "(ALL k. b1$(iterate k$g$x)=TT) ==> p$x = UU"
apply (rule_tac F1 = "g" and t = "x" in iterate_0 [THEN subst])
apply (erule fernpass_lemma [THEN spec])
done

(* -------- results about q for case  (ALL k. b1$(iterate k$g$x)=TT) ------- *)

lemma hoare_lemma17: "(ALL k. b1$(iterate k$g$x)=TT) ==> ALL k. q$(iterate k$g$x) = UU"
apply (rule q_def [THEN eq_reflection, THEN def_fix_ind])
apply simp
apply simp
apply (rule allI)
apply (simp (no_asm))
apply (rule_tac s = "TT" and t = "b1$ (iterate k$g$x) " in ssubst)
apply (erule spec)
apply (simp)
apply (rule iterate_Suc [THEN subst])
apply (erule spec)
done

lemma hoare_lemma18: "(ALL k. b1$(iterate k$g$x)=TT) ==> q$x = UU"
apply (rule_tac F1 = "g" and t = "x" in iterate_0 [THEN subst])
apply (erule hoare_lemma17 [THEN spec])
done

lemma hoare_lemma19:
  "(ALL k. (b1::'a->tr)$(iterate k$g$x)=TT) ==> b1$(UU::'a) = UU | (ALL y. b1$(y::'a)=TT)"
apply (rule flat_codom)
apply (rule_tac t = "x1" in iterate_0 [THEN subst])
apply (erule spec)
done

lemma hoare_lemma20: "(ALL y. b1$(y::'a)=TT) ==> ALL k. q$(iterate k$g$(x::'a)) = UU"
apply (rule q_def [THEN eq_reflection, THEN def_fix_ind])
apply simp
apply simp
apply (rule allI)
apply (simp (no_asm))
apply (rule_tac s = "TT" and t = "b1$ (iterate k$g$ (x::'a))" in ssubst)
apply (erule spec)
apply (simp)
apply (rule iterate_Suc [THEN subst])
apply (erule spec)
done

lemma hoare_lemma21: "(ALL y. b1$(y::'a)=TT) ==> q$(x::'a) = UU"
apply (rule_tac F1 = "g" and t = "x" in iterate_0 [THEN subst])
apply (erule hoare_lemma20 [THEN spec])
done

lemma hoare_lemma22: "b1$(UU::'a)=UU ==> q$(UU::'a) = UU"
apply (subst q_def3)
apply simp
done

(* -------- results about q for case (EX k. b1$(iterate k$g$x) ~= TT) ------- *)

lemma hoare_lemma25: "EX k. b1$(iterate k$g$x) ~= TT
  ==> Suc k = (LEAST n. b1$(iterate n$g$x) ~= TT) ==> q$(iterate k$g$x) = q$x"
  by (rule hoare_lemma8 [THEN hoare_lemma24 [THEN mp]])

lemma hoare_lemma26: "(EX n. b1$(iterate n$g$x)~=TT) ==> 
  k=Least(%n. b1$(iterate n$g$x) ~= TT) & b1$(iterate k$g$x) =FF  
  --> q$x = q$(iterate k$g$x)"
apply (case_tac "k")
apply hypsubst
apply (intro strip)
apply (simp (no_asm))
apply hypsubst
apply (intro strip)
apply (erule conjE)
apply (rule trans)
apply (rule hoare_lemma25 [symmetric])
apply assumption
apply assumption
apply (rule trans)
apply (rule q_def3)
apply (rule_tac s = "TT" and t = "b1$ (iterate nat$g$x) " in ssubst)
apply (rule hoare_lemma8 [THEN spec, THEN mp])
apply assumption
apply assumption
apply (simp (no_asm))
apply (simp (no_asm))
done


lemma hoare_lemma27: "(EX n. b1$(iterate n$g$x) ~= TT) ==> 
  k=Least(%n. b1$(iterate n$g$x)~=TT) & b1$(iterate k$g$x)=UU  
  --> q$x = UU"
apply (case_tac "k")
apply hypsubst
apply (simp (no_asm))
apply (intro strip)
apply (erule conjE)
apply (subst q_def3)
apply (simp)
apply hypsubst
apply (simp (no_asm))
apply (intro strip)
apply (erule conjE)
apply (rule trans)
apply (rule hoare_lemma25 [symmetric])
apply assumption
apply assumption
apply (rule trans)
apply (rule q_def3)
apply (rule_tac s = "TT" and t = "b1$ (iterate nat$g$x) " in ssubst)
apply (rule hoare_lemma8 [THEN spec, THEN mp])
apply assumption
apply assumption
apply (simp (no_asm))
apply (simp)
apply (rule trans)
apply (rule q_def3)
apply (simp)
done

(* ------- (ALL k. b1$(iterate k$g$x)=TT) ==> q o p = q   ----- *)

lemma hoare_lemma23: "(ALL k. b1$(iterate k$g$x)=TT) ==> q$(p$x) = q$x"
apply (subst hoare_lemma16)
apply assumption
apply (rule hoare_lemma19 [THEN disjE])
apply assumption
apply (simplesubst hoare_lemma18)
apply assumption
apply (simplesubst hoare_lemma22)
apply assumption
apply (rule refl)
apply (simplesubst hoare_lemma21)
apply assumption
apply (simplesubst hoare_lemma21)
apply assumption
apply (rule refl)
done

(* ------------  EX k. b1~(iterate k$g$x) ~= TT ==> q o p = q   ----- *)

lemma hoare_lemma29: "EX k. b1$(iterate k$g$x) ~= TT ==> q$(p$x) = q$x"
apply (rule hoare_lemma5 [THEN disjE])
apply assumption
apply (rule refl)
apply (subst hoare_lemma11 [THEN mp])
apply assumption
apply (rule conjI)
apply (rule refl)
apply assumption
apply (rule hoare_lemma26 [THEN mp, THEN subst])
apply assumption
apply (rule conjI)
apply (rule refl)
apply assumption
apply (rule refl)
apply (subst hoare_lemma12 [THEN mp])
apply assumption
apply (rule conjI)
apply (rule refl)
apply assumption
apply (subst hoare_lemma22)
apply (subst hoare_lemma28)
apply assumption
apply (rule refl)
apply (rule sym)
apply (subst hoare_lemma27 [THEN mp])
apply assumption
apply (rule conjI)
apply (rule refl)
apply assumption
apply (rule refl)
done

(* ------ the main proof q o p = q ------ *)

theorem hoare_main: "q oo p = q"
apply (rule cfun_eqI)
apply (subst cfcomp2)
apply (rule hoare_lemma3 [THEN disjE])
apply (erule hoare_lemma23)
apply (erule hoare_lemma29)
done

end
