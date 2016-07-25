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
  b1 :: "'a \<rightarrow> tr" and
  b2 :: "'a \<rightarrow> tr" and
  g :: "'a \<rightarrow> 'a"

definition
  p :: "'a \<rightarrow> 'a" where
  "p = fix\<cdot>(LAM f. LAM x. If b1\<cdot>x then f\<cdot>(g\<cdot>x) else x)"

definition
  q :: "'a \<rightarrow> 'a" where
  "q = fix\<cdot>(LAM f. LAM x. If b1\<cdot>x orelse b2\<cdot>x then f\<cdot>(g\<cdot>x) else x)"


(* --------- pure HOLCF logic, some little lemmas ------ *)

lemma hoare_lemma2: "b \<noteq> TT \<Longrightarrow> b = FF \<or> b = UU"
apply (rule Exh_tr [THEN disjE])
apply blast+
done

lemma hoare_lemma3: "(\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) \<or> (\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT)"
apply blast
done

lemma hoare_lemma4: "(\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT) \<Longrightarrow>
  \<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = FF \<or> b1\<cdot>(iterate k\<cdot>g\<cdot>x) = UU"
apply (erule exE)
apply (rule exI)
apply (rule hoare_lemma2)
apply assumption
done

lemma hoare_lemma5: "\<lbrakk>(\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT);
    k = Least (\<lambda>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT)\<rbrakk> \<Longrightarrow>
  b1\<cdot>(iterate k\<cdot>g\<cdot>x) = FF \<or> b1\<cdot>(iterate k\<cdot>g\<cdot>x) = UU"
apply hypsubst
apply (rule hoare_lemma2)
apply (erule exE)
apply (erule LeastI)
done

lemma hoare_lemma6: "b = UU \<Longrightarrow> b \<noteq> TT"
apply hypsubst
apply (rule dist_eq_tr)
done

lemma hoare_lemma7: "b = FF \<Longrightarrow> b \<noteq> TT"
apply hypsubst
apply (rule dist_eq_tr)
done

lemma hoare_lemma8: "\<lbrakk>(\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT);
    k = Least (\<lambda>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT)\<rbrakk> \<Longrightarrow>
  \<forall>m. m < k \<longrightarrow> b1\<cdot>(iterate m\<cdot>g\<cdot>x) = TT"
apply hypsubst
apply (erule exE)
apply (intro strip)
apply (rule_tac p = "b1\<cdot>(iterate m\<cdot>g\<cdot>x)" in trE)
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


lemma hoare_lemma28: "f\<cdot>(y::'a) = (UU::tr) \<Longrightarrow> f\<cdot>UU = UU"
by (rule strictI)


(* ----- access to definitions ----- *)

lemma p_def3: "p\<cdot>x = If b1\<cdot>x then p\<cdot>(g\<cdot>x) else x"
apply (rule trans)
apply (rule p_def [THEN eq_reflection, THEN fix_eq3])
apply simp
done

lemma q_def3: "q\<cdot>x = If b1\<cdot>x orelse b2\<cdot>x then q\<cdot>(g\<cdot>x) else x"
apply (rule trans)
apply (rule q_def [THEN eq_reflection, THEN fix_eq3])
apply simp
done

(** --------- proofs about iterations of p and q ---------- **)

lemma hoare_lemma9: "(\<forall>m. m < Suc k \<longrightarrow> b1\<cdot>(iterate m\<cdot>g\<cdot>x) = TT) \<longrightarrow>
   p\<cdot>(iterate k\<cdot>g\<cdot>x) = p\<cdot>x"
apply (induct_tac k)
apply (simp (no_asm))
apply (simp (no_asm))
apply (intro strip)
apply (rule_tac s = "p\<cdot>(iterate n\<cdot>g\<cdot>x)" in trans)
apply (rule trans)
apply (rule_tac [2] p_def3 [symmetric])
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate n\<cdot>g\<cdot>x)" in ssubst)
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

lemma hoare_lemma24: "(\<forall>m. m < Suc k \<longrightarrow> b1\<cdot>(iterate m\<cdot>g\<cdot>x) = TT) \<longrightarrow>
  q\<cdot>(iterate k\<cdot>g\<cdot>x) = q\<cdot>x"
apply (induct_tac k)
apply (simp (no_asm))
apply (simp (no_asm) add: less_Suc_eq)
apply (intro strip)
apply (rule_tac s = "q\<cdot>(iterate n\<cdot>g\<cdot>x)" in trans)
apply (rule trans)
apply (rule_tac [2] q_def3 [symmetric])
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate n\<cdot>g\<cdot>x)" in ssubst)
apply blast
apply simp
apply (erule mp)
apply (intro strip)
apply (fast dest!: less_Suc_eq [THEN iffD1])
done

(* -------- results about p for case (\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT) ------- *)

lemma hoare_lemma10:
  "\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT
    \<Longrightarrow> Suc k = (LEAST n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<Longrightarrow> p\<cdot>(iterate k\<cdot>g\<cdot>x) = p\<cdot>x"
  by (rule hoare_lemma8 [THEN hoare_lemma9 [THEN mp]])

lemma hoare_lemma11: "(\<exists>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<Longrightarrow>
  k = (LEAST n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<and> b1\<cdot>(iterate k\<cdot>g\<cdot>x) = FF
  \<longrightarrow> p\<cdot>x = iterate k\<cdot>g\<cdot>x"
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
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate nat\<cdot>g\<cdot>x)" in ssubst)
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

lemma hoare_lemma12: "(\<exists>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<Longrightarrow>
  k = Least (\<lambda>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<and> b1\<cdot>(iterate k\<cdot>g\<cdot>x) = UU
  \<longrightarrow> p\<cdot>x = UU"
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
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate nat\<cdot>g\<cdot>x)" in ssubst)
apply (rule hoare_lemma8 [THEN spec, THEN mp])
apply assumption
apply assumption
apply (simp (no_asm))
apply (simp)
apply (rule trans)
apply (rule p_def3)
apply simp
done

(* -------- results about p for case  (\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) ------- *)

lemma fernpass_lemma: "(\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) \<Longrightarrow> \<forall>k. p\<cdot>(iterate k\<cdot>g\<cdot>x) = UU"
apply (rule p_def [THEN eq_reflection, THEN def_fix_ind])
apply simp
apply simp
apply (simp (no_asm))
apply (rule allI)
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate k\<cdot>g\<cdot>x)" in ssubst)
apply (erule spec)
apply (simp)
apply (rule iterate_Suc [THEN subst])
apply (erule spec)
done

lemma hoare_lemma16: "(\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) \<Longrightarrow> p\<cdot>x = UU"
apply (rule_tac F1 = "g" and t = "x" in iterate_0 [THEN subst])
apply (erule fernpass_lemma [THEN spec])
done

(* -------- results about q for case  (\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) ------- *)

lemma hoare_lemma17: "(\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) \<Longrightarrow> \<forall>k. q\<cdot>(iterate k\<cdot>g\<cdot>x) = UU"
apply (rule q_def [THEN eq_reflection, THEN def_fix_ind])
apply simp
apply simp
apply (rule allI)
apply (simp (no_asm))
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate k\<cdot>g\<cdot>x)" in ssubst)
apply (erule spec)
apply (simp)
apply (rule iterate_Suc [THEN subst])
apply (erule spec)
done

lemma hoare_lemma18: "(\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) \<Longrightarrow> q\<cdot>x = UU"
apply (rule_tac F1 = "g" and t = "x" in iterate_0 [THEN subst])
apply (erule hoare_lemma17 [THEN spec])
done

lemma hoare_lemma19:
  "(\<forall>k. (b1::'a\<rightarrow>tr)\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) \<Longrightarrow> b1\<cdot>(UU::'a) = UU \<or> (\<forall>y. b1\<cdot>(y::'a) = TT)"
apply (rule flat_codom)
apply (rule_tac t = "x" in iterate_0 [THEN subst])
apply (erule spec)
done

lemma hoare_lemma20: "(\<forall>y. b1\<cdot>(y::'a) = TT) \<Longrightarrow> \<forall>k. q\<cdot>(iterate k\<cdot>g\<cdot>(x::'a)) = UU"
apply (rule q_def [THEN eq_reflection, THEN def_fix_ind])
apply simp
apply simp
apply (rule allI)
apply (simp (no_asm))
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate k\<cdot>g\<cdot>(x::'a))" in ssubst)
apply (erule spec)
apply (simp)
apply (rule iterate_Suc [THEN subst])
apply (erule spec)
done

lemma hoare_lemma21: "(\<forall>y. b1\<cdot>(y::'a) = TT) \<Longrightarrow> q\<cdot>(x::'a) = UU"
apply (rule_tac F1 = "g" and t = "x" in iterate_0 [THEN subst])
apply (erule hoare_lemma20 [THEN spec])
done

lemma hoare_lemma22: "b1\<cdot>(UU::'a) = UU \<Longrightarrow> q\<cdot>(UU::'a) = UU"
apply (subst q_def3)
apply simp
done

(* -------- results about q for case (\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT) ------- *)

lemma hoare_lemma25: "\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT
  \<Longrightarrow> Suc k = (LEAST n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<Longrightarrow> q\<cdot>(iterate k\<cdot>g\<cdot>x) = q\<cdot>x"
  by (rule hoare_lemma8 [THEN hoare_lemma24 [THEN mp]])

lemma hoare_lemma26: "(\<exists>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<Longrightarrow>
  k = Least (\<lambda>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<and> b1\<cdot>(iterate k\<cdot>g\<cdot>x) = FF
  \<longrightarrow> q\<cdot>x = q\<cdot>(iterate k\<cdot>g\<cdot>x)"
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
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate nat\<cdot>g\<cdot>x)" in ssubst)
apply (rule hoare_lemma8 [THEN spec, THEN mp])
apply assumption
apply assumption
apply (simp (no_asm))
apply (simp (no_asm))
done


lemma hoare_lemma27: "(\<exists>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<Longrightarrow>
  k = Least(\<lambda>n. b1\<cdot>(iterate n\<cdot>g\<cdot>x) \<noteq> TT) \<and> b1\<cdot>(iterate k\<cdot>g\<cdot>x) = UU
  \<longrightarrow> q\<cdot>x = UU"
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
apply (rule_tac s = "TT" and t = "b1\<cdot>(iterate nat\<cdot>g\<cdot>x)" in ssubst)
apply (rule hoare_lemma8 [THEN spec, THEN mp])
apply assumption
apply assumption
apply (simp (no_asm))
apply (simp)
apply (rule trans)
apply (rule q_def3)
apply (simp)
done

(* ------- (\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) \<Longrightarrow> q \<circ> p = q   ----- *)

lemma hoare_lemma23: "(\<forall>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) = TT) \<Longrightarrow> q\<cdot>(p\<cdot>x) = q\<cdot>x"
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

(* ------------  \<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT \<Longrightarrow> q \<circ> p = q   ----- *)

lemma hoare_lemma29: "\<exists>k. b1\<cdot>(iterate k\<cdot>g\<cdot>x) \<noteq> TT \<Longrightarrow> q\<cdot>(p\<cdot>x) = q\<cdot>x"
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

(* ------ the main proof q \<circ> p = q ------ *)

theorem hoare_main: "q oo p = q"
apply (rule cfun_eqI)
apply (subst cfcomp2)
apply (rule hoare_lemma3 [THEN disjE])
apply (erule hoare_lemma23)
apply (erule hoare_lemma29)
done

end
