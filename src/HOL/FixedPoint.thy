(*  Title:      HOL/FixedPoint.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header{* Fixed Points and the Knaster-Tarski Theorem*}

theory FixedPoint
imports Product_Type
begin

constdefs
  lfp :: "['a set \<Rightarrow> 'a set] \<Rightarrow> 'a set"
    "lfp(f) == Inter({u. f(u) \<subseteq> u})"    --{*least fixed point*}

  gfp :: "['a set=>'a set] => 'a set"
    "gfp(f) == Union({u. u \<subseteq> f(u)})"


subsection{*Proof of Knaster-Tarski Theorem using @{term lfp}*}


text{*@{term "lfp f"} is the least upper bound of 
      the set @{term "{u. f(u) \<subseteq> u}"} *}

lemma lfp_lowerbound: "f(A) \<subseteq> A ==> lfp(f) \<subseteq> A"
by (auto simp add: lfp_def)

lemma lfp_greatest: "[| !!u. f(u) \<subseteq> u ==> A\<subseteq>u |] ==> A \<subseteq> lfp(f)"
by (auto simp add: lfp_def)

lemma lfp_lemma2: "mono(f) ==> f(lfp(f)) \<subseteq> lfp(f)"
by (rules intro: lfp_greatest subset_trans monoD lfp_lowerbound)

lemma lfp_lemma3: "mono(f) ==> lfp(f) \<subseteq> f(lfp(f))"
by (rules intro: lfp_lemma2 monoD lfp_lowerbound)

lemma lfp_unfold: "mono(f) ==> lfp(f) = f(lfp(f))"
by (rules intro: equalityI lfp_lemma2 lfp_lemma3)

subsection{*General induction rules for greatest fixed points*}

lemma lfp_induct: 
  assumes lfp: "a: lfp(f)"
      and mono: "mono(f)"
      and indhyp: "!!x. [| x: f(lfp(f) Int {x. P(x)}) |] ==> P(x)"
  shows "P(a)"
apply (rule_tac a=a in Int_lower2 [THEN subsetD, THEN CollectD]) 
apply (rule lfp [THEN [2] lfp_lowerbound [THEN subsetD]]) 
apply (rule Int_greatest)
 apply (rule subset_trans [OF Int_lower1 [THEN mono [THEN monoD]]
                              mono [THEN lfp_lemma2]]) 
apply (blast intro: indhyp) 
done


text{*Version of induction for binary relations*}
lemmas lfp_induct2 =  lfp_induct [of "(a,b)", split_format (complete)]


lemma lfp_ordinal_induct: 
  assumes mono: "mono f"
  shows "[| !!S. P S ==> P(f S); !!M. !S:M. P S ==> P(Union M) |] 
         ==> P(lfp f)"
apply(subgoal_tac "lfp f = Union{S. S \<subseteq> lfp f & P S}")
 apply (erule ssubst, simp) 
apply(subgoal_tac "Union{S. S \<subseteq> lfp f & P S} \<subseteq> lfp f")
 prefer 2 apply blast
apply(rule equalityI)
 prefer 2 apply assumption
apply(drule mono [THEN monoD])
apply (cut_tac mono [THEN lfp_unfold], simp)
apply (rule lfp_lowerbound, auto) 
done


text{*Definition forms of @{text lfp_unfold} and @{text lfp_induct}, 
    to control unfolding*}

lemma def_lfp_unfold: "[| h==lfp(f);  mono(f) |] ==> h = f(h)"
by (auto intro!: lfp_unfold)

lemma def_lfp_induct: 
    "[| A == lfp(f);  mono(f);   a:A;                    
        !!x. [| x: f(A Int {x. P(x)}) |] ==> P(x)         
     |] ==> P(a)"
by (blast intro: lfp_induct)

(*Monotonicity of lfp!*)
lemma lfp_mono: "[| !!Z. f(Z)\<subseteq>g(Z) |] ==> lfp(f) \<subseteq> lfp(g)"
by (rule lfp_lowerbound [THEN lfp_greatest], blast)


subsection{*Proof of Knaster-Tarski Theorem using @{term gfp}*}


text{*@{term "gfp f"} is the greatest lower bound of 
      the set @{term "{u. u \<subseteq> f(u)}"} *}

lemma gfp_upperbound: "[| X \<subseteq> f(X) |] ==> X \<subseteq> gfp(f)"
by (auto simp add: gfp_def)

lemma gfp_least: "[| !!u. u \<subseteq> f(u) ==> u\<subseteq>X |] ==> gfp(f) \<subseteq> X"
by (auto simp add: gfp_def)

lemma gfp_lemma2: "mono(f) ==> gfp(f) \<subseteq> f(gfp(f))"
by (rules intro: gfp_least subset_trans monoD gfp_upperbound)

lemma gfp_lemma3: "mono(f) ==> f(gfp(f)) \<subseteq> gfp(f)"
by (rules intro: gfp_lemma2 monoD gfp_upperbound)

lemma gfp_unfold: "mono(f) ==> gfp(f) = f(gfp(f))"
by (rules intro: equalityI gfp_lemma2 gfp_lemma3)

subsection{*Coinduction rules for greatest fixed points*}

text{*weak version*}
lemma weak_coinduct: "[| a: X;  X \<subseteq> f(X) |] ==> a : gfp(f)"
by (rule gfp_upperbound [THEN subsetD], auto)

lemma weak_coinduct_image: "!!X. [| a : X; g`X \<subseteq> f (g`X) |] ==> g a : gfp f"
apply (erule gfp_upperbound [THEN subsetD])
apply (erule imageI)
done

lemma coinduct_lemma:
     "[| X \<subseteq> f(X Un gfp(f));  mono(f) |] ==> X Un gfp(f) \<subseteq> f(X Un gfp(f))"
by (blast dest: gfp_lemma2 mono_Un)

text{*strong version, thanks to Coen and Frost*}
lemma coinduct: "[| mono(f);  a: X;  X \<subseteq> f(X Un gfp(f)) |] ==> a : gfp(f)"
by (blast intro: weak_coinduct [OF _ coinduct_lemma])

lemma gfp_fun_UnI2: "[| mono(f);  a: gfp(f) |] ==> a: f(X Un gfp(f))"
by (blast dest: gfp_lemma2 mono_Un)

subsection{*Even Stronger Coinduction Rule, by Martin Coen*}

text{* Weakens the condition @{term "X \<subseteq> f(X)"} to one expressed using both
  @{term lfp} and @{term gfp}*}

lemma coinduct3_mono_lemma: "mono(f) ==> mono(%x. f(x) Un X Un B)"
by (rules intro: subset_refl monoI Un_mono monoD)

lemma coinduct3_lemma:
     "[| X \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f)));  mono(f) |]
      ==> lfp(%x. f(x) Un X Un gfp(f)) \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f)))"
apply (rule subset_trans)
apply (erule coinduct3_mono_lemma [THEN lfp_lemma3])
apply (rule Un_least [THEN Un_least])
apply (rule subset_refl, assumption)
apply (rule gfp_unfold [THEN equalityD1, THEN subset_trans], assumption)
apply (rule monoD, assumption)
apply (subst coinduct3_mono_lemma [THEN lfp_unfold], auto)
done

lemma coinduct3: 
  "[| mono(f);  a:X;  X \<subseteq> f(lfp(%x. f(x) Un X Un gfp(f))) |] ==> a : gfp(f)"
apply (rule coinduct3_lemma [THEN [2] weak_coinduct])
apply (rule coinduct3_mono_lemma [THEN lfp_unfold, THEN ssubst], auto)
done


text{*Definition forms of @{text gfp_unfold} and @{text coinduct}, 
    to control unfolding*}

lemma def_gfp_unfold: "[| A==gfp(f);  mono(f) |] ==> A = f(A)"
by (auto intro!: gfp_unfold)

lemma def_coinduct:
     "[| A==gfp(f);  mono(f);  a:X;  X \<subseteq> f(X Un A) |] ==> a: A"
by (auto intro!: coinduct)

(*The version used in the induction/coinduction package*)
lemma def_Collect_coinduct:
    "[| A == gfp(%w. Collect(P(w)));  mono(%w. Collect(P(w)));   
        a: X;  !!z. z: X ==> P (X Un A) z |] ==>  
     a : A"
apply (erule def_coinduct, auto) 
done

lemma def_coinduct3:
    "[| A==gfp(f); mono(f);  a:X;  X \<subseteq> f(lfp(%x. f(x) Un X Un A)) |] ==> a: A"
by (auto intro!: coinduct3)

text{*Monotonicity of @{term gfp}!*}
lemma gfp_mono: "[| !!Z. f(Z)\<subseteq>g(Z) |] ==> gfp(f) \<subseteq> gfp(g)"
by (rule gfp_upperbound [THEN gfp_least], blast)


ML
{*
val lfp_def = thm "lfp_def";
val lfp_lowerbound = thm "lfp_lowerbound";
val lfp_greatest = thm "lfp_greatest";
val lfp_unfold = thm "lfp_unfold";
val lfp_induct = thm "lfp_induct";
val lfp_induct2 = thm "lfp_induct2";
val lfp_ordinal_induct = thm "lfp_ordinal_induct";
val def_lfp_unfold = thm "def_lfp_unfold";
val def_lfp_induct = thm "def_lfp_induct";
val lfp_mono = thm "lfp_mono";
val gfp_def = thm "gfp_def";
val gfp_upperbound = thm "gfp_upperbound";
val gfp_least = thm "gfp_least";
val gfp_unfold = thm "gfp_unfold";
val weak_coinduct = thm "weak_coinduct";
val weak_coinduct_image = thm "weak_coinduct_image";
val coinduct = thm "coinduct";
val gfp_fun_UnI2 = thm "gfp_fun_UnI2";
val coinduct3 = thm "coinduct3";
val def_gfp_unfold = thm "def_gfp_unfold";
val def_coinduct = thm "def_coinduct";
val def_Collect_coinduct = thm "def_Collect_coinduct";
val def_coinduct3 = thm "def_coinduct3";
val gfp_mono = thm "gfp_mono";
*}

end
