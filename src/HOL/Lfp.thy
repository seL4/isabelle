(*  Title:      HOL/Lfp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header{*Least Fixed Points and the Knaster-Tarski Theorem*}

theory Lfp
imports Product_Type
begin

constdefs
  lfp :: "['a set \<Rightarrow> 'a set] \<Rightarrow> 'a set"
    "lfp(f) == Inter({u. f(u) \<subseteq> u})"    --{*least fixed point*}



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
*}

end
