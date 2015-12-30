(*  Title:      HOL/HOLCF/IOA/meta_theory/TL.thy
    Author:     Olaf Müller
*)

section \<open>A General Temporal Logic\<close>

theory TL
imports Pred Sequence
begin

default_sort type

type_synonym
  'a temporal = "'a Seq predicate"


consts
suffix     :: "'a Seq => 'a Seq => bool"
tsuffix    :: "'a Seq => 'a Seq => bool"

validT     :: "'a Seq predicate => bool"

unlift     ::  "'a lift => 'a"

Init       :: "'a predicate => 'a temporal"  ("\<langle>_\<rangle>" [0] 1000)

Box        :: "'a temporal => 'a temporal"   ("\<box>(_)" [80] 80)
Diamond    :: "'a temporal => 'a temporal"   ("\<diamond>(_)" [80] 80)
Next       :: "'a temporal => 'a temporal"
Leadsto    :: "'a temporal => 'a temporal => 'a temporal"  (infixr "\<leadsto>" 22)

defs

unlift_def:
  "unlift x == (case x of Def y   => y)"

(* this means that for nil and UU the effect is unpredictable *)
Init_def:
  "Init P s ==  (P (unlift (HD$s)))"

suffix_def:
  "suffix s2 s == ? s1. (Finite s1  & s = s1 @@ s2)"

tsuffix_def:
  "tsuffix s2 s == s2 ~= nil & s2 ~= UU & suffix s2 s"

Box_def:
  "(\<box>P) s == ! s2. tsuffix s2 s --> P s2"

Next_def:
  "(Next P) s == if (TL$s=UU | TL$s=nil) then (P s) else P (TL$s)"

Diamond_def:
  "\<diamond>P == \<^bold>\<not> (\<box>(\<^bold>\<not> P))"

Leadsto_def:
   "P \<leadsto> Q == (\<box>(P \<^bold>\<longrightarrow> (\<diamond>Q)))"

validT_def:
  "validT P == ! s. s~=UU & s~=nil --> (s \<Turnstile> P)"


lemma simple: "\<box>\<diamond>(\<^bold>\<not> P) = (\<^bold>\<not> \<diamond>\<box>P)"
apply (rule ext)
apply (simp add: Diamond_def NOT_def Box_def)
done

lemma Boxnil: "nil \<Turnstile> \<box>P"
apply (simp add: satisfies_def Box_def tsuffix_def suffix_def nil_is_Conc)
done

lemma Diamondnil: "~(nil \<Turnstile> \<diamond>P)"
apply (simp add: Diamond_def satisfies_def NOT_def)
apply (cut_tac Boxnil)
apply (simp add: satisfies_def)
done

lemma Diamond_def2: "(\<diamond>F) s = (? s2. tsuffix s2 s & F s2)"
apply (simp add: Diamond_def NOT_def Box_def)
done



subsection "TLA Axiomatization by Merz"

lemma suffix_refl: "suffix s s"
apply (simp add: suffix_def)
apply (rule_tac x = "nil" in exI)
apply auto
done

lemma reflT: "s~=UU & s~=nil --> (s \<Turnstile> \<box>F \<^bold>\<longrightarrow> F)"
apply (simp add: satisfies_def IMPLIES_def Box_def)
apply (rule impI)+
apply (erule_tac x = "s" in allE)
apply (simp add: tsuffix_def suffix_refl)
done


lemma suffix_trans: "[| suffix y x ; suffix z y |]  ==> suffix z x"
apply (simp add: suffix_def)
apply auto
apply (rule_tac x = "s1 @@ s1a" in exI)
apply auto
apply (simp (no_asm) add: Conc_assoc)
done

lemma transT: "s \<Turnstile> \<box>F \<^bold>\<longrightarrow> \<box>\<box>F"
apply (simp (no_asm) add: satisfies_def IMPLIES_def Box_def tsuffix_def)
apply auto
apply (drule suffix_trans)
apply assumption
apply (erule_tac x = "s2a" in allE)
apply auto
done


lemma normalT: "s \<Turnstile> \<box>(F \<^bold>\<longrightarrow> G) \<^bold>\<longrightarrow> \<box>F \<^bold>\<longrightarrow> \<box>G"
apply (simp (no_asm) add: satisfies_def IMPLIES_def Box_def)
done


subsection "TLA Rules by Lamport"

lemma STL1a: "validT P ==> validT (\<box>P)"
apply (simp add: validT_def satisfies_def Box_def tsuffix_def)
done

lemma STL1b: "valid P ==> validT (Init P)"
apply (simp add: valid_def validT_def satisfies_def Init_def)
done

lemma STL1: "valid P ==> validT (\<box>(Init P))"
apply (rule STL1a)
apply (erule STL1b)
done

(* Note that unlift and HD is not at all used !!! *)
lemma STL4: "valid (P \<^bold>\<longrightarrow> Q)  ==> validT (\<box>(Init P) \<^bold>\<longrightarrow> \<box>(Init Q))"
apply (simp add: valid_def validT_def satisfies_def IMPLIES_def Box_def Init_def)
done


subsection "LTL Axioms by Manna/Pnueli"

lemma tsuffix_TL [rule_format (no_asm)]: 
"s~=UU & s~=nil --> tsuffix s2 (TL$s) --> tsuffix s2 s"
apply (unfold tsuffix_def suffix_def)
apply auto
apply (tactic \<open>Seq_case_simp_tac @{context} "s" 1\<close>)
apply (rule_tac x = "a\<leadsto>s1" in exI)
apply auto
done

lemmas tsuffix_TL2 = conjI [THEN tsuffix_TL]

declare split_if [split del]
lemma LTL1: 
   "s~=UU & s~=nil --> (s \<Turnstile> \<box>F \<^bold>\<longrightarrow> (F \<^bold>\<and> (Next (\<box>F))))"
apply (unfold Next_def satisfies_def NOT_def IMPLIES_def AND_def Box_def)
apply auto
(* \<box>F \<^bold>\<longrightarrow> F *)
apply (erule_tac x = "s" in allE)
apply (simp add: tsuffix_def suffix_refl)
(* \<box>F \<^bold>\<longrightarrow> Next \<box>F *)
apply (simp split add: split_if)
apply auto
apply (drule tsuffix_TL2)
apply assumption+
apply auto
done
declare split_if [split]


lemma LTL2a: 
    "s \<Turnstile> \<^bold>\<not> (Next F) \<^bold>\<longrightarrow> (Next (\<^bold>\<not> F))"
apply (unfold Next_def satisfies_def NOT_def IMPLIES_def)
apply simp
done

lemma LTL2b: 
    "s \<Turnstile> (Next (\<^bold>\<not> F)) \<^bold>\<longrightarrow> (\<^bold>\<not> (Next F))"
apply (unfold Next_def satisfies_def NOT_def IMPLIES_def)
apply simp
done

lemma LTL3: 
"ex \<Turnstile> (Next (F \<^bold>\<longrightarrow> G)) \<^bold>\<longrightarrow> (Next F) \<^bold>\<longrightarrow> (Next G)"
apply (unfold Next_def satisfies_def NOT_def IMPLIES_def)
apply simp
done


lemma ModusPonens: "[| validT (P \<^bold>\<longrightarrow> Q); validT P |] ==> validT Q"
apply (simp add: validT_def satisfies_def IMPLIES_def)
done

end
