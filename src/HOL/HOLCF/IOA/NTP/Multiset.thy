(*  Title:      HOL/HOLCF/IOA/NTP/Multiset.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

header {* Axiomatic multisets *}

theory Multiset
imports Lemmas
begin

typedecl
  'a multiset

consts

  emptym :: "'a multiset"                        ("{|}")
  addm   :: "['a multiset, 'a] => 'a multiset"
  delm   :: "['a multiset, 'a] => 'a multiset"
  countm :: "['a multiset, 'a => bool] => nat"
  count  :: "['a multiset, 'a] => nat"

axiomatization where

delm_empty_def:
  "delm {|} x = {|}" and

delm_nonempty_def:
  "delm (addm M x) y == (if x=y then M else addm (delm M y) x)" and

countm_empty_def:
   "countm {|} P == 0" and

countm_nonempty_def:
   "countm (addm M x) P == countm M P + (if P x then Suc 0 else 0)" and

count_def:
   "count M x == countm M (%y. y = x)" and

"induction":
   "\<And>P M. [| P({|}); !!M x. P(M) ==> P(addm M x) |] ==> P(M)"

lemma count_empty: 
   "count {|} x = 0"
  by (simp add: Multiset.count_def Multiset.countm_empty_def)

lemma count_addm_simp: 
     "count (addm M x) y = (if y=x then Suc(count M y) else count M y)"
  by (simp add: Multiset.count_def Multiset.countm_nonempty_def)

lemma count_leq_addm: "count M y <= count (addm M x) y"
  by (simp add: count_addm_simp)

lemma count_delm_simp: 
     "count (delm M x) y = (if y=x then count M y - 1 else count M y)"
apply (unfold Multiset.count_def)
apply (rule_tac M = "M" in Multiset.induction)
apply (simp (no_asm_simp) add: Multiset.delm_empty_def Multiset.countm_empty_def)
apply (simp add: Multiset.delm_nonempty_def Multiset.countm_nonempty_def)
apply safe
apply simp
done

lemma countm_props: "!!M. (!x. P(x) --> Q(x)) ==> (countm M P <= countm M Q)"
apply (rule_tac M = "M" in Multiset.induction)
 apply (simp (no_asm) add: Multiset.countm_empty_def)
apply (simp (no_asm) add: Multiset.countm_nonempty_def)
apply auto
done

lemma countm_spurious_delm: "!!P. ~P(obj) ==> countm M P = countm (delm M obj) P"
  apply (rule_tac M = "M" in Multiset.induction)
  apply (simp (no_asm) add: Multiset.delm_empty_def Multiset.countm_empty_def)
  apply (simp (no_asm_simp) add: Multiset.countm_nonempty_def Multiset.delm_nonempty_def)
  done


lemma pos_count_imp_pos_countm [rule_format (no_asm)]: "!!P. P(x) ==> 0<count M x --> countm M P > 0"
  apply (rule_tac M = "M" in Multiset.induction)
  apply (simp (no_asm) add: Multiset.delm_empty_def Multiset.count_def Multiset.countm_empty_def)
  apply (simp add: Multiset.count_def Multiset.delm_nonempty_def Multiset.countm_nonempty_def)
  done

lemma countm_done_delm: 
   "!!P. P(x) ==> 0<count M x --> countm (delm M x) P = countm M P - 1"
  apply (rule_tac M = "M" in Multiset.induction)
  apply (simp (no_asm) add: Multiset.delm_empty_def Multiset.countm_empty_def)
  apply (simp (no_asm_simp) add: count_addm_simp Multiset.delm_nonempty_def Multiset.countm_nonempty_def pos_count_imp_pos_countm)
  apply auto
  done


declare count_addm_simp [simp] count_delm_simp [simp]
  Multiset.countm_empty_def [simp] Multiset.delm_empty_def [simp] count_empty [simp]

end
