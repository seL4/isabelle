(*  Title:      HOL/Extraction/QuotRem.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Quotient and remainder *}

theory QuotRem = Main:

text {* Derivation of quotient and remainder using program extraction. *}

consts_code
  arbitrary :: sumbool ("{* Left *}")

lemma le_lt_eq_dec: "\<And>m::nat. n <= m \<Longrightarrow> n < m \<or> n = m"
  apply (induct n)
  apply (case_tac m)
  apply simp
  apply simp
  apply (case_tac m)
  apply simp
  apply simp
  done

lemma division: "\<exists>r q. a = Suc b * q + r \<and> r <= b"
  apply (induct a)
  apply (rule_tac x = 0 in exI)
  apply (rule_tac x = 0 in exI)
  apply simp
  apply (erule exE)
  apply (erule exE)
  apply (erule conjE)
  apply (drule le_lt_eq_dec)
  apply (erule disjE)
  apply (rule_tac x = "Suc r" in exI)
  apply (rule_tac x = q in exI)
  apply simp
  apply (rule_tac x = 0 in exI)
  apply (rule_tac x = "Suc q" in exI)
  apply simp
  done

extract division

text {*
  The program extracted from the above proof looks as follows
  @{thm [display] division_def [no_vars]}
  The corresponding correctness theorem is
  @{thm [display] division_correctness [no_vars]}
*}

generate_code
  test = "division 9 2"

end
