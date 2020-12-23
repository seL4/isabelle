(*  Title:      HOL/Hoare/Pointer_ExamplesAbort.thy
    Author:     Tobias Nipkow
    Copyright   2002 TUM
*)

section \<open>Examples of verifications of pointer programs\<close>

theory Pointer_ExamplesAbort
  imports HeapSyntaxAbort
begin

subsection "Verifications"

subsubsection "List reversal"

text "Interestingly, this proof is the same as for the unguarded program:"

lemma "VARS tl p q r
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {}}
  WHILE p \<noteq> Null
  INV {\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                 rev ps @ qs = rev Ps @ Qs}
  DO r := p; (p \<noteq> Null \<rightarrow> p := p^.tl); r^.tl := q; q := r OD
  {List tl q (rev Ps @ Qs)}"
apply vcg_simp
  apply fastforce
 apply(fastforce intro:notin_List_update[THEN iffD2])
done

end
