(*  Title:      HOL/Hoare/Pointer_ExamplesAbort.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TUM

Examples of verifications of pointer programs
*)

theory Pointer_ExamplesAbort = HeapSyntaxAbort:

section "Verifications"

subsection "List reversal"

text "Interestingly, this proof is the same as for the unguarded program:"

lemma "VARS tl p q r
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {}}
  WHILE p \<noteq> Null
  INV {\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                 rev ps @ qs = rev Ps @ Qs}
  DO r := p; (p \<noteq> Null \<rightarrow> p := p^.tl); r^.tl := q; q := r OD
  {List tl q (rev Ps @ Qs)}"
apply vcg_simp
  apply fastsimp
 apply(fastsimp intro:notin_List_update[THEN iffD2])
apply fastsimp
done

end
