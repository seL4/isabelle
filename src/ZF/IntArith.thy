
theory IntArith imports Bin
uses ("int_arith.ML")
begin


(** To simplify inequalities involving integer negation and literals,
    such as -x = #3
**)

lemmas [simp] =
  zminus_equation [where y = "integ_of(w)"]
  equation_zminus [where x = "integ_of(w)"]
  for w

lemmas [iff] =
  zminus_zless [where y = "integ_of(w)"]
  zless_zminus [where x = "integ_of(w)"]
  for w

lemmas [iff] =
  zminus_zle [where y = "integ_of(w)"]
  zle_zminus [where x = "integ_of(w)"]
  for w

lemmas [simp] =
  Let_def [where s = "integ_of(w)"] for w


(*** Simprocs for numeric literals ***)

(** Combining of literal coefficients in sums of products **)

lemma zless_iff_zdiff_zless_0: "(x $< y) \<longleftrightarrow> (x$-y $< #0)"
  by (simp add: zcompare_rls)

lemma eq_iff_zdiff_eq_0: "[| x: int; y: int |] ==> (x = y) \<longleftrightarrow> (x$-y = #0)"
  by (simp add: zcompare_rls)

lemma zle_iff_zdiff_zle_0: "(x $<= y) \<longleftrightarrow> (x$-y $<= #0)"
  by (simp add: zcompare_rls)


(** For combine_numerals **)

lemma left_zadd_zmult_distrib: "i$*u $+ (j$*u $+ k) = (i$+j)$*u $+ k"
  by (simp add: zadd_zmult_distrib zadd_ac)


(** For cancel_numerals **)

lemmas rel_iff_rel_0_rls =
  zless_iff_zdiff_zless_0 [where y = "u $+ v"]
  eq_iff_zdiff_eq_0 [where y = "u $+ v"]
  zle_iff_zdiff_zle_0 [where y = "u $+ v"]
  zless_iff_zdiff_zless_0 [where y = n]
  eq_iff_zdiff_eq_0 [where y = n]
  zle_iff_zdiff_zle_0 [where y = n]
  for u v (* FIXME n (!?) *)

lemma eq_add_iff1: "(i$*u $+ m = j$*u $+ n) \<longleftrightarrow> ((i$-j)$*u $+ m = intify(n))"
  apply (simp add: zdiff_def zadd_zmult_distrib)
  apply (simp add: zcompare_rls)
  apply (simp add: zadd_ac)
  done

lemma eq_add_iff2: "(i$*u $+ m = j$*u $+ n) \<longleftrightarrow> (intify(m) = (j$-i)$*u $+ n)"
  apply (simp add: zdiff_def zadd_zmult_distrib)
  apply (simp add: zcompare_rls)
  apply (simp add: zadd_ac)
  done

lemma less_add_iff1: "(i$*u $+ m $< j$*u $+ n) \<longleftrightarrow> ((i$-j)$*u $+ m $< n)"
  apply (simp add: zdiff_def zadd_zmult_distrib zadd_ac rel_iff_rel_0_rls)
  done

lemma less_add_iff2: "(i$*u $+ m $< j$*u $+ n) \<longleftrightarrow> (m $< (j$-i)$*u $+ n)"
  apply (simp add: zdiff_def zadd_zmult_distrib zadd_ac rel_iff_rel_0_rls)
  done

lemma le_add_iff1: "(i$*u $+ m $<= j$*u $+ n) \<longleftrightarrow> ((i$-j)$*u $+ m $<= n)"
  apply (simp add: zdiff_def zadd_zmult_distrib)
  apply (simp add: zcompare_rls)
  apply (simp add: zadd_ac)
  done

lemma le_add_iff2: "(i$*u $+ m $<= j$*u $+ n) \<longleftrightarrow> (m $<= (j$-i)$*u $+ n)"
  apply (simp add: zdiff_def zadd_zmult_distrib)
  apply (simp add: zcompare_rls)
  apply (simp add: zadd_ac)
  done

use "int_arith.ML"

end
