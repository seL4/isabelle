(* ID:         $Id$ *)
theory Numbers = Real:

ML "Pretty.setmargin 64"
ML "IsarOutput.indent := 0"  (*we don't want 5 for listing theorems*)

text{*

numeric literals; default simprules; can re-orient
*}

lemma "#2 * m = m + m"
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
oops

consts h :: "nat \<Rightarrow> nat"
recdef h "{}"
"h i = (if i = #3 then #2 else i)"

text{*
@{term"h #3 = #2"}
@{term"h i  = i"}
*}

text{*
@{thm[display] numeral_0_eq_0[no_vars]}
\rulename{numeral_0_eq_0}

@{thm[display] numeral_1_eq_1[no_vars]}
\rulename{numeral_1_eq_1}

@{thm[display] add_2_eq_Suc[no_vars]}
\rulename{add_2_eq_Suc}

@{thm[display] add_2_eq_Suc'[no_vars]}
\rulename{add_2_eq_Suc'}

@{thm[display] add_assoc[no_vars]}
\rulename{add_assoc}

@{thm[display] add_commute[no_vars]}
\rulename{add_commute}

@{thm[display] add_left_commute[no_vars]}
\rulename{add_left_commute}

these form add_ac; similarly there is mult_ac
*}

lemma "Suc(i + j*l*k + m*n) = f (n*m + i + k*j*l)"
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply (simp add: add_ac mult_ac)
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
oops

text{*
@{thm[display] mult_le_mono[no_vars]}
\rulename{mult_le_mono}

@{thm[display] mult_less_mono1[no_vars]}
\rulename{mult_less_mono1}

@{thm[display] div_le_mono[no_vars]}
\rulename{div_le_mono}

@{thm[display] add_mult_distrib[no_vars]}
\rulename{add_mult_distrib}

@{thm[display] diff_mult_distrib[no_vars]}
\rulename{diff_mult_distrib}

@{thm[display] mod_mult_distrib[no_vars]}
\rulename{mod_mult_distrib}

@{thm[display] nat_diff_split[no_vars]}
\rulename{nat_diff_split}
*}


lemma "(n-1)*(n+1) = n*n - 1"
apply (simp split: nat_diff_split)
done

text{*
@{thm[display] mod_if[no_vars]}
\rulename{mod_if}

@{thm[display] mod_div_equality[no_vars]}
\rulename{mod_div_equality}


@{thm[display] div_mult1_eq[no_vars]}
\rulename{div_mult1_eq}

@{thm[display] mod_mult1_eq[no_vars]}
\rulename{mod_mult1_eq}

@{thm[display] div_mult2_eq[no_vars]}
\rulename{div_mult2_eq}

@{thm[display] mod_mult2_eq[no_vars]}
\rulename{mod_mult2_eq}

@{thm[display] div_mult_mult1[no_vars]}
\rulename{div_mult_mult1}

@{thm[display] DIVISION_BY_ZERO_DIV[no_vars]}
\rulename{DIVISION_BY_ZERO_DIV}

@{thm[display] DIVISION_BY_ZERO_MOD[no_vars]}
\rulename{DIVISION_BY_ZERO_MOD}

@{thm[display] dvd_anti_sym[no_vars]}
\rulename{dvd_anti_sym}

@{thm[display] dvd_add[no_vars]}
\rulename{dvd_add}

For the integers, I'd list a few theorems that somehow involve negative 
numbers.  

Division, remainder of negatives


@{thm[display] pos_mod_sign[no_vars]}
\rulename{pos_mod_sign}

@{thm[display] pos_mod_bound[no_vars]}
\rulename{pos_mod_bound}

@{thm[display] neg_mod_sign[no_vars]}
\rulename{neg_mod_sign}

@{thm[display] neg_mod_bound[no_vars]}
\rulename{neg_mod_bound}

@{thm[display] zdiv_zadd1_eq[no_vars]}
\rulename{zdiv_zadd1_eq}

@{thm[display] zmod_zadd1_eq[no_vars]}
\rulename{zmod_zadd1_eq}

@{thm[display] zdiv_zmult1_eq[no_vars]}
\rulename{zdiv_zmult1_eq}

@{thm[display] zmod_zmult1_eq[no_vars]}
\rulename{zmod_zmult1_eq}

@{thm[display] zdiv_zmult2_eq[no_vars]}
\rulename{zdiv_zmult2_eq}

@{thm[display] zmod_zmult2_eq[no_vars]}
\rulename{zmod_zmult2_eq}

@{thm[display] abs_mult[no_vars]}
\rulename{abs_mult}
*}  

lemma "\<lbrakk>abs x < a; abs y < b\<rbrakk> \<Longrightarrow> abs x + abs y < (a + b :: int)"
by arith

text {*REALS

@{thm[display] realpow_abs[no_vars]}
\rulename{realpow_abs}

@{thm[display] real_dense[no_vars]}
\rulename{real_dense}

@{thm[display] realpow_abs[no_vars]}
\rulename{realpow_abs}

@{thm[display] real_times_divide1_eq[no_vars]}
\rulename{real_times_divide1_eq}

@{thm[display] real_times_divide2_eq[no_vars]}
\rulename{real_times_divide2_eq}

@{thm[display] real_divide_divide1_eq[no_vars]}
\rulename{real_divide_divide1_eq}

@{thm[display] real_divide_divide2_eq[no_vars]}
\rulename{real_divide_divide2_eq}

@{thm[display] real_minus_divide_eq[no_vars]}
\rulename{real_minus_divide_eq}

@{thm[display] real_divide_minus_eq[no_vars]}
\rulename{real_divide_minus_eq}

This last NOT a simprule

@{thm[display] real_add_divide_distrib[no_vars]}
\rulename{real_add_divide_distrib}
*}

end
