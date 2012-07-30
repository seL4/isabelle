theory Numbers
imports Complex_Main
begin

text{*

numeric literals; default simprules; can re-orient
*}

lemma "2 * m = m + m"
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
oops

fun h :: "nat \<Rightarrow> nat" where
"h i = (if i = 3 then 2 else i)"

text{*
@{term"h 3 = 2"}
@{term"h i  = i"}
*}

text{*
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

@{thm[display] div_le_mono[no_vars]}
\rulename{div_le_mono}

@{thm[display] diff_mult_distrib[no_vars]}
\rulename{diff_mult_distrib}

@{thm[display] mult_mod_left[no_vars]}
\rulename{mult_mod_left}

@{thm[display] nat_diff_split[no_vars]}
\rulename{nat_diff_split}
*}


lemma "(n - 1) * (n + 1) = n * n - (1::nat)"
apply (clarsimp split: nat_diff_split iff del: less_Suc0)
 --{* @{subgoals[display,indent=0,margin=65]} *}
apply (subgoal_tac "n=0", force, arith)
done


lemma "(n - 2) * (n + 2) = n * n - (4::nat)"
apply (simp split: nat_diff_split, clarify)
 --{* @{subgoals[display,indent=0,margin=65]} *}
apply (subgoal_tac "n=0 | n=1", force, arith)
done

text{*
@{thm[display] mod_if[no_vars]}
\rulename{mod_if}

@{thm[display] mod_div_equality[no_vars]}
\rulename{mod_div_equality}


@{thm[display] div_mult1_eq[no_vars]}
\rulename{div_mult1_eq}

@{thm[display] mod_mult_right_eq[no_vars]}
\rulename{mod_mult_right_eq}

@{thm[display] div_mult2_eq[no_vars]}
\rulename{div_mult2_eq}

@{thm[display] mod_mult2_eq[no_vars]}
\rulename{mod_mult2_eq}

@{thm[display] div_mult_mult1[no_vars]}
\rulename{div_mult_mult1}

@{thm[display] div_by_0 [no_vars]}
\rulename{div_by_0}

@{thm[display] mod_by_0 [no_vars]}
\rulename{mod_by_0}

@{thm[display] dvd_antisym[no_vars]}
\rulename{dvd_antisym}

@{thm[display] dvd_add[no_vars]}
\rulename{dvd_add}

For the integers, I'd list a few theorems that somehow involve negative 
numbers.*}


text{*
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

@{thm[display] mod_add_eq[no_vars]}
\rulename{mod_add_eq}

@{thm[display] zdiv_zmult1_eq[no_vars]}
\rulename{zdiv_zmult1_eq}

@{thm[display] mod_mult_right_eq[no_vars]}
\rulename{mod_mult_right_eq}

@{thm[display] zdiv_zmult2_eq[no_vars]}
\rulename{zdiv_zmult2_eq}

@{thm[display] zmod_zmult2_eq[no_vars]}
\rulename{zmod_zmult2_eq}
*}  

lemma "abs (x+y) \<le> abs x + abs (y :: int)"
by arith

lemma "abs (2*x) = 2 * abs (x :: int)"
by (simp add: abs_if) 


text {*Induction rules for the Integers

@{thm[display] int_ge_induct[no_vars]}
\rulename{int_ge_induct}

@{thm[display] int_gr_induct[no_vars]}
\rulename{int_gr_induct}

@{thm[display] int_le_induct[no_vars]}
\rulename{int_le_induct}

@{thm[display] int_less_induct[no_vars]}
\rulename{int_less_induct}
*}  

text {*FIELDS

@{thm[display] dense[no_vars]}
\rulename{dense}

@{thm[display] times_divide_eq_right[no_vars]}
\rulename{times_divide_eq_right}

@{thm[display] times_divide_eq_left[no_vars]}
\rulename{times_divide_eq_left}

@{thm[display] divide_divide_eq_right[no_vars]}
\rulename{divide_divide_eq_right}

@{thm[display] divide_divide_eq_left[no_vars]}
\rulename{divide_divide_eq_left}

@{thm[display] minus_divide_left[no_vars]}
\rulename{minus_divide_left}

@{thm[display] minus_divide_right[no_vars]}
\rulename{minus_divide_right}

This last NOT a simprule

@{thm[display] add_divide_distrib[no_vars]}
\rulename{add_divide_distrib}
*}

lemma "3/4 < (7/8 :: real)"
by simp 

lemma "P ((3/4) * (8/15 :: real))"
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply simp 
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
oops

lemma "(3/4) * (8/15) < (x :: real)"
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply simp 
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
oops

text{*
Ring and Field

Requires a field, or else an ordered ring

@{thm[display] mult_eq_0_iff[no_vars]}
\rulename{mult_eq_0_iff}

@{thm[display] mult_cancel_right[no_vars]}
\rulename{mult_cancel_right}

@{thm[display] mult_cancel_left[no_vars]}
\rulename{mult_cancel_left}
*}

text{*
effect of show sorts on the above

@{thm[display,show_sorts] mult_cancel_left[no_vars]}
\rulename{mult_cancel_left}
*}

text{*
absolute value

@{thm[display] abs_mult[no_vars]}
\rulename{abs_mult}

@{thm[display] abs_le_iff[no_vars]}
\rulename{abs_le_iff}

@{thm[display] abs_triangle_ineq[no_vars]}
\rulename{abs_triangle_ineq}

@{thm[display] power_add[no_vars]}
\rulename{power_add}

@{thm[display] power_mult[no_vars]}
\rulename{power_mult}

@{thm[display] power_abs[no_vars]}
\rulename{power_abs}


*}


end
