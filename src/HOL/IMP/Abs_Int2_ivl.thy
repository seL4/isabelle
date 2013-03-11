(* Author: Tobias Nipkow *)

theory Abs_Int2_ivl
imports Abs_Int2
begin

subsection "Interval Analysis"

type_synonym eint = "int extended"
type_synonym eint2 = "eint * eint"

definition \<gamma>_rep :: "eint2 \<Rightarrow> int set" where
"\<gamma>_rep p = (let (l,h) = p in {i. l \<le> Fin i \<and> Fin i \<le> h})"

definition eq_ivl :: "eint2 \<Rightarrow> eint2 \<Rightarrow> bool" where
"eq_ivl p1 p2 = (\<gamma>_rep p1 = \<gamma>_rep p2)"

lemma refl_eq_ivl[simp]: "eq_ivl p p"
by(auto simp: eq_ivl_def)

quotient_type ivl = eint2 / eq_ivl
by(rule equivpI)(auto simp: reflp_def symp_def transp_def eq_ivl_def)

lift_definition \<gamma>_ivl :: "ivl \<Rightarrow> int set" is \<gamma>_rep
by(simp add: eq_ivl_def)

abbreviation ivl_abbr :: "eint \<Rightarrow> eint \<Rightarrow> ivl" ("[_\<dots>_]") where
"[l\<dots>h] == abs_ivl(l,h)"

lift_definition num_ivl :: "int \<Rightarrow> ivl" is "\<lambda>i. (Fin i, Fin i)"
by(auto simp: eq_ivl_def)

fun in_ivl_rep :: "int \<Rightarrow> eint2 \<Rightarrow> bool" where
"in_ivl_rep k (l,h) \<longleftrightarrow> l \<le> Fin k \<and> Fin k \<le> h"

lift_definition in_ivl :: "int \<Rightarrow> ivl \<Rightarrow> bool" is in_ivl_rep
by(auto simp: eq_ivl_def \<gamma>_rep_def)

definition is_empty_rep :: "eint2 \<Rightarrow> bool" where
"is_empty_rep p = (let (l,h) = p in l>h | l=Pinf & h=Pinf | l=Minf & h=Minf)"

lemma \<gamma>_rep_cases: "\<gamma>_rep p = (case p of (Fin i,Fin j) => {i..j} | (Fin i,Pinf) => {i..} |
  (Minf,Fin i) \<Rightarrow> {..i} | (Minf,Pinf) \<Rightarrow> UNIV | _ \<Rightarrow> {})"
by(auto simp add: \<gamma>_rep_def split: prod.splits extended.splits)

lift_definition  is_empty_ivl :: "ivl \<Rightarrow> bool" is is_empty_rep
apply(auto simp: eq_ivl_def \<gamma>_rep_cases is_empty_rep_def)
apply(auto simp: not_less less_eq_extended_cases split: extended.splits)
done

lemma eq_ivl_iff: "eq_ivl p1 p2 = (is_empty_rep p1 & is_empty_rep p2 | p1 = p2)"
by(auto simp: eq_ivl_def is_empty_rep_def \<gamma>_rep_cases Icc_eq_Icc split: prod.splits extended.splits)

definition empty_rep :: eint2 where "empty_rep = (Pinf,Minf)"

lift_definition empty_ivl :: ivl is empty_rep
by simp

lemma is_empty_empty_rep[simp]: "is_empty_rep empty_rep"
by(auto simp add: is_empty_rep_def empty_rep_def)

lemma is_empty_rep_iff: "is_empty_rep p = (\<gamma>_rep p = {})"
by(auto simp add: \<gamma>_rep_cases is_empty_rep_def split: prod.splits extended.splits)

declare is_empty_rep_iff[THEN iffD1, simp]


instantiation ivl :: semilattice
begin

definition le_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> bool" where
"le_rep p1 p2 = (let (l1,h1) = p1; (l2,h2) = p2 in
  if is_empty_rep(l1,h1) then True else
  if is_empty_rep(l2,h2) then False else l1 \<ge> l2 & h1 \<le> h2)"

lemma le_iff_subset: "le_rep p1 p2 \<longleftrightarrow> \<gamma>_rep p1 \<subseteq> \<gamma>_rep p2"
apply rule
apply(auto simp: is_empty_rep_def le_rep_def \<gamma>_rep_def split: if_splits prod.splits)[1]
apply(auto simp: is_empty_rep_def \<gamma>_rep_cases le_rep_def)
apply(auto simp: not_less split: extended.splits)
done

lift_definition less_eq_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> bool" is le_rep
by(auto simp: eq_ivl_def le_iff_subset)

definition less_ivl where "i1 < i2 = (i1 \<le> i2 \<and> \<not> i2 \<le> (i1::ivl))"

definition sup_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
"sup_rep p1 p2 = (if is_empty_rep p1 then p2 else if is_empty_rep p2 then p1
  else let (l1,h1) = p1; (l2,h2) = p2 in  (min l1 l2, max h1 h2))"

lift_definition sup_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is sup_rep
by(auto simp: eq_ivl_iff sup_rep_def)

lift_definition top_ivl :: ivl is "(Minf,Pinf)"
by(auto simp: eq_ivl_def)

lemma is_empty_min_max:
  "\<not> is_empty_rep (l1,h1) \<Longrightarrow> \<not> is_empty_rep (l2, h2) \<Longrightarrow> \<not> is_empty_rep (min l1 l2, max h1 h2)"
by(auto simp add: is_empty_rep_def max_def min_def split: if_splits)

instance
proof
  case goal1 show ?case by (rule less_ivl_def)
next
  case goal2 show ?case by transfer (simp add: le_rep_def split: prod.splits)
next
  case goal3 thus ?case by transfer (auto simp: le_rep_def split: if_splits)
next
  case goal4 thus ?case by transfer (auto simp: le_rep_def eq_ivl_iff split: if_splits)
next
  case goal5 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def is_empty_min_max)
next
  case goal6 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def is_empty_min_max)
next
  case goal7 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def)
next
  case goal8 show ?case by transfer (simp add: le_rep_def is_empty_rep_def)
qed

end

text{* Implement (naive) executable equality: *}
instantiation ivl :: equal
begin

definition equal_ivl where
"equal_ivl i1 (i2::ivl) = (i1\<le>i2 \<and> i2 \<le> i1)"

instance
proof
  case goal1 show ?case by(simp add: equal_ivl_def eq_iff)
qed

end

lemma [simp]: fixes x :: "'a::linorder extended" shows "(\<not> x < Pinf) = (x = Pinf)"
by(simp add: not_less)
lemma [simp]: fixes x :: "'a::linorder extended" shows "(\<not> Minf < x) = (x = Minf)"
by(simp add: not_less)

instantiation ivl :: lattice
begin

definition inf_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
"inf_rep p1 p2 = (let (l1,h1) = p1; (l2,h2) = p2 in (max l1 l2, min h1 h2))"

lemma \<gamma>_inf_rep: "\<gamma>_rep(inf_rep p1 p2) = \<gamma>_rep p1 \<inter> \<gamma>_rep p2"
by(auto simp:inf_rep_def \<gamma>_rep_cases split: prod.splits extended.splits)

lift_definition inf_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is inf_rep
by(auto simp: \<gamma>_inf_rep eq_ivl_def)

definition "\<bottom> = empty_ivl"

instance
proof
  case goal1 thus ?case
    unfolding inf_rep_def by transfer (auto simp: le_iff_subset \<gamma>_inf_rep)
next
  case goal2 thus ?case
    unfolding inf_rep_def by transfer (auto simp: le_iff_subset \<gamma>_inf_rep)
next
  case goal3 thus ?case
    unfolding inf_rep_def by transfer (auto simp: le_iff_subset \<gamma>_inf_rep)
next
  case goal4 show ?case unfolding bot_ivl_def by transfer (auto simp: le_iff_subset)
qed

end


lemma eq_ivl_empty: "eq_ivl p empty_rep = is_empty_rep p"
by (metis eq_ivl_iff is_empty_empty_rep)

lemma le_ivl_nice: "[l1\<dots>h1] \<le> [l2\<dots>h2] \<longleftrightarrow>
  (if [l1\<dots>h1] = \<bottom> then True else
   if [l2\<dots>h2] = \<bottom> then False else l1 \<ge> l2 & h1 \<le> h2)"
unfolding bot_ivl_def by transfer (simp add: le_rep_def eq_ivl_empty)

lemma sup_ivl_nice: "[l1\<dots>h1] \<squnion> [l2\<dots>h2] =
  (if [l1\<dots>h1] = \<bottom> then [l2\<dots>h2] else
   if [l2\<dots>h2] = \<bottom> then [l1\<dots>h1] else [min l1 l2\<dots>max h1 h2])"
unfolding bot_ivl_def by transfer (simp add: sup_rep_def eq_ivl_empty)

lemma inf_ivl_nice: "[l1\<dots>h1] \<sqinter> [l2\<dots>h2] = [max l1 l2\<dots>min h1 h2]"
by transfer (simp add: inf_rep_def)


instantiation ivl :: plus
begin

definition plus_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
"plus_rep p1 p2 =
  (if is_empty_rep p1 \<or> is_empty_rep p2 then empty_rep else
   let (l1,h1) = p1; (l2,h2) = p2 in (l1+l2, h1+h2))"

lift_definition plus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is plus_rep
by(auto simp: plus_rep_def eq_ivl_iff)

instance ..
end

lemma plus_ivl_nice: "[l1\<dots>h1] + [l2\<dots>h2] =
  (if [l1\<dots>h1] = \<bottom> \<or> [l2\<dots>h2] = \<bottom> then \<bottom> else [l1+l2 \<dots> h1+h2])"
unfolding bot_ivl_def by transfer (auto simp: plus_rep_def eq_ivl_empty)

lemma uminus_eq_Minf[simp]: "-x = Minf \<longleftrightarrow> x = Pinf"
by(cases x) auto
lemma uminus_eq_Pinf[simp]: "-x = Pinf \<longleftrightarrow> x = Minf"
by(cases x) auto

lemma uminus_le_Fin_iff: "- x \<le> Fin(-y) \<longleftrightarrow> Fin y \<le> (x::'a::ordered_ab_group_add extended)"
by(cases x) auto
lemma Fin_uminus_le_iff: "Fin(-y) \<le> -x \<longleftrightarrow> x \<le> ((Fin y)::'a::ordered_ab_group_add extended)"
by(cases x) auto

instantiation ivl :: uminus
begin

definition uminus_rep :: "eint2 \<Rightarrow> eint2" where
"uminus_rep p = (let (l,h) = p in (-h, -l))"

lemma \<gamma>_uminus_rep: "i : \<gamma>_rep p \<Longrightarrow> -i \<in> \<gamma>_rep(uminus_rep p)"
by(auto simp: uminus_rep_def \<gamma>_rep_def image_def uminus_le_Fin_iff Fin_uminus_le_iff
        split: prod.split)

lift_definition uminus_ivl :: "ivl \<Rightarrow> ivl" is uminus_rep
by (auto simp: uminus_rep_def eq_ivl_def \<gamma>_rep_cases)
   (auto simp: Icc_eq_Icc split: extended.splits)

instance ..
end

lemma uminus_nice: "-[l\<dots>h] = [-h\<dots>-l]"
by transfer (simp add: uminus_rep_def)

instantiation ivl :: minus
begin
definition minus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where "(iv1::ivl) - iv2 = iv1 + -iv2"
instance ..
end


definition filter_plus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl*ivl" where
"filter_plus_ivl iv iv1 iv2 = (iv1 \<sqinter> (iv - iv2), iv2 \<sqinter> (iv - iv1))"

definition filter_less_rep :: "bool \<Rightarrow> eint2 \<Rightarrow> eint2 \<Rightarrow> eint2 * eint2" where
"filter_less_rep res p1 p2 =
  (if is_empty_rep p1 \<or> is_empty_rep p2 then (empty_rep,empty_rep) else
   let (l1,h1) = p1; (l2,h2) = p2 in
   if res
   then ((l1, min h1 (h2 + Fin -1)), (max (l1 + Fin 1) l2, h2))
   else ((max l1 l2, h1), (l2, min h1 h2)))"

lift_definition filter_less_ivl :: "bool \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl * ivl" is filter_less_rep
by(auto simp: prod_pred_def filter_less_rep_def eq_ivl_iff)
declare filter_less_ivl.abs_eq[code] (* bug in lifting *)

lemma filter_less_ivl_nice: "filter_less_ivl b [l1\<dots>h1] [l2\<dots>h2] =
  (if [l1\<dots>h1] = \<bottom> \<or> [l2\<dots>h2] = \<bottom> then (\<bottom>,\<bottom>) else
   if b
   then ([l1 \<dots> min h1 (h2 + Fin -1)], [max (l1 + Fin 1) l2 \<dots> h2])
   else ([max l1 l2 \<dots> h1], [l2 \<dots> min h1 h2]))"
unfolding prod_rel_eq[symmetric] bot_ivl_def
by transfer (auto simp: filter_less_rep_def eq_ivl_empty)

lemma add_mono_le_Fin:
  "\<lbrakk>x1 \<le> Fin y1; x2 \<le> Fin y2\<rbrakk> \<Longrightarrow> x1 + x2 \<le> Fin (y1 + (y2::'a::ordered_ab_group_add))"
by(drule (1) add_mono) simp

lemma add_mono_Fin_le:
  "\<lbrakk>Fin y1 \<le> x1; Fin y2 \<le> x2\<rbrakk> \<Longrightarrow> Fin(y1 + y2::'a::ordered_ab_group_add) \<le> x1 + x2"
by(drule (1) add_mono) simp

lemma plus_rep_plus:
  "\<lbrakk> i1 \<in> \<gamma>_rep (l1,h1); i2 \<in> \<gamma>_rep (l2, h2)\<rbrakk> \<Longrightarrow> i1 + i2 \<in> \<gamma>_rep (l1 + l2, h1 + h2)"
by(simp add: \<gamma>_rep_def add_mono_Fin_le add_mono_le_Fin)

interpretation Val_abs
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
proof
  case goal1 thus ?case by transfer (simp add: le_iff_subset)
next
  case goal2 show ?case by transfer (simp add: \<gamma>_rep_def)
next
  case goal3 show ?case by transfer (simp add: \<gamma>_rep_def)
next
  case goal4 thus ?case
    apply transfer
    apply(auto simp: \<gamma>_rep_def plus_rep_def add_mono_le_Fin add_mono_Fin_le)
    by(auto simp: empty_rep_def is_empty_rep_def)
qed


interpretation Val_abs1_gamma
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
defines aval_ivl is aval'
proof
  case goal1 show ?case
    by transfer (auto simp add:inf_rep_def \<gamma>_rep_cases split: prod.split extended.split)
next
  case goal2 show ?case unfolding bot_ivl_def by transfer simp
qed

lemma \<gamma>_plus_rep: "i1 : \<gamma>_rep p1 \<Longrightarrow> i2 : \<gamma>_rep p2 \<Longrightarrow> i1+i2 \<in> \<gamma>_rep(plus_rep p1 p2)"
by(auto simp: plus_rep_def plus_rep_plus split: prod.splits)

lemma non_empty_inf: "\<lbrakk>n1 \<in> \<gamma>_rep a1; n2 \<in> \<gamma>_rep a2; n1 + n2 \<in> \<gamma>_rep a \<rbrakk> \<Longrightarrow>
     \<not> is_empty_rep (inf_rep a1 (plus_rep a (uminus_rep a2)))"
by (auto simp add: \<gamma>_inf_rep set_eq_iff is_empty_rep_iff simp del: all_not_in_conv)
   (metis \<gamma>_plus_rep \<gamma>_uminus_rep add_diff_cancel diff_minus)

lemma filter_plus: "\<lbrakk>eq_ivl (inf_rep a1 (plus_rep a (uminus_rep a2))) b1 \<and>
       eq_ivl (inf_rep a2 (plus_rep a (uminus_rep a1))) b2;
        n1 \<in> \<gamma>_rep a1; n2 \<in> \<gamma>_rep a2; n1 + n2 \<in> \<gamma>_rep a\<rbrakk>
       \<Longrightarrow> n1 \<in> \<gamma>_rep b1 \<and> n2 \<in> \<gamma>_rep b2"
by (auto simp: eq_ivl_iff \<gamma>_inf_rep non_empty_inf add_ac)
   (metis \<gamma>_plus_rep \<gamma>_uminus_rep add_diff_cancel diff_def add_commute)+

interpretation Val_abs1
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
proof
  case goal1 thus ?case by transfer (auto simp: \<gamma>_rep_def)
next
  case goal2 thus ?case unfolding filter_plus_ivl_def minus_ivl_def prod_rel_eq[symmetric]
    by transfer (simp add: filter_plus)
next
  case goal3 thus ?case
    unfolding prod_rel_eq[symmetric]
    apply transfer
    apply (auto simp add: filter_less_rep_def eq_ivl_iff max_def min_def split: if_splits)
    apply(auto simp: \<gamma>_rep_cases is_empty_rep_def split: extended.splits)
    done
qed

interpretation Abs_Int1
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
defines afilter_ivl is afilter
and bfilter_ivl is bfilter
and step_ivl is step'
and AI_ivl is AI
and aval_ivl' is aval''
..


text{* Monotonicity: *}

lemma mono_inf_rep: "le_rep p1 p2 \<Longrightarrow> le_rep q1 q2 \<Longrightarrow> le_rep (inf_rep p1 q1) (inf_rep p2 q2)"
by(auto simp add: le_iff_subset \<gamma>_inf_rep)

lemma mono_plus_rep: "le_rep p1 p2 \<Longrightarrow> le_rep q1 q2 \<Longrightarrow> le_rep (plus_rep p1 q1) (plus_rep p2 q2)"
apply(auto simp: plus_rep_def le_iff_subset split: if_splits)
by(auto simp: is_empty_rep_iff \<gamma>_rep_cases split: extended.splits)

lemma mono_minus_rep: "le_rep p1 p2 \<Longrightarrow> le_rep (uminus_rep p1) (uminus_rep p2)"
apply(auto simp: uminus_rep_def le_iff_subset split: if_splits prod.split)
by(auto simp: \<gamma>_rep_cases split: extended.splits)

interpretation Abs_Int1_mono
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
proof
  case goal1 thus ?case by transfer (rule mono_plus_rep)
next
  case goal2 thus ?case unfolding filter_plus_ivl_def minus_ivl_def less_eq_prod_def
    by transfer (auto simp: mono_inf_rep mono_plus_rep mono_minus_rep)
next
  case goal3 thus ?case unfolding less_eq_prod_def
    apply transfer
    apply(auto simp:filter_less_rep_def le_iff_subset min_def max_def split: if_splits)
    by(auto simp:is_empty_rep_iff \<gamma>_rep_cases split: extended.splits)
qed


subsubsection "Tests"

(* Hide Fin in numerals on output *)
declare
Fin_numeral [code_post] Fin_neg_numeral [code_post]
zero_extended_def[symmetric, code_post] one_extended_def[symmetric, code_post]

value "show_acom_opt (AI_ivl test1_ivl)"

text{* Better than @{text AI_const}: *}
value "show_acom_opt (AI_ivl test3_const)"
value "show_acom_opt (AI_ivl test4_const)"
value "show_acom_opt (AI_ivl test6_const)"

definition "steps c i = (step_ivl(Top(vars c)) ^^ i) (bot c)"

value "show_acom_opt (AI_ivl test2_ivl)"
value "show_acom (steps test2_ivl 0)"
value "show_acom (steps test2_ivl 1)"
value "show_acom (steps test2_ivl 2)"
value "show_acom (steps test2_ivl 3)"

text{* Fixed point reached in 2 steps.
 Not so if the start value of x is known: *}

value "show_acom_opt (AI_ivl test3_ivl)"
value "show_acom (steps test3_ivl 0)"
value "show_acom (steps test3_ivl 1)"
value "show_acom (steps test3_ivl 2)"
value "show_acom (steps test3_ivl 3)"
value "show_acom (steps test3_ivl 4)"
value "show_acom (steps test3_ivl 5)"

text{* Takes as many iterations as the actual execution. Would diverge if
loop did not terminate. Worse still, as the following example shows: even if
the actual execution terminates, the analysis may not. The value of y keeps
decreasing as the analysis is iterated, no matter how long: *}

value "show_acom (steps test4_ivl 50)"

text{* Relationships between variables are NOT captured: *}
value "show_acom_opt (AI_ivl test5_ivl)"

text{* Again, the analysis would not terminate: *}
value "show_acom (steps test6_ivl 50)"

end
