(* Author: Tobias Nipkow *)

subsection "Interval Analysis"

theory Abs_Int2_ivl
imports Abs_Int2
begin

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

abbreviation ivl_abbr :: "eint \<Rightarrow> eint \<Rightarrow> ivl" (\<open>[_, _]\<close>) where
"[l,h] == abs_ivl(l,h)"

lift_definition \<gamma>_ivl :: "ivl \<Rightarrow> int set" is \<gamma>_rep
by(simp add: eq_ivl_def)

lemma \<gamma>_ivl_nice: "\<gamma>_ivl[l,h] = {i. l \<le> Fin i \<and> Fin i \<le> h}"
by transfer (simp add: \<gamma>_rep_def)

lift_definition num_ivl :: "int \<Rightarrow> ivl" is "\<lambda>i. (Fin i, Fin i)" .

lift_definition in_ivl :: "int \<Rightarrow> ivl \<Rightarrow> bool"
  is "\<lambda>i (l,h). l \<le> Fin i \<and> Fin i \<le> h"
by(auto simp: eq_ivl_def \<gamma>_rep_def)

lemma in_ivl_nice: "in_ivl i [l,h] = (l \<le> Fin i \<and> Fin i \<le> h)"
by transfer simp

definition is_empty_rep :: "eint2 \<Rightarrow> bool" where
"is_empty_rep p = (let (l,h) = p in l>h | l=Pinf & h=Pinf | l=Minf & h=Minf)"

lemma \<gamma>_rep_cases: "\<gamma>_rep p = (case p of (Fin i,Fin j) => {i..j} | (Fin i,Pinf) => {i..} |
  (Minf,Fin i) \<Rightarrow> {..i} | (Minf,Pinf) \<Rightarrow> UNIV | _ \<Rightarrow> {})"
by(auto simp add: \<gamma>_rep_def split: prod.splits extended.splits)

lift_definition  is_empty_ivl :: "ivl \<Rightarrow> bool" is is_empty_rep
apply(auto simp: eq_ivl_def \<gamma>_rep_cases is_empty_rep_def)
apply(auto simp: not_less less_eq_extended_case split: extended.splits)
done

lemma eq_ivl_iff: "eq_ivl p1 p2 = (is_empty_rep p1 & is_empty_rep p2 | p1 = p2)"
by(auto simp: eq_ivl_def is_empty_rep_def \<gamma>_rep_cases Icc_eq_Icc split: prod.splits extended.splits)

definition empty_rep :: eint2 where "empty_rep = (Pinf,Minf)"

lift_definition empty_ivl :: ivl is empty_rep .

lemma is_empty_empty_rep[simp]: "is_empty_rep empty_rep"
by(auto simp add: is_empty_rep_def empty_rep_def)

lemma is_empty_rep_iff: "is_empty_rep p = (\<gamma>_rep p = {})"
by(auto simp add: \<gamma>_rep_cases is_empty_rep_def split: prod.splits extended.splits)

declare is_empty_rep_iff[THEN iffD1, simp]


instantiation ivl :: semilattice_sup_top
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

lemma le_ivl_iff_subset: "iv1 \<le> iv2 \<longleftrightarrow> \<gamma>_ivl iv1 \<subseteq> \<gamma>_ivl iv2"
by transfer (rule le_iff_subset)

definition sup_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
"sup_rep p1 p2 = (if is_empty_rep p1 then p2 else if is_empty_rep p2 then p1
  else let (l1,h1) = p1; (l2,h2) = p2 in  (min l1 l2, max h1 h2))"

lift_definition sup_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is sup_rep
by(auto simp: eq_ivl_iff sup_rep_def)

lift_definition top_ivl :: ivl is "(Minf,Pinf)" .

lemma is_empty_min_max:
  "\<not> is_empty_rep (l1,h1) \<Longrightarrow> \<not> is_empty_rep (l2, h2) \<Longrightarrow> \<not> is_empty_rep (min l1 l2, max h1 h2)"
by(auto simp add: is_empty_rep_def max_def min_def split: if_splits)

instance
proof (standard, goal_cases)
  case 1 show ?case by (rule less_ivl_def)
next
  case 2 show ?case by transfer (simp add: le_rep_def split: prod.splits)
next
  case 3 thus ?case by transfer (auto simp: le_rep_def split: if_splits)
next
  case 4 thus ?case by transfer (auto simp: le_rep_def eq_ivl_iff split: if_splits)
next
  case 5 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def is_empty_min_max)
next
  case 6 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def is_empty_min_max)
next
  case 7 thus ?case by transfer (auto simp add: le_rep_def sup_rep_def)
next
  case 8 show ?case by transfer (simp add: le_rep_def is_empty_rep_def)
qed

end

text\<open>Implement (naive) executable equality:\<close>
instantiation ivl :: equal
begin

definition equal_ivl where
"equal_ivl i1 (i2::ivl) = (i1\<le>i2 \<and> i2 \<le> i1)"

instance
proof (standard, goal_cases)
  case 1 show ?case by(simp add: equal_ivl_def eq_iff)
qed

end

lemma [simp]: fixes x :: "'a::linorder extended" shows "(\<not> x < Pinf) = (x = Pinf)"
by(simp add: not_less)
lemma [simp]: fixes x :: "'a::linorder extended" shows "(\<not> Minf < x) = (x = Minf)"
by(simp add: not_less)

instantiation ivl :: bounded_lattice
begin

definition inf_rep :: "eint2 \<Rightarrow> eint2 \<Rightarrow> eint2" where
"inf_rep p1 p2 = (let (l1,h1) = p1; (l2,h2) = p2 in (max l1 l2, min h1 h2))"

lemma \<gamma>_inf_rep: "\<gamma>_rep(inf_rep p1 p2) = \<gamma>_rep p1 \<inter> \<gamma>_rep p2"
by(auto simp:inf_rep_def \<gamma>_rep_cases split: prod.splits extended.splits)

lift_definition inf_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" is inf_rep
by(auto simp: \<gamma>_inf_rep eq_ivl_def)

lemma \<gamma>_inf: "\<gamma>_ivl (iv1 \<sqinter> iv2) = \<gamma>_ivl iv1 \<inter> \<gamma>_ivl iv2"
by transfer (rule \<gamma>_inf_rep)

definition "\<bottom> = empty_ivl"

instance
proof (standard, goal_cases)
  case 1 thus ?case by (simp add: \<gamma>_inf le_ivl_iff_subset)
next
  case 2 thus ?case by (simp add: \<gamma>_inf le_ivl_iff_subset)
next
  case 3 thus ?case by (simp add: \<gamma>_inf le_ivl_iff_subset)
next
  case 4 show ?case
    unfolding bot_ivl_def by transfer (auto simp: le_iff_subset)
qed

end


lemma eq_ivl_empty: "eq_ivl p empty_rep = is_empty_rep p"
by (metis eq_ivl_iff is_empty_empty_rep)

lemma le_ivl_nice: "[l1,h1] \<le> [l2,h2] \<longleftrightarrow>
  (if [l1,h1] = \<bottom> then True else
   if [l2,h2] = \<bottom> then False else l1 \<ge> l2 & h1 \<le> h2)"
unfolding bot_ivl_def by transfer (simp add: le_rep_def eq_ivl_empty)

lemma sup_ivl_nice: "[l1,h1] \<squnion> [l2,h2] =
  (if [l1,h1] = \<bottom> then [l2,h2] else
   if [l2,h2] = \<bottom> then [l1,h1] else [min l1 l2,max h1 h2])"
unfolding bot_ivl_def by transfer (simp add: sup_rep_def eq_ivl_empty)

lemma inf_ivl_nice: "[l1,h1] \<sqinter> [l2,h2] = [max l1 l2,min h1 h2]"
by transfer (simp add: inf_rep_def)

lemma top_ivl_nice: "\<top> = [-\<infinity>,\<infinity>]"
by (simp add: top_ivl_def)


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

lemma plus_ivl_nice: "[l1,h1] + [l2,h2] =
  (if [l1,h1] = \<bottom> \<or> [l2,h2] = \<bottom> then \<bottom> else [l1+l2 , h1+h2])"
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

lemma \<gamma>_uminus_rep: "i \<in> \<gamma>_rep p \<Longrightarrow> -i \<in> \<gamma>_rep(uminus_rep p)"
by(auto simp: uminus_rep_def \<gamma>_rep_def image_def uminus_le_Fin_iff Fin_uminus_le_iff
        split: prod.split)

lift_definition uminus_ivl :: "ivl \<Rightarrow> ivl" is uminus_rep
by (auto simp: uminus_rep_def eq_ivl_def \<gamma>_rep_cases)
   (auto simp: Icc_eq_Icc split: extended.splits)

instance ..
end

lemma \<gamma>_uminus: "i \<in> \<gamma>_ivl iv \<Longrightarrow> -i \<in> \<gamma>_ivl(- iv)"
by transfer (rule \<gamma>_uminus_rep)

lemma uminus_nice: "-[l,h] = [-h,-l]"
by transfer (simp add: uminus_rep_def)

instantiation ivl :: minus
begin

definition minus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
"(iv1::ivl) - iv2 = iv1 + -iv2"

instance ..
end


definition inv_plus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl*ivl" where
"inv_plus_ivl iv iv1 iv2 = (iv1 \<sqinter> (iv - iv2), iv2 \<sqinter> (iv - iv1))"

definition above_rep :: "eint2 \<Rightarrow> eint2" where
"above_rep p = (if is_empty_rep p then empty_rep else let (l,h) = p in (l,\<infinity>))"

definition below_rep :: "eint2 \<Rightarrow> eint2" where
"below_rep p = (if is_empty_rep p then empty_rep else let (l,h) = p in (-\<infinity>,h))"

lift_definition above :: "ivl \<Rightarrow> ivl" is above_rep
by(auto simp: above_rep_def eq_ivl_iff)

lift_definition below :: "ivl \<Rightarrow> ivl" is below_rep
by(auto simp: below_rep_def eq_ivl_iff)

lemma \<gamma>_aboveI: "i \<in> \<gamma>_ivl iv \<Longrightarrow> i \<le> j \<Longrightarrow> j \<in> \<gamma>_ivl(above iv)"
by transfer 
   (auto simp add: above_rep_def \<gamma>_rep_cases is_empty_rep_def
         split: extended.splits)

lemma \<gamma>_belowI: "i \<in> \<gamma>_ivl iv \<Longrightarrow> j \<le> i \<Longrightarrow> j \<in> \<gamma>_ivl(below iv)"
by transfer 
   (auto simp add: below_rep_def \<gamma>_rep_cases is_empty_rep_def
         split: extended.splits)

definition inv_less_ivl :: "bool \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl * ivl" where
"inv_less_ivl res iv1 iv2 =
  (if res
   then (iv1 \<sqinter> (below iv2 - [1,1]),
         iv2 \<sqinter> (above iv1 + [1,1]))
   else (iv1 \<sqinter> above iv2, iv2 \<sqinter> below iv1))"

lemma above_nice: "above[l,h] = (if [l,h] = \<bottom> then \<bottom> else [l,\<infinity>])"
unfolding bot_ivl_def by transfer (simp add: above_rep_def eq_ivl_empty)

lemma below_nice: "below[l,h] = (if [l,h] = \<bottom> then \<bottom> else [-\<infinity>,h])"
unfolding bot_ivl_def by transfer (simp add: below_rep_def eq_ivl_empty)

lemma add_mono_le_Fin:
  "\<lbrakk>x1 \<le> Fin y1; x2 \<le> Fin y2\<rbrakk> \<Longrightarrow> x1 + x2 \<le> Fin (y1 + (y2::'a::ordered_ab_group_add))"
by(drule (1) add_mono) simp

lemma add_mono_Fin_le:
  "\<lbrakk>Fin y1 \<le> x1; Fin y2 \<le> x2\<rbrakk> \<Longrightarrow> Fin(y1 + y2::'a::ordered_ab_group_add) \<le> x1 + x2"
by(drule (1) add_mono) simp

global_interpretation Val_semilattice
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "(+)"
proof (standard, goal_cases)
  case 1 thus ?case by transfer (simp add: le_iff_subset)
next
  case 2 show ?case by transfer (simp add: \<gamma>_rep_def)
next
  case 3 show ?case by transfer (simp add: \<gamma>_rep_def)
next
  case 4 thus ?case
    apply transfer
    apply(auto simp: \<gamma>_rep_def plus_rep_def add_mono_le_Fin add_mono_Fin_le)
    by(auto simp: empty_rep_def is_empty_rep_def)
qed


global_interpretation Val_lattice_gamma
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "(+)"
defines aval_ivl = aval'
proof (standard, goal_cases)
  case 1 show ?case by(simp add: \<gamma>_inf)
next
  case 2 show ?case unfolding bot_ivl_def by transfer simp
qed

global_interpretation Val_inv
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "(+)"
and test_num' = in_ivl
and inv_plus' = inv_plus_ivl and inv_less' = inv_less_ivl
proof (standard, goal_cases)
  case 1 thus ?case by transfer (auto simp: \<gamma>_rep_def)
next
  case (2 _ _ _ _ _ i1 i2) thus ?case
    unfolding inv_plus_ivl_def minus_ivl_def
    apply(clarsimp simp add: \<gamma>_inf)
    using gamma_plus'[of "i1+i2" _ "-i1"] gamma_plus'[of "i1+i2" _ "-i2"]
    by(simp add:  \<gamma>_uminus)
next
  case (3 i1 i2) thus ?case
    unfolding inv_less_ivl_def minus_ivl_def one_extended_def
    apply(clarsimp simp add: \<gamma>_inf split: if_splits)
    using gamma_plus'[of "i1+1" _ "-1"] gamma_plus'[of "i2 - 1" _ "1"]
    apply(simp add: \<gamma>_belowI[of i2] \<gamma>_aboveI[of i1]
      uminus_ivl.abs_eq uminus_rep_def \<gamma>_ivl_nice)
    apply(simp add: \<gamma>_aboveI[of i2] \<gamma>_belowI[of i1])
    done
qed

global_interpretation Abs_Int_inv
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "(+)"
and test_num' = in_ivl
and inv_plus' = inv_plus_ivl and inv_less' = inv_less_ivl
defines inv_aval_ivl = inv_aval'
and inv_bval_ivl = inv_bval'
and step_ivl = step'
and AI_ivl = AI
and aval_ivl' = aval''
..


text\<open>Monotonicity:\<close>

lemma mono_plus_ivl: "iv1 \<le> iv2 \<Longrightarrow> iv3 \<le> iv4 \<Longrightarrow> iv1+iv3 \<le> iv2+(iv4::ivl)"
apply transfer
apply(auto simp: plus_rep_def le_iff_subset split: if_splits)
by(auto simp: is_empty_rep_iff \<gamma>_rep_cases split: extended.splits)

lemma mono_minus_ivl: "iv1 \<le> iv2 \<Longrightarrow> -iv1 \<le> -(iv2::ivl)"
apply transfer
apply(auto simp: uminus_rep_def le_iff_subset split: if_splits prod.split)
by(auto simp: \<gamma>_rep_cases split: extended.splits)

lemma mono_above: "iv1 \<le> iv2 \<Longrightarrow> above iv1 \<le> above iv2"
apply transfer
apply(auto simp: above_rep_def le_iff_subset split: if_splits prod.split)
by(auto simp: is_empty_rep_iff \<gamma>_rep_cases split: extended.splits)

lemma mono_below: "iv1 \<le> iv2 \<Longrightarrow> below iv1 \<le> below iv2"
apply transfer
apply(auto simp: below_rep_def le_iff_subset split: if_splits prod.split)
by(auto simp: is_empty_rep_iff \<gamma>_rep_cases split: extended.splits)

global_interpretation Abs_Int_inv_mono
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "(+)"
and test_num' = in_ivl
and inv_plus' = inv_plus_ivl and inv_less' = inv_less_ivl
proof (standard, goal_cases)
  case 1 thus ?case by (rule mono_plus_ivl)
next
  case 2 thus ?case
    unfolding inv_plus_ivl_def minus_ivl_def less_eq_prod_def
    by (auto simp: le_infI1 le_infI2 mono_plus_ivl mono_minus_ivl)
next
  case 3 thus ?case
    unfolding less_eq_prod_def inv_less_ivl_def minus_ivl_def
    by (auto simp: le_infI1 le_infI2 mono_plus_ivl mono_above mono_below)
qed


subsubsection "Tests"

value "show_acom_opt (AI_ivl test1_ivl)"

text\<open>Better than \<open>AI_const\<close>:\<close>
value "show_acom_opt (AI_ivl test3_const)"
value "show_acom_opt (AI_ivl test4_const)"
value "show_acom_opt (AI_ivl test6_const)"

definition "steps c i = (step_ivl \<top> ^^ i) (bot c)"

value "show_acom_opt (AI_ivl test2_ivl)"
value "show_acom (steps test2_ivl 0)"
value "show_acom (steps test2_ivl 1)"
value "show_acom (steps test2_ivl 2)"
value "show_acom (steps test2_ivl 3)"

text\<open>Fixed point reached in 2 steps.
 Not so if the start value of x is known:\<close>

value "show_acom_opt (AI_ivl test3_ivl)"
value "show_acom (steps test3_ivl 0)"
value "show_acom (steps test3_ivl 1)"
value "show_acom (steps test3_ivl 2)"
value "show_acom (steps test3_ivl 3)"
value "show_acom (steps test3_ivl 4)"
value "show_acom (steps test3_ivl 5)"

text\<open>Takes as many iterations as the actual execution. Would diverge if
loop did not terminate. Worse still, as the following example shows: even if
the actual execution terminates, the analysis may not. The value of y keeps
increasing as the analysis is iterated, no matter how long:\<close>

value "show_acom (steps test4_ivl 50)"

text\<open>Relationships between variables are NOT captured:\<close>
value "show_acom_opt (AI_ivl test5_ivl)"

text\<open>Again, the analysis would not terminate:\<close>
value "show_acom (steps test6_ivl 50)"

end
