(* Author: Tobias Nipkow *)

theory Abs_Int2_ivl
imports Abs_Int2
begin

subsection "Interval Analysis"

datatype lb = Minf | Lb int
datatype ub = Pinf | Ub int

datatype ivl = Ivl lb ub

definition "\<gamma>_ivl i = (case i of
  Ivl (Lb l) (Ub h) \<Rightarrow> {l..h} |
  Ivl (Lb l) Pinf \<Rightarrow> {l..} |
  Ivl Minf (Ub h) \<Rightarrow> {..h} |
  Ivl Minf Pinf \<Rightarrow> UNIV)"

abbreviation Ivl_Lb_Ub :: "int \<Rightarrow> int \<Rightarrow> ivl"  ("{_\<dots>_}") where
"{lo\<dots>hi} == Ivl (Lb lo) (Ub hi)"
abbreviation Ivl_Lb_Pinf :: "int \<Rightarrow> ivl"  ("{_\<dots>}") where
"{lo\<dots>} == Ivl (Lb lo) Pinf"
abbreviation Ivl_Minf_Ub :: "int \<Rightarrow> ivl"  ("{\<dots>_}") where
"{\<dots>hi} == Ivl Minf (Ub hi)"
abbreviation Ivl_Minf_Pinf :: "ivl"  ("{\<dots>}") where
"{\<dots>} == Ivl Minf Pinf"

lemmas lub_splits = lb.splits ub.splits

definition "num_ivl n = {n\<dots>n}"

fun in_ivl :: "int \<Rightarrow> ivl \<Rightarrow> bool" where
"in_ivl k (Ivl (Lb l) (Ub h)) \<longleftrightarrow> l \<le> k \<and> k \<le> h" |
"in_ivl k (Ivl (Lb l) Pinf) \<longleftrightarrow> l \<le> k" |
"in_ivl k (Ivl Minf (Ub h)) \<longleftrightarrow> k \<le> h" |
"in_ivl k (Ivl Minf Pinf) \<longleftrightarrow> True"


instantiation lb :: linorder
begin

definition less_eq_lb where
"l1 \<le> l2 = (case l1 of Minf \<Rightarrow> True | Lb i1 \<Rightarrow> (case l2 of Minf \<Rightarrow> False | Lb i2 \<Rightarrow> i1 \<le> i2))"

definition less_lb :: "lb \<Rightarrow> lb \<Rightarrow> bool" where
"((l1::lb) < l2) = (l1 \<le> l2 & ~ l1 \<ge> l2)"

instance
proof
  case goal1 show ?case by(rule less_lb_def)
next
  case goal2 show ?case by(auto simp: less_eq_lb_def split:lub_splits)
next
  case goal3 thus ?case by(auto simp: less_eq_lb_def split:lub_splits)
next
  case goal4 thus ?case by(auto simp: less_eq_lb_def split:lub_splits)
next
  case goal5 thus ?case by(auto simp: less_eq_lb_def split:lub_splits)
qed

end

instantiation ub :: linorder
begin

definition less_eq_ub where
"u1 \<le> u2 = (case u2 of Pinf \<Rightarrow> True | Ub i2 \<Rightarrow> (case u1 of Pinf \<Rightarrow> False | Ub i1 \<Rightarrow> i1 \<le> i2))"

definition less_ub :: "ub \<Rightarrow> ub \<Rightarrow> bool" where
"((u1::ub) < u2) = (u1 \<le> u2 & ~ u1 \<ge> u2)"

instance
proof
  case goal1 show ?case by(rule less_ub_def)
next
  case goal2 show ?case by(auto simp: less_eq_ub_def split:lub_splits)
next
  case goal3 thus ?case by(auto simp: less_eq_ub_def split:lub_splits)
next
  case goal4 thus ?case by(auto simp: less_eq_ub_def split:lub_splits)
next
  case goal5 thus ?case by(auto simp: less_eq_ub_def split:lub_splits)
qed

end

lemmas le_lub_defs = less_eq_lb_def less_eq_ub_def

lemma le_lub_simps[simp]:
  "Minf \<le> l" "Lb i \<le> Lb j = (i \<le> j)" "~ Lb i \<le> Minf"
  "h \<le> Pinf" "Ub i \<le> Ub j = (i \<le> j)" "~ Pinf \<le> Ub j"
by(auto simp: le_lub_defs split: lub_splits)

definition empty where "empty = {1\<dots>0}"

fun is_empty where
"is_empty {l\<dots>h} = (h<l)" |
"is_empty _ = False"

lemma [simp]: "is_empty(Ivl l h) =
  (case l of Lb l \<Rightarrow> (case h of Ub h \<Rightarrow> h<l | Pinf \<Rightarrow> False) | Minf \<Rightarrow> False)"
by(auto split: lub_splits)

lemma [simp]: "is_empty i \<Longrightarrow> \<gamma>_ivl i = {}"
by(auto simp add: \<gamma>_ivl_def split: ivl.split lub_splits)


instantiation ivl :: semilattice
begin

fun le_aux where
"le_aux (Ivl l1 h1) (Ivl l2 h2) = (l2 \<le> l1 & h1 \<le> h2)"

definition le_ivl where
"i1 \<sqsubseteq> i2 =
 (if is_empty i1 then True else
  if is_empty i2 then False else le_aux i1 i2)"

definition "i1 \<squnion> i2 =
 (if is_empty i1 then i2 else if is_empty i2 then i1
  else case (i1,i2) of (Ivl l1 h1, Ivl l2 h2) \<Rightarrow> Ivl (min l1 l2) (max h1 h2))"

definition "\<top> = {\<dots>}"

instance
proof
  case goal1 thus ?case
    by(cases x, simp add: le_ivl_def)
next
  case goal2 thus ?case
    by(cases x, cases y, cases z, auto simp: le_ivl_def split: if_splits)
next
  case goal3 thus ?case
    by(cases x, cases y, simp add: le_ivl_def join_ivl_def le_lub_defs min_def max_def split: lub_splits)
next
  case goal4 thus ?case
    by(cases x, cases y, simp add: le_ivl_def join_ivl_def le_lub_defs min_def max_def split: lub_splits)
next
  case goal5 thus ?case
    by(cases x, cases y, cases z, auto simp add: le_ivl_def join_ivl_def le_lub_defs min_def max_def split: lub_splits if_splits)
next
  case goal6 thus ?case
    by(cases x, simp add: Top_ivl_def le_ivl_def le_lub_defs split: lub_splits)
qed

end


instantiation ivl :: lattice
begin

definition "i1 \<sqinter> i2 = (if is_empty i1 \<or> is_empty i2 then empty else
  case (i1,i2) of (Ivl l1 h1, Ivl l2 h2) \<Rightarrow> Ivl (max l1 l2) (min h1 h2))"

definition "\<bottom> = empty"

instance
proof
  case goal2 thus ?case
    by (simp add:meet_ivl_def empty_def le_ivl_def le_lub_defs max_def min_def split: ivl.splits lub_splits)
next
  case goal3 thus ?case
    by (simp add: empty_def meet_ivl_def le_ivl_def le_lub_defs max_def min_def split: ivl.splits lub_splits)
next
  case goal4 thus ?case
    by (cases x, cases y, cases z, auto simp add: le_ivl_def meet_ivl_def empty_def le_lub_defs max_def min_def split: lub_splits if_splits)
next
  case goal1 show ?case by(cases x, simp add: bot_ivl_def empty_def le_ivl_def)
qed

end


instantiation lb :: plus
begin

fun plus_lb where
"Lb x + Lb y = Lb(x+y)" |
"_ + _ = Minf"

instance ..
end

instantiation ub :: plus
begin

fun plus_ub where
"Ub x + Ub y = Ub(x+y)" |
"_ + _ = Pinf"

instance ..
end

instantiation ivl :: plus
begin

definition "i1+i2 = (if is_empty i1 | is_empty i2 then empty else
  case (i1,i2) of (Ivl l1 h1, Ivl l2 h2) \<Rightarrow> Ivl (l1+l2) (h1+h2))"

instance ..
end

fun uminus_ub :: "ub \<Rightarrow> lb" where
"uminus_ub(Ub( x)) = Lb(-x)" |
"uminus_ub Pinf = Minf"

fun uminus_lb :: "lb \<Rightarrow> ub" where
"uminus_lb(Lb( x)) = Ub(-x)" |
"uminus_lb Minf = Pinf"

instantiation ivl :: uminus
begin

fun uminus_ivl where
"-(Ivl l h) = Ivl (uminus_ub h) (uminus_lb l)"

instance ..
end

instantiation ivl :: minus
begin

definition minus_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
"(i1::ivl) - i2 = i1 + -i2"

instance ..
end

lemma minus_ivl_cases: "i1 - i2 = (if is_empty i1 | is_empty i2 then empty else
  case (i1,i2) of (Ivl l1 h1, Ivl l2 h2) \<Rightarrow> Ivl (l1 + uminus_ub h2) (h1 + uminus_lb l2))"
by(auto simp: plus_ivl_def minus_ivl_def split: ivl.split lub_splits)

lemma gamma_minus_ivl:
  "n1 : \<gamma>_ivl i1 \<Longrightarrow> n2 : \<gamma>_ivl i2 \<Longrightarrow> n1-n2 : \<gamma>_ivl(i1 - i2)"
by(auto simp add: minus_ivl_def plus_ivl_def \<gamma>_ivl_def split: ivl.splits lub_splits)

definition "filter_plus_ivl i i1 i2 = ((*if is_empty i then empty else*)
  i1 \<sqinter> (i - i2), i2 \<sqinter> (i - i1))"

fun filter_less_ivl :: "bool \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl * ivl" where
"filter_less_ivl res (Ivl l1 h1) (Ivl l2 h2) =
  (if is_empty(Ivl l1 h1) \<or> is_empty(Ivl l2 h2) then (empty, empty) else
   if res
   then (Ivl l1 (min h1 (h2 + Ub -1)), Ivl (max (l1 + Lb 1) l2) h2)
   else (Ivl (max l1 l2) h1, Ivl l2 (min h1 h2)))"

interpretation Val_abs
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
proof
  case goal1 thus ?case
    by(auto simp: \<gamma>_ivl_def le_ivl_def le_lub_defs split: ivl.split lub_splits if_splits)
next
  case goal2 show ?case by(simp add: \<gamma>_ivl_def Top_ivl_def)
next
  case goal3 thus ?case by(simp add: \<gamma>_ivl_def num_ivl_def)
next
  case goal4 thus ?case
    by(auto simp add: \<gamma>_ivl_def plus_ivl_def split: ivl.split lub_splits)
qed

interpretation Val_abs1_gamma
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
defines aval_ivl is aval'
proof
  case goal1 thus ?case
    by(auto simp add: \<gamma>_ivl_def meet_ivl_def empty_def min_def max_def split: ivl.split lub_splits)
next
  case goal2 show ?case by(auto simp add: bot_ivl_def \<gamma>_ivl_def empty_def)
qed

lemma mono_minus_ivl: fixes i1 :: ivl
shows "i1 \<sqsubseteq> i1' \<Longrightarrow> i2 \<sqsubseteq> i2' \<Longrightarrow> i1 - i2 \<sqsubseteq> i1' - i2'"
apply(auto simp add: minus_ivl_cases empty_def le_ivl_def le_lub_defs split: ivl.splits)
  apply(simp split: lub_splits)
 apply(simp split: lub_splits)
apply(simp split: lub_splits)
done


interpretation Val_abs1
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
proof
  case goal1 thus ?case
    by (simp add: \<gamma>_ivl_def split: ivl.split lub_splits)
next
  case goal2 thus ?case
    by(auto simp add: filter_plus_ivl_def)
      (metis gamma_minus_ivl add_diff_cancel add_commute)+
next
  case goal3 thus ?case
    by(cases a1, cases a2, auto simp: \<gamma>_ivl_def min_def max_def split: if_splits lub_splits)
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

interpretation Abs_Int1_mono
where \<gamma> = \<gamma>_ivl and num' = num_ivl and plus' = "op +"
and test_num' = in_ivl
and filter_plus' = filter_plus_ivl and filter_less' = filter_less_ivl
proof
  case goal1 thus ?case
    by(auto simp: plus_ivl_def le_ivl_def le_lub_defs empty_def split: if_splits ivl.splits lub_splits)
next
  case goal2 thus ?case
    by(auto simp: filter_plus_ivl_def le_prod_def mono_meet mono_minus_ivl)
next
  case goal3 thus ?case
    apply(cases a1, cases b1, cases a2, cases b2, auto simp: le_prod_def)
    by(auto simp add: empty_def le_ivl_def le_lub_defs min_def max_def split: lub_splits)
qed


subsubsection "Tests"

value "show_acom_opt (AI_ivl test1_ivl)"

text{* Better than @{text AI_const}: *}
value "show_acom_opt (AI_ivl test3_const)"
value "show_acom_opt (AI_ivl test4_const)"
value "show_acom_opt (AI_ivl test6_const)"

definition "steps c i = (step_ivl(top(vars c)) ^^ i) (bot c)"

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
