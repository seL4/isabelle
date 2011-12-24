(* Author: Tobias Nipkow *)

theory Abs_Int_den1_ivl
imports Abs_Int_den1 "~~/src/HOL/Library/More_Set"
begin

subsection "Interval Analysis"

datatype ivl = I "int option" "int option"

text{* We assume an important invariant: arithmetic operations are never
applied to empty intervals @{term"I (Some i) (Some j)"} with @{term"j <
i"}. This avoids special cases. Why can we assume this? Because an empty
interval of values for a variable means that the current program point is
unreachable. But this should actually translate into the bottom state, not a
state where some variables have empty intervals. *}

definition "rep_ivl i =
 (case i of I (Some l) (Some h) \<Rightarrow> {l..h} | I (Some l) None \<Rightarrow> {l..}
  | I None (Some h) \<Rightarrow> {..h} | I None None \<Rightarrow> UNIV)"

definition "num_ivl n = I (Some n) (Some n)"

definition
  "contained_in i k \<longleftrightarrow> k \<in> rep_ivl i"

lemma in_rep_ivl_contained_in [code_unfold_post]:
  "k \<in> rep_ivl i \<longleftrightarrow> contained_in i k"
  by (simp only: contained_in_def)

lemma contained_in_simps [code]:
  "contained_in (I (Some l) (Some h)) k \<longleftrightarrow> l \<le> k \<and> k \<le> h"
  "contained_in (I (Some l) None) k \<longleftrightarrow> l \<le> k"
  "contained_in (I None (Some h)) k \<longleftrightarrow> k \<le> h"
  "contained_in (I None None) k \<longleftrightarrow> True"
  by (simp_all add: contained_in_def rep_ivl_def)

instantiation option :: (plus)plus
begin

fun plus_option where
"Some x + Some y = Some(x+y)" |
"_ + _ = None"

instance proof qed

end

definition empty where "empty = I (Some 1) (Some 0)"

fun is_empty where
"is_empty(I (Some l) (Some h)) = (h<l)" |
"is_empty _ = False"

lemma [simp]: "is_empty(I l h) =
  (case l of Some l \<Rightarrow> (case h of Some h \<Rightarrow> h<l | None \<Rightarrow> False) | None \<Rightarrow> False)"
by(auto split:option.split)

lemma [simp]: "is_empty i \<Longrightarrow> rep_ivl i = {}"
by(auto simp add: rep_ivl_def split: ivl.split option.split)

definition "plus_ivl i1 i2 = ((*if is_empty i1 | is_empty i2 then empty else*)
  case (i1,i2) of (I l1 h1, I l2 h2) \<Rightarrow> I (l1+l2) (h1+h2))"

instantiation ivl :: SL_top
begin

definition le_option :: "bool \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> bool" where
"le_option pos x y =
 (case x of (Some i) \<Rightarrow> (case y of Some j \<Rightarrow> i\<le>j | None \<Rightarrow> pos)
  | None \<Rightarrow> (case y of Some j \<Rightarrow> \<not>pos | None \<Rightarrow> True))"

fun le_aux where
"le_aux (I l1 h1) (I l2 h2) = (le_option False l2 l1 & le_option True h1 h2)"

definition le_ivl where
"i1 \<sqsubseteq> i2 =
 (if is_empty i1 then True else
  if is_empty i2 then False else le_aux i1 i2)"

definition min_option :: "bool \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> int option" where
"min_option pos o1 o2 = (if le_option pos o1 o2 then o1 else o2)"

definition max_option :: "bool \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> int option" where
"max_option pos o1 o2 = (if le_option pos o1 o2 then o2 else o1)"

definition "i1 \<squnion> i2 =
 (if is_empty i1 then i2 else if is_empty i2 then i1
  else case (i1,i2) of (I l1 h1, I l2 h2) \<Rightarrow>
          I (min_option False l1 l2) (max_option True h1 h2))"

definition "Top = I None None"

instance
proof
  case goal1 thus ?case
    by(cases x, simp add: le_ivl_def le_option_def split: option.split)
next
  case goal2 thus ?case
    by(cases x, cases y, cases z, auto simp: le_ivl_def le_option_def split: option.splits if_splits)
next
  case goal3 thus ?case
    by(cases x, cases y, simp add: le_ivl_def join_ivl_def le_option_def min_option_def max_option_def split: option.splits)
next
  case goal4 thus ?case
    by(cases x, cases y, simp add: le_ivl_def join_ivl_def le_option_def min_option_def max_option_def split: option.splits)
next
  case goal5 thus ?case
    by(cases x, cases y, cases z, auto simp add: le_ivl_def join_ivl_def le_option_def min_option_def max_option_def split: option.splits if_splits)
next
  case goal6 thus ?case
    by(cases x, simp add: Top_ivl_def le_ivl_def le_option_def split: option.split)
qed

end


instantiation ivl :: L_top_bot
begin

definition "i1 \<sqinter> i2 = (if is_empty i1 \<or> is_empty i2 then empty else
  case (i1,i2) of (I l1 h1, I l2 h2) \<Rightarrow>
    I (max_option False l1 l2) (min_option True h1 h2))"

definition "Bot = empty"

instance
proof
  case goal1 thus ?case
    by (simp add:meet_ivl_def empty_def meet_ivl_def le_ivl_def le_option_def max_option_def min_option_def split: ivl.splits option.splits)
next
  case goal2 thus ?case
    by (simp add:meet_ivl_def empty_def meet_ivl_def le_ivl_def le_option_def max_option_def min_option_def split: ivl.splits option.splits)
next
  case goal3 thus ?case
    by (cases x, cases y, cases z, auto simp add: le_ivl_def meet_ivl_def empty_def le_option_def max_option_def min_option_def split: option.splits if_splits)
next
  case goal4 show ?case by(cases x, simp add: Bot_ivl_def empty_def le_ivl_def)
qed

end

instantiation option :: (minus)minus
begin

fun minus_option where
"Some x - Some y = Some(x-y)" |
"_ - _ = None"

instance proof qed

end

definition "minus_ivl i1 i2 = ((*if is_empty i1 | is_empty i2 then empty else*)
  case (i1,i2) of (I l1 h1, I l2 h2) \<Rightarrow> I (l1-h2) (h1-l2))"

lemma rep_minus_ivl:
  "n1 : rep_ivl i1 \<Longrightarrow> n2 : rep_ivl i2 \<Longrightarrow> n1-n2 : rep_ivl(minus_ivl i1 i2)"
by(auto simp add: minus_ivl_def rep_ivl_def split: ivl.splits option.splits)


definition "filter_plus_ivl i i1 i2 = ((*if is_empty i then empty else*)
  i1 \<sqinter> minus_ivl i i2, i2 \<sqinter> minus_ivl i i1)"

fun filter_less_ivl :: "bool \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl * ivl" where
"filter_less_ivl res (I l1 h1) (I l2 h2) =
  ((*if is_empty(I l1 h1) \<or> is_empty(I l2 h2) then (empty, empty) else*)
   if res
   then (I l1 (min_option True h1 (h2 - Some 1)),
         I (max_option False (l1 + Some 1) l2) h2)
   else (I (max_option False l1 l2) h1, I l2 (min_option True h1 h2)))"

interpretation Rep rep_ivl
proof
  case goal1 thus ?case
    by(auto simp: rep_ivl_def le_ivl_def le_option_def split: ivl.split option.split if_splits)
qed

interpretation Val_abs rep_ivl num_ivl plus_ivl
proof
  case goal1 thus ?case by(simp add: rep_ivl_def num_ivl_def)
next
  case goal2 thus ?case
    by(auto simp add: rep_ivl_def plus_ivl_def split: ivl.split option.splits)
qed

interpretation Rep1 rep_ivl
proof
  case goal1 thus ?case
    by(auto simp add: rep_ivl_def meet_ivl_def empty_def min_option_def max_option_def split: ivl.split option.split)
next
  case goal2 show ?case by(auto simp add: Bot_ivl_def rep_ivl_def empty_def)
qed

interpretation
  Val_abs1 rep_ivl num_ivl plus_ivl filter_plus_ivl filter_less_ivl
proof
  case goal1 thus ?case
    by(auto simp add: filter_plus_ivl_def)
      (metis rep_minus_ivl add_diff_cancel add_commute)+
next
  case goal2 thus ?case
    by(cases a1, cases a2,
      auto simp: rep_ivl_def min_option_def max_option_def le_option_def split: if_splits option.splits)
qed

interpretation
  Abs_Int1 rep_ivl num_ivl plus_ivl filter_plus_ivl filter_less_ivl "(iter' 3)"
defines afilter_ivl is afilter
and bfilter_ivl is bfilter
and AI_ivl is AI
and aval_ivl is aval'
proof qed (auto simp: iter'_pfp_above)


fun list_up where
"list_up bot = bot" |
"list_up (Up x) = Up(list x)"

value [code] "list_up(afilter_ivl (N 5) (I (Some 4) (Some 5)) Top)"
value [code] "list_up(afilter_ivl (N 5) (I (Some 4) (Some 4)) Top)"
value [code] "list_up(afilter_ivl (V ''x'') (I (Some 4) (Some 4))
 (Up(FunDom(Top(''x'':=I (Some 5) (Some 6))) [''x''])))"
value [code] "list_up(afilter_ivl (V ''x'') (I (Some 4) (Some 5))
 (Up(FunDom(Top(''x'':=I (Some 5) (Some 6))) [''x''])))"
value [code] "list_up(afilter_ivl (Plus (V ''x'') (V ''x'')) (I (Some 0) (Some 10))
  (Up(FunDom(Top(''x'':= I (Some 0) (Some 100)))[''x''])))"
value [code] "list_up(afilter_ivl (Plus (V ''x'') (N 7)) (I (Some 0) (Some 10))
  (Up(FunDom(Top(''x'':= I (Some 0) (Some 100)))[''x''])))"

value [code] "list_up(bfilter_ivl (Less (V ''x'') (V ''x'')) True
  (Up(FunDom(Top(''x'':= I (Some 0) (Some 0)))[''x''])))"
value [code] "list_up(bfilter_ivl (Less (V ''x'') (V ''x'')) True
  (Up(FunDom(Top(''x'':= I (Some 0) (Some 2)))[''x''])))"
value [code] "list_up(bfilter_ivl (Less (V ''x'') (Plus (N 10) (V ''y''))) True
  (Up(FunDom(Top(''x'':= I (Some 15) (Some 20),''y'':= I (Some 5) (Some 7)))[''x'', ''y''])))"

definition "test_ivl1 =
 ''y'' ::= N 7;
 IF Less (V ''x'') (V ''y'')
 THEN ''y'' ::= Plus (V ''y'') (V ''x'')
 ELSE ''x'' ::= Plus (V ''x'') (V ''y'')"
value [code] "list_up(AI_ivl test_ivl1 Top)"

value "list_up (AI_ivl test3_const Top)"

value "list_up (AI_ivl test5_const Top)"

value "list_up (AI_ivl test6_const Top)"

definition "test2_ivl =
 ''y'' ::= N 7;
 WHILE Less (V ''x'') (N 100) DO ''y'' ::= Plus (V ''y'') (N 1)"
value [code] "list_up(AI_ivl test2_ivl Top)"

definition "test3_ivl =
 ''x'' ::= N 0; ''y'' ::= N 100; ''z'' ::= Plus (V ''x'') (V ''y'');
 WHILE Less (V ''x'') (N 11)
 DO (''x'' ::= Plus (V ''x'') (N 1); ''y'' ::= Plus (V ''y'') (N -1))"
value [code] "list_up(AI_ivl test3_ivl Top)"

definition "test4_ivl =
 ''x'' ::= N 0; ''y'' ::= N 0;
 WHILE Less (V ''x'') (N 1001)
 DO (''y'' ::= V ''x''; ''x'' ::= Plus (V ''x'') (N 1))"
value [code] "list_up(AI_ivl test4_ivl Top)"

text{* Nontermination not detected: *}
definition "test5_ivl =
 ''x'' ::= N 0;
 WHILE Less (V ''x'') (N 1) DO ''x'' ::= Plus (V ''x'') (N -1)"
value [code] "list_up(AI_ivl test5_ivl Top)"

end
