(*  Title:      HOL/Library/State_Monad.thy
    Author:     Lars Hupel, TU München
*)

section \<open>State monad\<close>

theory State_Monad
imports Monad_Syntax
begin

datatype ('s, 'a) state = State (run_state: "'s \<Rightarrow> ('a \<times> 's)")

lemma set_state_iff: "x \<in> set_state m \<longleftrightarrow> (\<exists>s s'. run_state m s = (x, s'))"
by (cases m) (simp add: prod_set_defs eq_fst_iff)

lemma pred_stateI[intro]:
  assumes "\<And>a s s'. run_state m s = (a, s') \<Longrightarrow> P a"
  shows "pred_state P m"
proof (subst state.pred_set, rule)
  fix x
  assume "x \<in> set_state m"
  then obtain s s' where "run_state m s = (x, s')"
    by (auto simp: set_state_iff)
  with assms show "P x" .
qed

lemma pred_stateD[dest]:
  assumes "pred_state P m" "run_state m s = (a, s')"
  shows "P a"
proof (rule state.exhaust[of m])
  fix f
  assume "m = State f"
  with assms have "pred_fun (\<lambda>_. True) (pred_prod P top) f"
    by (metis state.pred_inject)
  moreover have "f s = (a, s')"
    using assms unfolding \<open>m = _\<close> by auto
  ultimately show "P a"
    unfolding pred_prod_beta pred_fun_def
    by (metis fst_conv)
qed

lemma pred_state_run_state: "pred_state P m \<Longrightarrow> P (fst (run_state m s))"
by (meson pred_stateD prod.exhaust_sel)

definition state_io_rel :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s, 'a) state \<Rightarrow> bool" where
"state_io_rel P m = (\<forall>s. P s (snd (run_state m s)))"

lemma state_io_relI[intro]:
  assumes "\<And>a s s'. run_state m s = (a, s') \<Longrightarrow> P s s'"
  shows "state_io_rel P m"
using assms unfolding state_io_rel_def
by (metis prod.collapse)

lemma state_io_relD[dest]:
  assumes "state_io_rel P m" "run_state m s = (a, s')"
  shows "P s s'"
using assms unfolding state_io_rel_def
by (metis snd_conv)

lemma state_io_rel_mono[mono]: "P \<le> Q \<Longrightarrow> state_io_rel P \<le> state_io_rel Q"
by blast

lemma state_ext:
  assumes "\<And>s. run_state m s = run_state n s"
  shows "m = n"
using assms
by (cases m; cases n) auto

context begin

qualified definition return :: "'a \<Rightarrow> ('s, 'a) state" where
"return a = State (Pair a)"

lemma run_state_return[simp]: "run_state (return x) s = (x, s)"
unfolding return_def
by simp

qualified definition ap :: "('s, 'a \<Rightarrow> 'b) state \<Rightarrow> ('s, 'a) state \<Rightarrow> ('s, 'b) state" where
"ap f x = State (\<lambda>s. case run_state f s of (g, s') \<Rightarrow> case run_state x s' of (y, s'') \<Rightarrow> (g y, s''))"

lemma run_state_ap[simp]:
  "run_state (ap f x) s = (case run_state f s of (g, s') \<Rightarrow> case run_state x s' of (y, s'') \<Rightarrow> (g y, s''))"
unfolding ap_def by auto

qualified definition bind :: "('s, 'a) state \<Rightarrow> ('a \<Rightarrow> ('s, 'b) state) \<Rightarrow> ('s, 'b) state" where
"bind x f = State (\<lambda>s. case run_state x s of (a, s') \<Rightarrow> run_state (f a) s')"

lemma run_state_bind[simp]:
  "run_state (bind x f) s = (case run_state x s of (a, s') \<Rightarrow> run_state (f a) s')"
unfolding bind_def by auto

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bind

lemma bind_left_identity[simp]: "bind (return a) f = f a"
unfolding return_def bind_def by simp

lemma bind_right_identity[simp]: "bind m return = m"
unfolding return_def bind_def by simp

lemma bind_assoc[simp]: "bind (bind m f) g = bind m (\<lambda>x. bind (f x) g)"
unfolding bind_def by (auto split: prod.splits)

lemma bind_predI[intro]:
  assumes "pred_state (\<lambda>x. pred_state P (f x)) m"
  shows "pred_state P (bind m f)"
apply (rule pred_stateI)
unfolding bind_def
using assms by (auto split: prod.splits)

qualified definition get :: "('s, 's) state" where
"get = State (\<lambda>s. (s, s))"

lemma run_state_get[simp]: "run_state get s = (s, s)"
unfolding get_def by simp

qualified definition set :: "'s \<Rightarrow> ('s, unit) state" where
"set s' = State (\<lambda>_. ((), s'))"

lemma run_state_set[simp]: "run_state (set s') s = ((), s')"
unfolding set_def by simp

lemma get_set[simp]: "bind get set = return ()"
unfolding bind_def get_def set_def return_def
by simp

lemma set_set[simp]: "bind (set s) (\<lambda>_. set s') = set s'"
unfolding bind_def set_def
by simp

lemma get_bind_set[simp]: "bind get (\<lambda>s. bind (set s) (f s)) = bind get (\<lambda>s. f s ())"
unfolding bind_def get_def set_def
by simp

lemma get_const[simp]: "bind get (\<lambda>_. m) = m"
unfolding get_def bind_def
by simp

fun traverse_list :: "('a \<Rightarrow> ('b, 'c) state) \<Rightarrow> 'a list \<Rightarrow> ('b, 'c list) state" where
"traverse_list _ [] = return []" |
"traverse_list f (x # xs) = do {
  x \<leftarrow> f x;
  xs \<leftarrow> traverse_list f xs;
  return (x # xs)
}"

lemma traverse_list_app[simp]: "traverse_list f (xs @ ys) = do {
  xs \<leftarrow> traverse_list f xs;
  ys \<leftarrow> traverse_list f ys;
  return (xs @ ys)
}"
by (induction xs) auto

lemma traverse_comp[simp]: "traverse_list (g \<circ> f) xs = traverse_list g (map f xs)"
by (induction xs) auto

abbreviation mono_state :: "('s::preorder, 'a) state \<Rightarrow> bool" where
"mono_state \<equiv> state_io_rel (\<le>)"

abbreviation strict_mono_state :: "('s::preorder, 'a) state \<Rightarrow> bool" where
"strict_mono_state \<equiv> state_io_rel (<)"

corollary strict_mono_implies_mono: "strict_mono_state m \<Longrightarrow> mono_state m"
unfolding state_io_rel_def
by (simp add: less_imp_le)

lemma return_mono[simp, intro]: "mono_state (return x)"
unfolding return_def by auto

lemma get_mono[simp, intro]: "mono_state get"
unfolding get_def by auto

lemma put_mono:
  assumes "\<And>x. s' \<ge> x"
  shows "mono_state (set s')"
using assms unfolding set_def
by auto

lemma map_mono[intro]: "mono_state m \<Longrightarrow> mono_state (map_state f m)"
by (auto intro!: state_io_relI split: prod.splits simp: map_prod_def state.map_sel)

lemma map_strict_mono[intro]: "strict_mono_state m \<Longrightarrow> strict_mono_state (map_state f m)"
by (auto intro!: state_io_relI split: prod.splits simp: map_prod_def state.map_sel)

lemma bind_mono_strong:
  assumes "mono_state m"
  assumes "\<And>x s s'. run_state m s = (x, s') \<Longrightarrow> mono_state (f x)"
  shows "mono_state (bind m f)"
unfolding bind_def
apply (rule state_io_relI)
using assms by (auto split: prod.splits dest!: state_io_relD intro: order_trans)

lemma bind_strict_mono_strong1:
  assumes "mono_state m"
  assumes "\<And>x s s'. run_state m s = (x, s') \<Longrightarrow> strict_mono_state (f x)"
  shows "strict_mono_state (bind m f)"
unfolding bind_def
apply (rule state_io_relI)
using assms by (auto split: prod.splits dest!: state_io_relD intro: le_less_trans)

lemma bind_strict_mono_strong2:
  assumes "strict_mono_state m"
  assumes "\<And>x s s'. run_state m s = (x, s') \<Longrightarrow> mono_state (f x)"
  shows "strict_mono_state (bind m f)"
unfolding bind_def
apply (rule state_io_relI)
using assms by (auto split: prod.splits dest!: state_io_relD intro: less_le_trans)

corollary bind_strict_mono_strong:
  assumes "strict_mono_state m"
  assumes "\<And>x s s'. run_state m s = (x, s') \<Longrightarrow> strict_mono_state (f x)"
  shows "strict_mono_state (bind m f)"
using assms by (auto intro: bind_strict_mono_strong1 strict_mono_implies_mono)

qualified definition update :: "('s \<Rightarrow> 's) \<Rightarrow> ('s, unit) state" where
"update f = bind get (set \<circ> f)"

lemma update_id[simp]: "update (\<lambda>x. x) = return ()"
unfolding update_def return_def get_def set_def bind_def
by auto

lemma update_comp[simp]: "bind (update f) (\<lambda>_. update g) = update (g \<circ> f)"
unfolding update_def return_def get_def set_def bind_def
by auto

lemma set_update[simp]: "bind (set s) (\<lambda>_. update f) = set (f s)"
unfolding set_def update_def bind_def get_def set_def
by simp

lemma set_bind_update[simp]: "bind (set s) (\<lambda>_. bind (update f) g) = bind (set (f s)) g"
unfolding set_def update_def bind_def get_def set_def
by simp

lemma update_mono:
  assumes "\<And>x. x \<le> f x"
  shows "mono_state (update f)"
using assms unfolding update_def get_def set_def bind_def
by (auto intro!: state_io_relI)

lemma update_strict_mono:
  assumes "\<And>x. x < f x"
  shows "strict_mono_state (update f)"
using assms unfolding update_def get_def set_def bind_def
by (auto intro!: state_io_relI)

end

end