(* Author: Tobias Nipkow *)

theory Abs_State
imports Abs_Int0_fun
  "~~/src/HOL/Library/Char_ord" "~~/src/HOL/Library/List_lexord"
  (* Library import merely to allow string lists to be sorted for output *)
begin

subsection "Abstract State with Computable Ordering"

text{* A concrete type of state with computable @{text"\<sqsubseteq>"}: *}

datatype 'a st = FunDom "name \<Rightarrow> 'a" "name list"

fun "fun" where "fun (FunDom f _) = f"
fun dom where "dom (FunDom _ A) = A"

definition [simp]: "inter_list xs ys = [x\<leftarrow>xs. x \<in> set ys]"

definition "show_st S = [(x,fun S x). x \<leftarrow> sort(dom S)]"

fun show_st_up where
"show_st_up Bot = Bot" |
"show_st_up (Up S) = Up(show_st S)"

definition "show_acom = map_acom show_st_up"
definition "show_acom_opt = Option.map show_acom"

definition "lookup F x = (if x : set(dom F) then fun F x else \<top>)"

definition "update F x y =
  FunDom ((fun F)(x:=y)) (if x \<in> set(dom F) then dom F else x # dom F)"

lemma lookup_update: "lookup (update S x y) = (lookup S)(x:=y)"
by(rule ext)(auto simp: lookup_def update_def)

definition "rep_st rep F = {f. \<forall>x. f x \<in> rep(lookup F x)}"

instantiation st :: (SL_top) SL_top
begin

definition "le_st F G = (ALL x : set(dom G). lookup F x \<sqsubseteq> fun G x)"

definition
"join_st F G =
 FunDom (\<lambda>x. fun F x \<squnion> fun G x) (inter_list (dom F) (dom G))"

definition "\<top> = FunDom (\<lambda>x. \<top>) []"

instance
proof
  case goal2 thus ?case
    apply(auto simp: le_st_def)
    by (metis lookup_def preord_class.le_trans top)
qed (auto simp: le_st_def lookup_def join_st_def Top_st_def)

end

lemma mono_lookup: "F \<sqsubseteq> F' \<Longrightarrow> lookup F x \<sqsubseteq> lookup F' x"
by(auto simp add: lookup_def le_st_def)

lemma mono_update: "a \<sqsubseteq> a' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> update S x a \<sqsubseteq> update S' x a'"
by(auto simp add: le_st_def lookup_def update_def)

context Val_abs
begin

abbreviation fun_in_rep :: "state \<Rightarrow> 'a st \<Rightarrow> bool" (infix "<:f" 50) where
"s <:f S == s \<in> rep_st rep S"

notation fun_in_rep (infix "<:\<^sub>f" 50)

lemma fun_in_rep_le: "s <:f S \<Longrightarrow> S \<sqsubseteq> T \<Longrightarrow> s <:f T"
apply(auto simp add: rep_st_def le_st_def dest: le_rep)
by (metis in_rep_Top le_rep lookup_def subsetD)

abbreviation in_rep_up :: "state \<Rightarrow> 'a st up \<Rightarrow> bool"  (infix "<:up" 50)
where "s <:up S == s : rep_up (rep_st rep) S"

notation (output) in_rep_up (infix "<:\<^sub>u\<^sub>p" 50)

lemma up_fun_in_rep_le: "s <:up S \<Longrightarrow> S \<sqsubseteq> T \<Longrightarrow> s <:up T"
by (cases S) (auto intro:fun_in_rep_le)

lemma in_rep_up_iff: "x <:up u \<longleftrightarrow> (\<exists>u'. u = Up u' \<and> x <:f u')"
by (cases u) auto

lemma in_rep_Top_fun: "s <:f \<top>"
by(simp add: rep_st_def lookup_def Top_st_def)

lemma in_rep_Top_up: "s <:up \<top>"
by(simp add: Top_up_def in_rep_Top_fun)

end

end
