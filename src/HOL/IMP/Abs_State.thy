(* Author: Tobias Nipkow *)

theory Abs_State
imports Abs_Int0_fun
  "~~/src/HOL/Library/Char_ord" "~~/src/HOL/Library/List_lexord"
  (* Library import merely to allow string lists to be sorted for output *)
begin

subsection "Abstract State with Computable Ordering"

text{* A concrete type of state with computable @{text"\<sqsubseteq>"}: *}

datatype 'a st = FunDom "vname \<Rightarrow> 'a" "vname list"

fun "fun" where "fun (FunDom f _) = f"
fun dom where "dom (FunDom _ A) = A"

definition [simp]: "inter_list xs ys = [x\<leftarrow>xs. x \<in> set ys]"

definition "show_st S = [(x,fun S x). x \<leftarrow> sort(dom S)]"

definition "show_acom = map_acom (Option.map show_st)"
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

abbreviation rep_f :: "'a st \<Rightarrow> state set" ("\<gamma>\<^isub>f")
where "\<gamma>\<^isub>f == rep_st rep"

abbreviation rep_u :: "'a st option \<Rightarrow> state set" ("\<gamma>\<^isub>u")
where "\<gamma>\<^isub>u == rep_option \<gamma>\<^isub>f"

abbreviation rep_c :: "'a st option acom \<Rightarrow> state set acom" ("\<gamma>\<^isub>c")
where "\<gamma>\<^isub>c == map_acom \<gamma>\<^isub>u"

lemma rep_f_Top[simp]: "rep_f Top = UNIV"
by(auto simp: Top_st_def rep_st_def lookup_def)

lemma rep_u_Top[simp]: "rep_u Top = UNIV"
by (simp add: Top_option_def)

(* FIXME (maybe also le \<rightarrow> sqle?) *)

lemma mono_rep_f: "f \<sqsubseteq> g \<Longrightarrow> \<gamma>\<^isub>f f \<subseteq> \<gamma>\<^isub>f g"
apply(simp add:rep_st_def subset_iff lookup_def le_st_def split: if_splits)
by (metis UNIV_I mono_rep rep_Top subsetD)

lemma mono_rep_u:
  "sa \<sqsubseteq> sa' \<Longrightarrow> \<gamma>\<^isub>u sa \<subseteq> \<gamma>\<^isub>u sa'"
by(induction sa sa' rule: le_option.induct)(simp_all add: mono_rep_f)

lemma mono_rep_c: "ca \<sqsubseteq> ca' \<Longrightarrow> \<gamma>\<^isub>c ca \<le> \<gamma>\<^isub>c ca'"
by (induction ca ca' rule: le_acom.induct) (simp_all add:mono_rep_u)

lemma in_rep_up_iff: "x : rep_option r u \<longleftrightarrow> (\<exists>u'. u = Some u' \<and> x : r u')"
by (cases u) auto

end

end
