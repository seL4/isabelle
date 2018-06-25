(* Author: Tobias Nipkow *)

section \<open>Specifications of Map ADT\<close>

theory Map_Specs
imports AList_Upd_Del
begin

text \<open>The basic map interface with traditional \<open>set\<close>-based specification:\<close>

locale Map =
fixes empty :: "'m"
fixes update :: "'a \<Rightarrow> 'b \<Rightarrow> 'm \<Rightarrow> 'm"
fixes delete :: "'a \<Rightarrow> 'm \<Rightarrow> 'm"
fixes lookup :: "'m \<Rightarrow> 'a \<Rightarrow> 'b option"
fixes invar :: "'m \<Rightarrow> bool"
assumes map_empty: "lookup empty = (\<lambda>_. None)"
and map_update: "invar m \<Longrightarrow> lookup(update a b m) = (lookup m)(a := Some b)"
and map_delete: "invar m \<Longrightarrow> lookup(delete a m) = (lookup m)(a := None)"
and invar_empty: "invar empty"
and invar_update: "invar m \<Longrightarrow> invar(update a b m)"
and invar_delete: "invar m \<Longrightarrow> invar(delete a m)"

lemmas (in Map) map_specs =
  map_empty map_update map_delete invar_empty invar_update invar_delete


text \<open>The basic map interface with \<open>inorder\<close>-based specification:\<close>

locale Map_by_Ordered =
fixes empty :: "'t"
fixes update :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> 't \<Rightarrow> 't"
fixes delete :: "'a \<Rightarrow> 't \<Rightarrow> 't"
fixes lookup :: "'t \<Rightarrow> 'a \<Rightarrow> 'b option"
fixes inorder :: "'t \<Rightarrow> ('a * 'b) list"
fixes inv :: "'t \<Rightarrow> bool"
assumes inorder_empty: "inorder empty = []"
and inorder_lookup: "inv t \<and> sorted1 (inorder t) \<Longrightarrow>
  lookup t a = map_of (inorder t) a"
and inorder_update: "inv t \<and> sorted1 (inorder t) \<Longrightarrow>
  inorder(update a b t) = upd_list a b (inorder t)"
and inorder_delete: "inv t \<and> sorted1 (inorder t) \<Longrightarrow>
  inorder(delete a t) = del_list a (inorder t)"
and inorder_inv_empty:  "inv empty"
and inorder_inv_update: "inv t \<and> sorted1 (inorder t) \<Longrightarrow> inv(update a b t)"
and inorder_inv_delete: "inv t \<and> sorted1 (inorder t) \<Longrightarrow> inv(delete a t)"

begin

text \<open>It implements the traditional specification:\<close>

definition invar :: "'t \<Rightarrow> bool" where
"invar t == inv t \<and> sorted1 (inorder t)"

sublocale Map
  empty update delete lookup invar
proof(standard, goal_cases)
  case 1 show ?case by (auto simp: inorder_lookup inorder_empty inorder_inv_empty)
next
  case 2 thus ?case
    by(simp add: fun_eq_iff inorder_update inorder_inv_update map_of_ins_list inorder_lookup
         sorted_upd_list invar_def)
next
  case 3 thus ?case
    by(simp add: fun_eq_iff inorder_delete inorder_inv_delete map_of_del_list inorder_lookup
         sorted_del_list invar_def)
next
  case 4 thus ?case by(simp add: inorder_empty inorder_inv_empty invar_def)
next
  case 5 thus ?case by(simp add: inorder_update inorder_inv_update sorted_upd_list invar_def)
next
  case 6 thus ?case by (auto simp: inorder_delete inorder_inv_delete sorted_del_list invar_def)
qed

end

end
