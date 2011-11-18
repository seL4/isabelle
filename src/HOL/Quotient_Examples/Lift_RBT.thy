(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Lifting operations of RBT trees *}

theory Lift_RBT 
imports Main "~~/src/HOL/Library/RBT_Impl"
begin

subsection {* Type definition *}

typedef (open) ('a, 'b) rbt = "{t :: ('a\<Colon>linorder, 'b) RBT_Impl.rbt. is_rbt t}"
  morphisms impl_of RBT
proof -
  have "RBT_Impl.Empty \<in> ?rbt" by simp
  then show ?thesis ..
qed

local_setup {* fn lthy =>
let
  val quotients = {qtyp = @{typ "('a, 'b) rbt"}, rtyp = @{typ "('a, 'b) RBT_Impl.rbt"},
    equiv_rel = @{term "dummy"}, equiv_thm = @{thm refl}}
  val qty_full_name = @{type_name "rbt"}

  fun qinfo phi = Quotient_Info.transform_quotients phi quotients
  in lthy
    |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Quotient_Info.update_quotients qty_full_name (qinfo phi)
       #> Quotient_Info.update_abs_rep qty_full_name (Quotient_Info.transform_abs_rep phi
         {abs = @{term "RBT"}, rep = @{term "impl_of"}}))
  end
*}

lemma rbt_eq_iff:
  "t1 = t2 \<longleftrightarrow> impl_of t1 = impl_of t2"
  by (simp add: impl_of_inject)

lemma rbt_eqI:
  "impl_of t1 = impl_of t2 \<Longrightarrow> t1 = t2"
  by (simp add: rbt_eq_iff)

lemma is_rbt_impl_of [simp, intro]:
  "is_rbt (impl_of t)"
  using impl_of [of t] by simp

lemma RBT_impl_of [simp, code abstype]:
  "RBT (impl_of t) = t"
  by (simp add: impl_of_inverse)


subsection {* Primitive operations *}

quotient_definition lookup where "lookup :: ('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b" is "RBT_Impl.lookup"

declare lookup_def[unfolded map_fun_def comp_def id_def, code]

(* FIXME: some bug in quotient?*)
(*
quotient_definition empty where "empty :: ('a\<Colon>linorder, 'b) rbt"
is "RBT_Impl.Empty"
*)

definition empty :: "('a\<Colon>linorder, 'b) rbt" where
  "empty = RBT RBT_Impl.Empty"

lemma impl_of_empty [code abstract]:
  "impl_of empty = RBT_Impl.Empty"
  by (simp add: empty_def RBT_inverse)

quotient_definition insert where "insert :: 'a\<Colon>linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
is "RBT_Impl.insert"

lemma impl_of_insert [code abstract]:
  "impl_of (insert k v t) = RBT_Impl.insert k v (impl_of t)"
  by (simp add: insert_def RBT_inverse)

quotient_definition delete where "delete :: 'a\<Colon>linorder \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
is "RBT_Impl.delete"

lemma impl_of_delete [code abstract]:
  "impl_of (delete k t) = RBT_Impl.delete k (impl_of t)"
  by (simp add: delete_def RBT_inverse)

(* FIXME: bug in quotient? *)
(*
quotient_definition entries where "entries :: ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a \<times> 'b) list"
is "RBT_Impl.entries"
*)
definition entries :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a \<times> 'b) list" where
  [code]: "entries t = RBT_Impl.entries (impl_of t)"

(* FIXME: bug in quotient? *)
(*
quotient_definition keys where "keys :: ('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'a list"
is "RBT_Impl.keys"
*)

quotient_definition "bulkload :: ('a\<Colon>linorder \<times> 'b) list \<Rightarrow> ('a, 'b) rbt"
is "RBT_Impl.bulkload"

lemma impl_of_bulkload [code abstract]:
  "impl_of (bulkload xs) = RBT_Impl.bulkload xs"
  by (simp add: bulkload_def RBT_inverse)

quotient_definition "map_entry :: 'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
is "RBT_Impl.map_entry"

lemma impl_of_map_entry [code abstract]:
  "impl_of (map_entry k f t) = RBT_Impl.map_entry k f (impl_of t)"
  by (simp add: map_entry_def RBT_inverse)

(* Another bug: map is supposed to be a new definition, not using the old one.
quotient_definition "map :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
is "RBT_Impl.map"
*)
(* But this works, and then shows the other bug... *)
(*
quotient_definition map where "map :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
is "RBT_Impl.map"
*)
definition map :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "map f t = RBT (RBT_Impl.map f (impl_of t))"

lemma impl_of_map [code abstract]:
  "impl_of (map f t) = RBT_Impl.map f (impl_of t)"
  by (simp add: map_def RBT_inverse)
(* FIXME: bug?
quotient_definition fold where "fold :: ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c" is "RBT_Impl.fold"
*)
(*FIXME: definition of fold should have the code attribute. *)

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c" where
  [code]: "fold f t = RBT_Impl.fold f (impl_of t)"


end