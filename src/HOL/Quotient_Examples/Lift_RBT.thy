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

(* FIXME: quotient_definition at the moment requires that types variables match exactly,
i.e., sort constraints must be annotated to the constant being lifted.
But, it should be possible to infer the necessary sort constraints, making the explicit
sort constraints unnecessary.

Hence this unannotated quotient_definition fails:

quotient_definition empty where "empty :: ('a\<Colon>linorder, 'b) rbt"
is "RBT_Impl.Empty"

Similar issue for quotient_definition for entries, keys, map, and fold.
*)

quotient_definition empty where "empty :: ('a\<Colon>linorder, 'b) rbt"
is "(RBT_Impl.Empty :: ('a\<Colon>linorder, 'b) RBT_Impl.rbt)"

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

(* FIXME: unnecessary type annotations *)
quotient_definition "entries :: ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a \<times> 'b) list"
is "RBT_Impl.entries :: ('a\<Colon>linorder, 'b) RBT_Impl.rbt \<Rightarrow> ('a \<times> 'b) list"

lemma [code]: "entries t = RBT_Impl.entries (impl_of t)"
unfolding entries_def map_fun_def comp_def id_def ..

(* FIXME: unnecessary type annotations *)
quotient_definition "keys :: ('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'a list"
is "RBT_Impl.keys :: ('a\<Colon>linorder, 'b) RBT_Impl.rbt \<Rightarrow> 'a list"

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

(* FIXME: unnecesary type annotations *)
quotient_definition map where "map :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
is "RBT_Impl.map :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a\<Colon>linorder, 'b) RBT_Impl.rbt \<Rightarrow> ('a, 'b) RBT_Impl.rbt"

lemma impl_of_map [code abstract]:
  "impl_of (map f t) = RBT_Impl.map f (impl_of t)"
  by (simp add: map_def RBT_inverse)

(* FIXME: unnecessary type annotations *)
quotient_definition fold where "fold :: ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a\<Colon>linorder, 'b) rbt \<Rightarrow> 'c \<Rightarrow> 'c" is "RBT_Impl.fold :: ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a\<Colon>linorder, 'b) RBT_Impl.rbt \<Rightarrow> 'c \<Rightarrow> 'c"

lemma [code]: "fold f t = RBT_Impl.fold f (impl_of t)"
unfolding fold_def map_fun_def comp_def id_def ..


subsection {* Derived operations *}

definition is_empty :: "('a\<Colon>linorder, 'b) rbt \<Rightarrow> bool" where
  [code]: "is_empty t = (case impl_of t of RBT_Impl.Empty \<Rightarrow> True | _ \<Rightarrow> False)"


subsection {* Abstract lookup properties *}

(* TODO: obtain the following lemmas by lifting existing theorems. *)

lemma lookup_RBT:
  "is_rbt t \<Longrightarrow> lookup (RBT t) = RBT_Impl.lookup t"
  by (simp add: lookup_def RBT_inverse)

lemma lookup_impl_of:
  "RBT_Impl.lookup (impl_of t) = lookup t"
  by (simp add: lookup_def)

lemma entries_impl_of:
  "RBT_Impl.entries (impl_of t) = entries t"
  by (simp add: entries_def)

lemma keys_impl_of:
  "RBT_Impl.keys (impl_of t) = keys t"
  by (simp add: keys_def)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
  by (simp add: empty_def lookup_RBT fun_eq_iff)

lemma lookup_insert [simp]:
  "lookup (insert k v t) = (lookup t)(k \<mapsto> v)"
  by (simp add: insert_def lookup_RBT lookup_insert lookup_impl_of)

lemma lookup_delete [simp]:
  "lookup (delete k t) = (lookup t)(k := None)"
  by (simp add: delete_def lookup_RBT RBT_Impl.lookup_delete lookup_impl_of restrict_complement_singleton_eq)

lemma map_of_entries [simp]:
  "map_of (entries t) = lookup t"
  by (simp add: entries_def map_of_entries lookup_impl_of)

lemma entries_lookup:
  "entries t1 = entries t2 \<longleftrightarrow> lookup t1 = lookup t2"
  by (simp add: entries_def lookup_def entries_lookup)

lemma lookup_bulkload [simp]:
  "lookup (bulkload xs) = map_of xs"
  by (simp add: bulkload_def lookup_RBT RBT_Impl.lookup_bulkload)

lemma lookup_map_entry [simp]:
  "lookup (map_entry k f t) = (lookup t)(k := Option.map f (lookup t k))"
  by (simp add: map_entry_def lookup_RBT RBT_Impl.lookup_map_entry lookup_impl_of)

lemma lookup_map [simp]:
  "lookup (map f t) k = Option.map (f k) (lookup t k)"
  by (simp add: map_def lookup_RBT RBT_Impl.lookup_map lookup_impl_of)

lemma fold_fold:
  "fold f t = More_List.fold (prod_case f) (entries t)"
  by (simp add: fold_def fun_eq_iff RBT_Impl.fold_def entries_impl_of)

lemma is_empty_empty [simp]:
  "is_empty t \<longleftrightarrow> t = empty"
  by (simp add: rbt_eq_iff is_empty_def impl_of_empty split: rbt.split)

lemma RBT_lookup_empty [simp]: (*FIXME*)
  "RBT_Impl.lookup t = Map.empty \<longleftrightarrow> t = RBT_Impl.Empty"
  by (cases t) (auto simp add: fun_eq_iff)

lemma lookup_empty_empty [simp]:
  "lookup t = Map.empty \<longleftrightarrow> t = empty"
  by (cases t) (simp add: empty_def lookup_def RBT_inject RBT_inverse)

lemma sorted_keys [iff]:
  "sorted (keys t)"
  by (simp add: keys_def RBT_Impl.keys_def sorted_entries)

lemma distinct_keys [iff]:
  "distinct (keys t)"
  by (simp add: keys_def RBT_Impl.keys_def distinct_entries)



end