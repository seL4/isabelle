(*  Title:      HOL/Library/Mapping.thy
    Author:     Florian Haftmann and Ondrej Kuncar
*)

section \<open>An abstract view on maps for code generation.\<close>

theory Mapping
imports Main AList
begin

subsection \<open>Parametricity transfer rules\<close>

lemma map_of_foldr: "map_of xs = foldr (\<lambda>(k, v) m. m(k \<mapsto> v)) xs Map.empty"  (* FIXME move *)
  using map_add_map_of_foldr [of Map.empty] by auto

context includes lifting_syntax
begin

lemma empty_parametric: "(A ===> rel_option B) Map.empty Map.empty"
  by transfer_prover

lemma lookup_parametric: "((A ===> B) ===> A ===> B) (\<lambda>m k. m k) (\<lambda>m k. m k)"
  by transfer_prover

lemma update_parametric:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> B ===> (A ===> rel_option B) ===> A ===> rel_option B)
    (\<lambda>k v m. m(k \<mapsto> v)) (\<lambda>k v m. m(k \<mapsto> v))"
  by transfer_prover

lemma delete_parametric:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> (A ===> rel_option B) ===> A ===> rel_option B)
    (\<lambda>k m. m(k := None)) (\<lambda>k m. m(k := None))"
  by transfer_prover

lemma is_none_parametric [transfer_rule]:
  "(rel_option A ===> HOL.eq) Option.is_none Option.is_none"
  by (auto simp add: Option.is_none_def rel_fun_def rel_option_iff split: option.split)

lemma dom_parametric:
  assumes [transfer_rule]: "bi_total A"
  shows "((A ===> rel_option B) ===> rel_set A) dom dom"
  unfolding dom_def [abs_def] Option.is_none_def [symmetric] by transfer_prover

lemma graph_parametric:
  assumes "bi_total A"
  shows "((A ===> rel_option B) ===> rel_set (rel_prod A B)) Map.graph Map.graph"
proof
  fix f g assume "(A ===> rel_option B) f g"
  with assms[unfolded bi_total_def] show "rel_set (rel_prod A B) (Map.graph f) (Map.graph g)"
    unfolding graph_def rel_set_def rel_fun_def
    by auto (metis option_rel_Some1 option_rel_Some2)+
qed

lemma map_of_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique R1"
  shows "(list_all2 (rel_prod R1 R2) ===> R1 ===> rel_option R2) map_of map_of"
  unfolding map_of_def by transfer_prover

lemma map_entry_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> (B ===> B) ===> (A ===> rel_option B) ===> A ===> rel_option B)
    (\<lambda>k f m. (case m k of None \<Rightarrow> m
      | Some v \<Rightarrow> m (k \<mapsto> (f v)))) (\<lambda>k f m. (case m k of None \<Rightarrow> m
      | Some v \<Rightarrow> m (k \<mapsto> (f v))))"
  by transfer_prover

lemma tabulate_parametric:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> (A ===> B) ===> A ===> rel_option B)
    (\<lambda>ks f. (map_of (map (\<lambda>k. (k, f k)) ks))) (\<lambda>ks f. (map_of (map (\<lambda>k. (k, f k)) ks)))"
  by transfer_prover

lemma bulkload_parametric:
  "(list_all2 A ===> HOL.eq ===> rel_option A)
    (\<lambda>xs k. if k < length xs then Some (xs ! k) else None)
    (\<lambda>xs k. if k < length xs then Some (xs ! k) else None)"
proof
  fix xs ys
  assume "list_all2 A xs ys"
  then show
    "(HOL.eq ===> rel_option A)
      (\<lambda>k. if k < length xs then Some (xs ! k) else None)
      (\<lambda>k. if k < length ys then Some (ys ! k) else None)"
    apply induct
     apply auto
    unfolding rel_fun_def
    apply clarsimp
    apply (case_tac xa)
     apply (auto dest: list_all2_lengthD list_all2_nthD)
    done
qed

lemma map_parametric:
  "((A ===> B) ===> (C ===> D) ===> (B ===> rel_option C) ===> A ===> rel_option D)
     (\<lambda>f g m. (map_option g \<circ> m \<circ> f)) (\<lambda>f g m. (map_option g \<circ> m \<circ> f))"
  by transfer_prover

lemma combine_with_key_parametric:
  "((A ===> B ===> B ===> B) ===> (A ===> rel_option B) ===> (A ===> rel_option B) ===>
    (A ===> rel_option B)) (\<lambda>f m1 m2 x. combine_options (f x) (m1 x) (m2 x))
    (\<lambda>f m1 m2 x. combine_options (f x) (m1 x) (m2 x))"
  unfolding combine_options_def by transfer_prover

lemma combine_parametric:
  "((B ===> B ===> B) ===> (A ===> rel_option B) ===> (A ===> rel_option B) ===>
    (A ===> rel_option B)) (\<lambda>f m1 m2 x. combine_options f (m1 x) (m2 x))
    (\<lambda>f m1 m2 x. combine_options f (m1 x) (m2 x))"
  unfolding combine_options_def by transfer_prover

end


subsection \<open>Type definition and primitive operations\<close>

typedef ('a, 'b) mapping = "UNIV :: ('a \<rightharpoonup> 'b) set"
  morphisms rep Mapping ..

setup_lifting type_definition_mapping

lift_definition empty :: "('a, 'b) mapping"
  is Map.empty parametric empty_parametric .

lift_definition lookup :: "('a, 'b) mapping \<Rightarrow> 'a \<Rightarrow> 'b option"
  is "\<lambda>m k. m k" parametric lookup_parametric .

definition "lookup_default d m k = (case Mapping.lookup m k of None \<Rightarrow> d | Some v \<Rightarrow> v)"

lift_definition update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
  is "\<lambda>k v m. m(k \<mapsto> v)" parametric update_parametric .

lift_definition delete :: "'a \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
  is "\<lambda>k m. m(k := None)" parametric delete_parametric .

lift_definition filter :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
  is "\<lambda>P m k. case m k of None \<Rightarrow> None | Some v \<Rightarrow> if P k v then Some v else None" .

lift_definition keys :: "('a, 'b) mapping \<Rightarrow> 'a set"
  is dom parametric dom_parametric .

lift_definition entries :: "('a, 'b) mapping \<Rightarrow> ('a \<times> 'b) set"
  is Map.graph parametric graph_parametric .

lift_definition tabulate :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping"
  is "\<lambda>ks f. (map_of (List.map (\<lambda>k. (k, f k)) ks))" parametric tabulate_parametric .

lift_definition bulkload :: "'a list \<Rightarrow> (nat, 'a) mapping"
  is "\<lambda>xs k. if k < length xs then Some (xs ! k) else None" parametric bulkload_parametric .

lift_definition map :: "('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('c, 'd) mapping"
  is "\<lambda>f g m. (map_option g \<circ> m \<circ> f)" parametric map_parametric .

lift_definition map_values :: "('c \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('c, 'a) mapping \<Rightarrow> ('c, 'b) mapping"
  is "\<lambda>f m x. map_option (f x) (m x)" .

lift_definition combine_with_key ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) mapping \<Rightarrow> ('a,'b) mapping \<Rightarrow> ('a,'b) mapping"
  is "\<lambda>f m1 m2 x. combine_options (f x) (m1 x) (m2 x)" parametric combine_with_key_parametric .

lift_definition combine ::
  "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) mapping \<Rightarrow> ('a,'b) mapping \<Rightarrow> ('a,'b) mapping"
  is "\<lambda>f m1 m2 x. combine_options f (m1 x) (m2 x)" parametric combine_parametric .

definition "All_mapping m P \<longleftrightarrow>
  (\<forall>x. case Mapping.lookup m x of None \<Rightarrow> True | Some y \<Rightarrow> P x y)"

declare [[code drop: map]]


subsection \<open>Functorial structure\<close>

functor map: map
  by (transfer, auto simp add: fun_eq_iff option.map_comp option.map_id)+


subsection \<open>Derived operations\<close>

definition ordered_keys :: "('a::linorder, 'b) mapping \<Rightarrow> 'a list"
  where "ordered_keys m = (if finite (keys m) then sorted_list_of_set (keys m) else [])"

definition ordered_entries :: "('a::linorder, 'b) mapping \<Rightarrow> ('a \<times> 'b) list"
  where "ordered_entries m = (if finite (entries m) then sorted_key_list_of_set fst (entries m)
                                                    else [])"

definition fold :: "('a::linorder \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> 'c \<Rightarrow> 'c"
  where "fold f m a = List.fold (case_prod f) (ordered_entries m) a"

definition is_empty :: "('a, 'b) mapping \<Rightarrow> bool"
  where "is_empty m \<longleftrightarrow> keys m = {}"

definition size :: "('a, 'b) mapping \<Rightarrow> nat"
  where "size m = (if finite (keys m) then card (keys m) else 0)"

definition replace :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
  where "replace k v m = (if k \<in> keys m then update k v m else m)"

definition default :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
  where "default k v m = (if k \<in> keys m then m else update k v m)"

text \<open>Manual derivation of transfer rule is non-trivial\<close>

lift_definition map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>k f m.
    (case m k of
      None \<Rightarrow> m
    | Some v \<Rightarrow> m (k \<mapsto> (f v)))" parametric map_entry_parametric .

lemma map_entry_code [code]:
  "map_entry k f m =
    (case lookup m k of
      None \<Rightarrow> m
    | Some v \<Rightarrow> update k (f v) m)"
  by transfer rule

definition map_default :: "'a \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
  where "map_default k v f m = map_entry k f (default k v m)"

definition of_alist :: "('k \<times> 'v) list \<Rightarrow> ('k, 'v) mapping"
  where "of_alist xs = foldr (\<lambda>(k, v) m. update k v m) xs empty"

instantiation mapping :: (type, type) equal
begin

definition "HOL.equal m1 m2 \<longleftrightarrow> (\<forall>k. lookup m1 k = lookup m2 k)"

instance
  apply standard
  unfolding equal_mapping_def
  apply transfer
  apply auto
  done

end

context includes lifting_syntax
begin

lemma [transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
    and [transfer_rule]: "bi_unique B"
  shows "(pcr_mapping A B ===> pcr_mapping A B ===> (=)) HOL.eq HOL.equal"
  unfolding equal by transfer_prover

lemma of_alist_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique R1"
  shows "(list_all2 (rel_prod R1 R2) ===> pcr_mapping R1 R2) map_of of_alist"
  unfolding of_alist_def [abs_def] map_of_foldr [abs_def] by transfer_prover

end


subsection \<open>Properties\<close>

lemma mapping_eqI: "(\<And>x. lookup m x = lookup m' x) \<Longrightarrow> m = m'"
  by transfer (simp add: fun_eq_iff)

lemma mapping_eqI':
  assumes "\<And>x. x \<in> Mapping.keys m \<Longrightarrow> Mapping.lookup_default d m x = Mapping.lookup_default d m' x"
    and "Mapping.keys m = Mapping.keys m'"
  shows "m = m'"
proof (intro mapping_eqI)
  show "Mapping.lookup m x = Mapping.lookup m' x" for x
  proof (cases "Mapping.lookup m x")
    case None
    then have "x \<notin> Mapping.keys m"
      by transfer (simp add: dom_def)
    then have "x \<notin> Mapping.keys m'"
      by (simp add: assms)
    then have "Mapping.lookup m' x = None"
      by transfer (simp add: dom_def)
    with None show ?thesis
      by simp
  next
    case (Some y)
    then have A: "x \<in> Mapping.keys m"
      by transfer (simp add: dom_def)
    then have "x \<in> Mapping.keys m'"
      by (simp add: assms)
    then have "\<exists>y'. Mapping.lookup m' x = Some y'"
      by transfer (simp add: dom_def)
    with Some assms(1)[OF A] show ?thesis
      by (auto simp add: lookup_default_def)
  qed
qed

lemma lookup_update[simp]: "lookup (update k v m) k = Some v"
  by transfer simp

lemma lookup_update_neq[simp]: "k \<noteq> k' \<Longrightarrow> lookup (update k v m) k' = lookup m k'"
  by transfer simp

lemma lookup_update': "lookup (update k v m) k' = (if k = k' then Some v else lookup m k')"
  by transfer simp

lemma lookup_empty[simp]: "lookup empty k = None"
  by transfer simp

lemma lookup_delete[simp]: "lookup (delete k m) k = None"
  by transfer simp

lemma lookup_delete_neq[simp]: "k \<noteq> k' \<Longrightarrow> lookup (delete k m) k' = lookup m k'"
  by transfer simp

lemma lookup_filter:
  "lookup (filter P m) k =
    (case lookup m k of
      None \<Rightarrow> None
    | Some v \<Rightarrow> if P k v then Some v else None)"
  by transfer simp_all

lemma lookup_map_values: "lookup (map_values f m) k = map_option (f k) (lookup m k)"
  by transfer simp_all

lemma lookup_default_empty: "lookup_default d empty k = d"
  by (simp add: lookup_default_def lookup_empty)

lemma lookup_default_update: "lookup_default d (update k v m) k = v"
  by (simp add: lookup_default_def)

lemma lookup_default_update_neq:
  "k \<noteq> k' \<Longrightarrow> lookup_default d (update k v m) k' = lookup_default d m k'"
  by (simp add: lookup_default_def)

lemma lookup_default_update':
  "lookup_default d (update k v m) k' = (if k = k' then v else lookup_default d m k')"
  by (auto simp: lookup_default_update lookup_default_update_neq)

lemma lookup_default_filter:
  "lookup_default d (filter P m) k =
     (if P k (lookup_default d m k) then lookup_default d m k else d)"
  by (simp add: lookup_default_def lookup_filter split: option.splits)

lemma lookup_default_map_values:
  "lookup_default (f k d) (map_values f m) k = f k (lookup_default d m k)"
  by (simp add: lookup_default_def lookup_map_values split: option.splits)

lemma lookup_combine_with_key:
  "Mapping.lookup (combine_with_key f m1 m2) x =
    combine_options (f x) (Mapping.lookup m1 x) (Mapping.lookup m2 x)"
  by transfer (auto split: option.splits)

lemma combine_altdef: "combine f m1 m2 = combine_with_key (\<lambda>_. f) m1 m2"
  by transfer' (rule refl)

lemma lookup_combine:
  "Mapping.lookup (combine f m1 m2) x =
     combine_options f (Mapping.lookup m1 x) (Mapping.lookup m2 x)"
  by transfer (auto split: option.splits)

lemma lookup_default_neutral_combine_with_key:
  assumes "\<And>x. f k d x = x" "\<And>x. f k x d = x"
  shows "Mapping.lookup_default d (combine_with_key f m1 m2) k =
    f k (Mapping.lookup_default d m1 k) (Mapping.lookup_default d m2 k)"
  by (auto simp: lookup_default_def lookup_combine_with_key assms split: option.splits)

lemma lookup_default_neutral_combine:
  assumes "\<And>x. f d x = x" "\<And>x. f x d = x"
  shows "Mapping.lookup_default d (combine f m1 m2) x =
    f (Mapping.lookup_default d m1 x) (Mapping.lookup_default d m2 x)"
  by (auto simp: lookup_default_def lookup_combine assms split: option.splits)

lemma lookup_map_entry: "lookup (map_entry x f m) x = map_option f (lookup m x)"
  by transfer (auto split: option.splits)

lemma lookup_map_entry_neq: "x \<noteq> y \<Longrightarrow> lookup (map_entry x f m) y = lookup m y"
  by transfer (auto split: option.splits)

lemma lookup_map_entry':
  "lookup (map_entry x f m) y =
     (if x = y then map_option f (lookup m y) else lookup m y)"
  by transfer (auto split: option.splits)

lemma lookup_default: "lookup (default x d m) x = Some (lookup_default d m x)"
  unfolding lookup_default_def default_def
  by transfer (auto split: option.splits)

lemma lookup_default_neq: "x \<noteq> y \<Longrightarrow> lookup (default x d m) y = lookup m y"
  unfolding lookup_default_def default_def
  by transfer (auto split: option.splits)

lemma lookup_default':
  "lookup (default x d m) y =
    (if x = y then Some (lookup_default d m x) else lookup m y)"
  unfolding lookup_default_def default_def
  by transfer (auto split: option.splits)

lemma lookup_map_default: "lookup (map_default x d f m) x = Some (f (lookup_default d m x))"
  unfolding lookup_default_def default_def
  by (simp add: map_default_def lookup_map_entry lookup_default lookup_default_def)

lemma lookup_map_default_neq: "x \<noteq> y \<Longrightarrow> lookup (map_default x d f m) y = lookup m y"
  unfolding lookup_default_def default_def
  by (simp add: map_default_def lookup_map_entry_neq lookup_default_neq)

lemma lookup_map_default':
  "lookup (map_default x d f m) y =
    (if x = y then Some (f (lookup_default d m x)) else lookup m y)"
  unfolding lookup_default_def default_def
  by (simp add: map_default_def lookup_map_entry' lookup_default' lookup_default_def)

lemma lookup_tabulate:
  assumes "distinct xs"
  shows "Mapping.lookup (Mapping.tabulate xs f) x = (if x \<in> set xs then Some (f x) else None)"
  using assms by transfer (auto simp: map_of_eq_None_iff o_def dest!: map_of_SomeD)

lemma lookup_of_alist: "lookup (of_alist xs) k = map_of xs k"
  by transfer simp_all

lemma keys_is_none_rep [code_unfold]: "k \<in> keys m \<longleftrightarrow> \<not> (Option.is_none (lookup m k))"
  by transfer (auto simp add: Option.is_none_def)

lemma update_update:
  "update k v (update k w m) = update k v m"
  "k \<noteq> l \<Longrightarrow> update k v (update l w m) = update l w (update k v m)"
  by (transfer; simp add: fun_upd_twist)+

lemma update_delete [simp]: "update k v (delete k m) = update k v m"
  by transfer simp

lemma delete_update:
  "delete k (update k v m) = delete k m"
  "k \<noteq> l \<Longrightarrow> delete k (update l v m) = update l v (delete k m)"
  by (transfer; simp add: fun_upd_twist)+

lemma delete_empty [simp]: "delete k empty = empty"
  by transfer simp

lemma Mapping_delete_if_notin_keys[simp]:
  "k \<notin> keys m \<Longrightarrow> delete k m = m"
  by transfer simp

lemma replace_update:
  "k \<notin> keys m \<Longrightarrow> replace k v m = m"
  "k \<in> keys m \<Longrightarrow> replace k v m = update k v m"
  by (transfer; auto simp add: replace_def fun_upd_twist)+

lemma map_values_update: "map_values f (update k v m) = update k (f k v) (map_values f m)"
  by transfer (simp_all add: fun_eq_iff)

lemma size_mono: "finite (keys m') \<Longrightarrow> keys m \<subseteq> keys m' \<Longrightarrow> size m \<le> size m'"
  unfolding size_def by (auto intro: card_mono)

lemma size_empty [simp]: "size empty = 0"
  unfolding size_def by transfer simp

lemma size_update:
  "finite (keys m) \<Longrightarrow> size (update k v m) =
    (if k \<in> keys m then size m else Suc (size m))"
  unfolding size_def by transfer (auto simp add: insert_dom)

lemma size_delete: "size (delete k m) = (if k \<in> keys m then size m - 1 else size m)"
  unfolding size_def by transfer simp

lemma size_tabulate [simp]: "size (tabulate ks f) = length (remdups ks)"
  unfolding size_def by transfer (auto simp add: map_of_map_restrict card_set comp_def)

lemma keys_filter: "keys (filter P m) \<subseteq> keys m"
  by transfer (auto split: option.splits)

lemma size_filter: "finite (keys m) \<Longrightarrow> size (filter P m) \<le> size m"
  by (intro size_mono keys_filter)

lemma bulkload_tabulate: "bulkload xs = tabulate [0..<length xs] (nth xs)"
  by transfer (auto simp add: map_of_map_restrict)

lemma is_empty_empty [simp]: "is_empty empty"
  unfolding is_empty_def by transfer simp

lemma is_empty_update [simp]: "\<not> is_empty (update k v m)"
  unfolding is_empty_def by transfer simp

lemma is_empty_delete: "is_empty (delete k m) \<longleftrightarrow> is_empty m \<or> keys m = {k}"
  unfolding is_empty_def by transfer (auto simp del: dom_eq_empty_conv)

lemma is_empty_replace [simp]: "is_empty (replace k v m) \<longleftrightarrow> is_empty m"
  unfolding is_empty_def replace_def by transfer auto

lemma is_empty_default [simp]: "\<not> is_empty (default k v m)"
  unfolding is_empty_def default_def by transfer auto

lemma is_empty_map_entry [simp]: "is_empty (map_entry k f m) \<longleftrightarrow> is_empty m"
  unfolding is_empty_def by transfer (auto split: option.split)

lemma is_empty_map_values [simp]: "is_empty (map_values f m) \<longleftrightarrow> is_empty m"
  unfolding is_empty_def by transfer (auto simp: fun_eq_iff)

lemma is_empty_map_default [simp]: "\<not> is_empty (map_default k v f m)"
  by (simp add: map_default_def)

lemma keys_dom_lookup: "keys m = dom (Mapping.lookup m)"
  by transfer rule

lemma keys_empty [simp]: "keys empty = {}"
  by transfer (fact dom_empty)

lemma in_keysD: "k \<in> keys m \<Longrightarrow> \<exists>v. lookup m k = Some v"
  by transfer (fact domD)

lemma keys_update [simp]: "keys (update k v m) = insert k (keys m)"
  by transfer simp

lemma keys_delete [simp]: "keys (delete k m) = keys m - {k}"
  by transfer simp

lemma keys_replace [simp]: "keys (replace k v m) = keys m"
  unfolding replace_def by transfer (simp add: insert_absorb)

lemma keys_default [simp]: "keys (default k v m) = insert k (keys m)"
  unfolding default_def by transfer (simp add: insert_absorb)

lemma keys_map_entry [simp]: "keys (map_entry k f m) = keys m"
  by transfer (auto split: option.split)

lemma keys_map_default [simp]: "keys (map_default k v f m) = insert k (keys m)"
  by (simp add: map_default_def)

lemma keys_map_values [simp]: "keys (map_values f m) = keys m"
  by transfer (simp_all add: dom_def)

lemma keys_combine_with_key [simp]:
  "Mapping.keys (combine_with_key f m1 m2) = Mapping.keys m1 \<union> Mapping.keys m2"
  by transfer (auto simp: dom_def combine_options_def split: option.splits)

lemma keys_combine [simp]: "Mapping.keys (combine f m1 m2) = Mapping.keys m1 \<union> Mapping.keys m2"
  by (simp add: combine_altdef)

lemma keys_tabulate [simp]: "keys (tabulate ks f) = set ks"
  by transfer (simp add: map_of_map_restrict o_def)

lemma keys_of_alist [simp]: "keys (of_alist xs) = set (List.map fst xs)"
  by transfer (simp_all add: dom_map_of_conv_image_fst)

lemma keys_bulkload [simp]: "keys (bulkload xs) = {0..<length xs}"
  by (simp add: bulkload_tabulate)

lemma finite_keys_update[simp]:
  "finite (keys (update k v m)) = finite (keys m)"
  by transfer simp

lemma set_ordered_keys[simp]:
  "finite (Mapping.keys m) \<Longrightarrow> set (Mapping.ordered_keys m) = Mapping.keys m"
  unfolding ordered_keys_def by transfer auto

lemma distinct_ordered_keys [simp]: "distinct (ordered_keys m)"
  by (simp add: ordered_keys_def)

lemma ordered_keys_infinite [simp]: "\<not> finite (keys m) \<Longrightarrow> ordered_keys m = []"
  by (simp add: ordered_keys_def)

lemma ordered_keys_empty [simp]: "ordered_keys empty = []"
  by (simp add: ordered_keys_def)

lemma sorted_ordered_keys[simp]: "sorted (ordered_keys m)"
  unfolding ordered_keys_def by simp

lemma ordered_keys_update [simp]:
  "k \<in> keys m \<Longrightarrow> ordered_keys (update k v m) = ordered_keys m"
  "finite (keys m) \<Longrightarrow> k \<notin> keys m \<Longrightarrow>
    ordered_keys (update k v m) = insort k (ordered_keys m)"
  by (simp_all add: ordered_keys_def)
     (auto simp only: sorted_list_of_set_insert_remove[symmetric] insert_absorb)

lemma ordered_keys_delete [simp]: "ordered_keys (delete k m) = remove1 k (ordered_keys m)"
proof (cases "finite (keys m)")
  case False
  then show ?thesis by simp
next
  case fin: True
  show ?thesis
  proof (cases "k \<in> keys m")
    case False
    with fin have "k \<notin> set (sorted_list_of_set (keys m))"
      by simp
    with False show ?thesis
      by (simp add: ordered_keys_def remove1_idem)
  next
    case True
    with fin show ?thesis
      by (simp add: ordered_keys_def sorted_list_of_set_remove)
  qed
qed

lemma ordered_keys_replace [simp]: "ordered_keys (replace k v m) = ordered_keys m"
  by (simp add: replace_def)

lemma ordered_keys_default [simp]:
  "k \<in> keys m \<Longrightarrow> ordered_keys (default k v m) = ordered_keys m"
  "finite (keys m) \<Longrightarrow> k \<notin> keys m \<Longrightarrow> ordered_keys (default k v m) = insort k (ordered_keys m)"
  by (simp_all add: default_def)

lemma ordered_keys_map_entry [simp]: "ordered_keys (map_entry k f m) = ordered_keys m"
  by (simp add: ordered_keys_def)

lemma ordered_keys_map_default [simp]:
  "k \<in> keys m \<Longrightarrow> ordered_keys (map_default k v f m) = ordered_keys m"
  "finite (keys m) \<Longrightarrow> k \<notin> keys m \<Longrightarrow> ordered_keys (map_default k v f m) = insort k (ordered_keys m)"
  by (simp_all add: map_default_def)

lemma ordered_keys_tabulate [simp]: "ordered_keys (tabulate ks f) = sort (remdups ks)"
  by (simp add: ordered_keys_def sorted_list_of_set_sort_remdups)

lemma ordered_keys_bulkload [simp]: "ordered_keys (bulkload ks) = [0..<length ks]"
  by (simp add: ordered_keys_def)

lemma tabulate_fold: "tabulate xs f = List.fold (\<lambda>k m. update k (f k) m) xs empty"
proof transfer
  fix f :: "'a \<Rightarrow> 'b" and xs
  have "map_of (List.map (\<lambda>k. (k, f k)) xs) = foldr (\<lambda>k m. m(k \<mapsto> f k)) xs Map.empty"
    by (simp add: foldr_map comp_def map_of_foldr)
  also have "foldr (\<lambda>k m. m(k \<mapsto> f k)) xs = List.fold (\<lambda>k m. m(k \<mapsto> f k)) xs"
    by (rule foldr_fold) (simp add: fun_eq_iff)
  ultimately show "map_of (List.map (\<lambda>k. (k, f k)) xs) = List.fold (\<lambda>k m. m(k \<mapsto> f k)) xs Map.empty"
    by simp
qed

lemma All_mapping_mono:
  "(\<And>k v. k \<in> keys m \<Longrightarrow> P k v \<Longrightarrow> Q k v) \<Longrightarrow> All_mapping m P \<Longrightarrow> All_mapping m Q"
  unfolding All_mapping_def by transfer (auto simp: All_mapping_def dom_def split: option.splits)

lemma All_mapping_empty [simp]: "All_mapping Mapping.empty P"
  by (auto simp: All_mapping_def lookup_empty)

lemma All_mapping_update_iff:
  "All_mapping (Mapping.update k v m) P \<longleftrightarrow> P k v \<and> All_mapping m (\<lambda>k' v'. k = k' \<or> P k' v')"
  unfolding All_mapping_def
proof safe
  assume "\<forall>x. case Mapping.lookup (Mapping.update k v m) x of None \<Rightarrow> True | Some y \<Rightarrow> P x y"
  then have *: "case Mapping.lookup (Mapping.update k v m) x of None \<Rightarrow> True | Some y \<Rightarrow> P x y" for x
    by blast
  from *[of k] show "P k v"
    by (simp add: lookup_update)
  show "case Mapping.lookup m x of None \<Rightarrow> True | Some v' \<Rightarrow> k = x \<or> P x v'" for x
    using *[of x] by (auto simp add: lookup_update' split: if_splits option.splits)
next
  assume "P k v"
  assume "\<forall>x. case Mapping.lookup m x of None \<Rightarrow> True | Some v' \<Rightarrow> k = x \<or> P x v'"
  then have A: "case Mapping.lookup m x of None \<Rightarrow> True | Some v' \<Rightarrow> k = x \<or> P x v'" for x
    by blast
  show "case Mapping.lookup (Mapping.update k v m) x of None \<Rightarrow> True | Some xa \<Rightarrow> P x xa" for x
    using \<open>P k v\<close> A[of x] by (auto simp: lookup_update' split: option.splits)
qed

lemma All_mapping_update:
  "P k v \<Longrightarrow> All_mapping m (\<lambda>k' v'. k = k' \<or> P k' v') \<Longrightarrow> All_mapping (Mapping.update k v m) P"
  by (simp add: All_mapping_update_iff)

lemma All_mapping_filter_iff: "All_mapping (filter P m) Q \<longleftrightarrow> All_mapping m (\<lambda>k v. P k v \<longrightarrow> Q k v)"
  by (auto simp: All_mapping_def lookup_filter split: option.splits)

lemma All_mapping_filter: "All_mapping m Q \<Longrightarrow> All_mapping (filter P m) Q"
  by (auto simp: All_mapping_filter_iff intro: All_mapping_mono)

lemma All_mapping_map_values: "All_mapping (map_values f m) P \<longleftrightarrow> All_mapping m (\<lambda>k v. P k (f k v))"
  by (auto simp: All_mapping_def lookup_map_values split: option.splits)

lemma All_mapping_tabulate: "(\<forall>x\<in>set xs. P x (f x)) \<Longrightarrow> All_mapping (Mapping.tabulate xs f) P"
  unfolding All_mapping_def
  apply (intro allI)
  apply transfer
  apply (auto split: option.split dest!: map_of_SomeD)
  done

lemma All_mapping_alist:
  "(\<And>k v. (k, v) \<in> set xs \<Longrightarrow> P k v) \<Longrightarrow> All_mapping (Mapping.of_alist xs) P"
  by (auto simp: All_mapping_def lookup_of_alist dest!: map_of_SomeD split: option.splits)

lemma combine_empty [simp]: "combine f Mapping.empty y = y" "combine f y Mapping.empty = y"
  by (transfer; force)+

lemma (in abel_semigroup) comm_monoid_set_combine: "comm_monoid_set (combine f) Mapping.empty"
  by standard (transfer fixing: f, simp add: combine_options_ac[of f] ac_simps)+

locale combine_mapping_abel_semigroup = abel_semigroup
begin

sublocale combine: comm_monoid_set "combine f" Mapping.empty
  by (rule comm_monoid_set_combine)

lemma fold_combine_code:
  "combine.F g (set xs) = foldr (\<lambda>x. combine f (g x)) (remdups xs) Mapping.empty"
proof -
  have "combine.F g (set xs) = foldr (\<lambda>x. combine f (g x)) xs Mapping.empty"
    if "distinct xs" for xs
    using that by (induction xs) simp_all
  from this[of "remdups xs"] show ?thesis by simp
qed

lemma keys_fold_combine: "finite A \<Longrightarrow> Mapping.keys (combine.F g A) = (\<Union>x\<in>A. Mapping.keys (g x))"
  by (induct A rule: finite_induct) simp_all

end

subsubsection \<open>@{term [source] entries}, @{term [source] ordered_entries},
               and @{term [source] fold}\<close>

context linorder
begin

sublocale folding_Map_graph: folding_insort_key "(\<le>)" "(<)" "Map.graph m" fst for m
  by unfold_locales (fact inj_on_fst_graph)

end

lemma sorted_fst_list_of_set_insort_Map_graph[simp]:
  assumes "finite (dom m)" "fst x \<notin> dom m"
  shows "sorted_key_list_of_set fst (insert x (Map.graph m))
       = insort_key fst x (sorted_key_list_of_set fst (Map.graph m))"
proof(cases x)
  case (Pair k v)
  with \<open>fst x \<notin> dom m\<close> have "Map.graph m \<subseteq> Map.graph (m(k \<mapsto> v))"
    by(auto simp: graph_def)
  moreover from Pair \<open>fst x \<notin> dom m\<close> have "(k, v) \<notin> Map.graph m"
    using graph_domD by fastforce
  ultimately show ?thesis
    using Pair assms folding_Map_graph.sorted_key_list_of_set_insert[where ?m="m(k \<mapsto> v)"]
    by auto
qed

lemma sorted_fst_list_of_set_insort_insert_Map_graph[simp]:
  assumes "finite (dom m)" "fst x \<notin> dom m"
  shows "sorted_key_list_of_set fst (insert x (Map.graph m))
       = insort_insert_key fst x (sorted_key_list_of_set fst (Map.graph m))"
proof(cases x)
  case (Pair k v)
  with \<open>fst x \<notin> dom m\<close> have "Map.graph m \<subseteq> Map.graph (m(k \<mapsto> v))"
    by(auto simp: graph_def)    
  with assms Pair show ?thesis
    unfolding sorted_fst_list_of_set_insort_Map_graph[OF assms] insort_insert_key_def
    using folding_Map_graph.set_sorted_key_list_of_set in_graphD by (fastforce split: if_splits)
qed

lemma linorder_finite_Map_induct[consumes 1, case_names empty update]:
  fixes m :: "'a::linorder \<rightharpoonup> 'b"
  assumes "finite (dom m)"
  assumes "P Map.empty"
  assumes "\<And>k v m. \<lbrakk> finite (dom m); k \<notin> dom m; (\<And>k'. k' \<in> dom m \<Longrightarrow> k' \<le> k); P m \<rbrakk>
                    \<Longrightarrow> P (m(k \<mapsto> v))"
  shows "P m"
proof -
  let ?key_list = "\<lambda>m. sorted_list_of_set (dom m)"
  from assms(1,2) show ?thesis
  proof(induction "length (?key_list m)" arbitrary: m)
    case 0
    then have "sorted_list_of_set (dom m) = []"
      by auto
    with \<open>finite (dom m)\<close> have "m = Map.empty"
       by auto
     with \<open>P Map.empty\<close> show ?case by simp
  next
    case (Suc n)
    then obtain x xs where x_xs: "sorted_list_of_set (dom m) = xs @ [x]"
      by (metis append_butlast_last_id length_greater_0_conv zero_less_Suc)
    have "sorted_list_of_set (dom (m(x := None))) = xs"
    proof -
      have "distinct (xs @ [x])"
        by (metis sorted_list_of_set.distinct_sorted_key_list_of_set x_xs)
      then have "remove1 x (xs @ [x]) = xs"
        by (simp add: remove1_append)
      with \<open>finite (dom m)\<close> x_xs show ?thesis
        by (simp add: sorted_list_of_set_remove)
    qed
    moreover have "k \<le> x" if "k \<in> dom (m(x := None))" for k
    proof -
      from x_xs have "sorted (xs @ [x])"
        by (metis sorted_list_of_set.sorted_sorted_key_list_of_set)
      moreover from \<open>k \<in> dom (m(x := None))\<close> have "k \<in> set xs"
        using \<open>finite (dom m)\<close> \<open>sorted_list_of_set (dom (m(x := None))) = xs\<close>
        by auto
      ultimately show "k \<le> x"
        by (simp add: sorted_append)
    qed     
    moreover from \<open>finite (dom m)\<close> have "finite (dom (m(x := None)))" "x \<notin> dom (m(x := None))"
      by simp_all
    moreover have "P (m(x := None))"
      using Suc \<open>sorted_list_of_set (dom (m(x := None))) = xs\<close> x_xs by auto
    ultimately show ?case
      using assms(3)[where ?m="m(x := None)"] by (metis fun_upd_triv fun_upd_upd not_Some_eq)
  qed
qed

lemma delete_insort_fst[simp]: "AList.delete k (insort_key fst (k, v) xs) = AList.delete k xs"
  by (induction xs) simp_all

lemma insort_fst_delete: "\<lbrakk> fst x \<noteq> k2; sorted (List.map fst xs) \<rbrakk>
  \<Longrightarrow> insort_key fst x (AList.delete k2 xs) = AList.delete k2 (insort_key fst x xs)"
  by (induction xs) (fastforce simp add: insort_is_Cons order_trans)+

lemma sorted_fst_list_of_set_Map_graph_fun_upd_None[simp]:
  "sorted_key_list_of_set fst (Map.graph (m(k := None)))
   = AList.delete k (sorted_key_list_of_set fst (Map.graph m))"
proof(cases "finite (Map.graph m)")
  assume "finite (Map.graph m)"
  from this[unfolded finite_graph_iff_finite_dom] show ?thesis
  proof(induction rule: finite_Map_induct)
    let ?list_of="sorted_key_list_of_set fst"
    case (update k2 v2 m)
    note [simp] = \<open>k2 \<notin> dom m\<close> \<open>finite (dom m)\<close>

    have right_eq: "AList.delete k (?list_of (Map.graph (m(k2 \<mapsto> v2))))
      = AList.delete k (insort_key fst (k2, v2) (?list_of (Map.graph m)))"
      by simp

    show ?case
    proof(cases "k = k2")
      case True
      then have "?list_of (Map.graph ((m(k2 \<mapsto> v2))(k := None)))
        = AList.delete k (insort_key fst (k2, v2) (?list_of (Map.graph m)))"
        using fst_graph_eq_dom update.IH by auto
      then show ?thesis
        using right_eq by metis
    next
      case False
      then have "AList.delete k (insort_key fst (k2, v2) (?list_of (Map.graph m)))
        = insort_key fst (k2, v2) (?list_of (Map.graph (m(k := None))))"
        by (auto simp add: insort_fst_delete update.IH
                      folding_Map_graph.sorted_sorted_key_list_of_set[OF subset_refl])
      also have "\<dots> = ?list_of (insert (k2, v2) (Map.graph (m(k := None))))"
        by auto
      also from False \<open>k2 \<notin> dom m\<close> have "\<dots> = ?list_of (Map.graph ((m(k2 \<mapsto> v2))(k := None)))"
        by (metis graph_map_upd domIff fun_upd_triv fun_upd_twist)
      finally show ?thesis using right_eq by metis
    qed
  qed simp
qed simp

lemma entries_empty[simp]: "entries empty = {}"
  by transfer (fact graph_empty)

lemma entries_lookup: "entries m = Map.graph (lookup m)"
  by transfer rule

lemma in_entriesI: "lookup m k = Some v \<Longrightarrow> (k, v) \<in> entries m"
  by transfer (fact in_graphI)

lemma in_entriesD: "(k, v) \<in> entries m \<Longrightarrow> lookup m k = Some v"
  by transfer (fact in_graphD)

lemma fst_image_entries_eq_keys[simp]: "fst ` Mapping.entries m = Mapping.keys m"
  by transfer (fact fst_graph_eq_dom)

lemma finite_entries_iff_finite_keys[simp]:
  "finite (entries m) = finite (keys m)"
  by transfer (fact finite_graph_iff_finite_dom)

lemma entries_update:
  "entries (update k v m) = insert (k, v) (entries (delete k m))"
  by transfer (fact graph_map_upd)

lemma entries_delete:
  "entries (delete k m) = {e \<in> entries m. fst e \<noteq> k}"
  by transfer (fact graph_fun_upd_None)

lemma entries_of_alist[simp]:
  "distinct (List.map fst xs) \<Longrightarrow> entries (of_alist xs) = set xs"
  by transfer (fact graph_map_of_if_distinct_dom)

lemma entries_keysD:
  "x \<in> entries m \<Longrightarrow> fst x \<in> keys m"
  by transfer (fact graph_domD)

lemma set_ordered_entries[simp]:
  "finite (keys m) \<Longrightarrow> set (ordered_entries m) = entries m"
  unfolding ordered_entries_def
  by transfer (auto simp: folding_Map_graph.set_sorted_key_list_of_set[OF subset_refl])

lemma distinct_ordered_entries[simp]: "distinct (List.map fst (ordered_entries m))"
  unfolding ordered_entries_def
  by transfer (simp add: folding_Map_graph.distinct_sorted_key_list_of_set[OF subset_refl])

lemma sorted_ordered_entries[simp]: "sorted (List.map fst (ordered_entries m))"
  unfolding ordered_entries_def
  by transfer (auto intro: folding_Map_graph.sorted_sorted_key_list_of_set)

lemma ordered_entries_infinite[simp]:
  "\<not> finite (Mapping.keys m) \<Longrightarrow> ordered_entries m = []"
  by (simp add: ordered_entries_def)

lemma ordered_entries_empty[simp]: "ordered_entries empty = []"
  by (simp add: ordered_entries_def)

lemma ordered_entries_update[simp]:
  assumes "finite (keys m)"
  shows "ordered_entries (update k v m)
   = insort_insert_key fst (k, v) (AList.delete k (ordered_entries m))"
proof -
  let ?list_of="sorted_key_list_of_set fst" and ?insort="insort_insert_key fst"

  have *: "?list_of (insert (k, v) (Map.graph (m(k := None))))
    = ?insort (k, v) (AList.delete k (?list_of (Map.graph m)))" if "finite (dom m)" for m
  proof -
    from \<open>finite (dom m)\<close> have "?list_of (insert (k, v) (Map.graph (m(k := None))))
      = ?insort (k, v) (?list_of (Map.graph (m(k := None))))"
      by (intro sorted_fst_list_of_set_insort_insert_Map_graph) (simp_all add: subset_insertI) 
    then show ?thesis by simp
  qed
  from assms show ?thesis
    unfolding ordered_entries_def
    apply (transfer fixing: k v) using "*" by auto
qed

lemma ordered_entries_delete[simp]:
  "ordered_entries (delete k m) = AList.delete k (ordered_entries m)"
  unfolding ordered_entries_def by transfer auto

lemma map_fst_ordered_entries[simp]:
  "List.map fst (ordered_entries m) = ordered_keys m"
proof(cases "finite (Mapping.keys m)")
  case True
  then have "set (List.map fst (Mapping.ordered_entries m)) = set (Mapping.ordered_keys m)"
    unfolding ordered_entries_def ordered_keys_def
    by (transfer) (simp add: folding_Map_graph.set_sorted_key_list_of_set[OF subset_refl] fst_graph_eq_dom)
  with True show "List.map fst (Mapping.ordered_entries m) = Mapping.ordered_keys m"
    by (metis distinct_ordered_entries ordered_keys_def sorted_list_of_set.idem_if_sorted_distinct          
              sorted_list_of_set.set_sorted_key_list_of_set sorted_ordered_entries)
next
  case False
  then show ?thesis
    unfolding ordered_entries_def ordered_keys_def by simp
qed

lemma fold_empty[simp]: "fold f empty a = a"
  unfolding fold_def by simp

lemma insort_key_is_snoc_if_sorted_and_distinct:
  assumes "sorted (List.map f xs)" "f y \<notin> f ` set xs" "\<forall>x \<in> set xs. f x \<le> f y"
  shows "insort_key f y xs = xs @ [y]"
  using assms by (induction xs) (auto dest!: insort_is_Cons)

lemma fold_update:
  assumes "finite (keys m)"
  assumes "k \<notin> keys m" "\<And>k'. k' \<in> keys m \<Longrightarrow> k' \<le> k"
  shows "fold f (update k v m) a = f k v (fold f m a)"
proof -
  from assms have k_notin_entries: "k \<notin> fst ` set (ordered_entries m)"
    using entries_keysD by fastforce
  with assms have "ordered_entries (update k v m)
    = insort_insert_key fst (k, v) (ordered_entries m)"
    by simp
  also from k_notin_entries have "\<dots> = ordered_entries m @ [(k, v)]"
  proof -
    from assms have "\<forall>x \<in> set (ordered_entries m). fst x \<le> fst (k, v)"
      unfolding ordered_entries_def
      by transfer (fastforce simp: folding_Map_graph.set_sorted_key_list_of_set[OF order_refl]
                             dest: graph_domD)
    from insort_key_is_snoc_if_sorted_and_distinct[OF _ _ this] k_notin_entries \<open>finite (keys m)\<close>
    show ?thesis
      using sorted_ordered_keys
      unfolding insort_insert_key_def by auto
  qed
  finally show ?thesis unfolding fold_def by simp
qed

lemma linorder_finite_Mapping_induct[consumes 1, case_names empty update]:
  fixes m :: "('a::linorder, 'b) mapping"
  assumes "finite (keys m)"
  assumes "P empty"
  assumes "\<And>k v m.
    \<lbrakk> finite (keys m); k \<notin> keys m; (\<And>k'. k' \<in> keys m \<Longrightarrow> k' \<le> k); P m \<rbrakk>
    \<Longrightarrow> P (update k v m)"
  shows "P m"
  using assms by transfer (simp add: linorder_finite_Map_induct)


subsection \<open>Code generator setup\<close>

hide_const (open) empty is_empty rep lookup lookup_default filter update delete ordered_keys
  keys size replace default map_entry map_default tabulate bulkload map map_values combine of_alist
  entries ordered_entries fold

end
