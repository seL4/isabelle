theory Lift_BNF
imports Main
begin

typedef 'a nonempty_list = "{xs :: 'a list. xs \<noteq> []}"
  by blast

lift_bnf (no_warn_wits) (neset: 'a) nonempty_list
  for map: nemap rel: nerel
  by simp_all

typedef ('a :: finite, 'b) fin_nonempty_list = "{(xs :: 'a set, ys :: 'b list). ys \<noteq> []}"
  by blast

lift_bnf (dead 'a :: finite, 'b) fin_nonempty_list
  by auto

datatype 'a tree = Leaf | Node 'a "'a tree nonempty_list"

record 'a point =
  xCoord :: 'a
  yCoord :: 'a

copy_bnf ('a, 's) point_ext

typedef 'a it = "UNIV :: 'a set"
  by blast

copy_bnf (plugins del: size) 'a it

typedef ('a, 'b) T_prod = "UNIV :: ('a \<times> 'b) set"
  by blast

copy_bnf ('a, 'b) T_prod

typedef ('a, 'b, 'c) T_func = "UNIV :: ('a \<Rightarrow> 'b * 'c) set"
  by blast

copy_bnf ('a, 'b, 'c) T_func

typedef ('a, 'b) sum_copy = "UNIV :: ('a + 'b) set"
  by blast

copy_bnf ('a, 'b) sum_copy

typedef ('a, 'b) T_sum = "{Inl x | x. True} :: ('a + 'b) set"
  by blast

lift_bnf (no_warn_wits) ('a, 'b) T_sum [wits: "Inl :: 'a \<Rightarrow> 'a + 'b"]
  by (auto simp: map_sum_def sum_set_defs split: sum.splits)

typedef ('key, 'value) alist = "{xs :: ('key \<times> 'value) list. (distinct \<circ> map fst) xs}"
  morphisms impl_of Alist
proof
  show "[] \<in> {xs. (distinct o map fst) xs}"
    by simp
qed

lift_bnf (dead 'k, 'v) alist [wits: "Nil :: ('k \<times> 'v) list"]
  by simp_all

typedef 'a myopt = "{X :: 'a set. finite X \<and> card X \<le> 1}" by (rule exI[of _ "{}"]) auto
lemma myopt_type_def: "type_definition
  (\<lambda>X. if card (Rep_myopt X) = 1 then Some (the_elem (Rep_myopt X)) else None)
  (\<lambda>x. Abs_myopt (case x of Some x \<Rightarrow> {x} | _ \<Rightarrow> {}))
  (UNIV :: 'a option set)"
  apply unfold_locales
    apply (auto simp: Abs_myopt_inverse dest!: card_eq_SucD split: option.splits)
   apply (metis Rep_myopt_inverse)
  apply (metis One_nat_def Rep_myopt Rep_myopt_inverse Suc_le_mono card_0_eq le0 le_antisym mem_Collect_eq nat.exhaust)
  done

copy_bnf 'a myopt via myopt_type_def

typedef ('k, 'v) fmap = "{M :: ('k \<rightharpoonup> 'v). finite (dom M)}"
  by (rule exI[of _ Map.empty]) simp_all

lift_bnf (dead 'k, 'v) fmap [wits: "Map.empty :: 'k \<Rightarrow> 'v option"]
  by auto

end
