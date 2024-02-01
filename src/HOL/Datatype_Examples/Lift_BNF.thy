(*  Title:      HOL/Datatype_Examples/Lift_BNF.thy
    Author:     Dmitriy Traytel, ETH Zürich
    Copyright   2015

Demonstration of the "lift_bnf" command.
*)

section \<open>Demonstration of the \textbf{lift_bnf} Command\<close>

theory Lift_BNF
imports Main
begin

subsection \<open>Lifting \textbf{typedef}s\<close>

typedef 'a nonempty_list = "{xs :: 'a list. xs \<noteq> []}"
  by blast
setup_lifting type_definition_nonempty_list

lift_bnf (no_warn_wits) (neset: 'a) nonempty_list
  for map: nemap rel: nerel
  by auto

typedef ('a :: finite, 'b) fin_nonempty_list = "{(xs :: 'a set, ys :: 'b list). ys \<noteq> []}"
  by blast
setup_lifting type_definition_fin_nonempty_list

lift_bnf (no_warn_wits) (dead 'a :: finite, 'b) fin_nonempty_list
  [wits: "\<lambda>b. ({} :: 'a :: finite set, [b :: 'b])"]
  by auto

datatype 'a tree = Leaf | Node 'a "'a tree nonempty_list"

record 'a point =
  xCoord :: 'a
  yCoord :: 'a


copy_bnf (no_warn_transfer) ('a, 's) point_ext

typedef 'a it = "UNIV :: 'a set"
  by blast

setup_lifting type_definition_it

copy_bnf (plugins del: size) 'a it

typedef ('a, 'b) T_prod = "UNIV :: ('a \<times> 'b) set"
  by blast

setup_lifting type_definition_T_prod

copy_bnf ('a, 'b) T_prod

typedef ('a, 'b, 'c) T_func = "UNIV :: ('a \<Rightarrow> 'b * 'c) set"
  by blast

setup_lifting type_definition_T_func

copy_bnf ('a, 'b, 'c) T_func

typedef ('a, 'b) sum_copy = "UNIV :: ('a + 'b) set"
  by blast

setup_lifting type_definition_sum_copy

copy_bnf ('a, 'b) sum_copy

typedef ('a, 'b) T_sum = "{Inl x | x. True} :: ('a + 'b) set"
  by blast

lift_bnf (no_warn_wits, no_warn_transfer) ('a, 'b) T_sum [wits: "Inl :: 'a \<Rightarrow> 'a + 'b"]
  by (force simp: map_sum_def sum_set_defs split: sum.splits)+

typedef ('key, 'value) alist = "{xs :: ('key \<times> 'value) list. (distinct \<circ> map fst) xs}"
  morphisms impl_of Alist
proof
  show "[] \<in> {xs. (distinct o map fst) xs}"
    by simp
qed

setup_lifting type_definition_alist

lift_bnf (dead 'k, 'v) alist [wits: "Nil :: ('k \<times> 'v) list"]
  by auto

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

copy_bnf (no_warn_transfer) 'a myopt via myopt_type_def

typedef ('k, 'v) fmap = "{M :: ('k \<rightharpoonup> 'v). finite (dom M)}"
  by (rule exI[of _ Map.empty]) simp_all
setup_lifting type_definition_fmap

lift_bnf (dead 'k, 'v) fmap [wits: "Map.empty :: 'k \<Rightarrow> 'v option"]
  by auto

class len = fixes len :: "'a \<Rightarrow> nat"
typedef (overloaded) ('a, 'b :: len) vec = "{xs :: 'a list. length xs = len (undefined :: 'b)}"
  by (auto intro!: exI[of _ "replicate _ _"])
setup_lifting type_definition_vec
lift_bnf (no_warn_wits) ('a, dead 'b :: len) vec
  by auto

typedef ('a, 'b) tuple_dead = "UNIV :: ('a \<times> 'b) set" ..
typedef ('a, 'b) tuple_dead1 = "UNIV :: ('a \<times> 'b) set" ..
typedef ('a, 'b) tuple_dead2 = "UNIV :: ('a \<times> 'b) set" ..
typedef ('a, 'b, 'c) triple_dead = "UNIV :: ('a \<times> 'b \<times> 'c) set" ..
typedef ('a, 'b, 'c) triple_dead1 = "UNIV :: ('a \<times> 'b \<times> 'c) set" ..
typedef ('a, 'b, 'c) triple_dead2 = "UNIV :: ('a \<times> 'b \<times> 'c) set" ..
typedef ('a, 'b, 'c) triple_dead3 = "UNIV :: ('a \<times> 'b \<times> 'c) set" ..
typedef ('a, 'b, 'c) triple_dead12 = "UNIV :: ('a \<times> 'b \<times> 'c) set" ..
typedef ('a, 'b, 'c) triple_dead13 = "UNIV :: ('a \<times> 'b \<times> 'c) set" ..
typedef ('a, 'b, 'c) triple_dead23 = "UNIV :: ('a \<times> 'b \<times> 'c) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead =    "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead1 =   "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead2 =   "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead3 =   "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead4 =   "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead12 =  "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead13 =  "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead14 =  "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead23 =  "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead24 =  "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead34 =  "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead123 = "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead124 = "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead134 = "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
typedef ('a, 'b, 'c, 'd) quadruple_dead234 = "UNIV :: ('a \<times> 'b \<times> 'c \<times> 'd) set" ..
setup_lifting type_definition_tuple_dead
setup_lifting type_definition_tuple_dead1
setup_lifting type_definition_tuple_dead2
setup_lifting type_definition_triple_dead
setup_lifting type_definition_triple_dead1
setup_lifting type_definition_triple_dead2
setup_lifting type_definition_triple_dead3
setup_lifting type_definition_triple_dead12
setup_lifting type_definition_triple_dead13
setup_lifting type_definition_triple_dead23
setup_lifting type_definition_quadruple_dead
setup_lifting type_definition_quadruple_dead1
setup_lifting type_definition_quadruple_dead2
setup_lifting type_definition_quadruple_dead3
setup_lifting type_definition_quadruple_dead4
setup_lifting type_definition_quadruple_dead12
setup_lifting type_definition_quadruple_dead13
setup_lifting type_definition_quadruple_dead14
setup_lifting type_definition_quadruple_dead23
setup_lifting type_definition_quadruple_dead24
setup_lifting type_definition_quadruple_dead34
setup_lifting type_definition_quadruple_dead123
setup_lifting type_definition_quadruple_dead124
setup_lifting type_definition_quadruple_dead134
setup_lifting type_definition_quadruple_dead234

lift_bnf (no_warn_wits) (     'a,      'b) tuple_dead by auto
lift_bnf (no_warn_wits) (dead 'a,      'b) tuple_dead1 by auto
lift_bnf (no_warn_wits) (     'a, dead 'b) tuple_dead2 by auto
lift_bnf (no_warn_wits) (     'a,      'b,      'c) triple_dead by auto
lift_bnf (no_warn_wits) (dead 'a,      'b,      'c) triple_dead1 by auto
lift_bnf (no_warn_wits) (     'a, dead 'b,      'c) triple_dead2 by auto
lift_bnf (no_warn_wits) (     'a,      'b, dead 'c) triple_dead3 by auto
lift_bnf (no_warn_wits) (dead 'a, dead 'b,      'c) triple_dead12 by auto
lift_bnf (no_warn_wits) (dead 'a,      'b, dead 'c) triple_dead13 by auto
lift_bnf (no_warn_wits) (     'a, dead 'b, dead 'c) triple_dead23 by auto
lift_bnf (no_warn_wits) (     'a,      'b,      'c,      'd) quadruple_dead  by auto
lift_bnf (no_warn_wits) (dead 'a,      'b,      'c,      'd) quadruple_dead1 by auto
lift_bnf (no_warn_wits) (     'a, dead 'b,      'c,      'd) quadruple_dead2 by auto
lift_bnf (no_warn_wits) (     'a,      'b, dead 'c,      'd) quadruple_dead3 by auto
lift_bnf (no_warn_wits) (     'a,      'b,      'c, dead 'd) quadruple_dead4 by auto
lift_bnf (no_warn_wits) (dead 'a, dead 'b,      'c,      'd) quadruple_dead12  by auto
lift_bnf (no_warn_wits) (dead 'a,      'b, dead 'c,      'd) quadruple_dead13  by auto
lift_bnf (no_warn_wits) (dead 'a,      'b,      'c, dead 'd) quadruple_dead14  by auto
lift_bnf (no_warn_wits) (     'a, dead 'b, dead 'c,      'd) quadruple_dead23  by auto
lift_bnf (no_warn_wits) (     'a, dead 'b,      'c, dead 'd) quadruple_dead24  by auto
lift_bnf (no_warn_wits) (     'a,      'b, dead 'c, dead 'd) quadruple_dead34  by auto
lift_bnf (no_warn_wits) (dead 'a, dead 'b, dead 'c,      'd) quadruple_dead123 by auto
lift_bnf (no_warn_wits) (dead 'a, dead 'b,      'c, dead 'd) quadruple_dead124 by auto
lift_bnf (no_warn_wits) (dead 'a,      'b, dead 'c, dead 'd) quadruple_dead134 by auto
lift_bnf (no_warn_wits) (     'a, dead 'b, dead 'c, dead 'd) quadruple_dead234 by auto

subsection \<open>Lifting \textbf{quotient_type}s\<close>

quotient_type 'a cpy_list = "'a list" / "(=)"
  by (rule identity_equivp)

lift_bnf 'a cpy_list
  by (auto intro: list_all2_trans)

quotient_type ('a, 'b) funk = "('a \<Rightarrow> 'b)" / "\<lambda>f g. \<forall>a. f a = g a"
  unfolding equivp_def by metis

lemma funk_closure: "{(x, x'). \<forall>a. x a = x' a} `` {x. range x \<subseteq> A} = {x. range x \<subseteq> A}"
  by auto

lift_bnf (dead 'a, 'b) funk
  unfolding funk_closure rel_fun_def by (auto 0 10 split: if_splits)

lemma assumes "equivp REL"
  shows "REL OO REL OO R = REL OO R"
  using equivp_transp[OF assms] equivp_reflp[OF assms]
  by blast

inductive ignore_Inl :: "'a + 'a \<Rightarrow> 'a + 'a \<Rightarrow> bool" where
  "ignore_Inl (Inl x) (Inl y)"
| "ignore_Inl (Inr x) (Inr x)"

inductive_simps [simp]:
  "ignore_Inl (Inl x) y"
  "ignore_Inl (Inr x') y"
  "ignore_Inl y (Inl x)"
  "ignore_Inl y (Inr x')"

quotient_type 'a opt = "'a + 'a" / ignore_Inl
  apply(auto intro!: equivpI simp add: reflp_def symp_def transp_def elim!: ignore_Inl.cases)
  subgoal for x by(cases x) simp_all.

lemma ignore_Inl_map_respect:
  "(rel_fun (=) (rel_fun ignore_Inl ignore_Inl)) (\<lambda>f. map_sum f f) (\<lambda>f. map_sum f f)"
  by(auto simp add: rel_fun_def elim: ignore_Inl.cases)

lemma ignore_Inl_pos_distr:
  "A OO B \<noteq> bot \<Longrightarrow> ignore_Inl OO rel_sum A A OO ignore_Inl OO rel_sum B B OO ignore_Inl \<le>
   ignore_Inl OO rel_sum (A OO B) (A OO B) OO ignore_Inl"
  by(fastforce elim!: ignore_Inl.cases simp add: relcompp_apply fun_eq_iff intro: exI[where x="Inl _"])

lemma ignore_Inl_Inter:
  "\<lbrakk> S \<noteq> {}; \<Inter>S \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Inter>A\<in>S. {(x, y). ignore_Inl x y} `` {x. Basic_BNFs.setl x \<union> Basic_BNFs.setr x \<subseteq> A}) \<subseteq> {(x, y). ignore_Inl x y} `` (\<Inter>A\<in>S. {x. Basic_BNFs.setl x \<union> Basic_BNFs.setr x \<subseteq> A})"
  apply(clarsimp; safe; clarsimp)
  subgoal for x A x'
    apply(cases x)
     apply(drule bspec[where x="Inl x'"])
      apply clarsimp
     apply simp
    apply clarsimp
    apply(drule bspec[where x="Inr _"])
     apply simp
    apply simp
    done
  done

lift_bnf 'a opt [wits: "(Inl undefined :: 'a + 'a)"]
   apply(auto simp add: rel_fun_def elim: ignore_Inl.cases)[]
  apply(fastforce simp add: rel_sum.simps)
  subgoal for Ss
    using ignore_Inl_Inter[unfolded Plus_def, of Ss]
    by blast
  apply (auto simp: Ball_def image_iff sum_set_defs elim: ignore_Inl.cases split: sum.splits) []
  done

end
