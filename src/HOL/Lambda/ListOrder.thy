(*  Title:      HOL/Lambda/ListOrder.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

header {* Lifting an order to lists of elements *}

theory ListOrder imports Main begin

text {*
  Lifting an order to lists of elements, relating exactly one
  element.
*}

definition
  step1 :: "('a => 'a => bool) => 'a list => 'a list => bool" where
  "step1 r =
    (\<lambda>ys xs. \<exists>us z z' vs. xs = us @ z # vs \<and> r z' z \<and> ys =
      us @ z' # vs)"


lemma step1_converse [simp]: "step1 (r^--1) = (step1 r)^--1"
  apply (unfold step1_def)
  apply (blast intro!: order_antisym)
  done

lemma in_step1_converse [iff]: "(step1 (r^--1) x y) = ((step1 r)^--1 x y)"
  apply auto
  done

lemma not_Nil_step1 [iff]: "\<not> step1 r [] xs"
  apply (unfold step1_def)
  apply blast
  done

lemma not_step1_Nil [iff]: "\<not> step1 r xs []"
  apply (unfold step1_def)
  apply blast
  done

lemma Cons_step1_Cons [iff]:
    "(step1 r (y # ys) (x # xs)) =
      (r y x \<and> xs = ys \<or> x = y \<and> step1 r ys xs)"
  apply (unfold step1_def)
  apply (rule iffI)
   apply (erule exE)
   apply (rename_tac ts)
   apply (case_tac ts)
    apply fastsimp
   apply force
  apply (erule disjE)
   apply blast
  apply (blast intro: Cons_eq_appendI)
  done

lemma append_step1I:
  "step1 r ys xs \<and> vs = us \<or> ys = xs \<and> step1 r vs us
    ==> step1 r (ys @ vs) (xs @ us)"
  apply (unfold step1_def)
  apply auto
   apply blast
  apply (blast intro: append_eq_appendI)
  done

lemma Cons_step1E [elim!]:
  assumes "step1 r ys (x # xs)"
    and "!!y. ys = y # xs \<Longrightarrow> r y x \<Longrightarrow> R"
    and "!!zs. ys = x # zs \<Longrightarrow> step1 r zs xs \<Longrightarrow> R"
  shows R
  using assms
  apply (cases ys)
   apply (simp add: step1_def)
  apply blast
  done

lemma Snoc_step1_SnocD:
  "step1 r (ys @ [y]) (xs @ [x])
    ==> (step1 r ys xs \<and> y = x \<or> ys = xs \<and> r y x)"
  apply (unfold step1_def)
  apply (clarify del: disjCI)
  apply (rename_tac vs)
  apply (rule_tac xs = vs in rev_exhaust)
   apply force
  apply simp
  apply blast
  done

lemma Cons_acc_step1I [intro!]:
    "acc r x ==> acc (step1 r) xs \<Longrightarrow> acc (step1 r) (x # xs)"
  apply (induct arbitrary: xs set: acc)
  apply (erule thin_rl)
  apply (erule acc_induct)
  apply (rule accI)
  apply blast
  done

lemma lists_accD: "listsp (acc r) xs ==> acc (step1 r) xs"
  apply (induct set: listsp)
   apply (rule accI)
   apply simp
  apply (rule accI)
  apply (fast dest: acc_downward)
  done

lemma ex_step1I:
  "[| x \<in> set xs; r y x |]
    ==> \<exists>ys. step1 r ys xs \<and> y \<in> set ys"
  apply (unfold step1_def)
  apply (drule in_set_conv_decomp [THEN iffD1])
  apply force
  done

lemma lists_accI: "acc (step1 r) xs ==> listsp (acc r) xs"
  apply (induct set: acc)
  apply clarify
  apply (rule accI)
  apply (drule_tac r=r in ex_step1I, assumption)
  apply blast
  done

end
