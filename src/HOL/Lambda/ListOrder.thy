(*  Title:      HOL/Lambda/ListOrder.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen

Lifting an order to lists of elements, relating exactly one element
*)

theory ListOrder = Acc:

constdefs
  step1 :: "('a \<times> 'a) set => ('a list \<times> 'a list) set"
  "step1 r ==
    {(ys, xs). \<exists>us z z' vs. xs = us @ z # vs \<and> (z', z) \<in> r \<and> ys = us @ z' # vs}"


lemma step1_converse [simp]: "step1 (r^-1) = (step1 r)^-1"
  apply (unfold step1_def)
  apply blast
  done

lemma in_step1_converse [iff]: "(p \<in> step1 (r^-1)) = (p \<in> (step1 r)^-1)"
  apply auto
  done

lemma not_Nil_step1 [iff]: "([], xs) \<notin> step1 r"
  apply (unfold step1_def)
  apply blast
  done

lemma not_step1_Nil [iff]: "(xs, []) \<notin> step1 r"
  apply (unfold step1_def)
  apply blast
  done

lemma Cons_step1_Cons [iff]:
  "((y # ys, x # xs) \<in> step1 r) = ((y, x) \<in> r \<and> xs = ys \<or> x = y \<and> (ys, xs) \<in> step1 r)"
  apply (unfold step1_def)
  apply simp
  apply (rule iffI)
   apply (erule exE)
   apply (rename_tac ts)
   apply (case_tac ts)
    apply force
   apply force
  apply (erule disjE)
   apply blast
  apply (blast intro: Cons_eq_appendI)
  done

lemma append_step1I:
  "(ys, xs) \<in> step1 r \<and> vs = us \<or> ys = xs \<and> (vs, us) \<in> step1 r
    ==> (ys @ vs, xs @ us) : step1 r"
  apply (unfold step1_def)
  apply auto
   apply blast
  apply (blast intro: append_eq_appendI)
  done

lemma Cons_step1E [rulify_prems, elim!]:
  "[| (ys, x # xs) \<in> step1 r;
      \<forall>y. ys = y # xs --> (y, x) \<in> r --> R;
      \<forall>zs. ys = x # zs --> (zs, xs) : step1 r --> R
   |] ==> R"
  apply (case_tac ys)
   apply (simp add: step1_def)
  apply blast
  done

lemma Snoc_step1_SnocD:
  "(ys @ [y], xs @ [x]) \<in> step1 r
    ==> ((ys, xs) \<in> step1 r \<and> y = x \<or> ys = xs \<and> (y, x) \<in> r)"
  apply (unfold step1_def)
  apply simp
  apply (clarify del: disjCI)
  apply (rename_tac vs)
  apply (rule_tac xs = vs in rev_exhaust)
   apply force
  apply simp
  apply blast
  done

lemma Cons_acc_step1I [rulify, intro!]:
    "x \<in> acc r ==> \<forall>xs. xs \<in> acc (step1 r) --> x # xs \<in> acc (step1 r)"
  apply (erule acc_induct)
  apply (erule thin_rl)
  apply clarify
  apply (erule acc_induct)
  apply (rule accI)
  apply blast
  done

lemma lists_accD: "xs \<in> lists (acc r) ==> xs \<in> acc (step1 r)"
  apply (erule lists.induct)
   apply (rule accI)
   apply simp
  apply (rule accI)
  apply (fast dest: acc_downward)
  done

lemma ex_step1I: "[| x \<in> set xs; (y, x) \<in> r |]
    ==> \<exists>ys. (ys, xs) \<in> step1 r \<and> y \<in> set ys"
  apply (unfold step1_def)
  apply (drule in_set_conv_decomp [THEN iffD1])
  apply force
  done

lemma lists_accI: "xs \<in> acc (step1 r) ==> xs \<in> lists (acc r)"
  apply (erule acc_induct)
  apply clarify
  apply (rule accI)
  apply (drule ex_step1I, assumption)
  apply blast
  done

end
