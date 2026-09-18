(*  Title:      HOL/Alethe_Boolean_Rewrites.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_Boolean_Rewrites
  imports "Alethe_Boolean_Rewrites_Lemmas"
begin

(*
Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in
Alethe_Rare_Interface.thy and register the rules using the cvc5_rare command.
Note: The proofs for these lemmas are in Alethe_Boolean_Rewrites_Lemmas.thy allowing this file to be
impervious to small changes.
*)

named_theorems rewrite_bool_double_not_elim \<open>automatically_generated\<close>

(* (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t) *)
lemma [rewrite_bool_double_not_elim]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (\<not> \<not> t) = t"
  by auto

named_theorems rewrite_bool_not_true \<open>automatically_generated\<close>

(* (define-cond-rule bool-not-true ((t Bool)) (= t false) (not t) true) *)
lemma [rewrite_bool_not_true]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = False) \<Longrightarrow> (\<not> t) = True"
  by auto

named_theorems rewrite_bool_not_false \<open>automatically_generated\<close>

(* (define-cond-rule bool-not-false ((t Bool)) (= t true) (not t) false) *)
lemma [rewrite_bool_not_false]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = True) \<Longrightarrow> (\<not> t) = False"
  by auto

named_theorems rewrite_bool_eq_true \<open>automatically_generated\<close>

(* (define-rule bool-eq-true ((t Bool)) (= t true) t) *)
lemma [rewrite_bool_eq_true]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = True) = t"
  by auto

named_theorems rewrite_bool_eq_false \<open>automatically_generated\<close>

(* (define-rule bool-eq-false ((t Bool)) (= t false) (not t)) *)
lemma [rewrite_bool_eq_false]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = False) = (\<not> t)"
  by auto

named_theorems rewrite_bool_eq_nrefl \<open>automatically_generated\<close>

(* (define-rule bool-eq-nrefl ((x Bool)) (= x (not x)) false) *)
lemma [rewrite_bool_eq_nrefl]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x = (\<not> x)) = False"
  by auto

named_theorems rewrite_bool_impl_false1 \<open>automatically_generated\<close>

(* (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t)) *)
lemma [rewrite_bool_impl_false1]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<longrightarrow> False) = (\<not> t)"
  by auto

named_theorems rewrite_bool_impl_false2 \<open>automatically_generated\<close>

(* (define-rule bool-impl-false2 ((t Bool)) (=> false t) true) *)
lemma [rewrite_bool_impl_false2]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (False \<longrightarrow> t) = True"
  by auto

named_theorems rewrite_bool_impl_true1 \<open>automatically_generated\<close>

(* (define-rule bool-impl-true1 ((t Bool)) (=> t true) true) *)
lemma [rewrite_bool_impl_true1]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<longrightarrow> True) = True"
  by auto

named_theorems rewrite_bool_impl_true2 \<open>automatically_generated\<close>

(* (define-rule bool-impl-true2 ((t Bool)) (=> true t) t) *)
lemma [rewrite_bool_impl_true2]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (True \<longrightarrow> t) = t"
  by auto

named_theorems rewrite_bool_impl_elim \<open>automatically_generated\<close>

(* (define-rule bool-impl-elim ((t Bool) (s Bool)) (=> t s) (or (not t) s)) *)
lemma [rewrite_bool_impl_elim]:
  fixes t::"bool" and s::"bool"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<longrightarrow> s) = (\<not> t \<or> s)"
  by auto

named_theorems rewrite_bool_dual_impl_eq \<open>automatically_generated\<close>

(* used in proof elaboration
   (define-rule bool-dual-impl-eq ((t Bool) (s Bool)) (and (=> t s) (=> s t)) (= t s)) *)
lemma [rewrite_bool_dual_impl_eq]:
  fixes t::"bool" and s::"bool"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> ((t \<longrightarrow> s) \<and> (s \<longrightarrow> t)) = (t = s)"
  by auto

named_theorems rewrite_bool_and_conf \<open>automatically_generated\<close>

(* (define-rule bool-and-conf ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (and xs w ys (not w) zs) false) *)
lemma [rewrite_bool_and_conf]:
  fixes xs::"bool cvc_ListVar" and w::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs w ys zs) \<Longrightarrow> cvc_list_left (\<and>) xs
    (w \<and>
     cvc_list_left (\<and>) ys (cvc_list_right (\<and>) (\<not> w) zs)) =
   False"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss)
    apply simp_all
    apply (induction yss)
    apply simp_all
    apply (induction xss)
    apply simp_all
    by (simp_all add: bool_and_conf_lemma)
  done

named_theorems rewrite_bool_and_conf2 \<open>automatically_generated\<close>

(* (define-rule bool-and-conf2 ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (and xs (not w) ys w zs) false) *)
lemma [rewrite_bool_and_conf2]:
  fixes xs::"bool cvc_ListVar" and w::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs w ys zs) \<Longrightarrow> cvc_list_left (\<and>) xs
    ((\<not> w) \<and>
     cvc_list_left (\<and>) ys (cvc_list_right (\<and>) w zs)) =
   False"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss)
    apply simp_all
    apply (induction yss)
    apply simp_all
    apply (induction xss)
    apply simp_all
    apply (simp_all add: bool_and_conf2_lemma)
    by force
  done

named_theorems rewrite_bool_or_taut \<open>automatically_generated\<close>

(* (define-rule bool-or-taut ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (or xs w ys (not w) zs) true) *)
lemma [rewrite_bool_or_taut]:
  fixes xs::"bool cvc_ListVar" and w::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs w ys zs) \<Longrightarrow> cvc_list_left (\<or>) xs
    (w \<or>
     cvc_list_left (\<or>) ys (cvc_list_right (\<or>) (\<not> w) zs)) =
   True"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss)
    apply simp_all
    apply (induction yss)
    apply simp_all
    apply (induction xss)
    apply simp_all
    by (simp_all add: bool_or_taut_lemma)
  done

named_theorems rewrite_bool_or_taut2 \<open>automatically_generated\<close>

(* (define-rule bool-or-taut2 ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (or xs (not w) ys w zs) true) *)
lemma [rewrite_bool_or_taut2]:
  fixes xs::"bool cvc_ListVar" and w::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs w ys zs) \<Longrightarrow> cvc_list_left (\<or>) xs
    ((\<not> w) \<or>
     cvc_list_left (\<or>) ys (cvc_list_right (\<or>) w zs)) =
   True"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
  done

named_theorems rewrite_bool_or_de_morgan \<open>automatically_generated\<close>

(* (define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list))
     (not (or x y zs))
     (not (or y zs))
     (and (not x) _)) *)
lemma [rewrite_bool_or_de_morgan]:
  fixes zs :: "bool cvc_ListVar" and y :: "bool" and x :: "bool"
  shows "NO_MATCH cvc_a (undefined x y zs) \<Longrightarrow> (\<not> (x \<or> cvc_list_right (\<or>) y zs)) =
(\<not> x \<and> \<not> cvc_list_right (\<or>) y zs)"
  apply simp ?
  done

named_theorems rewrite_bool_implies_de_morgan \<open>automatically_generated\<close>

(* (define-rule bool-implies-de-morgan ((x Bool) (y Bool)) (not (=> x y)) (and x (not y))) *)
lemma [rewrite_bool_implies_de_morgan]:
  fixes y :: "bool" and x :: "bool"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (\<not> (x \<longrightarrow> y)) = (x \<and> \<not> y)"
  apply simp ?
  done

named_theorems rewrite_bool_and_de_morgan \<open>automatically_generated\<close>

(* (define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list))
     (not (and x y zs))
     (not (and y zs))
     (or (not x) _)) *)
lemma [rewrite_bool_and_de_morgan]:
  fixes zs :: "bool cvc_ListVar" and y :: "bool" and x :: "bool"
  shows "NO_MATCH cvc_a (undefined x y zs) \<Longrightarrow> (\<not> (x \<and> cvc_list_right (\<and>) y zs)) =
(\<not> x \<or> \<not> cvc_list_right (\<and>) y zs)"
  apply simp ?
  done

named_theorems rewrite_bool_or_and_distrib \<open>automatically_generated\<close>

(* (define-rule* bool-or-and-distrib ((y1 Bool) (y2 Bool) (ys Bool :list) (z1 Bool) (zs Bool :list))
     (or (and y1 y2 ys) z1 zs)
     (or (and y2 ys) z1 zs)
     (and (or y1 z1 zs) _)) *)
lemma [rewrite_bool_or_and_distrib]:
  fixes zs :: "bool cvc_ListVar" and ys :: "bool cvc_ListVar" and y2 :: "bool" and y1 :: "bool" and z1 :: "bool"
  shows "NO_MATCH cvc_a (undefined y1 y2 ys z1 zs) \<Longrightarrow>
 ((y1 \<and> cvc_list_right (\<and>) y2 ys) \<or> (cvc_list_right (\<or>) z1 zs)) =
((y1 \<or> cvc_list_right (\<or>) z1 zs) \<and>
  ((cvc_list_right (\<and>) y2 ys) \<or> cvc_list_right (\<or>) z1 zs))"
  apply (cases zs)
  apply (cases ys)
  subgoal for zss yss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all add: bool_or_and_distrib_lemma)
  done

named_theorems rewrite_bool_implies_or_distrib \<open>automatically_generated\<close>

(* (define-rule* bool-implies-or-distrib ((y1 Bool) (y2 Bool) (ys Bool :list) (z Bool))
     (=> (or y1 y2 ys) z)
     (=> (or y2 ys) z)
     (and (=> y1 z) _)) *)
lemma [rewrite_bool_implies_or_distrib]:
  fixes y1 :: "bool" and y2 :: "bool" and ys :: "bool cvc_ListVar" and z :: "bool"
  shows "NO_MATCH cvc_a (undefined y1 y2 ys z) \<Longrightarrow> (y1 \<or> cvc_list_right (\<or>) y2 ys \<longrightarrow> z) =
((y1 \<longrightarrow> z) \<and>
 (cvc_list_right (\<or>) y2 ys \<longrightarrow> z))"
  apply simp ?
  done

named_theorems rewrite_bool_xor_refl \<open>automatically_generated\<close>

(* (define-rule bool-xor-refl ((x Bool)) (xor x x) false) *)
lemma [rewrite_bool_xor_refl]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<noteq> x) = False"
  by auto

named_theorems rewrite_bool_xor_nrefl \<open>automatically_generated\<close>

(* (define-rule bool-xor-nrefl ((x Bool)) (xor x (not x)) true) *)
lemma [rewrite_bool_xor_nrefl]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<noteq> (\<not> x)) = True"
  by auto

named_theorems rewrite_bool_xor_false \<open>automatically_generated\<close>

(* (define-rule bool-xor-false ((x Bool)) (xor x false) x) *)
lemma [rewrite_bool_xor_false]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<noteq> False) = x"
  by auto

named_theorems rewrite_bool_xor_true \<open>automatically_generated\<close>

(* (define-rule bool-xor-true ((x Bool)) (xor x true) (not x)) *)
lemma [rewrite_bool_xor_true]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<noteq> True) = (\<not> x)"
  by auto

named_theorems rewrite_bool_xor_comm \<open>automatically_generated\<close>

(* (define-rule bool-xor-comm ((x Bool) (y Bool)) (xor x y) (xor y x)) *)
lemma [rewrite_bool_xor_comm]:
  fixes x::"bool" and y::"bool"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<noteq> y) = (\<not>(y = x))"
  by auto

named_theorems rewrite_bool_xor_elim \<open>automatically_generated\<close>

(* (define-rule bool-xor-elim ((x Bool) (y Bool)) (xor x y) (= (not x) y)) *)
lemma [rewrite_bool_xor_elim]:
  fixes x::"bool" and y::"bool"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<noteq> y) = ((\<not>x) = y)"
  by auto

named_theorems rewrite_bool_not_xor_elim \<open>automatically_generated\<close>

(* (define-rule bool-not-xor-elim ((x Bool) (y Bool)) (not (xor x y)) (= x y)) *)
lemma [rewrite_bool_not_xor_elim]:
  fixes y :: "bool" and x :: "bool"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (\<not> (x \<noteq> y)) = (x = y)"
  apply simp ?
  done

named_theorems rewrite_bool_not_eq_elim1 \<open>automatically_generated\<close>

(* (define-rule bool-not-eq-elim1 ((x Bool) (y Bool)) (not (= x y)) (= (not x) y)) *)
lemma [rewrite_bool_not_eq_elim1]:
  fixes y :: "bool" and x :: "bool"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<noteq> y) = ((\<not> x) = y)"
  apply simp ?
  apply auto ?
  done

named_theorems rewrite_bool_not_eq_elim2 \<open>automatically_generated\<close>

(* (define-rule bool-not-eq-elim2 ((x Bool) (y Bool)) (not (= x y)) (= x (not y))) *)
lemma [rewrite_bool_not_eq_elim2]:
  fixes y :: "bool" and x :: "bool"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<noteq> y) = (x = (\<not> y))"
  apply simp ?
  apply auto ?
  done

named_theorems rewrite_ite_neg_branch \<open>automatically_generated\<close>

(* (define-cond-rule ite-neg-branch ((c Bool) (x Bool) (y Bool)) (= (not y) x) (ite c x y) (= c x)) *)
lemma [rewrite_ite_neg_branch]:
  fixes c::"bool" and x::"bool" and y::"bool"
  shows "NO_MATCH cvc_a (undefined c x y) \<Longrightarrow> (\<not> y) = x \<longrightarrow> (if c then x else y) = (c = x)"
  by auto

named_theorems rewrite_ite_then_true \<open>automatically_generated\<close>

(* (define-rule ite-then-true ((c Bool) (x Bool)) (ite c true x) (or c x)) *)
lemma [rewrite_ite_then_true]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then True else x) = (c \<or> x)"
  by auto

named_theorems rewrite_ite_else_false \<open>automatically_generated\<close>

(* (define-rule ite-else-false ((c Bool) (x Bool)) (ite c x false) (and c x)) *)
lemma [rewrite_ite_else_false]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else False) = (c \<and> x)"
  by auto

named_theorems rewrite_ite_then_false \<open>automatically_generated\<close>

(* (define-rule ite-then-false ((c Bool) (x Bool)) (ite c false x) (and (not c) x)) *)
lemma [rewrite_ite_then_false]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then False else x) = (\<not> c \<and> x)"
  by auto

named_theorems rewrite_ite_else_true \<open>automatically_generated\<close>

(* (define-rule ite-else-true ((c Bool) (x Bool)) (ite c x true) (or (not c) x)) *)
lemma [rewrite_ite_else_true]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else True) = (\<not> c \<or> x)"
  by auto

named_theorems rewrite_ite_then_lookahead_self \<open>automatically_generated\<close>

(* (define-rule ite-then-lookahead-self ((c Bool) (x Bool)) (ite c c x) (ite c true x)) *)
lemma [rewrite_ite_then_lookahead_self]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then c else x) = (if c then True else x)"
  by auto

named_theorems rewrite_ite_else_lookahead_self \<open>automatically_generated\<close>

(* (define-rule ite-else-lookahead-self ((c Bool) (x Bool)) (ite c x c) (ite c x false)) *)
lemma [rewrite_ite_else_lookahead_self]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else c) = (if c then x else False)"
  by auto

named_theorems rewrite_ite_then_lookahead_not_self \<open>automatically_generated\<close>

(* (define-rule ite-then-lookahead-not-self ((c Bool) (x Bool)) (ite c (not c) x) (ite c false x)) *)
lemma [rewrite_ite_then_lookahead_not_self]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then \<not>c else x) = (if c then False else x)"
  by auto

named_theorems rewrite_ite_else_lookahead_not_self \<open>automatically_generated\<close>

(* (define-rule ite-else-lookahead-not-self ((c Bool) (x Bool)) (ite c x (not c)) (ite c x true)) *)
lemma [rewrite_ite_else_lookahead_not_self]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else \<not>c) = (if c then x else True)"
  by auto

named_theorems rewrite_ite_expand \<open>automatically_generated\<close>

(* (define-rule ite-expand ((c Bool) (x Bool) (y Bool)) (ite c x y) (and (or (not c) x) (or c y))) *)
lemma [rewrite_ite_expand]:
  fixes c::"bool" and x::"bool" and y::"bool"
  shows "NO_MATCH cvc_a (undefined c x y) \<Longrightarrow> (if c then x else y) = ((\<not>c \<or> x) \<and> (c \<or> y))"
  by auto

named_theorems rewrite_bool_not_ite_elim \<open>automatically_generated\<close>

(* (define-rule bool-not-ite-elim ((c Bool) (x Bool) (y Bool)) (not (ite c x y)) (ite c (not x) (not y))) *)
lemma [rewrite_bool_not_ite_elim]:
  fixes c::"bool" and x::"bool" and y::"bool"
  shows "NO_MATCH cvc_a (undefined c x y) \<Longrightarrow> (\<not>(if c then x else y)) = (if c then \<not>x else \<not>y)"
  by auto

end
