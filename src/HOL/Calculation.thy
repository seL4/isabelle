(*  Title:      HOL/Calculation.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Setup transitivity rules for calculational proofs.
*)

theory Calculation = IntArith:

lemma forw_subst: "a = b ==> P b ==> P a"
  by (rule ssubst)

lemma back_subst: "P a ==> a = b ==> P b"
  by (rule subst)

lemma set_rev_mp: "x:A ==> A <= B ==> x:B"
  by (rule subsetD)

lemma set_mp: "A <= B ==> x:A ==> x:B"
  by (rule subsetD)

lemma order_neq_le_trans: "a ~= b ==> (a::'a::order) <= b ==> a < b"
  by (simp add: order_less_le)

lemma order_le_neq_trans: "(a::'a::order) <= b ==> a ~= b ==> a < b"
  by (simp add: order_less_le)

lemma order_less_asym': "(a::'a::order) < b ==> b < a ==> P"
  by (rule order_less_asym)

lemma ord_le_eq_trans: "a <= b ==> b = c ==> a <= c"
  by (rule subst)

lemma ord_eq_le_trans: "a = b ==> b <= c ==> a <= c"
  by (rule ssubst)

lemma ord_less_eq_trans: "a < b ==> b = c ==> a < c"
  by (rule subst)

lemma ord_eq_less_trans: "a = b ==> b < c ==> a < c"
  by (rule ssubst)

lemma order_less_subst2: "(a::'a::order) < b ==> f b < (c::'c::order) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b < c"
  finally (order_less_trans) show ?thesis .
qed

lemma order_less_subst1: "(a::'a::order) < f b ==> (b::'b::order) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (order_less_trans) show ?thesis .
qed

lemma order_le_less_subst2: "(a::'a::order) <= b ==> f b < (c::'c::order) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a < c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b < c"
  finally (order_le_less_trans) show ?thesis .
qed

lemma order_le_less_subst1: "(a::'a::order) <= f b ==> (b::'b::order) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a <= f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (order_le_less_trans) show ?thesis .
qed

lemma order_less_le_subst2: "(a::'a::order) < b ==> f b <= (c::'c::order) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b <= c"
  finally (order_less_le_trans) show ?thesis .
qed

lemma order_less_le_subst1: "(a::'a::order) < f b ==> (b::'b::order) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a < f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a < f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_less_le_trans) show ?thesis .
qed

lemma order_subst1: "(a::'a::order) <= f b ==> (b::'b::order) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_trans) show ?thesis .
qed

lemma order_subst2: "(a::'a::order) <= b ==> f b <= (c::'c::order) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b <= c"
  finally (order_trans) show ?thesis .
qed

lemma ord_le_eq_subst: "a <= b ==> f b = c ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b = c"
  finally (ord_le_eq_trans) show ?thesis .
qed

lemma ord_eq_le_subst: "a = f b ==> b <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a = f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (ord_eq_le_trans) show ?thesis .
qed

lemma ord_less_eq_subst: "a < b ==> f b = c ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b = c"
  finally (ord_less_eq_trans) show ?thesis .
qed

lemma ord_eq_less_subst: "a = f b ==> b < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a = f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (ord_eq_less_trans) show ?thesis .
qed

text {*
  Note that this list of rules is in reverse order of priorities.
*}

lemmas trans_rules [trans] =
  order_less_subst2
  order_less_subst1
  order_le_less_subst2
  order_le_less_subst1
  order_less_le_subst2
  order_less_le_subst1
  order_subst2
  order_subst1
  ord_le_eq_subst
  ord_eq_le_subst
  ord_less_eq_subst
  ord_eq_less_subst
  forw_subst
  back_subst
  dvd_trans
  rev_mp
  mp
  set_rev_mp
  set_mp
  order_neq_le_trans
  order_le_neq_trans
  order_less_asym'
  order_less_trans
  order_le_less_trans
  order_less_le_trans
  order_trans
  order_antisym
  ord_le_eq_trans
  ord_eq_le_trans
  ord_less_eq_trans
  ord_eq_less_trans
  trans
  transitive

end
