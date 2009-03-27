(*  Title:      HOL/Library/SetsAndFunctions.thy
    Author:     Jeremy Avigad and Kevin Donnelly
*)

header {* Operations on sets and functions *}

theory SetsAndFunctions
imports Main
begin

text {*
This library lifts operations like addition and muliplication to sets and
functions of appropriate types. It was designed to support asymptotic
calculations. See the comments at the top of theory @{text BigO}.
*}

subsection {* Basic definitions *}

definition
  set_plus :: "('a::plus) set => 'a set => 'a set"  (infixl "\<oplus>" 65) where
  "A \<oplus> B == {c. EX a:A. EX b:B. c = a + b}"

instantiation "fun" :: (type, plus) plus
begin

definition
  func_plus: "f + g == (%x. f x + g x)"

instance ..

end

definition
  set_times :: "('a::times) set => 'a set => 'a set"  (infixl "\<otimes>" 70) where
  "A \<otimes> B == {c. EX a:A. EX b:B. c = a * b}"

instantiation "fun" :: (type, times) times
begin

definition
  func_times: "f * g == (%x. f x * g x)"

instance ..

end


instantiation "fun" :: (type, zero) zero
begin

definition
  func_zero: "0::(('a::type) => ('b::zero)) == %x. 0"

instance ..

end

instantiation "fun" :: (type, one) one
begin

definition
  func_one: "1::(('a::type) => ('b::one)) == %x. 1"

instance ..

end

definition
  elt_set_plus :: "'a::plus => 'a set => 'a set"  (infixl "+o" 70) where
  "a +o B = {c. EX b:B. c = a + b}"

definition
  elt_set_times :: "'a::times => 'a set => 'a set"  (infixl "*o" 80) where
  "a *o B = {c. EX b:B. c = a * b}"

abbreviation (input)
  elt_set_eq :: "'a => 'a set => bool"  (infix "=o" 50) where
  "x =o A == x : A"

instance "fun" :: (type,semigroup_add)semigroup_add
  by default (auto simp add: func_plus add_assoc)

instance "fun" :: (type,comm_monoid_add)comm_monoid_add
  by default (auto simp add: func_zero func_plus add_ac)

instance "fun" :: (type,ab_group_add)ab_group_add
  apply default
   apply (simp add: fun_Compl_def func_plus func_zero)
  apply (simp add: fun_Compl_def func_plus fun_diff_def diff_minus)
  done

instance "fun" :: (type,semigroup_mult)semigroup_mult
  apply default
  apply (auto simp add: func_times mult_assoc)
  done

instance "fun" :: (type,comm_monoid_mult)comm_monoid_mult
  apply default
   apply (auto simp add: func_one func_times mult_ac)
  done

instance "fun" :: (type,comm_ring_1)comm_ring_1
  apply default
   apply (auto simp add: func_plus func_times fun_Compl_def fun_diff_def
     func_one func_zero algebra_simps)
  apply (drule fun_cong)
  apply simp
  done

interpretation set_semigroup_add: semigroup_add "op \<oplus> :: ('a::semigroup_add) set => 'a set => 'a set"
  apply default
  apply (unfold set_plus_def)
  apply (force simp add: add_assoc)
  done

interpretation set_semigroup_mult: semigroup_mult "op \<otimes> :: ('a::semigroup_mult) set => 'a set => 'a set"
  apply default
  apply (unfold set_times_def)
  apply (force simp add: mult_assoc)
  done

interpretation set_comm_monoid_add: comm_monoid_add "{0}" "op \<oplus> :: ('a::comm_monoid_add) set => 'a set => 'a set"
  apply default
   apply (unfold set_plus_def)
   apply (force simp add: add_ac)
  apply force
  done

interpretation set_comm_monoid_mult: comm_monoid_mult "{1}" "op \<otimes> :: ('a::comm_monoid_mult) set => 'a set => 'a set"
  apply default
   apply (unfold set_times_def)
   apply (force simp add: mult_ac)
  apply force
  done


subsection {* Basic properties *}

lemma set_plus_intro [intro]: "a : C ==> b : D ==> a + b : C \<oplus> D"
  by (auto simp add: set_plus_def)

lemma set_plus_intro2 [intro]: "b : C ==> a + b : a +o C"
  by (auto simp add: elt_set_plus_def)

lemma set_plus_rearrange: "((a::'a::comm_monoid_add) +o C) \<oplus>
    (b +o D) = (a + b) +o (C \<oplus> D)"
  apply (auto simp add: elt_set_plus_def set_plus_def add_ac)
   apply (rule_tac x = "ba + bb" in exI)
  apply (auto simp add: add_ac)
  apply (rule_tac x = "aa + a" in exI)
  apply (auto simp add: add_ac)
  done

lemma set_plus_rearrange2: "(a::'a::semigroup_add) +o (b +o C) =
    (a + b) +o C"
  by (auto simp add: elt_set_plus_def add_assoc)

lemma set_plus_rearrange3: "((a::'a::semigroup_add) +o B) \<oplus> C =
    a +o (B \<oplus> C)"
  apply (auto simp add: elt_set_plus_def set_plus_def)
   apply (blast intro: add_ac)
  apply (rule_tac x = "a + aa" in exI)
  apply (rule conjI)
   apply (rule_tac x = "aa" in bexI)
    apply auto
  apply (rule_tac x = "ba" in bexI)
   apply (auto simp add: add_ac)
  done

theorem set_plus_rearrange4: "C \<oplus> ((a::'a::comm_monoid_add) +o D) =
    a +o (C \<oplus> D)"
  apply (auto intro!: subsetI simp add: elt_set_plus_def set_plus_def add_ac)
   apply (rule_tac x = "aa + ba" in exI)
   apply (auto simp add: add_ac)
  done

theorems set_plus_rearranges = set_plus_rearrange set_plus_rearrange2
  set_plus_rearrange3 set_plus_rearrange4

lemma set_plus_mono [intro!]: "C <= D ==> a +o C <= a +o D"
  by (auto simp add: elt_set_plus_def)

lemma set_plus_mono2 [intro]: "(C::('a::plus) set) <= D ==> E <= F ==>
    C \<oplus> E <= D \<oplus> F"
  by (auto simp add: set_plus_def)

lemma set_plus_mono3 [intro]: "a : C ==> a +o D <= C \<oplus> D"
  by (auto simp add: elt_set_plus_def set_plus_def)

lemma set_plus_mono4 [intro]: "(a::'a::comm_monoid_add) : C ==>
    a +o D <= D \<oplus> C"
  by (auto simp add: elt_set_plus_def set_plus_def add_ac)

lemma set_plus_mono5: "a:C ==> B <= D ==> a +o B <= C \<oplus> D"
  apply (subgoal_tac "a +o B <= a +o D")
   apply (erule order_trans)
   apply (erule set_plus_mono3)
  apply (erule set_plus_mono)
  done

lemma set_plus_mono_b: "C <= D ==> x : a +o C
    ==> x : a +o D"
  apply (frule set_plus_mono)
  apply auto
  done

lemma set_plus_mono2_b: "C <= D ==> E <= F ==> x : C \<oplus> E ==>
    x : D \<oplus> F"
  apply (frule set_plus_mono2)
   prefer 2
   apply force
  apply assumption
  done

lemma set_plus_mono3_b: "a : C ==> x : a +o D ==> x : C \<oplus> D"
  apply (frule set_plus_mono3)
  apply auto
  done

lemma set_plus_mono4_b: "(a::'a::comm_monoid_add) : C ==>
    x : a +o D ==> x : D \<oplus> C"
  apply (frule set_plus_mono4)
  apply auto
  done

lemma set_zero_plus [simp]: "(0::'a::comm_monoid_add) +o C = C"
  by (auto simp add: elt_set_plus_def)

lemma set_zero_plus2: "(0::'a::comm_monoid_add) : A ==> B <= A \<oplus> B"
  apply (auto intro!: subsetI simp add: set_plus_def)
  apply (rule_tac x = 0 in bexI)
   apply (rule_tac x = x in bexI)
    apply (auto simp add: add_ac)
  done

lemma set_plus_imp_minus: "(a::'a::ab_group_add) : b +o C ==> (a - b) : C"
  by (auto simp add: elt_set_plus_def add_ac diff_minus)

lemma set_minus_imp_plus: "(a::'a::ab_group_add) - b : C ==> a : b +o C"
  apply (auto simp add: elt_set_plus_def add_ac diff_minus)
  apply (subgoal_tac "a = (a + - b) + b")
   apply (rule bexI, assumption, assumption)
  apply (auto simp add: add_ac)
  done

lemma set_minus_plus: "((a::'a::ab_group_add) - b : C) = (a : b +o C)"
  by (rule iffI, rule set_minus_imp_plus, assumption, rule set_plus_imp_minus,
    assumption)

lemma set_times_intro [intro]: "a : C ==> b : D ==> a * b : C \<otimes> D"
  by (auto simp add: set_times_def)

lemma set_times_intro2 [intro!]: "b : C ==> a * b : a *o C"
  by (auto simp add: elt_set_times_def)

lemma set_times_rearrange: "((a::'a::comm_monoid_mult) *o C) \<otimes>
    (b *o D) = (a * b) *o (C \<otimes> D)"
  apply (auto simp add: elt_set_times_def set_times_def)
   apply (rule_tac x = "ba * bb" in exI)
   apply (auto simp add: mult_ac)
  apply (rule_tac x = "aa * a" in exI)
  apply (auto simp add: mult_ac)
  done

lemma set_times_rearrange2: "(a::'a::semigroup_mult) *o (b *o C) =
    (a * b) *o C"
  by (auto simp add: elt_set_times_def mult_assoc)

lemma set_times_rearrange3: "((a::'a::semigroup_mult) *o B) \<otimes> C =
    a *o (B \<otimes> C)"
  apply (auto simp add: elt_set_times_def set_times_def)
   apply (blast intro: mult_ac)
  apply (rule_tac x = "a * aa" in exI)
  apply (rule conjI)
   apply (rule_tac x = "aa" in bexI)
    apply auto
  apply (rule_tac x = "ba" in bexI)
   apply (auto simp add: mult_ac)
  done

theorem set_times_rearrange4: "C \<otimes> ((a::'a::comm_monoid_mult) *o D) =
    a *o (C \<otimes> D)"
  apply (auto intro!: subsetI simp add: elt_set_times_def set_times_def
    mult_ac)
   apply (rule_tac x = "aa * ba" in exI)
   apply (auto simp add: mult_ac)
  done

theorems set_times_rearranges = set_times_rearrange set_times_rearrange2
  set_times_rearrange3 set_times_rearrange4

lemma set_times_mono [intro]: "C <= D ==> a *o C <= a *o D"
  by (auto simp add: elt_set_times_def)

lemma set_times_mono2 [intro]: "(C::('a::times) set) <= D ==> E <= F ==>
    C \<otimes> E <= D \<otimes> F"
  by (auto simp add: set_times_def)

lemma set_times_mono3 [intro]: "a : C ==> a *o D <= C \<otimes> D"
  by (auto simp add: elt_set_times_def set_times_def)

lemma set_times_mono4 [intro]: "(a::'a::comm_monoid_mult) : C ==>
    a *o D <= D \<otimes> C"
  by (auto simp add: elt_set_times_def set_times_def mult_ac)

lemma set_times_mono5: "a:C ==> B <= D ==> a *o B <= C \<otimes> D"
  apply (subgoal_tac "a *o B <= a *o D")
   apply (erule order_trans)
   apply (erule set_times_mono3)
  apply (erule set_times_mono)
  done

lemma set_times_mono_b: "C <= D ==> x : a *o C
    ==> x : a *o D"
  apply (frule set_times_mono)
  apply auto
  done

lemma set_times_mono2_b: "C <= D ==> E <= F ==> x : C \<otimes> E ==>
    x : D \<otimes> F"
  apply (frule set_times_mono2)
   prefer 2
   apply force
  apply assumption
  done

lemma set_times_mono3_b: "a : C ==> x : a *o D ==> x : C \<otimes> D"
  apply (frule set_times_mono3)
  apply auto
  done

lemma set_times_mono4_b: "(a::'a::comm_monoid_mult) : C ==>
    x : a *o D ==> x : D \<otimes> C"
  apply (frule set_times_mono4)
  apply auto
  done

lemma set_one_times [simp]: "(1::'a::comm_monoid_mult) *o C = C"
  by (auto simp add: elt_set_times_def)

lemma set_times_plus_distrib: "(a::'a::semiring) *o (b +o C)=
    (a * b) +o (a *o C)"
  by (auto simp add: elt_set_plus_def elt_set_times_def ring_distribs)

lemma set_times_plus_distrib2: "(a::'a::semiring) *o (B \<oplus> C) =
    (a *o B) \<oplus> (a *o C)"
  apply (auto simp add: set_plus_def elt_set_times_def ring_distribs)
   apply blast
  apply (rule_tac x = "b + bb" in exI)
  apply (auto simp add: ring_distribs)
  done

lemma set_times_plus_distrib3: "((a::'a::semiring) +o C) \<otimes> D <=
    a *o D \<oplus> C \<otimes> D"
  apply (auto intro!: subsetI simp add:
    elt_set_plus_def elt_set_times_def set_times_def
    set_plus_def ring_distribs)
  apply auto
  done

theorems set_times_plus_distribs =
  set_times_plus_distrib
  set_times_plus_distrib2

lemma set_neg_intro: "(a::'a::ring_1) : (- 1) *o C ==>
    - a : C"
  by (auto simp add: elt_set_times_def)

lemma set_neg_intro2: "(a::'a::ring_1) : C ==>
    - a : (- 1) *o C"
  by (auto simp add: elt_set_times_def)

end
