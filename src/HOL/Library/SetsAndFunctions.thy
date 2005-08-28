(*  Title:      HOL/Library/SetsAndFunctions.thy
    ID:		$Id$
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

instance set :: (plus) plus ..
instance fun :: (type, plus) plus ..

defs (overloaded)
  func_plus: "f + g == (%x. f x + g x)"
  set_plus: "A + B == {c. EX a:A. EX b:B. c = a + b}"

instance set :: (times) times ..
instance fun :: (type, times) times ..

defs (overloaded)
  func_times: "f * g == (%x. f x * g x)" 
  set_times:"A * B == {c. EX a:A. EX b:B. c = a * b}"

instance fun :: (type, minus) minus ..

defs (overloaded)
  func_minus: "- f == (%x. - f x)"
  func_diff: "f - g == %x. f x - g x"                 

instance fun :: (type, zero) zero ..
instance set :: (zero) zero ..

defs (overloaded)
  func_zero: "0::(('a::type) => ('b::zero)) == %x. 0"
  set_zero: "0::('a::zero)set == {0}"

instance fun :: (type, one) one ..
instance set :: (one) one ..

defs (overloaded)
  func_one: "1::(('a::type) => ('b::one)) == %x. 1"
  set_one: "1::('a::one)set == {1}"

constdefs 
  elt_set_plus :: "'a::plus => 'a set => 'a set"    (infixl "+o" 70)
  "a +o B == {c. EX b:B. c = a + b}"

  elt_set_times :: "'a::times => 'a set => 'a set"  (infixl "*o" 80)
  "a *o B == {c. EX b:B. c = a * b}"

syntax
  "elt_set_eq" :: "'a => 'a set => bool"      (infix "=o" 50)

translations
  "x =o A" => "x : A"

instance fun :: (type,semigroup_add)semigroup_add
  apply intro_classes
  apply (auto simp add: func_plus add_assoc)
done

instance fun :: (type,comm_monoid_add)comm_monoid_add
  apply intro_classes
  apply (auto simp add: func_zero func_plus add_ac)
done

instance fun :: (type,ab_group_add)ab_group_add
  apply intro_classes
  apply (simp add: func_minus func_plus func_zero)
  apply (simp add: func_minus func_plus func_diff diff_minus)
done

instance fun :: (type,semigroup_mult)semigroup_mult
  apply intro_classes
  apply (auto simp add: func_times mult_assoc)
done

instance fun :: (type,comm_monoid_mult)comm_monoid_mult
  apply intro_classes
  apply (auto simp add: func_one func_times mult_ac)
done

instance fun :: (type,comm_ring_1)comm_ring_1
  apply intro_classes
  apply (auto simp add: func_plus func_times func_minus func_diff ext 
    func_one func_zero ring_eq_simps) 
  apply (drule fun_cong)
  apply simp
done

instance set :: (semigroup_add)semigroup_add
  apply intro_classes
  apply (unfold set_plus)
  apply (force simp add: add_assoc)
done

instance set :: (semigroup_mult)semigroup_mult
  apply intro_classes
  apply (unfold set_times)
  apply (force simp add: mult_assoc)
done

instance set :: (comm_monoid_add)comm_monoid_add
  apply intro_classes
  apply (unfold set_plus)
  apply (force simp add: add_ac)
  apply (unfold set_zero)
  apply force
done

instance set :: (comm_monoid_mult)comm_monoid_mult
  apply intro_classes
  apply (unfold set_times)
  apply (force simp add: mult_ac)
  apply (unfold set_one)
  apply force
done

subsection {* Basic properties *}

lemma set_plus_intro [intro]: "a : C ==> b : D ==> a + b : C + D" 
by (auto simp add: set_plus)

lemma set_plus_intro2 [intro]: "b : C ==> a + b : a +o C"
by (auto simp add: elt_set_plus_def)

lemma set_plus_rearrange: "((a::'a::comm_monoid_add) +o C) + 
  (b +o D) = (a + b) +o (C + D)"
  apply (auto simp add: elt_set_plus_def set_plus add_ac)
  apply (rule_tac x = "ba + bb" in exI)
  apply (auto simp add: add_ac)
  apply (rule_tac x = "aa + a" in exI)
  apply (auto simp add: add_ac)
done

lemma set_plus_rearrange2: "(a::'a::semigroup_add) +o (b +o C) = 
  (a + b) +o C"
by (auto simp add: elt_set_plus_def add_assoc)

lemma set_plus_rearrange3: "((a::'a::semigroup_add) +o B) + C = 
  a +o (B + C)"
  apply (auto simp add: elt_set_plus_def set_plus)
  apply (blast intro: add_ac)
  apply (rule_tac x = "a + aa" in exI)
  apply (rule conjI)
  apply (rule_tac x = "aa" in bexI)
  apply auto
  apply (rule_tac x = "ba" in bexI)
  apply (auto simp add: add_ac)
done

theorem set_plus_rearrange4: "C + ((a::'a::comm_monoid_add) +o D) = 
    a +o (C + D)" 
  apply (auto intro!: subsetI simp add: elt_set_plus_def set_plus add_ac)
  apply (rule_tac x = "aa + ba" in exI)
  apply (auto simp add: add_ac)
done

theorems set_plus_rearranges = set_plus_rearrange set_plus_rearrange2
  set_plus_rearrange3 set_plus_rearrange4

lemma set_plus_mono [intro!]: "C <= D ==> a +o C <= a +o D"
by (auto simp add: elt_set_plus_def)

lemma set_plus_mono2 [intro]: "(C::('a::plus) set) <= D ==> E <= F ==> 
    C + E <= D + F"
by (auto simp add: set_plus)

lemma set_plus_mono3 [intro]: "a : C ==> a +o D <= C + D"
by (auto simp add: elt_set_plus_def set_plus)

lemma set_plus_mono4 [intro]: "(a::'a::comm_monoid_add) : C ==> 
  a +o D <= D + C" 
by (auto simp add: elt_set_plus_def set_plus add_ac)

lemma set_plus_mono5: "a:C ==> B <= D ==> a +o B <= C + D"
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

lemma set_plus_mono2_b: "C <= D ==> E <= F ==> x : C + E ==> 
    x : D + F"
  apply (frule set_plus_mono2)
  prefer 2
  apply force
  apply assumption
done

lemma set_plus_mono3_b: "a : C ==> x : a +o D ==> x : C + D"
  apply (frule set_plus_mono3)
  apply auto
done

lemma set_plus_mono4_b: "(a::'a::comm_monoid_add) : C ==> 
  x : a +o D ==> x : D + C" 
  apply (frule set_plus_mono4)
  apply auto
done

lemma set_zero_plus [simp]: "(0::'a::comm_monoid_add) +o C = C"
by (auto simp add: elt_set_plus_def)

lemma set_zero_plus2: "(0::'a::comm_monoid_add) : A ==> B <= A + B"
  apply (auto intro!: subsetI simp add: set_plus)
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

lemma set_times_intro [intro]: "a : C ==> b : D ==> a * b : C * D" 
by (auto simp add: set_times)

lemma set_times_intro2 [intro!]: "b : C ==> a * b : a *o C"
by (auto simp add: elt_set_times_def)

lemma set_times_rearrange: "((a::'a::comm_monoid_mult) *o C) * 
  (b *o D) = (a * b) *o (C * D)"
  apply (auto simp add: elt_set_times_def set_times)
  apply (rule_tac x = "ba * bb" in exI)
  apply (auto simp add: mult_ac)
  apply (rule_tac x = "aa * a" in exI)
  apply (auto simp add: mult_ac)
done

lemma set_times_rearrange2: "(a::'a::semigroup_mult) *o (b *o C) = 
  (a * b) *o C"
by (auto simp add: elt_set_times_def mult_assoc)

lemma set_times_rearrange3: "((a::'a::semigroup_mult) *o B) * C = 
  a *o (B * C)"
  apply (auto simp add: elt_set_times_def set_times)
  apply (blast intro: mult_ac)
  apply (rule_tac x = "a * aa" in exI)
  apply (rule conjI)
  apply (rule_tac x = "aa" in bexI)
  apply auto
  apply (rule_tac x = "ba" in bexI)
  apply (auto simp add: mult_ac)
done

theorem set_times_rearrange4: "C * ((a::'a::comm_monoid_mult) *o D) = 
    a *o (C * D)" 
  apply (auto intro!: subsetI simp add: elt_set_times_def set_times 
    mult_ac)
  apply (rule_tac x = "aa * ba" in exI)
  apply (auto simp add: mult_ac)
done

theorems set_times_rearranges = set_times_rearrange set_times_rearrange2
  set_times_rearrange3 set_times_rearrange4

lemma set_times_mono [intro]: "C <= D ==> a *o C <= a *o D"
by (auto simp add: elt_set_times_def)

lemma set_times_mono2 [intro]: "(C::('a::times) set) <= D ==> E <= F ==> 
    C * E <= D * F"
by (auto simp add: set_times)

lemma set_times_mono3 [intro]: "a : C ==> a *o D <= C * D"
by (auto simp add: elt_set_times_def set_times)

lemma set_times_mono4 [intro]: "(a::'a::comm_monoid_mult) : C ==> 
  a *o D <= D * C" 
by (auto simp add: elt_set_times_def set_times mult_ac)

lemma set_times_mono5: "a:C ==> B <= D ==> a *o B <= C * D"
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

lemma set_times_mono2_b: "C <= D ==> E <= F ==> x : C * E ==> 
    x : D * F"
  apply (frule set_times_mono2)
  prefer 2
  apply force
  apply assumption
done

lemma set_times_mono3_b: "a : C ==> x : a *o D ==> x : C * D"
  apply (frule set_times_mono3)
  apply auto
done

lemma set_times_mono4_b: "(a::'a::comm_monoid_mult) : C ==> 
  x : a *o D ==> x : D * C" 
  apply (frule set_times_mono4)
  apply auto
done

lemma set_one_times [simp]: "(1::'a::comm_monoid_mult) *o C = C"
by (auto simp add: elt_set_times_def)

lemma set_times_plus_distrib: "(a::'a::semiring) *o (b +o C)= 
  (a * b) +o (a *o C)"
by (auto simp add: elt_set_plus_def elt_set_times_def ring_distrib)

lemma set_times_plus_distrib2: "(a::'a::semiring) *o (B + C) = 
  (a *o B) + (a *o C)"
  apply (auto simp add: set_plus elt_set_times_def ring_distrib)
  apply blast
  apply (rule_tac x = "b + bb" in exI)
  apply (auto simp add: ring_distrib)
done

lemma set_times_plus_distrib3: "((a::'a::semiring) +o C) * D <= 
    a *o D + C * D"
  apply (auto intro!: subsetI simp add: 
    elt_set_plus_def elt_set_times_def set_times 
    set_plus ring_distrib)
  apply auto
done

theorems set_times_plus_distribs = set_times_plus_distrib
  set_times_plus_distrib2

lemma set_neg_intro: "(a::'a::ring_1) : (- 1) *o C ==> 
    - a : C" 
by (auto simp add: elt_set_times_def)

lemma set_neg_intro2: "(a::'a::ring_1) : C ==>
    - a : (- 1) *o C"
by (auto simp add: elt_set_times_def)
  
end
