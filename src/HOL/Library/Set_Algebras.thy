(*  Title:      HOL/Library/Set_Algebras.thy
    Author:     Jeremy Avigad and Kevin Donnelly; Florian Haftmann, TUM
*)

header {* Algebraic operations on sets *}

theory Set_Algebras
imports Main
begin

text {*
  This library lifts operations like addition and muliplication to
  sets.  It was designed to support asymptotic calculations. See the
  comments at the top of theory @{text BigO}.
*}

instantiation set :: (plus) plus
begin

definition plus_set :: "'a::plus set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  set_plus_def: "A + B = {c. \<exists>a\<in>A. \<exists>b\<in>B. c = a + b}"

instance ..

end

instantiation set :: (times) times
begin

definition times_set :: "'a::times set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  set_times_def: "A * B = {c. \<exists>a\<in>A. \<exists>b\<in>B. c = a * b}"

instance ..

end


text {* Legacy syntax: *}

abbreviation (input) set_plus :: "'a::plus set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<oplus>" 65) where
  "A \<oplus> B \<equiv> A + B"
abbreviation (input) set_times :: "'a::times set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<otimes>" 70) where
  "A \<otimes> B \<equiv> A * B"

instantiation set :: (zero) zero
begin

definition
  set_zero[simp]: "0::('a::zero)set == {0}"

instance ..

end
 
instantiation set :: (one) one
begin

definition
  set_one[simp]: "1::('a::one)set == {1}"

instance ..

end

definition elt_set_plus :: "'a::plus \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl "+o" 70) where
  "a +o B = {c. \<exists>b\<in>B. c = a + b}"

definition elt_set_times :: "'a::times \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl "*o" 80) where
  "a *o B = {c. \<exists>b\<in>B. c = a * b}"

abbreviation (input) elt_set_eq :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infix "=o" 50) where
  "x =o A \<equiv> x \<in> A"

instance set :: (semigroup_add) semigroup_add
by default (force simp add: set_plus_def add.assoc)

instance set :: (ab_semigroup_add) ab_semigroup_add
by default (force simp add: set_plus_def add.commute)

instance set :: (monoid_add) monoid_add
by default (simp_all add: set_plus_def)

instance set :: (comm_monoid_add) comm_monoid_add
by default (simp_all add: set_plus_def)

instance set :: (semigroup_mult) semigroup_mult
by default (force simp add: set_times_def mult.assoc)

instance set :: (ab_semigroup_mult) ab_semigroup_mult
by default (force simp add: set_times_def mult.commute)

instance set :: (monoid_mult) monoid_mult
by default (simp_all add: set_times_def)

instance set :: (comm_monoid_mult) comm_monoid_mult
by default (simp_all add: set_times_def)

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
  apply (auto simp add: elt_set_plus_def set_plus_def add_ac)
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
  apply (auto simp add: set_plus_def)
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
  apply (auto simp add: elt_set_times_def set_times_def
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
  apply (auto simp add:
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

lemma set_plus_image:
  fixes S T :: "'n::semigroup_add set" shows "S \<oplus> T = (\<lambda>(x, y). x + y) ` (S \<times> T)"
  unfolding set_plus_def by (fastforce simp: image_iff)

text {* Legacy syntax: *}

abbreviation (input) setsum_set :: "('b \<Rightarrow> ('a::comm_monoid_add) set) \<Rightarrow> 'b set \<Rightarrow> 'a set" where
   "setsum_set == setsum"

lemma set_setsum_alt:
  assumes fin: "finite I"
  shows "setsum_set S I = {setsum s I |s. \<forall>i\<in>I. s i \<in> S i}"
    (is "_ = ?setsum I")
using fin proof induct
  case (insert x F)
  have "setsum_set S (insert x F) = S x \<oplus> ?setsum F"
    using insert.hyps by auto
  also have "...= {s x + setsum s F |s. \<forall> i\<in>insert x F. s i \<in> S i}"
    unfolding set_plus_def
  proof safe
    fix y s assume "y \<in> S x" "\<forall>i\<in>F. s i \<in> S i"
    then show "\<exists>s'. y + setsum s F = s' x + setsum s' F \<and> (\<forall>i\<in>insert x F. s' i \<in> S i)"
      using insert.hyps
      by (intro exI[of _ "\<lambda>i. if i \<in> F then s i else y"]) (auto simp add: set_plus_def)
  qed auto
  finally show ?case
    using insert.hyps by auto
qed auto

lemma setsum_set_cond_linear:
  fixes f :: "('a::comm_monoid_add) set \<Rightarrow> ('b::comm_monoid_add) set"
  assumes [intro!]: "\<And>A B. P A  \<Longrightarrow> P B  \<Longrightarrow> P (A \<oplus> B)" "P {0}"
    and f: "\<And>A B. P A  \<Longrightarrow> P B \<Longrightarrow> f (A \<oplus> B) = f A \<oplus> f B" "f {0} = {0}"
  assumes all: "\<And>i. i \<in> I \<Longrightarrow> P (S i)"
  shows "f (setsum_set S I) = setsum_set (f \<circ> S) I"
proof cases
  assume "finite I" from this all show ?thesis
  proof induct
    case (insert x F)
    from `finite F` `\<And>i. i \<in> insert x F \<Longrightarrow> P (S i)` have "P (setsum_set S F)"
      by induct auto
    with insert show ?case
      by (simp, subst f) auto
  qed (auto intro!: f)
qed (auto intro!: f)

lemma setsum_set_linear:
  fixes f :: "('a::comm_monoid_add) set => ('b::comm_monoid_add) set"
  assumes "\<And>A B. f(A) \<oplus> f(B) = f(A \<oplus> B)" "f {0} = {0}"
  shows "f (setsum_set S I) = setsum_set (f \<circ> S) I"
  using setsum_set_cond_linear[of "\<lambda>x. True" f I S] assms by auto

end
