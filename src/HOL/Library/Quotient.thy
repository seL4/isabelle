(*  Title:      HOL/Library/Quotient.thy
    ID:         $Id$
    Author:     Gertrud Bauer and Markus Wenzel, TU Muenchen
*)

header {*
  \title{Quotient types}
  \author{Gertrud Bauer and Markus Wenzel}
*}

theory Quotient = Main:

text {*
 We introduce the notion of quotient types over equivalence relations
 via axiomatic type classes.
*}

subsection {* Equivalence relations and quotient types *}

text {*
 \medskip Type class @{text equiv} models equivalence relations @{text
 "\<sim> :: 'a => 'a => bool"}.
*}

axclass eqv < "term"
consts
  eqv :: "('a::eqv) => 'a => bool"    (infixl "\<sim>" 50)

axclass equiv < eqv
  equiv_refl [intro]: "x \<sim> x"
  equiv_trans [trans]: "x \<sim> y ==> y \<sim> z ==> x \<sim> z"
  equiv_sym [elim?]: "x \<sim> y ==> y \<sim> x"

text {*
 \medskip The quotient type @{text "'a quot"} consists of all
 \emph{equivalence classes} over elements of the base type @{typ 'a}.
*}

typedef 'a quot = "{{x. a \<sim> x} | a::'a::eqv. True}"
  by blast

lemma quotI [intro]: "{x. a \<sim> x} \<in> quot"
  by (unfold quot_def) blast

lemma quotE [elim]: "R \<in> quot ==> (!!a. R = {x. a \<sim> x} ==> C) ==> C"
  by (unfold quot_def) blast

text {*
 \medskip Abstracted equivalence classes are the canonical
 representation of elements of a quotient type.
*}

constdefs
  equivalence_class :: "'a::equiv => 'a quot"    ("\<lfloor>_\<rfloor>")
  "\<lfloor>a\<rfloor> == Abs_quot {x. a \<sim> x}"

theorem quot_exhaust: "\<exists>a. A = \<lfloor>a\<rfloor>"
proof (cases A)
  fix R assume R: "A = Abs_quot R"
  assume "R \<in> quot" hence "\<exists>a. R = {x. a \<sim> x}" by blast
  with R have "\<exists>a. A = Abs_quot {x. a \<sim> x}" by blast
  thus ?thesis by (unfold equivalence_class_def)
qed

lemma quot_cases [cases type: quot]: "(!!a. A = \<lfloor>a\<rfloor> ==> C) ==> C"
  by (insert quot_exhaust) blast


subsection {* Equality on quotients *}

text {*
 Equality of canonical quotient elements coincides with the original
 relation.
*}

theorem equivalence_class_iff [iff?]: "(\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>) = (a \<sim> b)"
proof
  assume eq: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
  show "a \<sim> b"
  proof -
    from eq have "{x. a \<sim> x} = {x. b \<sim> x}"
      by (simp only: equivalence_class_def Abs_quot_inject quotI)
    moreover have "a \<sim> a" ..
    ultimately have "a \<in> {x. b \<sim> x}" by blast
    hence "b \<sim> a" by blast
    thus ?thesis ..
  qed
next
  assume ab: "a \<sim> b"
  show "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
  proof -
    have "{x. a \<sim> x} = {x. b \<sim> x}"
    proof (rule Collect_cong)
      fix x show "(a \<sim> x) = (b \<sim> x)"
      proof
        from ab have "b \<sim> a" ..
        also assume "a \<sim> x"
        finally show "b \<sim> x" .
      next
        note ab
        also assume "b \<sim> x"
        finally show "a \<sim> x" .
      qed
    qed
    thus ?thesis by (simp only: equivalence_class_def)
  qed
qed


subsection {* Picking representing elements *}

constdefs
  pick :: "'a::equiv quot => 'a"
  "pick A == SOME a. A = \<lfloor>a\<rfloor>"

theorem pick_equiv [intro]: "pick \<lfloor>a\<rfloor> \<sim> a"
proof (unfold pick_def)
  show "(SOME x. \<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>) \<sim> a"
  proof (rule someI2)
    show "\<lfloor>a\<rfloor> = \<lfloor>a\<rfloor>" ..
    fix x assume "\<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>"
    hence "a \<sim> x" .. thus "x \<sim> a" ..
  qed
qed

theorem pick_inverse: "\<lfloor>pick A\<rfloor> = A"
proof (cases A)
  fix a assume a: "A = \<lfloor>a\<rfloor>"
  hence "pick A \<sim> a" by (simp only: pick_equiv)
  hence "\<lfloor>pick A\<rfloor> = \<lfloor>a\<rfloor>" ..
  with a show ?thesis by simp
qed

text {*
 \medskip The following rules support canonical function definitions
 on quotient types.
*}

theorem quot_cond_function1:
  "(!!X. f X == g (pick X)) ==>
    (!!x x'. x \<sim> x' ==> P x ==> P x' ==> g x = g x') ==>
    (!!x x'. x \<sim> x' ==> P x = P x') ==>
  P a ==> f \<lfloor>a\<rfloor> = g a"
proof -
  assume cong_g: "!!x x'. x \<sim> x' ==> P x ==> P x' ==> g x = g x'"
  assume cong_P: "!!x x'. x \<sim> x' ==> P x = P x'"
  assume P: "P a"
  assume "!!X. f X == g (pick X)"
  hence "f \<lfloor>a\<rfloor> = g (pick \<lfloor>a\<rfloor>)" by (simp only:)
  also have "\<dots> = g a"
  proof (rule cong_g)
    show "pick \<lfloor>a\<rfloor> \<sim> a" ..
    hence "P (pick \<lfloor>a\<rfloor>) = P a" by (rule cong_P)
    also note P
    finally show "P (pick \<lfloor>a\<rfloor>)" .
  qed
  finally show ?thesis .
qed

theorem quot_function1:
  "(!!X. f X == g (pick X)) ==>
    (!!x x'. x \<sim> x' ==> g x = g x') ==>
    f \<lfloor>a\<rfloor> = g a"
proof -
  case antecedent from this refl TrueI
  show ?thesis by (rule quot_cond_function1)
qed

theorem quot_cond_operation1:
  "(!!X. f X == \<lfloor>g (pick X)\<rfloor>) ==>
    (!!x x'. x \<sim> x' ==> P x ==> P x' ==> g x \<sim> g x') ==>
    (!!x x'. x \<sim> x' ==> P x = P x') ==>
  P a ==> f \<lfloor>a\<rfloor> = \<lfloor>g a\<rfloor>"
proof -
  assume defn: "!!X. f X == \<lfloor>g (pick X)\<rfloor>"
  assume "!!x x'. x \<sim> x' ==> P x ==> P x' ==> g x \<sim> g x'"
  hence cong_g: "!!x x'. x \<sim> x' ==> P x ==> P x' ==> \<lfloor>g x\<rfloor> = \<lfloor>g x'\<rfloor>" ..
  assume "!!x x'. x \<sim> x' ==> P x = P x'" and "P a"
  with defn cong_g show ?thesis by (rule quot_cond_function1)
qed

theorem quot_operation1:
  "(!!X. f X == \<lfloor>g (pick X)\<rfloor>) ==>
    (!!x x'. x \<sim> x' ==> g x \<sim> g x') ==>
    f \<lfloor>a\<rfloor> = \<lfloor>g a\<rfloor>"
proof -
  case antecedent from this refl TrueI
  show ?thesis by (rule quot_cond_operation1)
qed

theorem quot_cond_function2:
  "(!!X Y. f X Y == g (pick X) (pick Y)) ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y ==> P x' y'
      ==> g x y = g x' y') ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y = P x' y') ==>
    P a b ==> f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
proof -
  assume cong_g: "!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y ==> P x' y'
    ==> g x y = g x' y'"
  assume cong_P: "!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y = P x' y'"
  assume P: "P a b"
  assume "!!X Y. f X Y == g (pick X) (pick Y)"
  hence "f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g (pick \<lfloor>a\<rfloor>) (pick \<lfloor>b\<rfloor>)" by (simp only:)
  also have "\<dots> = g a b"
  proof (rule cong_g)
    show "pick \<lfloor>a\<rfloor> \<sim> a" ..
    moreover show "pick \<lfloor>b\<rfloor> \<sim> b" ..
    ultimately have "P (pick \<lfloor>a\<rfloor>) (pick \<lfloor>b\<rfloor>) = P a b" by (rule cong_P)
    also show "P a b" .
    finally show "P (pick \<lfloor>a\<rfloor>) (pick \<lfloor>b\<rfloor>)" .
  qed
  finally show ?thesis .
qed

theorem quot_function2:
  "(!!X Y. f X Y == g (pick X) (pick Y)) ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> g x y = g x' y') ==>
    f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
proof -
  case antecedent from this refl TrueI
  show ?thesis by (rule quot_cond_function2)
qed

theorem quot_cond_operation2:
  "(!!X Y. f X Y == \<lfloor>g (pick X) (pick Y)\<rfloor>) ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y ==> P x' y'
      ==> g x y \<sim> g x' y') ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y = P x' y') ==>
    P a b ==> f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = \<lfloor>g a b\<rfloor>"
proof -
  assume defn: "!!X Y. f X Y == \<lfloor>g (pick X) (pick Y)\<rfloor>"
  assume "!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y ==> P x' y'
    ==> g x y \<sim> g x' y'"
  hence cong_g: "!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y ==> P x' y'
    ==> \<lfloor>g x y\<rfloor> = \<lfloor>g x' y'\<rfloor>" ..
  assume "!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> P x y = P x' y'" and "P a b"
  with defn cong_g show ?thesis by (rule quot_cond_function2)
qed

theorem quot_operation2:
  "(!!X Y. f X Y == \<lfloor>g (pick X) (pick Y)\<rfloor>) ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> g x y \<sim> g x' y') ==>
    f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = \<lfloor>g a b\<rfloor>"
proof -
  case antecedent from this refl TrueI
  show ?thesis by (rule quot_cond_operation2)
qed

text {*
 \medskip HOL's collection of overloaded standard operations is lifted
 to quotient types in the canonical manner.
*}

instance quot :: (zero) zero ..
instance quot :: (plus) plus ..
instance quot :: (minus) minus ..
instance quot :: (times) times ..
instance quot :: (inverse) inverse ..
instance quot :: (power) power ..
instance quot :: (number) number ..
instance quot :: (ord) ord ..

defs (overloaded)
  zero_quot_def: "0 == \<lfloor>0\<rfloor>"
  add_quot_def: "X + Y == \<lfloor>pick X + pick Y\<rfloor>"
  diff_quot_def: "X - Y == \<lfloor>pick X - pick Y\<rfloor>"
  minus_quot_def: "- X == \<lfloor>- pick X\<rfloor>"
  abs_quot_def: "abs X == \<lfloor>abs (pick X)\<rfloor>"
  mult_quot_def: "X * Y == \<lfloor>pick X * pick Y\<rfloor>"
  inverse_quot_def: "inverse X == \<lfloor>inverse (pick X)\<rfloor>"
  divide_quot_def: "X / Y == \<lfloor>pick X / pick Y\<rfloor>"
  power_quot_def: "X^n == \<lfloor>(pick X)^n\<rfloor>"
  number_of_quot_def: "number_of b == \<lfloor>number_of b\<rfloor>"
  le_quot_def: "X \<le> Y == pick X \<le> pick Y"
  less_quot_def: "X < Y == pick X < pick Y"

end
