(*  Title:      HOL/Library/Quotient.thy
    ID:         $Id$
    Author:     Gertrud Bauer and Markus Wenzel, TU Muenchen
*)

header {*
  \title{Quotients}
  \author{Gertrud Bauer and Markus Wenzel}
*}

theory Quotient = Main:

text {*
 We introduce the notion of quotient types over equivalence relations
 via axiomatic type classes.
*}

subsection {* Equivalence relations and quotient types *}

text {*
 \medskip Type class @{text equiv} models equivalence relations using
 the polymorphic @{text "\<sim> :: 'a => 'a => bool"} relation.
*}

axclass eqv < "term"
consts
  eqv :: "('a::eqv) => 'a => bool"    (infixl "\<sim>" 50)

axclass equiv < eqv
  eqv_refl [intro]: "x \<sim> x"
  eqv_trans [trans]: "x \<sim> y ==> y \<sim> z ==> x \<sim> z"
  eqv_sym [elim?]: "x \<sim> y ==> y \<sim> x"

text {*
 \medskip The quotient type @{text "'a quot"} consists of all
 \emph{equivalence classes} over elements of the base type @{typ 'a}.
*}

typedef 'a quot = "{{x. a \<sim> x}| a::'a::eqv. True}"
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

theorem quot_rep: "\<exists>a. A = \<lfloor>a\<rfloor>"
proof (cases A)
  fix R assume R: "A = Abs_quot R"
  assume "R \<in> quot" hence "\<exists>a. R = {x. a \<sim> x}" by blast
  with R have "\<exists>a. A = Abs_quot {x. a \<sim> x}" by blast
  thus ?thesis by (unfold equivalence_class_def)
qed

lemma quot_cases [case_names rep, cases type: quot]:
    "(!!a. A = \<lfloor>a\<rfloor> ==> C) ==> C"
  by (insert quot_rep) blast


subsection {* Equality on quotients *}

text {*
 Equality of canonical quotient elements coincides with the original
 relation.
*}

theorem equivalence_class_eq [iff?]: "(\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>) = (a \<sim> b)"
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

theorem cong_definition1:
  "(!!X. f X == g (pick X)) ==>
    (!!x x'. x \<sim> x' ==> g x = g x') ==>
    f \<lfloor>a\<rfloor> = g a"
proof -
  assume cong: "!!x x'. x \<sim> x' ==> g x = g x'"
  assume "!!X. f X == g (pick X)"
  hence "f \<lfloor>a\<rfloor> = g (pick \<lfloor>a\<rfloor>)" by (simp only:)
  also have "\<dots> = g a"
  proof (rule cong)
    show "pick \<lfloor>a\<rfloor> \<sim> a" ..
  qed
  finally show ?thesis .
qed

theorem cong_definition2:
  "(!!X Y. f X Y == g (pick X) (pick Y)) ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> g x y = g x' y') ==>
    f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
proof -
  assume cong: "!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> g x y = g x' y'"
  assume "!!X Y. f X Y == g (pick X) (pick Y)"
  hence "f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g (pick \<lfloor>a\<rfloor>) (pick \<lfloor>b\<rfloor>)" by (simp only:)
  also have "\<dots> = g a b"
  proof (rule cong)
    show "pick \<lfloor>a\<rfloor> \<sim> a" ..
    show "pick \<lfloor>b\<rfloor> \<sim> b" ..
  qed
  finally show ?thesis .
qed

end
