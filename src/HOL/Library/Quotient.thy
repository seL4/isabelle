(*  Title:      HOL/Library/Quotient.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

header {*
  \title{Quotient types}
  \author{Markus Wenzel}
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

lemma not_equiv_sym [elim?]: "\<not> (x \<sim> y) ==> \<not> (y \<sim> (x::'a::equiv))"
proof -
  assume "\<not> (x \<sim> y)" thus "\<not> (y \<sim> x)"
    by (rule contrapos_nn) (rule equiv_sym)
qed

lemma not_equiv_trans1 [trans]: "\<not> (x \<sim> y) ==> y \<sim> z ==> \<not> (x \<sim> (z::'a::equiv))"
proof -
  assume "\<not> (x \<sim> y)" and yz: "y \<sim> z"
  show "\<not> (x \<sim> z)"
  proof
    assume "x \<sim> z"
    also from yz have "z \<sim> y" ..
    finally have "x \<sim> y" .
    thus False by contradiction
  qed
qed

lemma not_equiv_trans2 [trans]: "x \<sim> y ==> \<not> (y \<sim> z) ==> \<not> (x \<sim> (z::'a::equiv))"
proof -
  assume "\<not> (y \<sim> z)" hence "\<not> (z \<sim> y)" ..
  also assume "x \<sim> y" hence "y \<sim> x" ..
  finally have "\<not> (z \<sim> x)" . thus "(\<not> x \<sim> z)" ..
qed

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

theorem quot_equality: "(\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>) = (a \<sim> b)"
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

lemma quot_equalI [intro?]: "a \<sim> b ==> \<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
  by (simp only: quot_equality)

lemma quot_equalD [dest?]: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> ==> a \<sim> b"
  by (simp only: quot_equality)

lemma quot_not_equalI [intro?]: "\<not> (a \<sim> b) ==> \<lfloor>a\<rfloor> \<noteq> \<lfloor>b\<rfloor>"
  by (simp add: quot_equality)

lemma quot_not_equalD [dest?]: "\<lfloor>a\<rfloor> \<noteq> \<lfloor>b\<rfloor> ==> \<not> (a \<sim> b)"
  by (simp add: quot_equality)


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

theorem pick_inverse [intro]: "\<lfloor>pick A\<rfloor> = A"
proof (cases A)
  fix a assume a: "A = \<lfloor>a\<rfloor>"
  hence "pick A \<sim> a" by (simp only: pick_equiv)
  hence "\<lfloor>pick A\<rfloor> = \<lfloor>a\<rfloor>" ..
  with a show ?thesis by simp
qed

text {*
 \medskip The following rules support canonical function definitions
 on quotient types (with up to two arguments).  Note that the
 stripped-down version without additional conditions is sufficient
 most of the time.
*}

theorem quot_cond_function:
  "(!!X Y. P X Y ==> f X Y == g (pick X) (pick Y)) ==>
    (!!x x' y y'. \<lfloor>x\<rfloor> = \<lfloor>x'\<rfloor> ==> \<lfloor>y\<rfloor> = \<lfloor>y'\<rfloor>
      ==> P \<lfloor>x\<rfloor> \<lfloor>y\<rfloor> ==> P \<lfloor>x'\<rfloor> \<lfloor>y'\<rfloor> ==> g x y = g x' y') ==>
    P \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> ==> f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
  (is "PROP ?eq ==> PROP ?cong ==> _ ==> _")
proof -
  assume cong: "PROP ?cong"
  assume "PROP ?eq" and "P \<lfloor>a\<rfloor> \<lfloor>b\<rfloor>"
  hence "f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g (pick \<lfloor>a\<rfloor>) (pick \<lfloor>b\<rfloor>)" by (simp only:)
  also have "\<dots> = g a b"
  proof (rule cong)
    show "\<lfloor>pick \<lfloor>a\<rfloor>\<rfloor> = \<lfloor>a\<rfloor>" ..
    moreover
    show "\<lfloor>pick \<lfloor>b\<rfloor>\<rfloor> = \<lfloor>b\<rfloor>" ..
    moreover
    show "P \<lfloor>a\<rfloor> \<lfloor>b\<rfloor>" .
    ultimately show "P \<lfloor>pick \<lfloor>a\<rfloor>\<rfloor> \<lfloor>pick \<lfloor>b\<rfloor>\<rfloor>" by (simp only:)
  qed
  finally show ?thesis .
qed

theorem quot_function:
  "(!!X Y. f X Y == g (pick X) (pick Y)) ==>
    (!!x x' y y'. \<lfloor>x\<rfloor> = \<lfloor>x'\<rfloor> ==> \<lfloor>y\<rfloor> = \<lfloor>y'\<rfloor> ==> g x y = g x' y') ==>
    f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
proof -
  case antecedent from this TrueI
  show ?thesis by (rule quot_cond_function)
qed

theorem quot_function':
  "(!!X Y. f X Y == g (pick X) (pick Y)) ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> g x y = g x' y') ==>
    f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
  by  (rule quot_function) (simp only: quot_equality)+

end
