(*  Title:      HOL/Library/Quotient_Type.thy
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Quotient types *}

theory Quotient_Type
imports Main
begin

text {*
 We introduce the notion of quotient types over equivalence relations
 via type classes.
*}

subsection {* Equivalence relations and quotient types *}

text {*
 \medskip Type class @{text equiv} models equivalence relations @{text
 "\<sim> :: 'a => 'a => bool"}.
*}

class eqv =
  fixes eqv :: "'a \<Rightarrow> 'a \<Rightarrow> bool"    (infixl "\<sim>" 50)

class equiv = eqv +
  assumes equiv_refl [intro]: "x \<sim> x"
  assumes equiv_trans [trans]: "x \<sim> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<sim> z"
  assumes equiv_sym [sym]: "x \<sim> y \<Longrightarrow> y \<sim> x"

lemma equiv_not_sym [sym]: "\<not> (x \<sim> y) ==> \<not> (y \<sim> (x::'a::equiv))"
proof -
  assume "\<not> (x \<sim> y)" then show "\<not> (y \<sim> x)"
    by (rule contrapos_nn) (rule equiv_sym)
qed

lemma not_equiv_trans1 [trans]: "\<not> (x \<sim> y) ==> y \<sim> z ==> \<not> (x \<sim> (z::'a::equiv))"
proof -
  assume "\<not> (x \<sim> y)" and "y \<sim> z"
  show "\<not> (x \<sim> z)"
  proof
    assume "x \<sim> z"
    also from `y \<sim> z` have "z \<sim> y" ..
    finally have "x \<sim> y" .
    with `\<not> (x \<sim> y)` show False by contradiction
  qed
qed

lemma not_equiv_trans2 [trans]: "x \<sim> y ==> \<not> (y \<sim> z) ==> \<not> (x \<sim> (z::'a::equiv))"
proof -
  assume "\<not> (y \<sim> z)" then have "\<not> (z \<sim> y)" ..
  also assume "x \<sim> y" then have "y \<sim> x" ..
  finally have "\<not> (z \<sim> x)" . then show "(\<not> x \<sim> z)" ..
qed

text {*
 \medskip The quotient type @{text "'a quot"} consists of all
 \emph{equivalence classes} over elements of the base type @{typ 'a}.
*}

definition "quot = {{x. a \<sim> x} | a::'a::eqv. True}"

typedef (open) 'a quot = "quot :: 'a::eqv set set"
  unfolding quot_def by blast

lemma quotI [intro]: "{x. a \<sim> x} \<in> quot"
  unfolding quot_def by blast

lemma quotE [elim]: "R \<in> quot ==> (!!a. R = {x. a \<sim> x} ==> C) ==> C"
  unfolding quot_def by blast

text {*
 \medskip Abstracted equivalence classes are the canonical
 representation of elements of a quotient type.
*}

definition
  "class" :: "'a::equiv => 'a quot"  ("\<lfloor>_\<rfloor>") where
  "\<lfloor>a\<rfloor> = Abs_quot {x. a \<sim> x}"

theorem quot_exhaust: "\<exists>a. A = \<lfloor>a\<rfloor>"
proof (cases A)
  fix R assume R: "A = Abs_quot R"
  assume "R \<in> quot" then have "\<exists>a. R = {x. a \<sim> x}" by blast
  with R have "\<exists>a. A = Abs_quot {x. a \<sim> x}" by blast
  then show ?thesis unfolding class_def .
qed

lemma quot_cases [cases type: quot]: "(!!a. A = \<lfloor>a\<rfloor> ==> C) ==> C"
  using quot_exhaust by blast


subsection {* Equality on quotients *}

text {*
 Equality of canonical quotient elements coincides with the original
 relation.
*}

theorem quot_equality [iff?]: "(\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>) = (a \<sim> b)"
proof
  assume eq: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
  show "a \<sim> b"
  proof -
    from eq have "{x. a \<sim> x} = {x. b \<sim> x}"
      by (simp only: class_def Abs_quot_inject quotI)
    moreover have "a \<sim> a" ..
    ultimately have "a \<in> {x. b \<sim> x}" by blast
    then have "b \<sim> a" by blast
    then show ?thesis ..
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
    then show ?thesis by (simp only: class_def)
  qed
qed


subsection {* Picking representing elements *}

definition
  pick :: "'a::equiv quot => 'a" where
  "pick A = (SOME a. A = \<lfloor>a\<rfloor>)"

theorem pick_equiv [intro]: "pick \<lfloor>a\<rfloor> \<sim> a"
proof (unfold pick_def)
  show "(SOME x. \<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>) \<sim> a"
  proof (rule someI2)
    show "\<lfloor>a\<rfloor> = \<lfloor>a\<rfloor>" ..
    fix x assume "\<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>"
    then have "a \<sim> x" .. then show "x \<sim> a" ..
  qed
qed

theorem pick_inverse [intro]: "\<lfloor>pick A\<rfloor> = A"
proof (cases A)
  fix a assume a: "A = \<lfloor>a\<rfloor>"
  then have "pick A \<sim> a" by (simp only: pick_equiv)
  then have "\<lfloor>pick A\<rfloor> = \<lfloor>a\<rfloor>" ..
  with a show ?thesis by simp
qed

text {*
 \medskip The following rules support canonical function definitions
 on quotient types (with up to two arguments).  Note that the
 stripped-down version without additional conditions is sufficient
 most of the time.
*}

theorem quot_cond_function:
  assumes eq: "!!X Y. P X Y ==> f X Y == g (pick X) (pick Y)"
    and cong: "!!x x' y y'. \<lfloor>x\<rfloor> = \<lfloor>x'\<rfloor> ==> \<lfloor>y\<rfloor> = \<lfloor>y'\<rfloor>
      ==> P \<lfloor>x\<rfloor> \<lfloor>y\<rfloor> ==> P \<lfloor>x'\<rfloor> \<lfloor>y'\<rfloor> ==> g x y = g x' y'"
    and P: "P \<lfloor>a\<rfloor> \<lfloor>b\<rfloor>"
  shows "f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
proof -
  from eq and P have "f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g (pick \<lfloor>a\<rfloor>) (pick \<lfloor>b\<rfloor>)" by (simp only:)
  also have "... = g a b"
  proof (rule cong)
    show "\<lfloor>pick \<lfloor>a\<rfloor>\<rfloor> = \<lfloor>a\<rfloor>" ..
    moreover
    show "\<lfloor>pick \<lfloor>b\<rfloor>\<rfloor> = \<lfloor>b\<rfloor>" ..
    moreover
    show "P \<lfloor>a\<rfloor> \<lfloor>b\<rfloor>" by (rule P)
    ultimately show "P \<lfloor>pick \<lfloor>a\<rfloor>\<rfloor> \<lfloor>pick \<lfloor>b\<rfloor>\<rfloor>" by (simp only:)
  qed
  finally show ?thesis .
qed

theorem quot_function:
  assumes "!!X Y. f X Y == g (pick X) (pick Y)"
    and "!!x x' y y'. \<lfloor>x\<rfloor> = \<lfloor>x'\<rfloor> ==> \<lfloor>y\<rfloor> = \<lfloor>y'\<rfloor> ==> g x y = g x' y'"
  shows "f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
  using assms and TrueI
  by (rule quot_cond_function)

theorem quot_function':
  "(!!X Y. f X Y == g (pick X) (pick Y)) ==>
    (!!x x' y y'. x \<sim> x' ==> y \<sim> y' ==> g x y = g x' y') ==>
    f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
  by (rule quot_function) (simp_all only: quot_equality)

end
