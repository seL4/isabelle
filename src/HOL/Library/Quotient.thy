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
 Higher-order quotients are defined over partial equivalence relations
 (PERs) instead of total ones.  We provide axiomatic type classes
 @{text "equiv < partial_equiv"} and a type constructor
 @{text "'a quot"} with basic operations.  Note that conventional
 quotient constructions emerge as a special case.  This development is
 loosely based on \cite{Slotosch:1997}.
*}


subsection {* Equivalence relations *}

subsubsection {* Partial equivalence *}

text {*
 Type class @{text partial_equiv} models partial equivalence relations
 (PERs) using the polymorphic @{text "\<sim> :: 'a => 'a => bool"} relation,
 which is required to be symmetric and transitive, but not necessarily
 reflexive.
*}

consts
  eqv :: "'a => 'a => bool"    (infixl "\<sim>" 50)

axclass partial_equiv < "term"
  eqv_sym [elim?]: "x \<sim> y ==> y \<sim> x"
  eqv_trans [trans]: "x \<sim> y ==> y \<sim> z ==> x \<sim> z"

text {*
 \medskip The domain of a partial equivalence relation is the set of
 reflexive elements.  Due to symmetry and transitivity this
 characterizes exactly those elements that are connected with
 \emph{any} other one.
*}

constdefs
  domain :: "'a::partial_equiv set"
  "domain == {x. x \<sim> x}"

lemma domainI [intro]: "x \<sim> x ==> x \<in> domain"
  by (unfold domain_def) blast

lemma domainD [dest]: "x \<in> domain ==> x \<sim> x"
  by (unfold domain_def) blast

theorem domainI' [elim?]: "x \<sim> y ==> x \<in> domain"
proof
  assume xy: "x \<sim> y"
  also from xy have "y \<sim> x" ..
  finally show "x \<sim> x" .
qed


subsubsection {* Equivalence on function spaces *}

text {*
 The @{text \<sim>} relation is lifted to function spaces.  It is
 important to note that this is \emph{not} the direct product, but a
 structural one corresponding to the congruence property.
*}

defs (overloaded)
  eqv_fun_def: "f \<sim> g == \<forall>x \<in> domain. \<forall>y \<in> domain. x \<sim> y --> f x \<sim> g y"

lemma partial_equiv_funI [intro?]:
    "(!!x y. x \<in> domain ==> y \<in> domain ==> x \<sim> y ==> f x \<sim> g y) ==> f \<sim> g"
  by (unfold eqv_fun_def) blast

lemma partial_equiv_funD [dest?]:
    "f \<sim> g ==> x \<in> domain ==> y \<in> domain ==> x \<sim> y ==> f x \<sim> g y"
  by (unfold eqv_fun_def) blast

text {*
 The class of partial equivalence relations is closed under function
 spaces (in \emph{both} argument positions).
*}

instance fun :: (partial_equiv, partial_equiv) partial_equiv
proof intro_classes
  fix f g h :: "'a::partial_equiv => 'b::partial_equiv"
  assume fg: "f \<sim> g"
  show "g \<sim> f"
  proof
    fix x y :: 'a
    assume x: "x \<in> domain" and y: "y \<in> domain"
    assume "x \<sim> y" hence "y \<sim> x" ..
    with fg y x have "f y \<sim> g x" ..
    thus "g x \<sim> f y" ..
  qed
  assume gh: "g \<sim> h"
  show "f \<sim> h"
  proof
    fix x y :: 'a
    assume x: "x \<in> domain" and y: "y \<in> domain" and "x \<sim> y"
    with fg have "f x \<sim> g y" ..
    also from y have "y \<sim> y" ..
    with gh y y have "g y \<sim> h y" ..
    finally show "f x \<sim> h y" .
  qed
qed


subsubsection {* Total equivalence *}

text {*
 The class of total equivalence relations on top of PERs.  It
 coincides with the standard notion of equivalence, i.e.\
 @{text "\<sim> :: 'a => 'a => bool"} is required to be reflexive, transitive
 and symmetric.
*}

axclass equiv < partial_equiv
  eqv_refl [intro]: "x \<sim> x"

text {*
 On total equivalences all elements are reflexive, and congruence
 holds unconditionally.
*}

theorem equiv_domain [intro]: "(x::'a::equiv) \<in> domain"
proof
  show "x \<sim> x" ..
qed

theorem equiv_cong [dest?]: "f \<sim> g ==> x \<sim> y ==> f x \<sim> g (y::'a::equiv)"
proof -
  assume "f \<sim> g"
  moreover have "x \<in> domain" ..
  moreover have "y \<in> domain" ..
  moreover assume "x \<sim> y"
  ultimately show ?thesis ..
qed


subsection {* Quotient types *}

subsubsection {* General quotients and equivalence classes *}

text {*
 The quotient type @{text "'a quot"} consists of all \emph{equivalence
 classes} over elements of the base type @{typ 'a}.
*}

typedef 'a quot = "{{x. a \<sim> x}| a::'a. True}"
  by blast

lemma quotI [intro]: "{x. a \<sim> x} \<in> quot"
  by (unfold quot_def) blast

lemma quotE [elim]: "R \<in> quot ==> (!!a. R = {x. a \<sim> x} ==> C) ==> C"
  by (unfold quot_def) blast


text {*
 \medskip Standard properties of type-definitions.\footnote{(FIXME)
 Better incorporate these into the typedef package?}
*}

theorem Rep_quot_inject: "(Rep_quot x = Rep_quot y) = (x = y)"
proof
  assume "Rep_quot x = Rep_quot y"
  hence "Abs_quot (Rep_quot x) = Abs_quot (Rep_quot y)" by (simp only:)
  thus "x = y" by (simp only: Rep_quot_inverse)
next
  assume "x = y"
  thus "Rep_quot x = Rep_quot y" by simp
qed

theorem Abs_quot_inject:
  "x \<in> quot ==> y \<in> quot ==> (Abs_quot x = Abs_quot y) = (x = y)"
proof
  assume "Abs_quot x = Abs_quot y"
  hence "Rep_quot (Abs_quot x) = Rep_quot (Abs_quot y)" by simp
  also assume "x \<in> quot" hence "Rep_quot (Abs_quot x) = x" by (rule Abs_quot_inverse)
  also assume "y \<in> quot" hence "Rep_quot (Abs_quot y) = y" by (rule Abs_quot_inverse)
  finally show "x = y" .
next
  assume "x = y"
  thus "Abs_quot x = Abs_quot y" by simp
qed

theorem Rep_quot_induct: "y \<in> quot ==> (!!x. P (Rep_quot x)) ==> P y"
proof -
  assume "!!x. P (Rep_quot x)" hence "P (Rep_quot (Abs_quot y))" .
  also assume "y \<in> quot" hence "Rep_quot (Abs_quot y) = y" by (rule Abs_quot_inverse)
  finally show "P y" .
qed

theorem Abs_quot_induct: "(!!y. y \<in> quot ==> P (Abs_quot y)) ==> P x"
proof -
  assume r: "!!y. y \<in> quot ==> P (Abs_quot y)"
  have "Rep_quot x \<in> quot" by (rule Rep_quot)
  hence "P (Abs_quot (Rep_quot x))" by (rule r)
  also have "Abs_quot (Rep_quot x) = x" by (rule Rep_quot_inverse)
  finally show "P x" .
qed

text {*
 \medskip Abstracted equivalence classes are the canonical
 representation of elements of a quotient type.
*}

constdefs
  eqv_class :: "('a::partial_equiv) => 'a quot"    ("\<lfloor>_\<rfloor>")
  "\<lfloor>a\<rfloor> == Abs_quot {x. a \<sim> x}"

theorem quot_rep: "\<exists>a. A = \<lfloor>a\<rfloor>"
proof (unfold eqv_class_def)
  show "\<exists>a. A = Abs_quot {x. a \<sim> x}"
  proof (induct A rule: Abs_quot_induct)
    fix R assume "R \<in> quot"
    hence "\<exists>a. R = {x. a \<sim> x}" by blast
    thus "\<exists>a. Abs_quot R = Abs_quot {x. a \<sim> x}" by blast
  qed
qed

lemma quot_cases [case_names rep, cases type: quot]:
    "(!!a. A = \<lfloor>a\<rfloor> ==> C) ==> C"
  by (insert quot_rep) blast


subsubsection {* Equality on quotients *}

text {*
 Equality of canonical quotient elements corresponds to the original
 relation as follows.
*}

theorem eqv_class_eqI [intro]: "a \<sim> b ==> \<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
proof -
  assume ab: "a \<sim> b"
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
  thus ?thesis by (simp only: eqv_class_def)
qed

theorem eqv_class_eqD' [dest?]: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> ==> a \<in> domain ==> a \<sim> b"  (* FIXME [dest] would cause trouble with blast due to overloading *)
proof (unfold eqv_class_def)
  assume "Abs_quot {x. a \<sim> x} = Abs_quot {x. b \<sim> x}"
  hence "{x. a \<sim> x} = {x. b \<sim> x}" by (simp only: Abs_quot_inject quotI)
  moreover assume "a \<in> domain" hence "a \<sim> a" ..
  ultimately have "a \<in> {x. b \<sim> x}" by blast
  hence "b \<sim> a" by blast
  thus "a \<sim> b" ..
qed

theorem eqv_class_eqD [dest?]: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> ==> a \<sim> (b::'a::equiv)"  (* FIXME [dest] would cause trouble with blast due to overloading *)
proof (rule eqv_class_eqD')
  show "a \<in> domain" ..
qed

lemma eqv_class_eq' [simp]: "a \<in> domain ==> (\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>) = (a \<sim> b)"
  by (insert eqv_class_eqI eqv_class_eqD') blast

lemma eqv_class_eq [simp]: "(\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>) = (a \<sim> (b::'a::equiv))"
  by (insert eqv_class_eqI eqv_class_eqD) blast


subsubsection {* Picking representing elements *}

constdefs
  pick :: "'a::partial_equiv quot => 'a"
  "pick A == SOME a. A = \<lfloor>a\<rfloor>"

theorem pick_eqv' [intro?, simp]: "a \<in> domain ==> pick \<lfloor>a\<rfloor> \<sim> a" (* FIXME [intro] !? *)
proof (unfold pick_def)
  assume a: "a \<in> domain"
  show "(SOME x. \<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>) \<sim> a"
  proof (rule someI2)
    show "\<lfloor>a\<rfloor> = \<lfloor>a\<rfloor>" ..
    fix x assume "\<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>"
    hence "a \<sim> x" ..
    thus "x \<sim> a" ..
  qed
qed

theorem pick_eqv [intro, simp]: "pick \<lfloor>a\<rfloor> \<sim> (a::'a::equiv)"
proof (rule pick_eqv')
  show "a \<in> domain" ..
qed

theorem pick_inverse: "\<lfloor>pick A\<rfloor> = (A::'a::equiv quot)"   (* FIXME tune proof *)
proof (cases A)
  fix a assume a: "A = \<lfloor>a\<rfloor>"
  hence "pick A \<sim> a" by (simp only: pick_eqv)
  hence "\<lfloor>pick A\<rfloor> = \<lfloor>a\<rfloor>" by simp
  with a show ?thesis by simp
qed

end
