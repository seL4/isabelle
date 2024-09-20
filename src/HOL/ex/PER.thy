(*  Title:      HOL/ex/PER.thy
    Author:     Oscar Slotosch and Markus Wenzel, TU Muenchen
*)

section \<open>Partial equivalence relations\<close>

theory PER
imports Main
begin

text \<open>
  Higher-order quotients are defined over partial equivalence
  relations (PERs) instead of total ones.  We provide axiomatic type
  classes \<open>equiv < partial_equiv\<close> and a type constructor
  \<open>'a quot\<close> with basic operations.  This development is based
  on:

  Oscar Slotosch: \emph{Higher Order Quotients and their
  Implementation in Isabelle HOL.}  Elsa L. Gunter and Amy Felty,
  editors, Theorem Proving in Higher Order Logics: TPHOLs '97,
  Springer LNCS 1275, 1997.
\<close>


subsection \<open>Partial equivalence\<close>

text \<open>
  Type class \<open>partial_equiv\<close> models partial equivalence
  relations (PERs) using the polymorphic \<open>\<sim> :: 'a \<Rightarrow> 'a \<Rightarrow>
  bool\<close> relation, which is required to be symmetric and transitive,
  but not necessarily reflexive.
\<close>

class partial_equiv =
  fixes eqv :: "'a \<Rightarrow> 'a \<Rightarrow> bool"    (infixl \<open>\<sim>\<close> 50)
  assumes partial_equiv_sym [elim?]: "x \<sim> y \<Longrightarrow> y \<sim> x"
  assumes partial_equiv_trans [trans]: "x \<sim> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<sim> z"

text \<open>
  \medskip The domain of a partial equivalence relation is the set of
  reflexive elements.  Due to symmetry and transitivity this
  characterizes exactly those elements that are connected with
  \emph{any} other one.
\<close>

definition
  "domain" :: "'a::partial_equiv set" where
  "domain = {x. x \<sim> x}"

lemma domainI [intro]: "x \<sim> x \<Longrightarrow> x \<in> domain"
  unfolding domain_def by blast

lemma domainD [dest]: "x \<in> domain \<Longrightarrow> x \<sim> x"
  unfolding domain_def by blast

theorem domainI' [elim?]: "x \<sim> y \<Longrightarrow> x \<in> domain"
proof
  assume xy: "x \<sim> y"
  also from xy have "y \<sim> x" ..
  finally show "x \<sim> x" .
qed


subsection \<open>Equivalence on function spaces\<close>

text \<open>
  The \<open>\<sim>\<close> relation is lifted to function spaces.  It is
  important to note that this is \emph{not} the direct product, but a
  structural one corresponding to the congruence property.
\<close>

instantiation "fun" :: (partial_equiv, partial_equiv) partial_equiv
begin

definition "f \<sim> g \<longleftrightarrow> (\<forall>x \<in> domain. \<forall>y \<in> domain. x \<sim> y \<longrightarrow> f x \<sim> g y)"

lemma partial_equiv_funI [intro?]:
    "(\<And>x y. x \<in> domain \<Longrightarrow> y \<in> domain \<Longrightarrow> x \<sim> y \<Longrightarrow> f x \<sim> g y) \<Longrightarrow> f \<sim> g"
  unfolding eqv_fun_def by blast

lemma partial_equiv_funD [dest?]:
    "f \<sim> g \<Longrightarrow> x \<in> domain \<Longrightarrow> y \<in> domain \<Longrightarrow> x \<sim> y \<Longrightarrow> f x \<sim> g y"
  unfolding eqv_fun_def by blast

text \<open>
  The class of partial equivalence relations is closed under function
  spaces (in \emph{both} argument positions).
\<close>

instance proof
  fix f g h :: "'a::partial_equiv \<Rightarrow> 'b::partial_equiv"
  assume fg: "f \<sim> g"
  show "g \<sim> f"
  proof
    fix x y :: 'a
    assume x: "x \<in> domain" and y: "y \<in> domain"
    assume "x \<sim> y" then have "y \<sim> x" ..
    with fg y x have "f y \<sim> g x" ..
    then show "g x \<sim> f y" ..
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

end


subsection \<open>Total equivalence\<close>

text \<open>
  The class of total equivalence relations on top of PERs.  It
  coincides with the standard notion of equivalence, i.e.\ \<open>\<sim>
  :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> is required to be reflexive, transitive and
  symmetric.
\<close>

class equiv =
  assumes eqv_refl [intro]: "x \<sim> x"

text \<open>
  On total equivalences all elements are reflexive, and congruence
  holds unconditionally.
\<close>

theorem equiv_domain [intro]: "(x::'a::equiv) \<in> domain"
proof
  show "x \<sim> x" ..
qed

theorem equiv_cong [dest?]: "f \<sim> g \<Longrightarrow> x \<sim> y \<Longrightarrow> f x \<sim> g (y::'a::equiv)"
proof -
  assume "f \<sim> g"
  moreover have "x \<in> domain" ..
  moreover have "y \<in> domain" ..
  moreover assume "x \<sim> y"
  ultimately show ?thesis ..
qed


subsection \<open>Quotient types\<close>

text \<open>
  The quotient type \<open>'a quot\<close> consists of all
  \emph{equivalence classes} over elements of the base type \<^typ>\<open>'a\<close>.
\<close>

definition "quot = {{x. a \<sim> x}| a::'a::partial_equiv. True}"

typedef (overloaded) 'a quot = "quot :: 'a::partial_equiv set set"
  unfolding quot_def by blast

lemma quotI [intro]: "{x. a \<sim> x} \<in> quot"
  unfolding quot_def by blast

lemma quotE [elim]: "R \<in> quot \<Longrightarrow> (\<And>a. R = {x. a \<sim> x} \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding quot_def by blast

text \<open>
  \medskip Abstracted equivalence classes are the canonical
  representation of elements of a quotient type.
\<close>

definition eqv_class :: "('a::partial_equiv) \<Rightarrow> 'a quot"  (\<open>\<lfloor>_\<rfloor>\<close>)
  where "\<lfloor>a\<rfloor> = Abs_quot {x. a \<sim> x}"

theorem quot_rep: "\<exists>a. A = \<lfloor>a\<rfloor>"
proof (cases A)
  fix R assume R: "A = Abs_quot R"
  assume "R \<in> quot" then have "\<exists>a. R = {x. a \<sim> x}" by blast
  with R have "\<exists>a. A = Abs_quot {x. a \<sim> x}" by blast
  then show ?thesis by (unfold eqv_class_def)
qed

lemma quot_cases [cases type: quot]:
  obtains (rep) a where "A = \<lfloor>a\<rfloor>"
  using quot_rep by blast


subsection \<open>Equality on quotients\<close>

text \<open>
  Equality of canonical quotient elements corresponds to the original
  relation as follows.
\<close>

theorem eqv_class_eqI [intro]: "a \<sim> b \<Longrightarrow> \<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
proof -
  assume ab: "a \<sim> b"
  have "{x. a \<sim> x} = {x. b \<sim> x}"
  proof (rule Collect_cong)
    fix x show "a \<sim> x \<longleftrightarrow> b \<sim> x"
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
  then show ?thesis by (simp only: eqv_class_def)
qed

theorem eqv_class_eqD' [dest?]: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> \<Longrightarrow> a \<in> domain \<Longrightarrow> a \<sim> b"
proof (unfold eqv_class_def)
  assume "Abs_quot {x. a \<sim> x} = Abs_quot {x. b \<sim> x}"
  then have "{x. a \<sim> x} = {x. b \<sim> x}" by (simp only: Abs_quot_inject quotI)
  moreover assume "a \<in> domain" then have "a \<sim> a" ..
  ultimately have "a \<in> {x. b \<sim> x}" by blast
  then have "b \<sim> a" by blast
  then show "a \<sim> b" ..
qed

theorem eqv_class_eqD [dest?]: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> \<Longrightarrow> a \<sim> (b::'a::equiv)"
proof (rule eqv_class_eqD')
  show "a \<in> domain" ..
qed

lemma eqv_class_eq' [simp]: "a \<in> domain \<Longrightarrow> \<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> \<longleftrightarrow> a \<sim> b"
  using eqv_class_eqI eqv_class_eqD' by (blast del: eqv_refl)

lemma eqv_class_eq [simp]: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> \<longleftrightarrow> a \<sim> (b::'a::equiv)"
  using eqv_class_eqI eqv_class_eqD by blast


subsection \<open>Picking representing elements\<close>

definition pick :: "'a::partial_equiv quot \<Rightarrow> 'a"
  where "pick A = (SOME a. A = \<lfloor>a\<rfloor>)"

theorem pick_eqv' [intro?, simp]: "a \<in> domain \<Longrightarrow> pick \<lfloor>a\<rfloor> \<sim> a"
proof (unfold pick_def)
  assume a: "a \<in> domain"
  show "(SOME x. \<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>) \<sim> a"
  proof (rule someI2)
    show "\<lfloor>a\<rfloor> = \<lfloor>a\<rfloor>" ..
    fix x assume "\<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>"
    from this and a have "a \<sim> x" ..
    then show "x \<sim> a" ..
  qed
qed

theorem pick_eqv [intro, simp]: "pick \<lfloor>a\<rfloor> \<sim> (a::'a::equiv)"
proof (rule pick_eqv')
  show "a \<in> domain" ..
qed

theorem pick_inverse: "\<lfloor>pick A\<rfloor> = (A::'a::equiv quot)"
proof (cases A)
  fix a assume a: "A = \<lfloor>a\<rfloor>"
  then have "pick A \<sim> a" by simp
  then have "\<lfloor>pick A\<rfloor> = \<lfloor>a\<rfloor>" by simp
  with a show ?thesis by simp
qed

end
