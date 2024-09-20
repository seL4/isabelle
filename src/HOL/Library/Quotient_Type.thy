(*  Title:      HOL/Library/Quotient_Type.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Quotient types\<close>

theory Quotient_Type
imports Main
begin

text \<open>We introduce the notion of quotient types over equivalence relations
  via type classes.\<close>


subsection \<open>Equivalence relations and quotient types\<close>

text \<open>Type class \<open>equiv\<close> models equivalence relations
  \<open>\<sim> :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>.\<close>

class eqv =
  fixes eqv :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infixl \<open>\<sim>\<close> 50)

class equiv = eqv +
  assumes equiv_refl [intro]: "x \<sim> x"
    and equiv_trans [trans]: "x \<sim> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<sim> z"
    and equiv_sym [sym]: "x \<sim> y \<Longrightarrow> y \<sim> x"
begin

lemma equiv_not_sym [sym]: "\<not> x \<sim> y \<Longrightarrow> \<not> y \<sim> x"
proof -
  assume "\<not> x \<sim> y"
  then show "\<not> y \<sim> x" by (rule contrapos_nn) (rule equiv_sym)
qed

lemma not_equiv_trans1 [trans]: "\<not> x \<sim> y \<Longrightarrow> y \<sim> z \<Longrightarrow> \<not> x \<sim> z"
proof -
  assume "\<not> x \<sim> y" and "y \<sim> z"
  show "\<not> x \<sim> z"
  proof
    assume "x \<sim> z"
    also from \<open>y \<sim> z\<close> have "z \<sim> y" ..
    finally have "x \<sim> y" .
    with \<open>\<not> x \<sim> y\<close> show False by contradiction
  qed
qed

lemma not_equiv_trans2 [trans]: "x \<sim> y \<Longrightarrow> \<not> y \<sim> z \<Longrightarrow> \<not> x \<sim> z"
proof -
  assume "\<not> y \<sim> z"
  then have "\<not> z \<sim> y" ..
  also
  assume "x \<sim> y"
  then have "y \<sim> x" ..
  finally have "\<not> z \<sim> x" .
  then show "\<not> x \<sim> z" ..
qed

end

text \<open>The quotient type \<open>'a quot\<close> consists of all \emph{equivalence
  classes} over elements of the base type \<^typ>\<open>'a\<close>.\<close>

definition (in eqv) "quot = {{x. a \<sim> x} | a. True}"

typedef (overloaded) 'a quot = "quot :: 'a::eqv set set"
  unfolding quot_def by blast

lemma quotI [intro]: "{x. a \<sim> x} \<in> quot"
  unfolding quot_def by blast

lemma quotE [elim]:
  assumes "R \<in> quot"
  obtains a where "R = {x. a \<sim> x}"
  using assms unfolding quot_def by blast

text \<open>Abstracted equivalence classes are the canonical representation of
  elements of a quotient type.\<close>

definition "class" :: "'a::equiv \<Rightarrow> 'a quot"  (\<open>\<lfloor>_\<rfloor>\<close>)
  where "\<lfloor>a\<rfloor> = Abs_quot {x. a \<sim> x}"

theorem quot_exhaust: "\<exists>a. A = \<lfloor>a\<rfloor>"
proof (cases A)
  fix R
  assume R: "A = Abs_quot R"
  assume "R \<in> quot"
  then have "\<exists>a. R = {x. a \<sim> x}" by blast
  with R have "\<exists>a. A = Abs_quot {x. a \<sim> x}" by blast
  then show ?thesis unfolding class_def .
qed

lemma quot_cases [cases type: quot]:
  obtains a where "A = \<lfloor>a\<rfloor>"
  using quot_exhaust by blast


subsection \<open>Equality on quotients\<close>

text \<open>Equality of canonical quotient elements coincides with the original
  relation.\<close>

theorem quot_equality [iff?]: "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> \<longleftrightarrow> a \<sim> b"
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


subsection \<open>Picking representing elements\<close>

definition pick :: "'a::equiv quot \<Rightarrow> 'a"
  where "pick A = (SOME a. A = \<lfloor>a\<rfloor>)"

theorem pick_equiv [intro]: "pick \<lfloor>a\<rfloor> \<sim> a"
proof (unfold pick_def)
  show "(SOME x. \<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>) \<sim> a"
  proof (rule someI2)
    show "\<lfloor>a\<rfloor> = \<lfloor>a\<rfloor>" ..
    fix x assume "\<lfloor>a\<rfloor> = \<lfloor>x\<rfloor>"
    then have "a \<sim> x" ..
    then show "x \<sim> a" ..
  qed
qed

theorem pick_inverse [intro]: "\<lfloor>pick A\<rfloor> = A"
proof (cases A)
  fix a assume a: "A = \<lfloor>a\<rfloor>"
  then have "pick A \<sim> a" by (simp only: pick_equiv)
  then have "\<lfloor>pick A\<rfloor> = \<lfloor>a\<rfloor>" ..
  with a show ?thesis by simp
qed

text \<open>The following rules support canonical function definitions on quotient
  types (with up to two arguments). Note that the stripped-down version
  without additional conditions is sufficient most of the time.\<close>

theorem quot_cond_function:
  assumes eq: "\<And>X Y. P X Y \<Longrightarrow> f X Y \<equiv> g (pick X) (pick Y)"
    and cong: "\<And>x x' y y'. \<lfloor>x\<rfloor> = \<lfloor>x'\<rfloor> \<Longrightarrow> \<lfloor>y\<rfloor> = \<lfloor>y'\<rfloor>
      \<Longrightarrow> P \<lfloor>x\<rfloor> \<lfloor>y\<rfloor> \<Longrightarrow> P \<lfloor>x'\<rfloor> \<lfloor>y'\<rfloor> \<Longrightarrow> g x y = g x' y'"
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
  assumes "\<And>X Y. f X Y \<equiv> g (pick X) (pick Y)"
    and "\<And>x x' y y'. \<lfloor>x\<rfloor> = \<lfloor>x'\<rfloor> \<Longrightarrow> \<lfloor>y\<rfloor> = \<lfloor>y'\<rfloor> \<Longrightarrow> g x y = g x' y'"
  shows "f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
  using assms and TrueI
  by (rule quot_cond_function)

theorem quot_function':
  "(\<And>X Y. f X Y \<equiv> g (pick X) (pick Y)) \<Longrightarrow>
    (\<And>x x' y y'. x \<sim> x' \<Longrightarrow> y \<sim> y' \<Longrightarrow> g x y = g x' y') \<Longrightarrow>
    f \<lfloor>a\<rfloor> \<lfloor>b\<rfloor> = g a b"
  by (rule quot_function) (simp_all only: quot_equality)

end
