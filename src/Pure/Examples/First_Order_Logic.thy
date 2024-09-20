(*  Title:      Pure/Examples/First_Order_Logic.thy
    Author:     Makarius
*)

section \<open>A simple formulation of First-Order Logic\<close>

text \<open>
  The subsequent theory development illustrates single-sorted intuitionistic
  first-order logic with equality, formulated within the Pure framework.
\<close>

theory First_Order_Logic
  imports Pure
begin

subsection \<open>Abstract syntax\<close>

typedecl i
typedecl o

judgment Trueprop :: "o \<Rightarrow> prop"  (\<open>_\<close> 5)


subsection \<open>Propositional logic\<close>

axiomatization false :: o  (\<open>\<bottom>\<close>)
  where falseE [elim]: "\<bottom> \<Longrightarrow> A"


axiomatization imp :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr \<open>\<longrightarrow>\<close> 25)
  where impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B"
    and mp [dest]: "A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"


axiomatization conj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr \<open>\<and>\<close> 35)
  where conjI [intro]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
    and conjD1: "A \<and> B \<Longrightarrow> A"
    and conjD2: "A \<and> B \<Longrightarrow> B"

theorem conjE [elim]:
  assumes "A \<and> B"
  obtains A and B
proof
  from \<open>A \<and> B\<close> show A
    by (rule conjD1)
  from \<open>A \<and> B\<close> show B
    by (rule conjD2)
qed


axiomatization disj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr \<open>\<or>\<close> 30)
  where disjE [elim]: "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C"
    and disjI1 [intro]: "A \<Longrightarrow> A \<or> B"
    and disjI2 [intro]: "B \<Longrightarrow> A \<or> B"


definition true :: o  (\<open>\<top>\<close>)
  where "\<top> \<equiv> \<bottom> \<longrightarrow> \<bottom>"

theorem trueI [intro]: \<top>
  unfolding true_def ..


definition not :: "o \<Rightarrow> o"  (\<open>\<not> _\<close> [40] 40)
  where "\<not> A \<equiv> A \<longrightarrow> \<bottom>"

theorem notI [intro]: "(A \<Longrightarrow> \<bottom>) \<Longrightarrow> \<not> A"
  unfolding not_def ..

theorem notE [elim]: "\<not> A \<Longrightarrow> A \<Longrightarrow> B"
  unfolding not_def
proof -
  assume "A \<longrightarrow> \<bottom>" and A
  then have \<bottom> ..
  then show B ..
qed


definition iff :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr \<open>\<longleftrightarrow>\<close> 25)
  where "A \<longleftrightarrow> B \<equiv> (A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"

theorem iffI [intro]:
  assumes "A \<Longrightarrow> B"
    and "B \<Longrightarrow> A"
  shows "A \<longleftrightarrow> B"
  unfolding iff_def
proof
  from \<open>A \<Longrightarrow> B\<close> show "A \<longrightarrow> B" ..
  from \<open>B \<Longrightarrow> A\<close> show "B \<longrightarrow> A" ..
qed

theorem iff1 [elim]:
  assumes "A \<longleftrightarrow> B" and A
  shows B
proof -
  from \<open>A \<longleftrightarrow> B\<close> have "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
    unfolding iff_def .
  then have "A \<longrightarrow> B" ..
  from this and \<open>A\<close> show B ..
qed

theorem iff2 [elim]:
  assumes "A \<longleftrightarrow> B" and B
  shows A
proof -
  from \<open>A \<longleftrightarrow> B\<close> have "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
    unfolding iff_def .
  then have "B \<longrightarrow> A" ..
  from this and \<open>B\<close> show A ..
qed


subsection \<open>Equality\<close>

axiomatization equal :: "i \<Rightarrow> i \<Rightarrow> o"  (infixl \<open>=\<close> 50)
  where refl [intro]: "x = x"
    and subst: "x = y \<Longrightarrow> P x \<Longrightarrow> P y"

theorem trans [trans]: "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (rule subst)

theorem sym [sym]: "x = y \<Longrightarrow> y = x"
proof -
  assume "x = y"
  from this and refl show "y = x"
    by (rule subst)
qed


subsection \<open>Quantifiers\<close>

axiomatization All :: "(i \<Rightarrow> o) \<Rightarrow> o"  (binder \<open>\<forall>\<close> 10)
  where allI [intro]: "(\<And>x. P x) \<Longrightarrow> \<forall>x. P x"
    and allD [dest]: "\<forall>x. P x \<Longrightarrow> P a"

axiomatization Ex :: "(i \<Rightarrow> o) \<Rightarrow> o"  (binder \<open>\<exists>\<close> 10)
  where exI [intro]: "P a \<Longrightarrow> \<exists>x. P x"
    and exE [elim]: "\<exists>x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> C) \<Longrightarrow> C"


lemma "(\<exists>x. P (f x)) \<longrightarrow> (\<exists>y. P y)"
proof
  assume "\<exists>x. P (f x)"
  then obtain x where "P (f x)" ..
  then show "\<exists>y. P y" ..
qed

lemma "(\<exists>x. \<forall>y. R x y) \<longrightarrow> (\<forall>y. \<exists>x. R x y)"
proof
  assume "\<exists>x. \<forall>y. R x y"
  then obtain x where "\<forall>y. R x y" ..
  show "\<forall>y. \<exists>x. R x y"
  proof
    fix y
    from \<open>\<forall>y. R x y\<close> have "R x y" ..
    then show "\<exists>x. R x y" ..
  qed
qed

end
