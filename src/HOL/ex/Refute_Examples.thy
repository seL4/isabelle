(*  Title:      HOL/ex/Refute_Examples.thy
    Author:     Tjark Weber
    Copyright   2003-2007

See HOL/Refute.thy for help.
*)

section \<open>Examples for the 'refute' command\<close>

theory Refute_Examples
imports "HOL-Library.Refute"
begin

refute_params [satsolver = "cdclite"]

lemma "P \<and> Q"
apply (rule conjI)
refute [expect = genuine] 1  \<comment> \<open>refutes @{term "P"}\<close>
refute [expect = genuine] 2  \<comment> \<open>refutes @{term "Q"}\<close>
refute [expect = genuine]    \<comment> \<open>equivalent to 'refute 1'\<close>
  \<comment> \<open>here 'refute 3' would cause an exception, since we only have 2 subgoals\<close>
refute [maxsize = 5, expect = genuine]   \<comment> \<open>we can override parameters ...\<close>
refute [satsolver = "cdclite", expect = genuine] 2
  \<comment> \<open>... and specify a subgoal at the same time\<close>
oops

(*****************************************************************************)

subsection \<open>Examples and Test Cases\<close>

subsubsection \<open>Propositional logic\<close>

lemma "True"
refute [expect = none]
by auto

lemma "False"
refute [expect = genuine]
oops

lemma "P"
refute [expect = genuine]
oops

lemma "~ P"
refute [expect = genuine]
oops

lemma "P & Q"
refute [expect = genuine]
oops

lemma "P | Q"
refute [expect = genuine]
oops

lemma "P \<longrightarrow> Q"
refute [expect = genuine]
oops

lemma "(P::bool) = Q"
refute [expect = genuine]
oops

lemma "(P | Q) \<longrightarrow> (P & Q)"
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection \<open>Predicate logic\<close>

lemma "P x y z"
refute [expect = genuine]
oops

lemma "P x y \<longrightarrow> P y x"
refute [expect = genuine]
oops

lemma "P (f (f x)) \<longrightarrow> P x \<longrightarrow> P (f x)"
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection \<open>Equality\<close>

lemma "P = True"
refute [expect = genuine]
oops

lemma "P = False"
refute [expect = genuine]
oops

lemma "x = y"
refute [expect = genuine]
oops

lemma "f x = g x"
refute [expect = genuine]
oops

lemma "(f::'a\<Rightarrow>'b) = g"
refute [expect = genuine]
oops

lemma "(f::('d\<Rightarrow>'d)\<Rightarrow>('c\<Rightarrow>'d)) = g"
refute [expect = genuine]
oops

lemma "distinct [a, b]"
(* refute *)
apply simp
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection \<open>First-Order Logic\<close>

lemma "\<exists>x. P x"
refute [expect = genuine]
oops

lemma "\<forall>x. P x"
refute [expect = genuine]
oops

lemma "\<exists>!x. P x"
refute [expect = genuine]
oops

lemma "Ex P"
refute [expect = genuine]
oops

lemma "All P"
refute [expect = genuine]
oops

lemma "Ex1 P"
refute [expect = genuine]
oops

lemma "(\<exists>x. P x) \<longrightarrow> (\<forall>x. P x)"
refute [expect = genuine]
oops

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
refute [expect = genuine]
oops

lemma "(\<exists>x. P x) \<longrightarrow> (\<exists>!x. P x)"
refute [expect = genuine]
oops

text \<open>A true statement (also testing names of free and bound variables being identical)\<close>

lemma "(\<forall>x y. P x y \<longrightarrow> P y x) \<longrightarrow> (\<forall>x. P x y) \<longrightarrow> P y x"
refute [maxsize = 4, expect = none]
by fast

text \<open>"A type has at most 4 elements."\<close>

lemma "a=b | a=c | a=d | a=e | b=c | b=d | b=e | c=d | c=e | d=e"
refute [expect = genuine]
oops

lemma "\<forall>a b c d e. a=b | a=c | a=d | a=e | b=c | b=d | b=e | c=d | c=e | d=e"
refute [expect = genuine]
oops

text \<open>"Every reflexive and symmetric relation is transitive."\<close>

lemma "\<lbrakk> \<forall>x. P x x; \<forall>x y. P x y \<longrightarrow> P y x \<rbrakk> \<Longrightarrow> P x y \<longrightarrow> P y z \<longrightarrow> P x z"
refute [expect = genuine]
oops

text \<open>The "Drinker's theorem" ...\<close>

lemma "\<exists>x. f x = g x \<longrightarrow> f = g"
refute [maxsize = 4, expect = none]
by (auto simp add: ext)

text \<open>... and an incorrect version of it\<close>

lemma "(\<exists>x. f x = g x) \<longrightarrow> f = g"
refute [expect = genuine]
oops

text \<open>"Every function has a fixed point."\<close>

lemma "\<exists>x. f x = x"
refute [expect = genuine]
oops

text \<open>"Function composition is commutative."\<close>

lemma "f (g x) = g (f x)"
refute [expect = genuine]
oops

text \<open>"Two functions that are equivalent wrt.\ the same predicate 'P' are equal."\<close>

lemma "((P::('a\<Rightarrow>'b)\<Rightarrow>bool) f = P g) \<longrightarrow> (f x = g x)"
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection \<open>Higher-Order Logic\<close>

lemma "\<exists>P. P"
refute [expect = none]
by auto

lemma "\<forall>P. P"
refute [expect = genuine]
oops

lemma "\<exists>!P. P"
refute [expect = none]
by auto

lemma "\<exists>!P. P x"
refute [expect = genuine]
oops

lemma "P Q | Q x"
refute [expect = genuine]
oops

lemma "x \<noteq> All"
refute [expect = genuine]
oops

lemma "x \<noteq> Ex"
refute [expect = genuine]
oops

lemma "x \<noteq> Ex1"
refute [expect = genuine]
oops

text \<open>"The transitive closure 'T' of an arbitrary relation 'P' is non-empty."\<close>

definition "trans" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "trans P \<equiv> (\<forall>x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z)"

definition "subset" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "subset P Q \<equiv> (\<forall>x y. P x y \<longrightarrow> Q x y)"

definition "trans_closure" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "trans_closure P Q \<equiv> (subset Q P) \<and> (trans P) \<and> (\<forall>R. subset Q R \<longrightarrow> trans R \<longrightarrow> subset P R)"

lemma "trans_closure T P \<longrightarrow> (\<exists>x y. T x y)"
refute [expect = genuine]
oops

text \<open>"Every surjective function is invertible."\<close>

lemma "(\<forall>y. \<exists>x. y = f x) \<longrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"
refute [expect = genuine]
oops

text \<open>"Every invertible function is surjective."\<close>

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
refute [expect = genuine]
oops

text \<open>Every point is a fixed point of some function.\<close>

lemma "\<exists>f. f x = x"
refute [maxsize = 4, expect = none]
apply (rule_tac x="\<lambda>x. x" in exI)
by simp

text \<open>Axiom of Choice: first an incorrect version ...\<close>

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>!f. \<forall>x. P x (f x))"
refute [expect = genuine]
oops

text \<open>... and now two correct ones\<close>

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>f. \<forall>x. P x (f x))"
refute [maxsize = 4, expect = none]
by (simp add: choice)

lemma "(\<forall>x. \<exists>!y. P x y) \<longrightarrow> (\<exists>!f. \<forall>x. P x (f x))"
refute [maxsize = 2, expect = none]
apply auto
  apply (simp add: ex1_implies_ex choice)
by (fast intro: ext)

(*****************************************************************************)

subsubsection \<open>Meta-logic\<close>

lemma "!!x. P x"
refute [expect = genuine]
oops

lemma "f x == g x"
refute [expect = genuine]
oops

lemma "P \<Longrightarrow> Q"
refute [expect = genuine]
oops

lemma "\<lbrakk> P; Q; R \<rbrakk> \<Longrightarrow> S"
refute [expect = genuine]
oops

lemma "(x == Pure.all) \<Longrightarrow> False"
refute [expect = genuine]
oops

lemma "(x == (==)) \<Longrightarrow> False"
refute [expect = genuine]
oops

lemma "(x == (\<Longrightarrow>)) \<Longrightarrow> False"
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection \<open>Schematic variables\<close>

schematic_goal "?P"
refute [expect = none]
by auto

schematic_goal "x = ?y"
refute [expect = none]
by auto

(******************************************************************************)

subsubsection \<open>Abstractions\<close>

lemma "(\<lambda>x. x) = (\<lambda>x. y)"
refute [expect = genuine]
oops

lemma "(\<lambda>f. f x) = (\<lambda>f. True)"
refute [expect = genuine]
oops

lemma "(\<lambda>x. x) = (\<lambda>y. y)"
refute
by simp

(*****************************************************************************)

subsubsection \<open>Sets\<close>

lemma "P (A::'a set)"
refute
oops

lemma "P (A::'a set set)"
refute
oops

lemma "{x. P x} = {y. P y}"
refute
by simp

lemma "x \<in> {x. P x}"
refute
oops

lemma "P (\<in>)"
refute
oops

lemma "P ((\<in>) x)"
refute
oops

lemma "P Collect"
refute
oops

lemma "A \<union> B = A \<inter> B"
refute
oops

lemma "(A \<inter> B) \<union> C = (A \<union> C) \<inter> B"
refute
oops

lemma "Ball A P \<longrightarrow> Bex A P"
refute
oops

(*****************************************************************************)

subsubsection \<open>undefined\<close>

lemma "undefined"
refute [expect = genuine]
oops

lemma "P undefined"
refute [expect = genuine]
oops

lemma "undefined x"
refute [expect = genuine]
oops

lemma "undefined undefined"
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection \<open>The\<close>

lemma "The P"
refute [expect = genuine]
oops

lemma "P The"
refute [expect = genuine]
oops

lemma "P (The P)"
refute [expect = genuine]
oops

lemma "(THE x. x=y) = z"
refute [expect = genuine]
oops

lemma "Ex P \<longrightarrow> P (The P)"
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection \<open>Eps\<close>

lemma "Eps P"
refute [expect = genuine]
oops

lemma "P Eps"
refute [expect = genuine]
oops

lemma "P (Eps P)"
refute [expect = genuine]
oops

lemma "(SOME x. x=y) = z"
refute [expect = genuine]
oops

lemma "Ex P \<longrightarrow> P (Eps P)"
refute [maxsize = 3, expect = none]
by (auto simp add: someI)

(*****************************************************************************)

subsubsection \<open>Subtypes (typedef), typedecl\<close>

text \<open>A completely unspecified non-empty subset of @{typ "'a"}:\<close>

definition "myTdef = insert (undefined::'a) (undefined::'a set)"

typedef 'a myTdef = "myTdef :: 'a set"
  unfolding myTdef_def by auto

lemma "(x::'a myTdef) = y"
refute
oops

typedecl myTdecl

definition "T_bij = {(f::'a\<Rightarrow>'a). \<forall>y. \<exists>!x. f x = y}"

typedef 'a T_bij = "T_bij :: ('a \<Rightarrow> 'a) set"
  unfolding T_bij_def by auto

lemma "P (f::(myTdecl myTdef) T_bij)"
refute
oops

(*****************************************************************************)

subsubsection \<open>Inductive datatypes\<close>

text \<open>unit\<close>

lemma "P (x::unit)"
refute [expect = genuine]
oops

lemma "\<forall>x::unit. P x"
refute [expect = genuine]
oops

lemma "P ()"
refute [expect = genuine]
oops

lemma "P (case x of () \<Rightarrow> u)"
refute [expect = genuine]
oops

text \<open>option\<close>

lemma "P (x::'a option)"
refute [expect = genuine]
oops

lemma "\<forall>x::'a option. P x"
refute [expect = genuine]
oops

lemma "P None"
refute [expect = genuine]
oops

lemma "P (Some x)"
refute [expect = genuine]
oops

lemma "P (case x of None \<Rightarrow> n | Some u \<Rightarrow> s u)"
refute [expect = genuine]
oops

text \<open>*\<close>

lemma "P (x::'a*'b)"
refute [expect = genuine]
oops

lemma "\<forall>x::'a*'b. P x"
refute [expect = genuine]
oops

lemma "P (x, y)"
refute [expect = genuine]
oops

lemma "P (fst x)"
refute [expect = genuine]
oops

lemma "P (snd x)"
refute [expect = genuine]
oops

lemma "P Pair"
refute [expect = genuine]
oops

lemma "P (case x of Pair a b \<Rightarrow> p a b)"
refute [expect = genuine]
oops

text \<open>+\<close>

lemma "P (x::'a+'b)"
refute [expect = genuine]
oops

lemma "\<forall>x::'a+'b. P x"
refute [expect = genuine]
oops

lemma "P (Inl x)"
refute [expect = genuine]
oops

lemma "P (Inr x)"
refute [expect = genuine]
oops

lemma "P Inl"
refute [expect = genuine]
oops

lemma "P (case x of Inl a \<Rightarrow> l a | Inr b \<Rightarrow> r b)"
refute [expect = genuine]
oops

text \<open>Non-recursive datatypes\<close>

datatype T1 = A | B

lemma "P (x::T1)"
refute [expect = genuine]
oops

lemma "\<forall>x::T1. P x"
refute [expect = genuine]
oops

lemma "P A"
refute [expect = genuine]
oops

lemma "P B"
refute [expect = genuine]
oops

lemma "rec_T1 a b A = a"
refute [expect = none]
by simp

lemma "rec_T1 a b B = b"
refute [expect = none]
by simp

lemma "P (rec_T1 a b x)"
refute [expect = genuine]
oops

lemma "P (case x of A \<Rightarrow> a | B \<Rightarrow> b)"
refute [expect = genuine]
oops

datatype 'a T2 = C T1 | D 'a

lemma "P (x::'a T2)"
refute [expect = genuine]
oops

lemma "\<forall>x::'a T2. P x"
refute [expect = genuine]
oops

lemma "P D"
refute [expect = genuine]
oops

lemma "rec_T2 c d (C x) = c x"
refute [maxsize = 4, expect = none]
by simp

lemma "rec_T2 c d (D x) = d x"
refute [maxsize = 4, expect = none]
by simp

lemma "P (rec_T2 c d x)"
refute [expect = genuine]
oops

lemma "P (case x of C u \<Rightarrow> c u | D v \<Rightarrow> d v)"
refute [expect = genuine]
oops

datatype ('a,'b) T3 = E "'a \<Rightarrow> 'b"

lemma "P (x::('a,'b) T3)"
refute [expect = genuine]
oops

lemma "\<forall>x::('a,'b) T3. P x"
refute [expect = genuine]
oops

lemma "P E"
refute [expect = genuine]
oops

lemma "rec_T3 e (E x) = e x"
refute [maxsize = 2, expect = none]
by simp

lemma "P (rec_T3 e x)"
refute [expect = genuine]
oops

lemma "P (case x of E f \<Rightarrow> e f)"
refute [expect = genuine]
oops

text \<open>Recursive datatypes\<close>

text \<open>nat\<close>

lemma "P (x::nat)"
refute [expect = potential]
oops

lemma "\<forall>x::nat. P x"
refute [expect = potential]
oops

lemma "P (Suc 0)"
refute [expect = potential]
oops

lemma "P Suc"
refute [maxsize = 3, expect = none]
\<comment> \<open>@{term Suc} is a partial function (regardless of the size
      of the model), hence @{term "P Suc"} is undefined and no
      model will be found\<close>
oops

lemma "rec_nat zero suc 0 = zero"
refute [expect = none]
by simp

lemma "rec_nat zero suc (Suc x) = suc x (rec_nat zero suc x)"
refute [maxsize = 2, expect = none]
by simp

lemma "P (rec_nat zero suc x)"
refute [expect = potential]
oops

lemma "P (case x of 0 \<Rightarrow> zero | Suc n \<Rightarrow> suc n)"
refute [expect = potential]
oops

text \<open>'a list\<close>

lemma "P (xs::'a list)"
refute [expect = potential]
oops

lemma "\<forall>xs::'a list. P xs"
refute [expect = potential]
oops

lemma "P [x, y]"
refute [expect = potential]
oops

lemma "rec_list nil cons [] = nil"
refute [maxsize = 3, expect = none]
by simp

lemma "rec_list nil cons (x#xs) = cons x xs (rec_list nil cons xs)"
refute [maxsize = 2, expect = none]
by simp

lemma "P (rec_list nil cons xs)"
refute [expect = potential]
oops

lemma "P (case x of Nil \<Rightarrow> nil | Cons a b \<Rightarrow> cons a b)"
refute [expect = potential]
oops

lemma "(xs::'a list) = ys"
refute [expect = potential]
oops

lemma "a # xs = b # xs"
refute [expect = potential]
oops

datatype BitList = BitListNil | Bit0 BitList | Bit1 BitList

lemma "P (x::BitList)"
refute [expect = potential]
oops

lemma "\<forall>x::BitList. P x"
refute [expect = potential]
oops

lemma "P (Bit0 (Bit1 BitListNil))"
refute [expect = potential]
oops

lemma "rec_BitList nil bit0 bit1 BitListNil = nil"
refute [maxsize = 4, expect = none]
by simp

lemma "rec_BitList nil bit0 bit1 (Bit0 xs) = bit0 xs (rec_BitList nil bit0 bit1 xs)"
refute [maxsize = 2, expect = none]
by simp

lemma "rec_BitList nil bit0 bit1 (Bit1 xs) = bit1 xs (rec_BitList nil bit0 bit1 xs)"
refute [maxsize = 2, expect = none]
by simp

lemma "P (rec_BitList nil bit0 bit1 x)"
refute [expect = potential]
oops

(*****************************************************************************)

subsubsection \<open>Examples involving special functions\<close>

lemma "card x = 0"
refute [expect = potential]
oops

lemma "finite x"
refute \<comment> \<open>no finite countermodel exists\<close>
oops

lemma "(x::nat) + y = 0"
refute [expect = potential]
oops

lemma "(x::nat) = x + x"
refute [expect = potential]
oops

lemma "(x::nat) - y + y = x"
refute [expect = potential]
oops

lemma "(x::nat) = x * x"
refute [expect = potential]
oops

lemma "(x::nat) < x + y"
refute [expect = potential]
oops

lemma "xs @ [] = ys @ []"
refute [expect = potential]
oops

lemma "xs @ ys = ys @ xs"
refute [expect = potential]
oops

(*****************************************************************************)

subsubsection \<open>Type classes and overloading\<close>

text \<open>A type class without axioms:\<close>

class classA

lemma "P (x::'a::classA)"
refute [expect = genuine]
oops

text \<open>An axiom with a type variable (denoting types which have at least two elements):\<close>

class classC =
  assumes classC_ax: "\<exists>x y. x \<noteq> y"

lemma "P (x::'a::classC)"
refute [expect = genuine]
oops

lemma "\<exists>x y. (x::'a::classC) \<noteq> y"
(* refute [expect = none] FIXME *)
oops

text \<open>A type class for which a constant is defined:\<close>

class classD =
  fixes classD_const :: "'a \<Rightarrow> 'a"
  assumes classD_ax: "classD_const (classD_const x) = classD_const x"

lemma "P (x::'a::classD)"
refute [expect = genuine]
oops

text \<open>A type class with multiple superclasses:\<close>

class classE = classC + classD

lemma "P (x::'a::classE)"
refute [expect = genuine]
oops

text \<open>OFCLASS:\<close>

lemma "OFCLASS('a::type, type_class)"
refute [expect = none]
by intro_classes

lemma "OFCLASS('a::classC, type_class)"
refute [expect = none]
by intro_classes

lemma "OFCLASS('a::type, classC_class)"
refute [expect = genuine]
oops

text \<open>Overloading:\<close>

consts inverse :: "'a \<Rightarrow> 'a"

overloading inverse_bool \<equiv> "inverse :: bool \<Rightarrow> bool"
begin
  definition "inverse (b::bool) \<equiv> \<not> b"
end

overloading inverse_set \<equiv> "inverse :: 'a set \<Rightarrow> 'a set"
begin
  definition "inverse (S::'a set) \<equiv> -S"
end

overloading inverse_pair \<equiv> "inverse :: 'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
begin
  definition "inverse_pair p \<equiv> (inverse (fst p), inverse (snd p))"
end

lemma "inverse b"
refute [expect = genuine]
oops

lemma "P (inverse (S::'a set))"
refute [expect = genuine]
oops

lemma "P (inverse (p::'a\<times>'b))"
refute [expect = genuine]
oops

text \<open>Structured proofs\<close>

lemma "x = y"
proof cases
  assume "x = y"
  show ?thesis
  refute [expect = none]
  refute [no_assms, expect = genuine]
  refute [no_assms = false, expect = none]
oops

refute_params [satsolver = "auto"]

end
