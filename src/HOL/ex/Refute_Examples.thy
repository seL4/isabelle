(*  Title:      HOL/ex/Refute_Examples.thy
    Author:     Tjark Weber
    Copyright   2003-2007

See HOL/Refute.thy for help.
*)

header {* Examples for the 'refute' command *}

theory Refute_Examples
imports "~~/src/HOL/Library/Refute"
begin

refute_params [satsolver = "cdclite"]

lemma "P \<and> Q"
apply (rule conjI)
refute [expect = genuine] 1  -- {* refutes @{term "P"} *}
refute [expect = genuine] 2  -- {* refutes @{term "Q"} *}
refute [expect = genuine]    -- {* equivalent to 'refute 1' *}
  -- {* here 'refute 3' would cause an exception, since we only have 2 subgoals *}
refute [maxsize = 5, expect = genuine]   -- {* we can override parameters ... *}
refute [satsolver = "cdclite", expect = genuine] 2
  -- {* ... and specify a subgoal at the same time *}
oops

(*****************************************************************************)

subsection {* Examples and Test Cases *}

subsubsection {* Propositional logic *}

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

subsubsection {* Predicate logic *}

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

subsubsection {* Equality *}

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

subsubsection {* First-Order Logic *}

lemma "\<exists>x. P x"
refute [expect = genuine]
oops

lemma "\<forall>x. P x"
refute [expect = genuine]
oops

lemma "EX! x. P x"
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

lemma "(\<exists>x. P x) \<longrightarrow> (EX! x. P x)"
refute [expect = genuine]
oops

text {* A true statement (also testing names of free and bound variables being identical) *}

lemma "(\<forall>x y. P x y \<longrightarrow> P y x) \<longrightarrow> (\<forall>x. P x y) \<longrightarrow> P y x"
refute [maxsize = 4, expect = none]
by fast

text {* "A type has at most 4 elements." *}

lemma "a=b | a=c | a=d | a=e | b=c | b=d | b=e | c=d | c=e | d=e"
refute [expect = genuine]
oops

lemma "\<forall>a b c d e. a=b | a=c | a=d | a=e | b=c | b=d | b=e | c=d | c=e | d=e"
refute [expect = genuine]
oops

text {* "Every reflexive and symmetric relation is transitive." *}

lemma "\<lbrakk> \<forall>x. P x x; \<forall>x y. P x y \<longrightarrow> P y x \<rbrakk> \<Longrightarrow> P x y \<longrightarrow> P y z \<longrightarrow> P x z"
refute [expect = genuine]
oops

text {* The "Drinker's theorem" ... *}

lemma "\<exists>x. f x = g x \<longrightarrow> f = g"
refute [maxsize = 4, expect = none]
by (auto simp add: ext)

text {* ... and an incorrect version of it *}

lemma "(\<exists>x. f x = g x) \<longrightarrow> f = g"
refute [expect = genuine]
oops

text {* "Every function has a fixed point." *}

lemma "\<exists>x. f x = x"
refute [expect = genuine]
oops

text {* "Function composition is commutative." *}

lemma "f (g x) = g (f x)"
refute [expect = genuine]
oops

text {* "Two functions that are equivalent wrt.\ the same predicate 'P' are equal." *}

lemma "((P::('a\<Rightarrow>'b)\<Rightarrow>bool) f = P g) \<longrightarrow> (f x = g x)"
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection {* Higher-Order Logic *}

lemma "\<exists>P. P"
refute [expect = none]
by auto

lemma "\<forall>P. P"
refute [expect = genuine]
oops

lemma "EX! P. P"
refute [expect = none]
by auto

lemma "EX! P. P x"
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

text {* "The transitive closure 'T' of an arbitrary relation 'P' is non-empty." *}

definition "trans" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "trans P == (ALL x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z)"

definition "subset" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "subset P Q == (ALL x y. P x y \<longrightarrow> Q x y)"

definition "trans_closure" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "trans_closure P Q == (subset Q P) & (trans P) & (ALL R. subset Q R \<longrightarrow> trans R \<longrightarrow> subset P R)"

lemma "trans_closure T P \<longrightarrow> (\<exists>x y. T x y)"
refute [expect = genuine]
oops

text {* "The union of transitive closures is equal to the transitive closure of unions." *}

lemma "(\<forall>x y. (P x y | R x y) \<longrightarrow> T x y) \<longrightarrow> trans T \<longrightarrow> (\<forall>Q. (\<forall>x y. (P x y | R x y) \<longrightarrow> Q x y) \<longrightarrow> trans Q \<longrightarrow> subset T Q)
        \<longrightarrow> trans_closure TP P
        \<longrightarrow> trans_closure TR R
        \<longrightarrow> (T x y = (TP x y | TR x y))"
refute [expect = genuine]
oops

text {* "Every surjective function is invertible." *}

lemma "(\<forall>y. \<exists>x. y = f x) \<longrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"
refute [expect = genuine]
oops

text {* "Every invertible function is surjective." *}

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
refute [expect = genuine]
oops

text {* Every point is a fixed point of some function. *}

lemma "\<exists>f. f x = x"
refute [maxsize = 4, expect = none]
apply (rule_tac x="\<lambda>x. x" in exI)
by simp

text {* Axiom of Choice: first an incorrect version ... *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (EX!f. \<forall>x. P x (f x))"
refute [expect = genuine]
oops

text {* ... and now two correct ones *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>f. \<forall>x. P x (f x))"
refute [maxsize = 4, expect = none]
by (simp add: choice)

lemma "(\<forall>x. EX!y. P x y) \<longrightarrow> (EX!f. \<forall>x. P x (f x))"
refute [maxsize = 2, expect = none]
apply auto
  apply (simp add: ex1_implies_ex choice)
by (fast intro: ext)

(*****************************************************************************)

subsubsection {* Meta-logic *}

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

lemma "(x == (op ==)) \<Longrightarrow> False"
refute [expect = genuine]
oops

lemma "(x == (op \<Longrightarrow>)) \<Longrightarrow> False"
refute [expect = genuine]
oops

(*****************************************************************************)

subsubsection {* Schematic variables *}

schematic_lemma "?P"
refute [expect = none]
by auto

schematic_lemma "x = ?y"
refute [expect = none]
by auto

(******************************************************************************)

subsubsection {* Abstractions *}

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

subsubsection {* Sets *}

lemma "P (A::'a set)"
refute
oops

lemma "P (A::'a set set)"
refute
oops

lemma "{x. P x} = {y. P y}"
refute
by simp

lemma "x : {x. P x}"
refute
oops

lemma "P op:"
refute
oops

lemma "P (op: x)"
refute
oops

lemma "P Collect"
refute
oops

lemma "A Un B = A Int B"
refute
oops

lemma "(A Int B) Un C = (A Un C) Int B"
refute
oops

lemma "Ball A P \<longrightarrow> Bex A P"
refute
oops

(*****************************************************************************)

subsubsection {* undefined *}

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

subsubsection {* The *}

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

subsubsection {* Eps *}

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

subsubsection {* Subtypes (typedef), typedecl *}

text {* A completely unspecified non-empty subset of @{typ "'a"}: *}

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

subsubsection {* Inductive datatypes *}

text {* unit *}

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

text {* option *}

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

text {* * *}

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

text {* + *}

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

text {* Non-recursive datatypes *}

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

text {* Recursive datatypes *}

text {* nat *}

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
-- {* @{term Suc} is a partial function (regardless of the size
      of the model), hence @{term "P Suc"} is undefined and no
      model will be found *}
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

text {* 'a list *}

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

subsubsection {* Examples involving special functions *}

lemma "card x = 0"
refute [expect = potential]
oops

lemma "finite x"
refute -- {* no finite countermodel exists *}
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

subsubsection {* Type classes and overloading *}

text {* A type class without axioms: *}

class classA

lemma "P (x::'a::classA)"
refute [expect = genuine]
oops

text {* An axiom with a type variable (denoting types which have at least two elements): *}

class classC =
  assumes classC_ax: "\<exists>x y. x \<noteq> y"

lemma "P (x::'a::classC)"
refute [expect = genuine]
oops

lemma "\<exists>x y. (x::'a::classC) \<noteq> y"
(* refute [expect = none] FIXME *)
oops

text {* A type class for which a constant is defined: *}

class classD =
  fixes classD_const :: "'a \<Rightarrow> 'a"
  assumes classD_ax: "classD_const (classD_const x) = classD_const x"

lemma "P (x::'a::classD)"
refute [expect = genuine]
oops

text {* A type class with multiple superclasses: *}

class classE = classC + classD

lemma "P (x::'a::classE)"
refute [expect = genuine]
oops

text {* OFCLASS: *}

lemma "OFCLASS('a::type, type_class)"
refute [expect = none]
by intro_classes

lemma "OFCLASS('a::classC, type_class)"
refute [expect = none]
by intro_classes

lemma "OFCLASS('a::type, classC_class)"
refute [expect = genuine]
oops

text {* Overloading: *}

consts inverse :: "'a \<Rightarrow> 'a"

defs (overloaded)
  inverse_bool: "inverse (b::bool)   == ~ b"
  inverse_set : "inverse (S::'a set) == -S"
  inverse_pair: "inverse p           == (inverse (fst p), inverse (snd p))"

lemma "inverse b"
refute [expect = genuine]
oops

lemma "P (inverse (S::'a set))"
refute [expect = genuine]
oops

lemma "P (inverse (p::'a\<times>'b))"
refute [expect = genuine]
oops

text {* Structured proofs *}

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
