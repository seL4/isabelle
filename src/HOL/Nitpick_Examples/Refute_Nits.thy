(*  Title:      HOL/Nitpick_Examples/Refute_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Refute examples adapted to Nitpick.
*)

section \<open>Refute Examples Adapted to Nitpick\<close>

theory Refute_Nits
imports Main
begin

nitpick_params [verbose, card = 1-6, max_potential = 0,
                sat_solver = MiniSat_JNI, max_threads = 1, timeout = 240]

lemma "P \<and> Q"
apply (rule conjI)
nitpick [expect = genuine] 1
nitpick [expect = genuine] 2
nitpick [expect = genuine]
nitpick [card = 5, expect = genuine]
nitpick [sat_solver = SAT4J, expect = genuine] 2
oops

subsection \<open>Examples and Test Cases\<close>

subsubsection \<open>Propositional logic\<close>

lemma "True"
nitpick [expect = none]
apply auto
done

lemma "False"
nitpick [expect = genuine]
oops

lemma "P"
nitpick [expect = genuine]
oops

lemma "\<not> P"
nitpick [expect = genuine]
oops

lemma "P \<and> Q"
nitpick [expect = genuine]
oops

lemma "P \<or> Q"
nitpick [expect = genuine]
oops

lemma "P \<longrightarrow> Q"
nitpick [expect = genuine]
oops

lemma "(P::bool) = Q"
nitpick [expect = genuine]
oops

lemma "(P \<or> Q) \<longrightarrow> (P \<and> Q)"
nitpick [expect = genuine]
oops

subsubsection \<open>Predicate logic\<close>

lemma "P x y z"
nitpick [expect = genuine]
oops

lemma "P x y \<longrightarrow> P y x"
nitpick [expect = genuine]
oops

lemma "P (f (f x)) \<longrightarrow> P x \<longrightarrow> P (f x)"
nitpick [expect = genuine]
oops

subsubsection \<open>Equality\<close>

lemma "P = True"
nitpick [expect = genuine]
oops

lemma "P = False"
nitpick [expect = genuine]
oops

lemma "x = y"
nitpick [expect = genuine]
oops

lemma "f x = g x"
nitpick [expect = genuine]
oops

lemma "(f::'a\<Rightarrow>'b) = g"
nitpick [expect = genuine]
oops

lemma "(f::('d\<Rightarrow>'d)\<Rightarrow>('c\<Rightarrow>'d)) = g"
nitpick [expect = genuine]
oops

lemma "distinct [a, b]"
nitpick [expect = genuine]
apply simp
nitpick [expect = genuine]
oops

subsubsection \<open>First-Order Logic\<close>

lemma "\<exists>x. P x"
nitpick [expect = genuine]
oops

lemma "\<forall>x. P x"
nitpick [expect = genuine]
oops

lemma "\<exists>!x. P x"
nitpick [expect = genuine]
oops

lemma "Ex P"
nitpick [expect = genuine]
oops

lemma "All P"
nitpick [expect = genuine]
oops

lemma "Ex1 P"
nitpick [expect = genuine]
oops

lemma "(\<exists>x. P x) \<longrightarrow> (\<forall>x. P x)"
nitpick [expect = genuine]
oops

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
nitpick [expect = genuine]
oops

lemma "(\<exists>x. P x) \<longrightarrow> (\<exists>!x. P x)"
nitpick [expect = genuine]
oops

text \<open>A true statement (also testing names of free and bound variables being identical)\<close>

lemma "(\<forall>x y. P x y \<longrightarrow> P y x) \<longrightarrow> (\<forall>x. P x y) \<longrightarrow> P y x"
nitpick [expect = none]
apply fast
done

text \<open>"A type has at most 4 elements."\<close>

lemma "\<not> distinct [a, b, c, d, e]"
nitpick [expect = genuine]
apply simp
nitpick [expect = genuine]
oops

lemma "distinct [a, b, c, d]"
nitpick [expect = genuine]
apply simp
nitpick [expect = genuine]
oops

text \<open>"Every reflexive and symmetric relation is transitive."\<close>

lemma "\<lbrakk>\<forall>x. P x x; \<forall>x y. P x y \<longrightarrow> P y x\<rbrakk> \<Longrightarrow> P x y \<longrightarrow> P y z \<longrightarrow> P x z"
nitpick [expect = genuine]
oops

text \<open>The ``Drinker's theorem''\<close>

lemma "\<exists>x. f x = g x \<longrightarrow> f = g"
nitpick [expect = none]
apply (auto simp add: ext)
done

text \<open>And an incorrect version of it\<close>

lemma "(\<exists>x. f x = g x) \<longrightarrow> f = g"
nitpick [expect = genuine]
oops

text \<open>"Every function has a fixed point."\<close>

lemma "\<exists>x. f x = x"
nitpick [expect = genuine]
oops

text \<open>"Function composition is commutative."\<close>

lemma "f (g x) = g (f x)"
nitpick [expect = genuine]
oops

text \<open>"Two functions that are equivalent wrt.\ the same predicate 'P' are equal."\<close>

lemma "((P::('a\<Rightarrow>'b)\<Rightarrow>bool) f = P g) \<longrightarrow> (f x = g x)"
nitpick [expect = genuine]
oops

subsubsection \<open>Higher-Order Logic\<close>

lemma "\<exists>P. P"
nitpick [expect = none]
apply auto
done

lemma "\<forall>P. P"
nitpick [expect = genuine]
oops

lemma "\<exists>!P. P"
nitpick [expect = none]
apply auto
done

lemma "\<exists>!P. P x"
nitpick [expect = genuine]
oops

lemma "P Q \<or> Q x"
nitpick [expect = genuine]
oops

lemma "x \<noteq> All"
nitpick [expect = genuine]
oops

lemma "x \<noteq> Ex"
nitpick [expect = genuine]
oops

lemma "x \<noteq> Ex1"
nitpick [expect = genuine]
oops

text \<open>``The transitive closure of an arbitrary relation is non-empty.''\<close>

definition "trans" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"trans P \<equiv> (\<forall>x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z)"

definition
"subset" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"subset P Q \<equiv> (\<forall>x y. P x y \<longrightarrow> Q x y)"

definition
"trans_closure" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"trans_closure P Q \<equiv> (subset Q P) \<and> (trans P) \<and> (\<forall>R. subset Q R \<longrightarrow> trans R \<longrightarrow> subset P R)"

lemma "trans_closure T P \<longrightarrow> (\<exists>x y. T x y)"
nitpick [expect = genuine]
oops

text \<open>``The union of transitive closures is equal to the transitive closure of unions.''\<close>

lemma "(\<forall>x y. (P x y \<or> R x y) \<longrightarrow> T x y) \<longrightarrow> trans T \<longrightarrow> (\<forall>Q. (\<forall>x y. (P x y \<or> R x y) \<longrightarrow> Q x y) \<longrightarrow> trans Q \<longrightarrow> subset T Q)
 \<longrightarrow> trans_closure TP P
 \<longrightarrow> trans_closure TR R
 \<longrightarrow> (T x y = (TP x y \<or> TR x y))"
nitpick [expect = genuine]
oops

text \<open>``Every surjective function is invertible.''\<close>

lemma "(\<forall>y. \<exists>x. y = f x) \<longrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"
nitpick [expect = genuine]
oops

text \<open>``Every invertible function is surjective.''\<close>

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
nitpick [expect = genuine]
oops

text \<open>``Every point is a fixed point of some function.''\<close>

lemma "\<exists>f. f x = x"
nitpick [card = 1-7, expect = none]
apply (rule_tac x = "\<lambda>x. x" in exI)
apply simp
done

text \<open>Axiom of Choice: first an incorrect version\<close>

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>!f. \<forall>x. P x (f x))"
nitpick [expect = genuine]
oops

text \<open>And now two correct ones\<close>

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>f. \<forall>x. P x (f x))"
nitpick [card = 1-4, expect = none]
apply (simp add: choice)
done

lemma "(\<forall>x. \<exists>!y. P x y) \<longrightarrow> (\<exists>!f. \<forall>x. P x (f x))"
nitpick [card = 1-3, expect = none]
apply auto
 apply (simp add: ex1_implies_ex choice)
apply (fast intro: ext)
done

subsubsection \<open>Metalogic\<close>

lemma "\<And>x. P x"
nitpick [expect = genuine]
oops

lemma "f x \<equiv> g x"
nitpick [expect = genuine]
oops

lemma "P \<Longrightarrow> Q"
nitpick [expect = genuine]
oops

lemma "\<lbrakk>P; Q; R\<rbrakk> \<Longrightarrow> S"
nitpick [expect = genuine]
oops

lemma "(x \<equiv> Pure.all) \<Longrightarrow> False"
nitpick [expect = genuine]
oops

lemma "(x \<equiv> (\<equiv>)) \<Longrightarrow> False"
nitpick [expect = genuine]
oops

lemma "(x \<equiv> (\<Longrightarrow>)) \<Longrightarrow> False"
nitpick [expect = genuine]
oops

subsubsection \<open>Schematic Variables\<close>

schematic_goal "?P"
nitpick [expect = none]
apply auto
done

schematic_goal "x = ?y"
nitpick [expect = none]
apply auto
done

subsubsection \<open>Abstractions\<close>

lemma "(\<lambda>x. x) = (\<lambda>x. y)"
nitpick [expect = genuine]
oops

lemma "(\<lambda>f. f x) = (\<lambda>f. True)"
nitpick [expect = genuine]
oops

lemma "(\<lambda>x. x) = (\<lambda>y. y)"
nitpick [expect = none]
apply simp
done

subsubsection \<open>Sets\<close>

lemma "P (A::'a set)"
nitpick [expect = genuine]
oops

lemma "P (A::'a set set)"
nitpick [expect = genuine]
oops

lemma "{x. P x} = {y. P y}"
nitpick [expect = none]
apply simp
done

lemma "x \<in> {x. P x}"
nitpick [expect = genuine]
oops

lemma "P (\<in>)"
nitpick [expect = genuine]
oops

lemma "P ((\<in>) x)"
nitpick [expect = genuine]
oops

lemma "P Collect"
nitpick [expect = genuine]
oops

lemma "A Un B = A Int B"
nitpick [expect = genuine]
oops

lemma "(A Int B) Un C = (A Un C) Int B"
nitpick [expect = genuine]
oops

lemma "Ball A P \<longrightarrow> Bex A P"
nitpick [expect = genuine]
oops

subsubsection \<open>@{const undefined}\<close>

lemma "undefined"
nitpick [expect = genuine]
oops

lemma "P undefined"
nitpick [expect = genuine]
oops

lemma "undefined x"
nitpick [expect = genuine]
oops

lemma "undefined undefined"
nitpick [expect = genuine]
oops

subsubsection \<open>@{const The}\<close>

lemma "The P"
nitpick [expect = genuine]
oops

lemma "P The"
nitpick [expect = genuine]
oops

lemma "P (The P)"
nitpick [expect = genuine]
oops

lemma "(THE x. x=y) = z"
nitpick [expect = genuine]
oops

lemma "Ex P \<longrightarrow> P (The P)"
nitpick [expect = genuine]
oops

subsubsection \<open>@{const Eps}\<close>

lemma "Eps P"
nitpick [expect = genuine]
oops

lemma "P Eps"
nitpick [expect = genuine]
oops

lemma "P (Eps P)"
nitpick [expect = genuine]
oops

lemma "(SOME x. x=y) = z"
nitpick [expect = genuine]
oops

lemma "Ex P \<longrightarrow> P (Eps P)"
nitpick [expect = none]
apply (auto simp add: someI)
done

subsubsection \<open>Operations on Natural Numbers\<close>

lemma "(x::nat) + y = 0"
nitpick [expect = genuine]
oops

lemma "(x::nat) = x + x"
nitpick [expect = genuine]
oops

lemma "(x::nat) - y + y = x"
nitpick [expect = genuine]
oops

lemma "(x::nat) = x * x"
nitpick [expect = genuine]
oops

lemma "(x::nat) < x + y"
nitpick [card = 1, expect = genuine]
oops

text \<open>\<times>\<close>

lemma "P (x::'a\<times>'b)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'a\<times>'b. P x"
nitpick [expect = genuine]
oops

lemma "P (x, y)"
nitpick [expect = genuine]
oops

lemma "P (fst x)"
nitpick [expect = genuine]
oops

lemma "P (snd x)"
nitpick [expect = genuine]
oops

lemma "P Pair"
nitpick [expect = genuine]
oops

lemma "P (case x of Pair a b \<Rightarrow> f a b)"
nitpick [expect = genuine]
oops

subsubsection \<open>Subtypes (typedef), typedecl\<close>

text \<open>A completely unspecified non-empty subset of @{typ "'a"}:\<close>

definition "myTdef = insert (undefined::'a) (undefined::'a set)"

typedef 'a myTdef = "myTdef :: 'a set"
unfolding myTdef_def by auto

lemma "(x::'a myTdef) = y"
nitpick [expect = genuine]
oops

typedecl myTdecl

definition "T_bij = {(f::'a\<Rightarrow>'a). \<forall>y. \<exists>!x. f x = y}"

typedef 'a T_bij = "T_bij :: ('a \<Rightarrow> 'a) set"
unfolding T_bij_def by auto

lemma "P (f::(myTdecl myTdef) T_bij)"
nitpick [expect = genuine]
oops

subsubsection \<open>Inductive Datatypes\<close>

text \<open>unit\<close>

lemma "P (x::unit)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::unit. P x"
nitpick [expect = genuine]
oops

lemma "P ()"
nitpick [expect = genuine]
oops

lemma "P (case x of () \<Rightarrow> u)"
nitpick [expect = genuine]
oops

text \<open>option\<close>

lemma "P (x::'a option)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'a option. P x"
nitpick [expect = genuine]
oops

lemma "P None"
nitpick [expect = genuine]
oops

lemma "P (Some x)"
nitpick [expect = genuine]
oops

lemma "P (case x of None \<Rightarrow> n | Some u \<Rightarrow> s u)"
nitpick [expect = genuine]
oops

text \<open>+\<close>

lemma "P (x::'a+'b)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'a+'b. P x"
nitpick [expect = genuine]
oops

lemma "P (Inl x)"
nitpick [expect = genuine]
oops

lemma "P (Inr x)"
nitpick [expect = genuine]
oops

lemma "P Inl"
nitpick [expect = genuine]
oops

lemma "P (case x of Inl a \<Rightarrow> l a | Inr b \<Rightarrow> r b)"
nitpick [expect = genuine]
oops

text \<open>Non-recursive datatypes\<close>

datatype T1 = A | B

lemma "P (x::T1)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::T1. P x"
nitpick [expect = genuine]
oops

lemma "P A"
nitpick [expect = genuine]
oops

lemma "P B"
nitpick [expect = genuine]
oops

lemma "rec_T1 a b A = a"
nitpick [expect = none]
apply simp
done

lemma "rec_T1 a b B = b"
nitpick [expect = none]
apply simp
done

lemma "P (rec_T1 a b x)"
nitpick [expect = genuine]
oops

lemma "P (case x of A \<Rightarrow> a | B \<Rightarrow> b)"
nitpick [expect = genuine]
oops

datatype 'a T2 = C T1 | D 'a

lemma "P (x::'a T2)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'a T2. P x"
nitpick [expect = genuine]
oops

lemma "P D"
nitpick [expect = genuine]
oops

lemma "rec_T2 c d (C x) = c x"
nitpick [expect = none]
apply simp
done

lemma "rec_T2 c d (D x) = d x"
nitpick [expect = none]
apply simp
done

lemma "P (rec_T2 c d x)"
nitpick [expect = genuine]
oops

lemma "P (case x of C u \<Rightarrow> c u | D v \<Rightarrow> d v)"
nitpick [expect = genuine]
oops

datatype ('a, 'b) T3 = E "'a \<Rightarrow> 'b"

lemma "P (x::('a, 'b) T3)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::('a, 'b) T3. P x"
nitpick [expect = genuine]
oops

lemma "P E"
nitpick [expect = genuine]
oops

lemma "rec_T3 e (E x) = e x"
nitpick [card = 1-4, expect = none]
apply simp
done

lemma "P (rec_T3 e x)"
nitpick [expect = genuine]
oops

lemma "P (case x of E f \<Rightarrow> e f)"
nitpick [expect = genuine]
oops

text \<open>Recursive datatypes\<close>

text \<open>nat\<close>

lemma "P (x::nat)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::nat. P x"
nitpick [expect = genuine]
oops

lemma "P (Suc 0)"
nitpick [expect = genuine]
oops

lemma "P Suc"
nitpick [card = 1-7, expect = none]
oops

lemma "rec_nat zero suc 0 = zero"
nitpick [expect = none]
apply simp
done

lemma "rec_nat zero suc (Suc x) = suc x (rec_nat zero suc x)"
nitpick [expect = none]
apply simp
done

lemma "P (rec_nat zero suc x)"
nitpick [expect = genuine]
oops

lemma "P (case x of 0 \<Rightarrow> zero | Suc n \<Rightarrow> suc n)"
nitpick [expect = genuine]
oops

text \<open>'a list\<close>

lemma "P (xs::'a list)"
nitpick [expect = genuine]
oops

lemma "\<forall>xs::'a list. P xs"
nitpick [expect = genuine]
oops

lemma "P [x, y]"
nitpick [expect = genuine]
oops

lemma "rec_list nil cons [] = nil"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "rec_list nil cons (x#xs) = cons x xs (rec_list nil cons xs)"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "P (rec_list nil cons xs)"
nitpick [expect = genuine]
oops

lemma "P (case x of Nil \<Rightarrow> nil | Cons a b \<Rightarrow> cons a b)"
nitpick [expect = genuine]
oops

lemma "(xs::'a list) = ys"
nitpick [expect = genuine]
oops

lemma "a # xs = b # xs"
nitpick [expect = genuine]
oops

datatype BitList = BitListNil | Bit0 BitList | Bit1 BitList

lemma "P (x::BitList)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::BitList. P x"
nitpick [expect = genuine]
oops

lemma "P (Bit0 (Bit1 BitListNil))"
nitpick [expect = genuine]
oops

lemma "rec_BitList nil bit0 bit1 BitListNil = nil"
nitpick [expect = none]
apply simp
done

lemma "rec_BitList nil bit0 bit1 (Bit0 xs) = bit0 xs (rec_BitList nil bit0 bit1 xs)"
nitpick [expect = none]
apply simp
done

lemma "rec_BitList nil bit0 bit1 (Bit1 xs) = bit1 xs (rec_BitList nil bit0 bit1 xs)"
nitpick [expect = none]
apply simp
done

lemma "P (rec_BitList nil bit0 bit1 x)"
nitpick [expect = genuine]
oops

datatype 'a BinTree = Leaf 'a | Node "'a BinTree" "'a BinTree"

lemma "P (x::'a BinTree)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'a BinTree. P x"
nitpick [expect = genuine]
oops

lemma "P (Node (Leaf x) (Leaf y))"
nitpick [expect = genuine]
oops

lemma "rec_BinTree l n (Leaf x) = l x"
nitpick [expect = none]
apply simp
done

lemma "rec_BinTree l n (Node x y) = n x y (rec_BinTree l n x) (rec_BinTree l n y)"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "P (rec_BinTree l n x)"
nitpick [expect = genuine]
oops

lemma "P (case x of Leaf a \<Rightarrow> l a | Node a b \<Rightarrow> n a b)"
nitpick [expect = genuine]
oops

text \<open>Mutually recursive datatypes\<close>

datatype 'a aexp = Number 'a | ITE "'a bexp" "'a aexp" "'a aexp"
 and 'a bexp = Equal "'a aexp" "'a aexp"

lemma "P (x::'a aexp)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'a aexp. P x"
nitpick [expect = genuine]
oops

lemma "P (ITE (Equal (Number x) (Number y)) (Number x) (Number y))"
nitpick [expect = genuine]
oops

lemma "P (x::'a bexp)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'a bexp. P x"
nitpick [expect = genuine]
oops

lemma "rec_aexp number ite equal (Number x) = number x"
nitpick [card = 1-3, expect = none]
apply simp
done

lemma "rec_aexp number ite equal (ITE x y z) = ite x y z (rec_bexp number ite equal x) (rec_aexp number ite equal y) (rec_aexp number ite equal z)"
nitpick [card = 1-3, expect = none]
apply simp
done

lemma "P (rec_aexp number ite equal x)"
nitpick [expect = genuine]
oops

lemma "P (case x of Number a \<Rightarrow> number a | ITE b a1 a2 \<Rightarrow> ite b a1 a2)"
nitpick [expect = genuine]
oops

lemma "rec_bexp number ite equal (Equal x y) = equal x y (rec_aexp number ite equal x) (rec_aexp number ite equal y)"
nitpick [card = 1-3, expect = none]
apply simp
done

lemma "P (rec_bexp number ite equal x)"
nitpick [expect = genuine]
oops

lemma "P (case x of Equal a1 a2 \<Rightarrow> equal a1 a2)"
nitpick [expect = genuine]
oops

datatype X = A | B X | C Y and Y = D X | E Y | F

lemma "P (x::X)"
nitpick [expect = genuine]
oops

lemma "P (y::Y)"
nitpick [expect = genuine]
oops

lemma "P (B (B A))"
nitpick [expect = genuine]
oops

lemma "P (B (C F))"
nitpick [expect = genuine]
oops

lemma "P (C (D A))"
nitpick [expect = genuine]
oops

lemma "P (C (E F))"
nitpick [expect = genuine]
oops

lemma "P (D (B A))"
nitpick [expect = genuine]
oops

lemma "P (D (C F))"
nitpick [expect = genuine]
oops

lemma "P (E (D A))"
nitpick [expect = genuine]
oops

lemma "P (E (E F))"
nitpick [expect = genuine]
oops

lemma "P (C (D (C F)))"
nitpick [expect = genuine]
oops

lemma "rec_X a b c d e f A = a"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "rec_X a b c d e f (B x) = b x (rec_X a b c d e f x)"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "rec_X a b c d e f (C y) = c y (rec_Y a b c d e f y)"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "rec_Y a b c d e f (D x) = d x (rec_X a b c d e f x)"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "rec_Y a b c d e f (E y) = e y (rec_Y a b c d e f y)"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "rec_Y a b c d e f F = f"
nitpick [card = 1-5, expect = none]
apply simp
done

lemma "P (rec_X a b c d e f x)"
nitpick [expect = genuine]
oops

lemma "P (rec_Y a b c d e f y)"
nitpick [expect = genuine]
oops

text \<open>Other datatype examples\<close>

text \<open>Indirect recursion is implemented via mutual recursion.\<close>

datatype XOpt = CX "XOpt option" | DX "bool \<Rightarrow> XOpt option"

lemma "P (x::XOpt)"
nitpick [expect = genuine]
oops

lemma "P (CX None)"
nitpick [expect = genuine]
oops

lemma "P (CX (Some (CX None)))"
nitpick [expect = genuine]
oops

lemma "P (rec_X cx dx n1 s1 n2 s2 x)"
nitpick [expect = genuine]
oops

datatype 'a YOpt = CY "('a \<Rightarrow> 'a YOpt) option"

lemma "P (x::'a YOpt)"
nitpick [expect = genuine]
oops

lemma "P (CY None)"
nitpick [expect = genuine]
oops

lemma "P (CY (Some (\<lambda>a. CY None)))"
nitpick [expect = genuine]
oops

datatype Trie = TR "Trie list"

lemma "P (x::Trie)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::Trie. P x"
nitpick [expect = genuine]
oops

lemma "P (TR [TR []])"
nitpick [expect = genuine]
oops

datatype InfTree = Leaf | Node "nat \<Rightarrow> InfTree"

lemma "P (x::InfTree)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::InfTree. P x"
nitpick [expect = genuine]
oops

lemma "P (Node (\<lambda>n. Leaf))"
nitpick [expect = genuine]
oops

lemma "rec_InfTree leaf node Leaf = leaf"
nitpick [card = 1-3, expect = none]
apply simp
done

lemma "rec_InfTree leaf node (Node g) = node ((\<lambda>InfTree. (InfTree, rec_InfTree leaf node InfTree)) \<circ> g)"
nitpick [card = 1-3, expect = none]
apply simp
done

lemma "P (rec_InfTree leaf node x)"
nitpick [expect = genuine]
oops

datatype 'a lambda = Var 'a | App "'a lambda" "'a lambda" | Lam "'a \<Rightarrow> 'a lambda"

lemma "P (x::'a lambda)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'a lambda. P x"
nitpick [expect = genuine]
oops

lemma "P (Lam (\<lambda>a. Var a))"
nitpick [card = 1-5, expect = none]
nitpick [card 'a = 4, card "'a lambda" = 5, expect = genuine]
oops

lemma "rec_lambda var app lam (Var x) = var x"
nitpick [card = 1-3, expect = none]
apply simp
done

lemma "rec_lambda var app lam (App x y) = app x y (rec_lambda var app lam x) (rec_lambda var app lam y)"
nitpick [card = 1-3, expect = none]
apply simp
done

lemma "rec_lambda var app lam (Lam x) = lam ((\<lambda>lambda. (lambda, rec_lambda var app lam lambda)) \<circ> x)"
nitpick [card = 1-3, expect = none]
apply simp
done

lemma "P (rec_lambda v a l x)"
nitpick [expect = genuine]
oops

text \<open>Taken from "Inductive datatypes in HOL", p. 8:\<close>

datatype (dead 'a, 'b) T = C "'a \<Rightarrow> bool" | D "'b list"
datatype 'c U = E "('c, 'c U) T"

lemma "P (x::'c U)"
nitpick [expect = genuine]
oops

lemma "\<forall>x::'c U. P x"
nitpick [expect = genuine]
oops

lemma "P (E (C (\<lambda>a. True)))"
nitpick [expect = genuine]
oops

subsubsection \<open>Records\<close>

record ('a, 'b) point =
  xpos :: 'a
  ypos :: 'b

lemma "(x::('a, 'b) point) = y"
nitpick [expect = genuine]
oops

record ('a, 'b, 'c) extpoint = "('a, 'b) point" +
  ext :: 'c

lemma "(x::('a, 'b, 'c) extpoint) = y"
nitpick [expect = genuine]
oops

subsubsection \<open>Inductively Defined Sets\<close>

inductive_set undefinedSet :: "'a set" where
"undefined \<in> undefinedSet"

lemma "x \<in> undefinedSet"
nitpick [expect = genuine]
oops

inductive_set evenCard :: "'a set set"
where
"{} \<in> evenCard" |
"\<lbrakk>S \<in> evenCard; x \<notin> S; y \<notin> S; x \<noteq> y\<rbrakk> \<Longrightarrow> S \<union> {x, y} \<in> evenCard"

lemma "S \<in> evenCard"
nitpick [expect = genuine]
oops

inductive_set
even :: "nat set"
and odd :: "nat set"
where
"0 \<in> even" |
"n \<in> even \<Longrightarrow> Suc n \<in> odd" |
"n \<in> odd \<Longrightarrow> Suc n \<in> even"

lemma "n \<in> odd"
nitpick [expect = genuine]
oops

consts f :: "'a \<Rightarrow> 'a"

inductive_set a_even :: "'a set" and a_odd :: "'a set" where
"undefined \<in> a_even" |
"x \<in> a_even \<Longrightarrow> f x \<in> a_odd" |
"x \<in> a_odd \<Longrightarrow> f x \<in> a_even"

lemma "x \<in> a_odd"
nitpick [expect = genuine]
oops

subsubsection \<open>Examples Involving Special Functions\<close>

lemma "card x = 0"
nitpick [expect = genuine]
oops

lemma "finite x"
nitpick [expect = none]
oops

lemma "xs @ [] = ys @ []"
nitpick [expect = genuine]
oops

lemma "xs @ ys = ys @ xs"
nitpick [expect = genuine]
oops

lemma "f (lfp f) = lfp f"
nitpick [card = 2, expect = genuine]
oops

lemma "f (gfp f) = gfp f"
nitpick [card = 2, expect = genuine]
oops

lemma "lfp f = gfp f"
nitpick [card = 2, expect = genuine]
oops

subsubsection \<open>Axiomatic Type Classes and Overloading\<close>

text \<open>A type class without axioms:\<close>

class classA

lemma "P (x::'a::classA)"
nitpick [expect = genuine]
oops

text \<open>An axiom with a type variable (denoting types which have at least two elements):\<close>

class classC =
  assumes classC_ax: "\<exists>x y. x \<noteq> y"

lemma "P (x::'a::classC)"
nitpick [expect = genuine]
oops

lemma "\<exists>x y. (x::'a::classC) \<noteq> y"
nitpick [expect = none]
sorry

text \<open>A type class for which a constant is defined:\<close>

class classD =
  fixes classD_const :: "'a \<Rightarrow> 'a"
  assumes classD_ax: "classD_const (classD_const x) = classD_const x"

lemma "P (x::'a::classD)"
nitpick [expect = genuine]
oops

text \<open>A type class with multiple superclasses:\<close>

class classE = classC + classD

lemma "P (x::'a::classE)"
nitpick [expect = genuine]
oops

text \<open>OFCLASS:\<close>

lemma "OFCLASS('a::type, type_class)"
nitpick [expect = none]
apply intro_classes
done

lemma "OFCLASS('a::classC, type_class)"
nitpick [expect = none]
apply intro_classes
done

lemma "OFCLASS('a::type, classC_class)"
nitpick [expect = genuine]
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
nitpick [expect = genuine]
oops

lemma "P (inverse (S::'a set))"
nitpick [expect = genuine]
oops

lemma "P (inverse (p::'a\<times>'b))"
nitpick [expect = genuine]
oops

end
