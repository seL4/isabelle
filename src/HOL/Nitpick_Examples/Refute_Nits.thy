(*  Title:      HOL/Nitpick_Examples/Refute_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Refute examples adapted to Nitpick.
*)

header {* Refute Examples Adapted to Nitpick *}

theory Refute_Nits
imports Main
begin

nitpick_params [verbose, card = 1\<emdash>6, max_potential = 0,
                sat_solver = MiniSat_JNI, max_threads = 1, timeout = 240]

lemma "P \<and> Q"
apply (rule conjI)
nitpick [expect = genuine] 1
nitpick [expect = genuine] 2
nitpick [expect = genuine]
nitpick [card = 5, expect = genuine]
nitpick [sat_solver = SAT4J, expect = genuine] 2
oops

subsection {* Examples and Test Cases *}

subsubsection {* Propositional logic *}

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

lemma "(P\<Colon>bool) = Q"
nitpick [expect = genuine]
oops

lemma "(P \<or> Q) \<longrightarrow> (P \<and> Q)"
nitpick [expect = genuine]
oops

subsubsection {* Predicate logic *}

lemma "P x y z"
nitpick [expect = genuine]
oops

lemma "P x y \<longrightarrow> P y x"
nitpick [expect = genuine]
oops

lemma "P (f (f x)) \<longrightarrow> P x \<longrightarrow> P (f x)"
nitpick [expect = genuine]
oops

subsubsection {* Equality *}

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

lemma "(f\<Colon>'a\<Rightarrow>'b) = g"
nitpick [expect = genuine]
oops

lemma "(f\<Colon>('d\<Rightarrow>'d)\<Rightarrow>('c\<Rightarrow>'d)) = g"
nitpick [expect = genuine]
oops

lemma "distinct [a, b]"
nitpick [expect = genuine]
apply simp
nitpick [expect = genuine]
oops

subsubsection {* First-Order Logic *}

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

text {* A true statement (also testing names of free and bound variables being identical) *}

lemma "(\<forall>x y. P x y \<longrightarrow> P y x) \<longrightarrow> (\<forall>x. P x y) \<longrightarrow> P y x"
nitpick [expect = none]
apply fast
done

text {* "A type has at most 4 elements." *}

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

text {* "Every reflexive and symmetric relation is transitive." *}

lemma "\<lbrakk>\<forall>x. P x x; \<forall>x y. P x y \<longrightarrow> P y x\<rbrakk> \<Longrightarrow> P x y \<longrightarrow> P y z \<longrightarrow> P x z"
nitpick [expect = genuine]
oops

text {* The ``Drinker's theorem'' *}

lemma "\<exists>x. f x = g x \<longrightarrow> f = g"
nitpick [expect = none]
apply (auto simp add: ext)
done

text {* And an incorrect version of it *}

lemma "(\<exists>x. f x = g x) \<longrightarrow> f = g"
nitpick [expect = genuine]
oops

text {* "Every function has a fixed point." *}

lemma "\<exists>x. f x = x"
nitpick [expect = genuine]
oops

text {* "Function composition is commutative." *}

lemma "f (g x) = g (f x)"
nitpick [expect = genuine]
oops

text {* "Two functions that are equivalent wrt.\ the same predicate 'P' are equal." *}

lemma "((P\<Colon>('a\<Rightarrow>'b)\<Rightarrow>bool) f = P g) \<longrightarrow> (f x = g x)"
nitpick [expect = genuine]
oops

subsubsection {* Higher-Order Logic *}

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

text {* ``The transitive closure of an arbitrary relation is non-empty.'' *}

definition "trans" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"trans P \<equiv> (ALL x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z)"

definition
"subset" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"subset P Q \<equiv> (ALL x y. P x y \<longrightarrow> Q x y)"

definition
"trans_closure" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"trans_closure P Q \<equiv> (subset Q P) \<and> (trans P) \<and> (ALL R. subset Q R \<longrightarrow> trans R \<longrightarrow> subset P R)"

lemma "trans_closure T P \<longrightarrow> (\<exists>x y. T x y)"
nitpick [expect = genuine]
oops

text {* ``The union of transitive closures is equal to the transitive closure of unions.'' *}

lemma "(\<forall>x y. (P x y \<or> R x y) \<longrightarrow> T x y) \<longrightarrow> trans T \<longrightarrow> (\<forall>Q. (\<forall>x y. (P x y \<or> R x y) \<longrightarrow> Q x y) \<longrightarrow> trans Q \<longrightarrow> subset T Q)
 \<longrightarrow> trans_closure TP P
 \<longrightarrow> trans_closure TR R
 \<longrightarrow> (T x y = (TP x y \<or> TR x y))"
nitpick [expect = genuine]
oops

text {* ``Every surjective function is invertible.'' *}

lemma "(\<forall>y. \<exists>x. y = f x) \<longrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"
nitpick [expect = genuine]
oops

text {* ``Every invertible function is surjective.'' *}

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
nitpick [expect = genuine]
oops

text {* ``Every point is a fixed point of some function.'' *}

lemma "\<exists>f. f x = x"
nitpick [card = 1\<emdash>7, expect = none]
apply (rule_tac x = "\<lambda>x. x" in exI)
apply simp
done

text {* Axiom of Choice: first an incorrect version *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>!f. \<forall>x. P x (f x))"
nitpick [expect = genuine]
oops

text {* And now two correct ones *}

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

subsubsection {* Metalogic *}

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

lemma "(x \<equiv> all) \<Longrightarrow> False"
nitpick [expect = genuine]
oops

lemma "(x \<equiv> (op \<equiv>)) \<Longrightarrow> False"
nitpick [expect = genuine]
oops

lemma "(x \<equiv> (op \<Longrightarrow>)) \<Longrightarrow> False"
nitpick [expect = genuine]
oops

subsubsection {* Schematic Variables *}

schematic_lemma "?P"
nitpick [expect = none]
apply auto
done

schematic_lemma "x = ?y"
nitpick [expect = none]
apply auto
done

subsubsection {* Abstractions *}

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

subsubsection {* Sets *}

lemma "P (A\<Colon>'a set)"
nitpick [expect = genuine]
oops

lemma "P (A\<Colon>'a set set)"
nitpick [expect = genuine]
oops

lemma "{x. P x} = {y. P y}"
nitpick [expect = none]
apply simp
done

lemma "x \<in> {x. P x}"
nitpick [expect = genuine]
oops

lemma "P (op \<in>)"
nitpick [expect = genuine]
oops

lemma "P (op \<in> x)"
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

subsubsection {* @{const undefined} *}

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

subsubsection {* @{const The} *}

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

subsubsection {* @{const Eps} *}

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

subsubsection {* Operations on Natural Numbers *}

lemma "(x\<Colon>nat) + y = 0"
nitpick [expect = genuine]
oops

lemma "(x\<Colon>nat) = x + x"
nitpick [expect = genuine]
oops

lemma "(x\<Colon>nat) - y + y = x"
nitpick [expect = genuine]
oops

lemma "(x\<Colon>nat) = x * x"
nitpick [expect = genuine]
oops

lemma "(x\<Colon>nat) < x + y"
nitpick [card = 1, expect = genuine]
oops

text {* \<times> *}

lemma "P (x\<Colon>'a\<times>'b)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'a\<times>'b. P x"
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

lemma "prod_rec f p = f (fst p) (snd p)"
nitpick [expect = none]
by (case_tac p) auto

lemma "prod_rec f (a, b) = f a b"
nitpick [expect = none]
by auto

lemma "P (prod_rec f x)"
nitpick [expect = genuine]
oops

lemma "P (case x of Pair a b \<Rightarrow> f a b)"
nitpick [expect = genuine]
oops

subsubsection {* Subtypes (typedef), typedecl *}

text {* A completely unspecified non-empty subset of @{typ "'a"}: *}

definition "myTdef = insert (undefined::'a) (undefined::'a set)"

typedef 'a myTdef = "myTdef :: 'a set"
unfolding myTdef_def by auto

lemma "(x\<Colon>'a myTdef) = y"
nitpick [expect = genuine]
oops

typedecl myTdecl

definition "T_bij = {(f::'a\<Rightarrow>'a). \<forall>y. \<exists>!x. f x = y}"

typedef 'a T_bij = "T_bij :: ('a \<Rightarrow> 'a) set"
unfolding T_bij_def by auto

lemma "P (f\<Colon>(myTdecl myTdef) T_bij)"
nitpick [expect = genuine]
oops

subsubsection {* Inductive Datatypes *}

text {* unit *}

lemma "P (x\<Colon>unit)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>unit. P x"
nitpick [expect = genuine]
oops

lemma "P ()"
nitpick [expect = genuine]
oops

lemma "unit_rec u x = u"
nitpick [expect = none]
apply simp
done

lemma "P (unit_rec u x)"
nitpick [expect = genuine]
oops

lemma "P (case x of () \<Rightarrow> u)"
nitpick [expect = genuine]
oops

text {* option *}

lemma "P (x\<Colon>'a option)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'a option. P x"
nitpick [expect = genuine]
oops

lemma "P None"
nitpick [expect = genuine]
oops

lemma "P (Some x)"
nitpick [expect = genuine]
oops

lemma "option_rec n s None = n"
nitpick [expect = none]
apply simp
done

lemma "option_rec n s (Some x) = s x"
nitpick [expect = none]
apply simp
done

lemma "P (option_rec n s x)"
nitpick [expect = genuine]
oops

lemma "P (case x of None \<Rightarrow> n | Some u \<Rightarrow> s u)"
nitpick [expect = genuine]
oops

text {* + *}

lemma "P (x\<Colon>'a+'b)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'a+'b. P x"
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

lemma "sum_rec l r (Inl x) = l x"
nitpick [expect = none]
apply simp
done

lemma "sum_rec l r (Inr x) = r x"
nitpick [expect = none]
apply simp
done

lemma "P (sum_rec l r x)"
nitpick [expect = genuine]
oops

lemma "P (case x of Inl a \<Rightarrow> l a | Inr b \<Rightarrow> r b)"
nitpick [expect = genuine]
oops

text {* Non-recursive datatypes *}

datatype T1 = A | B

lemma "P (x\<Colon>T1)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>T1. P x"
nitpick [expect = genuine]
oops

lemma "P A"
nitpick [expect = genuine]
oops

lemma "P B"
nitpick [expect = genuine]
oops

lemma "T1_rec a b A = a"
nitpick [expect = none]
apply simp
done

lemma "T1_rec a b B = b"
nitpick [expect = none]
apply simp
done

lemma "P (T1_rec a b x)"
nitpick [expect = genuine]
oops

lemma "P (case x of A \<Rightarrow> a | B \<Rightarrow> b)"
nitpick [expect = genuine]
oops

datatype 'a T2 = C T1 | D 'a

lemma "P (x\<Colon>'a T2)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'a T2. P x"
nitpick [expect = genuine]
oops

lemma "P D"
nitpick [expect = genuine]
oops

lemma "T2_rec c d (C x) = c x"
nitpick [expect = none]
apply simp
done

lemma "T2_rec c d (D x) = d x"
nitpick [expect = none]
apply simp
done

lemma "P (T2_rec c d x)"
nitpick [expect = genuine]
oops

lemma "P (case x of C u \<Rightarrow> c u | D v \<Rightarrow> d v)"
nitpick [expect = genuine]
oops

datatype ('a, 'b) T3 = E "'a \<Rightarrow> 'b"

lemma "P (x\<Colon>('a, 'b) T3)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>('a, 'b) T3. P x"
nitpick [expect = genuine]
oops

lemma "P E"
nitpick [expect = genuine]
oops

lemma "T3_rec e (E x) = e x"
nitpick [card = 1\<emdash>4, expect = none]
apply simp
done

lemma "P (T3_rec e x)"
nitpick [expect = genuine]
oops

lemma "P (case x of E f \<Rightarrow> e f)"
nitpick [expect = genuine]
oops

text {* Recursive datatypes *}

text {* nat *}

lemma "P (x\<Colon>nat)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>nat. P x"
nitpick [expect = genuine]
oops

lemma "P (Suc 0)"
nitpick [expect = genuine]
oops

lemma "P Suc"
nitpick [card = 1\<emdash>7, expect = none]
oops

lemma "nat_rec zero suc 0 = zero"
nitpick [expect = none]
apply simp
done

lemma "nat_rec zero suc (Suc x) = suc x (nat_rec zero suc x)"
nitpick [expect = none]
apply simp
done

lemma "P (nat_rec zero suc x)"
nitpick [expect = genuine]
oops

lemma "P (case x of 0 \<Rightarrow> zero | Suc n \<Rightarrow> suc n)"
nitpick [expect = genuine]
oops

text {* 'a list *}

lemma "P (xs\<Colon>'a list)"
nitpick [expect = genuine]
oops

lemma "\<forall>xs\<Colon>'a list. P xs"
nitpick [expect = genuine]
oops

lemma "P [x, y]"
nitpick [expect = genuine]
oops

lemma "list_rec nil cons [] = nil"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "list_rec nil cons (x#xs) = cons x xs (list_rec nil cons xs)"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "P (list_rec nil cons xs)"
nitpick [expect = genuine]
oops

lemma "P (case x of Nil \<Rightarrow> nil | Cons a b \<Rightarrow> cons a b)"
nitpick [expect = genuine]
oops

lemma "(xs\<Colon>'a list) = ys"
nitpick [expect = genuine]
oops

lemma "a # xs = b # xs"
nitpick [expect = genuine]
oops

datatype BitList = BitListNil | Bit0 BitList | Bit1 BitList

lemma "P (x\<Colon>BitList)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>BitList. P x"
nitpick [expect = genuine]
oops

lemma "P (Bit0 (Bit1 BitListNil))"
nitpick [expect = genuine]
oops

lemma "BitList_rec nil bit0 bit1 BitListNil = nil"
nitpick [expect = none]
apply simp
done

lemma "BitList_rec nil bit0 bit1 (Bit0 xs) = bit0 xs (BitList_rec nil bit0 bit1 xs)"
nitpick [expect = none]
apply simp
done

lemma "BitList_rec nil bit0 bit1 (Bit1 xs) = bit1 xs (BitList_rec nil bit0 bit1 xs)"
nitpick [expect = none]
apply simp
done

lemma "P (BitList_rec nil bit0 bit1 x)"
nitpick [expect = genuine]
oops

datatype 'a BinTree = Leaf 'a | Node "'a BinTree" "'a BinTree"

lemma "P (x\<Colon>'a BinTree)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'a BinTree. P x"
nitpick [expect = genuine]
oops

lemma "P (Node (Leaf x) (Leaf y))"
nitpick [expect = genuine]
oops

lemma "BinTree_rec l n (Leaf x) = l x"
nitpick [expect = none]
apply simp
done

lemma "BinTree_rec l n (Node x y) = n x y (BinTree_rec l n x) (BinTree_rec l n y)"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "P (BinTree_rec l n x)"
nitpick [expect = genuine]
oops

lemma "P (case x of Leaf a \<Rightarrow> l a | Node a b \<Rightarrow> n a b)"
nitpick [expect = genuine]
oops

text {* Mutually recursive datatypes *}

datatype 'a aexp = Number 'a | ITE "'a bexp" "'a aexp" "'a aexp"
 and 'a bexp = Equal "'a aexp" "'a aexp"

lemma "P (x\<Colon>'a aexp)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'a aexp. P x"
nitpick [expect = genuine]
oops

lemma "P (ITE (Equal (Number x) (Number y)) (Number x) (Number y))"
nitpick [expect = genuine]
oops

lemma "P (x\<Colon>'a bexp)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'a bexp. P x"
nitpick [expect = genuine]
oops

lemma "aexp_bexp_rec_1 number ite equal (Number x) = number x"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "aexp_bexp_rec_1 number ite equal (ITE x y z) = ite x y z (aexp_bexp_rec_2 number ite equal x) (aexp_bexp_rec_1 number ite equal y) (aexp_bexp_rec_1 number ite equal z)"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "P (aexp_bexp_rec_1 number ite equal x)"
nitpick [expect = genuine]
oops

lemma "P (case x of Number a \<Rightarrow> number a | ITE b a1 a2 \<Rightarrow> ite b a1 a2)"
nitpick [expect = genuine]
oops

lemma "aexp_bexp_rec_2 number ite equal (Equal x y) = equal x y (aexp_bexp_rec_1 number ite equal x) (aexp_bexp_rec_1 number ite equal y)"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "P (aexp_bexp_rec_2 number ite equal x)"
nitpick [expect = genuine]
oops

lemma "P (case x of Equal a1 a2 \<Rightarrow> equal a1 a2)"
nitpick [expect = genuine]
oops

datatype X = A | B X | C Y
     and Y = D X | E Y | F

lemma "P (x\<Colon>X)"
nitpick [expect = genuine]
oops

lemma "P (y\<Colon>Y)"
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

lemma "X_Y_rec_1 a b c d e f A = a"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "X_Y_rec_1 a b c d e f (B x) = b x (X_Y_rec_1 a b c d e f x)"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "X_Y_rec_1 a b c d e f (C y) = c y (X_Y_rec_2 a b c d e f y)"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "X_Y_rec_2 a b c d e f (D x) = d x (X_Y_rec_1 a b c d e f x)"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "X_Y_rec_2 a b c d e f (E y) = e y (X_Y_rec_2 a b c d e f y)"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "X_Y_rec_2 a b c d e f F = f"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "P (X_Y_rec_1 a b c d e f x)"
nitpick [expect = genuine]
oops

lemma "P (X_Y_rec_2 a b c d e f y)"
nitpick [expect = genuine]
oops

text {* Other datatype examples *}

text {* Indirect recursion is implemented via mutual recursion. *}

datatype XOpt = CX "XOpt option" | DX "bool \<Rightarrow> XOpt option"

lemma "P (x\<Colon>XOpt)"
nitpick [expect = genuine]
oops

lemma "P (CX None)"
nitpick [expect = genuine]
oops

lemma "P (CX (Some (CX None)))"
nitpick [expect = genuine]
oops

lemma "XOpt_rec_1 cx dx n1 s1 n2 s2 (CX x) = cx x (XOpt_rec_2 cx dx n1 s1 n2 s2 x)"
nitpick [card = 1\<emdash>5, expect = none]
apply simp
done

lemma "XOpt_rec_1 cx dx n1 s1 n2 s2 (DX x) = dx x (\<lambda>b. XOpt_rec_3 cx dx n1 s1 n2 s2 (x b))"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "XOpt_rec_2 cx dx n1 s1 n2 s2 None = n1"
nitpick [card = 1\<emdash>4, expect = none]
apply simp
done

lemma "XOpt_rec_2 cx dx n1 s1 n2 s2 (Some x) = s1 x (XOpt_rec_1 cx dx n1 s1 n2 s2 x)"
nitpick [card = 1\<emdash>4, expect = none]
apply simp
done

lemma "XOpt_rec_3 cx dx n1 s1 n2 s2 None = n2"
nitpick [card = 1\<emdash>4, expect = none]
apply simp
done

lemma "XOpt_rec_3 cx dx n1 s1 n2 s2 (Some x) = s2 x (XOpt_rec_1 cx dx n1 s1 n2 s2 x)"
nitpick [card = 1\<emdash>4, expect = none]
apply simp
done

lemma "P (XOpt_rec_1 cx dx n1 s1 n2 s2 x)"
nitpick [expect = genuine]
oops

lemma "P (XOpt_rec_2 cx dx n1 s1 n2 s2 x)"
nitpick [expect = genuine]
oops

lemma "P (XOpt_rec_3 cx dx n1 s1 n2 s2 x)"
nitpick [expect = genuine]
oops

datatype 'a YOpt = CY "('a \<Rightarrow> 'a YOpt) option"

lemma "P (x\<Colon>'a YOpt)"
nitpick [expect = genuine]
oops

lemma "P (CY None)"
nitpick [expect = genuine]
oops

lemma "P (CY (Some (\<lambda>a. CY None)))"
nitpick [expect = genuine]
oops

lemma "YOpt_rec_1 cy n s (CY x) = cy x (YOpt_rec_2 cy n s x)"
nitpick [card = 1\<emdash>2, expect = none]
apply simp
done

lemma "YOpt_rec_2 cy n s None = n"
nitpick [card = 1\<emdash>2, expect = none]
apply simp
done

lemma "YOpt_rec_2 cy n s (Some x) = s x (\<lambda>a. YOpt_rec_1 cy n s (x a))"
nitpick [card = 1\<emdash>2, expect = none]
apply simp
done

lemma "P (YOpt_rec_1 cy n s x)"
nitpick [expect = genuine]
oops

lemma "P (YOpt_rec_2 cy n s x)"
nitpick [expect = genuine]
oops

datatype Trie = TR "Trie list"

lemma "P (x\<Colon>Trie)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>Trie. P x"
nitpick [expect = genuine]
oops

lemma "P (TR [TR []])"
nitpick [expect = genuine]
oops

lemma "Trie_rec_1 tr nil cons (TR x) = tr x (Trie_rec_2 tr nil cons x)"
nitpick [card = 1\<emdash>4, expect = none]
apply simp
done

lemma "Trie_rec_2 tr nil cons [] = nil"
nitpick [card = 1\<emdash>4, expect = none]
apply simp
done

lemma "Trie_rec_2 tr nil cons (x#xs) = cons x xs (Trie_rec_1 tr nil cons x) (Trie_rec_2 tr nil cons xs)"
nitpick [card = 1\<emdash>4, expect = none]
apply simp
done

lemma "P (Trie_rec_1 tr nil cons x)"
nitpick [card = 1, expect = genuine]
oops

lemma "P (Trie_rec_2 tr nil cons x)"
nitpick [card = 1, expect = genuine]
oops

datatype InfTree = Leaf | Node "nat \<Rightarrow> InfTree"

lemma "P (x\<Colon>InfTree)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>InfTree. P x"
nitpick [expect = genuine]
oops

lemma "P (Node (\<lambda>n. Leaf))"
nitpick [expect = genuine]
oops

lemma "InfTree_rec leaf node Leaf = leaf"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "InfTree_rec leaf node (Node x) = node x (\<lambda>n. InfTree_rec leaf node (x n))"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "P (InfTree_rec leaf node x)"
nitpick [expect = genuine]
oops

datatype 'a lambda = Var 'a | App "'a lambda" "'a lambda" | Lam "'a \<Rightarrow> 'a lambda"

lemma "P (x\<Colon>'a lambda)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'a lambda. P x"
nitpick [expect = genuine]
oops

lemma "P (Lam (\<lambda>a. Var a))"
nitpick [card = 1\<emdash>5, expect = none]
nitpick [card 'a = 4, card "'a lambda" = 5, expect = genuine]
oops

lemma "lambda_rec var app lam (Var x) = var x"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "lambda_rec var app lam (App x y) = app x y (lambda_rec var app lam x) (lambda_rec var app lam y)"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "lambda_rec var app lam (Lam x) = lam x (\<lambda>a. lambda_rec var app lam (x a))"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "P (lambda_rec v a l x)"
nitpick [expect = genuine]
oops

text {* Taken from "Inductive datatypes in HOL", p. 8: *}

datatype ('a, 'b) T = C "'a \<Rightarrow> bool" | D "'b list"
datatype 'c U = E "('c, 'c U) T"

lemma "P (x\<Colon>'c U)"
nitpick [expect = genuine]
oops

lemma "\<forall>x\<Colon>'c U. P x"
nitpick [expect = genuine]
oops

lemma "P (E (C (\<lambda>a. True)))"
nitpick [expect = genuine]
oops

lemma "U_rec_1 e c d nil cons (E x) = e x (U_rec_2 e c d nil cons x)"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "U_rec_2 e c d nil cons (C x) = c x"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "U_rec_2 e c d nil cons (D x) = d x (U_rec_3 e c d nil cons x)"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "U_rec_3 e c d nil cons [] = nil"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "U_rec_3 e c d nil cons (x#xs) = cons x xs (U_rec_1 e c d nil cons x) (U_rec_3 e c d nil cons xs)"
nitpick [card = 1\<emdash>3, expect = none]
apply simp
done

lemma "P (U_rec_1 e c d nil cons x)"
nitpick [expect = genuine]
oops

lemma "P (U_rec_2 e c d nil cons x)"
nitpick [card = 1, expect = genuine]
oops

lemma "P (U_rec_3 e c d nil cons x)"
nitpick [card = 1, expect = genuine]
oops

subsubsection {* Records *}

record ('a, 'b) point =
  xpos :: 'a
  ypos :: 'b

lemma "(x\<Colon>('a, 'b) point) = y"
nitpick [expect = genuine]
oops

record ('a, 'b, 'c) extpoint = "('a, 'b) point" +
  ext :: 'c

lemma "(x\<Colon>('a, 'b, 'c) extpoint) = y"
nitpick [expect = genuine]
oops

subsubsection {* Inductively Defined Sets *}

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

subsubsection {* Examples Involving Special Functions *}

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

subsubsection {* Axiomatic Type Classes and Overloading *}

text {* A type class without axioms: *}

class classA

lemma "P (x\<Colon>'a\<Colon>classA)"
nitpick [expect = genuine]
oops

text {* An axiom with a type variable (denoting types which have at least two elements): *}

class classC =
  assumes classC_ax: "\<exists>x y. x \<noteq> y"

lemma "P (x\<Colon>'a\<Colon>classC)"
nitpick [expect = genuine]
oops

lemma "\<exists>x y. (x\<Colon>'a\<Colon>classC) \<noteq> y"
nitpick [expect = none]
sorry

text {* A type class for which a constant is defined: *}

class classD =
  fixes classD_const :: "'a \<Rightarrow> 'a"
  assumes classD_ax: "classD_const (classD_const x) = classD_const x"

lemma "P (x\<Colon>'a\<Colon>classD)"
nitpick [expect = genuine]
oops

text {* A type class with multiple superclasses: *}

class classE = classC + classD

lemma "P (x\<Colon>'a\<Colon>classE)"
nitpick [expect = genuine]
oops

text {* OFCLASS: *}

lemma "OFCLASS('a\<Colon>type, type_class)"
nitpick [expect = none]
apply intro_classes
done

lemma "OFCLASS('a\<Colon>classC, type_class)"
nitpick [expect = none]
apply intro_classes
done

lemma "OFCLASS('a\<Colon>type, classC_class)"
nitpick [expect = genuine]
oops

text {* Overloading: *}

consts inverse :: "'a \<Rightarrow> 'a"

defs (overloaded)
inverse_bool: "inverse (b\<Colon>bool) \<equiv> \<not> b"
inverse_set: "inverse (S\<Colon>'a set) \<equiv> -S"
inverse_pair: "inverse p \<equiv> (inverse (fst p), inverse (snd p))"

lemma "inverse b"
nitpick [expect = genuine]
oops

lemma "P (inverse (S\<Colon>'a set))"
nitpick [expect = genuine]
oops

lemma "P (inverse (p\<Colon>'a\<times>'b))"
nitpick [expect = genuine]
oops

end
