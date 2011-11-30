(*  Title:      HOL/ex/Refute_Examples.thy
    Author:     Tjark Weber
    Copyright   2003-2007

See HOL/Refute.thy for help.
*)

header {* Examples for the 'refute' command *}

theory Refute_Examples imports Main
begin

refute_params [satsolver="dpll"]

lemma "P \<and> Q"
  apply (rule conjI)
  refute 1  -- {* refutes @{term "P"} *}
  refute 2  -- {* refutes @{term "Q"} *}
  refute    -- {* equivalent to 'refute 1' *}
    -- {* here 'refute 3' would cause an exception, since we only have 2 subgoals *}
  refute [maxsize=5]           -- {* we can override parameters ... *}
  refute [satsolver="dpll"] 2  -- {* ... and specify a subgoal at the same time *}
oops

(*****************************************************************************)

subsection {* Examples and Test Cases *}

subsubsection {* Propositional logic *}

lemma "True"
  refute
  apply auto
done

lemma "False"
  refute
oops

lemma "P"
  refute
oops

lemma "~ P"
  refute
oops

lemma "P & Q"
  refute
oops

lemma "P | Q"
  refute
oops

lemma "P \<longrightarrow> Q"
  refute
oops

lemma "(P::bool) = Q"
  refute
oops

lemma "(P | Q) \<longrightarrow> (P & Q)"
  refute
oops

(*****************************************************************************)

subsubsection {* Predicate logic *}

lemma "P x y z"
  refute
oops

lemma "P x y \<longrightarrow> P y x"
  refute
oops

lemma "P (f (f x)) \<longrightarrow> P x \<longrightarrow> P (f x)"
  refute
oops

(*****************************************************************************)

subsubsection {* Equality *}

lemma "P = True"
  refute
oops

lemma "P = False"
  refute
oops

lemma "x = y"
  refute
oops

lemma "f x = g x"
  refute
oops

lemma "(f::'a\<Rightarrow>'b) = g"
  refute
oops

lemma "(f::('d\<Rightarrow>'d)\<Rightarrow>('c\<Rightarrow>'d)) = g"
  refute
oops

lemma "distinct [a,b]"
  refute
  apply simp
  refute
oops

(*****************************************************************************)

subsubsection {* First-Order Logic *}

lemma "\<exists>x. P x"
  refute
oops

lemma "\<forall>x. P x"
  refute
oops

lemma "EX! x. P x"
  refute
oops

lemma "Ex P"
  refute
oops

lemma "All P"
  refute
oops

lemma "Ex1 P"
  refute
oops

lemma "(\<exists>x. P x) \<longrightarrow> (\<forall>x. P x)"
  refute
oops

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
  refute
oops

lemma "(\<exists>x. P x) \<longrightarrow> (EX! x. P x)"
  refute
oops

text {* A true statement (also testing names of free and bound variables being identical) *}

lemma "(\<forall>x y. P x y \<longrightarrow> P y x) \<longrightarrow> (\<forall>x. P x y) \<longrightarrow> P y x"
  refute [maxsize=4]
  apply fast
done

text {* "A type has at most 4 elements." *}

lemma "a=b | a=c | a=d | a=e | b=c | b=d | b=e | c=d | c=e | d=e"
  refute
oops

lemma "\<forall>a b c d e. a=b | a=c | a=d | a=e | b=c | b=d | b=e | c=d | c=e | d=e"
  refute
oops

text {* "Every reflexive and symmetric relation is transitive." *}

lemma "\<lbrakk> \<forall>x. P x x; \<forall>x y. P x y \<longrightarrow> P y x \<rbrakk> \<Longrightarrow> P x y \<longrightarrow> P y z \<longrightarrow> P x z"
  refute
oops

text {* The "Drinker's theorem" ... *}

lemma "\<exists>x. f x = g x \<longrightarrow> f = g"
  refute [maxsize=4]
  apply (auto simp add: ext)
done

text {* ... and an incorrect version of it *}

lemma "(\<exists>x. f x = g x) \<longrightarrow> f = g"
  refute
oops

text {* "Every function has a fixed point." *}

lemma "\<exists>x. f x = x"
  refute
oops

text {* "Function composition is commutative." *}

lemma "f (g x) = g (f x)"
  refute
oops

text {* "Two functions that are equivalent wrt.\ the same predicate 'P' are equal." *}

lemma "((P::('a\<Rightarrow>'b)\<Rightarrow>bool) f = P g) \<longrightarrow> (f x = g x)"
  refute
oops

(*****************************************************************************)

subsubsection {* Higher-Order Logic *}

lemma "\<exists>P. P"
  refute
  apply auto
done

lemma "\<forall>P. P"
  refute
oops

lemma "EX! P. P"
  refute
  apply auto
done

lemma "EX! P. P x"
  refute
oops

lemma "P Q | Q x"
  refute
oops

lemma "x \<noteq> All"
  refute
oops

lemma "x \<noteq> Ex"
  refute
oops

lemma "x \<noteq> Ex1"
  refute
oops

text {* "The transitive closure 'T' of an arbitrary relation 'P' is non-empty." *}

definition "trans" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "trans P == (ALL x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z)"

definition "subset" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "subset P Q == (ALL x y. P x y \<longrightarrow> Q x y)"

definition "trans_closure" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "trans_closure P Q == (subset Q P) & (trans P) & (ALL R. subset Q R \<longrightarrow> trans R \<longrightarrow> subset P R)"

lemma "trans_closure T P \<longrightarrow> (\<exists>x y. T x y)"
  refute
oops

text {* "The union of transitive closures is equal to the transitive closure of unions." *}

lemma "(\<forall>x y. (P x y | R x y) \<longrightarrow> T x y) \<longrightarrow> trans T \<longrightarrow> (\<forall>Q. (\<forall>x y. (P x y | R x y) \<longrightarrow> Q x y) \<longrightarrow> trans Q \<longrightarrow> subset T Q)
        \<longrightarrow> trans_closure TP P
        \<longrightarrow> trans_closure TR R
        \<longrightarrow> (T x y = (TP x y | TR x y))"
  refute
oops

text {* "Every surjective function is invertible." *}

lemma "(\<forall>y. \<exists>x. y = f x) \<longrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"
  refute
oops

text {* "Every invertible function is surjective." *}

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
  refute
oops

text {* Every point is a fixed point of some function. *}

lemma "\<exists>f. f x = x"
  refute [maxsize=4]
  apply (rule_tac x="\<lambda>x. x" in exI)
  apply simp
done

text {* Axiom of Choice: first an incorrect version ... *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (EX!f. \<forall>x. P x (f x))"
  refute
oops

text {* ... and now two correct ones *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>f. \<forall>x. P x (f x))"
  refute [maxsize=4]
  apply (simp add: choice)
done

lemma "(\<forall>x. EX!y. P x y) \<longrightarrow> (EX!f. \<forall>x. P x (f x))"
  refute [maxsize=2]
  apply auto
    apply (simp add: ex1_implies_ex choice)
  apply (fast intro: ext)
done

(*****************************************************************************)

subsubsection {* Meta-logic *}

lemma "!!x. P x"
  refute
oops

lemma "f x == g x"
  refute
oops

lemma "P \<Longrightarrow> Q"
  refute
oops

lemma "\<lbrakk> P; Q; R \<rbrakk> \<Longrightarrow> S"
  refute
oops

lemma "(x == all) \<Longrightarrow> False"
  refute
oops

lemma "(x == (op ==)) \<Longrightarrow> False"
  refute
oops

lemma "(x == (op \<Longrightarrow>)) \<Longrightarrow> False"
  refute
oops

(*****************************************************************************)

subsubsection {* Schematic variables *}

schematic_lemma "?P"
  refute
  apply auto
done

schematic_lemma "x = ?y"
  refute
  apply auto
done

(******************************************************************************)

subsubsection {* Abstractions *}

lemma "(\<lambda>x. x) = (\<lambda>x. y)"
  refute
oops

lemma "(\<lambda>f. f x) = (\<lambda>f. True)"
  refute
oops

lemma "(\<lambda>x. x) = (\<lambda>y. y)"
  refute
  apply simp
done

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
  apply simp
done

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
  refute
oops

lemma "P undefined"
  refute
oops

lemma "undefined x"
  refute
oops

lemma "undefined undefined"
  refute
oops

(*****************************************************************************)

subsubsection {* The *}

lemma "The P"
  refute
oops

lemma "P The"
  refute
oops

lemma "P (The P)"
  refute
oops

lemma "(THE x. x=y) = z"
  refute
oops

lemma "Ex P \<longrightarrow> P (The P)"
  refute
oops

(*****************************************************************************)

subsubsection {* Eps *}

lemma "Eps P"
  refute
oops

lemma "P Eps"
  refute
oops

lemma "P (Eps P)"
  refute
oops

lemma "(SOME x. x=y) = z"
  refute
oops

lemma "Ex P \<longrightarrow> P (Eps P)"
  refute [maxsize=3]
  apply (auto simp add: someI)
done

(*****************************************************************************)

subsubsection {* Subtypes (typedef), typedecl *}

text {* A completely unspecified non-empty subset of @{typ "'a"}: *}

definition "myTdef = insert (undefined::'a) (undefined::'a set)"

typedef (open) 'a myTdef = "myTdef :: 'a set"
  unfolding myTdef_def by auto

lemma "(x::'a myTdef) = y"
  refute
oops

typedecl myTdecl

definition "T_bij = {(f::'a\<Rightarrow>'a). \<forall>y. \<exists>!x. f x = y}"

typedef (open) 'a T_bij = "T_bij :: ('a \<Rightarrow> 'a) set"
  unfolding T_bij_def by auto

lemma "P (f::(myTdecl myTdef) T_bij)"
  refute
oops

(*****************************************************************************)

subsubsection {* Inductive datatypes *}

text {* With @{text quick_and_dirty} set, the datatype package does
  not generate certain axioms for recursion operators.  Without these
  axioms, refute may find spurious countermodels. *}

text {* unit *}

lemma "P (x::unit)"
  refute
oops

lemma "\<forall>x::unit. P x"
  refute
oops

lemma "P ()"
  refute
oops

lemma "unit_rec u x = u"
  refute
  apply simp
done

lemma "P (unit_rec u x)"
  refute
oops

lemma "P (case x of () \<Rightarrow> u)"
  refute
oops

text {* option *}

lemma "P (x::'a option)"
  refute
oops

lemma "\<forall>x::'a option. P x"
  refute
oops

lemma "P None"
  refute
oops

lemma "P (Some x)"
  refute
oops

lemma "option_rec n s None = n"
  refute
  apply simp
done

lemma "option_rec n s (Some x) = s x"
  refute [maxsize=4]
  apply simp
done

lemma "P (option_rec n s x)"
  refute
oops

lemma "P (case x of None \<Rightarrow> n | Some u \<Rightarrow> s u)"
  refute
oops

text {* * *}

lemma "P (x::'a*'b)"
  refute
oops

lemma "\<forall>x::'a*'b. P x"
  refute
oops

lemma "P (x, y)"
  refute
oops

lemma "P (fst x)"
  refute
oops

lemma "P (snd x)"
  refute
oops

lemma "P Pair"
  refute
oops

lemma "prod_rec p (a, b) = p a b"
  refute [maxsize=2]
  apply simp
oops

lemma "P (prod_rec p x)"
  refute
oops

lemma "P (case x of Pair a b \<Rightarrow> p a b)"
  refute
oops

text {* + *}

lemma "P (x::'a+'b)"
  refute
oops

lemma "\<forall>x::'a+'b. P x"
  refute
oops

lemma "P (Inl x)"
  refute
oops

lemma "P (Inr x)"
  refute
oops

lemma "P Inl"
  refute
oops

lemma "sum_rec l r (Inl x) = l x"
  refute [maxsize=3]
  apply simp
done

lemma "sum_rec l r (Inr x) = r x"
  refute [maxsize=3]
  apply simp
done

lemma "P (sum_rec l r x)"
  refute
oops

lemma "P (case x of Inl a \<Rightarrow> l a | Inr b \<Rightarrow> r b)"
  refute
oops

text {* Non-recursive datatypes *}

datatype T1 = A | B

lemma "P (x::T1)"
  refute
oops

lemma "\<forall>x::T1. P x"
  refute
oops

lemma "P A"
  refute
oops

lemma "P B"
  refute
oops

lemma "T1_rec a b A = a"
  refute
  apply simp
done

lemma "T1_rec a b B = b"
  refute
  apply simp
done

lemma "P (T1_rec a b x)"
  refute
oops

lemma "P (case x of A \<Rightarrow> a | B \<Rightarrow> b)"
  refute
oops

datatype 'a T2 = C T1 | D 'a

lemma "P (x::'a T2)"
  refute
oops

lemma "\<forall>x::'a T2. P x"
  refute
oops

lemma "P D"
  refute
oops

lemma "T2_rec c d (C x) = c x"
  refute [maxsize=4]
  apply simp
done

lemma "T2_rec c d (D x) = d x"
  refute [maxsize=4]
  apply simp
done

lemma "P (T2_rec c d x)"
  refute
oops

lemma "P (case x of C u \<Rightarrow> c u | D v \<Rightarrow> d v)"
  refute
oops

datatype ('a,'b) T3 = E "'a \<Rightarrow> 'b"

lemma "P (x::('a,'b) T3)"
  refute
oops

lemma "\<forall>x::('a,'b) T3. P x"
  refute
oops

lemma "P E"
  refute
oops

lemma "T3_rec e (E x) = e x"
  refute [maxsize=2]
  apply simp
done

lemma "P (T3_rec e x)"
  refute
oops

lemma "P (case x of E f \<Rightarrow> e f)"
  refute
oops

text {* Recursive datatypes *}

text {* nat *}

lemma "P (x::nat)"
  refute
oops

lemma "\<forall>x::nat. P x"
  refute
oops

lemma "P (Suc 0)"
  refute
oops

lemma "P Suc"
  refute  -- {* @{term Suc} is a partial function (regardless of the size
                of the model), hence @{term "P Suc"} is undefined, hence no
                model will be found *}
oops

lemma "nat_rec zero suc 0 = zero"
  refute
  apply simp
done

lemma "nat_rec zero suc (Suc x) = suc x (nat_rec zero suc x)"
  refute [maxsize=2]
  apply simp
done

lemma "P (nat_rec zero suc x)"
  refute
oops

lemma "P (case x of 0 \<Rightarrow> zero | Suc n \<Rightarrow> suc n)"
  refute
oops

text {* 'a list *}

lemma "P (xs::'a list)"
  refute
oops

lemma "\<forall>xs::'a list. P xs"
  refute
oops

lemma "P [x, y]"
  refute
oops

lemma "list_rec nil cons [] = nil"
  refute [maxsize=3]
  apply simp
done

lemma "list_rec nil cons (x#xs) = cons x xs (list_rec nil cons xs)"
  refute [maxsize=2]
  apply simp
done

lemma "P (list_rec nil cons xs)"
  refute
oops

lemma "P (case x of Nil \<Rightarrow> nil | Cons a b \<Rightarrow> cons a b)"
  refute
oops

lemma "(xs::'a list) = ys"
  refute
oops

lemma "a # xs = b # xs"
  refute
oops

datatype BitList = BitListNil | Bit0 BitList | Bit1 BitList

lemma "P (x::BitList)"
  refute
oops

lemma "\<forall>x::BitList. P x"
  refute
oops

lemma "P (Bit0 (Bit1 BitListNil))"
  refute
oops

lemma "BitList_rec nil bit0 bit1 BitListNil = nil"
  refute [maxsize=4]
  apply simp
done

lemma "BitList_rec nil bit0 bit1 (Bit0 xs) = bit0 xs (BitList_rec nil bit0 bit1 xs)"
  refute [maxsize=2]
  apply simp
done

lemma "BitList_rec nil bit0 bit1 (Bit1 xs) = bit1 xs (BitList_rec nil bit0 bit1 xs)"
  refute [maxsize=2]
  apply simp
done

lemma "P (BitList_rec nil bit0 bit1 x)"
  refute
oops

datatype 'a BinTree = Leaf 'a | Node "'a BinTree" "'a BinTree"

lemma "P (x::'a BinTree)"
  refute
oops

lemma "\<forall>x::'a BinTree. P x"
  refute
oops

lemma "P (Node (Leaf x) (Leaf y))"
  refute
oops

lemma "BinTree_rec l n (Leaf x) = l x"
  refute [maxsize=1]  (* The "maxsize=1" tests are a bit pointless: for some formulae
                         below, refute will find no countermodel simply because this
                         size makes involved terms undefined.  Unfortunately, any
                         larger size already takes too long. *)
  apply simp
done

lemma "BinTree_rec l n (Node x y) = n x y (BinTree_rec l n x) (BinTree_rec l n y)"
  refute [maxsize=1]
  apply simp
done

lemma "P (BinTree_rec l n x)"
  refute
oops

lemma "P (case x of Leaf a \<Rightarrow> l a | Node a b \<Rightarrow> n a b)"
  refute
oops

text {* Mutually recursive datatypes *}

datatype 'a aexp = Number 'a | ITE "'a bexp" "'a aexp" "'a aexp"
     and 'a bexp = Equal "'a aexp" "'a aexp"

lemma "P (x::'a aexp)"
  refute
oops

lemma "\<forall>x::'a aexp. P x"
  refute
oops

lemma "P (ITE (Equal (Number x) (Number y)) (Number x) (Number y))"
  refute
oops

lemma "P (x::'a bexp)"
  refute
oops

lemma "\<forall>x::'a bexp. P x"
  refute
oops

lemma "aexp_bexp_rec_1 number ite equal (Number x) = number x"
  refute [maxsize=1]
  apply simp
done

lemma "aexp_bexp_rec_1 number ite equal (ITE x y z) = ite x y z (aexp_bexp_rec_2 number ite equal x) (aexp_bexp_rec_1 number ite equal y) (aexp_bexp_rec_1 number ite equal z)"
  refute [maxsize=1]
  apply simp
done

lemma "P (aexp_bexp_rec_1 number ite equal x)"
  refute
oops

lemma "P (case x of Number a \<Rightarrow> number a | ITE b a1 a2 \<Rightarrow> ite b a1 a2)"
  refute
oops

lemma "aexp_bexp_rec_2 number ite equal (Equal x y) = equal x y (aexp_bexp_rec_1 number ite equal x) (aexp_bexp_rec_1 number ite equal y)"
  refute [maxsize=1]
  apply simp
done

lemma "P (aexp_bexp_rec_2 number ite equal x)"
  refute
oops

lemma "P (case x of Equal a1 a2 \<Rightarrow> equal a1 a2)"
  refute
oops

datatype X = A | B X | C Y
     and Y = D X | E Y | F

lemma "P (x::X)"
  refute
oops

lemma "P (y::Y)"
  refute
oops

lemma "P (B (B A))"
  refute
oops

lemma "P (B (C F))"
  refute
oops

lemma "P (C (D A))"
  refute
oops

lemma "P (C (E F))"
  refute
oops

lemma "P (D (B A))"
  refute
oops

lemma "P (D (C F))"
  refute
oops

lemma "P (E (D A))"
  refute
oops

lemma "P (E (E F))"
  refute
oops

lemma "P (C (D (C F)))"
  refute
oops

lemma "X_Y_rec_1 a b c d e f A = a"
  refute [maxsize=3]
  apply simp
done

lemma "X_Y_rec_1 a b c d e f (B x) = b x (X_Y_rec_1 a b c d e f x)"
  refute [maxsize=1]
  apply simp
done

lemma "X_Y_rec_1 a b c d e f (C y) = c y (X_Y_rec_2 a b c d e f y)"
  refute [maxsize=1]
  apply simp
done

lemma "X_Y_rec_2 a b c d e f (D x) = d x (X_Y_rec_1 a b c d e f x)"
  refute [maxsize=1]
  apply simp
done

lemma "X_Y_rec_2 a b c d e f (E y) = e y (X_Y_rec_2 a b c d e f y)"
  refute [maxsize=1]
  apply simp
done

lemma "X_Y_rec_2 a b c d e f F = f"
  refute [maxsize=3]
  apply simp
done

lemma "P (X_Y_rec_1 a b c d e f x)"
  refute
oops

lemma "P (X_Y_rec_2 a b c d e f y)"
  refute
oops

text {* Other datatype examples *}

text {* Indirect recursion is implemented via mutual recursion. *}

datatype XOpt = CX "XOpt option" | DX "bool \<Rightarrow> XOpt option"

lemma "P (x::XOpt)"
  refute
oops

lemma "P (CX None)"
  refute
oops

lemma "P (CX (Some (CX None)))"
  refute
oops

lemma "XOpt_rec_1 cx dx n1 s1 n2 s2 (CX x) = cx x (XOpt_rec_2 cx dx n1 s1 n2 s2 x)"
  refute [maxsize=1]
  apply simp
done

lemma "XOpt_rec_1 cx dx n1 s1 n2 s2 (DX x) = dx x (\<lambda>b. XOpt_rec_3 cx dx n1 s1 n2 s2 (x b))"
  refute [maxsize=1]
  apply simp
done

lemma "XOpt_rec_2 cx dx n1 s1 n2 s2 None = n1"
  refute [maxsize=2]
  apply simp
done

lemma "XOpt_rec_2 cx dx n1 s1 n2 s2 (Some x) = s1 x (XOpt_rec_1 cx dx n1 s1 n2 s2 x)"
  refute [maxsize=1]
  apply simp
done

lemma "XOpt_rec_3 cx dx n1 s1 n2 s2 None = n2"
  refute [maxsize=2]
  apply simp
done

lemma "XOpt_rec_3 cx dx n1 s1 n2 s2 (Some x) = s2 x (XOpt_rec_1 cx dx n1 s1 n2 s2 x)"
  refute [maxsize=1]
  apply simp
done

lemma "P (XOpt_rec_1 cx dx n1 s1 n2 s2 x)"
  refute
oops

lemma "P (XOpt_rec_2 cx dx n1 s1 n2 s2 x)"
  refute
oops

lemma "P (XOpt_rec_3 cx dx n1 s1 n2 s2 x)"
  refute
oops

datatype 'a YOpt = CY "('a \<Rightarrow> 'a YOpt) option"

lemma "P (x::'a YOpt)"
  refute
oops

lemma "P (CY None)"
  refute
oops

lemma "P (CY (Some (\<lambda>a. CY None)))"
  refute
oops

lemma "YOpt_rec_1 cy n s (CY x) = cy x (YOpt_rec_2 cy n s x)"
  refute [maxsize=1]
  apply simp
done

lemma "YOpt_rec_2 cy n s None = n"
  refute [maxsize=2]
  apply simp
done

lemma "YOpt_rec_2 cy n s (Some x) = s x (\<lambda>a. YOpt_rec_1 cy n s (x a))"
  refute [maxsize=1]
  apply simp
done

lemma "P (YOpt_rec_1 cy n s x)"
  refute
oops

lemma "P (YOpt_rec_2 cy n s x)"
  refute
oops

datatype Trie = TR "Trie list"

lemma "P (x::Trie)"
  refute
oops

lemma "\<forall>x::Trie. P x"
  refute
oops

lemma "P (TR [TR []])"
  refute
oops

lemma "Trie_rec_1 tr nil cons (TR x) = tr x (Trie_rec_2 tr nil cons x)"
  refute [maxsize=1]
  apply simp
done

lemma "Trie_rec_2 tr nil cons [] = nil"
  refute [maxsize=3]
  apply simp
done

lemma "Trie_rec_2 tr nil cons (x#xs) = cons x xs (Trie_rec_1 tr nil cons x) (Trie_rec_2 tr nil cons xs)"
  refute [maxsize=1]
  apply simp
done

lemma "P (Trie_rec_1 tr nil cons x)"
  refute
oops

lemma "P (Trie_rec_2 tr nil cons x)"
  refute
oops

datatype InfTree = Leaf | Node "nat \<Rightarrow> InfTree"

lemma "P (x::InfTree)"
  refute
oops

lemma "\<forall>x::InfTree. P x"
  refute
oops

lemma "P (Node (\<lambda>n. Leaf))"
  refute
oops

lemma "InfTree_rec leaf node Leaf = leaf"
  refute [maxsize=2]
  apply simp
done

lemma "InfTree_rec leaf node (Node x) = node x (\<lambda>n. InfTree_rec leaf node (x n))"
  refute [maxsize=1]
  apply simp
done

lemma "P (InfTree_rec leaf node x)"
  refute
oops

datatype 'a lambda = Var 'a | App "'a lambda" "'a lambda" | Lam "'a \<Rightarrow> 'a lambda"

lemma "P (x::'a lambda)"
  refute
oops

lemma "\<forall>x::'a lambda. P x"
  refute
oops

lemma "P (Lam (\<lambda>a. Var a))"
  refute
oops

lemma "lambda_rec var app lam (Var x) = var x"
  refute [maxsize=1]
  apply simp
done

lemma "lambda_rec var app lam (App x y) = app x y (lambda_rec var app lam x) (lambda_rec var app lam y)"
  refute [maxsize=1]
  apply simp
done

lemma "lambda_rec var app lam (Lam x) = lam x (\<lambda>a. lambda_rec var app lam (x a))"
  refute [maxsize=1]
  apply simp
done

lemma "P (lambda_rec v a l x)"
  refute
oops

text {* Taken from "Inductive datatypes in HOL", p.8: *}

datatype ('a, 'b) T = C "'a \<Rightarrow> bool" | D "'b list"
datatype 'c U = E "('c, 'c U) T"

lemma "P (x::'c U)"
  refute
oops

lemma "\<forall>x::'c U. P x"
  refute
oops

lemma "P (E (C (\<lambda>a. True)))"
  refute
oops

lemma "U_rec_1 e c d nil cons (E x) = e x (U_rec_2 e c d nil cons x)"
  refute [maxsize=1]
  apply simp
done

lemma "U_rec_2 e c d nil cons (C x) = c x"
  refute [maxsize=1]
  apply simp
done

lemma "U_rec_2 e c d nil cons (D x) = d x (U_rec_3 e c d nil cons x)"
  refute [maxsize=1]
  apply simp
done

lemma "U_rec_3 e c d nil cons [] = nil"
  refute [maxsize=2]
  apply simp
done

lemma "U_rec_3 e c d nil cons (x#xs) = cons x xs (U_rec_1 e c d nil cons x) (U_rec_3 e c d nil cons xs)"
  refute [maxsize=1]
  apply simp
done

lemma "P (U_rec_1 e c d nil cons x)"
  refute
oops

lemma "P (U_rec_2 e c d nil cons x)"
  refute
oops

lemma "P (U_rec_3 e c d nil cons x)"
  refute
oops

(*****************************************************************************)

subsubsection {* Records *}

(*TODO: make use of pair types, rather than typedef, for record types*)

record ('a, 'b) point =
  xpos :: 'a
  ypos :: 'b

lemma "(x::('a, 'b) point) = y"
  refute
oops

record ('a, 'b, 'c) extpoint = "('a, 'b) point" +
  ext :: 'c

lemma "(x::('a, 'b, 'c) extpoint) = y"
  refute
oops

(*****************************************************************************)

subsubsection {* Inductively defined sets *}

inductive_set arbitrarySet :: "'a set"
where
  "undefined : arbitrarySet"

lemma "x : arbitrarySet"
  refute
oops

inductive_set evenCard :: "'a set set"
where
  "{} : evenCard"
| "\<lbrakk> S : evenCard; x \<notin> S; y \<notin> S; x \<noteq> y \<rbrakk> \<Longrightarrow> S \<union> {x, y} : evenCard"

lemma "S : evenCard"
  refute
oops

inductive_set
  even :: "nat set"
  and odd  :: "nat set"
where
  "0 : even"
| "n : even \<Longrightarrow> Suc n : odd"
| "n : odd \<Longrightarrow> Suc n : even"

lemma "n : odd"
  (*refute*)  (* TODO: there seems to be an issue here with undefined terms
                       because of the recursive datatype "nat" *)
oops

consts f :: "'a \<Rightarrow> 'a"

inductive_set
  a_even :: "'a set"
  and a_odd :: "'a set"
where
  "undefined : a_even"
| "x : a_even \<Longrightarrow> f x : a_odd"
| "x : a_odd \<Longrightarrow> f x : a_even"

lemma "x : a_odd"
  (* refute  -- {* finds a model of size 2, as expected *}
     NO LONGER WORKS since "lfp"'s interpreter is disabled *)
oops

(*****************************************************************************)

subsubsection {* Examples involving special functions *}

lemma "card x = 0"
  refute
oops

lemma "finite x"
  refute  -- {* no finite countermodel exists *}
oops

lemma "(x::nat) + y = 0"
  refute
oops

lemma "(x::nat) = x + x"
  refute
oops

lemma "(x::nat) - y + y = x"
  refute
oops

lemma "(x::nat) = x * x"
  refute
oops

lemma "(x::nat) < x + y"
  refute
oops

lemma "xs @ [] = ys @ []"
  refute
oops

lemma "xs @ ys = ys @ xs"
  refute
oops

lemma "f (lfp f) = lfp f"
  refute
oops

lemma "f (gfp f) = gfp f"
  refute
oops

lemma "lfp f = gfp f"
  refute
oops

(*****************************************************************************)

subsubsection {* Type classes and overloading *}

text {* A type class without axioms: *}

class classA

lemma "P (x::'a::classA)"
  refute
oops

text {* An axiom with a type variable (denoting types which have at least two elements): *}

class classC =
  assumes classC_ax: "\<exists>x y. x \<noteq> y"

lemma "P (x::'a::classC)"
  refute
oops

lemma "\<exists>x y. (x::'a::classC) \<noteq> y"
  refute  -- {* no countermodel exists *}
oops

text {* A type class for which a constant is defined: *}

class classD =
  fixes classD_const :: "'a \<Rightarrow> 'a"
  assumes classD_ax: "classD_const (classD_const x) = classD_const x"

lemma "P (x::'a::classD)"
  refute
oops

text {* A type class with multiple superclasses: *}

class classE = classC + classD

lemma "P (x::'a::classE)"
  refute
oops

text {* OFCLASS: *}

lemma "OFCLASS('a::type, type_class)"
  refute  -- {* no countermodel exists *}
  apply intro_classes
done

lemma "OFCLASS('a::classC, type_class)"
  refute  -- {* no countermodel exists *}
  apply intro_classes
done

lemma "OFCLASS('a::type, classC_class)"
  refute
oops

text {* Overloading: *}

consts inverse :: "'a \<Rightarrow> 'a"

defs (overloaded)
  inverse_bool: "inverse (b::bool)   == ~ b"
  inverse_set : "inverse (S::'a set) == -S"
  inverse_pair: "inverse p           == (inverse (fst p), inverse (snd p))"

lemma "inverse b"
  refute
oops

lemma "P (inverse (S::'a set))"
  refute
oops

lemma "P (inverse (p::'a\<times>'b))"
  refute
oops

text {* Structured proofs *}

lemma "x = y"
proof cases
  assume "x = y"
  show ?thesis
  refute
  refute [no_assms]
  refute [no_assms = false]
oops

refute_params [satsolver="auto"]

end
