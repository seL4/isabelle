(*  Title:      HOL/ex/Refute_Examples.thy
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2003-2005
*)

(* See 'HOL/Refute.thy' for help. *)

header {* Examples for the 'refute' command *}

theory Refute_Examples imports Main

begin

lemma "P \<and> Q"
  apply (rule conjI)
  refute 1  -- {* refutes @{term "P"} *}
  refute 2  -- {* refutes @{term "Q"} *}
  refute    -- {* equivalent to 'refute 1' *}
    -- {* here 'refute 3' would cause an exception, since we only have 2 subgoals *}
  refute [maxsize=5]           -- {* we can override parameters ... *}
  refute [satsolver="dpll"] 2  -- {* ... and specify a subgoal at the same time *}
oops

section {* Examples and Test Cases *}

subsection {* Propositional logic *}

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

subsection {* Predicate logic *}

lemma "P x y z"
  refute
oops

lemma "P x y \<longrightarrow> P y x"
  refute
oops

lemma "P (f (f x)) \<longrightarrow> P x \<longrightarrow> P (f x)"
  refute
oops

subsection {* Equality *}

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

subsection {* First-Order Logic *}

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
  refute [maxsize=6]
  apply fast
done

text {* "A type has at most 5 elements." *}

lemma "a=b | a=c | a=d | a=e | a=f | b=c | b=d | b=e | b=f | c=d | c=e | c=f | d=e | d=f | e=f"
  refute
oops

lemma "\<forall>a b c d e f. a=b | a=c | a=d | a=e | a=f | b=c | b=d | b=e | b=f | c=d | c=e | c=f | d=e | d=f | e=f"
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

subsection {* Higher-Order Logic *}

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

lemma "P All"
  refute
oops

lemma "P Ex"
  refute
oops

lemma "P Ex1"
  refute
oops

text {* "The transitive closure 'T' of an arbitrary relation 'P' is non-empty." *}

constdefs
  "trans" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  "trans P == (ALL x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z)"
  "subset" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  "subset P Q == (ALL x y. P x y \<longrightarrow> Q x y)"
  "trans_closure" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  "trans_closure P Q == (subset Q P) & (trans P) & (ALL R. subset Q R \<longrightarrow> trans R \<longrightarrow> subset P R)"

lemma "trans_closure T P \<longrightarrow> (\<exists>x y. T x y)"
  refute
oops

text {* "The union of transitive closures is equal to the transitive closure of unions." *}

lemma "(\<forall>x y. (P x y | R x y) \<longrightarrow> T x y) \<longrightarrow> trans T \<longrightarrow> (\<forall>Q. (\<forall>x y. (P x y | R x y) \<longrightarrow> Q x y) \<longrightarrow> trans Q \<longrightarrow> subset T Q)
        \<longrightarrow> trans_closure TP P
        \<longrightarrow> trans_closure TR R
        \<longrightarrow> (T x y = (TP x y | TR x y))"
  refute [satsolver="dpll"]
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

subsection {* Meta-logic *}

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

subsection {* Schematic variables *}

lemma "?P"
  refute
  apply auto
done

lemma "x = ?y"
  refute
  apply auto
done

subsection {* Abstractions *}

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

subsection {* Sets *}

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

subsection {* arbitrary *}

lemma "arbitrary"
  refute
oops

lemma "P arbitrary"
  refute
oops

lemma "arbitrary x"
  refute
oops

lemma "arbitrary arbitrary"
  refute
oops

subsection {* The *}

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

subsection {* Eps *}

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

subsection {* Subtypes (typedef), typedecl *}

text {* A completely unspecified non-empty subset of @{typ "'a"}: *}

typedef 'a myTdef = "insert (arbitrary::'a) (arbitrary::'a set)"
  by auto

lemma "(x::'a myTdef) = y"
  refute
oops

typedecl myTdecl

typedef 'a T_bij = "{(f::'a\<Rightarrow>'a). \<forall>y. \<exists>!x. f x = y}"
  by auto

lemma "P (f::(myTdecl myTdef) T_bij)"
  refute
oops

subsection {* Inductive datatypes *}

text {* This is necessary because with quick\_and\_dirty set, the datatype
package does not generate certain axioms for recursion operators.  Without
these axioms, refute may find spurious countermodels. *}

ML {* reset quick_and_dirty; *}

(*TODO*) ML {* set show_consts; set show_types; *}

subsubsection {* unit *}

lemma "P (x::unit)"
  refute
oops

lemma "\<forall>x::unit. P x"
  refute
oops

lemma "P ()"
  refute
oops

lemma "P (unit_rec u x)"
  refute
oops

lemma "P (case x of () \<Rightarrow> u)"
  refute
oops

subsubsection {* option *}

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

lemma "P (option_rec n s x)"
  refute
oops

lemma "P (case x of None \<Rightarrow> n | Some u \<Rightarrow> s u)"
  refute
oops

subsubsection {* * *}

lemma "P (x::'a*'b)"
  refute
oops

lemma "\<forall>x::'a*'b. P x"
  refute
oops

lemma "P (x,y)"
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

lemma "P (prod_rec p x)"
  refute
oops

lemma "P (case x of Pair a b \<Rightarrow> p a b)"
  refute
oops

subsubsection {* + *}

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

lemma "P (sum_rec l r x)"
  refute
oops

lemma "P (case x of Inl a \<Rightarrow> l a | Inr b \<Rightarrow> r b)"
  refute
oops

subsubsection {* Non-recursive datatypes *}

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

lemma "P (T3_rec e x)"
  refute
oops

lemma "P (case x of E f \<Rightarrow> e f)"
  refute
oops

subsubsection {* Recursive datatypes *}

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
  refute  -- {* @{term "Suc"} is a partial function (regardless of the size
                of the model), hence @{term "P Suc"} is undefined, hence no
                model will be found *}
oops

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

lemma "P (BinTree_rec l n x)"
  refute
oops

lemma "P (case x of Leaf a \<Rightarrow> l a | Node a b \<Rightarrow> n a b)"
  refute
oops

subsubsection {* Mutually recursive datatypes *}

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

lemma "P (aexp_bexp_rec_1 number ite equal x)"
  refute
oops

lemma "P (case x of Number a \<Rightarrow> number a | ITE b a1 a2 \<Rightarrow> ite b a1 a2)"
  refute
oops

lemma "P (aexp_bexp_rec_2 number ite equal x)"
  (*TODO refute*)
oops

lemma "P (case x of Equal a1 a2 \<Rightarrow> equal a1 a2)"
  (*TODO: refute*)
oops

subsubsection {* Other datatype examples *}

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

lemma "P (Trie_rec tr x)"
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

lemma "P (lambda_rec v a l x)"
  refute
oops

subsubsection {* Examples involving certain functions *}

lemma "card x = 0"
  refute
oops

lemma "P nat_rec"
  refute
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

lemma "a @ [] = b @ []"
  refute
oops

lemma "P (xs::'a list)"
  refute ["List.list"=4, "'a"=2]
oops

lemma "a @ b = b @ a"
  (*TODO refute*)  -- {* unfortunately, this little example already takes too long *}
oops

subsection {* Axiomatic type classes and overloading *}

ML {* set show_consts; set show_types; set show_sorts; *}

text {* A type class without axioms: *}

axclass classA

lemma "P (x::'a::classA)"
  refute
oops

text {* The axiom of this type class does not contain any type variables, but is internally converted into one that does: *}

axclass classB
  classB_ax: "P | ~ P"

lemma "P (x::'a::classB)"
  refute
oops

text {* An axiom with a type variable (denoting types which have at least two elements): *}

axclass classC < type
  classC_ax: "\<exists>x y. x \<noteq> y"

lemma "P (x::'a::classC)"
  refute
oops

lemma "\<exists>x y. (x::'a::classC) \<noteq> y"
  refute  -- {* no countermodel exists *}
oops

text {* A type class for which a constant is defined: *}

consts
  classD_const :: "'a \<Rightarrow> 'a"

axclass classD < type
  classD_ax: "classD_const (classD_const x) = classD_const x"

lemma "P (x::'a::classD)"
  refute
oops

text {* A type class with multiple superclasses: *}

axclass classE < classC, classD

lemma "P (x::'a::classE)"
  refute
oops

lemma "P (x::'a::{classB, classE})"
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

lemma "OFCLASS('a, classB_class)"
  refute  -- {* no countermodel exists *}
  apply intro_classes
  apply simp
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

end
