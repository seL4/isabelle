(*  Title:      HOL/ex/Refute_Examples.thy
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2003-2004
*)

(* See 'HOL/Refute.thy' for help. *)

header {* Examples for the 'refute' command *}

theory Refute_Examples = Main:

section {* 'refute': General usage *}

lemma "P"
  refute
oops

lemma "P \<and> Q"
  apply (rule conjI)
  refute 1  -- {* refutes @{term "P"} *}
  refute 2  -- {* refutes @{term "Q"} *}
  refute    -- {* equivalent to 'refute 1' *}
  -- {* here 'refute 3' would cause an exception, since we only have 2 subgoals *}
  refute [maxsize=5]     -- {* we can override parameters \<dots> *}
  refute [satformat="cnf"] 2  -- {* \<dots> and specify a subgoal at the same time *}
oops

section {* Examples / Test cases *}

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

lemma "P x"
  refute
oops

lemma "P a b c d"
  refute
oops

lemma "P x y \<longrightarrow> P y x"
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

text {* "A type has at most 3 elements." *}

lemma "\<forall>a b c d. a=b | a=c | a=d | b=c | b=d | c=d"
  refute
oops

text {* "Every reflexive and symmetric relation is transitive." *}

lemma "\<lbrakk> \<forall>x. P x x; \<forall>x y. P x y \<longrightarrow> P y x \<rbrakk> \<Longrightarrow> P x y \<longrightarrow> P y z \<longrightarrow> P x z"
  refute
oops

text {* The "Drinker's theorem" \<dots> *}

lemma "\<exists>x. f x = g x \<longrightarrow> f = g"
  refute
  apply (auto simp add: ext)
done

text {* \<dots> and an incorrect version of it *}

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

text {* "The transitive closure 'T' of an arbitrary relation 'P' is non-empty." *}

constdefs
  "trans" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  "trans P == (ALL x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z)"
  "subset" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  "subset P Q == (ALL x y. P x y \<longrightarrow> Q x y)"
  "trans_closure" :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  "trans_closure P Q == (subset Q P) & (trans P) & (ALL R. subset Q R \<longrightarrow> trans R \<longrightarrow> subset P R)"

lemma "trans_closure T P \<longrightarrow> (\<exists>x y. T x y)"
  apply (unfold trans_closure_def subset_def trans_def)
  refute
oops

text {* "The union of transitive closures is equal to the transitive closure of unions." *}

lemma "(\<forall>x y. (P x y | R x y) \<longrightarrow> T x y) \<longrightarrow> trans T \<longrightarrow> (\<forall>Q. (\<forall>x y. (P x y | R x y) \<longrightarrow> Q x y) \<longrightarrow> trans Q \<longrightarrow> subset T Q)
        \<longrightarrow> trans_closure TP P
        \<longrightarrow> trans_closure TR R
        \<longrightarrow> (T x y = (TP x y | TR x y))"
  apply (unfold trans_closure_def trans_def subset_def)
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
  refute [maxsize=5]
  apply (rule_tac x="\<lambda>x. x" in exI)
  apply simp
done

text {* Axiom of Choice: first an incorrect version \<dots> *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (EX!f. \<forall>x. P x (f x))"
  refute
oops

text {* \<dots> and now two correct ones *}

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>f. \<forall>x. P x (f x))"
  refute
  apply (simp add: choice)
done

lemma "(\<forall>x. EX!y. P x y) \<longrightarrow> (EX!f. \<forall>x. P x (f x))"
  refute [maxsize=5]
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

lemma "A Un B = A Int B"
  apply (unfold Un_def Int_def)
  refute
oops

lemma "(A Int B) Un C = (A Un C) Int B"
  apply (unfold Un_def Int_def)
  refute
oops

lemma "Ball A P \<longrightarrow> Bex A P"
  apply (unfold Ball_def Bex_def)
  refute
oops

subsection {* (Inductive) Datatypes *}

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

subsubsection {* * *}

lemma "P (x::'a*'b)"
oops

lemma "\<forall>x::'a*'b. P x"
oops

lemma "P (x,y)"
oops

lemma "P (fst x)"
oops

lemma "P (snd x)"
oops

subsubsection {* + *}

lemma "P (x::'a+'b)"
oops

lemma "\<forall>x::'a+'b. P x"
oops

lemma "P (Inl x)"
oops

lemma "P (Inr x)"
oops

subsubsection {* Non-recursive datatypes *}

datatype T1 = C1

lemma "P (x::T1)"
  refute
oops

lemma "\<forall>x::T1. P x"
  refute
oops

lemma "P C"
oops

datatype T2 = C2 T1

lemma "P (x::T2)"
  refute
oops

lemma "\<forall>x::T2. P x"
  refute
oops

lemma "P (C2 C1)"
oops

lemma "P (C2 x)"
oops

datatype 'a T3 = C3 'a

lemma "P (x::'a T3)"
  refute
oops

lemma "\<forall>x::'a T3. P x"
  refute
oops

lemma "P (C3 x)"
oops

subsubsection {* Recursive datatypes *}

datatype Nat = Zero | Suc Nat

lemma "P (x::Nat)"
  refute
oops

lemma "\<forall>x::Nat. P x"
  refute
oops

lemma "P (Suc Zero)"
oops

datatype 'a BinTree = Leaf 'a | Node "'a BinTree" "'a BinTree"

lemma "P (x::'a BinTree)"
  refute
oops

lemma "\<forall>x::'a BinTree. P x"
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

lemma "P (x::'a bexp)"
  refute
oops

lemma "\<forall>x::'a bexp. P x"
  refute
oops

lemma "P (ITE (Equal (Number x) (Number y)) (Number x) (Number y))"
oops

subsubsection {* Other datatype examples *}

datatype InfTree = Leaf | Node "Nat \<Rightarrow> InfTree"

lemma "P (x::InfTree)"
oops

datatype 'a lambda = Var 'a | App "'a lambda" "'a lambda" | Lam "'a \<Rightarrow> 'a lambda"

lemma "P (x::'a lambda)"
oops

end
