(*  Title:      HOL/ex/Intuitionistic.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Taken from FOL/ex/int.ML
*)

section \<open>Higher-Order Logic: Intuitionistic predicate calculus problems\<close>

theory Intuitionistic imports Main begin


(*Metatheorem (for PROPOSITIONAL formulae...):
  P is classically provable iff ~~P is intuitionistically provable.
  Therefore ~P is classically provable iff it is intuitionistically provable.  

Proof: Let Q be the conjuction of the propositions A|~A, one for each atom A
in P.  Now ~~Q is intuitionistically provable because ~~(A|~A) is and because
~~ distributes over &.  If P is provable classically, then clearly Q-->P is
provable intuitionistically, so ~~(Q-->P) is also provable intuitionistically.
The latter is intuitionistically equivalent to ~~Q-->~~P, hence to ~~P, since
~~Q is intuitionistically provable.  Finally, if P is a negation then ~~P is
intuitionstically equivalent to P.  [Andy Pitts] *)

lemma "(~~(P&Q)) = ((~~P) & (~~Q))"
  by iprover

lemma "~~ ((~P --> Q) --> (~P --> ~Q) --> P)"
  by iprover

(* ~~ does NOT distribute over | *)

lemma "(~~(P-->Q))  = (~~P --> ~~Q)"
  by iprover

lemma "(~~~P) = (~P)"
  by iprover

lemma "~~((P --> Q | R)  -->  (P-->Q) | (P-->R))"
  by iprover

lemma "(P=Q) = (Q=P)"
  by iprover

lemma "((P --> (Q | (Q-->R))) --> R) --> R"
  by iprover

lemma "(((G-->A) --> J) --> D --> E) --> (((H-->B)-->I)-->C-->J)
      --> (A-->H) --> F --> G --> (((C-->B)-->I)-->D)-->(A-->C)
      --> (((F-->A)-->B) --> I) --> E"
  by iprover


(* Lemmas for the propositional double-negation translation *)

lemma "P --> ~~P"
  by iprover

lemma "~~(~~P --> P)"
  by iprover

lemma "~~P & ~~(P --> Q) --> ~~Q"
  by iprover


(* de Bruijn formulae *)

(*de Bruijn formula with three predicates*)
lemma "((P=Q) --> P&Q&R) &
       ((Q=R) --> P&Q&R) &
       ((R=P) --> P&Q&R) --> P&Q&R"
  by iprover

(*de Bruijn formula with five predicates*)
lemma "((P=Q) --> P&Q&R&S&T) &
       ((Q=R) --> P&Q&R&S&T) &
       ((R=S) --> P&Q&R&S&T) &
       ((S=T) --> P&Q&R&S&T) &
       ((T=P) --> P&Q&R&S&T) --> P&Q&R&S&T"
  by iprover


(*** Problems from Sahlin, Franzen and Haridi, 
     An Intuitionistic Predicate Logic Theorem Prover.
     J. Logic and Comp. 2 (5), October 1992, 619-656.
***)

(*Problem 1.1*)
lemma "(\<forall>x. \<exists>y. \<forall>z. p(x) \<and> q(y) \<and> r(z)) =
       (\<forall>z. \<exists>y. \<forall>x. p(x) \<and> q(y) \<and> r(z))"
  by (iprover del: allE elim 2: allE')

(*Problem 3.1*)
lemma "\<not> (\<exists>x. \<forall>y. p y x = (\<not> p x x))"
  by iprover


(* Intuitionistic FOL: propositional problems based on Pelletier. *)

(* Problem ~~1 *)
lemma "~~((P-->Q)  =  (~Q --> ~P))"
  by iprover

(* Problem ~~2 *)
lemma "~~(~~P  =  P)"
  by iprover

(* Problem 3 *)
lemma "~(P-->Q) --> (Q-->P)"
  by iprover

(* Problem ~~4 *)
lemma "~~((~P-->Q)  =  (~Q --> P))"
  by iprover

(* Problem ~~5 *)
lemma "~~((P|Q-->P|R) --> P|(Q-->R))"
  by iprover

(* Problem ~~6 *)
lemma "~~(P | ~P)"
  by iprover

(* Problem ~~7 *)
lemma "~~(P | ~~~P)"
  by iprover

(* Problem ~~8.  Peirce's law *)
lemma "~~(((P-->Q) --> P)  -->  P)"
  by iprover

(* Problem 9 *)
lemma "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
  by iprover

(* Problem 10 *)
lemma "(Q-->R) --> (R-->P&Q) --> (P-->(Q|R)) --> (P=Q)"
  by iprover

(* 11.  Proved in each direction (incorrectly, says Pelletier!!) *)
lemma "P=P"
  by iprover

(* Problem ~~12.  Dijkstra's law *)
lemma "~~(((P = Q) = R)  =  (P = (Q = R)))"
  by iprover

lemma "((P = Q) = R)  -->  ~~(P = (Q = R))"
  by iprover

(* Problem 13.  Distributive law *)
lemma "(P | (Q & R))  = ((P | Q) & (P | R))"
  by iprover

(* Problem ~~14 *)
lemma "~~((P = Q) = ((Q | ~P) & (~Q|P)))"
  by iprover

(* Problem ~~15 *)
lemma "~~((P --> Q) = (~P | Q))"
  by iprover

(* Problem ~~16 *)
lemma "~~((P-->Q) | (Q-->P))"
by iprover

(* Problem ~~17 *)
lemma "~~(((P & (Q-->R))-->S) = ((~P | Q | S) & (~P | ~R | S)))"
  oops

(*Dijkstra's "Golden Rule"*)
lemma "(P&Q) = (P = (Q = (P|Q)))"
  by iprover


(****Examples with quantifiers****)

(* The converse is classical in the following implications... *)

lemma "(\<exists>x. P(x)\<longrightarrow>Q)  \<longrightarrow>  (\<forall>x. P(x)) \<longrightarrow> Q"
  by iprover

lemma "((\<forall>x. P(x))\<longrightarrow>Q) \<longrightarrow> \<not> (\<forall>x. P(x) \<and> \<not>Q)"
  by iprover

lemma "((\<forall>x. \<not>P(x))\<longrightarrow>Q)  \<longrightarrow>  \<not> (\<forall>x. \<not> (P(x)\<or>Q))"
  by iprover

lemma "(\<forall>x. P(x)) \<or> Q  \<longrightarrow>  (\<forall>x. P(x) \<or> Q)"
  by iprover 

lemma "(\<exists>x. P \<longrightarrow> Q(x)) \<longrightarrow> (P \<longrightarrow> (\<exists>x. Q(x)))"
  by iprover


(* Hard examples with quantifiers *)

(*The ones that have not been proved are not known to be valid!
  Some will require quantifier duplication -- not currently available*)

(* Problem ~~19 *)
lemma "\<not>\<not>(\<exists>x. \<forall>y z. (P(y)\<longrightarrow>Q(z)) \<longrightarrow> (P(x)\<longrightarrow>Q(x)))"
  by iprover

(* Problem 20 *)
lemma "(\<forall>x y. \<exists>z. \<forall>w. (P(x)\<and>Q(y)\<longrightarrow>R(z)\<and>S(w)))
    \<longrightarrow> (\<exists>x y. P(x) \<and> Q(y)) \<longrightarrow> (\<exists>z. R(z))"
  by iprover

(* Problem 21 *)
lemma "(\<exists>x. P\<longrightarrow>Q(x)) \<and> (\<exists>x. Q(x)\<longrightarrow>P) \<longrightarrow> \<not>\<not>(\<exists>x. P=Q(x))"
  by iprover

(* Problem 22 *)
lemma "(\<forall>x. P = Q(x))  \<longrightarrow>  (P = (\<forall>x. Q(x)))"
  by iprover

(* Problem ~~23 *)
lemma "\<not>\<not> ((\<forall>x. P \<or> Q(x))  =  (P \<or> (\<forall>x. Q(x))))"
  by iprover

(* Problem 25 *)
lemma "(\<exists>x. P(x)) \<and>
       (\<forall>x. L(x) \<longrightarrow> \<not> (M(x) \<and> R(x))) \<and>
       (\<forall>x. P(x) \<longrightarrow> (M(x) \<and> L(x))) \<and>
       ((\<forall>x. P(x)\<longrightarrow>Q(x)) \<or> (\<exists>x. P(x)\<and>R(x)))
   \<longrightarrow> (\<exists>x. Q(x)\<and>P(x))"
  by iprover

(* Problem 27 *)
lemma "(\<exists>x. P(x) \<and> \<not>Q(x)) \<and>
             (\<forall>x. P(x) \<longrightarrow> R(x)) \<and>
             (\<forall>x. M(x) \<and> L(x) \<longrightarrow> P(x)) \<and>
             ((\<exists>x. R(x) \<and> \<not> Q(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> \<not> R(x)))
         \<longrightarrow> (\<forall>x. M(x) \<longrightarrow> \<not>L(x))"
  by iprover

(* Problem ~~28.  AMENDED *)
lemma "(\<forall>x. P(x) \<longrightarrow> (\<forall>x. Q(x))) \<and>
       (\<not>\<not>(\<forall>x. Q(x)\<or>R(x)) \<longrightarrow> (\<exists>x. Q(x)&S(x))) \<and>
       (\<not>\<not>(\<exists>x. S(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> M(x)))
   \<longrightarrow> (\<forall>x. P(x) \<and> L(x) \<longrightarrow> M(x))"
  by iprover

(* Problem 29.  Essentially the same as Principia Mathematica *11.71 *)
lemma "(((\<exists>x. P(x)) \<and> (\<exists>y. Q(y))) \<longrightarrow>
   (((\<forall>x. (P(x) \<longrightarrow> R(x))) \<and> (\<forall>y. (Q(y) \<longrightarrow> S(y)))) =
    (\<forall>x y. ((P(x) \<and> Q(y)) \<longrightarrow> (R(x) \<and> S(y))))))"
  by iprover

(* Problem ~~30 *)
lemma "(\<forall>x. (P(x) \<or> Q(x)) \<longrightarrow> \<not> R(x)) \<and>
       (\<forall>x. (Q(x) \<longrightarrow> \<not> S(x)) \<longrightarrow> P(x) \<and> R(x))
   \<longrightarrow> (\<forall>x. \<not>\<not>S(x))"
  by iprover

(* Problem 31 *)
lemma "\<not>(\<exists>x. P(x) \<and> (Q(x) \<or> R(x))) \<and>
        (\<exists>x. L(x) \<and> P(x)) \<and>
        (\<forall>x. \<not> R(x) \<longrightarrow> M(x))
    \<longrightarrow> (\<exists>x. L(x) \<and> M(x))"
  by iprover

(* Problem 32 *)
lemma "(\<forall>x. P(x) \<and> (Q(x)|R(x))\<longrightarrow>S(x)) \<and>
       (\<forall>x. S(x) \<and> R(x) \<longrightarrow> L(x)) \<and>
       (\<forall>x. M(x) \<longrightarrow> R(x))
   \<longrightarrow> (\<forall>x. P(x) \<and> M(x) \<longrightarrow> L(x))"
  by iprover

(* Problem ~~33 *)
lemma "(\<forall>x. \<not>\<not>(P(a) \<and> (P(x)\<longrightarrow>P(b))\<longrightarrow>P(c)))  =
       (\<forall>x. \<not>\<not>((\<not>P(a) \<or> P(x) \<or> P(c)) \<and> (\<not>P(a) \<or> \<not>P(b) \<or> P(c))))"
  oops

(* Problem 36 *)
lemma
     "(\<forall>x. \<exists>y. J x y) \<and>
      (\<forall>x. \<exists>y. G x y) \<and>
      (\<forall>x y. J x y \<or> G x y \<longrightarrow> (\<forall>z. J y z \<or> G y z \<longrightarrow> H x z))
  \<longrightarrow> (\<forall>x. \<exists>y. H x y)"
  by iprover

(* Problem 39 *)
lemma "\<not> (\<exists>x. \<forall>y. F y x = (\<not>F y y))"
  by iprover

(* Problem 40.  AMENDED *)
lemma "(\<exists>y. \<forall>x. F x y = F x x) \<longrightarrow>
             \<not>(\<forall>x. \<exists>y. \<forall>z. F z y = (\<not> F z x))"
  by iprover

(* Problem 44 *)
lemma "(\<forall>x. f(x) \<longrightarrow>
             (\<exists>y. g(y) \<and> h x y \<and> (\<exists>y. g(y) \<and> ~ h x y)))  \<and>
             (\<exists>x. j(x) \<and> (\<forall>y. g(y) \<longrightarrow> h x y))
             \<longrightarrow> (\<exists>x. j(x) \<and> \<not>f(x))"
  by iprover

(* Problem 48 *)
lemma "(a=b \<or> c=d) \<and> (a=c \<or> b=d) \<longrightarrow> a=d \<or> b=c"
  by iprover

(* Problem 51 *)
lemma "((\<exists>z w. (\<forall>x y. (P x y = ((x = z) \<and> (y = w))))) \<longrightarrow>
  (\<exists>z. (\<forall>x. (\<exists>w. ((\<forall>y. (P x y = (y = w))) = (x = z))))))"
  by iprover

(* Problem 52 *)
(*Almost the same as 51. *)
lemma "((\<exists>z w. (\<forall>x y. (P x y = ((x = z) \<and> (y = w))))) \<longrightarrow>
   (\<exists>w. (\<forall>y. (\<exists>z. ((\<forall>x. (P x y = (x = z))) = (y = w))))))"
  by iprover

(* Problem 56 *)
lemma "(\<forall>x. (\<exists>y. P(y) \<and> x=f(y)) \<longrightarrow> P(x)) = (\<forall>x. P(x) \<longrightarrow> P(f(x)))"
  by iprover

(* Problem 57 *)
lemma "P (f a b) (f b c) & P (f b c) (f a c) \<and>
     (\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z) \<longrightarrow> P (f a b) (f a c)"
  by iprover

(* Problem 60 *)
lemma "\<forall>x. P x (f x) = (\<exists>y. (\<forall>z. P z y \<longrightarrow> P z (f x)) \<and> P x y)"
  by iprover

end
