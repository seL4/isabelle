(*  Title:      FOL/ex/Intuitionistic
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

header{*Intuitionistic First-Order Logic*}

theory Intuitionistic = IFOL:

(*
Single-step ML commands:
by (IntPr.step_tac 1)
by (biresolve_tac safe_brls 1);
by (biresolve_tac haz_brls 1);
by (assume_tac 1);
by (IntPr.safe_tac 1);
by (IntPr.mp_tac 1);
by (IntPr.fast_tac 1);
*)


text{*Metatheorem (for \emph{propositional} formulae):
  $P$ is classically provable iff $\neg\neg P$ is intuitionistically provable.
  Therefore $\neg P$ is classically provable iff it is intuitionistically
  provable.

Proof: Let $Q$ be the conjuction of the propositions $A\vee\neg A$, one for
each atom $A$ in $P$.  Now $\neg\neg Q$ is intuitionistically provable because
$\neg\neg(A\vee\neg A)$ is and because double-negation distributes over
conjunction.  If $P$ is provable classically, then clearly $Q\rightarrow P$ is
provable intuitionistically, so $\neg\neg(Q\rightarrow P)$ is also provable
intuitionistically.  The latter is intuitionistically equivalent to $\neg\neg
Q\rightarrow\neg\neg P$, hence to $\neg\neg P$, since $\neg\neg Q$ is
intuitionistically provable.  Finally, if $P$ is a negation then $\neg\neg P$
is intuitionstically equivalent to $P$.  [Andy Pitts] *}

lemma "~~(P&Q) <-> ~~P & ~~Q"
by (tactic{*IntPr.fast_tac 1*})

lemma "~~ ((~P --> Q) --> (~P --> ~Q) --> P)"
by (tactic{*IntPr.fast_tac 1*})

text{*Double-negation does NOT distribute over disjunction*}

lemma "~~(P-->Q)  <-> (~~P --> ~~Q)"
by (tactic{*IntPr.fast_tac 1*})

lemma "~~~P <-> ~P"
by (tactic{*IntPr.fast_tac 1*})

lemma "~~((P --> Q | R)  -->  (P-->Q) | (P-->R))"
by (tactic{*IntPr.fast_tac 1*})

lemma "(P<->Q) <-> (Q<->P)"
by (tactic{*IntPr.fast_tac 1*})

lemma "((P --> (Q | (Q-->R))) --> R) --> R"
by (tactic{*IntPr.fast_tac 1*})

lemma "(((G-->A) --> J) --> D --> E) --> (((H-->B)-->I)-->C-->J)
      --> (A-->H) --> F --> G --> (((C-->B)-->I)-->D)-->(A-->C)
      --> (((F-->A)-->B) --> I) --> E"
by (tactic{*IntPr.fast_tac 1*})


text{*Lemmas for the propositional double-negation translation*}

lemma "P --> ~~P"
by (tactic{*IntPr.fast_tac 1*})

lemma "~~(~~P --> P)"
by (tactic{*IntPr.fast_tac 1*})

lemma "~~P & ~~(P --> Q) --> ~~Q"
by (tactic{*IntPr.fast_tac 1*})


text{*The following are classically but not constructively valid.
      The attempt to prove them terminates quickly!*}
lemma "((P-->Q) --> P)  -->  P"
apply (tactic{*IntPr.fast_tac 1*} | -)
apply (rule asm_rl) --{*Checks that subgoals remain: proof failed.*}
oops

lemma "(P&Q-->R)  -->  (P-->R) | (Q-->R)"
apply (tactic{*IntPr.fast_tac 1*} | -)
apply (rule asm_rl) --{*Checks that subgoals remain: proof failed.*}
oops


subsection{*de Bruijn formulae*}

text{*de Bruijn formula with three predicates*}
lemma "((P<->Q) --> P&Q&R) &
               ((Q<->R) --> P&Q&R) &
               ((R<->P) --> P&Q&R) --> P&Q&R"
by (tactic{*IntPr.fast_tac 1*})


text{*de Bruijn formula with five predicates*}
lemma "((P<->Q) --> P&Q&R&S&T) &
               ((Q<->R) --> P&Q&R&S&T) &
               ((R<->S) --> P&Q&R&S&T) &
               ((S<->T) --> P&Q&R&S&T) &
               ((T<->P) --> P&Q&R&S&T) --> P&Q&R&S&T"
by (tactic{*IntPr.fast_tac 1*})


(*** Problems from of Sahlin, Franzen and Haridi,
     An Intuitionistic Predicate Logic Theorem Prover.
     J. Logic and Comp. 2 (5), October 1992, 619-656.
***)

text{*Problem 1.1*}
lemma "(ALL x. EX y. ALL z. p(x) & q(y) & r(z)) <->
      (ALL z. EX y. ALL x. p(x) & q(y) & r(z))"
by (tactic{*IntPr.best_dup_tac 1*})  --{*SLOW*}

text{*Problem 3.1*}
lemma "~ (EX x. ALL y. mem(y,x) <-> ~ mem(x,x))"
by (tactic{*IntPr.fast_tac 1*})

text{*Problem 4.1: hopeless!*}
lemma "(ALL x. p(x) --> p(h(x)) | p(g(x))) & (EX x. p(x)) & (ALL x. ~p(h(x)))
      --> (EX x. p(g(g(g(g(g(x)))))))"
oops


subsection{*Intuitionistic FOL: propositional problems based on Pelletier.*}

text{*~~1*}
lemma "~~((P-->Q)  <->  (~Q --> ~P))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~2*}
lemma "~~(~~P  <->  P)"
by (tactic{*IntPr.fast_tac 1*})

text{*3*}
lemma "~(P-->Q) --> (Q-->P)"
by (tactic{*IntPr.fast_tac 1*})

text{*~~4*}
lemma "~~((~P-->Q)  <->  (~Q --> P))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~5*}
lemma "~~((P|Q-->P|R) --> P|(Q-->R))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~6*}
lemma "~~(P | ~P)"
by (tactic{*IntPr.fast_tac 1*})

text{*~~7*}
lemma "~~(P | ~~~P)"
by (tactic{*IntPr.fast_tac 1*})

text{*~~8.  Peirce's law*}
lemma "~~(((P-->Q) --> P)  -->  P)"
by (tactic{*IntPr.fast_tac 1*})

text{*9*}
lemma "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
by (tactic{*IntPr.fast_tac 1*})

text{*10*}
lemma "(Q-->R) --> (R-->P&Q) --> (P-->(Q|R)) --> (P<->Q)"
by (tactic{*IntPr.fast_tac 1*})

subsection{*11.  Proved in each direction (incorrectly, says Pelletier!!) *}
lemma "P<->P"
by (tactic{*IntPr.fast_tac 1*})

text{*~~12.  Dijkstra's law  *}
lemma "~~(((P <-> Q) <-> R)  <->  (P <-> (Q <-> R)))"
by (tactic{*IntPr.fast_tac 1*})

lemma "((P <-> Q) <-> R)  -->  ~~(P <-> (Q <-> R))"
by (tactic{*IntPr.fast_tac 1*})

text{*13.  Distributive law*}
lemma "P | (Q & R)  <-> (P | Q) & (P | R)"
by (tactic{*IntPr.fast_tac 1*})

text{*~~14*}
lemma "~~((P <-> Q) <-> ((Q | ~P) & (~Q|P)))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~15*}
lemma "~~((P --> Q) <-> (~P | Q))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~16*}
lemma "~~((P-->Q) | (Q-->P))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~17*}
lemma "~~(((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S)))"
by (tactic{*IntPr.fast_tac 1*})

text{*Dijkstra's "Golden Rule"*}
lemma "(P&Q) <-> P <-> Q <-> (P|Q)"
by (tactic{*IntPr.fast_tac 1*})


subsection{*****Examples with quantifiers*****}


subsection{*The converse is classical in the following implications...*}

lemma "(EX x. P(x)-->Q)  -->  (ALL x. P(x)) --> Q"
by (tactic{*IntPr.fast_tac 1*})

lemma "((ALL x. P(x))-->Q) --> ~ (ALL x. P(x) & ~Q)"
by (tactic{*IntPr.fast_tac 1*})

lemma "((ALL x. ~P(x))-->Q)  -->  ~ (ALL x. ~ (P(x)|Q))"
by (tactic{*IntPr.fast_tac 1*})

lemma "(ALL x. P(x)) | Q  -->  (ALL x. P(x) | Q)"
by (tactic{*IntPr.fast_tac 1*})

lemma "(EX x. P --> Q(x)) --> (P --> (EX x. Q(x)))"
by (tactic{*IntPr.fast_tac 1*})




subsection{*The following are not constructively valid!*}
text{*The attempt to prove them terminates quickly!*}

lemma "((ALL x. P(x))-->Q) --> (EX x. P(x)-->Q)"
apply (tactic{*IntPr.fast_tac 1*} | -)
apply (rule asm_rl) --{*Checks that subgoals remain: proof failed.*}
oops

lemma "(P --> (EX x. Q(x))) --> (EX x. P-->Q(x))"
apply (tactic{*IntPr.fast_tac 1*} | -)
apply (rule asm_rl) --{*Checks that subgoals remain: proof failed.*}
oops

lemma "(ALL x. P(x) | Q) --> ((ALL x. P(x)) | Q)"
apply (tactic{*IntPr.fast_tac 1*} | -)
apply (rule asm_rl) --{*Checks that subgoals remain: proof failed.*}
oops

lemma "(ALL x. ~~P(x)) --> ~~(ALL x. P(x))"
apply (tactic{*IntPr.fast_tac 1*} | -)
apply (rule asm_rl) --{*Checks that subgoals remain: proof failed.*}
oops

text{*Classically but not intuitionistically valid.  Proved by a bug in 1986!*}
lemma "EX x. Q(x) --> (ALL x. Q(x))"
apply (tactic{*IntPr.fast_tac 1*} | -)
apply (rule asm_rl) --{*Checks that subgoals remain: proof failed.*}
oops


subsection{*Hard examples with quantifiers*}

text{*The ones that have not been proved are not known to be valid!
  Some will require quantifier duplication -- not currently available*}

text{*~~18*}
lemma "~~(EX y. ALL x. P(y)-->P(x))"
oops  --{*NOT PROVED*}

text{*~~19*}
lemma "~~(EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x)))"
oops  --{*NOT PROVED*}

text{*20*}
lemma "(ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))
    --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))"
by (tactic{*IntPr.fast_tac 1*})

text{*21*}
lemma "(EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> ~~(EX x. P<->Q(x))"
oops --{*NOT PROVED; needs quantifier duplication*}

text{*22*}
lemma "(ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~23*}
lemma "~~ ((ALL x. P | Q(x))  <->  (P | (ALL x. Q(x))))"
by (tactic{*IntPr.fast_tac 1*})

text{*24*}
lemma "~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &
     (~(EX x. P(x)) --> (EX x. Q(x))) & (ALL x. Q(x)|R(x) --> S(x))
    --> ~~(EX x. P(x)&R(x))"
txt{*Not clear why @{text fast_tac}, @{text best_tac}, @{text ASTAR} and 
    @{text ITER_DEEPEN} all take forever*}
apply (tactic{* IntPr.safe_tac*})
apply (erule impE)
apply (tactic{*IntPr.fast_tac 1*})
by (tactic{*IntPr.fast_tac 1*})

text{*25*}
lemma "(EX x. P(x)) &
        (ALL x. L(x) --> ~ (M(x) & R(x))) &
        (ALL x. P(x) --> (M(x) & L(x))) &
        ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))
    --> (EX x. Q(x)&P(x))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~26*}
lemma "(~~(EX x. p(x)) <-> ~~(EX x. q(x))) &
      (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))
  --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))"
oops  --{*NOT PROVED*}

text{*27*}
lemma "(EX x. P(x) & ~Q(x)) &
              (ALL x. P(x) --> R(x)) &
              (ALL x. M(x) & L(x) --> P(x)) &
              ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))
          --> (ALL x. M(x) --> ~L(x))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~28.  AMENDED*}
lemma "(ALL x. P(x) --> (ALL x. Q(x))) &
        (~~(ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &
        (~~(EX x. S(x)) --> (ALL x. L(x) --> M(x)))
    --> (ALL x. P(x) & L(x) --> M(x))"
by (tactic{*IntPr.fast_tac 1*})

text{*29.  Essentially the same as Principia Mathematica *11.71*}
lemma "(EX x. P(x)) & (EX y. Q(y))
    --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->
         (ALL x y. P(x) & Q(y) --> R(x) & S(y)))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~30*}
lemma "(ALL x. (P(x) | Q(x)) --> ~ R(x)) &
        (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))
    --> (ALL x. ~~S(x))"
by (tactic{*IntPr.fast_tac 1*})

text{*31*}
lemma "~(EX x. P(x) & (Q(x) | R(x))) &
        (EX x. L(x) & P(x)) &
        (ALL x. ~ R(x) --> M(x))
    --> (EX x. L(x) & M(x))"
by (tactic{*IntPr.fast_tac 1*})

text{*32*}
lemma "(ALL x. P(x) & (Q(x)|R(x))-->S(x)) &
        (ALL x. S(x) & R(x) --> L(x)) &
        (ALL x. M(x) --> R(x))
    --> (ALL x. P(x) & M(x) --> L(x))"
by (tactic{*IntPr.fast_tac 1*})

text{*~~33*}
lemma "(ALL x. ~~(P(a) & (P(x)-->P(b))-->P(c)))  <->
      (ALL x. ~~((~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c))))"
apply (tactic{*IntPr.best_tac 1*})
done


text{*36*}
lemma "(ALL x. EX y. J(x,y)) &
      (ALL x. EX y. G(x,y)) &
      (ALL x y. J(x,y) | G(x,y) --> (ALL z. J(y,z) | G(y,z) --> H(x,z)))
  --> (ALL x. EX y. H(x,y))"
by (tactic{*IntPr.fast_tac 1*})

text{*37*}
lemma "(ALL z. EX w. ALL x. EX y.
           ~~(P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u. Q(u,w)))) &
        (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) &
        (~~(EX x y. Q(x,y)) --> (ALL x. R(x,x)))
    --> ~~(ALL x. EX y. R(x,y))"
oops  --{*NOT PROVED*}

text{*39*}
lemma "~ (EX x. ALL y. F(y,x) <-> ~F(y,y))"
by (tactic{*IntPr.fast_tac 1*})

text{*40.  AMENDED*}
lemma "(EX y. ALL x. F(x,y) <-> F(x,x)) -->
              ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))"
by (tactic{*IntPr.fast_tac 1*})

text{*44*}
lemma "(ALL x. f(x) -->
              (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &
              (EX x. j(x) & (ALL y. g(y) --> h(x,y)))
              --> (EX x. j(x) & ~f(x))"
by (tactic{*IntPr.fast_tac 1*})

text{*48*}
lemma "(a=b | c=d) & (a=c | b=d) --> a=d | b=c"
by (tactic{*IntPr.fast_tac 1*})

text{*51*}
lemma "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->
     (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)"
by (tactic{*IntPr.fast_tac 1*})

text{*52*}
text{*Almost the same as 51. *}
lemma "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->
     (EX w. ALL y. EX z. (ALL x. P(x,y) <-> x=z) <-> y=w)"
by (tactic{*IntPr.fast_tac 1*})

text{*56*}
lemma "(ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))"
by (tactic{*IntPr.fast_tac 1*})

text{*57*}
lemma "P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) &
     (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))"
by (tactic{*IntPr.fast_tac 1*})

text{*60*}
lemma "ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))"
by (tactic{*IntPr.fast_tac 1*})

end


