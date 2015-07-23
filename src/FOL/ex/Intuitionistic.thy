(*  Title:      FOL/ex/Intuitionistic.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>Intuitionistic First-Order Logic\<close>

theory Intuitionistic
imports IFOL
begin

(*
Single-step ML commands:
by (IntPr.step_tac 1)
by (biresolve_tac safe_brls 1);
by (biresolve_tac haz_brls 1);
by (assume_tac 1);
by (IntPr.safe_tac 1);
by (IntPr.mp_tac 1);
by (IntPr.fast_tac @{context} 1);
*)


text\<open>Metatheorem (for \emph{propositional} formulae):
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
is intuitionstically equivalent to $P$.  [Andy Pitts]\<close>

lemma "~~(P&Q) <-> ~~P & ~~Q"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "~~ ((~P --> Q) --> (~P --> ~Q) --> P)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>Double-negation does NOT distribute over disjunction\<close>

lemma "~~(P-->Q)  <-> (~~P --> ~~Q)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "~~~P <-> ~P"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "~~((P --> Q | R)  -->  (P-->Q) | (P-->R))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "(P<->Q) <-> (Q<->P)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "((P --> (Q | (Q-->R))) --> R) --> R"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "(((G-->A) --> J) --> D --> E) --> (((H-->B)-->I)-->C-->J)
      --> (A-->H) --> F --> G --> (((C-->B)-->I)-->D)-->(A-->C)
      --> (((F-->A)-->B) --> I) --> E"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)


text\<open>Lemmas for the propositional double-negation translation\<close>

lemma "P --> ~~P"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "~~(~~P --> P)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "~~P & ~~(P --> Q) --> ~~Q"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)


text\<open>The following are classically but not constructively valid.
      The attempt to prove them terminates quickly!\<close>
lemma "((P-->Q) --> P)  -->  P"
apply (tactic\<open>IntPr.fast_tac @{context} 1\<close> | -)
apply (rule asm_rl) --\<open>Checks that subgoals remain: proof failed.\<close>
oops

lemma "(P&Q-->R)  -->  (P-->R) | (Q-->R)"
apply (tactic\<open>IntPr.fast_tac @{context} 1\<close> | -)
apply (rule asm_rl) --\<open>Checks that subgoals remain: proof failed.\<close>
oops


subsection\<open>de Bruijn formulae\<close>

text\<open>de Bruijn formula with three predicates\<close>
lemma "((P<->Q) --> P&Q&R) &
               ((Q<->R) --> P&Q&R) &
               ((R<->P) --> P&Q&R) --> P&Q&R"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)


text\<open>de Bruijn formula with five predicates\<close>
lemma "((P<->Q) --> P&Q&R&S&T) &
               ((Q<->R) --> P&Q&R&S&T) &
               ((R<->S) --> P&Q&R&S&T) &
               ((S<->T) --> P&Q&R&S&T) &
               ((T<->P) --> P&Q&R&S&T) --> P&Q&R&S&T"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)


(*** Problems from of Sahlin, Franzen and Haridi,
     An Intuitionistic Predicate Logic Theorem Prover.
     J. Logic and Comp. 2 (5), October 1992, 619-656.
***)

text\<open>Problem 1.1\<close>
lemma "(ALL x. EX y. ALL z. p(x) & q(y) & r(z)) <->
      (ALL z. EX y. ALL x. p(x) & q(y) & r(z))"
by (tactic\<open>IntPr.best_dup_tac @{context} 1\<close>)  --\<open>SLOW\<close>

text\<open>Problem 3.1\<close>
lemma "~ (EX x. ALL y. mem(y,x) <-> ~ mem(x,x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>Problem 4.1: hopeless!\<close>
lemma "(ALL x. p(x) --> p(h(x)) | p(g(x))) & (EX x. p(x)) & (ALL x. ~p(h(x)))
      --> (EX x. p(g(g(g(g(g(x)))))))"
oops


subsection\<open>Intuitionistic FOL: propositional problems based on Pelletier.\<close>

text\<open>~~1\<close>
lemma "~~((P-->Q)  <->  (~Q --> ~P))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~2\<close>
lemma "~~(~~P  <->  P)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>3\<close>
lemma "~(P-->Q) --> (Q-->P)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~4\<close>
lemma "~~((~P-->Q)  <->  (~Q --> P))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~5\<close>
lemma "~~((P|Q-->P|R) --> P|(Q-->R))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~6\<close>
lemma "~~(P | ~P)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~7\<close>
lemma "~~(P | ~~~P)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~8.  Peirce's law\<close>
lemma "~~(((P-->Q) --> P)  -->  P)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>9\<close>
lemma "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>10\<close>
lemma "(Q-->R) --> (R-->P&Q) --> (P-->(Q|R)) --> (P<->Q)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

subsection\<open>11.  Proved in each direction (incorrectly, says Pelletier!!)\<close>
lemma "P<->P"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~12.  Dijkstra's law\<close>
lemma "~~(((P <-> Q) <-> R)  <->  (P <-> (Q <-> R)))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "((P <-> Q) <-> R)  -->  ~~(P <-> (Q <-> R))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>13.  Distributive law\<close>
lemma "P | (Q & R)  <-> (P | Q) & (P | R)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~14\<close>
lemma "~~((P <-> Q) <-> ((Q | ~P) & (~Q|P)))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~15\<close>
lemma "~~((P --> Q) <-> (~P | Q))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~16\<close>
lemma "~~((P-->Q) | (Q-->P))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~17\<close>
lemma "~~(((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S)))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>Dijkstra's "Golden Rule"\<close>
lemma "(P&Q) <-> P <-> Q <-> (P|Q)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)


subsection\<open>****Examples with quantifiers****\<close>


subsection\<open>The converse is classical in the following implications...\<close>

lemma "(EX x. P(x)-->Q)  -->  (ALL x. P(x)) --> Q"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "((ALL x. P(x))-->Q) --> ~ (ALL x. P(x) & ~Q)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "((ALL x. ~P(x))-->Q)  -->  ~ (ALL x. ~ (P(x)|Q))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "(ALL x. P(x)) | Q  -->  (ALL x. P(x) | Q)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

lemma "(EX x. P --> Q(x)) --> (P --> (EX x. Q(x)))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)




subsection\<open>The following are not constructively valid!\<close>
text\<open>The attempt to prove them terminates quickly!\<close>

lemma "((ALL x. P(x))-->Q) --> (EX x. P(x)-->Q)"
apply (tactic\<open>IntPr.fast_tac @{context} 1\<close> | -)
apply (rule asm_rl) --\<open>Checks that subgoals remain: proof failed.\<close>
oops

lemma "(P --> (EX x. Q(x))) --> (EX x. P-->Q(x))"
apply (tactic\<open>IntPr.fast_tac @{context} 1\<close> | -)
apply (rule asm_rl) --\<open>Checks that subgoals remain: proof failed.\<close>
oops

lemma "(ALL x. P(x) | Q) --> ((ALL x. P(x)) | Q)"
apply (tactic\<open>IntPr.fast_tac @{context} 1\<close> | -)
apply (rule asm_rl) --\<open>Checks that subgoals remain: proof failed.\<close>
oops

lemma "(ALL x. ~~P(x)) --> ~~(ALL x. P(x))"
apply (tactic\<open>IntPr.fast_tac @{context} 1\<close> | -)
apply (rule asm_rl) --\<open>Checks that subgoals remain: proof failed.\<close>
oops

text\<open>Classically but not intuitionistically valid.  Proved by a bug in 1986!\<close>
lemma "EX x. Q(x) --> (ALL x. Q(x))"
apply (tactic\<open>IntPr.fast_tac @{context} 1\<close> | -)
apply (rule asm_rl) --\<open>Checks that subgoals remain: proof failed.\<close>
oops


subsection\<open>Hard examples with quantifiers\<close>

text\<open>The ones that have not been proved are not known to be valid!
  Some will require quantifier duplication -- not currently available\<close>

text\<open>~~18\<close>
lemma "~~(EX y. ALL x. P(y)-->P(x))"
oops  --\<open>NOT PROVED\<close>

text\<open>~~19\<close>
lemma "~~(EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x)))"
oops  --\<open>NOT PROVED\<close>

text\<open>20\<close>
lemma "(ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))
    --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>21\<close>
lemma "(EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> ~~(EX x. P<->Q(x))"
oops --\<open>NOT PROVED; needs quantifier duplication\<close>

text\<open>22\<close>
lemma "(ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~23\<close>
lemma "~~ ((ALL x. P | Q(x))  <->  (P | (ALL x. Q(x))))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>24\<close>
lemma "~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &
     (~(EX x. P(x)) --> (EX x. Q(x))) & (ALL x. Q(x)|R(x) --> S(x))
    --> ~~(EX x. P(x)&R(x))"
txt\<open>Not clear why @{text fast_tac}, @{text best_tac}, @{text ASTAR} and 
    @{text ITER_DEEPEN} all take forever\<close>
apply (tactic\<open>IntPr.safe_tac @{context}\<close>)
apply (erule impE)
apply (tactic\<open>IntPr.fast_tac @{context} 1\<close>)
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>25\<close>
lemma "(EX x. P(x)) &
        (ALL x. L(x) --> ~ (M(x) & R(x))) &
        (ALL x. P(x) --> (M(x) & L(x))) &
        ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))
    --> (EX x. Q(x)&P(x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~26\<close>
lemma "(~~(EX x. p(x)) <-> ~~(EX x. q(x))) &
      (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))
  --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))"
oops  --\<open>NOT PROVED\<close>

text\<open>27\<close>
lemma "(EX x. P(x) & ~Q(x)) &
              (ALL x. P(x) --> R(x)) &
              (ALL x. M(x) & L(x) --> P(x)) &
              ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))
          --> (ALL x. M(x) --> ~L(x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~28.  AMENDED\<close>
lemma "(ALL x. P(x) --> (ALL x. Q(x))) &
        (~~(ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &
        (~~(EX x. S(x)) --> (ALL x. L(x) --> M(x)))
    --> (ALL x. P(x) & L(x) --> M(x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>29.  Essentially the same as Principia Mathematica *11.71\<close>
lemma "(EX x. P(x)) & (EX y. Q(y))
    --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->
         (ALL x y. P(x) & Q(y) --> R(x) & S(y)))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~30\<close>
lemma "(ALL x. (P(x) | Q(x)) --> ~ R(x)) &
        (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))
    --> (ALL x. ~~S(x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>31\<close>
lemma "~(EX x. P(x) & (Q(x) | R(x))) &
        (EX x. L(x) & P(x)) &
        (ALL x. ~ R(x) --> M(x))
    --> (EX x. L(x) & M(x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>32\<close>
lemma "(ALL x. P(x) & (Q(x)|R(x))-->S(x)) &
        (ALL x. S(x) & R(x) --> L(x)) &
        (ALL x. M(x) --> R(x))
    --> (ALL x. P(x) & M(x) --> L(x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>~~33\<close>
lemma "(ALL x. ~~(P(a) & (P(x)-->P(b))-->P(c)))  <->
      (ALL x. ~~((~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c))))"
apply (tactic\<open>IntPr.best_tac @{context} 1\<close>)
done


text\<open>36\<close>
lemma "(ALL x. EX y. J(x,y)) &
      (ALL x. EX y. G(x,y)) &
      (ALL x y. J(x,y) | G(x,y) --> (ALL z. J(y,z) | G(y,z) --> H(x,z)))
  --> (ALL x. EX y. H(x,y))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>37\<close>
lemma "(ALL z. EX w. ALL x. EX y.
           ~~(P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u. Q(u,w)))) &
        (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) &
        (~~(EX x y. Q(x,y)) --> (ALL x. R(x,x)))
    --> ~~(ALL x. EX y. R(x,y))"
oops  --\<open>NOT PROVED\<close>

text\<open>39\<close>
lemma "~ (EX x. ALL y. F(y,x) <-> ~F(y,y))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>40.  AMENDED\<close>
lemma "(EX y. ALL x. F(x,y) <-> F(x,x)) -->
              ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>44\<close>
lemma "(ALL x. f(x) -->
              (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &
              (EX x. j(x) & (ALL y. g(y) --> h(x,y)))
              --> (EX x. j(x) & ~f(x))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>48\<close>
lemma "(a=b | c=d) & (a=c | b=d) --> a=d | b=c"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>51\<close>
lemma "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->
     (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>52\<close>
text\<open>Almost the same as 51.\<close>
lemma "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->
     (EX w. ALL y. EX z. (ALL x. P(x,y) <-> x=z) <-> y=w)"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>56\<close>
lemma "(ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>57\<close>
lemma "P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) &
     (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>60\<close>
lemma "ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))"
by (tactic\<open>IntPr.fast_tac @{context} 1\<close>)

end

