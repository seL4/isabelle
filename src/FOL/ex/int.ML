(*  Title:      FOL/ex/int
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Intuitionistic First-Order Logic

Single-step commands:
by (IntPr.step_tac 1);
by (biresolve_tac safe_brls 1);
by (biresolve_tac haz_brls 1);
by (assume_tac 1);
by (IntPr.safe_tac 1);
by (IntPr.mp_tac 1);
by (IntPr.fast_tac 1);
*)

context IFOL.thy;

writeln"File FOL/ex/int.";

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

Goal "~~(P&Q) <-> ~~P & ~~Q";
by (IntPr.fast_tac 1);
result();

Goal "~~ ((~P --> Q) --> (~P --> ~Q) --> P)";
by (IntPr.fast_tac 1);
result();

(* ~~ does NOT distribute over | *)

Goal "~~(P-->Q)  <-> (~~P --> ~~Q)";
by (IntPr.fast_tac 1);
result();

Goal "~~~P <-> ~P";
by (IntPr.fast_tac 1);
result();

Goal "~~((P --> Q | R)  -->  (P-->Q) | (P-->R))";
by (IntPr.fast_tac 1);
result();

Goal "(P<->Q) <-> (Q<->P)";
by (IntPr.fast_tac 1);
result();

Goal "((P --> (Q | (Q-->R))) --> R) --> R";
by (IntPr.fast_tac 1);
result();

Goal "(((G-->A) --> J) --> D --> E) --> (((H-->B)-->I)-->C-->J) \
\     --> (A-->H) --> F --> G --> (((C-->B)-->I)-->D)-->(A-->C) \
\     --> (((F-->A)-->B) --> I) --> E";
by (IntPr.fast_tac 1);
result();


writeln"Lemmas for the propositional double-negation translation";

Goal "P --> ~~P";
by (IntPr.fast_tac 1);
result();

Goal "~~(~~P --> P)";
by (IntPr.fast_tac 1);
result();

Goal "~~P & ~~(P --> Q) --> ~~Q";
by (IntPr.fast_tac 1);
result();


writeln"The following are classically but not constructively valid.";

(*The attempt to prove them terminates quickly!*)
Goal "((P-->Q) --> P)  -->  P";
by (IntPr.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
(*Check that subgoals remain: proof failed.*)
getgoal 1;  

Goal "(P&Q-->R)  -->  (P-->R) | (Q-->R)";
by (IntPr.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1;  


writeln"de Bruijn formulae";

(*de Bruijn formula with three predicates*)
Goal "((P<->Q) --> P&Q&R) &    \
\              ((Q<->R) --> P&Q&R) &    \
\              ((R<->P) --> P&Q&R) --> P&Q&R";
by (IntPr.fast_tac 1);
result();


(*de Bruijn formula with five predicates*)
Goal "((P<->Q) --> P&Q&R&S&T) &    \
\              ((Q<->R) --> P&Q&R&S&T) &    \
\              ((R<->S) --> P&Q&R&S&T) &    \
\              ((S<->T) --> P&Q&R&S&T) &    \
\              ((T<->P) --> P&Q&R&S&T) --> P&Q&R&S&T";
by (IntPr.fast_tac 1);
result();


(*** Problems from of Sahlin, Franzen and Haridi, 
     An Intuitionistic Predicate Logic Theorem Prover
***)

(*Problem 1.1*)
Goal "(ALL x. EX y. ALL z. p(x) & q(y) & r(z)) <->  \
\     (ALL z. EX y. ALL x. p(x) & q(y) & r(z))";
(*
by (IntPr.best_dup_tac 1);   (*65 seconds on a Pentium III!  Is it worth it?*)
*)

(*Problem 3.1*)
Goal "~ (EX x. ALL y. mem(y,x) <-> ~ mem(x,x))";
by (IntPr.fast_tac 1);
result();

(*Problem 4.1: hopeless!*)
Goal "(ALL x. p(x) --> p(h(x)) | p(g(x))) & (EX x. p(x)) & (ALL x. ~p(h(x))) \
\     --> (EX x. p(g(g(g(g(g(x)))))))";


writeln"Intuitionistic FOL: propositional problems based on Pelletier.";

writeln"Problem ~~1";
Goal "~~((P-->Q)  <->  (~Q --> ~P))";
by (IntPr.fast_tac 1);
result();


writeln"Problem ~~2";
Goal "~~(~~P  <->  P)";
by (IntPr.fast_tac 1);
result();
(*1 secs*)


writeln"Problem 3";
Goal "~(P-->Q) --> (Q-->P)";
by (IntPr.fast_tac 1);
result();

writeln"Problem ~~4";
Goal "~~((~P-->Q)  <->  (~Q --> P))";
by (IntPr.fast_tac 1);
result();
(*9 secs*)

writeln"Problem ~~5";
Goal "~~((P|Q-->P|R) --> P|(Q-->R))";
by (IntPr.fast_tac 1);
result();
(*10 secs*)


writeln"Problem ~~6";
Goal "~~(P | ~P)";
by (IntPr.fast_tac 1);
result();

writeln"Problem ~~7";
Goal "~~(P | ~~~P)";
by (IntPr.fast_tac 1);
result();

writeln"Problem ~~8.  Peirce's law";
Goal "~~(((P-->Q) --> P)  -->  P)";
by (IntPr.fast_tac 1);
result();

writeln"Problem 9";
Goal "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (IntPr.fast_tac 1);
result();
(*9 secs*)


writeln"Problem 10";
Goal "(Q-->R) --> (R-->P&Q) --> (P-->(Q|R)) --> (P<->Q)";
by (IntPr.fast_tac 1);
result();

writeln"11.  Proved in each direction (incorrectly, says Pelletier!!) ";
Goal "P<->P";
by (IntPr.fast_tac 1);

writeln"Problem ~~12.  Dijkstra's law  ";
Goal "~~(((P <-> Q) <-> R)  <->  (P <-> (Q <-> R)))";
by (IntPr.fast_tac 1);
result();

Goal "((P <-> Q) <-> R)  -->  ~~(P <-> (Q <-> R))";
by (IntPr.fast_tac 1);
result();

writeln"Problem 13.  Distributive law";
Goal "P | (Q & R)  <-> (P | Q) & (P | R)";
by (IntPr.fast_tac 1);
result();

writeln"Problem ~~14";
Goal "~~((P <-> Q) <-> ((Q | ~P) & (~Q|P)))";
by (IntPr.fast_tac 1);
result();

writeln"Problem ~~15";
Goal "~~((P --> Q) <-> (~P | Q))";
by (IntPr.fast_tac 1);
result();

writeln"Problem ~~16";
Goal "~~((P-->Q) | (Q-->P))";
by (IntPr.fast_tac 1);
result();

writeln"Problem ~~17";
Goal
  "~~(((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S)))";
by (IntPr.fast_tac 1);    
result();

(*Dijkstra's "Golden Rule"*)
Goal "(P&Q) <-> P <-> Q <-> (P|Q)";
by (IntPr.fast_tac 1);
result();


writeln"****Examples with quantifiers****";


writeln"The converse is classical in the following implications...";

Goal "(EX x. P(x)-->Q)  -->  (ALL x. P(x)) --> Q";
by (IntPr.fast_tac 1); 
result();  

Goal "((ALL x. P(x))-->Q) --> ~ (ALL x. P(x) & ~Q)";
by (IntPr.fast_tac 1); 
result();  

Goal "((ALL x. ~P(x))-->Q)  -->  ~ (ALL x. ~ (P(x)|Q))";
by (IntPr.fast_tac 1); 
result();  

Goal "(ALL x. P(x)) | Q  -->  (ALL x. P(x) | Q)";
by (IntPr.fast_tac 1); 
result();  

Goal "(EX x. P --> Q(x)) --> (P --> (EX x. Q(x)))";
by (IntPr.fast_tac 1);
result();  




writeln"The following are not constructively valid!";
(*The attempt to prove them terminates quickly!*)

Goal "((ALL x. P(x))-->Q) --> (EX x. P(x)-->Q)";
by (IntPr.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 

Goal "(P --> (EX x. Q(x))) --> (EX x. P-->Q(x))";
by (IntPr.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 

Goal "(ALL x. P(x) | Q) --> ((ALL x. P(x)) | Q)";
by (IntPr.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 

Goal "(ALL x. ~~P(x)) --> ~~(ALL x. P(x))";
by (IntPr.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 

(*Classically but not intuitionistically valid.  Proved by a bug in 1986!*)
Goal "EX x. Q(x) --> (ALL x. Q(x))";
by (IntPr.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 


writeln"Hard examples with quantifiers";

(*The ones that have not been proved are not known to be valid!
  Some will require quantifier duplication -- not currently available*)

writeln"Problem ~~18";
Goal "~~(EX y. ALL x. P(y)-->P(x))";
(*NOT PROVED*)

writeln"Problem ~~19";
Goal "~~(EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x)))";
(*NOT PROVED*)

writeln"Problem 20";
Goal "(ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))     \
\   --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))";
by (IntPr.fast_tac 1); 
result();

writeln"Problem 21";
Goal "(EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> ~~(EX x. P<->Q(x))";
(*NOT PROVED; needs quantifier duplication*)

writeln"Problem 22";
Goal "(ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))";
by (IntPr.fast_tac 1); 
result();

writeln"Problem ~~23";
Goal "~~ ((ALL x. P | Q(x))  <->  (P | (ALL x. Q(x))))";
by (IntPr.fast_tac 1); 
result();

writeln"Problem 24";
Goal "~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &  \
\    (~(EX x. P(x)) --> (EX x. Q(x))) & (ALL x. Q(x)|R(x) --> S(x))  \
\   --> ~~(EX x. P(x)&R(x))";
(*Not clear why fast_tac, best_tac, ASTAR and ITER_DEEPEN all take forever*)
by IntPr.safe_tac; 
by (etac impE 1);
by (IntPr.fast_tac 1); 
by (IntPr.fast_tac 1); 
result();

writeln"Problem 25";
Goal "(EX x. P(x)) &  \
\       (ALL x. L(x) --> ~ (M(x) & R(x))) &  \
\       (ALL x. P(x) --> (M(x) & L(x))) &   \
\       ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))  \
\   --> (EX x. Q(x)&P(x))";
by (IntPr.fast_tac 1); 
result();

writeln"Problem ~~26";
Goal "(~~(EX x. p(x)) <-> ~~(EX x. q(x))) &    \
\     (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))   \
\ --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))";
(*NOT PROVED*)

writeln"Problem 27";
Goal "(EX x. P(x) & ~Q(x)) &   \
\             (ALL x. P(x) --> R(x)) &   \
\             (ALL x. M(x) & L(x) --> P(x)) &   \
\             ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))  \
\         --> (ALL x. M(x) --> ~L(x))";
by (IntPr.fast_tac 1);   (*21 secs*)
result();

writeln"Problem ~~28.  AMENDED";
Goal "(ALL x. P(x) --> (ALL x. Q(x))) &   \
\       (~~(ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &  \
\       (~~(EX x. S(x)) --> (ALL x. L(x) --> M(x)))  \
\   --> (ALL x. P(x) & L(x) --> M(x))";
by (IntPr.fast_tac 1);  (*48 secs*)
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
Goal "(EX x. P(x)) & (EX y. Q(y))  \
\   --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->     \
\        (ALL x y. P(x) & Q(y) --> R(x) & S(y)))";
by (IntPr.fast_tac 1); 
result();

writeln"Problem ~~30";
Goal "(ALL x. (P(x) | Q(x)) --> ~ R(x)) & \
\       (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))  \
\   --> (ALL x. ~~S(x))";
by (IntPr.fast_tac 1);  
result();

writeln"Problem 31";
Goal "~(EX x. P(x) & (Q(x) | R(x))) & \
\       (EX x. L(x) & P(x)) & \
\       (ALL x. ~ R(x) --> M(x))  \
\   --> (EX x. L(x) & M(x))";
by (IntPr.fast_tac 1);
result();

writeln"Problem 32";
Goal "(ALL x. P(x) & (Q(x)|R(x))-->S(x)) & \
\       (ALL x. S(x) & R(x) --> L(x)) & \
\       (ALL x. M(x) --> R(x))  \
\   --> (ALL x. P(x) & M(x) --> L(x))";
by (IntPr.fast_tac 1);
result();

writeln"Problem ~~33";
Goal "(ALL x. ~~(P(a) & (P(x)-->P(b))-->P(c)))  <->    \
\     (ALL x. ~~((~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c))))";
by (IntPr.best_tac 1);   (*1.67s*)
result();


writeln"Problem 36";
Goal 
     "(ALL x. EX y. J(x,y)) & \
\     (ALL x. EX y. G(x,y)) & \
\     (ALL x y. J(x,y) | G(x,y) --> (ALL z. J(y,z) | G(y,z) --> H(x,z)))   \
\ --> (ALL x. EX y. H(x,y))";
by (IntPr.fast_tac 1);  (*5 secs*)
result();

writeln"Problem 37";
Goal
       "(ALL z. EX w. ALL x. EX y. \
\          ~~(P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u. Q(u,w)))) & \
\       (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) & \
\       (~~(EX x y. Q(x,y)) --> (ALL x. R(x,x)))  \
\   --> ~~(ALL x. EX y. R(x,y))";
(*NOT PROVED*)

writeln"Problem 39";
Goal "~ (EX x. ALL y. F(y,x) <-> ~F(y,y))";
by (IntPr.fast_tac 1);
result();

writeln"Problem 40.  AMENDED";
Goal "(EX y. ALL x. F(x,y) <-> F(x,x)) -->  \
\             ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))";
by (IntPr.fast_tac 1);
result();

writeln"Problem 44";
Goal "(ALL x. f(x) -->                                 \
\             (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &       \
\             (EX x. j(x) & (ALL y. g(y) --> h(x,y)))                   \
\             --> (EX x. j(x) & ~f(x))";
by (IntPr.fast_tac 1);
result();

writeln"Problem 48";
Goal "(a=b | c=d) & (a=c | b=d) --> a=d | b=c";
by (IntPr.fast_tac 1);
result();

writeln"Problem 51";
Goal "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\    (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)";
by (IntPr.fast_tac 1);
result();

writeln"Problem 52";
(*Almost the same as 51. *)
Goal "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\    (EX w. ALL y. EX z. (ALL x. P(x,y) <-> x=z) <-> y=w)";
by (IntPr.fast_tac 1);
result();

writeln"Problem 56";
Goal "(ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))";
by (IntPr.fast_tac 1);
result();

writeln"Problem 57";
Goal "P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) & \
\    (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))";
by (IntPr.fast_tac 1);
result();

writeln"Problem 60";
Goal "ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))";
by (IntPr.fast_tac 1);
result();

writeln"Reached end of file.";
