(*  Title: 	FOL/ex/int
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Intuitionistic First-Order Logic

Single-step commands:
by (Int.step_tac 1);
by (biresolve_tac safe_brls 1);
by (biresolve_tac haz_brls 1);
by (assume_tac 1);
by (Int.safe_tac 1);
by (Int.mp_tac 1);
by (Int.fast_tac 1);
*)

writeln"File FOL/ex/int.";

(*Note: for PROPOSITIONAL formulae...
  ~A is classically provable iff it is intuitionistically provable.  
  Therefore A is classically provable iff ~~A is intuitionistically provable.

Let Q be the conjuction of the propositions A|~A, one for each atom A in
P.  If P is provable classically, then clearly P&Q is provable
intuitionistically, so ~~(P&Q) is also provable intuitionistically.
The latter is intuitionistically equivalent to ~~P&~~Q, hence to ~~P,
since ~~Q is intuitionistically provable.  Finally, if P is a negation then
~~P is intuitionstically equivalent to P.  [Andy Pitts]
*)

goal IFOL.thy "~~(P&Q) <-> ~~P & ~~Q";
by (Int.fast_tac 1);
result();

goal IFOL.thy "~~~P <-> ~P";
by (Int.fast_tac 1);
result();

goal IFOL.thy "~~((P --> Q | R)  -->  (P-->Q) | (P-->R))";
by (Int.fast_tac 1);
result();

goal IFOL.thy "(P<->Q) <-> (Q<->P)";
by (Int.fast_tac 1);
result();


writeln"Lemmas for the propositional double-negation translation";

goal IFOL.thy "P --> ~~P";
by (Int.fast_tac 1);
result();

goal IFOL.thy "~~(~~P --> P)";
by (Int.fast_tac 1);
result();

goal IFOL.thy "~~P & ~~(P --> Q) --> ~~Q";
by (Int.fast_tac 1);
result();


writeln"The following are classically but not constructively valid.";

(*The attempt to prove them terminates quickly!*)
goal IFOL.thy "((P-->Q) --> P)  -->  P";
by (Int.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
(*Check that subgoals remain: proof failed.*)
getgoal 1;  

goal IFOL.thy "(P&Q-->R)  -->  (P-->R) | (Q-->R)";
by (Int.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1;  


writeln"Intuitionistic FOL: propositional problems based on Pelletier.";

writeln"Problem ~~1";
goal IFOL.thy "~~((P-->Q)  <->  (~Q --> ~P))";
by (Int.fast_tac 1);
result();
(*5 secs*)


writeln"Problem ~~2";
goal IFOL.thy "~~(~~P  <->  P)";
by (Int.fast_tac 1);
result();
(*1 secs*)


writeln"Problem 3";
goal IFOL.thy "~(P-->Q) --> (Q-->P)";
by (Int.fast_tac 1);
result();

writeln"Problem ~~4";
goal IFOL.thy "~~((~P-->Q)  <->  (~Q --> P))";
by (Int.fast_tac 1);
result();
(*9 secs*)

writeln"Problem ~~5";
goal IFOL.thy "~~((P|Q-->P|R) --> P|(Q-->R))";
by (Int.fast_tac 1);
result();
(*10 secs*)


writeln"Problem ~~6";
goal IFOL.thy "~~(P | ~P)";
by (Int.fast_tac 1);
result();

writeln"Problem ~~7";
goal IFOL.thy "~~(P | ~~~P)";
by (Int.fast_tac 1);
result();

writeln"Problem ~~8.  Peirce's law";
goal IFOL.thy "~~(((P-->Q) --> P)  -->  P)";
by (Int.fast_tac 1);
result();

writeln"Problem 9";
goal IFOL.thy "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (Int.fast_tac 1);
result();
(*9 secs*)


writeln"Problem 10";
goal IFOL.thy "(Q-->R) --> (R-->P&Q) --> (P-->(Q|R)) --> (P<->Q)";
by (Int.fast_tac 1);
result();

writeln"11.  Proved in each direction (incorrectly, says Pelletier!!) ";
goal IFOL.thy "P<->P";
by (Int.fast_tac 1);

writeln"Problem ~~12.  Dijkstra's law  ";
goal IFOL.thy "~~(((P <-> Q) <-> R)  <->  (P <-> (Q <-> R)))";
by (Int.fast_tac 1);
result();

goal IFOL.thy "((P <-> Q) <-> R)  -->  ~~(P <-> (Q <-> R))";
by (Int.fast_tac 1);
result();

writeln"Problem 13.  Distributive law";
goal IFOL.thy "P | (Q & R)  <-> (P | Q) & (P | R)";
by (Int.fast_tac 1);
result();

writeln"Problem ~~14";
goal IFOL.thy "~~((P <-> Q) <-> ((Q | ~P) & (~Q|P)))";
by (Int.fast_tac 1);
result();

writeln"Problem ~~15";
goal IFOL.thy "~~((P --> Q) <-> (~P | Q))";
by (Int.fast_tac 1);
result();

writeln"Problem ~~16";
goal IFOL.thy "~~((P-->Q) | (Q-->P))";
by (Int.fast_tac 1);
result();

writeln"Problem ~~17";
goal IFOL.thy
  "~~(((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S)))";
by (Int.fast_tac 1);    
result();

(*Dijkstra's "Golden Rule"*)
goal IFOL.thy "(P&Q) <-> P <-> Q <-> (P|Q)";
by (Int.fast_tac 1);
result();


writeln"U****Examples with quantifiers****";


writeln"The converse is classical in the following implications...";

goal IFOL.thy "(EX x.P(x)-->Q)  -->  (ALL x.P(x)) --> Q";
by (Int.fast_tac 1); 
result();  

goal IFOL.thy "((ALL x.P(x))-->Q) --> ~ (ALL x. P(x) & ~Q)";
by (Int.fast_tac 1); 
result();  

goal IFOL.thy "((ALL x. ~P(x))-->Q)  -->  ~ (ALL x. ~ (P(x)|Q))";
by (Int.fast_tac 1); 
result();  

goal IFOL.thy "(ALL x.P(x)) | Q  -->  (ALL x. P(x) | Q)";
by (Int.fast_tac 1); 
result();  

goal IFOL.thy "(EX x. P --> Q(x)) --> (P --> (EX x. Q(x)))";
by (Int.fast_tac 1);
result();  




writeln"The following are not constructively valid!";
(*The attempt to prove them terminates quickly!*)

goal IFOL.thy "((ALL x.P(x))-->Q) --> (EX x.P(x)-->Q)";
by (Int.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 

goal IFOL.thy "(P --> (EX x.Q(x))) --> (EX x. P-->Q(x))";
by (Int.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 

goal IFOL.thy "(ALL x. P(x) | Q) --> ((ALL x.P(x)) | Q)";
by (Int.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 

goal IFOL.thy "(ALL x. ~~P(x)) --> ~~(ALL x. P(x))";
by (Int.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 

(*Classically but not intuitionistically valid.  Proved by a bug in 1986!*)
goal IFOL.thy "EX x. Q(x) --> (ALL x. Q(x))";
by (Int.fast_tac 1) handle ERROR => writeln"Failed, as expected";  
getgoal 1; 


writeln"Hard examples with quantifiers";

(*The ones that have not been proved are not known to be valid!
  Some will require quantifier duplication -- not currently available*)

writeln"Problem ~~18";
goal IFOL.thy "~~(EX y. ALL x. P(y)-->P(x))";
(*NOT PROVED*)

writeln"Problem ~~19";
goal IFOL.thy "~~(EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x)))";
(*NOT PROVED*)

writeln"Problem 20";
goal IFOL.thy "(ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))     \
\   --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))";
by (Int.fast_tac 1); 
result();

writeln"Problem 21";
goal IFOL.thy "(EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> ~~(EX x. P<->Q(x))";
(*NOT PROVED*)

writeln"Problem 22";
goal IFOL.thy "(ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))";
by (Int.fast_tac 1); 
result();

writeln"Problem ~~23";
goal IFOL.thy "~~ ((ALL x. P | Q(x))  <->  (P | (ALL x. Q(x))))";
by (Int.best_tac 1);  
result();

writeln"Problem 24";
goal IFOL.thy "~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &  \
\    ~(EX x.P(x)) --> (EX x.Q(x)) & (ALL x. Q(x)|R(x) --> S(x))  \
\   --> (EX x. P(x)&R(x))";
by (Int.fast_tac 1); 
result();

writeln"Problem 25";
goal IFOL.thy "(EX x. P(x)) &  \
\       (ALL x. L(x) --> ~ (M(x) & R(x))) &  \
\       (ALL x. P(x) --> (M(x) & L(x))) &   \
\       ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))  \
\   --> (EX x. Q(x)&P(x))";
by (Int.best_tac 1); 
result();

writeln"Problem ~~26";
goal IFOL.thy "(~~(EX x. p(x)) <-> ~~(EX x. q(x))) &	\
\     (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))	\
\ --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))";
(*NOT PROVED*)

writeln"Problem 27";
goal IFOL.thy "(EX x. P(x) & ~Q(x)) &   \
\             (ALL x. P(x) --> R(x)) &   \
\             (ALL x. M(x) & L(x) --> P(x)) &   \
\             ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))  \
\         --> (ALL x. M(x) --> ~L(x))";
by (Int.fast_tac 1);   (*44 secs*)
result();

writeln"Problem ~~28.  AMENDED";
goal IFOL.thy "(ALL x. P(x) --> (ALL x. Q(x))) &   \
\       (~~(ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &  \
\       (~~(EX x.S(x)) --> (ALL x. L(x) --> M(x)))  \
\   --> (ALL x. P(x) & L(x) --> M(x))";
by (Int.fast_tac 1);  (*101 secs*)
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
goal IFOL.thy "(EX x. P(x)) & (EX y. Q(y))  \
\   --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->     \
\        (ALL x y. P(x) & Q(y) --> R(x) & S(y)))";
by (Int.fast_tac 1); 
result();

writeln"Problem ~~30";
goal IFOL.thy "(ALL x. (P(x) | Q(x)) --> ~ R(x)) & \
\       (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))  \
\   --> (ALL x. ~~S(x))";
by (Int.fast_tac 1);  
result();

writeln"Problem 31";
goal IFOL.thy "~(EX x.P(x) & (Q(x) | R(x))) & \
\       (EX x. L(x) & P(x)) & \
\       (ALL x. ~ R(x) --> M(x))  \
\   --> (EX x. L(x) & M(x))";
by (Int.fast_tac 1);
result();

writeln"Problem 32";
goal IFOL.thy "(ALL x. P(x) & (Q(x)|R(x))-->S(x)) & \
\       (ALL x. S(x) & R(x) --> L(x)) & \
\       (ALL x. M(x) --> R(x))  \
\   --> (ALL x. P(x) & M(x) --> L(x))";
by (Int.best_tac 1);
result();

writeln"Problem ~~33";
goal IFOL.thy "(ALL x. ~~(P(a) & (P(x)-->P(b))-->P(c)))  <->    \
\    (ALL x. ~~((~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c))))";
by (Int.best_tac 1);
result();


writeln"Problem 36";
goal IFOL.thy 
     "(ALL x. EX y. J(x,y)) & \
\     (ALL x. EX y. G(x,y)) & \
\     (ALL x y. J(x,y) | G(x,y) --> (ALL z. J(y,z) | G(y,z) --> H(x,z)))   \
\ --> (ALL x. EX y. H(x,y))";
by (Int.fast_tac 1);  (*35 secs*)
result();

writeln"Problem 37";
goal IFOL.thy
       "(ALL z. EX w. ALL x. EX y. \
\          ~~(P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u.Q(u,w)))) & \
\       (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) & \
\       (~~(EX x y. Q(x,y)) --> (ALL x. R(x,x)))  \
\   --> ~~(ALL x. EX y. R(x,y))";
(*NOT PROVED*)

writeln"Problem 39";
goal IFOL.thy "~ (EX x. ALL y. F(y,x) <-> ~F(y,y))";
by (Int.fast_tac 1);
result();

writeln"Problem 40.  AMENDED";
goal IFOL.thy "(EX y. ALL x. F(x,y) <-> F(x,x)) -->  \
\             ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))";
by (Int.fast_tac 1);
result();

writeln"Problem 44";
goal IFOL.thy "(ALL x. f(x) -->					\
\             (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &   	\
\             (EX x. j(x) & (ALL y. g(y) --> h(x,y)))			\
\             --> (EX x. j(x) & ~f(x))";
by (Int.fast_tac 1);
result();

writeln"Problem 48";
goal IFOL.thy "(a=b | c=d) & (a=c | b=d) --> a=d | b=c";
by (Int.fast_tac 1);
result();

writeln"Problem 51";
goal IFOL.thy
    "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\    (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)";
by (Int.best_tac 1);  (*60 seconds*)
result();

writeln"Problem 52";
(*Almost the same as 51. *)
goal IFOL.thy
    "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\    (EX w. ALL y. EX z. (ALL x. P(x,y) <-> x=z) <-> y=w)";
by (Int.best_tac 1);  (*60 seconds*)
result();

writeln"Problem 56";
goal IFOL.thy
    "(ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))";
by (Int.fast_tac 1);
result();

writeln"Problem 57";
goal IFOL.thy
    "P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) & \
\    (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))";
by (Int.fast_tac 1);
result();

writeln"Problem 60";
goal IFOL.thy
    "ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))";
by (Int.fast_tac 1);
result();

writeln"Reached end of file.";
