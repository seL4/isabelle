(*  Title:      FOL/ex/cla.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Classical First-Order Logic
*)

writeln"File FOL/ex/cla.ML";

open Cla;    (*in case structure Int is open!*)

goal FOL.thy "(P --> Q | R) --> (P-->Q) | (P-->R)";
by (Fast_tac 1);
result();

(*If and only if*)

goal FOL.thy "(P<->Q) <-> (Q<->P)";
by (Fast_tac 1);
result();

goal FOL.thy "~ (P <-> ~P)";
by (Fast_tac 1);
result();


(*Sample problems from 
  F. J. Pelletier, 
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.

The hardest problems -- judging by experience with several theorem provers,
including matrix ones -- are 34 and 43.
*)

writeln"Pelletier's examples";
(*1*)
goal FOL.thy "(P-->Q)  <->  (~Q --> ~P)";
by (Fast_tac 1);
result();

(*2*)
goal FOL.thy "~ ~ P  <->  P";
by (Fast_tac 1);
result();

(*3*)
goal FOL.thy "~(P-->Q) --> (Q-->P)";
by (Fast_tac 1);
result();

(*4*)
goal FOL.thy "(~P-->Q)  <->  (~Q --> P)";
by (Fast_tac 1);
result();

(*5*)
goal FOL.thy "((P|Q)-->(P|R)) --> (P|(Q-->R))";
by (Fast_tac 1);
result();

(*6*)
goal FOL.thy "P | ~ P";
by (Fast_tac 1);
result();

(*7*)
goal FOL.thy "P | ~ ~ ~ P";
by (Fast_tac 1);
result();

(*8.  Peirce's law*)
goal FOL.thy "((P-->Q) --> P)  -->  P";
by (Fast_tac 1);
result();

(*9*)
goal FOL.thy "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (Fast_tac 1);
result();

(*10*)
goal FOL.thy "(Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P<->Q)";
by (Fast_tac 1);
result();

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
goal FOL.thy "P<->P";
by (Fast_tac 1);
result();

(*12.  "Dijkstra's law"*)
goal FOL.thy "((P <-> Q) <-> R)  <->  (P <-> (Q <-> R))";
by (Fast_tac 1);
result();

(*13.  Distributive law*)
goal FOL.thy "P | (Q & R)  <-> (P | Q) & (P | R)";
by (Fast_tac 1);
result();

(*14*)
goal FOL.thy "(P <-> Q) <-> ((Q | ~P) & (~Q|P))";
by (Fast_tac 1);
result();

(*15*)
goal FOL.thy "(P --> Q) <-> (~P | Q)";
by (Fast_tac 1);
result();

(*16*)
goal FOL.thy "(P-->Q) | (Q-->P)";
by (Fast_tac 1);
result();

(*17*)
goal FOL.thy "((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S))";
by (Fast_tac 1);
result();

writeln"Classical Logic: examples with quantifiers";

goal FOL.thy "(ALL x. P(x) & Q(x)) <-> (ALL x. P(x))  &  (ALL x. Q(x))";
by (Fast_tac 1);
result(); 

goal FOL.thy "(EX x. P-->Q(x))  <->  (P --> (EX x.Q(x)))";
by (Fast_tac 1);
result(); 

goal FOL.thy "(EX x.P(x)-->Q)  <->  (ALL x.P(x)) --> Q";
by (Fast_tac 1);
result(); 

goal FOL.thy "(ALL x.P(x)) | Q  <->  (ALL x. P(x) | Q)";
by (Fast_tac 1);
result(); 

(*Discussed in Avron, Gentzen-Type Systems, Resolution and Tableaux,
  JAR 10 (265-281), 1993.  Proof is trivial!*)
goal FOL.thy
    "~ ((EX x.~P(x)) & ((EX x.P(x)) | (EX x.P(x) & Q(x))) & ~ (EX x.P(x)))";
by (Fast_tac 1);
result();

writeln"Problems requiring quantifier duplication";

(*Needs multiple instantiation of ALL.*)
goal FOL.thy "(ALL x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))";
by (Deepen_tac 0 1);
result();

(*Needs double instantiation of the quantifier*)
goal FOL.thy "EX x. P(x) --> P(a) & P(b)";
by (Deepen_tac 0 1);
result();

goal FOL.thy "EX z. P(z) --> (ALL x. P(x))";
by (Deepen_tac 0 1);
result();

goal FOL.thy "EX x. (EX y. P(y)) --> P(x)";
by (Deepen_tac 0 1);
result();

(*V. Lifschitz, What Is the Inverse Method?, JAR 5 (1989), 1--23.  NOT PROVED*)
goal FOL.thy "EX x x'. ALL y. EX z z'. \
\               (~P(y,y) | P(x,x) | ~S(z,x)) & \
\               (S(x,y) | ~S(y,z) | Q(z',z'))  & \
\               (Q(x',y) | ~Q(y,z') | S(x',x'))";

writeln"Hard examples with quantifiers";

writeln"Problem 18";
goal FOL.thy "EX y. ALL x. P(y)-->P(x)";
by (Deepen_tac 0 1);
result(); 

writeln"Problem 19";
goal FOL.thy "EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))";
by (Deepen_tac 0 1);
result();

writeln"Problem 20";
goal FOL.thy "(ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))     \
\   --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))";
by (Fast_tac 1); 
result();

writeln"Problem 21";
goal FOL.thy "(EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> (EX x. P<->Q(x))";
by (Deepen_tac 0 1);
result();

writeln"Problem 22";
goal FOL.thy "(ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))";
by (Fast_tac 1); 
result();

writeln"Problem 23";
goal FOL.thy "(ALL x. P | Q(x))  <->  (P | (ALL x. Q(x)))";
by (Best_tac 1);  
result();

writeln"Problem 24";
goal FOL.thy "~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &  \
\    ~(EX x.P(x)) --> (EX x.Q(x)) & (ALL x. Q(x)|R(x) --> S(x))  \
\   --> (EX x. P(x)&R(x))";
by (Fast_tac 1); 
result();

writeln"Problem 25";
goal FOL.thy "(EX x. P(x)) &  \
\       (ALL x. L(x) --> ~ (M(x) & R(x))) &  \
\       (ALL x. P(x) --> (M(x) & L(x))) &   \
\       ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))  \
\   --> (EX x. Q(x)&P(x))";
by (Best_tac 1); 
result();

writeln"Problem 26";
goal FOL.thy "((EX x. p(x)) <-> (EX x. q(x))) & \
\     (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))   \
\ --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))";
by (Fast_tac 1);
result();

writeln"Problem 27";
goal FOL.thy "(EX x. P(x) & ~Q(x)) &   \
\             (ALL x. P(x) --> R(x)) &   \
\             (ALL x. M(x) & L(x) --> P(x)) &   \
\             ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))  \
\         --> (ALL x. M(x) --> ~L(x))";
by (Fast_tac 1); 
result();

writeln"Problem 28.  AMENDED";
goal FOL.thy "(ALL x. P(x) --> (ALL x. Q(x))) &   \
\       ((ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &  \
\       ((EX x.S(x)) --> (ALL x. L(x) --> M(x)))  \
\   --> (ALL x. P(x) & L(x) --> M(x))";
by (Fast_tac 1);  
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
goal FOL.thy "(EX x. P(x)) & (EX y. Q(y))  \
\   --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->     \
\        (ALL x y. P(x) & Q(y) --> R(x) & S(y)))";
by (Fast_tac 1); 
result();

writeln"Problem 30";
goal FOL.thy "(ALL x. P(x) | Q(x) --> ~ R(x)) & \
\       (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))  \
\   --> (ALL x. S(x))";
by (Fast_tac 1);  
result();

writeln"Problem 31";
goal FOL.thy "~(EX x.P(x) & (Q(x) | R(x))) & \
\       (EX x. L(x) & P(x)) & \
\       (ALL x. ~ R(x) --> M(x))  \
\   --> (EX x. L(x) & M(x))";
by (Fast_tac 1);
result();

writeln"Problem 32";
goal FOL.thy "(ALL x. P(x) & (Q(x)|R(x))-->S(x)) & \
\       (ALL x. S(x) & R(x) --> L(x)) & \
\       (ALL x. M(x) --> R(x))  \
\   --> (ALL x. P(x) & M(x) --> L(x))";
by (Best_tac 1);
result();

writeln"Problem 33";
goal FOL.thy "(ALL x. P(a) & (P(x)-->P(b))-->P(c))  <->    \
\    (ALL x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))";
by (Best_tac 1);
result();

writeln"Problem 34  AMENDED (TWICE!!)";
(*Andrews's challenge*)
goal FOL.thy "((EX x. ALL y. p(x) <-> p(y))  <->                \
\              ((EX x. q(x)) <-> (ALL y. p(y))))     <->        \
\             ((EX x. ALL y. q(x) <-> q(y))  <->                \
\              ((EX x. p(x)) <-> (ALL y. q(y))))";
by (Deepen_tac 0 1);
result();

writeln"Problem 35";
goal FOL.thy "EX x y. P(x,y) -->  (ALL u v. P(u,v))";
by (mini_tac 1);
by (Fast_tac 1);
(*Without miniscope, would have to use deepen_tac; would be slower*)
result();

writeln"Problem 36";
goal FOL.thy
     "(ALL x. EX y. J(x,y)) & \
\     (ALL x. EX y. G(x,y)) & \
\     (ALL x y. J(x,y) | G(x,y) --> (ALL z. J(y,z) | G(y,z) --> H(x,z)))   \
\ --> (ALL x. EX y. H(x,y))";
by (Fast_tac 1);
result();

writeln"Problem 37";
goal FOL.thy "(ALL z. EX w. ALL x. EX y. \
\          (P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u.Q(u,w)))) & \
\       (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) & \
\       ((EX x y. Q(x,y)) --> (ALL x. R(x,x)))  \
\   --> (ALL x. EX y. R(x,y))";
by (Fast_tac 1);
result();

writeln"Problem 38";
goal FOL.thy
    "(ALL x. p(a) & (p(x) --> (EX y. p(y) & r(x,y))) -->        \
\            (EX z. EX w. p(z) & r(x,w) & r(w,z)))  <->         \
\    (ALL x. (~p(a) | p(x) | (EX z. EX w. p(z) & r(x,w) & r(w,z))) &    \
\            (~p(a) | ~(EX y. p(y) & r(x,y)) |                          \
\             (EX z. EX w. p(z) & r(x,w) & r(w,z))))";
by (Deepen_tac 0 1);  (*beats fast_tac!*)
result();

writeln"Problem 39";
goal FOL.thy "~ (EX x. ALL y. F(y,x) <-> ~F(y,y))";
by (Fast_tac 1);
result();

writeln"Problem 40.  AMENDED";
goal FOL.thy "(EX y. ALL x. F(x,y) <-> F(x,x)) -->  \
\             ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))";
by (Fast_tac 1);
result();

writeln"Problem 41";
goal FOL.thy "(ALL z. EX y. ALL x. f(x,y) <-> f(x,z) & ~ f(x,x))        \
\         --> ~ (EX z. ALL x. f(x,z))";
by (Fast_tac 1);
result();

writeln"Problem 42";
goal FOL.thy "~ (EX y. ALL x. p(x,y) <-> ~ (EX z. p(x,z) & p(z,x)))";
by (Deepen_tac 0 1);
result();

writeln"Problem 43";
goal FOL.thy "(ALL x. ALL y. q(x,y) <-> (ALL z. p(z,x) <-> p(z,y)))     \
\         --> (ALL x. ALL y. q(x,y) <-> q(y,x))";
by (Auto_tac());
(*The proof above cheats by using rewriting!  A purely logical proof is
  by (mini_tac 1 THEN Deepen_tac 5 1);
Can use just deepen_tac but it requires 253 secs?!?
  by (Deepen_tac 0 1);     
*)
result();

writeln"Problem 44";
goal FOL.thy "(ALL x. f(x) -->                                          \
\             (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &       \
\             (EX x. j(x) & (ALL y. g(y) --> h(x,y)))                   \
\             --> (EX x. j(x) & ~f(x))";
by (Fast_tac 1);
result();

writeln"Problem 45";
goal FOL.thy "(ALL x. f(x) & (ALL y. g(y) & h(x,y) --> j(x,y))  \
\                     --> (ALL y. g(y) & h(x,y) --> k(y))) &    \
\     ~ (EX y. l(y) & k(y)) &                                   \
\     (EX x. f(x) & (ALL y. h(x,y) --> l(y))                    \
\                 & (ALL y. g(y) & h(x,y) --> j(x,y)))          \
\     --> (EX x. f(x) & ~ (EX y. g(y) & h(x,y)))";
by (Best_tac 1); 
result();


writeln"Problems (mainly) involving equality or functions";

writeln"Problem 48";
goal FOL.thy "(a=b | c=d) & (a=c | b=d) --> a=d | b=c";
by (Fast_tac 1);
result();

writeln"Problem 49  NOT PROVED AUTOMATICALLY";
(*Hard because it involves substitution for Vars;
  the type constraint ensures that x,y,z have the same type as a,b,u. *)
goal FOL.thy "(EX x y::'a. ALL z. z=x | z=y) & P(a) & P(b) & a~=b \
\               --> (ALL u::'a.P(u))";
by (Step_tac 1);
by (res_inst_tac [("x","a")] allE 1);
by (assume_tac 1);
by (res_inst_tac [("x","b")] allE 1);
by (assume_tac 1);
by (Fast_tac 1);
result();

writeln"Problem 50";  
(*What has this to do with equality?*)
goal FOL.thy "(ALL x. P(a,x) | (ALL y.P(x,y))) --> (EX x. ALL y.P(x,y))";
by (mini_tac 1);
by (Deepen_tac 0 1);
result();

writeln"Problem 51";
goal FOL.thy
    "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\    (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)";
by (Fast_tac 1);
result();

writeln"Problem 52";
(*Almost the same as 51. *)
goal FOL.thy
    "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\    (EX w. ALL y. EX z. (ALL x. P(x,y) <-> x=z) <-> y=w)";
by (Best_tac 1);
result();

writeln"Problem 55";

(*Original, equational version by Len Schubert, via Pelletier *** NOT PROVED
goal FOL.thy
  "(EX x. lives(x) & killed(x,agatha)) & \
\  lives(agatha) & lives(butler) & lives(charles) & \
\  (ALL x. lives(x) --> x=agatha | x=butler | x=charles) & \
\  (ALL x y. killed(x,y) --> hates(x,y)) & \
\  (ALL x y. killed(x,y) --> ~richer(x,y)) & \
\  (ALL x. hates(agatha,x) --> ~hates(charles,x)) & \
\  (ALL x. ~ x=butler --> hates(agatha,x)) & \
\  (ALL x. ~richer(x,agatha) --> hates(butler,x)) & \
\  (ALL x. hates(agatha,x) --> hates(butler,x)) & \
\  (ALL x. EX y. ~hates(x,y)) & \
\  ~ agatha=butler --> \
\  killed(?who,agatha)";
by (Step_tac 1);
by (dres_inst_tac [("x1","x")] (spec RS mp) 1);
by (assume_tac 1);
by (etac (spec RS exE) 1);
by (REPEAT (etac allE 1));
by (Fast_tac 1);
result();
****)

(*Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  fast_tac DISCOVERS who killed Agatha. *)
goal FOL.thy "lives(agatha) & lives(butler) & lives(charles) & \
\  (killed(agatha,agatha) | killed(butler,agatha) | killed(charles,agatha)) & \
\  (ALL x y. killed(x,y) --> hates(x,y) & ~richer(x,y)) & \
\  (ALL x. hates(agatha,x) --> ~hates(charles,x)) & \
\  (hates(agatha,agatha) & hates(agatha,charles)) & \
\  (ALL x. lives(x) & ~richer(x,agatha) --> hates(butler,x)) & \
\  (ALL x. hates(agatha,x) --> hates(butler,x)) & \
\  (ALL x. ~hates(x,agatha) | ~hates(x,butler) | ~hates(x,charles)) --> \
\   killed(?who,agatha)";
by (Fast_tac 1);
result();


writeln"Problem 56";
goal FOL.thy
    "(ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))";
by (Fast_tac 1);
result();

writeln"Problem 57";
goal FOL.thy
    "P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) & \
\    (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))";
by (Fast_tac 1);
result();

writeln"Problem 58  NOT PROVED AUTOMATICALLY";
goal FOL.thy "(ALL x y. f(x)=g(y)) --> (ALL x y. f(f(x))=f(g(y)))";
by (slow_tac (!claset addEs [subst_context]) 1);
result();

writeln"Problem 59";
goal FOL.thy "(ALL x. P(x) <-> ~P(f(x))) --> (EX x. P(x) & ~P(f(x)))";
by (Deepen_tac 0 1);
result();

writeln"Problem 60";
goal FOL.thy
    "ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))";
by (Fast_tac 1);
result();

writeln"Problem 62 as corrected in AAR newletter #31";
goal FOL.thy
    "(ALL x. p(a) & (p(x) --> p(f(x))) --> p(f(f(x))))  <->     \
\    (ALL x. (~p(a) | p(x) | p(f(f(x)))) &                      \
\            (~p(a) | ~p(f(x)) | p(f(f(x)))))";
by (Fast_tac 1);
result();

(*Halting problem: Formulation of Li Dafa (AAR Newsletter 27, Oct 1994.)
	author U. Egly*)
goal FOL.thy
"((EX X. a(X) & (ALL Y. c(Y) --> (ALL Z. d(X, Y, Z)))) -->  \
\  (EX W. c(W) & (ALL Y. c(Y) --> (ALL Z. d(W, Y, Z)))))     \
\ &                                                          \
\ (ALL W. c(W) & (ALL U. c(U) --> (ALL V. d(W, U, V))) -->       \
\       (ALL Y Z.                                               \
\           (c(Y) & h2(Y, Z) --> h3(W, Y, Z) & o(W, g)) &       \
\           (c(Y) & ~h2(Y, Z) --> h3(W, Y, Z) & o(W, b))))  \
\ &                    \
\ (ALL W. c(W) &       \
\   (ALL Y Z.          \
\       (c(Y) & h2(Y, Z) --> h3(W, Y, Z) & o(W, g)) &       \
\       (c(Y) & ~h2(Y, Z) --> h3(W, Y, Z) & o(W, b))) -->       \
\   (EX V. c(V) &       \
\         (ALL Y. ((c(Y) & h3(W, Y, Y)) & o(W, g) --> ~h2(V, Y)) &       \
\                 ((c(Y) & h3(W, Y, Y)) & o(W, b) --> h2(V, Y) & o(V, b))))) \
\  -->                  \
\  ~ (EX X. a(X) & (ALL Y. c(Y) --> (ALL Z. d(X, Y, Z))))";


writeln"Reached end of file.";

(*Thu Jul 23 1992: loaded in 467s using iffE [on SPARC2] *)
(*Mon Nov 14 1994: loaded in 144s [on SPARC10, with deepen_tac] *)
(*Wed Nov 16 1994: loaded in 138s [after addition of norm_term_skip] *)
(*Mon Nov 21 1994: loaded in 131s [DEPTH_FIRST suppressing repetitions] *)

