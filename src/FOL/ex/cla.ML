(*  Title:      FOL/ex/cla.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Classical First-Order Logic
*)

writeln"File FOL/ex/cla.ML";

context FOL.thy;

open Cla;    (*in case structure IntPr is open!*)

Goal "(P --> Q | R) --> (P-->Q) | (P-->R)";
by (Blast_tac 1);
result();

(*If and only if*)

Goal "(P<->Q) <-> (Q<->P)";
by (Blast_tac 1);
result();

Goal "~ (P <-> ~P)";
by (Blast_tac 1);
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
Goal "(P-->Q)  <->  (~Q --> ~P)";
by (Blast_tac 1);
result();

(*2*)
Goal "~ ~ P  <->  P";
by (Blast_tac 1);
result();

(*3*)
Goal "~(P-->Q) --> (Q-->P)";
by (Blast_tac 1);
result();

(*4*)
Goal "(~P-->Q)  <->  (~Q --> P)";
by (Blast_tac 1);
result();

(*5*)
Goal "((P|Q)-->(P|R)) --> (P|(Q-->R))";
by (Blast_tac 1);
result();

(*6*)
Goal "P | ~ P";
by (Blast_tac 1);
result();

(*7*)
Goal "P | ~ ~ ~ P";
by (Blast_tac 1);
result();

(*8.  Peirce's law*)
Goal "((P-->Q) --> P)  -->  P";
by (Blast_tac 1);
result();

(*9*)
Goal "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (Blast_tac 1);
result();

(*10*)
Goal "(Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P<->Q)";
by (Blast_tac 1);
result();

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
Goal "P<->P";
by (Blast_tac 1);
result();

(*12.  "Dijkstra's law"*)
Goal "((P <-> Q) <-> R)  <->  (P <-> (Q <-> R))";
by (Blast_tac 1);
result();

(*13.  Distributive law*)
Goal "P | (Q & R)  <-> (P | Q) & (P | R)";
by (Blast_tac 1);
result();

(*14*)
Goal "(P <-> Q) <-> ((Q | ~P) & (~Q|P))";
by (Blast_tac 1);
result();

(*15*)
Goal "(P --> Q) <-> (~P | Q)";
by (Blast_tac 1);
result();

(*16*)
Goal "(P-->Q) | (Q-->P)";
by (Blast_tac 1);
result();

(*17*)
Goal "((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S))";
by (Blast_tac 1);
result();

writeln"Classical Logic: examples with quantifiers";

Goal "(ALL x. P(x) & Q(x)) <-> (ALL x. P(x))  &  (ALL x. Q(x))";
by (Blast_tac 1);
result(); 

Goal "(EX x. P-->Q(x))  <->  (P --> (EX x. Q(x)))";
by (Blast_tac 1);
result(); 

Goal "(EX x. P(x)-->Q)  <->  (ALL x. P(x)) --> Q";
by (Blast_tac 1);
result(); 

Goal "(ALL x. P(x)) | Q  <->  (ALL x. P(x) | Q)";
by (Blast_tac 1);
result(); 

(*Discussed in Avron, Gentzen-Type Systems, Resolution and Tableaux,
  JAR 10 (265-281), 1993.  Proof is trivial!*)
Goal "~((EX x.~P(x)) & ((EX x. P(x)) | (EX x. P(x) & Q(x))) & ~ (EX x. P(x)))";
by (Blast_tac 1);
result();

writeln"Problems requiring quantifier duplication";

(*Theorem B of Peter Andrews, Theorem Proving via General Matings, 
  JACM 28 (1981).*)
Goal "(EX x. ALL y. P(x) <-> P(y)) --> ((EX x. P(x)) <-> (ALL y. P(y)))";
by (Blast_tac 1);
result();

(*Needs multiple instantiation of ALL.*)
Goal "(ALL x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))";
by (Blast_tac 1);
result();

(*Needs double instantiation of the quantifier*)
Goal "EX x. P(x) --> P(a) & P(b)";
by (Blast_tac 1);
result();

Goal "EX z. P(z) --> (ALL x. P(x))";
by (Blast_tac 1);
result();

Goal "EX x. (EX y. P(y)) --> P(x)";
by (Blast_tac 1);
result();

(*V. Lifschitz, What Is the Inverse Method?, JAR 5 (1989), 1--23.  NOT PROVED*)
Goal "EX x x'. ALL y. EX z z'. \
\               (~P(y,y) | P(x,x) | ~S(z,x)) & \
\               (S(x,y) | ~S(y,z) | Q(z',z'))  & \
\               (Q(x',y) | ~Q(y,z') | S(x',x'))";



writeln"Hard examples with quantifiers";

writeln"Problem 18";
Goal "EX y. ALL x. P(y)-->P(x)";
by (Blast_tac 1);
result(); 

writeln"Problem 19";
Goal "EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))";
by (Blast_tac 1);
result();

writeln"Problem 20";
Goal "(ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))     \
\   --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))";
by (Blast_tac 1); 
result();

writeln"Problem 21";
Goal "(EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> (EX x. P<->Q(x))";
by (Blast_tac 1);
result();

writeln"Problem 22";
Goal "(ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))";
by (Blast_tac 1); 
result();

writeln"Problem 23";
Goal "(ALL x. P | Q(x))  <->  (P | (ALL x. Q(x)))";
by (Blast_tac 1);  
result();

writeln"Problem 24";
Goal "~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &  \
\     (~(EX x. P(x)) --> (EX x. Q(x))) & (ALL x. Q(x)|R(x) --> S(x))  \
\   --> (EX x. P(x)&R(x))";
by (Blast_tac 1); 
result();

writeln"Problem 25";
Goal "(EX x. P(x)) &  \
\     (ALL x. L(x) --> ~ (M(x) & R(x))) &  \
\     (ALL x. P(x) --> (M(x) & L(x))) &   \
\     ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))  \
\   --> (EX x. Q(x)&P(x))";
by (Blast_tac 1); 
result();

writeln"Problem 26";
Goal "((EX x. p(x)) <-> (EX x. q(x))) & \
\     (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))   \
\ --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))";
by (Blast_tac 1);
result();

writeln"Problem 27";
Goal "(EX x. P(x) & ~Q(x)) &   \
\     (ALL x. P(x) --> R(x)) &   \
\     (ALL x. M(x) & L(x) --> P(x)) &   \
\     ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))  \
\ --> (ALL x. M(x) --> ~L(x))";
by (Blast_tac 1); 
result();

writeln"Problem 28.  AMENDED";
Goal "(ALL x. P(x) --> (ALL x. Q(x))) &   \
\       ((ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &  \
\       ((EX x. S(x)) --> (ALL x. L(x) --> M(x)))  \
\   --> (ALL x. P(x) & L(x) --> M(x))";
by (Blast_tac 1);  
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
Goal "(EX x. P(x)) & (EX y. Q(y))  \
\   --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->     \
\        (ALL x y. P(x) & Q(y) --> R(x) & S(y)))";
by (Blast_tac 1); 
result();

writeln"Problem 30";
Goal "(ALL x. P(x) | Q(x) --> ~ R(x)) & \
\     (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))  \
\   --> (ALL x. S(x))";
by (Blast_tac 1);  
result();

writeln"Problem 31";
Goal "~(EX x. P(x) & (Q(x) | R(x))) & \
\       (EX x. L(x) & P(x)) & \
\       (ALL x. ~ R(x) --> M(x))  \
\   --> (EX x. L(x) & M(x))";
by (Blast_tac 1);
result();

writeln"Problem 32";
Goal "(ALL x. P(x) & (Q(x)|R(x))-->S(x)) & \
\     (ALL x. S(x) & R(x) --> L(x)) & \
\     (ALL x. M(x) --> R(x))  \
\     --> (ALL x. P(x) & M(x) --> L(x))";
by (Blast_tac 1);
result();

writeln"Problem 33";
Goal "(ALL x. P(a) & (P(x)-->P(b))-->P(c))  <->    \
\     (ALL x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))";
by (Blast_tac 1);
result();

writeln"Problem 34  AMENDED (TWICE!!)";
(*Andrews's challenge*)
Goal "((EX x. ALL y. p(x) <-> p(y))  <->                \
\      ((EX x. q(x)) <-> (ALL y. p(y))))     <->        \
\     ((EX x. ALL y. q(x) <-> q(y))  <->                \
\      ((EX x. p(x)) <-> (ALL y. q(y))))";
by (Blast_tac 1);
result();

writeln"Problem 35";
Goal "EX x y. P(x,y) -->  (ALL u v. P(u,v))";
by (Blast_tac 1);
result();

writeln"Problem 36";
Goal "(ALL x. EX y. J(x,y)) & \
\     (ALL x. EX y. G(x,y)) & \
\     (ALL x y. J(x,y) | G(x,y) --> (ALL z. J(y,z) | G(y,z) --> H(x,z)))   \
\ --> (ALL x. EX y. H(x,y))";
by (Blast_tac 1);
result();

writeln"Problem 37";
Goal "(ALL z. EX w. ALL x. EX y. \
\          (P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u. Q(u,w)))) & \
\     (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) & \
\     ((EX x y. Q(x,y)) --> (ALL x. R(x,x)))  \
\     --> (ALL x. EX y. R(x,y))";
by (Blast_tac 1);
result();

writeln"Problem 38";
Goal "(ALL x. p(a) & (p(x) --> (EX y. p(y) & r(x,y))) -->        \
\            (EX z. EX w. p(z) & r(x,w) & r(w,z)))  <->         \
\     (ALL x. (~p(a) | p(x) | (EX z. EX w. p(z) & r(x,w) & r(w,z))) &    \
\             (~p(a) | ~(EX y. p(y) & r(x,y)) |                          \
\             (EX z. EX w. p(z) & r(x,w) & r(w,z))))";
by (Blast_tac 1);  (*beats fast_tac!*)
result();

writeln"Problem 39";
Goal "~ (EX x. ALL y. F(y,x) <-> ~F(y,y))";
by (Blast_tac 1);
result();

writeln"Problem 40.  AMENDED";
Goal "(EX y. ALL x. F(x,y) <-> F(x,x)) -->  \
\             ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))";
by (Blast_tac 1);
result();

writeln"Problem 41";
Goal "(ALL z. EX y. ALL x. f(x,y) <-> f(x,z) & ~ f(x,x))        \
\         --> ~ (EX z. ALL x. f(x,z))";
by (Blast_tac 1);
result();

writeln"Problem 42";
Goal "~ (EX y. ALL x. p(x,y) <-> ~ (EX z. p(x,z) & p(z,x)))";
by (Blast_tac 1);
result();

writeln"Problem 43";
Goal "(ALL x. ALL y. q(x,y) <-> (ALL z. p(z,x) <-> p(z,y)))     \
\         --> (ALL x. ALL y. q(x,y) <-> q(y,x))";
by (Blast_tac 1);
(*Other proofs: Can use Auto_tac(), which cheats by using rewriting!  
  Deepen_tac alone requires 253 secs.  Or
  by (mini_tac 1 THEN Deepen_tac 5 1);
*)
result();

writeln"Problem 44";
Goal "(ALL x. f(x) --> (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y)))) & \
\     (EX x. j(x) & (ALL y. g(y) --> h(x,y)))                   \
\     --> (EX x. j(x) & ~f(x))";
by (Blast_tac 1);
result();

writeln"Problem 45";
Goal "(ALL x. f(x) & (ALL y. g(y) & h(x,y) --> j(x,y))  \
\                     --> (ALL y. g(y) & h(x,y) --> k(y))) &    \
\     ~ (EX y. l(y) & k(y)) &                                   \
\     (EX x. f(x) & (ALL y. h(x,y) --> l(y))                    \
\                 & (ALL y. g(y) & h(x,y) --> j(x,y)))          \
\     --> (EX x. f(x) & ~ (EX y. g(y) & h(x,y)))";
by (Blast_tac 1); 
result();


writeln"Problem 46";
Goal "(ALL x. f(x) & (ALL y. f(y) & h(y,x) --> g(y)) --> g(x)) &      \
\     ((EX x. f(x) & ~g(x)) -->                                    \
\      (EX x. f(x) & ~g(x) & (ALL y. f(y) & ~g(y) --> j(x,y)))) &    \
\     (ALL x y. f(x) & f(y) & h(x,y) --> ~j(y,x))                    \
\      --> (ALL x. f(x) --> g(x))";
by (Blast_tac 1); 
result();


writeln"Problems (mainly) involving equality or functions";

writeln"Problem 48";
Goal "(a=b | c=d) & (a=c | b=d) --> a=d | b=c";
by (Blast_tac 1);
result();

writeln"Problem 49  NOT PROVED AUTOMATICALLY";
(*Hard because it involves substitution for Vars;
  the type constraint ensures that x,y,z have the same type as a,b,u. *)
Goal "(EX x y::'a. ALL z. z=x | z=y) & P(a) & P(b) & a~=b \
\               --> (ALL u::'a. P(u))";
by Safe_tac;
by (res_inst_tac [("x","a")] allE 1);
by (assume_tac 1);
by (res_inst_tac [("x","b")] allE 1);
by (assume_tac 1);
by (Fast_tac 1);    (*Blast_tac's treatment of equality can't do it*)
result();

writeln"Problem 50";  
(*What has this to do with equality?*)
Goal "(ALL x. P(a,x) | (ALL y. P(x,y))) --> (EX x. ALL y. P(x,y))";
by (Blast_tac 1);
result();

writeln"Problem 51";
Goal "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\     (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)";
by (Blast_tac 1);
result();

writeln"Problem 52";
(*Almost the same as 51. *)
Goal "(EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\     (EX w. ALL y. EX z. (ALL x. P(x,y) <-> x=z) <-> y=w)";
by (Blast_tac 1);
result();

writeln"Problem 55";

(*Original, equational version by Len Schubert, via Pelletier *** NOT PROVED
Goal "(EX x. lives(x) & killed(x,agatha)) & \
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
by Safe_tac;
by (dres_inst_tac [("x1","x")] (spec RS mp) 1);
by (assume_tac 1);
by (etac (spec RS exE) 1);
by (REPEAT (etac allE 1));
by (Blast_tac 1);
result();
****)

(*Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  fast_tac DISCOVERS who killed Agatha. *)
Goal "lives(agatha) & lives(butler) & lives(charles) & \
\  (killed(agatha,agatha) | killed(butler,agatha) | killed(charles,agatha)) & \
\  (ALL x y. killed(x,y) --> hates(x,y) & ~richer(x,y)) & \
\  (ALL x. hates(agatha,x) --> ~hates(charles,x)) & \
\  (hates(agatha,agatha) & hates(agatha,charles)) & \
\  (ALL x. lives(x) & ~richer(x,agatha) --> hates(butler,x)) & \
\  (ALL x. hates(agatha,x) --> hates(butler,x)) & \
\  (ALL x. ~hates(x,agatha) | ~hates(x,butler) | ~hates(x,charles)) --> \
\   killed(?who,agatha)";
by (Fast_tac 1);  
  (*MUCH faster than Blast_tac: 1.5s against ??s, mostly proof reconstruction*)
result();


writeln"Problem 56";
Goal "(ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))";
by (Blast_tac 1);
result();

writeln"Problem 57";
Goal "P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) & \
\    (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))";
by (Blast_tac 1);
result();

writeln"Problem 58  NOT PROVED AUTOMATICALLY";
Goal "(ALL x y. f(x)=g(y)) --> (ALL x y. f(f(x))=f(g(y)))";
by (slow_tac (claset() addEs [subst_context]) 1);
result();

writeln"Problem 59";
Goal "(ALL x. P(x) <-> ~P(f(x))) --> (EX x. P(x) & ~P(f(x)))";
by (Blast_tac 1);
result();

writeln"Problem 60";
Goal "ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))";
by (Blast_tac 1);
result();

writeln"Problem 62 as corrected in JAR 18 (1997), page 135";
Goal "(ALL x. p(a) & (p(x) --> p(f(x))) --> p(f(f(x))))  <->     \
\     (ALL x. (~p(a) | p(x) | p(f(f(x)))) &                      \
\             (~p(a) | ~p(f(x)) | p(f(f(x)))))";
by (Blast_tac 1);
result();

(*From Davis, Obvious Logical Inferences, IJCAI-81, 530-531
  Fast_tac indeed copes!*)
Goal "(ALL x. F(x) & ~G(x) --> (EX y. H(x,y) & J(y))) & \
\             (EX x. K(x) & F(x) & (ALL y. H(x,y) --> K(y))) &   \
\             (ALL x. K(x) --> ~G(x))  -->  (EX x. K(x) & J(x))";
by (Fast_tac 1);
result();

(*From Rudnicki, Obvious Inferences, JAR 3 (1987), 383-393.  
  It does seem obvious!*)
Goal "(ALL x. F(x) & ~G(x) --> (EX y. H(x,y) & J(y))) &        \
\     (EX x. K(x) & F(x) & (ALL y. H(x,y) --> K(y)))  &        \
\     (ALL x. K(x) --> ~G(x))   -->   (EX x. K(x) --> ~G(x))";
by (Fast_tac 1);
result();

(*Halting problem: Formulation of Li Dafa (AAR Newsletter 27, Oct 1994.)
	author U. Egly*)
Goal "((EX x. A(x) & (ALL y. C(y) --> (ALL z. D(x,y,z)))) -->               \
\  (EX w. C(w) & (ALL y. C(y) --> (ALL z. D(w,y,z)))))                  \
\ &                                                                     \
\ (ALL w. C(w) & (ALL u. C(u) --> (ALL v. D(w,u,v))) -->                \
\       (ALL y z.                                                       \
\           (C(y) &  P(y,z) --> Q(w,y,z) & OO(w,g)) &                   \
\           (C(y) & ~P(y,z) --> Q(w,y,z) & OO(w,b))))                   \
\ &                                                                     \
\ (ALL w. C(w) &                                                        \
\   (ALL y z.                                                           \
\       (C(y) & P(y,z) --> Q(w,y,z) & OO(w,g)) &                        \
\       (C(y) & ~P(y,z) --> Q(w,y,z) & OO(w,b))) -->                    \
\   (EX v. C(v) &                                                       \
\         (ALL y. ((C(y) & Q(w,y,y)) & OO(w,g) --> ~P(v,y)) &           \
\                 ((C(y) & Q(w,y,y)) & OO(w,b) --> P(v,y) & OO(v,b))))) \
\  -->                  \
\  ~ (EX x. A(x) & (ALL y. C(y) --> (ALL z. D(x,y,z))))";
by (Blast.depth_tac (claset()) 12 1);
result();


(*Halting problem II: credited to M. Bruschi by Li Dafa in JAR 18(1), p.105*)
Goal "((EX x. A(x) & (ALL y. C(y) --> (ALL z. D(x,y,z)))) -->       \
\  (EX w. C(w) & (ALL y. C(y) --> (ALL z. D(w,y,z)))))          \
\ &                                                             \
\ (ALL w. C(w) & (ALL u. C(u) --> (ALL v. D(w,u,v))) -->        \
\       (ALL y z.                                               \
\           (C(y) &  P(y,z) --> Q(w,y,z) & OO(w,g)) &          \
\           (C(y) & ~P(y,z) --> Q(w,y,z) & OO(w,b))))         \
\ &                                                             \
\ ((EX w. C(w) & (ALL y. (C(y) &  P(y,y) --> Q(w,y,y) & OO(w,g)) &\
\                        (C(y) & ~P(y,y) --> Q(w,y,y) & OO(w,b)))) \
\  -->                                                            \
\  (EX v. C(v) & (ALL y. (C(y) &  P(y,y) --> P(v,y) & OO(v,g)) &  \
\                        (C(y) & ~P(y,y) --> P(v,y) & OO(v,b))))) \
\ -->                                                             \
\ ((EX v. C(v) & (ALL y. (C(y) &  P(y,y) --> P(v,y) & OO(v,g)) &  \
\                        (C(y) & ~P(y,y) --> P(v,y) & OO(v,b))))  \
\  -->                                                            \
\  (EX u. C(u) & (ALL y. (C(y) &  P(y,y) --> ~P(u,y)) &    \
\                        (C(y) & ~P(y,y) --> P(u,y) & OO(u,b))))) \
\  -->                                                            \
\  ~ (EX x. A(x) & (ALL y. C(y) --> (ALL z. D(x,y,z))))";
by (Blast.depth_tac(claset()) 7 1);
result();

(* Challenge found on info-hol *)
Goal "ALL x. EX v w. ALL y z. P(x) & Q(y) --> (P(v) | R(w)) & (R(z) --> Q(v))";
by (Blast_tac 1);
result();

writeln"Reached end of file.";

(*Thu Jul 23 1992: loaded in 467s using iffE [on SPARC2] *)
(*Mon Nov 14 1994: loaded in 144s [on SPARC10, with deepen_tac] *)
(*Wed Nov 16 1994: loaded in 138s [after addition of norm_term_skip] *)
(*Mon Nov 21 1994: loaded in 131s [DEPTH_FIRST suppressing repetitions] *)

(*Further runtimes on pochard*)
(*Tue Mar  4 1997: loaded in 93s (version 94-7) *)
(*Tue Mar  4 1997: loaded in 89s*)
(*Thu Apr  3 1997: loaded in 44s--using mostly Blast_tac*)
(*Thu Apr  3 1997: loaded in 96s--addition of two Halting Probs*)
(*Thu Apr  3 1997: loaded in 98s--using lim-1 for all haz rules*)
(*Tue Dec  2 1997: loaded in 107s--added 46; new equalSubst*)
(*Fri Dec 12 1997: loaded in 91s--faster proof reconstruction*)
(*Thu Dec 18 1997: loaded in 94s--two new "obvious theorems" (??)*)

