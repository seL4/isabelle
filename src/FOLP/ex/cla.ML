(*  Title:      FOLP/ex/cla
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Classical First-Order Logic
*)

writeln"File FOL/ex/cla.";

open Cla;    (*in case structure Int is open!*)

goal FOLP.thy "?p : (P --> Q | R) --> (P-->Q) | (P-->R)";
by (fast_tac FOLP_cs 1);
result();

(*If and only if*)

goal FOLP.thy "?p : (P<->Q) <-> (Q<->P)";
by (fast_tac FOLP_cs 1);
result();

goal FOLP.thy "?p : ~ (P <-> ~P)";
by (fast_tac FOLP_cs 1);
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
goal FOLP.thy "?p : (P-->Q)  <->  (~Q --> ~P)";
by (fast_tac FOLP_cs 1);
result();

(*2*)
goal FOLP.thy "?p : ~ ~ P  <->  P";
by (fast_tac FOLP_cs 1);
result();

(*3*)
goal FOLP.thy "?p : ~(P-->Q) --> (Q-->P)";
by (fast_tac FOLP_cs 1);
result();

(*4*)
goal FOLP.thy "?p : (~P-->Q)  <->  (~Q --> P)";
by (fast_tac FOLP_cs 1);
result();

(*5*)
goal FOLP.thy "?p : ((P|Q)-->(P|R)) --> (P|(Q-->R))";
by (fast_tac FOLP_cs 1);
result();

(*6*)
goal FOLP.thy "?p : P | ~ P";
by (fast_tac FOLP_cs 1);
result();

(*7*)
goal FOLP.thy "?p : P | ~ ~ ~ P";
by (fast_tac FOLP_cs 1);
result();

(*8.  Peirce's law*)
goal FOLP.thy "?p : ((P-->Q) --> P)  -->  P";
by (fast_tac FOLP_cs 1);
result();

(*9*)
goal FOLP.thy "?p : ((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (fast_tac FOLP_cs 1);
result();

(*10*)
goal FOLP.thy "?p : (Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P<->Q)";
by (fast_tac FOLP_cs 1);
result();

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
goal FOLP.thy "?p : P<->P";
by (fast_tac FOLP_cs 1);
result();

(*12.  "Dijkstra's law"*)
goal FOLP.thy "?p : ((P <-> Q) <-> R)  <->  (P <-> (Q <-> R))";
by (fast_tac FOLP_cs 1);
result();

(*13.  Distributive law*)
goal FOLP.thy "?p : P | (Q & R)  <-> (P | Q) & (P | R)";
by (fast_tac FOLP_cs 1);
result();

(*14*)
goal FOLP.thy "?p : (P <-> Q) <-> ((Q | ~P) & (~Q|P))";
by (fast_tac FOLP_cs 1);
result();

(*15*)
goal FOLP.thy "?p : (P --> Q) <-> (~P | Q)";
by (fast_tac FOLP_cs 1);
result();

(*16*)
goal FOLP.thy "?p : (P-->Q) | (Q-->P)";
by (fast_tac FOLP_cs 1);
result();

(*17*)
goal FOLP.thy "?p : ((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S))";
by (fast_tac FOLP_cs 1);
result();

writeln"Classical Logic: examples with quantifiers";

goal FOLP.thy "?p : (ALL x. P(x) & Q(x)) <-> (ALL x. P(x))  &  (ALL x. Q(x))";
by (fast_tac FOLP_cs 1);
result(); 

goal FOLP.thy "?p : (EX x. P-->Q(x))  <->  (P --> (EX x.Q(x)))";
by (fast_tac FOLP_cs 1);
result(); 

goal FOLP.thy "?p : (EX x.P(x)-->Q)  <->  (ALL x.P(x)) --> Q";
by (fast_tac FOLP_cs 1);
result(); 

goal FOLP.thy "?p : (ALL x.P(x)) | Q  <->  (ALL x. P(x) | Q)";
by (fast_tac FOLP_cs 1);
result(); 

writeln"Problems requiring quantifier duplication";

(*Needs multiple instantiation of ALL.*)
(*
goal FOLP.thy "?p : (ALL x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))";
by (best_tac FOLP_dup_cs 1);
result();
*)
(*Needs double instantiation of the quantifier*)
goal FOLP.thy "?p : EX x. P(x) --> P(a) & P(b)";
by (best_tac FOLP_dup_cs 1);
result();

goal FOLP.thy "?p : EX z. P(z) --> (ALL x. P(x))";
by (best_tac FOLP_dup_cs 1);
result();


writeln"Hard examples with quantifiers";

writeln"Problem 18";
goal FOLP.thy "?p : EX y. ALL x. P(y)-->P(x)";
by (best_tac FOLP_dup_cs 1);
result(); 

writeln"Problem 19";
goal FOLP.thy "?p : EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))";
by (best_tac FOLP_dup_cs 1);
result();

writeln"Problem 20";
goal FOLP.thy "?p : (ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))     \
\   --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))";
by (fast_tac FOLP_cs 1); 
result();
(*
writeln"Problem 21";
goal FOLP.thy "?p : (EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> (EX x. P<->Q(x))";
by (best_tac FOLP_dup_cs 1);
result();
*)
writeln"Problem 22";
goal FOLP.thy "?p : (ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))";
by (fast_tac FOLP_cs 1); 
result();

writeln"Problem 23";
goal FOLP.thy "?p : (ALL x. P | Q(x))  <->  (P | (ALL x. Q(x)))";
by (best_tac FOLP_cs 1);  
result();

writeln"Problem 24";
goal FOLP.thy "?p : ~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &  \
\    ~(EX x.P(x)) --> (EX x.Q(x)) & (ALL x. Q(x)|R(x) --> S(x))  \
\   --> (EX x. P(x)&R(x))";
by (fast_tac FOLP_cs 1); 
result();
(*
writeln"Problem 25";
goal FOLP.thy "?p : (EX x. P(x)) &  \
\       (ALL x. L(x) --> ~ (M(x) & R(x))) &  \
\       (ALL x. P(x) --> (M(x) & L(x))) &   \
\       ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))  \
\   --> (EX x. Q(x)&P(x))";
by (best_tac FOLP_cs 1); 
result();

writeln"Problem 26";
goal FOLP.thy "?u : ((EX x. p(x)) <-> (EX x. q(x))) &   \
\     (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))   \
\ --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))";
by (fast_tac FOLP_cs 1);
result();
*)
writeln"Problem 27";
goal FOLP.thy "?p : (EX x. P(x) & ~Q(x)) &   \
\             (ALL x. P(x) --> R(x)) &   \
\             (ALL x. M(x) & L(x) --> P(x)) &   \
\             ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))  \
\         --> (ALL x. M(x) --> ~L(x))";
by (fast_tac FOLP_cs 1); 
result();

writeln"Problem 28.  AMENDED";
goal FOLP.thy "?p : (ALL x. P(x) --> (ALL x. Q(x))) &   \
\       ((ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &  \
\       ((EX x.S(x)) --> (ALL x. L(x) --> M(x)))  \
\   --> (ALL x. P(x) & L(x) --> M(x))";
by (fast_tac FOLP_cs 1);  
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
goal FOLP.thy "?p : (EX x. P(x)) & (EX y. Q(y))  \
\   --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->     \
\        (ALL x y. P(x) & Q(y) --> R(x) & S(y)))";
by (fast_tac FOLP_cs 1); 
result();

writeln"Problem 30";
goal FOLP.thy "?p : (ALL x. P(x) | Q(x) --> ~ R(x)) & \
\       (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))  \
\   --> (ALL x. S(x))";
by (fast_tac FOLP_cs 1);  
result();

writeln"Problem 31";
goal FOLP.thy "?p : ~(EX x.P(x) & (Q(x) | R(x))) & \
\       (EX x. L(x) & P(x)) & \
\       (ALL x. ~ R(x) --> M(x))  \
\   --> (EX x. L(x) & M(x))";
by (fast_tac FOLP_cs 1);
result();

writeln"Problem 32";
goal FOLP.thy "?p : (ALL x. P(x) & (Q(x)|R(x))-->S(x)) & \
\       (ALL x. S(x) & R(x) --> L(x)) & \
\       (ALL x. M(x) --> R(x))  \
\   --> (ALL x. P(x) & M(x) --> L(x))";
by (best_tac FOLP_cs 1);
result();

writeln"Problem 33";
goal FOLP.thy "?p : (ALL x. P(a) & (P(x)-->P(b))-->P(c))  <->    \
\    (ALL x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))";
by (best_tac FOLP_cs 1);
result();

writeln"Problem 35";
goal FOLP.thy "?p : EX x y. P(x,y) -->  (ALL u v. P(u,v))";
by (best_tac FOLP_dup_cs 1);
result();

writeln"Problem 36";
goal FOLP.thy
"?p : (ALL x. EX y. J(x,y)) & \
\     (ALL x. EX y. G(x,y)) & \
\     (ALL x y. J(x,y) | G(x,y) --> (ALL z. J(y,z) | G(y,z) --> H(x,z)))   \
\ --> (ALL x. EX y. H(x,y))";
by (fast_tac FOLP_cs 1);
result();

writeln"Problem 37";
goal FOLP.thy "?p : (ALL z. EX w. ALL x. EX y. \
\          (P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u.Q(u,w)))) & \
\       (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) & \
\       ((EX x y. Q(x,y)) --> (ALL x. R(x,x)))  \
\   --> (ALL x. EX y. R(x,y))";
by (fast_tac FOLP_cs 1);
result();

writeln"Problem 39";
goal FOLP.thy "?p : ~ (EX x. ALL y. F(y,x) <-> ~F(y,y))";
by (fast_tac FOLP_cs 1);
result();

writeln"Problem 40.  AMENDED";
goal FOLP.thy "?p : (EX y. ALL x. F(x,y) <-> F(x,x)) -->  \
\             ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))";
by (fast_tac FOLP_cs 1);
result();

writeln"Problem 41";
goal FOLP.thy "?p : (ALL z. EX y. ALL x. f(x,y) <-> f(x,z) & ~ f(x,x))  \
\         --> ~ (EX z. ALL x. f(x,z))";
by (best_tac FOLP_cs 1);
result();

writeln"Problem 44";
goal FOLP.thy "?p : (ALL x. f(x) -->                                    \
\             (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &       \
\             (EX x. j(x) & (ALL y. g(y) --> h(x,y)))                   \
\             --> (EX x. j(x) & ~f(x))";
by (fast_tac FOLP_cs 1);
result();

writeln"Problems (mainly) involving equality or functions";

writeln"Problem 48";
goal FOLP.thy "?p : (a=b | c=d) & (a=c | b=d) --> a=d | b=c";
by (fast_tac FOLP_cs 1);
result();

writeln"Problem 50";  
(*What has this to do with equality?*)
goal FOLP.thy "?p : (ALL x. P(a,x) | (ALL y.P(x,y))) --> (EX x. ALL y.P(x,y))";
by (best_tac FOLP_dup_cs 1);
result();

writeln"Problem 56";
goal FOLP.thy
 "?p : (ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))";
by (fast_tac FOLP_cs 1);
result();

writeln"Problem 57";
goal FOLP.thy
"?p : P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) & \
\     (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))";
by (fast_tac FOLP_cs 1);
result();

writeln"Problem 58  NOT PROVED AUTOMATICALLY";
goal FOLP.thy "?p : (ALL x y. f(x)=g(y)) --> (ALL x y. f(f(x))=f(g(y)))";
val f_cong = read_instantiate [("t","f")] subst_context;
by (fast_tac (FOLP_cs addIs [f_cong]) 1);
result();

writeln"Problem 59";
goal FOLP.thy "?p : (ALL x. P(x) <-> ~P(f(x))) --> (EX x. P(x) & ~P(f(x)))";
by (best_tac FOLP_dup_cs 1);
result();

writeln"Problem 60";
goal FOLP.thy
"?p : ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))";
by (fast_tac FOLP_cs 1);
result();

writeln"Reached end of file.";
