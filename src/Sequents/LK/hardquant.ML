(*  Title:      LK/ex/hard-quant
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Hard examples with quantifiers.  Can be read to test the LK system.
From  F. J. Pelletier,
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.

Uses pc_tac rather than fast_tac when the former is significantly faster.
*)

writeln"File LK/ex/hard-quant.";

context LK.thy;

Goal "|- (ALL x. P(x) & Q(x)) <-> (ALL x. P(x))  &  (ALL x. Q(x))";
by (Fast_tac 1);
result(); 

Goal "|- (EX x. P-->Q(x))  <->  (P --> (EX x. Q(x)))";
by (Fast_tac 1);
result(); 

Goal "|- (EX x. P(x)-->Q)  <->  (ALL x. P(x)) --> Q";
by (Fast_tac 1);
result(); 

Goal "|- (ALL x. P(x)) | Q  <->  (ALL x. P(x) | Q)";
by (Fast_tac 1);
result(); 

writeln"Problems requiring quantifier duplication";

(*Not provable by Fast_tac: needs multiple instantiation of ALL*)
Goal "|- (ALL x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))";
by (best_tac LK_dup_pack 1);
result();

(*Needs double instantiation of the quantifier*)
Goal "|- EX x. P(x) --> P(a) & P(b)";
by (fast_tac LK_dup_pack 1);
result();

Goal "|- EX z. P(z) --> (ALL x. P(x))";
by (best_tac LK_dup_pack 1);
result();

writeln"Hard examples with quantifiers";

writeln"Problem 18";
Goal "|- EX y. ALL x. P(y)-->P(x)";
by (best_tac LK_dup_pack 1);
result(); 

writeln"Problem 19";
Goal "|- EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))";
by (best_tac LK_dup_pack 1);
result();

writeln"Problem 20";
Goal "|- (ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))     \
\   --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))";
by (Fast_tac 1); 
result();

writeln"Problem 21";
Goal "|- (EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> (EX x. P<->Q(x))";
by (best_tac LK_dup_pack 1);
result();

writeln"Problem 22";
Goal "|- (ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))";
by (Fast_tac 1); 
result();

writeln"Problem 23";
Goal "|- (ALL x. P | Q(x))  <->  (P | (ALL x. Q(x)))";
by (best_tac LK_pack 1);  
result();

writeln"Problem 24";
Goal "|- ~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &  \
\    ~(EX x. P(x)) --> (EX x. Q(x)) & (ALL x. Q(x)|R(x) --> S(x))  \
\   --> (EX x. P(x)&R(x))";
by (pc_tac LK_pack 1);
result();

writeln"Problem 25";
Goal "|- (EX x. P(x)) &  \
\       (ALL x. L(x) --> ~ (M(x) & R(x))) &  \
\       (ALL x. P(x) --> (M(x) & L(x))) &   \
\       ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))  \
\   --> (EX x. Q(x)&P(x))";
by (best_tac LK_pack 1);  
result();

writeln"Problem 26";
Goal "|- ((EX x. p(x)) <-> (EX x. q(x))) &       \
\     (ALL x. ALL y. p(x) & q(y) --> (r(x) <-> s(y)))   \
\ --> ((ALL x. p(x)-->r(x)) <-> (ALL x. q(x)-->s(x)))";
by (pc_tac LK_pack 1);
result();

writeln"Problem 27";
Goal "|- (EX x. P(x) & ~Q(x)) &   \
\             (ALL x. P(x) --> R(x)) &   \
\             (ALL x. M(x) & L(x) --> P(x)) &   \
\             ((EX x. R(x) & ~ Q(x)) --> (ALL x. L(x) --> ~ R(x)))  \
\         --> (ALL x. M(x) --> ~L(x))";
by (pc_tac LK_pack 1); 
result();

writeln"Problem 28.  AMENDED";
Goal "|- (ALL x. P(x) --> (ALL x. Q(x))) &   \
\       ((ALL x. Q(x)|R(x)) --> (EX x. Q(x)&S(x))) &  \
\       ((EX x. S(x)) --> (ALL x. L(x) --> M(x)))  \
\   --> (ALL x. P(x) & L(x) --> M(x))";
by (pc_tac LK_pack 1);  
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
Goal "|- (EX x. P(x)) & (EX y. Q(y))  \
\   --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->     \
\        (ALL x y. P(x) & Q(y) --> R(x) & S(y)))";
by (pc_tac LK_pack 1); 
result();

writeln"Problem 30";
Goal "|- (ALL x. P(x) | Q(x) --> ~ R(x)) & \
\       (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))  \
\   --> (ALL x. S(x))";
by (Fast_tac 1);  
result();

writeln"Problem 31";
Goal "|- ~(EX x. P(x) & (Q(x) | R(x))) & \
\       (EX x. L(x) & P(x)) & \
\       (ALL x. ~ R(x) --> M(x))  \
\   --> (EX x. L(x) & M(x))";
by (Fast_tac 1);
result();

writeln"Problem 32";
Goal "|- (ALL x. P(x) & (Q(x)|R(x))-->S(x)) & \
\       (ALL x. S(x) & R(x) --> L(x)) & \
\       (ALL x. M(x) --> R(x))  \
\   --> (ALL x. P(x) & M(x) --> L(x))";
by (best_tac LK_pack 1);
result();

writeln"Problem 33";
Goal "|- (ALL x. P(a) & (P(x)-->P(b))-->P(c))  <->    \
\    (ALL x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))";
by (Fast_tac 1);
result();

writeln"Problem 34  AMENDED (TWICE!!)";
(*Andrews's challenge*)
Goal "|- ((EX x. ALL y. p(x) <-> p(y))  <->              \
\              ((EX x. q(x)) <-> (ALL y. p(y))))     <->        \
\             ((EX x. ALL y. q(x) <-> q(y))  <->                \
\              ((EX x. p(x)) <-> (ALL y. q(y))))";
by (best_tac LK_dup_pack 1); (*10 secs!*)
result();


writeln"Problem 35";
Goal "|- EX x y. P(x,y) -->  (ALL u v. P(u,v))";
by (best_tac LK_dup_pack 1);
result();

writeln"Problem 36";
Goal "|- (ALL x. EX y. J(x,y)) & \
\        (ALL x. EX y. G(x,y)) & \
\        (ALL x y. J(x,y) | G(x,y) -->   \
\        (ALL z. J(y,z) | G(y,z) --> H(x,z)))   \
\        --> (ALL x. EX y. H(x,y))";
by (Fast_tac 1);
result();

writeln"Problem 37";
Goal "|- (ALL z. EX w. ALL x. EX y. \
\          (P(x,z)-->P(y,w)) & P(y,z) & (P(y,w) --> (EX u. Q(u,w)))) & \
\       (ALL x z. ~P(x,z) --> (EX y. Q(y,z))) & \
\       ((EX x y. Q(x,y)) --> (ALL x. R(x,x)))  \
\   --> (ALL x. EX y. R(x,y))";
by (pc_tac LK_pack 1);
result();

writeln"Problem 38";
Goal "|- (ALL x. p(a) & (p(x) --> (EX y. p(y) & r(x,y))) -->        \
\                (EX z. EX w. p(z) & r(x,w) & r(w,z)))  <->         \
\        (ALL x. (~p(a) | p(x) | (EX z. EX w. p(z) & r(x,w) & r(w,z))) &    \
\                (~p(a) | ~(EX y. p(y) & r(x,y)) |                          \
\                (EX z. EX w. p(z) & r(x,w) & r(w,z))))";
by (pc_tac LK_pack 1);
result();

writeln"Problem 39";
Goal "|- ~ (EX x. ALL y. F(y,x) <-> ~F(y,y))";
by (Fast_tac 1);
result();

writeln"Problem 40.  AMENDED";
Goal "|- (EX y. ALL x. F(x,y) <-> F(x,x)) -->  \
\        ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))";
by (Fast_tac 1);
result();

writeln"Problem 41";
Goal "|- (ALL z. EX y. ALL x. f(x,y) <-> f(x,z) & ~ f(x,x))      \
\        --> ~ (EX z. ALL x. f(x,z))";
by (Fast_tac 1);
result();

writeln"Problem 42";
Goal "|- ~ (EX y. ALL x. p(x,y) <-> ~ (EX z. p(x,z) & p(z,x)))";

writeln"Problem 43  NOT PROVED AUTOMATICALLY";
Goal "|- (ALL x. ALL y. q(x,y) <-> (ALL z. p(z,x) <-> p(z,y))) \
\         --> (ALL x. (ALL y. q(x,y) <-> q(y,x)))";

writeln"Problem 44";
Goal "|- (ALL x. f(x) -->                                        \
\                (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &       \
\        (EX x. j(x) & (ALL y. g(y) --> h(x,y)))                   \
\        --> (EX x. j(x) & ~f(x))";
by (Fast_tac 1);
result();

writeln"Problem 45";
Goal "|- (ALL x. f(x) & (ALL y. g(y) & h(x,y) --> j(x,y))        \
\                     --> (ALL y. g(y) & h(x,y) --> k(y))) &    \
\     ~ (EX y. l(y) & k(y)) &                                   \
\     (EX x. f(x) & (ALL y. h(x,y) --> l(y))                    \
\                  & (ALL y. g(y) & h(x,y) --> j(x,y)))         \
\     --> (EX x. f(x) & ~ (EX y. g(y) & h(x,y)))";
by (best_tac LK_pack 1); 
result();


writeln"Problems (mainly) involving equality or functions";

writeln"Problem 48";
Goal "|- (a=b | c=d) & (a=c | b=d) --> a=d | b=c";
by (fast_tac (pack() add_safes [subst]) 1);
result();

writeln"Problem 50";  
Goal "|- (ALL x. P(a,x) | (ALL y. P(x,y))) --> (EX x. ALL y. P(x,y))";
by (best_tac LK_dup_pack 1);
result();

writeln"Problem 51";
Goal "|- (EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\        (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)";
by (fast_tac (pack() add_safes [subst]) 1);
result();

writeln"Problem 52";
(*Almost the same as 51. *)
Goal "|- (EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->  \
\        (EX w. ALL y. EX z. (ALL x. P(x,y) <-> x=z) <-> y=w)";
by (fast_tac (pack() add_safes [subst]) 1);
result();

writeln"Problem 56";
Goal "|- (ALL x.(EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))";
by (best_tac (pack() add_unsafes [symL, subst]) 1);
(*requires tricker to orient the equality properly*)
result();

writeln"Problem 57";
Goal "|- P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) & \
\        (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))";
by (Fast_tac 1);
result();

writeln"Problem 58!";
Goal "|- (ALL x y. f(x)=g(y)) --> (ALL x y. f(f(x))=f(g(y)))";
by (fast_tac (pack() add_safes [subst]) 1);
result();

writeln"Problem 59";
(*Unification works poorly here -- the abstraction %sobj prevents efficient
  operation of the occurs check*)
Unify.trace_bound := !Unify.search_bound - 1; 
Goal "|- (ALL x. P(x) <-> ~P(f(x))) --> (EX x. P(x) & ~P(f(x)))";
by (best_tac LK_dup_pack 1);
result();

writeln"Problem 60";
Goal "|- ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))";
by (Fast_tac 1);
result();

writeln"Problem 62 as corrected in JAR 18 (1997), page 135";
Goal "|- (ALL x. p(a) & (p(x) --> p(f(x))) --> p(f(f(x))))  <->     \
\     (ALL x. (~p(a) | p(x) | p(f(f(x)))) &                      \
\             (~p(a) | ~p(f(x)) | p(f(f(x)))))";
by (Fast_tac 1);
result();

writeln"Reached end of file.";

(*18 June 92: loaded in 372 secs*)
(*19 June 92: loaded in 166 secs except #34, using repeat_goal_tac*)
(*29 June 92: loaded in 370 secs*)
