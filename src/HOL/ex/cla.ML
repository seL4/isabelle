(*  Title:      HOL/ex/cla
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Higher-Order Logic: predicate calculus problems

Taken from FOL/cla.ML; beware of precedence of = vs <->
*)

writeln"File HOL/ex/cla.";

set_current_thy "HOL";  (*Boosts efficiency by omitting redundant rules*)

goal HOL.thy "(P --> Q | R) --> (P-->Q) | (P-->R)";
by (Blast_tac 1);
result();

(*If and only if*)

goal HOL.thy "(P=Q) = (Q = (P::bool))";
by (Blast_tac 1);
result();

goal HOL.thy "~ (P = (~P))";
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
goal HOL.thy "(P-->Q)  =  (~Q --> ~P)";
by (Blast_tac 1);
result();

(*2*)
goal HOL.thy "(~ ~ P) =  P";
by (Blast_tac 1);
result();

(*3*)
goal HOL.thy "~(P-->Q) --> (Q-->P)";
by (Blast_tac 1);
result();

(*4*)
goal HOL.thy "(~P-->Q)  =  (~Q --> P)";
by (Blast_tac 1);
result();

(*5*)
goal HOL.thy "((P|Q)-->(P|R)) --> (P|(Q-->R))";
by (Blast_tac 1);
result();

(*6*)
goal HOL.thy "P | ~ P";
by (Blast_tac 1);
result();

(*7*)
goal HOL.thy "P | ~ ~ ~ P";
by (Blast_tac 1);
result();

(*8.  Peirce's law*)
goal HOL.thy "((P-->Q) --> P)  -->  P";
by (Blast_tac 1);
result();

(*9*)
goal HOL.thy "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (Blast_tac 1);
result();

(*10*)
goal HOL.thy "(Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P=Q)";
by (Blast_tac 1);
result();

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
goal HOL.thy "P=(P::bool)";
by (Blast_tac 1);
result();

(*12.  "Dijkstra's law"*)
goal HOL.thy "((P = Q) = R) = (P = (Q = R))";
by (Blast_tac 1);
result();

(*13.  Distributive law*)
goal HOL.thy "(P | (Q & R)) = ((P | Q) & (P | R))";
by (Blast_tac 1);
result();

(*14*)
goal HOL.thy "(P = Q) = ((Q | ~P) & (~Q|P))";
by (Blast_tac 1);
result();

(*15*)
goal HOL.thy "(P --> Q) = (~P | Q)";
by (Blast_tac 1);
result();

(*16*)
goal HOL.thy "(P-->Q) | (Q-->P)";
by (Blast_tac 1);
result();

(*17*)
goal HOL.thy "((P & (Q-->R))-->S)  =  ((~P | Q | S) & (~P | ~R | S))";
by (Blast_tac 1);
result();

writeln"Classical Logic: examples with quantifiers";

goal HOL.thy "(! x. P(x) & Q(x)) = ((! x. P(x)) & (! x. Q(x)))";
by (Blast_tac 1);
result(); 

goal HOL.thy "(? x. P-->Q(x))  =  (P --> (? x. Q(x)))";
by (Blast_tac 1);
result(); 

goal HOL.thy "(? x. P(x)-->Q) = ((! x. P(x)) --> Q)";
by (Blast_tac 1);
result(); 

goal HOL.thy "((! x. P(x)) | Q)  =  (! x. P(x) | Q)";
by (Blast_tac 1);
result(); 

(*From Wishnu Prasetya*)
goal HOL.thy
   "(!s. q(s) --> r(s)) & ~r(s) & (!s. ~r(s) & ~q(s) --> p(t) | q(t)) \
\   --> p(t) | r(t)";
by (Blast_tac 1);
result(); 


writeln"Problems requiring quantifier duplication";

(*Needs multiple instantiation of the quantifier.*)
goal HOL.thy "(! x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))";
by (Blast_tac 1);
result();

(*Needs double instantiation of the quantifier*)
goal HOL.thy "? x. P(x) --> P(a) & P(b)";
by (Blast_tac 1);
result();

goal HOL.thy "? z. P(z) --> (! x. P(x))";
by (Blast_tac 1);
result();

goal HOL.thy "? x. (? y. P(y)) --> P(x)";
by (Blast_tac 1);
result();

writeln"Hard examples with quantifiers";

writeln"Problem 18";
goal HOL.thy "? y. ! x. P(y)-->P(x)";
by (Blast_tac 1);
result(); 

writeln"Problem 19";
goal HOL.thy "? x. ! y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))";
by (Blast_tac 1);
result();

writeln"Problem 20";
goal HOL.thy "(! x y. ? z. ! w. (P(x)&Q(y)-->R(z)&S(w)))     \
\   --> (? x y. P(x) & Q(y)) --> (? z. R(z))";
by (Blast_tac 1); 
result();

writeln"Problem 21";
goal HOL.thy "(? x. P-->Q(x)) & (? x. Q(x)-->P) --> (? x. P=Q(x))";
by (Blast_tac 1); 
result();

writeln"Problem 22";
goal HOL.thy "(! x. P = Q(x))  -->  (P = (! x. Q(x)))";
by (Blast_tac 1); 
result();

writeln"Problem 23";
goal HOL.thy "(! x. P | Q(x))  =  (P | (! x. Q(x)))";
by (Blast_tac 1);  
result();

writeln"Problem 24";
goal HOL.thy "~(? x. S(x)&Q(x)) & (! x. P(x) --> Q(x)|R(x)) &  \
\    (~(? x. P(x)) --> (? x. Q(x))) & (! x. Q(x)|R(x) --> S(x))  \
\   --> (? x. P(x)&R(x))";
by (Blast_tac 1); 
result();

writeln"Problem 25";
goal HOL.thy "(? x. P(x)) &  \
\       (! x. L(x) --> ~ (M(x) & R(x))) &  \
\       (! x. P(x) --> (M(x) & L(x))) &   \
\       ((! x. P(x)-->Q(x)) | (? x. P(x)&R(x)))  \
\   --> (? x. Q(x)&P(x))";
by (Blast_tac 1); 
result();

writeln"Problem 26";
goal HOL.thy "((? x. p(x)) = (? x. q(x))) &     \
\     (! x. ! y. p(x) & q(y) --> (r(x) = s(y))) \
\ --> ((! x. p(x)-->r(x)) = (! x. q(x)-->s(x)))";
by (Blast_tac 1);
result();

writeln"Problem 27";
goal HOL.thy "(? x. P(x) & ~Q(x)) &   \
\             (! x. P(x) --> R(x)) &   \
\             (! x. M(x) & L(x) --> P(x)) &   \
\             ((? x. R(x) & ~ Q(x)) --> (! x. L(x) --> ~ R(x)))  \
\         --> (! x. M(x) --> ~L(x))";
by (Blast_tac 1); 
result();

writeln"Problem 28.  AMENDED";
goal HOL.thy "(! x. P(x) --> (! x. Q(x))) &   \
\       ((! x. Q(x)|R(x)) --> (? x. Q(x)&S(x))) &  \
\       ((? x. S(x)) --> (! x. L(x) --> M(x)))  \
\   --> (! x. P(x) & L(x) --> M(x))";
by (Blast_tac 1);  
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
goal HOL.thy "(? x. F(x)) & (? y. G(y))  \
\   --> ( ((! x. F(x)-->H(x)) & (! y. G(y)-->J(y)))  =   \
\         (! x y. F(x) & G(y) --> H(x) & J(y)))";
by (Blast_tac 1); 
result();

writeln"Problem 30";
goal HOL.thy "(! x. P(x) | Q(x) --> ~ R(x)) & \
\       (! x. (Q(x) --> ~ S(x)) --> P(x) & R(x))  \
\   --> (! x. S(x))";
by (Blast_tac 1);  
result();

writeln"Problem 31";
goal HOL.thy "~(? x. P(x) & (Q(x) | R(x))) & \
\       (? x. L(x) & P(x)) & \
\       (! x. ~ R(x) --> M(x))  \
\   --> (? x. L(x) & M(x))";
by (Blast_tac 1);
result();

writeln"Problem 32";
goal HOL.thy "(! x. P(x) & (Q(x)|R(x))-->S(x)) & \
\       (! x. S(x) & R(x) --> L(x)) & \
\       (! x. M(x) --> R(x))  \
\   --> (! x. P(x) & M(x) --> L(x))";
by (Blast_tac 1);
result();

writeln"Problem 33";
goal HOL.thy "(! x. P(a) & (P(x)-->P(b))-->P(c))  =    \
\    (! x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))";
by (Blast_tac 1);
result();

writeln"Problem 34  AMENDED (TWICE!!)";
(*Andrews's challenge*)
goal HOL.thy "((? x. ! y. p(x) = p(y))  =               \
\              ((? x. q(x)) = (! y. p(y))))   =    \
\             ((? x. ! y. q(x) = q(y))  =          \
\              ((? x. p(x)) = (! y. q(y))))";
by (Blast_tac 1);
result();

writeln"Problem 35";
goal HOL.thy "? x y. P x y -->  (! u v. P u v)";
by (Blast_tac 1);
result();

writeln"Problem 36";
goal HOL.thy "(! x. ? y. J x y) & \
\       (! x. ? y. G x y) & \
\       (! x y. J x y | G x y -->       \
\       (! z. J y z | G y z --> H x z))   \
\   --> (! x. ? y. H x y)";
by (Blast_tac 1);
result();

writeln"Problem 37";
goal HOL.thy "(! z. ? w. ! x. ? y. \
\          (P x z -->P y w) & P y z & (P y w --> (? u. Q u w))) & \
\       (! x z. ~(P x z) --> (? y. Q y z)) & \
\       ((? x y. Q x y) --> (! x. R x x))  \
\   --> (! x. ? y. R x y)";
by (Blast_tac 1);
result();

writeln"Problem 38";
goal HOL.thy
    "(! x. p(a) & (p(x) --> (? y. p(y) & r x y)) -->            \
\          (? z. ? w. p(z) & r x w & r w z))  =                 \
\    (! x. (~p(a) | p(x) | (? z. ? w. p(z) & r x w & r w z)) &  \
\          (~p(a) | ~(? y. p(y) & r x y) |                      \
\           (? z. ? w. p(z) & r x w & r w z)))";
by (Blast_tac 1);  (*beats fast_tac!*)
result();

writeln"Problem 39";
goal HOL.thy "~ (? x. ! y. F y x = (~ F y y))";
by (Blast_tac 1);
result();

writeln"Problem 40.  AMENDED";
goal HOL.thy "(? y. ! x. F x y = F x x)  \
\       -->  ~ (! x. ? y. ! z. F z y = (~ F z x))";
by (Blast_tac 1);
result();

writeln"Problem 41";
goal HOL.thy "(! z. ? y. ! x. f x y = (f x z & ~ f x x))        \
\              --> ~ (? z. ! x. f x z)";
by (Blast_tac 1);
result();

writeln"Problem 42";
goal HOL.thy "~ (? y. ! x. p x y = (~ (? z. p x z & p z x)))";
by (Blast_tac 1);
result();

writeln"Problem 43!!";
goal HOL.thy
    "(! x::'a. ! y::'a. q x y = (! z. p z x = (p z y::bool)))   \
\ --> (! x. (! y. q x y = (q y x::bool)))";
by (Blast_tac 1);
result();

writeln"Problem 44";
goal HOL.thy "(! x. f(x) -->                                    \
\             (? y. g(y) & h x y & (? y. g(y) & ~ h x y)))  &   \
\             (? x. j(x) & (! y. g(y) --> h x y))               \
\             --> (? x. j(x) & ~f(x))";
by (Blast_tac 1);
result();

writeln"Problem 45";
goal HOL.thy
    "(! x. f(x) & (! y. g(y) & h x y --> j x y) \
\                     --> (! y. g(y) & h x y --> k(y))) &       \
\    ~ (? y. l(y) & k(y)) &                                     \
\    (? x. f(x) & (! y. h x y --> l(y))                         \
\               & (! y. g(y) & h x y --> j x y))                \
\     --> (? x. f(x) & ~ (? y. g(y) & h x y))";
by (Blast_tac 1); 
result();


writeln"Problems (mainly) involving equality or functions";

writeln"Problem 48";
goal HOL.thy "(a=b | c=d) & (a=c | b=d) --> a=d | b=c";
by (Blast_tac 1);
result();

writeln"Problem 49  NOT PROVED AUTOMATICALLY";
(*Hard because it involves substitution for Vars;
  the type constraint ensures that x,y,z have the same type as a,b,u. *)
goal HOL.thy "(? x y::'a. ! z. z=x | z=y) & P(a) & P(b) & (~a=b) \
\               --> (! u::'a. P(u))";
by (Classical.safe_tac (!claset));
by (res_inst_tac [("x","a")] allE 1);
by (assume_tac 1);
by (res_inst_tac [("x","b")] allE 1);
by (assume_tac 1);
by (Blast_tac 1);
result();

writeln"Problem 50";  
(*What has this to do with equality?*)
goal HOL.thy "(! x. P a x | (! y. P x y)) --> (? x. ! y. P x y)";
by (Blast_tac 1);
result();

writeln"Problem 51";
goal HOL.thy
    "(? z w. ! x y. P x y = (x=z & y=w)) -->  \
\    (? z. ! x. ? w. (! y. P x y = (y=w)) = (x=z))";
by (Blast_tac 1);
result();

writeln"Problem 52";
(*Almost the same as 51. *)
goal HOL.thy
    "(? z w. ! x y. P x y = (x=z & y=w)) -->  \
\    (? w. ! y. ? z. (! x. P x y = (x=z)) = (y=w))";
by (Blast_tac 1);
result();

writeln"Problem 55";

(*Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  fast_tac DISCOVERS who killed Agatha. *)
goal HOL.thy "lives(agatha) & lives(butler) & lives(charles) & \
\  (killed agatha agatha | killed butler agatha | killed charles agatha) & \
\  (!x y. killed x y --> hates x y & ~richer x y) & \
\  (!x. hates agatha x --> ~hates charles x) & \
\  (hates agatha agatha & hates agatha charles) & \
\  (!x. lives(x) & ~richer x agatha --> hates butler x) & \
\  (!x. hates agatha x --> hates butler x) & \
\  (!x. ~hates x agatha | ~hates x butler | ~hates x charles) --> \
\   killed ?who agatha";
by (Fast_tac 1);
result();

writeln"Problem 56";
goal HOL.thy
    "(! x. (? y. P(y) & x=f(y)) --> P(x)) = (! x. P(x) --> P(f(x)))";
by (Blast_tac 1);
result();

writeln"Problem 57";
goal HOL.thy
    "P (f a b) (f b c) & P (f b c) (f a c) & \
\    (! x y z. P x y & P y z --> P x z)    -->   P (f a b) (f a c)";
by (Blast_tac 1);
result();

writeln"Problem 58  NOT PROVED AUTOMATICALLY";
goal HOL.thy "(! x y. f(x)=g(y)) --> (! x y. f(f(x))=f(g(y)))";
val f_cong = read_instantiate [("f","f")] arg_cong;
by (fast_tac (!claset addIs [f_cong]) 1);
result();

writeln"Problem 59";
goal HOL.thy "(! x. P(x) = (~P(f(x)))) --> (? x. P(x) & ~P(f(x)))";
by (Blast_tac 1);
result();

writeln"Problem 60";
goal HOL.thy
    "! x. P x (f x) = (? y. (! z. P z y --> P z (f x)) & P x y)";
by (Blast_tac 1);
result();

writeln"Problem 62 as corrected in JAR 18 (1997), page 135";
goal HOL.thy
    "(ALL x. p a & (p x --> p(f x)) --> p(f(f x)))  =   \
\    (ALL x. (~ p a | p x | p(f(f x))) &                        \
\            (~ p a | ~ p(f x) | p(f(f x))))";
by (Blast_tac 1);
result();

(*From Rudnicki, Obvious Inferences, JAR 3 (1987), 383-393.  
  It does seem obvious!*)
goal Prod.thy
    "(ALL x. F(x) & ~G(x) --> (EX y. H(x,y) & J(y))) &        \
\    (EX x. K(x) & F(x) & (ALL y. H(x,y) --> K(y)))  &        \
\    (ALL x. K(x) --> ~G(x))   -->   (EX x. K(x) --> ~G(x))";
by (Blast_tac 1);
result();

goal Prod.thy
    "(ALL x y. R(x,y) | R(y,x)) &                \
\    (ALL x y. S(x,y) & S(y,x) --> x=y) &        \
\    (ALL x y. R(x,y) --> S(x,y))    -->   (ALL x y. S(x,y) --> R(x,y))";
by (Blast_tac 1);
result();



writeln"Reached end of file.";
