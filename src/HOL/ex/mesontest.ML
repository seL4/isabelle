(*  Title: 	HOL/ex/meson
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Test data for the MESON proof procedure
   (Excludes the equality problems 51, 52, 56, 58)

show_hyps:=false;

by (rtac ccontr 1);
val [prem] = gethyps 1;
val nnf = make_nnf prem;
val xsko = skolemize nnf;
by (cut_facts_tac [xsko] 1 THEN REPEAT (etac exE 1));
val [_,sko] = gethyps 1;
val clauses = make_clauses [sko];	
val horns = make_horns clauses;
val go::_ = neg_clauses clauses;

goal HOL.thy "False";
by (rtac (make_goal go) 1);
by (prolog_step_tac horns 1);
by (depth_prolog_tac horns);
by (best_prolog_tac size_of_subgoals horns);
*)

writeln"File HOL/ex/meson-test.";

(**** Interactive examples ****)

(*Generate nice names for Skolem functions*)
Logic.auto_rename := true; Logic.set_rename_prefix "a";


writeln"Problem 25";
goal HOL.thy "(? x. P(x)) &  \
\       (! x. L(x) --> ~ (M(x) & R(x))) &  \
\       (! x. P(x) --> (M(x) & L(x))) &   \
\       ((! x. P(x)-->Q(x)) | (? x. P(x)&R(x)))  \
\   --> (? x. Q(x)&P(x))";
by (rtac ccontr 1);
val [prem25] = gethyps 1;
val nnf25 = make_nnf prem25;
val xsko25 = skolemize nnf25;
by (cut_facts_tac [xsko25] 1 THEN REPEAT (etac exE 1));
val [_,sko25] = gethyps 1;
val clauses25 = make_clauses [sko25];	(*7 clauses*)
val horns25 = make_horns clauses25;	(*16 Horn clauses*)
val go25::_ = neg_clauses clauses25;

goal HOL.thy "False";
by (rtac (make_goal go25) 1);
by (depth_prolog_tac horns25);


writeln"Problem 26";
goal HOL.thy "((? x. p(x)) = (? x. q(x))) &	\
\     (! x. ! y. p(x) & q(y) --> (r(x) = s(y)))	\
\ --> ((! x. p(x)-->r(x)) = (! x. q(x)-->s(x)))";
by (rtac ccontr 1);
val [prem26] = gethyps 1;
val nnf26 = make_nnf prem26;
val xsko26 = skolemize nnf26;
by (cut_facts_tac [xsko26] 1 THEN REPEAT (etac exE 1));
val [_,sko26] = gethyps 1;
val clauses26 = make_clauses [sko26];			(*9 clauses*)
val horns26 = make_horns clauses26;			(*24 Horn clauses*)
val go26::_ = neg_clauses clauses26;

goal HOL.thy "False";
by (rtac (make_goal go26) 1);
by (depth_prolog_tac horns26);	(*6 secs*)



writeln"Problem 43  NOW PROVED AUTOMATICALLY!!";
goal HOL.thy "(! x. ! y. q x y = (! z. p z x = (p z y::bool)))	\
\         --> (! x. (! y. q x y = (q y x::bool)))";
by (rtac ccontr 1);
val [prem43] = gethyps 1;
val nnf43 = make_nnf prem43;
val xsko43 = skolemize nnf43;
by (cut_facts_tac [xsko43] 1 THEN REPEAT (etac exE 1));
val [_,sko43] = gethyps 1;
val clauses43 = make_clauses [sko43];	(*6*)
val horns43 = make_horns clauses43;	(*16*)
val go43::_ = neg_clauses clauses43;

goal HOL.thy "False";
by (rtac (make_goal go43) 1);
by (best_prolog_tac size_of_subgoals horns43);
(*8.7 secs*)


(*Restore variable name preservation*)
Logic.auto_rename := false; 


(**** Batch test data ****)

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
by (safe_meson_tac 1);
result();

(*2*)
goal HOL.thy "(~ ~ P) =  P";
by (safe_meson_tac 1);
result();

(*3*)
goal HOL.thy "~(P-->Q) --> (Q-->P)";
by (safe_meson_tac 1);
result();

(*4*)
goal HOL.thy "(~P-->Q)  =  (~Q --> P)";
by (safe_meson_tac 1);
result();

(*5*)
goal HOL.thy "((P|Q)-->(P|R)) --> (P|(Q-->R))";
by (safe_meson_tac 1);
result();

(*6*)
goal HOL.thy "P | ~ P";
by (safe_meson_tac 1);
result();

(*7*)
goal HOL.thy "P | ~ ~ ~ P";
by (safe_meson_tac 1);
result();

(*8.  Peirce's law*)
goal HOL.thy "((P-->Q) --> P)  -->  P";
by (safe_meson_tac 1);
result();

(*9*)
goal HOL.thy "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (safe_meson_tac 1);
result();

(*10*)
goal HOL.thy "(Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P=Q)";
by (safe_meson_tac 1);
result();

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
goal HOL.thy "P=(P::bool)";
by (safe_meson_tac 1);
result();

(*12.  "Dijkstra's law"*)
goal HOL.thy "((P = Q) = R) = (P = (Q = R))";
by (best_meson_tac size_of_subgoals 1);
result();

(*13.  Distributive law*)
goal HOL.thy "(P | (Q & R)) = ((P | Q) & (P | R))";
by (safe_meson_tac 1);
result();

(*14*)
goal HOL.thy "(P = Q) = ((Q | ~P) & (~Q|P))";
by (safe_meson_tac 1);
result();

(*15*)
goal HOL.thy "(P --> Q) = (~P | Q)";
by (safe_meson_tac 1);
result();

(*16*)
goal HOL.thy "(P-->Q) | (Q-->P)";
by (safe_meson_tac 1);
result();

(*17*)
goal HOL.thy "((P & (Q-->R))-->S)  =  ((~P | Q | S) & (~P | ~R | S))";
by (safe_meson_tac 1);
result();

writeln"Classical Logic: examples with quantifiers";

goal HOL.thy "(! x. P(x) & Q(x)) = ((! x. P(x)) & (! x. Q(x)))";
by (safe_meson_tac 1);
result(); 

goal HOL.thy "(? x. P-->Q(x))  =  (P --> (? x.Q(x)))";
by (safe_meson_tac 1);
result(); 

goal HOL.thy "(? x.P(x)-->Q) = ((! x.P(x)) --> Q)";
by (safe_meson_tac 1);
result(); 

goal HOL.thy "((! x.P(x)) | Q)  =  (! x. P(x) | Q)";
by (safe_meson_tac 1);
result(); 

writeln"Testing the complete tactic";

(*Not provable by pc_tac: needs multiple instantiation of !.
  Could be proved trivially by a PROLOG interpreter*)
goal HOL.thy "(! x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))";
by (safe_meson_tac 1);
result();

(*Not provable by pc_tac: needs double instantiation of EXISTS*)
goal HOL.thy "? x. P(x) --> P(a) & P(b)";
by (safe_meson_tac 1);
result();

goal HOL.thy "? z. P(z) --> (! x. P(x))";
by (safe_meson_tac 1);
result();

writeln"Hard examples with quantifiers";

writeln"Problem 18";
goal HOL.thy "? y. ! x. P(y)-->P(x)";
by (safe_meson_tac 1);
result(); 

writeln"Problem 19";
goal HOL.thy "? x. ! y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))";
by (safe_meson_tac 1);
result();

writeln"Problem 20";
goal HOL.thy "(! x y. ? z. ! w. (P(x)&Q(y)-->R(z)&S(w)))     \
\   --> (? x y. P(x) & Q(y)) --> (? z. R(z))";
by (safe_meson_tac 1); 
result();

writeln"Problem 21";
goal HOL.thy "(? x. P-->Q(x)) & (? x. Q(x)-->P) --> (? x. P=Q(x))";
by (safe_meson_tac 1); 
result();

writeln"Problem 22";
goal HOL.thy "(! x. P = Q(x))  -->  (P = (! x. Q(x)))";
by (safe_meson_tac 1); 
result();

writeln"Problem 23";
goal HOL.thy "(! x. P | Q(x))  =  (P | (! x. Q(x)))";
by (safe_meson_tac 1);  
result();

writeln"Problem 24";
goal HOL.thy "~(? x. S(x)&Q(x)) & (! x. P(x) --> Q(x)|R(x)) &  \
\    ~(? x.P(x)) --> (? x.Q(x)) & (! x. Q(x)|R(x) --> S(x))  \
\   --> (? x. P(x)&R(x))";
by (safe_meson_tac 1); 
result();

writeln"Problem 25";
goal HOL.thy "(? x. P(x)) &  \
\       (! x. L(x) --> ~ (M(x) & R(x))) &  \
\       (! x. P(x) --> (M(x) & L(x))) &   \
\       ((! x. P(x)-->Q(x)) | (? x. P(x)&R(x)))  \
\   --> (? x. Q(x)&P(x))";
by (safe_meson_tac 1); 
result();

writeln"Problem 26";
goal HOL.thy "((? x. p(x)) = (? x. q(x))) &	\
\     (! x. ! y. p(x) & q(y) --> (r(x) = s(y)))	\
\ --> ((! x. p(x)-->r(x)) = (! x. q(x)-->s(x)))";
by (safe_meson_tac 1); 
result();

writeln"Problem 27";
goal HOL.thy "(? x. P(x) & ~Q(x)) &   \
\             (! x. P(x) --> R(x)) &   \
\             (! x. M(x) & L(x) --> P(x)) &   \
\             ((? x. R(x) & ~ Q(x)) --> (! x. L(x) --> ~ R(x)))  \
\         --> (! x. M(x) --> ~L(x))";
by (safe_meson_tac 1); 
result();

writeln"Problem 28.  AMENDED";
goal HOL.thy "(! x. P(x) --> (! x. Q(x))) &   \
\       ((! x. Q(x)|R(x)) --> (? x. Q(x)&S(x))) &  \
\       ((? x.S(x)) --> (! x. L(x) --> M(x)))  \
\   --> (! x. P(x) & L(x) --> M(x))";
by (safe_meson_tac 1);  
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
goal HOL.thy "(? x. F(x)) & (? y. G(y))  \
\   --> ( ((! x. F(x)-->H(x)) & (! y. G(y)-->J(y)))  =   \
\         (! x y. F(x) & G(y) --> H(x) & J(y)))";
by (safe_meson_tac 1);		(*5 secs*)
result();

writeln"Problem 30";
goal HOL.thy "(! x. P(x) | Q(x) --> ~ R(x)) & \
\       (! x. (Q(x) --> ~ S(x)) --> P(x) & R(x))  \
\   --> (! x. S(x))";
by (safe_meson_tac 1);  
result();

writeln"Problem 31";
goal HOL.thy "~(? x.P(x) & (Q(x) | R(x))) & \
\       (? x. L(x) & P(x)) & \
\       (! x. ~ R(x) --> M(x))  \
\   --> (? x. L(x) & M(x))";
by (safe_meson_tac 1);
result();

writeln"Problem 32";
goal HOL.thy "(! x. P(x) & (Q(x)|R(x))-->S(x)) & \
\       (! x. S(x) & R(x) --> L(x)) & \
\       (! x. M(x) --> R(x))  \
\   --> (! x. P(x) & M(x) --> L(x))";
by (safe_meson_tac 1);
result();

writeln"Problem 33";
goal HOL.thy "(! x. P(a) & (P(x)-->P(b))-->P(c))  =    \
\    (! x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))";
by (safe_meson_tac 1);		(*5.6 secs*)
result();

writeln"Problem 34  AMENDED (TWICE!!)";
(*Andrews's challenge*)
goal HOL.thy "((? x. ! y. p(x) = p(y))  =		\
\              ((? x. q(x)) = (! y. p(y))))     =	\
\             ((? x. ! y. q(x) = q(y))  =		\
\              ((? x. p(x)) = (! y. q(y))))";
by (safe_meson_tac 1);  	(*90 secs*)
result();

writeln"Problem 35";
goal HOL.thy "? x y. P x y -->  (! u v. P u v)";
by (safe_meson_tac 1);
result();

writeln"Problem 36";
goal HOL.thy "(! x. ? y. J x y) & \
\       (! x. ? y. G x y) & \
\       (! x y. J x y | G x y -->	\
\       (! z. J y z | G y z --> H x z))   \
\   --> (! x. ? y. H x y)";
by (safe_meson_tac 1);
result();

writeln"Problem 37";
goal HOL.thy "(! z. ? w. ! x. ? y. \
\          (P x z-->P y w) & P y z & (P y w --> (? u.Q u w))) & \
\       (! x z. ~P x z --> (? y. Q y z)) & \
\       ((? x y. Q x y) --> (! x. R x x))  \
\   --> (! x. ? y. R x y)";
by (safe_meson_tac 1);   (*causes unification tracing messages*)
result();

writeln"Problem 38";
goal HOL.thy
    "(! x. p(a) & (p(x) --> (? y. p(y) & r x y)) -->		\
\          (? z. ? w. p(z) & r x w & r w z))  =			\
\    (! x. (~p(a) | p(x) | (? z. ? w. p(z) & r x w & r w z)) &	\
\          (~p(a) | ~(? y. p(y) & r x y) |			\
\           (? z. ? w. p(z) & r x w & r w z)))";
by (safe_meson_tac 1);		(*62 secs*)
result();

writeln"Problem 39";
goal HOL.thy "~ (? x. ! y. F y x = (~F y y))";
by (safe_meson_tac 1);
result();

writeln"Problem 40.  AMENDED";
goal HOL.thy "(? y. ! x. F x y = F x x)  \
\       -->  ~ (! x. ? y. ! z. F z y = (~F z x))";
by (safe_meson_tac 1);
result();

writeln"Problem 41";
goal HOL.thy "(! z. (? y. (! x. f x y = (f x z & ~ f x x))))	\
\              --> ~ (? z. ! x. f x z)";
by (safe_meson_tac 1);
result();

writeln"Problem 42";
goal HOL.thy "~ (? y. ! x. p x y = (~ (? z. p x z & p z x)))";
by (safe_meson_tac 1);
result();

writeln"Problem 43  NOW PROVED AUTOMATICALLY!!";
goal HOL.thy "(! x. ! y. q x y = (! z. p z x = (p z y::bool)))	\
\         --> (! x. (! y. q x y = (q y x::bool)))";
by (safe_meson_tac 1);
result();

writeln"Problem 44";
goal HOL.thy "(! x. f(x) -->					\
\             (? y. g(y) & h x y & (? y. g(y) & ~ h x y)))  &  	\
\             (? x. j(x) & (! y. g(y) --> h x y))		\
\             --> (? x. j(x) & ~f(x))";
by (safe_meson_tac 1);
result();

writeln"Problem 45";
goal HOL.thy "(! x. f(x) & (! y. g(y) & h x y --> j x y)	\
\                     --> (! y. g(y) & h x y --> k(y))) &	\
\     ~ (? y. l(y) & k(y)) &					\
\     (? x. f(x) & (! y. h x y --> l(y))			\
\                  & (! y. g(y) & h x y --> j x y))		\
\     --> (? x. f(x) & ~ (? y. g(y) & h x y))";
by (safe_meson_tac 1);  	(*11 secs*)
result();

writeln"Problem 46";
goal HOL.thy
    "(! x. f(x) & (! y. f(y) & h y x --> g(y)) --> g(x)) &	\
\    ((? x.f(x) & ~g(x)) -->					\
\     (? x. f(x) & ~g(x) & (! y. f(y) & ~g(y) --> j x y))) &	\
\    (! x y. f(x) & f(y) & h x y --> ~j y x)			\
\     --> (! x. f(x) --> g(x))";
by (safe_meson_tac 1); 		(*11 secs*)
result();

(* Example suggested by Johannes Schumann and credited to Pelletier *)
goal HOL.thy "(!x y z. P x y --> P y z --> P x z) --> \
\	(!x y z. Q x y --> Q y z --> Q x z) --> \
\	(!x y.Q x y --> Q y x) -->  (!x y. P x y | Q x y) --> \
\	(!x y.P x y) | (!x y.Q x y)";
by (safe_meson_tac 1);		(*32 secs*)
result();

writeln"Problem 50";  
(*What has this to do with equality?*)
goal HOL.thy "(! x. P a x | (! y.P x y)) --> (? x. ! y.P x y)";
by (safe_meson_tac 1);
result();

writeln"Problem 55";

(*Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  meson_tac cannot report who killed Agatha. *)
goal HOL.thy "lives(agatha) & lives(butler) & lives(charles) & \
\  (killed agatha agatha | killed butler agatha | killed charles agatha) & \
\  (!x y. killed x y --> hates x y & ~richer x y) & \
\  (!x. hates agatha x --> ~hates charles x) & \
\  (hates agatha agatha & hates agatha charles) & \
\  (!x. lives(x) & ~richer x agatha --> hates butler x) & \
\  (!x. hates agatha x --> hates butler x) & \
\  (!x. ~hates x agatha | ~hates x butler | ~hates x charles) --> \
\  (? x. killed x agatha)";
by (safe_meson_tac 1);
result();

writeln"Problem 57";
goal HOL.thy
    "P (f a b) (f b c) & P (f b c) (f a c) & \
\    (! x y z. P x y & P y z --> P x z)    -->   P (f a b) (f a c)";
by (safe_meson_tac 1);
result();

writeln"Problem 58";
(* Challenge found on info-hol *)
goal HOL.thy
    "! P Q R x. ? v w. ! y z. P(x) & Q(y) --> (P(v) | R(w)) & (R(z) --> Q(v))";
by (safe_meson_tac 1);
result();

writeln"Problem 59";
goal HOL.thy "(! x. P(x) = (~P(f(x)))) --> (? x. P(x) & ~P(f(x)))";
by (safe_meson_tac 1);
result();

writeln"Problem 60";
goal HOL.thy "! x. P x (f x) = (? y. (! z. P z y --> P z (f x)) & P x y)";
by (safe_meson_tac 1);
result();

writeln"Reached end of file.";

(*26 August 1992: loaded in 277 secs.  New Jersey v 75*)
