(*  Title:      HOL/ex/unsolved
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Problems that currently defeat the MESON procedure as well as best_tac
*)

(*from Vladimir Lifschitz, What Is the Inverse Method?, JAR 5 (1989), 1--23*)
goal HOL.thy "? x x'. ! y. ? z z'. (~P(y,y) | P(x,x) | ~S(z,x)) & \
\                                       (S(x,y) | ~S(y,z) | Q(z',z'))  & \
\                                       (Q(x',y) | ~Q(y,z') | S(x',x'))";


writeln"Problem 47  Schubert's Steamroller";
goal HOL.thy
    "(! x. P1(x) --> P0(x)) & (? x.P1(x)) &     \
\    (! x. P2(x) --> P0(x)) & (? x.P2(x)) &     \
\    (! x. P3(x) --> P0(x)) & (? x.P3(x)) &     \
\    (! x. P4(x) --> P0(x)) & (? x.P4(x)) &     \
\    (! x. P5(x) --> P0(x)) & (? x.P5(x)) &     \
\    (! x. Q1(x) --> Q0(x)) & (? x.Q1(x)) &     \
\    (! x. P0(x) --> ((! y.Q0(y)-->R(x,y)) |    \
\                     (! y.P0(y) & S(y,x) &     \
\                          (? z.Q0(z)&R(y,z)) --> R(x,y)))) &   \
\    (! x y. P3(y) & (P5(x)|P4(x)) --> S(x,y)) &        \
\    (! x y. P3(x) & P2(y) --> S(x,y)) &        \
\    (! x y. P2(x) & P1(y) --> S(x,y)) &        \
\    (! x y. P1(x) & (P2(y)|Q1(y)) --> ~R(x,y)) &       \
\    (! x y. P3(x) & P4(y) --> R(x,y)) &        \
\    (! x y. P3(x) & P5(y) --> ~R(x,y)) &       \
\    (! x. (P4(x)|P5(x)) --> (? y.Q0(y) & R(x,y)))      \
\    --> (? x y. P0(x) & P0(y) & (? z. Q1(z) & R(y,z) & R(x,y)))";


writeln"Problem 55";

(*Original, equational version by Len Schubert, via Pelletier *)
goal HOL.thy
  "(? x. lives(x) & killed(x,agatha)) & \
\  lives(agatha) & lives(butler) & lives(charles) & \
\  (! x. lives(x) --> x=agatha | x=butler | x=charles) & \
\  (! x y. killed(x,y) --> hates(x,y)) & \
\  (! x y. killed(x,y) --> ~richer(x,y)) & \
\  (! x. hates(agatha,x) --> ~hates(charles,x)) & \
\  (! x. ~ x=butler --> hates(agatha,x)) & \
\  (! x. ~richer(x,agatha) --> hates(butler,x)) & \
\  (! x. hates(agatha,x) --> hates(butler,x)) & \
\  (! x. ? y. ~hates(x,y)) & \
\  ~ agatha=butler --> \
\  killed(agatha,agatha)";

(** Charles Morgan's problems **)

val axa = "! x y.   T(i(x, i(y,x)))";
val axb = "! x y z. T(i(i(x, i(y,z)), i(i(x,y), i(x,z))))";
val axc = "! x y.   T(i(i(n(x), n(y)), i(y,x)))";
val axd = "! x y.   T(i(x,y)) & T(x) --> T(y)";

fun axjoin ([],   q) = q
  | axjoin(p::ps, q) = "(" ^ p ^ ") --> (" ^ axjoin(ps,q) ^ ")";

goal HOL.thy (axjoin([axa,axb,axd], "! x. T(i(x,x))"));

writeln"Problem 66";
goal HOL.thy (axjoin([axa,axb,axc,axd], "! x. T(i(x, n(n(x))))"));

writeln"Problem 67";
goal HOL.thy (axjoin([axa,axb,axc,axd], "! x. T(i(n(n(x)), x))"));

