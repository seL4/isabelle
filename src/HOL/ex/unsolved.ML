(*  Title:      HOL/ex/unsolved
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Problems that currently defeat the MESON procedure as well as best_tac
*)

(*from Vladimir Lifschitz, What Is the Inverse Method?, JAR 5  1989.  1--23*)
        (*27 clauses; 81 Horn clauses*)
goal HOL.thy "? x x'. ! y. ? z z'. (~P y y | P x x | ~S z x) & \
\                                  (S x y | ~S y z | Q z' z')  & \
\                                  (Q x' y | ~Q y z' | S x' x')";



writeln"Problem 55";

(*Original, equational version by Len Schubert [via Pelletier] *)
goal HOL.thy
  "(? x. lives x & killed x agatha) & \
\  lives agatha & lives butler & lives charles & \
\  (! x. lives x --> x=agatha | x=butler | x=charles) & \
\  (! x y. killed x y --> hates x y) & \
\  (! x y. killed x y --> ~richer x y) & \
\  (! x. hates agatha x --> ~hates charles x) & \
\  (! x. ~ x=butler --> hates agatha x) & \
\  (! x. ~richer x agatha --> hates butler x) & \
\  (! x. hates agatha x --> hates butler x) & \
\  (! x. ? y. ~hates x y) & \
\  ~ agatha=butler --> \
\  killed agatha agatha";

(*Halting problem: Formulation of Li Dafa (AAR Newsletter 27, Oct 1994.)
        author U. Egly;  46 clauses; 264 Horn clauses*)
goal HOL.thy
 "((EX X. (a X) & (ALL Y. (c Y) --> (ALL Z. (d X Y Z)))) -->  \
\  (EX W. (c W) & (ALL Y. (c Y) --> (ALL Z. (d W Y Z)))))     \
\ &                                                          \
\ (ALL W. (c W) & (ALL U. (c U) --> (ALL V. (d W U V))) -->       \
\       (ALL Y Z.                                               \
\           ((c Y) & (h2 Y Z) --> (h3 W Y Z) & (oo W g)) &       \
\           ((c Y) & ~(h2 Y Z) --> (h3 W Y Z) & (oo W b))))  \
\ &                    \
\ (ALL W. (c W) &       \
\   (ALL Y Z.          \
\       ((c Y) & (h2 Y Z) --> (h3 W Y Z) & (oo W g)) &       \
\       ((c Y) & ~(h2 Y Z) --> (h3 W Y Z) & (oo W b))) -->       \
\   (EX V. (c V) &       \
\         (ALL Y. (((c Y) & (h3 W Y Y)) & (oo W g) --> ~(h2 V Y)) &       \
\                 (((c Y) & (h3 W Y Y)) & (oo W b) --> (h2 V Y) & (oo V b))))) \
\  -->                  \
\  ~ (EX X. (a X) & (ALL Y. (c Y) --> (ALL Z. (d X Y Z))))";

