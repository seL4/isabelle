(*  Title:      HOL/Lambda/InductTermi.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen

Inductive characterization of terminating lambda terms.
Goes back to
Raamsdonk & Severi. On normalization. CWI TR CS-R9545, 1995.
Also rediscovered by Matthes and Joachimski.
*)

InductTermi = ListBeta +

consts IT :: dB set
inductive IT
intrs
VarI "rs : lists IT ==> (Var n)$$rs : IT"
LambdaI "r : IT ==> Abs r : IT"
BetaI "[| (r[s/0])$$ss : IT; s : IT |] ==> (Abs r $ s)$$ss : IT"
monos lists_mono

end
