(*  Title:      Redex.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Redex;

(* ------------------------------------------------------------------------- *)
(*      redex_rec conversions                                                *)
(* ------------------------------------------------------------------------- *)

goal Redex.thy  "redex_rec(Var(n),b,c,d) = b(n)";
by (rtac (redex_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (rank_ss addsimps redexes.con_defs)  1);
val redex_rec_Var = result();

goal Redex.thy  "redex_rec(Fun(t),b,c,d) = c(t,redex_rec(t,b,c,d))";
by (rtac (redex_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (rank_ss addsimps redexes.con_defs)  1);
val redex_rec_Fun = result();

goal Redex.thy  "redex_rec(App(m,f,a),b,c,d) =  \
\                      d(m,f,a,redex_rec(f,b,c,d),redex_rec(a,b,c,d))";
by (rtac (redex_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (rank_ss addsimps redexes.con_defs)  1);
val redex_rec_App = result();

val redexes_ss = (arith_ss addsimps 
                  ([redex_rec_App,redex_rec_Fun,redex_rec_Var]@redexes.intrs));





