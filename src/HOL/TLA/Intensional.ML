(* 
    File:	 Intensional.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

Lemmas and tactics for "intensional" logics.
*)

val intensional_rews = [unl_con,unl_lift,unl_lift2,unl_lift3,unl_Rall,unl_Rex];

(** Lift usual HOL simplifications to "intensional" level. 
    Convert s .= t into rewrites s == t, so we can use the standard 
    simplifier.
**)
local

fun prover s = (prove_goal Intensional.thy s 
                 (fn _ => [rewrite_goals_tac (int_valid::intensional_rews), 
                           blast_tac HOL_cs 1])) RS inteq_reflection;

in

val int_simps = map prover
 [ "(x.=x) .= #True",
   "(.~#True) .= #False", "(.~#False) .= #True", "(.~ .~ P) .= P",
   "((.~P) .= P) .= #False", "(P .= (.~P)) .= #False", 
   "(P .~= Q) .= (P .= (.~Q))",
   "(#True.=P) .= P", "(P.=#True) .= P",
   "(#True .-> P) .= P", "(#False .-> P) .= #True", 
   "(P .-> #True) .= #True", "(P .-> P) .= #True",
   "(P .-> #False) .= (.~P)", "(P .-> .~P) .= (.~P)",
   "(P .& #True) .= P", "(#True .& P) .= P", 
   "(P .& #False) .= #False", "(#False .& P) .= #False", 
   "(P .& P) .= P", "(P .& .~P) .= #False", "(.~P .& P) .= #False",
   "(P .| #True) .= #True", "(#True .| P) .= #True", 
   "(P .| #False) .= P", "(#False .| P) .= P", 
   "(P .| P) .= P", "(P .| .~P) .= #True", "(.~P .| P) .= #True",
   "(RALL x.P) .= P", "(REX x.P) .= P",
   "(.~Q .-> .~P) .= (P .-> Q)",
   "(P.|Q .-> R) .= ((P.->R).&(Q.->R))" ];

end;

Addsimps (intensional_rews @ int_simps);

(* Derive introduction and destruction rules from definition of 
   intensional validity.
*)
qed_goal "intI" Intensional.thy "(!!w. w |= A) ==> A"
  (fn prems => [rewtac int_valid,
                resolve_tac prems 1
               ]);

qed_goalw "intD" Intensional.thy [int_valid] "A ==> w |= A"
  (fn [prem] => [ rtac (forall_elim_var 0 prem) 1 ]);

(* ======== Functions to "unlift" intensional implications into HOL rules ====== *)

(* Basic unlifting introduces a parameter "w" and applies basic rewrites, e.g.
   F .= G    gets   (w |= F) = (w |= G)
   F .-> G   gets   (w |= F) --> (w |= G)
*)
fun int_unlift th = rewrite_rule intensional_rews (th RS intD);

(* F .-> G   becomes   w |= F  ==>  w |= G *)
fun int_mp th = zero_var_indexes ((int_unlift th) RS mp);

(* F .-> G   becomes   [| w |= F; w |= G ==> R |] ==> R 
   so that it can be used as an elimination rule
*)
fun int_impE th = zero_var_indexes ((int_unlift th) RS impE);

(* F .& G .-> H  becomes  [| w |= F; w |= G |] ==> w |= H *)
fun int_conjmp th = zero_var_indexes (conjI RS (int_mp th));

(* F .& G .-> H  becomes  [| w |= F; w |= G; (w |= H ==> R) |] ==> R *)
fun int_conjimpE th = zero_var_indexes (conjI RS (int_impE th));

(* Turn  F .= G  into meta-level rewrite rule  F == G *)
fun int_rewrite th = (rewrite_rule intensional_rews (th RS inteq_reflection));

(* Make the simplifier accept "intensional" goals by first unlifting them.
   This is the standard way of proving "intensional" theorems; apply
   int_rewrite (or action_rewrite, temp_rewrite) to convert "x .= y" into "x == y"
   if you want to rewrite without unlifting.
*)
fun maybe_unlift th =
    (case concl_of th of
	 Const("TrueInt",_) $ p => int_unlift th
       | _ => th);

simpset := !simpset setmksimps ((mksimps mksimps_pairs) o maybe_unlift);


(* ==================== Rewrites for abstractions ==================== *)

(* The following are occasionally useful. Don't add them to the default
   simpset, or it will loop! Alternatively, we could replace the "unl_XXX"
   rules by definitions of lifting via lambda abstraction, but then proof
   states would have lots of lambdas, and would be hard to read.
*)

qed_goal "con_abs" Intensional.thy "(%w. c) == #c"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift_abs" Intensional.thy "(%w. f(x w)) == (f[x])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift2_abs" Intensional.thy "(%w. f(x w) (y w)) == (f[x,y])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift2_abs_con1" Intensional.thy "(%w. f x (y w)) == (f[#x,y])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift2_abs_con2" Intensional.thy "(%w. f(x w) y) == (f[x,#y])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift3_abs" Intensional.thy "(%w. f(x w) (y w) (z w)) == (f[x,y,z])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift3_abs_con1" Intensional.thy "(%w. f x (y w) (z w)) == (f[#x,y,z])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift3_abs_con2" Intensional.thy "(%w. f (x w) y (z w)) == (f[x,#y,z])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift3_abs_con3" Intensional.thy "(%w. f (x w) (y w) z) == (f[x,y,#z])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift3_abs_con12" Intensional.thy "(%w. f x y (z w)) == (f[#x,#y,z])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift3_abs_con13" Intensional.thy "(%w. f x (y w) z) == (f[#x,y,#z])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

qed_goal "lift3_abs_con23" Intensional.thy "(%w. f (x w) y z) == (f[x,#y,#z])"
  (fn _ => [rtac inteq_reflection 1,
            rtac intI 1,
            rewrite_goals_tac intensional_rews,
            rtac refl 1
           ]);

(* ========================================================================= *)

qed_goal "Not_rall" Intensional.thy
   "(.~ (RALL x. F(x))) .= (REX x. .~ F(x))"
   (fn _ => [rtac intI 1,
	     rewrite_goals_tac intensional_rews,
	     fast_tac HOL_cs 1
	    ]);

qed_goal "Not_rex" Intensional.thy
   "(.~ (REX x. F(x))) .= (RALL x. .~ F(x))"
   (fn _ => [rtac intI 1,
	     rewrite_goals_tac intensional_rews,
	     fast_tac HOL_cs 1
	    ]);

(* IntLemmas.ML contains a collection of further lemmas about "intensional" logic.
   These are not loaded by default because they are not required for the
   standard proof procedures that first unlift proof goals to the HOL level.

use "IntLemmas.ML";

*)
