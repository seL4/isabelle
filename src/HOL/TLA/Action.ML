(* 
    File:	 Action.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

Lemmas and tactics for TLA actions.
*)

val act_rews = [pairSF_def RS eq_reflection,unl_before,unl_after,unchanged_def,
                pr_con,pr_before,pr_lift,pr_lift2,pr_lift3,pr_all,pr_ex];

val action_rews = act_rews @ intensional_rews;

qed_goal "actionI" Action.thy "(!!s t. ([[s,t]] |= A)) ==> A"
  (fn [prem] => [REPEAT (resolve_tac [prem,intI,state2_ext] 1)]);

qed_goal "actionD" Action.thy "A ==> ([[s,t]] |= A)"
  (fn [prem] => [REPEAT (resolve_tac [prem,intD] 1)]);



(* ================ Functions to "unlift" action theorems into HOL rules ================ *)

(* Basic unlifting introduces a world parameter and applies basic rewrites, e.g.
   A .= B    gets   ([[s,t]] |= A) = ([[s,t]] |= B)
   A .-> B   gets   ([[s,t]] |= A) --> ([[s,t]] |= B)
*)
fun action_unlift th = rewrite_rule action_rews (th RS actionD);

(* A .-> B   becomes   A [[s,t]] ==> B [[s,t]] *)
fun action_mp th = zero_var_indexes ((action_unlift th) RS mp);

(* A .-> B   becomes   [| A[[s,t]]; B[[s,t]] ==> R |] ==> R 
   so that it can be used as an elimination rule
*)
fun action_impE th = zero_var_indexes ((action_unlift th) RS impE);

(* A .& B .-> C  becomes  [| A[[s,t]]; B[[s,t]] |] ==> C[[s,t]] *)
fun action_conjmp th = zero_var_indexes (conjI RS (action_mp th));

(* A .& B .-> C  becomes  [| A[[s,t]]; B[[s,t]]; (C[[s,t]] ==> R) |] ==> R *)
fun action_conjimpE th = zero_var_indexes (conjI RS (action_impE th));

(* Turn  A .= B  into meta-level rewrite rule  A == B *)
fun action_rewrite th = (rewrite_rule action_rews (th RS inteq_reflection));

(* ===================== Update simpset and classical prover ============================= *)

(* Make the simplifier use action_unlift rather than int_unlift 
   when action simplifications are added.
*)
fun maybe_unlift th =
    (case concl_of th of
         Const("Intensional.TrueInt",_) $ p 
           => (action_unlift th
                  handle _ => int_unlift th)
       | _ => th);

simpset_ref() := simpset() setmksimps ((mksimps mksimps_pairs) o maybe_unlift);

(* make act_rews be always active -- intensional_rews has been added before *)
Addsimps act_rews;

use "cladata.ML";        (* local version! *)

(* ================================ action_simp_tac ================================== *)

(* A dumb simplification tactic with just a little first-order logic:
   should plug in only "very safe" rules that can be applied blindly.
   Note that it applies whatever simplifications are currently active.
*)
fun action_simp_tac ss intros elims i =
    (asm_full_simp_tac 
         (ss setloop ((resolve_tac (intros @ [refl,impI,conjI,actionI,allI]))
		      ORELSE' (eresolve_tac (elims @ [conjE,disjE,exE_prop]))))
         i);
(* default version without additional plug-in rules *)
fun Action_simp_tac i = (action_simp_tac (simpset()) [] [] i);


(* ==================== Simplification of abstractions ==================== *)

(* Somewhat obscure simplifications, rarely necessary to get rid
   of abstractions that may be introduced by higher-order unification.
*)

qed_goal "pr_con_abs" Action.thy "(%w. c)` .= #c"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac (con_abs::action_rews),
            rtac refl 1
           ]);

qed_goal "pr_lift_abs" Action.thy "(%w. f(x w))` .= f[x`]"
  (fn _ => [rtac actionI 1,
              (* give all rewrites to the engine and it loops! *)
            rewrite_goals_tac intensional_rews,
            rewtac lift_abs,
            rewtac pr_lift,
            rewtac unl_lift,
            rtac refl 1
           ]);

qed_goal "pr_lift2_abs" Action.thy "(%w. f(x w) (y w))` .= f[x`,y`]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift2_abs,
            rewtac pr_lift2,
            rewtac unl_lift2,
            rtac refl 1
           ]);

qed_goal "pr_lift2_abs_con1" Action.thy "(%w. f x (y w))` .= f[#x, y`]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift2_abs_con1,
            rewtac pr_lift2,
            rewtac unl_lift2,
            rewtac pr_con,
            rewtac unl_con,
            rtac refl 1
           ]);

qed_goal "pr_lift2_abs_con2" Action.thy "(%w. f (x w) y)` .= f[x`, #y]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift2_abs_con2,
            rewtac pr_lift2,
            rewtac unl_lift2,
            rewtac pr_con,
            rewtac unl_con,
            rtac refl 1
           ]);

qed_goal "pr_lift3_abs" Action.thy "(%w. f(x w) (y w) (z w))` .= f[x`,y`,z`]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift3_abs,
            rewtac pr_lift3,
            rewtac unl_lift3,
            rtac refl 1
           ]);

qed_goal "pr_lift3_abs_con1" Action.thy "(%w. f x (y w) (z w))` .= f[#x, y`, z`]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift3_abs_con1,
            rewtac pr_lift3,
            rewtac unl_lift3,
            rewtac pr_con,
            rewtac unl_con,
            rtac refl 1
           ]);

qed_goal "pr_lift3_abs_con2" Action.thy "(%w. f (x w) y (z w))` .= f[x`, #y, z`]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift3_abs_con2,
            rewtac pr_lift3,
            rewtac unl_lift3,
            rewtac pr_con,
            rewtac unl_con,
            rtac refl 1
           ]);

qed_goal "pr_lift3_abs_con3" Action.thy "(%w. f (x w) (y w) z)` .= f[x`, y`, #z]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift3_abs_con3,
            rewtac pr_lift3,
            rewtac unl_lift3,
            rewtac pr_con,
            rewtac unl_con,
            rtac refl 1
           ]);

qed_goal "pr_lift3_abs_con12" Action.thy "(%w. f x y (z w))` .= f[#x, #y, z`]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift3_abs_con12,
            rewtac pr_lift3,
            rewtac unl_lift3,
            rewtac pr_con,
            rewtac unl_con,
            rtac refl 1
           ]);

qed_goal "pr_lift3_abs_con13" Action.thy "(%w. f x (y w) z)` .= f[#x, y`, #z]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift3_abs_con13,
            rewtac pr_lift3,
            rewtac unl_lift3,
            rewtac pr_con,
            rewtac unl_con,
            rtac refl 1
           ]);

qed_goal "pr_lift3_abs_con23" Action.thy "(%w. f (x w) y z)` .= f[x`, #y, #z]"
  (fn _ => [rtac actionI 1,
            rewrite_goals_tac intensional_rews,
            rewtac lift3_abs_con23,
            rewtac pr_lift3,
            rewtac unl_lift3,
            rewtac pr_con,
            rewtac unl_con,
            rtac refl 1
           ]);

(* We don't add these as default rewrite rules, because they are
   rarely needed and may slow down automatic proofs.
*)
val pr_abs_rews = map (fn th => th RS inteq_reflection) 
                      [pr_con_abs,
                       pr_lift_abs,pr_lift2_abs,pr_lift2_abs_con1,pr_lift2_abs_con2,
                       pr_lift3_abs,pr_lift3_abs_con1,pr_lift3_abs_con2,pr_lift3_abs_con3,
                       pr_lift3_abs_con12,pr_lift3_abs_con13,pr_lift3_abs_con23];

(* =========================== square / angle brackets =========================== *)

qed_goalw "idle_squareI" Action.thy [square_def]
   "!!s t. ([[s,t]] |= unchanged v) ==> ([[s,t]] |= [A]_v)"
   (fn _ => [ Auto_tac ]);

qed_goalw "busy_squareI" Action.thy [square_def]
   "!!s t. ([[s,t]] |= A) ==> ([[s,t]] |= [A]_v)"
   (fn _ => [ Auto_tac ]);

qed_goalw "square_simulation" Action.thy [square_def]
   "[| unchanged f .& .~B .-> unchanged g;   \
\      A .& .~unchanged g .-> B              \
\   |] ==> [A]_f .-> [B]_g"
   (fn [p1,p2] => [Auto_tac,
                   etac (action_conjimpE p2) 1,
                   etac swap 3, etac (action_conjimpE p1) 3,
                   ALLGOALS atac
                  ]);
                   
qed_goalw "not_square" Action.thy [square_def,angle_def]
   "(.~ [A]_v) .= <.~A>_v"
   (fn _ => [ Auto_tac ]);

qed_goalw "not_angle" Action.thy [square_def,angle_def]
   "(.~ <A>_v) .= [.~A]_v"
   (fn _ => [ Auto_tac ]);

(* ============================== Facts about ENABLED ============================== *)

qed_goalw "enabledI" Action.thy [enabled_def]
  "A [[s,t]] ==> (Enabled A) s"
  (fn prems => [ REPEAT (resolve_tac (exI::prems) 1) ]);

qed_goalw "enabledE" Action.thy [enabled_def]
  "[| (Enabled A) s; !!u. A[[s,u]] ==> PROP R |] ==> PROP R"
  (fn prems => [cut_facts_tac prems 1,
                etac exE_prop 1,
                resolve_tac prems 1, atac 1
               ]);

qed_goal "notEnabledD" Action.thy
  "!!G. ~ (Enabled G s) ==> ~ G [[s,t]]"
  (fn _ => [ auto_tac (action_css addsimps2 [enabled_def]) ]);

(* Monotonicity *)
qed_goal "enabled_mono" Action.thy
  "[| (Enabled F) s; F .-> G |] ==> (Enabled G) s"
  (fn [min,maj] => [rtac (min RS enabledE) 1,
                    rtac enabledI 1,
                    etac (action_mp maj) 1
                   ]);

(* stronger variant *)
qed_goal "enabled_mono2" Action.thy
   "[| (Enabled F) s; !!t. (F [[s,t]] ==> G[[s,t]] ) |] ==> (Enabled G) s"
   (fn [min,maj] => [rtac (min RS enabledE) 1,
		     rtac enabledI 1,
		     etac maj 1
		    ]);

qed_goal "enabled_disj1" Action.thy
  "!!s. (Enabled F) s ==> (Enabled (F .| G)) s"
  (fn _ => [etac enabled_mono 1, Auto_tac
	   ]);

qed_goal "enabled_disj2" Action.thy
  "!!s. (Enabled G) s ==> (Enabled (F .| G)) s"
  (fn _ => [etac enabled_mono 1, Auto_tac
	   ]);

qed_goal "enabled_conj1" Action.thy
  "!!s. (Enabled (F .& G)) s ==> (Enabled F) s"
  (fn _ => [etac enabled_mono 1, Auto_tac
           ]);

qed_goal "enabled_conj2" Action.thy
  "!!s. (Enabled (F .& G)) s ==> (Enabled G) s"
  (fn _ => [etac enabled_mono 1, Auto_tac
           ]);

qed_goal "enabled_conjE" Action.thy
  "[| (Enabled (F .& G)) s; [| (Enabled F) s; (Enabled G) s |] ==> PROP R |] ==> PROP R"
  (fn prems => [cut_facts_tac prems 1, resolve_tac prems 1,
                etac enabled_conj1 1, etac enabled_conj2 1]);

qed_goal "enabled_disjD" Action.thy
  "!!s. (Enabled (F .| G)) s ==> ((Enabled F) s) | ((Enabled G) s)"
  (fn _ => [etac enabledE 1,
            auto_tac (action_css addSDs2 [notEnabledD] addSEs2 [enabledI])
           ]);

qed_goal "enabled_disj" Action.thy
  "(Enabled (F .| G)) s = ( (Enabled F) s | (Enabled G) s )"
  (fn _ => [rtac iffI 1,
            etac enabled_disjD 1,
            REPEAT (eresolve_tac [disjE,enabled_disj1,enabled_disj2] 1)
           ]);

qed_goal "enabled_ex" Action.thy
  "(Enabled (REX x. F x)) s = (EX x. (Enabled (F x)) s)"
  (fn _ => [ auto_tac (action_css addsimps2 [enabled_def]) ]);
	    

(* A rule that combines enabledI and baseE, but generates fewer possible instantiations *)
qed_goal "base_enabled" Action.thy
  "[| base_var(v); !!u. v u = c s ==> A [[s,u]] |] ==> Enabled A s"
  (fn prems => [cut_facts_tac prems 1,
		etac baseE 1, rtac enabledI 1,
		REPEAT (ares_tac prems 1)]);


(* ---------------- enabled_tac: tactic to prove (Enabled A) -------------------- *)
(* "Enabled A" can be proven as follows:
   - Assume that we know which state variables are "base variables";
     this should be expressed by a theorem of the form "base_var <x,y,z,...>".
   - Resolve this theorem with baseE to introduce a constant for the value of the
     variables in the successor state, and resolve the goal with the result.
   - E-resolve with PairVarE so that we have one constant per variable.
   - Resolve with enabledI and do some rewriting.
   - Solve for the unknowns using standard HOL reasoning.
   The following tactic combines these steps except the final one.
*)

fun enabled_tac base_vars i =
    EVERY [(* apply actionI (plus rewriting) if the goal is of the form $(Enabled A),
	      do nothing if it is of the form (Enabled A) s *)
	   TRY ((rtac actionI i) THEN (SELECT_GOAL (rewrite_goals_tac action_rews) i)),
	   rtac (base_vars RS base_enabled) i,
	   REPEAT_DETERM (etac PairVarE i),
	   (SELECT_GOAL (rewrite_goals_tac action_rews) i)
	  ];

(* Example of use:

val [prem] = goal Action.thy "base_var <x,y,z> ==> $x .-> $Enabled ($x .& (y$ .= #False))";
by (REPEAT ((CHANGED (Action_simp_tac 1)) ORELSE (enabled_tac prem 1)));

*)
