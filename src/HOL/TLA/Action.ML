(* 
    File:	 Action.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

Lemmas and tactics for TLA actions.
*)

(* The following assertion specializes "intI" for any world type 
   which is a pair, not just for "state * state".
*)
qed_goal "actionI" Action.thy "(!!s t. (s,t) |= A) ==> |- A"
  (fn [prem] => [REPEAT (resolve_tac [prem,intI,prod_induct] 1)]);

qed_goal "actionD" Action.thy "|- A ==> (s,t) |= A"
  (fn [prem] => [rtac (prem RS intD) 1]);

local
  fun prover s = prove_goal Action.thy s 
                    (fn _ => [rtac actionI 1, 
                              rewrite_goals_tac (unl_after::intensional_rews),
                              rtac refl 1])
in
  val pr_rews = map (int_rewrite o prover)
    [ "|- (#c)` = #c",
      "|- f<x>` = f<x`>",
      "|- f<x,y>` = f<x`,y`>",
      "|- f<x,y,z>` = f<x`,y`,z`>",
      "|- (! x. P x)` = (! x. (P x)`)",
      "|- (? x. P x)` = (? x. (P x)`)"
    ]
end;

val act_rews = [unl_before,unl_after,unchanged_def] @ pr_rews;
Addsimps act_rews;

val action_rews = act_rews @ intensional_rews;

(* ================ Functions to "unlift" action theorems into HOL rules ================ *)

(* The following functions are specialized versions of the corresponding
   functions defined in Intensional.ML in that they introduce a
   "world" parameter of the form (s,t) and apply additional rewrites.
*)
fun action_unlift th = 
    (rewrite_rule action_rews (th RS actionD)) 
    handle _ => int_unlift th;

(* Turn  |- A = B  into meta-level rewrite rule  A == B *)
val action_rewrite = int_rewrite;

fun action_use th =
    case (concl_of th) of
      Const _ $ (Const ("Intensional.Valid", _) $ _) =>
              ((flatten (action_unlift th)) handle _ => th)
    | _ => th;

(* ===================== Update simpset and classical prover ============================= *)

(***
(* Make the simplifier use action_use rather than int_use
   when action simplifications are added.
*)

let
  val ss = simpset_ref()
  fun try_rewrite th = 
      (action_rewrite th) handle _ => (action_use th) handle _ => th
in
  ss := !ss setmksimps ((mksimps mksimps_pairs) o try_rewrite)
end;
***)

AddSIs [actionI];
AddDs  [actionD];

(* =========================== square / angle brackets =========================== *)

qed_goalw "idle_squareI" Action.thy [square_def]
   "!!s t. (s,t) |= unchanged v ==> (s,t) |= [A]_v"
   (fn _ => [ Asm_full_simp_tac 1 ]);

qed_goalw "busy_squareI" Action.thy [square_def]
   "!!s t. (s,t) |= A ==> (s,t) |= [A]_v"
   (fn _ => [ Asm_simp_tac 1 ]);

qed_goal "squareE" Action.thy
  "[| (s,t) |= [A]_v; A (s,t) ==> B (s,t); v t = v s ==> B (s,t) |] ==> B (s,t)"
  (fn prems => [cut_facts_tac prems 1,
                rewrite_goals_tac (square_def::action_rews),
                etac disjE 1,
                REPEAT (eresolve_tac prems 1)]);

qed_goalw "squareCI" Action.thy (square_def::action_rews)
  "[| v t ~= v s ==> A (s,t) |] ==> (s,t) |= [A]_v"
  (fn prems => [rtac disjCI 1,
                eresolve_tac prems 1]);

qed_goalw "angleI" Action.thy [angle_def]
  "!!s t. [| A (s,t); v t ~= v s |] ==> (s,t) |= <A>_v"
  (fn _ => [ Asm_simp_tac 1 ]);

qed_goalw "angleE" Action.thy (angle_def::action_rews)
  "[| (s,t) |= <A>_v; [| A (s,t); v t ~= v s |] ==> R |] ==> R"
  (fn prems => [cut_facts_tac prems 1,
                etac conjE 1,
                REPEAT (ares_tac prems 1)]);

AddIs [angleI, squareCI];
AddEs [angleE, squareE];

qed_goal "square_simulation" Action.thy
   "!!f. [| |- unchanged f & ~B --> unchanged g;   \
\           |- A & ~unchanged g --> B              \
\        |] ==> |- [A]_f --> [B]_g"
   (fn _ => [Clarsimp_tac 1,
             etac squareE 1,
             auto_tac (claset(), simpset() addsimps [square_def])
            ]);

qed_goalw "not_square" Action.thy [square_def,angle_def]
   "|- (~ [A]_v) = <~A>_v"
   (fn _ => [ Auto_tac ]);

qed_goalw "not_angle" Action.thy [square_def,angle_def]
   "|- (~ <A>_v) = [~A]_v"
   (fn _ => [ Auto_tac ]);

(* ============================== Facts about ENABLED ============================== *)

qed_goal "enabledI" Action.thy
  "|- A --> $Enabled A"
  (fn _ => [ auto_tac (claset(), simpset() addsimps [enabled_def]) ]);

qed_goalw "enabledE" Action.thy [enabled_def]
  "[| s |= Enabled A; !!u. A (s,u) ==> Q |] ==> Q"
  (fn prems => [cut_facts_tac prems 1,
                etac exE 1,
                resolve_tac prems 1, atac 1
               ]);

qed_goal "notEnabledD" Action.thy
  "|- ~$Enabled G --> ~ G"
  (fn _ => [ auto_tac (claset(), simpset() addsimps [enabled_def]) ]);

(* Monotonicity *)
qed_goal "enabled_mono" Action.thy
  "[| s |= Enabled F; |- F --> G |] ==> s |= Enabled G"
  (fn [min,maj] => [rtac (min RS enabledE) 1,
                    rtac (action_use enabledI) 1,
                    etac (action_use maj) 1
                   ]);

(* stronger variant *)
qed_goal "enabled_mono2" Action.thy
   "[| s |= Enabled F; !!t. F (s,t) ==> G (s,t) |] ==> s |= Enabled G"
   (fn [min,maj] => [rtac (min RS enabledE) 1,
		     rtac (action_use enabledI) 1,
		     etac maj 1
		    ]);

qed_goal "enabled_disj1" Action.thy
  "|- Enabled F --> Enabled (F | G)"
  (fn _ => [ auto_tac (claset() addSEs [enabled_mono], simpset()) ]);

qed_goal "enabled_disj2" Action.thy
  "|- Enabled G --> Enabled (F | G)"
  (fn _ => [ auto_tac (claset() addSEs [enabled_mono], simpset()) ]);

qed_goal "enabled_conj1" Action.thy
  "|- Enabled (F & G) --> Enabled F"
  (fn _ => [ auto_tac (claset() addSEs [enabled_mono], simpset()) ]);

qed_goal "enabled_conj2" Action.thy
  "|- Enabled (F & G) --> Enabled G"
  (fn _ => [ auto_tac (claset() addSEs [enabled_mono], simpset()) ]);

qed_goal "enabled_conjE" Action.thy
  "[| s |= Enabled (F & G); [| s |= Enabled F; s |= Enabled G |] ==> Q |] ==> Q"
  (fn prems => [cut_facts_tac prems 1, resolve_tac prems 1,
                etac (action_use enabled_conj1) 1, 
		etac (action_use enabled_conj2) 1
	       ]);

qed_goal "enabled_disjD" Action.thy
  "|- Enabled (F | G) --> Enabled F | Enabled G"
  (fn _ => [ auto_tac (claset(), simpset() addsimps [enabled_def]) ]);

qed_goal "enabled_disj" Action.thy
  "|- Enabled (F | G) = (Enabled F | Enabled G)"
  (fn _ => [Clarsimp_tac 1,
	    rtac iffI 1,
            etac (action_use enabled_disjD) 1,
            REPEAT (eresolve_tac (disjE::map action_use [enabled_disj1,enabled_disj2]) 1)
           ]);

qed_goal "enabled_ex" Action.thy
  "|- Enabled (? x. F x) = (? x. Enabled (F x))"
  (fn _ => [ force_tac (claset(), simpset() addsimps [enabled_def]) 1 ]);


(* A rule that combines enabledI and baseE, but generates fewer possible instantiations *)
qed_goal "base_enabled" Action.thy
  "[| basevars vs; !!u. vs u = c s ==> A (s,u) |] ==> s |= Enabled A"
  (fn prems => [cut_facts_tac prems 1,
		etac baseE 1, rtac (action_use enabledI) 1,
		REPEAT (ares_tac prems 1)]);


(* ================================ action_simp_tac ================================== *)

(* A dumb simplification-based tactic with just a little first-order logic:
   should plug in only "very safe" rules that can be applied blindly.
   Note that it applies whatever simplifications are currently active.
*)
fun action_simp_tac ss intros elims =
    asm_full_simp_tac 
         (ss setloop ((resolve_tac ((map action_use intros)
                                    @ [refl,impI,conjI,actionI,intI,allI]))
		      ORELSE' (eresolve_tac ((map action_use elims) 
                                             @ [conjE,disjE,exE]))));

(* default version without additional plug-in rules *)
val Action_simp_tac = action_simp_tac (simpset()) [] [];



(* ---------------- enabled_tac: tactic to prove (Enabled A) -------------------- *)
(* "Enabled A" can be proven as follows:
   - Assume that we know which state variables are "base variables";
     this should be expressed by a theorem of the form "basevars (x,y,z,...)".
   - Resolve this theorem with baseE to introduce a constant for the value of the
     variables in the successor state, and resolve the goal with the result.
   - Resolve with enabledI and do some rewriting.
   - Solve for the unknowns using standard HOL reasoning.
   The following tactic combines these steps except the final one.
*)
(*** old version
fun enabled_tac base_vars i =
    EVERY [(* apply actionI (plus rewriting) if the goal is of the form $(Enabled A),
	      do nothing if it is of the form s |= Enabled A *)
	   TRY ((resolve_tac [actionI,intI] i) 
                THEN (SELECT_GOAL (rewrite_goals_tac action_rews) i)),
	   clarify_tac (claset() addSIs [base_vars RS base_enabled]) i,
	   (SELECT_GOAL (rewrite_goals_tac action_rews) i)
	  ];
***)

fun enabled_tac base_vars =
    clarsimp_tac (claset() addSIs [base_vars RS base_enabled], simpset());

(* Example:

val [prem] = goal thy "basevars (x,y,z) ==> |- x --> Enabled ($x & (y$ = #False))";
by (enabled_tac prem 1);
by Auto_tac;

*)
