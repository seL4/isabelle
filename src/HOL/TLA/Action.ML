(* 
    File:	 Action.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

Lemmas and tactics for TLA actions.
*)

(* The following assertion specializes "intI" for any world type 
   which is a pair, not just for "state * state".
*)
val [prem] = goal thy "(!!s t. (s,t) |= A) ==> |- A";
by (REPEAT (resolve_tac [prem,intI,prod_induct] 1));
qed "actionI";

Goal "|- A ==> (s,t) |= A";
by (etac intD 1);
qed "actionD";

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

AddSIs [actionI];
AddDs  [actionD];

(* =========================== square / angle brackets =========================== *)

Goalw [square_def] "(s,t) |= unchanged v ==> (s,t) |= [A]_v";
by (Asm_full_simp_tac 1);
qed "idle_squareI";

Goalw [square_def] "(s,t) |= A ==> (s,t) |= [A]_v";
by (Asm_simp_tac 1);
qed "busy_squareI";

val prems = goal thy
  "[| (s,t) |= [A]_v; A (s,t) ==> B (s,t); v t = v s ==> B (s,t) |] ==> B (s,t)";
by (cut_facts_tac prems 1);
by (rewrite_goals_tac (square_def::action_rews));
by (etac disjE 1);
by (REPEAT (eresolve_tac prems 1));
qed "squareE";

val prems = goalw thy (square_def::action_rews)
  "[| v t ~= v s ==> A (s,t) |] ==> (s,t) |= [A]_v";
by (rtac disjCI 1);
by (eresolve_tac prems 1);
qed "squareCI";

goalw thy [angle_def]
  "!!s t. [| A (s,t); v t ~= v s |] ==> (s,t) |= <A>_v";
by (Asm_simp_tac 1);
qed "angleI";

val prems = goalw thy (angle_def::action_rews)
  "[| (s,t) |= <A>_v; [| A (s,t); v t ~= v s |] ==> R |] ==> R";
by (cut_facts_tac prems 1);
by (etac conjE 1);
by (REPEAT (ares_tac prems 1));
qed "angleE";

AddIs [angleI, squareCI];
AddEs [angleE, squareE];

goal thy
   "!!f. [| |- unchanged f & ~B --> unchanged g;   \
\           |- A & ~unchanged g --> B              \
\        |] ==> |- [A]_f --> [B]_g";
by (Clarsimp_tac 1);
by (etac squareE 1);
by (auto_tac (claset(), simpset() addsimps [square_def]));
qed "square_simulation";

goalw thy [square_def,angle_def]
   "|- (~ [A]_v) = <~A>_v";
by Auto_tac;
qed "not_square";

goalw thy [square_def,angle_def]
   "|- (~ <A>_v) = [~A]_v";
by Auto_tac;
qed "not_angle";

(* ============================== Facts about ENABLED ============================== *)

goal thy "|- A --> $Enabled A";
by (auto_tac (claset(), simpset() addsimps [enabled_def]));
qed "enabledI";

val prems = goalw thy [enabled_def]
  "[| s |= Enabled A; !!u. A (s,u) ==> Q |] ==> Q";
by (cut_facts_tac prems 1);
by (etac exE 1);
by (resolve_tac prems 1);
by (atac 1);
qed "enabledE";

goal thy "|- ~$Enabled G --> ~ G";
by (auto_tac (claset(), simpset() addsimps [enabled_def]));
qed "notEnabledD";

(* Monotonicity *)
val [min,maj] = goal thy
  "[| s |= Enabled F; |- F --> G |] ==> s |= Enabled G";
by (rtac (min RS enabledE) 1);
by (rtac (action_use enabledI) 1);
by (etac (action_use maj) 1);
qed "enabled_mono";

(* stronger variant *)
val [min,maj] = goal thy
  "[| s |= Enabled F; !!t. F (s,t) ==> G (s,t) |] ==> s |= Enabled G";
by (rtac (min RS enabledE) 1);
by (rtac (action_use enabledI) 1);
by (etac maj 1);
qed "enabled_mono2";

goal thy "|- Enabled F --> Enabled (F | G)";
by (auto_tac (claset() addSEs [enabled_mono], simpset()));
qed "enabled_disj1";

goal thy "|- Enabled G --> Enabled (F | G)";
by (auto_tac (claset() addSEs [enabled_mono], simpset()));
qed "enabled_disj2";

goal thy "|- Enabled (F & G) --> Enabled F";
by (auto_tac (claset() addSEs [enabled_mono], simpset()));
qed "enabled_conj1";

goal thy "|- Enabled (F & G) --> Enabled G";
by (auto_tac (claset() addSEs [enabled_mono], simpset()));
qed "enabled_conj2";

val prems = goal thy
  "[| s |= Enabled (F & G); [| s |= Enabled F; s |= Enabled G |] ==> Q |] ==> Q";
by (cut_facts_tac prems 1);
by (resolve_tac prems 1);
by (etac (action_use enabled_conj1) 1);
by (etac (action_use enabled_conj2) 1);
qed "enabled_conjE";

goal thy "|- Enabled (F | G) --> Enabled F | Enabled G";
by (auto_tac (claset(), simpset() addsimps [enabled_def]));
qed "enabled_disjD";

goal thy "|- Enabled (F | G) = (Enabled F | Enabled G)";
by (Clarsimp_tac 1);
by (rtac iffI 1);
by (etac (action_use enabled_disjD) 1);
by (REPEAT (eresolve_tac (disjE::map action_use [enabled_disj1,enabled_disj2]) 1));
qed "enabled_disj";

goal thy "|- Enabled (EX x. F x) = (EX x. Enabled (F x))";
by (force_tac (claset(), simpset() addsimps [enabled_def]) 1);
qed "enabled_ex";


(* A rule that combines enabledI and baseE, but generates fewer instantiations *)
val prems = goal thy
  "[| basevars vs; EX c. ! u. vs u = c --> A(s,u) |] ==> s |= Enabled A";
by (cut_facts_tac prems 1);
by (etac exE 1);
by (etac baseE 1);
by (rtac (action_use enabledI) 1);
by (etac allE 1);
by (etac mp 1);
by (atac 1);
qed "base_enabled";

(* ======================= action_simp_tac ============================== *)

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

fun enabled_tac base_vars =
    clarsimp_tac (claset() addSIs [base_vars RS base_enabled], simpset());

(* Example:

val [prem] = goal thy "basevars (x,y,z) ==> |- x --> Enabled ($x & (y$ = #False))";
by (enabled_tac prem 1);
by Auto_tac;

*)
