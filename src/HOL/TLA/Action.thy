(*  Title:      HOL/TLA/Action.thy 
    Author:     Stephan Merz
    Copyright:  1998 University of Munich
*)

header {* The action level of TLA as an Isabelle theory *}

theory Action
imports Stfun
begin


(** abstract syntax **)

type_synonym 'a trfun = "(state * state) => 'a"
type_synonym action   = "bool trfun"

arities prod :: (world, world) world

consts
  (** abstract syntax **)
  before        :: "'a stfun => 'a trfun"
  after         :: "'a stfun => 'a trfun"
  unch          :: "'a stfun => action"

  SqAct         :: "[action, 'a stfun] => action"
  AnAct         :: "[action, 'a stfun] => action"
  enabled       :: "action => stpred"

(** concrete syntax **)

syntax
  (* Syntax for writing action expressions in arbitrary contexts *)
  "_ACT"        :: "lift => 'a"                      ("(ACT _)")

  "_before"     :: "lift => lift"                    ("($_)"  [100] 99)
  "_after"      :: "lift => lift"                    ("(_$)"  [100] 99)
  "_unchanged"  :: "lift => lift"                    ("(unchanged _)" [100] 99)

  (*** Priming: same as "after" ***)
  "_prime"      :: "lift => lift"                    ("(_`)" [100] 99)

  "_SqAct"      :: "[lift, lift] => lift"            ("([_]'_(_))" [0,1000] 99)
  "_AnAct"      :: "[lift, lift] => lift"            ("(<_>'_(_))" [0,1000] 99)
  "_Enabled"    :: "lift => lift"                    ("(Enabled _)" [100] 100)

translations
  "ACT A"            =>   "(A::state*state => _)"
  "_before"          ==   "CONST before"
  "_after"           ==   "CONST after"
  "_prime"           =>   "_after"
  "_unchanged"       ==   "CONST unch"
  "_SqAct"           ==   "CONST SqAct"
  "_AnAct"           ==   "CONST AnAct"
  "_Enabled"         ==   "CONST enabled"
  "w |= [A]_v"       <=   "_SqAct A v w"
  "w |= <A>_v"       <=   "_AnAct A v w"
  "s |= Enabled A"   <=   "_Enabled A s"
  "w |= unchanged f" <=   "_unchanged f w"

axiomatization where
  unl_before:    "(ACT $v) (s,t) == v s" and
  unl_after:     "(ACT v$) (s,t) == v t" and

  unchanged_def: "(s,t) |= unchanged v == (v t = v s)"

defs
  square_def:    "ACT [A]_v == ACT (A | unchanged v)"
  angle_def:     "ACT <A>_v == ACT (A & ~ unchanged v)"

  enabled_def:   "s |= Enabled A  ==  EX u. (s,u) |= A"


(* The following assertion specializes "intI" for any world type
   which is a pair, not just for "state * state".
*)

lemma actionI [intro!]:
  assumes "!!s t. (s,t) |= A"
  shows "|- A"
  apply (rule assms intI prod.induct)+
  done

lemma actionD [dest]: "|- A ==> (s,t) |= A"
  apply (erule intD)
  done

lemma pr_rews [int_rewrite]:
  "|- (#c)` = #c"
  "!!f. |- f<x>` = f<x` >"
  "!!f. |- f<x,y>` = f<x`,y` >"
  "!!f. |- f<x,y,z>` = f<x`,y`,z` >"
  "|- (! x. P x)` = (! x. (P x)`)"
  "|- (? x. P x)` = (? x. (P x)`)"
  by (rule actionI, unfold unl_after intensional_rews, rule refl)+


lemmas act_rews [simp] = unl_before unl_after unchanged_def pr_rews

lemmas action_rews = act_rews intensional_rews


(* ================ Functions to "unlift" action theorems into HOL rules ================ *)

ML {*
(* The following functions are specialized versions of the corresponding
   functions defined in Intensional.ML in that they introduce a
   "world" parameter of the form (s,t) and apply additional rewrites.
*)

fun action_unlift th =
  (rewrite_rule @{thms action_rews} (th RS @{thm actionD}))
    handle THM _ => int_unlift th;

(* Turn  |- A = B  into meta-level rewrite rule  A == B *)
val action_rewrite = int_rewrite

fun action_use th =
    case (concl_of th) of
      Const _ $ (Const ("Intensional.Valid", _) $ _) =>
              (flatten (action_unlift th) handle THM _ => th)
    | _ => th;
*}

attribute_setup action_unlift = {* Scan.succeed (Thm.rule_attribute (K action_unlift)) *}
attribute_setup action_rewrite = {* Scan.succeed (Thm.rule_attribute (K action_rewrite)) *}
attribute_setup action_use = {* Scan.succeed (Thm.rule_attribute (K action_use)) *}


(* =========================== square / angle brackets =========================== *)

lemma idle_squareI: "(s,t) |= unchanged v ==> (s,t) |= [A]_v"
  by (simp add: square_def)

lemma busy_squareI: "(s,t) |= A ==> (s,t) |= [A]_v"
  by (simp add: square_def)
  
lemma squareE [elim]:
  "[| (s,t) |= [A]_v; A (s,t) ==> B (s,t); v t = v s ==> B (s,t) |] ==> B (s,t)"
  apply (unfold square_def action_rews)
  apply (erule disjE)
  apply simp_all
  done

lemma squareCI [intro]: "[| v t ~= v s ==> A (s,t) |] ==> (s,t) |= [A]_v"
  apply (unfold square_def action_rews)
  apply (rule disjCI)
  apply (erule (1) meta_mp)
  done

lemma angleI [intro]: "!!s t. [| A (s,t); v t ~= v s |] ==> (s,t) |= <A>_v"
  by (simp add: angle_def)

lemma angleE [elim]: "[| (s,t) |= <A>_v; [| A (s,t); v t ~= v s |] ==> R |] ==> R"
  apply (unfold angle_def action_rews)
  apply (erule conjE)
  apply simp
  done

lemma square_simulation:
   "!!f. [| |- unchanged f & ~B --> unchanged g;    
            |- A & ~unchanged g --> B               
         |] ==> |- [A]_f --> [B]_g"
  apply clarsimp
  apply (erule squareE)
  apply (auto simp add: square_def)
  done

lemma not_square: "|- (~ [A]_v) = <~A>_v"
  by (auto simp: square_def angle_def)

lemma not_angle: "|- (~ <A>_v) = [~A]_v"
  by (auto simp: square_def angle_def)


(* ============================== Facts about ENABLED ============================== *)

lemma enabledI: "|- A --> $Enabled A"
  by (auto simp add: enabled_def)

lemma enabledE: "[| s |= Enabled A; !!u. A (s,u) ==> Q |] ==> Q"
  apply (unfold enabled_def)
  apply (erule exE)
  apply simp
  done

lemma notEnabledD: "|- ~$Enabled G --> ~ G"
  by (auto simp add: enabled_def)

(* Monotonicity *)
lemma enabled_mono:
  assumes min: "s |= Enabled F"
    and maj: "|- F --> G"
  shows "s |= Enabled G"
  apply (rule min [THEN enabledE])
  apply (rule enabledI [action_use])
  apply (erule maj [action_use])
  done

(* stronger variant *)
lemma enabled_mono2:
  assumes min: "s |= Enabled F"
    and maj: "!!t. F (s,t) ==> G (s,t)"
  shows "s |= Enabled G"
  apply (rule min [THEN enabledE])
  apply (rule enabledI [action_use])
  apply (erule maj)
  done

lemma enabled_disj1: "|- Enabled F --> Enabled (F | G)"
  by (auto elim!: enabled_mono)

lemma enabled_disj2: "|- Enabled G --> Enabled (F | G)"
  by (auto elim!: enabled_mono)

lemma enabled_conj1: "|- Enabled (F & G) --> Enabled F"
  by (auto elim!: enabled_mono)

lemma enabled_conj2: "|- Enabled (F & G) --> Enabled G"
  by (auto elim!: enabled_mono)

lemma enabled_conjE:
    "[| s |= Enabled (F & G); [| s |= Enabled F; s |= Enabled G |] ==> Q |] ==> Q"
  apply (frule enabled_conj1 [action_use])
  apply (drule enabled_conj2 [action_use])
  apply simp
  done

lemma enabled_disjD: "|- Enabled (F | G) --> Enabled F | Enabled G"
  by (auto simp add: enabled_def)

lemma enabled_disj: "|- Enabled (F | G) = (Enabled F | Enabled G)"
  apply clarsimp
  apply (rule iffI)
   apply (erule enabled_disjD [action_use])
  apply (erule disjE enabled_disj1 [action_use] enabled_disj2 [action_use])+
  done

lemma enabled_ex: "|- Enabled (EX x. F x) = (EX x. Enabled (F x))"
  by (force simp add: enabled_def)


(* A rule that combines enabledI and baseE, but generates fewer instantiations *)
lemma base_enabled:
    "[| basevars vs; EX c. ! u. vs u = c --> A(s,u) |] ==> s |= Enabled A"
  apply (erule exE)
  apply (erule baseE)
  apply (rule enabledI [action_use])
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done

(* ======================= action_simp_tac ============================== *)

ML {*
(* A dumb simplification-based tactic with just a little first-order logic:
   should plug in only "very safe" rules that can be applied blindly.
   Note that it applies whatever simplifications are currently active.
*)
fun action_simp_tac ss intros elims =
    asm_full_simp_tac
         (ss setloop ((resolve_tac ((map action_use intros)
                                    @ [refl,impI,conjI,@{thm actionI},@{thm intI},allI]))
                      ORELSE' (eresolve_tac ((map action_use elims)
                                             @ [conjE,disjE,exE]))));
*}

(* ---------------- enabled_tac: tactic to prove (Enabled A) -------------------- *)

ML {*
(* "Enabled A" can be proven as follows:
   - Assume that we know which state variables are "base variables"
     this should be expressed by a theorem of the form "basevars (x,y,z,...)".
   - Resolve this theorem with baseE to introduce a constant for the value of the
     variables in the successor state, and resolve the goal with the result.
   - Resolve with enabledI and do some rewriting.
   - Solve for the unknowns using standard HOL reasoning.
   The following tactic combines these steps except the final one.
*)

fun enabled_tac ctxt base_vars =
  clarsimp_tac (ctxt addSIs [base_vars RS @{thm base_enabled}]);
*}

method_setup enabled = {*
  Attrib.thm >> (fn th => fn ctxt => SIMPLE_METHOD' (enabled_tac ctxt th))
*}

(* Example *)

lemma
  assumes "basevars (x,y,z)"
  shows "|- x --> Enabled ($x & (y$ = #False))"
  apply (enabled assms)
  apply auto
  done

end
