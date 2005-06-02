(*  ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge
*)

header{*Weak Safety Properties*}

theory Constrains
imports UNITY

begin
consts traces :: "[i, i] => i"
  (* Initial states and program => (final state, reversed trace to it)... 
      the domain may also be state*list(state) *)
inductive 
  domains 
     "traces(init, acts)" <=
         "(init Un (UN act:acts. field(act)))*list(UN act:acts. field(act))"
  intros 
         (*Initial trace is empty*)
    Init: "s: init ==> <s,[]> : traces(init,acts)"

    Acts: "[| act:acts;  <s,evs> : traces(init,acts);  <s,s'>: act |]
           ==> <s', Cons(s,evs)> : traces(init, acts)"
  
  type_intros list.intros UnI1 UnI2 UN_I fieldI2 fieldI1


consts reachable :: "i=>i"
inductive
  domains
  "reachable(F)" <= "Init(F) Un (UN act:Acts(F). field(act))"
  intros 
    Init: "s:Init(F) ==> s:reachable(F)"

    Acts: "[| act: Acts(F);  s:reachable(F);  <s,s'>: act |]
           ==> s':reachable(F)"

  type_intros UnI1 UnI2 fieldI2 UN_I

  
consts
  Constrains :: "[i,i] => i"  (infixl "Co"     60)
  op_Unless  :: "[i, i] => i"  (infixl "Unless" 60)

defs
  Constrains_def:
    "A Co B == {F:program. F:(reachable(F) Int A) co B}"

  Unless_def:
    "A Unless B == (A-B) Co (A Un B)"

constdefs
  Stable     :: "i => i"
    "Stable(A) == A Co A"
  (*Always is the weak form of "invariant"*)
  Always :: "i => i"
    "Always(A) == initially(A) Int Stable(A)"


(*** traces and reachable ***)

lemma reachable_type: "reachable(F) <= state"
apply (cut_tac F = F in Init_type)
apply (cut_tac F = F in Acts_type)
apply (cut_tac F = F in reachable.dom_subset, blast)
done

lemma st_set_reachable: "st_set(reachable(F))"
apply (unfold st_set_def)
apply (rule reachable_type)
done
declare st_set_reachable [iff]

lemma reachable_Int_state: "reachable(F) Int state = reachable(F)"
by (cut_tac reachable_type, auto)
declare reachable_Int_state [iff]

lemma state_Int_reachable: "state Int reachable(F) = reachable(F)"
by (cut_tac reachable_type, auto)
declare state_Int_reachable [iff]

lemma reachable_equiv_traces: 
"F \<in> program ==> reachable(F)={s \<in> state. \<exists>evs. <s,evs>:traces(Init(F), Acts(F))}"
apply (rule equalityI, safe)
apply (blast dest: reachable_type [THEN subsetD])
apply (erule_tac [2] traces.induct)
apply (erule reachable.induct)
apply (blast intro: reachable.intros traces.intros)+
done

lemma Init_into_reachable: "Init(F) <= reachable(F)"
by (blast intro: reachable.intros)

lemma stable_reachable: "[| F \<in> program; G \<in> program;  
    Acts(G) <= Acts(F)  |] ==> G \<in> stable(reachable(F))"
apply (blast intro: stableI constrainsI st_setI
             reachable_type [THEN subsetD] reachable.intros)
done

declare stable_reachable [intro!]
declare stable_reachable [simp]

(*The set of all reachable states is an invariant...*)
lemma invariant_reachable: 
   "F \<in> program ==> F \<in> invariant(reachable(F))"
apply (unfold invariant_def initially_def)
apply (blast intro: reachable_type [THEN subsetD] reachable.intros)
done

(*...in fact the strongest invariant!*)
lemma invariant_includes_reachable: "F \<in> invariant(A) ==> reachable(F) <= A"
apply (cut_tac F = F in Acts_type)
apply (cut_tac F = F in Init_type)
apply (cut_tac F = F in reachable_type)
apply (simp (no_asm_use) add: stable_def constrains_def invariant_def initially_def)
apply (rule subsetI)
apply (erule reachable.induct)
apply (blast intro: reachable.intros)+
done

(*** Co ***)

lemma constrains_reachable_Int: "F \<in> B co B'==>F:(reachable(F) Int B) co (reachable(F) Int B')"
apply (frule constrains_type [THEN subsetD])
apply (frule stable_reachable [OF _ _ subset_refl])
apply (simp_all add: stable_def constrains_Int)
done

(*Resembles the previous definition of Constrains*)
lemma Constrains_eq_constrains: 
"A Co B = {F \<in> program. F:(reachable(F) Int A) co (reachable(F)  Int  B)}"
apply (unfold Constrains_def)
apply (blast dest: constrains_reachable_Int constrains_type [THEN subsetD]
             intro: constrains_weaken)
done

lemmas Constrains_def2 = Constrains_eq_constrains [THEN eq_reflection]

lemma constrains_imp_Constrains: "F \<in> A co A' ==> F \<in> A Co A'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken_L dest: constrainsD2)
done

lemma ConstrainsI: 
    "[|!!act s s'. [| act \<in> Acts(F); <s,s'>:act; s \<in> A |] ==> s':A'; 
       F \<in> program|]
     ==> F \<in> A Co A'"
apply (auto simp add: Constrains_def constrains_def st_set_def)
apply (blast dest: reachable_type [THEN subsetD])
done

lemma Constrains_type: 
 "A Co B <= program"
apply (unfold Constrains_def, blast)
done

lemma Constrains_empty: "F \<in> 0 Co B <-> F \<in> program"
by (auto dest: Constrains_type [THEN subsetD]
            intro: constrains_imp_Constrains)
declare Constrains_empty [iff]

lemma Constrains_state: "F \<in> A Co state <-> F \<in> program"
apply (unfold Constrains_def)
apply (auto dest: Constrains_type [THEN subsetD] intro: constrains_imp_Constrains)
done
declare Constrains_state [iff]

lemma Constrains_weaken_R: 
        "[| F \<in> A Co A'; A'<=B' |] ==> F \<in> A Co B'"
apply (unfold Constrains_def2)
apply (blast intro: constrains_weaken_R)
done

lemma Constrains_weaken_L: 
    "[| F \<in> A Co A'; B<=A |] ==> F \<in> B Co A'"
apply (unfold Constrains_def2)
apply (blast intro: constrains_weaken_L st_set_subset)
done

lemma Constrains_weaken: 
   "[| F \<in> A Co A'; B<=A; A'<=B' |] ==> F \<in> B Co B'"
apply (unfold Constrains_def2)
apply (blast intro: constrains_weaken st_set_subset)
done

(** Union **)
lemma Constrains_Un: 
    "[| F \<in> A Co A'; F \<in> B Co B' |] ==> F \<in> (A Un B) Co (A' Un B')"
apply (unfold Constrains_def2, auto)
apply (simp add: Int_Un_distrib)
apply (blast intro: constrains_Un)
done

lemma Constrains_UN: 
    "[|(!!i. i \<in> I==>F \<in> A(i) Co A'(i)); F \<in> program|] 
     ==> F:(\<Union>i \<in> I. A(i)) Co (\<Union>i \<in> I. A'(i))"
by (auto intro: constrains_UN simp del: UN_simps 
         simp add: Constrains_def2 Int_UN_distrib)


(** Intersection **)

lemma Constrains_Int: 
    "[| F \<in> A Co A'; F \<in> B Co B'|]==> F:(A Int B) Co (A' Int B')"
apply (unfold Constrains_def)
apply (subgoal_tac "reachable (F) Int (A Int B) = (reachable (F) Int A) Int (reachable (F) Int B) ")
apply (auto intro: constrains_Int)
done

lemma Constrains_INT: 
    "[| (!!i. i \<in> I ==>F \<in> A(i) Co A'(i)); F \<in> program  |]  
     ==> F:(\<Inter>i \<in> I. A(i)) Co (\<Inter>i \<in> I. A'(i))"
apply (simp (no_asm_simp) del: INT_simps add: Constrains_def INT_extend_simps)
apply (rule constrains_INT)
apply (auto simp add: Constrains_def)
done

lemma Constrains_imp_subset: "F \<in> A Co A' ==> reachable(F) Int A <= A'"
apply (unfold Constrains_def)
apply (blast dest: constrains_imp_subset)
done

lemma Constrains_trans: 
 "[| F \<in> A Co B; F \<in> B Co C |] ==> F \<in> A Co C"
apply (unfold Constrains_def2)
apply (blast intro: constrains_trans constrains_weaken)
done

lemma Constrains_cancel: 
"[| F \<in> A Co (A' Un B); F \<in> B Co B' |] ==> F \<in> A Co (A' Un B')"
apply (unfold Constrains_def2)
apply (simp (no_asm_use) add: Int_Un_distrib)
apply (blast intro: constrains_cancel)
done

(*** Stable ***)
(* Useful because there's no Stable_weaken.  [Tanja Vos] *)

lemma stable_imp_Stable: 
"F \<in> stable(A) ==> F \<in> Stable(A)"

apply (unfold stable_def Stable_def)
apply (erule constrains_imp_Constrains)
done

lemma Stable_eq: "[| F \<in> Stable(A); A = B |] ==> F \<in> Stable(B)"
by blast

lemma Stable_eq_stable: 
"F \<in> Stable(A) <->  (F \<in> stable(reachable(F) Int A))"
apply (auto dest: constrainsD2 simp add: Stable_def stable_def Constrains_def2)
done

lemma StableI: "F \<in> A Co A ==> F \<in> Stable(A)"
by (unfold Stable_def, assumption)

lemma StableD: "F \<in> Stable(A) ==> F \<in> A Co A"
by (unfold Stable_def, assumption)

lemma Stable_Un: 
    "[| F \<in> Stable(A); F \<in> Stable(A') |] ==> F \<in> Stable(A Un A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Un)
done

lemma Stable_Int: 
    "[| F \<in> Stable(A); F \<in> Stable(A') |] ==> F \<in> Stable (A Int A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Int)
done

lemma Stable_Constrains_Un: 
    "[| F \<in> Stable(C); F \<in> A Co (C Un A') |]    
     ==> F \<in> (C Un A) Co (C Un A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Un [THEN Constrains_weaken_R])
done

lemma Stable_Constrains_Int: 
    "[| F \<in> Stable(C); F \<in> (C Int A) Co A' |]    
     ==> F \<in> (C Int A) Co (C Int A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Int [THEN Constrains_weaken])
done

lemma Stable_UN: 
    "[| (!!i. i \<in> I ==> F \<in> Stable(A(i))); F \<in> program |]
     ==> F \<in> Stable (\<Union>i \<in> I. A(i))"
apply (simp add: Stable_def)
apply (blast intro: Constrains_UN)
done

lemma Stable_INT: 
    "[|(!!i. i \<in> I ==> F \<in> Stable(A(i))); F \<in> program |]
     ==> F \<in> Stable (\<Inter>i \<in> I. A(i))"
apply (simp add: Stable_def)
apply (blast intro: Constrains_INT)
done

lemma Stable_reachable: "F \<in> program ==>F \<in> Stable (reachable(F))"
apply (simp (no_asm_simp) add: Stable_eq_stable Int_absorb)
done

lemma Stable_type: "Stable(A) <= program"
apply (unfold Stable_def)
apply (rule Constrains_type)
done

(*** The Elimination Theorem.  The "free" m has become universally quantified!
     Should the premise be !!m instead of \<forall>m ?  Would make it harder to use
     in forward proof. ***)

lemma Elimination: 
    "[| \<forall>m \<in> M. F \<in> ({s \<in> A. x(s) = m}) Co (B(m)); F \<in> program |]  
     ==> F \<in> ({s \<in> A. x(s):M}) Co (\<Union>m \<in> M. B(m))"
apply (unfold Constrains_def, auto)
apply (rule_tac A1 = "reachable (F) Int A" 
	in UNITY.elimination [THEN constrains_weaken_L])
apply (auto intro: constrains_weaken_L)
done

(* As above, but for the special case of A=state *)
lemma Elimination2: 
 "[| \<forall>m \<in> M. F \<in> {s \<in> state. x(s) = m} Co B(m); F \<in> program |]  
     ==> F \<in> {s \<in> state. x(s):M} Co (\<Union>m \<in> M. B(m))"
apply (blast intro: Elimination)
done

(** Unless **)

lemma Unless_type: "A Unless B <=program"

apply (unfold Unless_def)
apply (rule Constrains_type)
done

(*** Specialized laws for handling Always ***)

(** Natural deduction rules for "Always A" **)

lemma AlwaysI: 
"[| Init(F)<=A;  F \<in> Stable(A) |] ==> F \<in> Always(A)"

apply (unfold Always_def initially_def)
apply (frule Stable_type [THEN subsetD], auto)
done

lemma AlwaysD: "F \<in> Always(A) ==> Init(F)<=A & F \<in> Stable(A)"
by (simp add: Always_def initially_def)

lemmas AlwaysE = AlwaysD [THEN conjE, standard]
lemmas Always_imp_Stable = AlwaysD [THEN conjunct2, standard]

(*The set of all reachable states is Always*)
lemma Always_includes_reachable: "F \<in> Always(A) ==> reachable(F) <= A"
apply (simp (no_asm_use) add: Stable_def Constrains_def constrains_def Always_def initially_def)
apply (rule subsetI)
apply (erule reachable.induct)
apply (blast intro: reachable.intros)+
done

lemma invariant_imp_Always: 
     "F \<in> invariant(A) ==> F \<in> Always(A)"
apply (unfold Always_def invariant_def Stable_def stable_def)
apply (blast intro: constrains_imp_Constrains)
done

lemmas Always_reachable = invariant_reachable [THEN invariant_imp_Always, standard]

lemma Always_eq_invariant_reachable: "Always(A) = {F \<in> program. F \<in> invariant(reachable(F) Int A)}"
apply (simp (no_asm) add: Always_def invariant_def Stable_def Constrains_def2 stable_def initially_def)
apply (rule equalityI, auto) 
apply (blast intro: reachable.intros reachable_type)
done

(*the RHS is the traditional definition of the "always" operator*)
lemma Always_eq_includes_reachable: "Always(A) = {F \<in> program. reachable(F) <= A}"
apply (rule equalityI, safe)
apply (auto dest: invariant_includes_reachable 
   simp add: subset_Int_iff invariant_reachable Always_eq_invariant_reachable)
done

lemma Always_type: "Always(A) <= program"
by (unfold Always_def initially_def, auto)

lemma Always_state_eq: "Always(state) = program"
apply (rule equalityI)
apply (auto dest: Always_type [THEN subsetD] reachable_type [THEN subsetD]
            simp add: Always_eq_includes_reachable)
done
declare Always_state_eq [simp]

lemma state_AlwaysI: "F \<in> program ==> F \<in> Always(state)"
by (auto dest: reachable_type [THEN subsetD]
            simp add: Always_eq_includes_reachable)

lemma Always_eq_UN_invariant: "st_set(A) ==> Always(A) = (\<Union>I \<in> Pow(A). invariant(I))"
apply (simp (no_asm) add: Always_eq_includes_reachable)
apply (rule equalityI, auto) 
apply (blast intro: invariantI rev_subsetD [OF _ Init_into_reachable] 
		    rev_subsetD [OF _ invariant_includes_reachable]  
             dest: invariant_type [THEN subsetD])+
done

lemma Always_weaken: "[| F \<in> Always(A); A <= B |] ==> F \<in> Always(B)"
by (auto simp add: Always_eq_includes_reachable)


(*** "Co" rules involving Always ***)
lemmas Int_absorb2 = subset_Int_iff [unfolded iff_def, THEN conjunct1, THEN mp]

lemma Always_Constrains_pre: "F \<in> Always(I) ==> (F:(I Int A) Co A') <-> (F \<in> A Co A')"
apply (simp (no_asm_simp) add: Always_includes_reachable [THEN Int_absorb2] Constrains_def Int_assoc [symmetric])
done

lemma Always_Constrains_post: "F \<in> Always(I) ==> (F \<in> A Co (I Int A')) <->(F \<in> A Co A')"
apply (simp (no_asm_simp) add: Always_includes_reachable [THEN Int_absorb2] Constrains_eq_constrains Int_assoc [symmetric])
done

lemma Always_ConstrainsI: "[| F \<in> Always(I);  F \<in> (I Int A) Co A' |] ==> F \<in> A Co A'"
by (blast intro: Always_Constrains_pre [THEN iffD1])

(* [| F \<in> Always(I);  F \<in> A Co A' |] ==> F \<in> A Co (I Int A') *)
lemmas Always_ConstrainsD = Always_Constrains_post [THEN iffD2, standard]

(*The analogous proof of Always_LeadsTo_weaken doesn't terminate*)
lemma Always_Constrains_weaken: 
"[|F \<in> Always(C); F \<in> A Co A'; C Int B<=A; C Int A'<=B'|]==>F \<in> B Co B'"
apply (rule Always_ConstrainsI)
apply (drule_tac [2] Always_ConstrainsD, simp_all) 
apply (blast intro: Constrains_weaken)
done

(** Conjoining Always properties **)
lemma Always_Int_distrib: "Always(A Int B) = Always(A) Int Always(B)"
by (auto simp add: Always_eq_includes_reachable)

(* the premise i \<in> I is need since \<Inter>is formally not defined for I=0 *)
lemma Always_INT_distrib: "i \<in> I==>Always(\<Inter>i \<in> I. A(i)) = (\<Inter>i \<in> I. Always(A(i)))"
apply (rule equalityI)
apply (auto simp add: Inter_iff Always_eq_includes_reachable)
done


lemma Always_Int_I: "[| F \<in> Always(A);  F \<in> Always(B) |] ==> F \<in> Always(A Int B)"
apply (simp (no_asm_simp) add: Always_Int_distrib)
done

(*Allows a kind of "implication introduction"*)
lemma Always_Diff_Un_eq: "[| F \<in> Always(A) |] ==> (F \<in> Always(C-A Un B)) <-> (F \<in> Always(B))"
by (auto simp add: Always_eq_includes_reachable)

(*Delete the nearest invariance assumption (which will be the second one
  used by Always_Int_I) *)
lemmas Always_thin = thin_rl [of "F \<in> Always(A)", standard]

ML
{*
val reachable_type = thm "reachable_type";
val st_set_reachable = thm "st_set_reachable";
val reachable_Int_state = thm "reachable_Int_state";
val state_Int_reachable = thm "state_Int_reachable";
val reachable_equiv_traces = thm "reachable_equiv_traces";
val Init_into_reachable = thm "Init_into_reachable";
val stable_reachable = thm "stable_reachable";
val invariant_reachable = thm "invariant_reachable";
val invariant_includes_reachable = thm "invariant_includes_reachable";
val constrains_reachable_Int = thm "constrains_reachable_Int";
val Constrains_eq_constrains = thm "Constrains_eq_constrains";
val Constrains_def2 = thm "Constrains_def2";
val constrains_imp_Constrains = thm "constrains_imp_Constrains";
val ConstrainsI = thm "ConstrainsI";
val Constrains_type = thm "Constrains_type";
val Constrains_empty = thm "Constrains_empty";
val Constrains_state = thm "Constrains_state";
val Constrains_weaken_R = thm "Constrains_weaken_R";
val Constrains_weaken_L = thm "Constrains_weaken_L";
val Constrains_weaken = thm "Constrains_weaken";
val Constrains_Un = thm "Constrains_Un";
val Constrains_UN = thm "Constrains_UN";
val Constrains_Int = thm "Constrains_Int";
val Constrains_INT = thm "Constrains_INT";
val Constrains_imp_subset = thm "Constrains_imp_subset";
val Constrains_trans = thm "Constrains_trans";
val Constrains_cancel = thm "Constrains_cancel";
val stable_imp_Stable = thm "stable_imp_Stable";
val Stable_eq = thm "Stable_eq";
val Stable_eq_stable = thm "Stable_eq_stable";
val StableI = thm "StableI";
val StableD = thm "StableD";
val Stable_Un = thm "Stable_Un";
val Stable_Int = thm "Stable_Int";
val Stable_Constrains_Un = thm "Stable_Constrains_Un";
val Stable_Constrains_Int = thm "Stable_Constrains_Int";
val Stable_UN = thm "Stable_UN";
val Stable_INT = thm "Stable_INT";
val Stable_reachable = thm "Stable_reachable";
val Stable_type = thm "Stable_type";
val Elimination = thm "Elimination";
val Elimination2 = thm "Elimination2";
val Unless_type = thm "Unless_type";
val AlwaysI = thm "AlwaysI";
val AlwaysD = thm "AlwaysD";
val AlwaysE = thm "AlwaysE";
val Always_imp_Stable = thm "Always_imp_Stable";
val Always_includes_reachable = thm "Always_includes_reachable";
val invariant_imp_Always = thm "invariant_imp_Always";
val Always_reachable = thm "Always_reachable";
val Always_eq_invariant_reachable = thm "Always_eq_invariant_reachable";
val Always_eq_includes_reachable = thm "Always_eq_includes_reachable";
val Always_type = thm "Always_type";
val Always_state_eq = thm "Always_state_eq";
val state_AlwaysI = thm "state_AlwaysI";
val Always_eq_UN_invariant = thm "Always_eq_UN_invariant";
val Always_weaken = thm "Always_weaken";
val Int_absorb2 = thm "Int_absorb2";
val Always_Constrains_pre = thm "Always_Constrains_pre";
val Always_Constrains_post = thm "Always_Constrains_post";
val Always_ConstrainsI = thm "Always_ConstrainsI";
val Always_ConstrainsD = thm "Always_ConstrainsD";
val Always_Constrains_weaken = thm "Always_Constrains_weaken";
val Always_Int_distrib = thm "Always_Int_distrib";
val Always_INT_distrib = thm "Always_INT_distrib";
val Always_Int_I = thm "Always_Int_I";
val Always_Diff_Un_eq = thm "Always_Diff_Un_eq";
val Always_thin = thm "Always_thin";

(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
val Always_Int_tac = dtac Always_Int_I THEN' assume_tac THEN' etac Always_thin;

(*Combines a list of invariance THEOREMS into one.*)
val Always_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS Always_Int_I);

(*To allow expansion of the program's definition when appropriate*)
val program_defs_ref = ref ([]: thm list);

(*proves "co" properties when the program is specified*)

fun gen_constrains_tac(cs,ss) i = 
   SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
              REPEAT (etac Always_ConstrainsI 1
                      ORELSE
                      resolve_tac [StableI, stableI,
                                   constrains_imp_Constrains] 1),
              rtac constrainsI 1,
              (* Three subgoals *)
              rewrite_goal_tac [st_set_def] 3,
              REPEAT (Force_tac 2),
              full_simp_tac (ss addsimps !program_defs_ref) 1,
              ALLGOALS (clarify_tac cs),
              REPEAT (FIRSTGOAL (etac disjE)),
              ALLGOALS Clarify_tac,
              REPEAT (FIRSTGOAL (etac disjE)),
              ALLGOALS (clarify_tac cs),
              ALLGOALS (asm_full_simp_tac ss),
              ALLGOALS (clarify_tac cs)]) i;

fun constrains_tac st = gen_constrains_tac (claset(), simpset()) st;

(*For proving invariants*)
fun always_tac i = 
    rtac AlwaysI i THEN Force_tac i THEN constrains_tac i;
*}

method_setup safety = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            gen_constrains_tac (local_clasimpset_of ctxt) 1)) *}
    "for proving safety properties"


end

