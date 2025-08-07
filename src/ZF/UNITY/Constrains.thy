(*  Title:      ZF/UNITY/Constrains.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge
*)

section\<open>Weak Safety Properties\<close>

theory Constrains
imports UNITY
begin

consts traces :: "[i, i] \<Rightarrow> i"
  (* Initial states and program \<Rightarrow> (final state, reversed trace to it)... 
      the domain may also be state*list(state) *)
inductive 
  domains 
     "traces(init, acts)" <=
         "(init \<union> (\<Union>act\<in>acts. field(act)))*list(\<Union>act\<in>acts. field(act))"
  intros 
         (*Initial trace is empty*)
    Init: "s: init \<Longrightarrow> <s,[]> \<in> traces(init,acts)"

    Acts: "\<lbrakk>act:acts;  \<langle>s,evs\<rangle> \<in> traces(init,acts);  <s,s'>: act\<rbrakk>
           \<Longrightarrow> <s', Cons(s,evs)> \<in> traces(init, acts)"
  
  type_intros list.intros UnI1 UnI2 UN_I fieldI2 fieldI1


consts reachable :: "i\<Rightarrow>i"
inductive
  domains
  "reachable(F)" \<subseteq> "Init(F) \<union> (\<Union>act\<in>Acts(F). field(act))"
  intros 
    Init: "s:Init(F) \<Longrightarrow> s:reachable(F)"

    Acts: "\<lbrakk>act: Acts(F);  s:reachable(F);  <s,s'>: act\<rbrakk>
           \<Longrightarrow> s':reachable(F)"

  type_intros UnI1 UnI2 fieldI2 UN_I

  
definition
  Constrains :: "[i,i] \<Rightarrow> i"  (infixl \<open>Co\<close> 60)  where
  "A Co B \<equiv> {F:program. F:(reachable(F) \<inter> A) co B}"

definition
  op_Unless  :: "[i, i] \<Rightarrow> i"  (infixl \<open>Unless\<close> 60)  where
  "A Unless B \<equiv> (A-B) Co (A \<union> B)"

definition
  Stable     :: "i \<Rightarrow> i"  where
  "Stable(A) \<equiv> A Co A"

definition
  (*Always is the weak form of "invariant"*)
  Always :: "i \<Rightarrow> i"  where
  "Always(A) \<equiv> initially(A) \<inter> Stable(A)"


(*** traces and reachable ***)

lemma reachable_type: "reachable(F) \<subseteq> state"
apply (cut_tac F = F in Init_type)
apply (cut_tac F = F in Acts_type)
apply (cut_tac F = F in reachable.dom_subset, blast)
done

lemma st_set_reachable: "st_set(reachable(F))"
  unfolding st_set_def
apply (rule reachable_type)
done
declare st_set_reachable [iff]

lemma reachable_Int_state: "reachable(F) \<inter> state = reachable(F)"
by (cut_tac reachable_type, auto)
declare reachable_Int_state [iff]

lemma state_Int_reachable: "state \<inter> reachable(F) = reachable(F)"
by (cut_tac reachable_type, auto)
declare state_Int_reachable [iff]

lemma reachable_equiv_traces: 
"F \<in> program \<Longrightarrow> reachable(F)={s \<in> state. \<exists>evs. \<langle>s,evs\<rangle>:traces(Init(F), Acts(F))}"
apply (rule equalityI, safe)
apply (blast dest: reachable_type [THEN subsetD])
apply (erule_tac [2] traces.induct)
apply (erule reachable.induct)
apply (blast intro: reachable.intros traces.intros)+
done

lemma Init_into_reachable: "Init(F) \<subseteq> reachable(F)"
by (blast intro: reachable.intros)

lemma stable_reachable: "\<lbrakk>F \<in> program; G \<in> program;  
    Acts(G) \<subseteq> Acts(F)\<rbrakk> \<Longrightarrow> G \<in> stable(reachable(F))"
apply (blast intro: stableI constrainsI st_setI
             reachable_type [THEN subsetD] reachable.intros)
done

declare stable_reachable [intro!]
declare stable_reachable [simp]

(*The set of all reachable states is an invariant...*)
lemma invariant_reachable: 
   "F \<in> program \<Longrightarrow> F \<in> invariant(reachable(F))"
  unfolding invariant_def initially_def
apply (blast intro: reachable_type [THEN subsetD] reachable.intros)
done

(*...in fact the strongest invariant!*)
lemma invariant_includes_reachable: "F \<in> invariant(A) \<Longrightarrow> reachable(F) \<subseteq> A"
apply (cut_tac F = F in Acts_type)
apply (cut_tac F = F in Init_type)
apply (cut_tac F = F in reachable_type)
apply (simp (no_asm_use) add: stable_def constrains_def invariant_def initially_def)
apply (rule subsetI)
apply (erule reachable.induct)
apply (blast intro: reachable.intros)+
done

(*** Co ***)

lemma constrains_reachable_Int: "F \<in> B co B'\<Longrightarrow>F:(reachable(F) \<inter> B) co (reachable(F) \<inter> B')"
apply (frule constrains_type [THEN subsetD])
apply (frule stable_reachable [OF _ _ subset_refl])
apply (simp_all add: stable_def constrains_Int)
done

(*Resembles the previous definition of Constrains*)
lemma Constrains_eq_constrains: 
"A Co B = {F \<in> program. F:(reachable(F) \<inter> A) co (reachable(F)  \<inter>  B)}"
  unfolding Constrains_def
apply (blast dest: constrains_reachable_Int constrains_type [THEN subsetD]
             intro: constrains_weaken)
done

lemmas Constrains_def2 = Constrains_eq_constrains [THEN eq_reflection]

lemma constrains_imp_Constrains: "F \<in> A co A' \<Longrightarrow> F \<in> A Co A'"
  unfolding Constrains_def
apply (blast intro: constrains_weaken_L dest: constrainsD2)
done

lemma ConstrainsI: 
    "\<lbrakk>\<And>act s s'. \<lbrakk>act \<in> Acts(F); <s,s'>:act; s \<in> A\<rbrakk> \<Longrightarrow> s':A'; 
       F \<in> program\<rbrakk>
     \<Longrightarrow> F \<in> A Co A'"
apply (auto simp add: Constrains_def constrains_def st_set_def)
apply (blast dest: reachable_type [THEN subsetD])
done

lemma Constrains_type: 
 "A Co B \<subseteq> program"
apply (unfold Constrains_def, blast)
done

lemma Constrains_empty: "F \<in> 0 Co B \<longleftrightarrow> F \<in> program"
by (auto dest: Constrains_type [THEN subsetD]
            intro: constrains_imp_Constrains)
declare Constrains_empty [iff]

lemma Constrains_state: "F \<in> A Co state \<longleftrightarrow> F \<in> program"
  unfolding Constrains_def
apply (auto dest: Constrains_type [THEN subsetD] intro: constrains_imp_Constrains)
done
declare Constrains_state [iff]

lemma Constrains_weaken_R: 
        "\<lbrakk>F \<in> A Co A'; A'<=B'\<rbrakk> \<Longrightarrow> F \<in> A Co B'"
  unfolding Constrains_def2
apply (blast intro: constrains_weaken_R)
done

lemma Constrains_weaken_L: 
    "\<lbrakk>F \<in> A Co A'; B<=A\<rbrakk> \<Longrightarrow> F \<in> B Co A'"
  unfolding Constrains_def2
apply (blast intro: constrains_weaken_L st_set_subset)
done

lemma Constrains_weaken: 
   "\<lbrakk>F \<in> A Co A'; B<=A; A'<=B'\<rbrakk> \<Longrightarrow> F \<in> B Co B'"
  unfolding Constrains_def2
apply (blast intro: constrains_weaken st_set_subset)
done

(** Union **)
lemma Constrains_Un: 
    "\<lbrakk>F \<in> A Co A'; F \<in> B Co B'\<rbrakk> \<Longrightarrow> F \<in> (A \<union> B) Co (A' \<union> B')"
apply (unfold Constrains_def2, auto)
apply (simp add: Int_Un_distrib)
apply (blast intro: constrains_Un)
done

lemma Constrains_UN: 
    "\<lbrakk>(\<And>i. i \<in> I\<Longrightarrow>F \<in> A(i) Co A'(i)); F \<in> program\<rbrakk> 
     \<Longrightarrow> F:(\<Union>i \<in> I. A(i)) Co (\<Union>i \<in> I. A'(i))"
by (auto intro: constrains_UN simp del: UN_simps 
         simp add: Constrains_def2 Int_UN_distrib)


(** Intersection **)

lemma Constrains_Int: 
    "\<lbrakk>F \<in> A Co A'; F \<in> B Co B'\<rbrakk>\<Longrightarrow> F:(A \<inter> B) Co (A' \<inter> B')"
  unfolding Constrains_def
apply (subgoal_tac "reachable (F) \<inter> (A \<inter> B) = (reachable (F) \<inter> A) \<inter> (reachable (F) \<inter> B) ")
apply (auto intro: constrains_Int)
done

lemma Constrains_INT: 
    "\<lbrakk>(\<And>i. i \<in> I \<Longrightarrow>F \<in> A(i) Co A'(i)); F \<in> program\<rbrakk>  
     \<Longrightarrow> F:(\<Inter>i \<in> I. A(i)) Co (\<Inter>i \<in> I. A'(i))"
apply (simp (no_asm_simp) del: INT_simps add: Constrains_def INT_extend_simps)
apply (rule constrains_INT)
apply (auto simp add: Constrains_def)
done

lemma Constrains_imp_subset: "F \<in> A Co A' \<Longrightarrow> reachable(F) \<inter> A \<subseteq> A'"
  unfolding Constrains_def
apply (blast dest: constrains_imp_subset)
done

lemma Constrains_trans: 
 "\<lbrakk>F \<in> A Co B; F \<in> B Co C\<rbrakk> \<Longrightarrow> F \<in> A Co C"
  unfolding Constrains_def2
apply (blast intro: constrains_trans constrains_weaken)
done

lemma Constrains_cancel: 
"\<lbrakk>F \<in> A Co (A' \<union> B); F \<in> B Co B'\<rbrakk> \<Longrightarrow> F \<in> A Co (A' \<union> B')"
  unfolding Constrains_def2
apply (simp (no_asm_use) add: Int_Un_distrib)
apply (blast intro: constrains_cancel)
done

(*** Stable ***)
(* Useful because there's no Stable_weaken.  [Tanja Vos] *)

lemma stable_imp_Stable: 
"F \<in> stable(A) \<Longrightarrow> F \<in> Stable(A)"

  unfolding stable_def Stable_def
apply (erule constrains_imp_Constrains)
done

lemma Stable_eq: "\<lbrakk>F \<in> Stable(A); A = B\<rbrakk> \<Longrightarrow> F \<in> Stable(B)"
by blast

lemma Stable_eq_stable: 
"F \<in> Stable(A) \<longleftrightarrow>  (F \<in> stable(reachable(F) \<inter> A))"
apply (auto dest: constrainsD2 simp add: Stable_def stable_def Constrains_def2)
done

lemma StableI: "F \<in> A Co A \<Longrightarrow> F \<in> Stable(A)"
by (unfold Stable_def, assumption)

lemma StableD: "F \<in> Stable(A) \<Longrightarrow> F \<in> A Co A"
by (unfold Stable_def, assumption)

lemma Stable_Un: 
    "\<lbrakk>F \<in> Stable(A); F \<in> Stable(A')\<rbrakk> \<Longrightarrow> F \<in> Stable(A \<union> A')"
  unfolding Stable_def
apply (blast intro: Constrains_Un)
done

lemma Stable_Int: 
    "\<lbrakk>F \<in> Stable(A); F \<in> Stable(A')\<rbrakk> \<Longrightarrow> F \<in> Stable (A \<inter> A')"
  unfolding Stable_def
apply (blast intro: Constrains_Int)
done

lemma Stable_Constrains_Un: 
    "\<lbrakk>F \<in> Stable(C); F \<in> A Co (C \<union> A')\<rbrakk>    
     \<Longrightarrow> F \<in> (C \<union> A) Co (C \<union> A')"
  unfolding Stable_def
apply (blast intro: Constrains_Un [THEN Constrains_weaken_R])
done

lemma Stable_Constrains_Int: 
    "\<lbrakk>F \<in> Stable(C); F \<in> (C \<inter> A) Co A'\<rbrakk>    
     \<Longrightarrow> F \<in> (C \<inter> A) Co (C \<inter> A')"
  unfolding Stable_def
apply (blast intro: Constrains_Int [THEN Constrains_weaken])
done

lemma Stable_UN: 
    "\<lbrakk>(\<And>i. i \<in> I \<Longrightarrow> F \<in> Stable(A(i))); F \<in> program\<rbrakk>
     \<Longrightarrow> F \<in> Stable (\<Union>i \<in> I. A(i))"
apply (simp add: Stable_def)
apply (blast intro: Constrains_UN)
done

lemma Stable_INT: 
    "\<lbrakk>(\<And>i. i \<in> I \<Longrightarrow> F \<in> Stable(A(i))); F \<in> program\<rbrakk>
     \<Longrightarrow> F \<in> Stable (\<Inter>i \<in> I. A(i))"
apply (simp add: Stable_def)
apply (blast intro: Constrains_INT)
done

lemma Stable_reachable: "F \<in> program \<Longrightarrow>F \<in> Stable (reachable(F))"
apply (simp (no_asm_simp) add: Stable_eq_stable Int_absorb)
done

lemma Stable_type: "Stable(A) \<subseteq> program"
  unfolding Stable_def
apply (rule Constrains_type)
done

(*** The Elimination Theorem.  The "free" m has become universally quantified!
     Should the premise be \<And>m instead of \<forall>m ?  Would make it harder to use
     in forward proof. ***)

lemma Elimination: 
    "\<lbrakk>\<forall>m \<in> M. F \<in> ({s \<in> A. x(s) = m}) Co (B(m)); F \<in> program\<rbrakk>  
     \<Longrightarrow> F \<in> ({s \<in> A. x(s):M}) Co (\<Union>m \<in> M. B(m))"
apply (unfold Constrains_def, auto)
apply (rule_tac A1 = "reachable (F) \<inter> A" 
        in UNITY.elimination [THEN constrains_weaken_L])
apply (auto intro: constrains_weaken_L)
done

(* As above, but for the special case of A=state *)
lemma Elimination2: 
 "\<lbrakk>\<forall>m \<in> M. F \<in> {s \<in> state. x(s) = m} Co B(m); F \<in> program\<rbrakk>  
     \<Longrightarrow> F \<in> {s \<in> state. x(s):M} Co (\<Union>m \<in> M. B(m))"
apply (blast intro: Elimination)
done

(** Unless **)

lemma Unless_type: "A Unless B <=program"
  unfolding op_Unless_def
apply (rule Constrains_type)
done

(*** Specialized laws for handling Always ***)

(** Natural deduction rules for "Always A" **)

lemma AlwaysI: 
"\<lbrakk>Init(F)<=A;  F \<in> Stable(A)\<rbrakk> \<Longrightarrow> F \<in> Always(A)"

  unfolding Always_def initially_def
apply (frule Stable_type [THEN subsetD], auto)
done

lemma AlwaysD: "F \<in> Always(A) \<Longrightarrow> Init(F)<=A \<and> F \<in> Stable(A)"
by (simp add: Always_def initially_def)

lemmas AlwaysE = AlwaysD [THEN conjE]
lemmas Always_imp_Stable = AlwaysD [THEN conjunct2]

(*The set of all reachable states is Always*)
lemma Always_includes_reachable: "F \<in> Always(A) \<Longrightarrow> reachable(F) \<subseteq> A"
apply (simp (no_asm_use) add: Stable_def Constrains_def constrains_def Always_def initially_def)
apply (rule subsetI)
apply (erule reachable.induct)
apply (blast intro: reachable.intros)+
done

lemma invariant_imp_Always: 
     "F \<in> invariant(A) \<Longrightarrow> F \<in> Always(A)"
  unfolding Always_def invariant_def Stable_def stable_def
apply (blast intro: constrains_imp_Constrains)
done

lemmas Always_reachable = invariant_reachable [THEN invariant_imp_Always]

lemma Always_eq_invariant_reachable: "Always(A) = {F \<in> program. F \<in> invariant(reachable(F) \<inter> A)}"
apply (simp (no_asm) add: Always_def invariant_def Stable_def Constrains_def2 stable_def initially_def)
apply (rule equalityI, auto) 
apply (blast intro: reachable.intros reachable_type)
done

(*the RHS is the traditional definition of the "always" operator*)
lemma Always_eq_includes_reachable: "Always(A) = {F \<in> program. reachable(F) \<subseteq> A}"
apply (rule equalityI, safe)
apply (auto dest: invariant_includes_reachable 
   simp add: subset_Int_iff invariant_reachable Always_eq_invariant_reachable)
done

lemma Always_type: "Always(A) \<subseteq> program"
by (unfold Always_def initially_def, auto)

lemma Always_state_eq: "Always(state) = program"
apply (rule equalityI)
apply (auto dest: Always_type [THEN subsetD] reachable_type [THEN subsetD]
            simp add: Always_eq_includes_reachable)
done
declare Always_state_eq [simp]

lemma state_AlwaysI: "F \<in> program \<Longrightarrow> F \<in> Always(state)"
by (auto dest: reachable_type [THEN subsetD]
            simp add: Always_eq_includes_reachable)

lemma Always_eq_UN_invariant: "st_set(A) \<Longrightarrow> Always(A) = (\<Union>I \<in> Pow(A). invariant(I))"
apply (simp (no_asm) add: Always_eq_includes_reachable)
apply (rule equalityI, auto) 
apply (blast intro: invariantI rev_subsetD [OF _ Init_into_reachable] 
                    rev_subsetD [OF _ invariant_includes_reachable]  
             dest: invariant_type [THEN subsetD])+
done

lemma Always_weaken: "\<lbrakk>F \<in> Always(A); A \<subseteq> B\<rbrakk> \<Longrightarrow> F \<in> Always(B)"
by (auto simp add: Always_eq_includes_reachable)


(*** "Co" rules involving Always ***)
lemmas Int_absorb2 = subset_Int_iff [unfolded iff_def, THEN conjunct1, THEN mp]

lemma Always_Constrains_pre: "F \<in> Always(I) \<Longrightarrow> (F:(I \<inter> A) Co A') \<longleftrightarrow> (F \<in> A Co A')"
apply (simp (no_asm_simp) add: Always_includes_reachable [THEN Int_absorb2] Constrains_def Int_assoc [symmetric])
done

lemma Always_Constrains_post: "F \<in> Always(I) \<Longrightarrow> (F \<in> A Co (I \<inter> A')) \<longleftrightarrow>(F \<in> A Co A')"
apply (simp (no_asm_simp) add: Always_includes_reachable [THEN Int_absorb2] Constrains_eq_constrains Int_assoc [symmetric])
done

lemma Always_ConstrainsI: "\<lbrakk>F \<in> Always(I);  F \<in> (I \<inter> A) Co A'\<rbrakk> \<Longrightarrow> F \<in> A Co A'"
by (blast intro: Always_Constrains_pre [THEN iffD1])

(* \<lbrakk>F \<in> Always(I);  F \<in> A Co A'\<rbrakk> \<Longrightarrow> F \<in> A Co (I \<inter> A') *)
lemmas Always_ConstrainsD = Always_Constrains_post [THEN iffD2]

(*The analogous proof of Always_LeadsTo_weaken doesn't terminate*)
lemma Always_Constrains_weaken: 
"\<lbrakk>F \<in> Always(C); F \<in> A Co A'; C \<inter> B<=A; C \<inter> A'<=B'\<rbrakk>\<Longrightarrow>F \<in> B Co B'"
apply (rule Always_ConstrainsI)
apply (drule_tac [2] Always_ConstrainsD, simp_all) 
apply (blast intro: Constrains_weaken)
done

(** Conjoining Always properties **)
lemma Always_Int_distrib: "Always(A \<inter> B) = Always(A) \<inter> Always(B)"
by (auto simp add: Always_eq_includes_reachable)

(* the premise i \<in> I is need since \<Inter>is formally not defined for I=0 *)
lemma Always_INT_distrib: "i \<in> I\<Longrightarrow>Always(\<Inter>i \<in> I. A(i)) = (\<Inter>i \<in> I. Always(A(i)))"
apply (rule equalityI)
apply (auto simp add: Inter_iff Always_eq_includes_reachable)
done


lemma Always_Int_I: "\<lbrakk>F \<in> Always(A);  F \<in> Always(B)\<rbrakk> \<Longrightarrow> F \<in> Always(A \<inter> B)"
apply (simp (no_asm_simp) add: Always_Int_distrib)
done

(*Allows a kind of "implication introduction"*)
lemma Always_Diff_Un_eq: "\<lbrakk>F \<in> Always(A)\<rbrakk> \<Longrightarrow> (F \<in> Always(C-A \<union> B)) \<longleftrightarrow> (F \<in> Always(B))"
by (auto simp add: Always_eq_includes_reachable)

(*Delete the nearest invariance assumption (which will be the second one
  used by Always_Int_I) *)
lemmas Always_thin = thin_rl [of "F \<in> Always(A)"] for F A

(*To allow expansion of the program's definition when appropriate*)
named_theorems program "program definitions"

ML
\<open>
(*Combines two invariance ASSUMPTIONS into one.  USEFUL??*)
fun Always_Int_tac ctxt =
  dresolve_tac ctxt @{thms Always_Int_I} THEN'
  assume_tac ctxt THEN'
  eresolve_tac ctxt @{thms Always_thin};

(*Combines a list of invariance THEOREMS into one.*)
val Always_Int_rule = foldr1 (fn (th1,th2) => [th1,th2] MRS @{thm Always_Int_I});

(*proves "co" properties when the program is specified*)

fun constrains_tac ctxt =
   SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac ctxt 1),
              REPEAT (eresolve_tac ctxt @{thms Always_ConstrainsI} 1
                      ORELSE
                      resolve_tac ctxt [@{thm StableI}, @{thm stableI},
                                   @{thm constrains_imp_Constrains}] 1),
              resolve_tac ctxt @{thms constrainsI} 1,
              (* Three subgoals *)
              rewrite_goal_tac ctxt [@{thm st_set_def}] 3,
              REPEAT (force_tac ctxt 2),
              full_simp_tac (ctxt |> Simplifier.add_simps (Named_Theorems.get ctxt \<^named_theorems>\<open>program\<close>)) 1,
              ALLGOALS (clarify_tac ctxt),
              REPEAT (FIRSTGOAL (eresolve_tac ctxt @{thms disjE})),
              ALLGOALS (clarify_tac ctxt),
              REPEAT (FIRSTGOAL (eresolve_tac ctxt @{thms disjE})),
              ALLGOALS (clarify_tac ctxt),
              ALLGOALS (asm_full_simp_tac ctxt),
              ALLGOALS (clarify_tac ctxt)]);

(*For proving invariants*)
fun always_tac ctxt i =
  resolve_tac ctxt @{thms AlwaysI} i THEN
  force_tac ctxt i
  THEN constrains_tac ctxt i;
\<close>

method_setup safety = \<open>
  Scan.succeed (SIMPLE_METHOD' o constrains_tac)\<close>
  "for proving safety properties"

method_setup always = \<open>
  Scan.succeed (SIMPLE_METHOD' o always_tac)\<close>
  "for proving invariants"

end
