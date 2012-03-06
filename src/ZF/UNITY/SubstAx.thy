(*  Title:      ZF/UNITY/SubstAx.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Theory ported from HOL.
*)

header{*Weak LeadsTo relation (restricted to the set of reachable states)*}

theory SubstAx
imports WFair Constrains 
begin

definition
  (* The definitions below are not `conventional', but yield simpler rules *)
  Ensures :: "[i,i] => i"            (infixl "Ensures" 60)  where
  "A Ensures B == {F:program. F \<in> (reachable(F) \<inter> A) ensures (reachable(F) \<inter> B) }"

definition
  LeadsTo :: "[i, i] => i"            (infixl "LeadsTo" 60)  where
  "A LeadsTo B == {F:program. F:(reachable(F) \<inter> A) leadsTo (reachable(F) \<inter> B)}"

notation (xsymbols)
  LeadsTo  (infixl " \<longmapsto>w " 60)



(*Resembles the previous definition of LeadsTo*)

(* Equivalence with the HOL-like definition *)
lemma LeadsTo_eq: 
"st_set(B)==> A LeadsTo B = {F \<in> program. F:(reachable(F) \<inter> A) leadsTo B}"
apply (unfold LeadsTo_def)
apply (blast dest: psp_stable2 leadsToD2 constrainsD2 intro: leadsTo_weaken)
done

lemma LeadsTo_type: "A LeadsTo B <=program"
by (unfold LeadsTo_def, auto)

(*** Specialized laws for handling invariants ***)

(** Conjoining an Always property **)
lemma Always_LeadsTo_pre: "F \<in> Always(I) ==> (F:(I \<inter> A) LeadsTo A') \<longleftrightarrow> (F \<in> A LeadsTo A')"
by (simp add: LeadsTo_def Always_eq_includes_reachable Int_absorb2 Int_assoc [symmetric] leadsToD2)

lemma Always_LeadsTo_post: "F \<in> Always(I) ==> (F \<in> A LeadsTo (I \<inter> A')) \<longleftrightarrow> (F \<in> A LeadsTo A')"
apply (unfold LeadsTo_def)
apply (simp add: Always_eq_includes_reachable Int_absorb2 Int_assoc [symmetric] leadsToD2)
done

(* Like 'Always_LeadsTo_pre RS iffD1', but with premises in the good order *)
lemma Always_LeadsToI: "[| F \<in> Always(C); F \<in> (C \<inter> A) LeadsTo A' |] ==> F \<in> A LeadsTo A'"
by (blast intro: Always_LeadsTo_pre [THEN iffD1])

(* Like 'Always_LeadsTo_post RS iffD2', but with premises in the good order *)
lemma Always_LeadsToD: "[| F \<in> Always(C);  F \<in> A LeadsTo A' |] ==> F \<in> A LeadsTo (C \<inter> A')"
by (blast intro: Always_LeadsTo_post [THEN iffD2])

(*** Introduction rules \<in> Basis, Trans, Union ***)

lemma LeadsTo_Basis: "F \<in> A Ensures B ==> F \<in> A LeadsTo B"
by (auto simp add: Ensures_def LeadsTo_def)

lemma LeadsTo_Trans:
     "[| F \<in> A LeadsTo B;  F \<in> B LeadsTo C |] ==> F \<in> A LeadsTo C"
apply (simp (no_asm_use) add: LeadsTo_def)
apply (blast intro: leadsTo_Trans)
done

lemma LeadsTo_Union:
"[|(!!A. A \<in> S ==> F \<in> A LeadsTo B); F \<in> program|]==>F \<in> \<Union>(S) LeadsTo B"
apply (simp add: LeadsTo_def)
apply (subst Int_Union_Union2)
apply (rule leadsTo_UN, auto)
done

(*** Derived rules ***)

lemma leadsTo_imp_LeadsTo: "F \<in> A leadsTo B ==> F \<in> A LeadsTo B"
apply (frule leadsToD2, clarify)
apply (simp (no_asm_simp) add: LeadsTo_eq)
apply (blast intro: leadsTo_weaken_L)
done

(*Useful with cancellation, disjunction*)
lemma LeadsTo_Un_duplicate: "F \<in> A LeadsTo (A' \<union> A') ==> F \<in> A LeadsTo A'"
by (simp add: Un_ac)

lemma LeadsTo_Un_duplicate2:
     "F \<in> A LeadsTo (A' \<union> C \<union> C) ==> F \<in> A LeadsTo (A' \<union> C)"
by (simp add: Un_ac)

lemma LeadsTo_UN:
    "[|(!!i. i \<in> I ==> F \<in> A(i) LeadsTo B); F \<in> program|]
     ==>F:(\<Union>i \<in> I. A(i)) LeadsTo B"
apply (simp add: LeadsTo_def)
apply (simp (no_asm_simp) del: UN_simps add: Int_UN_distrib)
apply (rule leadsTo_UN, auto)
done

(*Binary union introduction rule*)
lemma LeadsTo_Un:
     "[| F \<in> A LeadsTo C; F \<in> B LeadsTo C |] ==> F \<in> (A \<union> B) LeadsTo C"
apply (subst Un_eq_Union)
apply (rule LeadsTo_Union)
apply (auto dest: LeadsTo_type [THEN subsetD])
done

(*Lets us look at the starting state*)
lemma single_LeadsTo_I: 
    "[|(!!s. s \<in> A ==> F:{s} LeadsTo B); F \<in> program|]==>F \<in> A LeadsTo B"
apply (subst UN_singleton [symmetric], rule LeadsTo_UN, auto)
done

lemma subset_imp_LeadsTo: "[| A \<subseteq> B; F \<in> program |] ==> F \<in> A LeadsTo B"
apply (simp (no_asm_simp) add: LeadsTo_def)
apply (blast intro: subset_imp_leadsTo)
done

lemma empty_LeadsTo: "F:0 LeadsTo A \<longleftrightarrow> F \<in> program"
by (auto dest: LeadsTo_type [THEN subsetD]
            intro: empty_subsetI [THEN subset_imp_LeadsTo])
declare empty_LeadsTo [iff]

lemma LeadsTo_state: "F \<in> A LeadsTo state \<longleftrightarrow> F \<in> program"
by (auto dest: LeadsTo_type [THEN subsetD] simp add: LeadsTo_eq)
declare LeadsTo_state [iff]

lemma LeadsTo_weaken_R: "[| F \<in> A LeadsTo A';  A'<=B'|] ==> F \<in> A LeadsTo B'"
apply (unfold LeadsTo_def)
apply (auto intro: leadsTo_weaken_R)
done

lemma LeadsTo_weaken_L: "[| F \<in> A LeadsTo A'; B \<subseteq> A |] ==> F \<in> B LeadsTo A'"
apply (unfold LeadsTo_def)
apply (auto intro: leadsTo_weaken_L)
done

lemma LeadsTo_weaken: "[| F \<in> A LeadsTo A'; B<=A; A'<=B' |] ==> F \<in> B LeadsTo B'"
by (blast intro: LeadsTo_weaken_R LeadsTo_weaken_L LeadsTo_Trans)

lemma Always_LeadsTo_weaken: 
"[| F \<in> Always(C);  F \<in> A LeadsTo A'; C \<inter> B \<subseteq> A;   C \<inter> A' \<subseteq> B' |]  
      ==> F \<in> B LeadsTo B'"
apply (blast dest: Always_LeadsToI intro: LeadsTo_weaken Always_LeadsToD)
done

(** Two theorems for "proof lattices" **)

lemma LeadsTo_Un_post: "F \<in> A LeadsTo B ==> F:(A \<union> B) LeadsTo B"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_Un subset_imp_LeadsTo)

lemma LeadsTo_Trans_Un: "[| F \<in> A LeadsTo B;  F \<in> B LeadsTo C |]  
      ==> F \<in> (A \<union> B) LeadsTo C"
apply (blast intro: LeadsTo_Un subset_imp_LeadsTo LeadsTo_weaken_L LeadsTo_Trans dest: LeadsTo_type [THEN subsetD])
done

(** Distributive laws **)
lemma LeadsTo_Un_distrib: "(F \<in> (A \<union> B) LeadsTo C)  \<longleftrightarrow> (F \<in> A LeadsTo C & F \<in> B LeadsTo C)"
by (blast intro: LeadsTo_Un LeadsTo_weaken_L)

lemma LeadsTo_UN_distrib: "(F \<in> (\<Union>i \<in> I. A(i)) LeadsTo B) \<longleftrightarrow>  (\<forall>i \<in> I. F \<in> A(i) LeadsTo B) & F \<in> program"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_UN LeadsTo_weaken_L)

lemma LeadsTo_Union_distrib: "(F \<in> \<Union>(S) LeadsTo B)  \<longleftrightarrow>  (\<forall>A \<in> S. F \<in> A LeadsTo B) & F \<in> program"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_Union LeadsTo_weaken_L)

(** More rules using the premise "Always(I)" **)

lemma EnsuresI: "[| F:(A-B) Co (A \<union> B);  F \<in> transient (A-B) |] ==> F \<in> A Ensures B"
apply (simp add: Ensures_def Constrains_eq_constrains)
apply (blast intro: ensuresI constrains_weaken transient_strengthen dest: constrainsD2)
done

lemma Always_LeadsTo_Basis: "[| F \<in> Always(I); F \<in> (I \<inter> (A-A')) Co (A \<union> A');  
         F \<in> transient (I \<inter> (A-A')) |]    
  ==> F \<in> A LeadsTo A'"
apply (rule Always_LeadsToI, assumption)
apply (blast intro: EnsuresI LeadsTo_Basis Always_ConstrainsD [THEN Constrains_weaken] transient_strengthen)
done

(*Set difference: maybe combine with leadsTo_weaken_L??
  This is the most useful form of the "disjunction" rule*)
lemma LeadsTo_Diff:
     "[| F \<in> (A-B) LeadsTo C;  F \<in> (A \<inter> B) LeadsTo C |] ==> F \<in> A LeadsTo C"
by (blast intro: LeadsTo_Un LeadsTo_weaken)

lemma LeadsTo_UN_UN:  
     "[|(!!i. i \<in> I ==> F \<in> A(i) LeadsTo A'(i)); F \<in> program |]  
      ==> F \<in> (\<Union>i \<in> I. A(i)) LeadsTo (\<Union>i \<in> I. A'(i))"
apply (rule LeadsTo_Union, auto) 
apply (blast intro: LeadsTo_weaken_R)
done

(*Binary union version*)
lemma LeadsTo_Un_Un:
  "[| F \<in> A LeadsTo A'; F \<in> B LeadsTo B' |] ==> F:(A \<union> B) LeadsTo (A' \<union> B')"
by (blast intro: LeadsTo_Un LeadsTo_weaken_R)

(** The cancellation law **)

lemma LeadsTo_cancel2: "[| F \<in> A LeadsTo(A' \<union> B); F \<in> B LeadsTo B' |] ==> F \<in> A LeadsTo (A' \<union> B')"
by (blast intro: LeadsTo_Un_Un subset_imp_LeadsTo LeadsTo_Trans dest: LeadsTo_type [THEN subsetD])

lemma Un_Diff: "A \<union> (B - A) = A \<union> B"
by auto

lemma LeadsTo_cancel_Diff2: "[| F \<in> A LeadsTo (A' \<union> B); F \<in> (B-A') LeadsTo B' |] ==> F \<in> A LeadsTo (A' \<union> B')"
apply (rule LeadsTo_cancel2)
prefer 2 apply assumption
apply (simp (no_asm_simp) add: Un_Diff)
done

lemma LeadsTo_cancel1: "[| F \<in> A LeadsTo (B \<union> A'); F \<in> B LeadsTo B' |] ==> F \<in> A LeadsTo (B' \<union> A')"
apply (simp add: Un_commute)
apply (blast intro!: LeadsTo_cancel2)
done

lemma Diff_Un2: "(B - A) \<union> A = B \<union> A"
by auto

lemma LeadsTo_cancel_Diff1: "[| F \<in> A LeadsTo (B \<union> A'); F \<in> (B-A') LeadsTo B' |] ==> F \<in> A LeadsTo (B' \<union> A')"
apply (rule LeadsTo_cancel1)
prefer 2 apply assumption
apply (simp (no_asm_simp) add: Diff_Un2)
done

(** The impossibility law **)

(*The set "A" may be non-empty, but it contains no reachable states*)
lemma LeadsTo_empty: "F \<in> A LeadsTo 0 ==> F \<in> Always (state -A)"
apply (simp (no_asm_use) add: LeadsTo_def Always_eq_includes_reachable)
apply (cut_tac reachable_type)
apply (auto dest!: leadsTo_empty)
done

(** PSP \<in> Progress-Safety-Progress **)

(*Special case of PSP \<in> Misra's "stable conjunction"*)
lemma PSP_Stable: "[| F \<in> A LeadsTo A';  F \<in> Stable(B) |]==> F:(A \<inter> B) LeadsTo (A' \<inter> B)"
apply (simp add: LeadsTo_def Stable_eq_stable, clarify)
apply (drule psp_stable, assumption)
apply (simp add: Int_ac)
done

lemma PSP_Stable2: "[| F \<in> A LeadsTo A'; F \<in> Stable(B) |] ==> F \<in> (B \<inter> A) LeadsTo (B \<inter> A')"
apply (simp (no_asm_simp) add: PSP_Stable Int_ac)
done

lemma PSP: "[| F \<in> A LeadsTo A'; F \<in> B Co B'|]==> F \<in> (A \<inter> B') LeadsTo ((A' \<inter> B) \<union> (B' - B))"
apply (simp (no_asm_use) add: LeadsTo_def Constrains_eq_constrains)
apply (blast dest: psp intro: leadsTo_weaken)
done

lemma PSP2: "[| F \<in> A LeadsTo A'; F \<in> B Co B' |]==> F:(B' \<inter> A) LeadsTo ((B \<inter> A') \<union> (B' - B))"
by (simp (no_asm_simp) add: PSP Int_ac)

lemma PSP_Unless: 
"[| F \<in> A LeadsTo A'; F \<in> B Unless B'|]==> F:(A \<inter> B) LeadsTo ((A' \<inter> B) \<union> B')"
apply (unfold op_Unless_def)
apply (drule PSP, assumption)
apply (blast intro: LeadsTo_Diff LeadsTo_weaken subset_imp_LeadsTo)
done

(*** Induction rules ***)

(** Meta or object quantifier ????? **)
lemma LeadsTo_wf_induct: "[| wf(r);      
         \<forall>m \<in> I. F \<in> (A \<inter> f-``{m}) LeadsTo                      
                            ((A \<inter> f-``(converse(r) `` {m})) \<union> B);  
         field(r)<=I; A<=f-``I; F \<in> program |]  
      ==> F \<in> A LeadsTo B"
apply (simp (no_asm_use) add: LeadsTo_def)
apply auto
apply (erule_tac I = I and f = f in leadsTo_wf_induct, safe)
apply (drule_tac [2] x = m in bspec, safe)
apply (rule_tac [2] A' = "reachable (F) \<inter> (A \<inter> f -`` (converse (r) ``{m}) \<union> B) " in leadsTo_weaken_R)
apply (auto simp add: Int_assoc) 
done


lemma LessThan_induct: "[| \<forall>m \<in> nat. F:(A \<inter> f-``{m}) LeadsTo ((A \<inter> f-``m) \<union> B);  
      A<=f-``nat; F \<in> program |] ==> F \<in> A LeadsTo B"
apply (rule_tac A1 = nat and f1 = "%x. x" in wf_measure [THEN LeadsTo_wf_induct])
apply (simp_all add: nat_measure_field)
apply (simp add: ltI Image_inverse_lessThan vimage_def [symmetric])
done


(****** 
 To be ported ??? I am not sure.

  integ_0_le_induct
  LessThan_bounded_induct
  GreaterThan_bounded_induct

*****)

(*** Completion \<in> Binary and General Finite versions ***)

lemma Completion: "[| F \<in> A LeadsTo (A' \<union> C);  F \<in> A' Co (A' \<union> C);  
         F \<in> B LeadsTo (B' \<union> C);  F \<in> B' Co (B' \<union> C) |]  
      ==> F \<in> (A \<inter> B) LeadsTo ((A' \<inter> B') \<union> C)"
apply (simp (no_asm_use) add: LeadsTo_def Constrains_eq_constrains Int_Un_distrib)
apply (blast intro: completion leadsTo_weaken)
done

lemma Finite_completion_aux:
     "[| I \<in> Fin(X);F \<in> program |]  
      ==> (\<forall>i \<in> I. F \<in> (A(i)) LeadsTo (A'(i) \<union> C)) \<longrightarrow>   
          (\<forall>i \<in> I. F \<in> (A'(i)) Co (A'(i) \<union> C)) \<longrightarrow>  
          F \<in> (\<Inter>i \<in> I. A(i)) LeadsTo ((\<Inter>i \<in> I. A'(i)) \<union> C)"
apply (erule Fin_induct)
apply (auto simp del: INT_simps simp add: Inter_0)
apply (rule Completion, auto) 
apply (simp del: INT_simps add: INT_extend_simps)
apply (blast intro: Constrains_INT)
done

lemma Finite_completion: 
     "[| I \<in> Fin(X); !!i. i \<in> I ==> F \<in> A(i) LeadsTo (A'(i) \<union> C);  
         !!i. i \<in> I ==> F \<in> A'(i) Co (A'(i) \<union> C);  
         F \<in> program |]    
      ==> F \<in> (\<Inter>i \<in> I. A(i)) LeadsTo ((\<Inter>i \<in> I. A'(i)) \<union> C)"
by (blast intro: Finite_completion_aux [THEN mp, THEN mp])

lemma Stable_completion: 
     "[| F \<in> A LeadsTo A';  F \<in> Stable(A');    
         F \<in> B LeadsTo B';  F \<in> Stable(B') |]  
    ==> F \<in> (A \<inter> B) LeadsTo (A' \<inter> B')"
apply (unfold Stable_def)
apply (rule_tac C1 = 0 in Completion [THEN LeadsTo_weaken_R])
    prefer 5
    apply blast 
apply auto 
done

lemma Finite_stable_completion: 
     "[| I \<in> Fin(X);  
         (!!i. i \<in> I ==> F \<in> A(i) LeadsTo A'(i));  
         (!!i. i \<in> I ==>F \<in> Stable(A'(i)));   F \<in> program  |]  
      ==> F \<in> (\<Inter>i \<in> I. A(i)) LeadsTo (\<Inter>i \<in> I. A'(i))"
apply (unfold Stable_def)
apply (rule_tac C1 = 0 in Finite_completion [THEN LeadsTo_weaken_R], simp_all)
apply (rule_tac [3] subset_refl, auto) 
done

ML {*
(*proves "ensures/leadsTo" properties when the program is specified*)
fun ensures_tac ctxt sact =
  let val ss = simpset_of ctxt in
    SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
              etac @{thm Always_LeadsTo_Basis} 1 
                  ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
                  REPEAT (ares_tac [@{thm LeadsTo_Basis}, @{thm leadsTo_Basis},
                                    @{thm EnsuresI}, @{thm ensuresI}] 1),
              (*now there are two subgoals: co & transient*)
              simp_tac (ss addsimps (Program_Defs.get ctxt)) 2,
              res_inst_tac ctxt [(("act", 0), sact)] @{thm transientI} 2,
                 (*simplify the command's domain*)
              simp_tac (ss addsimps [@{thm domain_def}]) 3, 
              (* proving the domain part *)
             clarify_tac ctxt 3, dtac @{thm swap} 3, force_tac ctxt 4,
             rtac @{thm ReplaceI} 3, force_tac ctxt 3, force_tac ctxt 4,
             asm_full_simp_tac ss 3, rtac @{thm conjI} 3, simp_tac ss 4,
             REPEAT (rtac @{thm state_update_type} 3),
             constrains_tac ctxt 1,
             ALLGOALS (clarify_tac ctxt),
             ALLGOALS (asm_full_simp_tac (ss addsimps [@{thm st_set_def}])),
                        ALLGOALS (clarify_tac ctxt),
            ALLGOALS (asm_lr_simp_tac ss)])
  end;
*}

method_setup ensures = {*
    Args.goal_spec -- Scan.lift Args.name_source >>
    (fn (quant, s) => fn ctxt => SIMPLE_METHOD'' quant (ensures_tac ctxt s))
*} "for proving progress properties"

end
