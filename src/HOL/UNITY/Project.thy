(*  Title:      HOL/UNITY/Project.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Projections of state sets (also of actions and programs)

Inheritance of GUARANTEES properties under extension
*)

header{*Projections of State Sets*}

theory Project = Extend:

constdefs
  projecting :: "['c program => 'c set, 'a*'b => 'c, 
		  'a program, 'c program set, 'a program set] => bool"
    "projecting C h F X' X ==
       \<forall>G. extend h F\<squnion>G \<in> X' --> F\<squnion>project h (C G) G \<in> X"

  extending :: "['c program => 'c set, 'a*'b => 'c, 'a program, 
		 'c program set, 'a program set] => bool"
    "extending C h F Y' Y ==
       \<forall>G. extend h F  ok G --> F\<squnion>project h (C G) G \<in> Y
	      --> extend h F\<squnion>G \<in> Y'"

  subset_closed :: "'a set set => bool"
    "subset_closed U == \<forall>A \<in> U. Pow A \<subseteq> U"  


lemma (in Extend) project_extend_constrains_I:
     "F \<in> A co B ==> project h C (extend h F) \<in> A co B"
apply (auto simp add: extend_act_def project_act_def constrains_def)
done


subsection{*Safety*}

(*used below to prove Join_project_ensures*)
lemma (in Extend) project_unless [rule_format]:
     "[| G \<in> stable C;  project h C G \<in> A unless B |]  
      ==> G \<in> (C \<inter> extend_set h A) unless (extend_set h B)"
apply (simp add: unless_def project_constrains)
apply (blast dest: stable_constrains_Int intro: constrains_weaken)
done

(*Generalizes project_constrains to the program F\<squnion>project h C G
  useful with guarantees reasoning*)
lemma (in Extend) Join_project_constrains:
     "(F\<squnion>project h C G \<in> A co B)  =   
        (extend h F\<squnion>G \<in> (C \<inter> extend_set h A) co (extend_set h B) &   
         F \<in> A co B)"
apply (simp (no_asm) add: project_constrains)
apply (blast intro: extend_constrains [THEN iffD2, THEN constrains_weaken] 
             dest: constrains_imp_subset)
done

(*The condition is required to prove the left-to-right direction
  could weaken it to G \<in> (C \<inter> extend_set h A) co C*)
lemma (in Extend) Join_project_stable: 
     "extend h F\<squnion>G \<in> stable C  
      ==> (F\<squnion>project h C G \<in> stable A)  =   
          (extend h F\<squnion>G \<in> stable (C \<inter> extend_set h A) &   
           F \<in> stable A)"
apply (unfold stable_def)
apply (simp only: Join_project_constrains)
apply (blast intro: constrains_weaken dest: constrains_Int)
done

(*For using project_guarantees in particular cases*)
lemma (in Extend) project_constrains_I:
     "extend h F\<squnion>G \<in> extend_set h A co extend_set h B  
      ==> F\<squnion>project h C G \<in> A co B"
apply (simp add: project_constrains extend_constrains)
apply (blast intro: constrains_weaken dest: constrains_imp_subset)
done

lemma (in Extend) project_increasing_I: 
     "extend h F\<squnion>G \<in> increasing (func o f)  
      ==> F\<squnion>project h C G \<in> increasing func"
apply (unfold increasing_def stable_def)
apply (simp del: Join_constrains
            add: project_constrains_I extend_set_eq_Collect)
done

lemma (in Extend) Join_project_increasing:
     "(F\<squnion>project h UNIV G \<in> increasing func)  =   
      (extend h F\<squnion>G \<in> increasing (func o f))"
apply (rule iffI)
apply (erule_tac [2] project_increasing_I)
apply (simp del: Join_stable
            add: increasing_def Join_project_stable)
apply (auto simp add: extend_set_eq_Collect extend_stable [THEN iffD1])
done

(*The UNIV argument is essential*)
lemma (in Extend) project_constrains_D:
     "F\<squnion>project h UNIV G \<in> A co B  
      ==> extend h F\<squnion>G \<in> extend_set h A co extend_set h B"
by (simp add: project_constrains extend_constrains)


subsection{*"projecting" and union/intersection (no converses)*}

lemma projecting_Int: 
     "[| projecting C h F XA' XA;  projecting C h F XB' XB |]  
      ==> projecting C h F (XA' \<inter> XB') (XA \<inter> XB)"
by (unfold projecting_def, blast)

lemma projecting_Un: 
     "[| projecting C h F XA' XA;  projecting C h F XB' XB |]  
      ==> projecting C h F (XA' \<union> XB') (XA \<union> XB)"
by (unfold projecting_def, blast)

lemma projecting_INT: 
     "[| !!i. i \<in> I ==> projecting C h F (X' i) (X i) |]  
      ==> projecting C h F (\<Inter>i \<in> I. X' i) (\<Inter>i \<in> I. X i)"
by (unfold projecting_def, blast)

lemma projecting_UN: 
     "[| !!i. i \<in> I ==> projecting C h F (X' i) (X i) |]  
      ==> projecting C h F (\<Union>i \<in> I. X' i) (\<Union>i \<in> I. X i)"
by (unfold projecting_def, blast)

lemma projecting_weaken: 
     "[| projecting C h F X' X;  U'<=X';  X \<subseteq> U |] ==> projecting C h F U' U"
by (unfold projecting_def, auto)

lemma projecting_weaken_L: 
     "[| projecting C h F X' X;  U'<=X' |] ==> projecting C h F U' X"
by (unfold projecting_def, auto)

lemma extending_Int: 
     "[| extending C h F YA' YA;  extending C h F YB' YB |]  
      ==> extending C h F (YA' \<inter> YB') (YA \<inter> YB)"
by (unfold extending_def, blast)

lemma extending_Un: 
     "[| extending C h F YA' YA;  extending C h F YB' YB |]  
      ==> extending C h F (YA' \<union> YB') (YA \<union> YB)"
by (unfold extending_def, blast)

lemma extending_INT: 
     "[| !!i. i \<in> I ==> extending C h F (Y' i) (Y i) |]  
      ==> extending C h F (\<Inter>i \<in> I. Y' i) (\<Inter>i \<in> I. Y i)"
by (unfold extending_def, blast)

lemma extending_UN: 
     "[| !!i. i \<in> I ==> extending C h F (Y' i) (Y i) |]  
      ==> extending C h F (\<Union>i \<in> I. Y' i) (\<Union>i \<in> I. Y i)"
by (unfold extending_def, blast)

lemma extending_weaken: 
     "[| extending C h F Y' Y;  Y'<=V';  V \<subseteq> Y |] ==> extending C h F V' V"
by (unfold extending_def, auto)

lemma extending_weaken_L: 
     "[| extending C h F Y' Y;  Y'<=V' |] ==> extending C h F V' Y"
by (unfold extending_def, auto)

lemma projecting_UNIV: "projecting C h F X' UNIV"
by (simp add: projecting_def)

lemma (in Extend) projecting_constrains: 
     "projecting C h F (extend_set h A co extend_set h B) (A co B)"
apply (unfold projecting_def)
apply (blast intro: project_constrains_I)
done

lemma (in Extend) projecting_stable: 
     "projecting C h F (stable (extend_set h A)) (stable A)"
apply (unfold stable_def)
apply (rule projecting_constrains)
done

lemma (in Extend) projecting_increasing: 
     "projecting C h F (increasing (func o f)) (increasing func)"
apply (unfold projecting_def)
apply (blast intro: project_increasing_I)
done

lemma (in Extend) extending_UNIV: "extending C h F UNIV Y"
apply (simp (no_asm) add: extending_def)
done

lemma (in Extend) extending_constrains: 
     "extending (%G. UNIV) h F (extend_set h A co extend_set h B) (A co B)"
apply (unfold extending_def)
apply (blast intro: project_constrains_D)
done

lemma (in Extend) extending_stable: 
     "extending (%G. UNIV) h F (stable (extend_set h A)) (stable A)"
apply (unfold stable_def)
apply (rule extending_constrains)
done

lemma (in Extend) extending_increasing: 
     "extending (%G. UNIV) h F (increasing (func o f)) (increasing func)"
by (force simp only: extending_def Join_project_increasing)


subsection{*Reachability and project*}

(*In practice, C = reachable(...): the inclusion is equality*)
lemma (in Extend) reachable_imp_reachable_project:
     "[| reachable (extend h F\<squnion>G) \<subseteq> C;   
         z \<in> reachable (extend h F\<squnion>G) |]  
      ==> f z \<in> reachable (F\<squnion>project h C G)"
apply (erule reachable.induct)
apply (force intro!: reachable.Init simp add: split_extended_all, auto)
 apply (rule_tac act = x in reachable.Acts)
 apply auto
 apply (erule extend_act_D)
apply (rule_tac act1 = "Restrict C act"
       in project_act_I [THEN [3] reachable.Acts], auto) 
done

lemma (in Extend) project_Constrains_D: 
     "F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> A Co B   
      ==> extend h F\<squnion>G \<in> (extend_set h A) Co (extend_set h B)"
apply (unfold Constrains_def)
apply (simp del: Join_constrains
            add: Join_project_constrains, clarify)
apply (erule constrains_weaken)
apply (auto intro: reachable_imp_reachable_project)
done

lemma (in Extend) project_Stable_D: 
     "F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> Stable A   
      ==> extend h F\<squnion>G \<in> Stable (extend_set h A)"
apply (unfold Stable_def)
apply (simp (no_asm_simp) add: project_Constrains_D)
done

lemma (in Extend) project_Always_D: 
     "F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> Always A   
      ==> extend h F\<squnion>G \<in> Always (extend_set h A)"
apply (unfold Always_def)
apply (force intro: reachable.Init simp add: project_Stable_D split_extended_all)
done

lemma (in Extend) project_Increasing_D: 
     "F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> Increasing func   
      ==> extend h F\<squnion>G \<in> Increasing (func o f)"
apply (unfold Increasing_def, auto)
apply (subst extend_set_eq_Collect [symmetric])
apply (simp (no_asm_simp) add: project_Stable_D)
done


subsection{*Converse results for weak safety: benefits of the argument C *}

(*In practice, C = reachable(...): the inclusion is equality*)
lemma (in Extend) reachable_project_imp_reachable:
     "[| C \<subseteq> reachable(extend h F\<squnion>G);    
         x \<in> reachable (F\<squnion>project h C G) |]  
      ==> \<exists>y. h(x,y) \<in> reachable (extend h F\<squnion>G)"
apply (erule reachable.induct)
apply  (force intro: reachable.Init)
apply (auto simp add: project_act_def)
apply (force del: Id_in_Acts intro: reachable.Acts extend_act_D)+
done

lemma (in Extend) project_set_reachable_extend_eq:
     "project_set h (reachable (extend h F\<squnion>G)) =  
      reachable (F\<squnion>project h (reachable (extend h F\<squnion>G)) G)"
by (auto dest: subset_refl [THEN reachable_imp_reachable_project] 
               subset_refl [THEN reachable_project_imp_reachable])

(*UNUSED*)
lemma (in Extend) reachable_extend_Join_subset:
     "reachable (extend h F\<squnion>G) \<subseteq> C   
      ==> reachable (extend h F\<squnion>G) \<subseteq>  
          extend_set h (reachable (F\<squnion>project h C G))"
apply (auto dest: reachable_imp_reachable_project)
done

lemma (in Extend) project_Constrains_I: 
     "extend h F\<squnion>G \<in> (extend_set h A) Co (extend_set h B)   
      ==> F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> A Co B"
apply (unfold Constrains_def)
apply (simp del: Join_constrains
            add: Join_project_constrains extend_set_Int_distrib)
apply (rule conjI)
 prefer 2 
 apply (force elim: constrains_weaken_L
              dest!: extend_constrains_project_set
                     subset_refl [THEN reachable_project_imp_reachable])
apply (blast intro: constrains_weaken_L)
done

lemma (in Extend) project_Stable_I: 
     "extend h F\<squnion>G \<in> Stable (extend_set h A)   
      ==> F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> Stable A"
apply (unfold Stable_def)
apply (simp (no_asm_simp) add: project_Constrains_I)
done

lemma (in Extend) project_Always_I: 
     "extend h F\<squnion>G \<in> Always (extend_set h A)   
      ==> F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> Always A"
apply (unfold Always_def)
apply (auto simp add: project_Stable_I)
apply (unfold extend_set_def, blast)
done

lemma (in Extend) project_Increasing_I: 
    "extend h F\<squnion>G \<in> Increasing (func o f)   
     ==> F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> Increasing func"
apply (unfold Increasing_def, auto)
apply (simp (no_asm_simp) add: extend_set_eq_Collect project_Stable_I)
done

lemma (in Extend) project_Constrains:
     "(F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> A Co B)  =   
      (extend h F\<squnion>G \<in> (extend_set h A) Co (extend_set h B))"
apply (blast intro: project_Constrains_I project_Constrains_D)
done

lemma (in Extend) project_Stable: 
     "(F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> Stable A)  =   
      (extend h F\<squnion>G \<in> Stable (extend_set h A))"
apply (unfold Stable_def)
apply (rule project_Constrains)
done

lemma (in Extend) project_Increasing: 
   "(F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> Increasing func)  =  
    (extend h F\<squnion>G \<in> Increasing (func o f))"
apply (simp (no_asm_simp) add: Increasing_def project_Stable extend_set_eq_Collect)
done

subsection{*A lot of redundant theorems: all are proved to facilitate reasoning
    about guarantees.*}

lemma (in Extend) projecting_Constrains: 
     "projecting (%G. reachable (extend h F\<squnion>G)) h F  
                 (extend_set h A Co extend_set h B) (A Co B)"

apply (unfold projecting_def)
apply (blast intro: project_Constrains_I)
done

lemma (in Extend) projecting_Stable: 
     "projecting (%G. reachable (extend h F\<squnion>G)) h F  
                 (Stable (extend_set h A)) (Stable A)"
apply (unfold Stable_def)
apply (rule projecting_Constrains)
done

lemma (in Extend) projecting_Always: 
     "projecting (%G. reachable (extend h F\<squnion>G)) h F  
                 (Always (extend_set h A)) (Always A)"
apply (unfold projecting_def)
apply (blast intro: project_Always_I)
done

lemma (in Extend) projecting_Increasing: 
     "projecting (%G. reachable (extend h F\<squnion>G)) h F  
                 (Increasing (func o f)) (Increasing func)"
apply (unfold projecting_def)
apply (blast intro: project_Increasing_I)
done

lemma (in Extend) extending_Constrains: 
     "extending (%G. reachable (extend h F\<squnion>G)) h F  
                  (extend_set h A Co extend_set h B) (A Co B)"
apply (unfold extending_def)
apply (blast intro: project_Constrains_D)
done

lemma (in Extend) extending_Stable: 
     "extending (%G. reachable (extend h F\<squnion>G)) h F  
                  (Stable (extend_set h A)) (Stable A)"
apply (unfold extending_def)
apply (blast intro: project_Stable_D)
done

lemma (in Extend) extending_Always: 
     "extending (%G. reachable (extend h F\<squnion>G)) h F  
                  (Always (extend_set h A)) (Always A)"
apply (unfold extending_def)
apply (blast intro: project_Always_D)
done

lemma (in Extend) extending_Increasing: 
     "extending (%G. reachable (extend h F\<squnion>G)) h F  
                  (Increasing (func o f)) (Increasing func)"
apply (unfold extending_def)
apply (blast intro: project_Increasing_D)
done


subsection{*leadsETo in the precondition (??)*}

subsubsection{*transient*}

lemma (in Extend) transient_extend_set_imp_project_transient: 
     "[| G \<in> transient (C \<inter> extend_set h A);  G \<in> stable C |]   
      ==> project h C G \<in> transient (project_set h C \<inter> A)"
apply (auto simp add: transient_def Domain_project_act)
apply (subgoal_tac "act `` (C \<inter> extend_set h A) \<subseteq> - extend_set h A")
 prefer 2
 apply (simp add: stable_def constrains_def, blast) 
(*back to main goal*)
apply (erule_tac V = "?AA \<subseteq> -C \<union> ?BB" in thin_rl)
apply (drule bspec, assumption) 
apply (simp add: extend_set_def project_act_def, blast)
done

(*converse might hold too?*)
lemma (in Extend) project_extend_transient_D: 
     "project h C (extend h F) \<in> transient (project_set h C \<inter> D)  
      ==> F \<in> transient (project_set h C \<inter> D)"
apply (simp add: transient_def Domain_project_act, safe)
apply blast+
done


subsubsection{*ensures -- a primitive combining progress with safety*}

(*Used to prove project_leadsETo_I*)
lemma (in Extend) ensures_extend_set_imp_project_ensures:
     "[| extend h F \<in> stable C;  G \<in> stable C;   
         extend h F\<squnion>G \<in> A ensures B;  A-B = C \<inter> extend_set h D |]   
      ==> F\<squnion>project h C G   
            \<in> (project_set h C \<inter> project_set h A) ensures (project_set h B)"
apply (simp add: ensures_def project_constrains Join_transient extend_transient,
       clarify)
apply (intro conjI) 
(*first subgoal*)
apply (blast intro: extend_stable_project_set 
                  [THEN stableD, THEN constrains_Int, THEN constrains_weaken] 
             dest!: extend_constrains_project_set equalityD1)
(*2nd subgoal*)
apply (erule stableD [THEN constrains_Int, THEN constrains_weaken])
    apply assumption
   apply (simp (no_asm_use) add: extend_set_def)
   apply blast
 apply (simp add: extend_set_Int_distrib extend_set_Un_distrib)
 apply (blast intro!: extend_set_project_set [THEN subsetD], blast)
(*The transient part*)
apply auto
 prefer 2
 apply (force dest!: equalityD1
              intro: transient_extend_set_imp_project_transient
                         [THEN transient_strengthen])
apply (simp (no_asm_use) add: Int_Diff)
apply (force dest!: equalityD1 
             intro: transient_extend_set_imp_project_transient 
               [THEN project_extend_transient_D, THEN transient_strengthen])
done

text{*Transferring a transient property upwards*}
lemma (in Extend) project_transient_extend_set:
     "project h C G \<in> transient (project_set h C \<inter> A - B)
      ==> G \<in> transient (C \<inter> extend_set h A - extend_set h B)"
apply (simp add: transient_def project_set_def extend_set_def project_act_def)
apply (elim disjE bexE)
 apply (rule_tac x=Id in bexI)  
  apply (blast intro!: rev_bexI )+
done

lemma (in Extend) project_unless2 [rule_format]:
     "[| G \<in> stable C;  project h C G \<in> (project_set h C \<inter> A) unless B |]  
      ==> G \<in> (C \<inter> extend_set h A) unless (extend_set h B)"
by (auto dest: stable_constrains_Int intro: constrains_weaken
         simp add: unless_def project_constrains Diff_eq Int_assoc 
                   Int_extend_set_lemma)


lemma (in Extend) extend_unless:
   "[|extend h F \<in> stable C; F \<in> A unless B|]
    ==> extend h F \<in> C \<inter> extend_set h A unless extend_set h B"
apply (simp add: unless_def stable_def)
apply (drule constrains_Int) 
apply (erule extend_constrains [THEN iffD2]) 
apply (erule constrains_weaken, blast) 
apply blast 
done

(*Used to prove project_leadsETo_D*)
lemma (in Extend) Join_project_ensures [rule_format]:
     "[| extend h F\<squnion>G \<in> stable C;   
         F\<squnion>project h C G \<in> A ensures B |]  
      ==> extend h F\<squnion>G \<in> (C \<inter> extend_set h A) ensures (extend_set h B)"
apply (auto simp add: ensures_eq extend_unless project_unless)
apply (blast intro:  extend_transient [THEN iffD2] transient_strengthen)  
apply (blast intro: project_transient_extend_set transient_strengthen)  
done

text{*Lemma useful for both STRONG and WEAK progress, but the transient
    condition's very strong*}

(*The strange induction formula allows induction over the leadsTo
  assumption's non-atomic precondition*)
lemma (in Extend) PLD_lemma:
     "[| extend h F\<squnion>G \<in> stable C;   
         F\<squnion>project h C G \<in> (project_set h C \<inter> A) leadsTo B |]  
      ==> extend h F\<squnion>G \<in>  
          C \<inter> extend_set h (project_set h C \<inter> A) leadsTo (extend_set h B)"
apply (erule leadsTo_induct)
  apply (blast intro: leadsTo_Basis Join_project_ensures)
 apply (blast intro: psp_stable2 [THEN leadsTo_weaken_L] leadsTo_Trans)
apply (simp del: UN_simps add: Int_UN_distrib leadsTo_UN extend_set_Union)
done

lemma (in Extend) project_leadsTo_D_lemma:
     "[| extend h F\<squnion>G \<in> stable C;   
         F\<squnion>project h C G \<in> (project_set h C \<inter> A) leadsTo B |]  
      ==> extend h F\<squnion>G \<in> (C \<inter> extend_set h A) leadsTo (extend_set h B)"
apply (rule PLD_lemma [THEN leadsTo_weaken])
apply (auto simp add: split_extended_all)
done

lemma (in Extend) Join_project_LeadsTo:
     "[| C = (reachable (extend h F\<squnion>G));  
         F\<squnion>project h C G \<in> A LeadsTo B |]  
      ==> extend h F\<squnion>G \<in> (extend_set h A) LeadsTo (extend_set h B)"
by (simp del: Join_stable    add: LeadsTo_def project_leadsTo_D_lemma
                                  project_set_reachable_extend_eq)


subsection{*Towards the theorem @{text project_Ensures_D}*}

lemma (in Extend) project_ensures_D_lemma:
     "[| G \<in> stable ((C \<inter> extend_set h A) - (extend_set h B));   
         F\<squnion>project h C G \<in> (project_set h C \<inter> A) ensures B;   
         extend h F\<squnion>G \<in> stable C |]  
      ==> extend h F\<squnion>G \<in> (C \<inter> extend_set h A) ensures (extend_set h B)"
(*unless*)
apply (auto intro!: project_unless2 [unfolded unless_def] 
            intro: project_extend_constrains_I 
            simp add: ensures_def)
(*transient*)
(*A G-action cannot occur*)
 prefer 2
 apply (blast intro: project_transient_extend_set) 
(*An F-action*)
apply (force elim!: extend_transient [THEN iffD2, THEN transient_strengthen]
             simp add: split_extended_all)
done

lemma (in Extend) project_ensures_D:
     "[| F\<squnion>project h UNIV G \<in> A ensures B;   
         G \<in> stable (extend_set h A - extend_set h B) |]  
      ==> extend h F\<squnion>G \<in> (extend_set h A) ensures (extend_set h B)"
apply (rule project_ensures_D_lemma [of _ UNIV, THEN revcut_rl], auto)
done

lemma (in Extend) project_Ensures_D: 
     "[| F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> A Ensures B;   
         G \<in> stable (reachable (extend h F\<squnion>G) \<inter> extend_set h A -  
                     extend_set h B) |]  
      ==> extend h F\<squnion>G \<in> (extend_set h A) Ensures (extend_set h B)"
apply (unfold Ensures_def)
apply (rule project_ensures_D_lemma [THEN revcut_rl])
apply (auto simp add: project_set_reachable_extend_eq [symmetric])
done


subsection{*Guarantees*}

lemma (in Extend) project_act_Restrict_subset_project_act:
     "project_act h (Restrict C act) \<subseteq> project_act h act"
apply (auto simp add: project_act_def)
done
					   
							   
lemma (in Extend) subset_closed_ok_extend_imp_ok_project:
     "[| extend h F ok G; subset_closed (AllowedActs F) |]  
      ==> F ok project h C G"
apply (auto simp add: ok_def)
apply (rename_tac act) 
apply (drule subsetD, blast)
apply (rule_tac x = "Restrict C  (extend_act h act)" in rev_image_eqI)
apply simp +
apply (cut_tac project_act_Restrict_subset_project_act)
apply (auto simp add: subset_closed_def)
done


(*Weak precondition and postcondition
  Not clear that it has a converse [or that we want one!]*)

(*The raw version; 3rd premise could be weakened by adding the
  precondition extend h F\<squnion>G \<in> X' *)
lemma (in Extend) project_guarantees_raw:
 assumes xguary:  "F \<in> X guarantees Y"
     and closed:  "subset_closed (AllowedActs F)"
     and project: "!!G. extend h F\<squnion>G \<in> X' 
                        ==> F\<squnion>project h (C G) G \<in> X"
     and extend:  "!!G. [| F\<squnion>project h (C G) G \<in> Y |]  
                        ==> extend h F\<squnion>G \<in> Y'"
 shows "extend h F \<in> X' guarantees Y'"
apply (rule xguary [THEN guaranteesD, THEN extend, THEN guaranteesI])
apply (blast intro: closed subset_closed_ok_extend_imp_ok_project)
apply (erule project)
done

lemma (in Extend) project_guarantees:
     "[| F \<in> X guarantees Y;  subset_closed (AllowedActs F);  
         projecting C h F X' X;  extending C h F Y' Y |]  
      ==> extend h F \<in> X' guarantees Y'"
apply (rule guaranteesI)
apply (auto simp add: guaranteesD projecting_def extending_def
                      subset_closed_ok_extend_imp_ok_project)
done


(*It seems that neither "guarantees" law can be proved from the other.*)


subsection{*guarantees corollaries*}

subsubsection{*Some could be deleted: the required versions are easy to prove*}

lemma (in Extend) extend_guar_increasing:
     "[| F \<in> UNIV guarantees increasing func;   
         subset_closed (AllowedActs F) |]  
      ==> extend h F \<in> X' guarantees increasing (func o f)"
apply (erule project_guarantees)
apply (rule_tac [3] extending_increasing)
apply (rule_tac [2] projecting_UNIV, auto)
done

lemma (in Extend) extend_guar_Increasing:
     "[| F \<in> UNIV guarantees Increasing func;   
         subset_closed (AllowedActs F) |]  
      ==> extend h F \<in> X' guarantees Increasing (func o f)"
apply (erule project_guarantees)
apply (rule_tac [3] extending_Increasing)
apply (rule_tac [2] projecting_UNIV, auto)
done

lemma (in Extend) extend_guar_Always:
     "[| F \<in> Always A guarantees Always B;   
         subset_closed (AllowedActs F) |]  
      ==> extend h F                    
            \<in> Always(extend_set h A) guarantees Always(extend_set h B)"
apply (erule project_guarantees)
apply (rule_tac [3] extending_Always)
apply (rule_tac [2] projecting_Always, auto)
done


subsubsection{*Guarantees with a leadsTo postcondition*}

lemma (in Extend) project_leadsTo_D:
     "F\<squnion>project h UNIV G \<in> A leadsTo B
      ==> extend h F\<squnion>G \<in> (extend_set h A) leadsTo (extend_set h B)"
apply (rule_tac C1 = UNIV in project_leadsTo_D_lemma [THEN leadsTo_weaken], auto)
done

lemma (in Extend) project_LeadsTo_D:
     "F\<squnion>project h (reachable (extend h F\<squnion>G)) G \<in> A LeadsTo B   
       ==> extend h F\<squnion>G \<in> (extend_set h A) LeadsTo (extend_set h B)"
apply (rule refl [THEN Join_project_LeadsTo], auto)
done

lemma (in Extend) extending_leadsTo: 
     "extending (%G. UNIV) h F  
                (extend_set h A leadsTo extend_set h B) (A leadsTo B)"
apply (unfold extending_def)
apply (blast intro: project_leadsTo_D)
done

lemma (in Extend) extending_LeadsTo: 
     "extending (%G. reachable (extend h F\<squnion>G)) h F  
                (extend_set h A LeadsTo extend_set h B) (A LeadsTo B)"
apply (unfold extending_def)
apply (blast intro: project_LeadsTo_D)
done

ML
{*
val projecting_Int = thm "projecting_Int";
val projecting_Un = thm "projecting_Un";
val projecting_INT = thm "projecting_INT";
val projecting_UN = thm "projecting_UN";
val projecting_weaken = thm "projecting_weaken";
val projecting_weaken_L = thm "projecting_weaken_L";
val extending_Int = thm "extending_Int";
val extending_Un = thm "extending_Un";
val extending_INT = thm "extending_INT";
val extending_UN = thm "extending_UN";
val extending_weaken = thm "extending_weaken";
val extending_weaken_L = thm "extending_weaken_L";
val projecting_UNIV = thm "projecting_UNIV";
*}

end
