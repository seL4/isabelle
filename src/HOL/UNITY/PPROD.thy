(*  Title:      HOL/UNITY/PPROD.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Abstraction over replicated components (PLam)
General products of programs (Pi operation)

Some dead wood here!
*)

theory PPROD = Lift_prog:

constdefs

  PLam  :: "[nat set, nat => ('b * ((nat=>'b) * 'c)) program]
            => ((nat=>'b) * 'c) program"
    "PLam I F == JN i:I. lift i (F i)"

syntax
  "@PLam" :: "[pttrn, nat set, 'b set] => (nat => 'b) set"
              ("(3plam _:_./ _)" 10)

translations
  "plam x:A. B"   == "PLam A (%x. B)"


(*** Basic properties ***)

lemma Init_PLam: "Init (PLam I F) = (INT i:I. lift_set i (Init (F i)))"
apply (simp (no_asm) add: PLam_def lift_def lift_set_def)
done

declare Init_PLam [simp]

lemma PLam_empty: "PLam {} F = SKIP"
apply (simp (no_asm) add: PLam_def)
done

lemma PLam_SKIP: "(plam i: I. SKIP) = SKIP"
apply (simp (no_asm) add: PLam_def lift_SKIP JN_constant)
done

declare PLam_SKIP [simp] PLam_empty [simp]

lemma PLam_insert: "PLam (insert i I) F = (lift i (F i)) Join (PLam I F)"
by (unfold PLam_def, auto)

lemma PLam_component_iff: "((PLam I F) <= H) = (ALL i: I. lift i (F i) <= H)"
apply (simp (no_asm) add: PLam_def JN_component_iff)
done

lemma component_PLam: "i : I ==> lift i (F i) <= (PLam I F)"
apply (unfold PLam_def)
(*blast_tac doesn't use HO unification*)
apply (fast intro: component_JN)
done


(** Safety & Progress: but are they used anywhere? **)

lemma PLam_constrains: 
     "[| i : I;  ALL j. F j : preserves snd |] ==>   
      (PLam I F : (lift_set i (A <*> UNIV)) co  
                  (lift_set i (B <*> UNIV)))  =   
      (F i : (A <*> UNIV) co (B <*> UNIV))"
apply (simp (no_asm_simp) add: PLam_def JN_constrains)
apply (subst insert_Diff [symmetric], assumption)
apply (simp (no_asm_simp) add: lift_constrains)
apply (blast intro: constrains_imp_lift_constrains)
done

lemma PLam_stable: 
     "[| i : I;  ALL j. F j : preserves snd |]   
      ==> (PLam I F : stable (lift_set i (A <*> UNIV))) =  
          (F i : stable (A <*> UNIV))"
apply (simp (no_asm_simp) add: stable_def PLam_constrains)
done

lemma PLam_transient: 
     "i : I ==>  
    PLam I F : transient A = (EX i:I. lift i (F i) : transient A)"
apply (simp (no_asm_simp) add: JN_transient PLam_def)
done

(*This holds because the F j cannot change (lift_set i)*)
lemma PLam_ensures: 
     "[| i : I;  F i : (A <*> UNIV) ensures (B <*> UNIV);   
         ALL j. F j : preserves snd |] ==>   
      PLam I F : lift_set i (A <*> UNIV) ensures lift_set i (B <*> UNIV)"
apply (auto simp add: ensures_def PLam_constrains PLam_transient lift_transient_eq_disj lift_set_Un_distrib [symmetric] lift_set_Diff_distrib [symmetric] Times_Un_distrib1 [symmetric] Times_Diff_distrib1 [symmetric])
done

lemma PLam_leadsTo_Basis: 
     "[| i : I;   
         F i : ((A <*> UNIV) - (B <*> UNIV)) co  
               ((A <*> UNIV) Un (B <*> UNIV));   
         F i : transient ((A <*> UNIV) - (B <*> UNIV));   
         ALL j. F j : preserves snd |] ==>   
      PLam I F : lift_set i (A <*> UNIV) leadsTo lift_set i (B <*> UNIV)"
by (rule PLam_ensures [THEN leadsTo_Basis], rule_tac [2] ensuresI)



(** invariant **)

lemma invariant_imp_PLam_invariant: 
     "[| F i : invariant (A <*> UNIV);  i : I;   
         ALL j. F j : preserves snd |]  
      ==> PLam I F : invariant (lift_set i (A <*> UNIV))"
by (auto simp add: PLam_stable invariant_def)


lemma PLam_preserves_fst [simp]:
     "ALL j. F j : preserves snd  
      ==> (PLam I F : preserves (v o sub j o fst)) =  
          (if j: I then F j : preserves (v o fst) else True)"
by (simp (no_asm_simp) add: PLam_def lift_preserves_sub)

lemma PLam_preserves_snd [simp,intro]:
     "ALL j. F j : preserves snd ==> PLam I F : preserves snd"
by (simp (no_asm_simp) add: PLam_def lift_preserves_snd_I)



(*** guarantees properties ***)

(*This rule looks unsatisfactory because it refers to "lift".  One must use
  lift_guarantees_eq_lift_inv to rewrite the first subgoal and
  something like lift_preserves_sub to rewrite the third.  However there's
  no obvious way to alternative for the third premise.*)
lemma guarantees_PLam_I: 
    "[| lift i (F i): X guarantees Y;  i : I;   
        OK I (%i. lift i (F i)) |]   
     ==> (PLam I F) : X guarantees Y"
apply (unfold PLam_def)
apply (simp (no_asm_simp) add: guarantees_JN_I)
done

lemma Allowed_PLam [simp]:
     "Allowed (PLam I F) = (INT i:I. lift i ` Allowed(F i))"
by (simp (no_asm) add: PLam_def)


lemma PLam_preserves [simp]:
     "(PLam I F) : preserves v = (ALL i:I. F i : preserves (v o lift_map i))"
by (simp (no_asm) add: PLam_def lift_def rename_preserves)


(**UNUSED
    (*The f0 premise ensures that the product is well-defined.*)
    lemma PLam_invariant_imp_invariant: 
     "[| PLam I F : invariant (lift_set i A);  i : I;   
             f0: Init (PLam I F) |] ==> F i : invariant A"
    apply (auto simp add: invariant_def)
    apply (drule_tac c = "f0 (i:=x) " in subsetD)
    apply auto
    done

    lemma PLam_invariant: 
     "[| i : I;  f0: Init (PLam I F) |]  
          ==> (PLam I F : invariant (lift_set i A)) = (F i : invariant A)"
    apply (blast intro: invariant_imp_PLam_invariant PLam_invariant_imp_invariant)
    done

    (*The f0 premise isn't needed if F is a constant program because then
      we get an initial state by replicating that of F*)
    lemma reachable_PLam: 
     "i : I  
          ==> ((plam x:I. F) : invariant (lift_set i A)) = (F : invariant A)"
    apply (auto simp add: invariant_def)
    done
**)


(**UNUSED
    (** Reachability **)

    Goal "[| f : reachable (PLam I F);  i : I |] ==> f i : reachable (F i)"
    apply (erule reachable.induct)
    apply (auto intro: reachable.intrs)
    done

    (*Result to justify a re-organization of this file*)
    lemma "{f. ALL i:I. f i : R i} = (INT i:I. lift_set i (R i))"
    by auto

    lemma reachable_PLam_subset1: 
     "reachable (PLam I F) <= (INT i:I. lift_set i (reachable (F i)))"
    apply (force dest!: reachable_PLam)
    done

    (*simplify using reachable_lift??*)
    lemma reachable_lift_Join_PLam [rule_format]:
      "[| i ~: I;  A : reachable (F i) |]      
       ==> ALL f. f : reachable (PLam I F)       
                  --> f(i:=A) : reachable (lift i (F i) Join PLam I F)"
    apply (erule reachable.induct)
    apply (ALLGOALS Clarify_tac)
    apply (erule reachable.induct)
    (*Init, Init case*)
    apply (force intro: reachable.intrs)
    (*Init of F, action of PLam F case*)
    apply (rule_tac act = act in reachable.Acts)
    apply force
    apply assumption
    apply (force intro: ext)
    (*induction over the 2nd "reachable" assumption*)
    apply (erule_tac xa = f in reachable.induct)
    (*Init of PLam F, action of F case*)
    apply (rule_tac act = "lift_act i act" in reachable.Acts)
    apply force
    apply (force intro: reachable.Init)
    apply (force intro: ext simp add: lift_act_def)
    (*last case: an action of PLam I F*)
    apply (rule_tac act = acta in reachable.Acts)
    apply force
    apply assumption
    apply (force intro: ext)
    done


    (*The index set must be finite: otherwise infinitely many copies of F can
      perform actions, and PLam can never catch up in finite time.*)
    lemma reachable_PLam_subset2: 
     "finite I  
          ==> (INT i:I. lift_set i (reachable (F i))) <= reachable (PLam I F)"
    apply (erule finite_induct)
    apply (simp (no_asm))
    apply (force dest: reachable_lift_Join_PLam simp add: PLam_insert)
    done

    lemma reachable_PLam_eq: 
     "finite I ==>  
          reachable (PLam I F) = (INT i:I. lift_set i (reachable (F i)))"
    apply (REPEAT_FIRST (ares_tac [equalityI, reachable_PLam_subset1, reachable_PLam_subset2]))
    done


    (** Co **)

    lemma Constrains_imp_PLam_Constrains: 
     "[| F i : A Co B;  i: I;  finite I |]   
          ==> PLam I F : (lift_set i A) Co (lift_set i B)"
    apply (auto simp add: Constrains_def Collect_conj_eq [symmetric] reachable_PLam_eq)
    apply (auto simp add: constrains_def PLam_def)
    apply (REPEAT (blast intro: reachable.intrs))
    done



    lemma PLam_Constrains: 
     "[| i: I;  finite I;  f0: Init (PLam I F) |]   
          ==> (PLam I F : (lift_set i A) Co (lift_set i B)) =   
              (F i : A Co B)"
    apply (blast intro: Constrains_imp_PLam_Constrains PLam_Constrains_imp_Constrains)
    done

    lemma PLam_Stable: 
     "[| i: I;  finite I;  f0: Init (PLam I F) |]   
          ==> (PLam I F : Stable (lift_set i A)) = (F i : Stable A)"
    apply (simp (no_asm_simp) del: Init_PLam add: Stable_def PLam_Constrains)
    done


    (** const_PLam (no dependence on i) doesn't require the f0 premise **)

    lemma const_PLam_Constrains: 
     "[| i: I;  finite I |]   
          ==> ((plam x:I. F) : (lift_set i A) Co (lift_set i B)) =   
              (F : A Co B)"
    apply (blast intro: Constrains_imp_PLam_Constrains const_PLam_Constrains_imp_Constrains)
    done

    lemma const_PLam_Stable: 
     "[| i: I;  finite I |]   
          ==> ((plam x:I. F) : Stable (lift_set i A)) = (F : Stable A)"
    apply (simp (no_asm_simp) add: Stable_def const_PLam_Constrains)
    done

    lemma const_PLam_Increasing: 
	 "[| i: I;  finite I |]   
          ==> ((plam x:I. F) : Increasing (f o sub i)) = (F : Increasing f)"
    apply (unfold Increasing_def)
    apply (subgoal_tac "ALL z. {s. z <= (f o sub i) s} = lift_set i {s. z <= f s}")
    apply (asm_simp_tac (simpset () add: lift_set_sub) 2)
    apply (simp add: finite_lessThan const_PLam_Stable)
    done
**)


end
