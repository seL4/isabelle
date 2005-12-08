(*  ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Theory ported from HOL.
*)

header{*Weak LeadsTo relation (restricted to the set of reachable states)*}

theory SubstAx
imports WFair Constrains 

begin

constdefs
  (* The definitions below are not `conventional', but yields simpler rules *)
   Ensures :: "[i,i] => i"            (infixl "Ensures" 60)
    "A Ensures B == {F:program. F : (reachable(F) Int A) ensures (reachable(F) Int B) }"

  LeadsTo :: "[i, i] => i"            (infixl "LeadsTo" 60)
    "A LeadsTo B == {F:program. F:(reachable(F) Int A) leadsTo (reachable(F) Int B)}"

syntax (xsymbols)
  "LeadsTo" :: "[i, i] => i" (infixl " \<longmapsto>w " 60)



(*Resembles the previous definition of LeadsTo*)

(* Equivalence with the HOL-like definition *)
lemma LeadsTo_eq: 
"st_set(B)==> A LeadsTo B = {F \<in> program. F:(reachable(F) Int A) leadsTo B}"
apply (unfold LeadsTo_def)
apply (blast dest: psp_stable2 leadsToD2 constrainsD2 intro: leadsTo_weaken)
done

lemma LeadsTo_type: "A LeadsTo B <=program"
by (unfold LeadsTo_def, auto)

(*** Specialized laws for handling invariants ***)

(** Conjoining an Always property **)
lemma Always_LeadsTo_pre: "F \<in> Always(I) ==> (F:(I Int A) LeadsTo A') <-> (F \<in> A LeadsTo A')"
by (simp add: LeadsTo_def Always_eq_includes_reachable Int_absorb2 Int_assoc [symmetric] leadsToD2)

lemma Always_LeadsTo_post: "F \<in> Always(I) ==> (F \<in> A LeadsTo (I Int A')) <-> (F \<in> A LeadsTo A')"
apply (unfold LeadsTo_def)
apply (simp add: Always_eq_includes_reachable Int_absorb2 Int_assoc [symmetric] leadsToD2)
done

(* Like 'Always_LeadsTo_pre RS iffD1', but with premises in the good order *)
lemma Always_LeadsToI: "[| F \<in> Always(C); F \<in> (C Int A) LeadsTo A' |] ==> F \<in> A LeadsTo A'"
by (blast intro: Always_LeadsTo_pre [THEN iffD1])

(* Like 'Always_LeadsTo_post RS iffD2', but with premises in the good order *)
lemma Always_LeadsToD: "[| F \<in> Always(C);  F \<in> A LeadsTo A' |] ==> F \<in> A LeadsTo (C Int A')"
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
"[|(!!A. A \<in> S ==> F \<in> A LeadsTo B); F \<in> program|]==>F \<in> Union(S) LeadsTo B"
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
lemma LeadsTo_Un_duplicate: "F \<in> A LeadsTo (A' Un A') ==> F \<in> A LeadsTo A'"
by (simp add: Un_ac)

lemma LeadsTo_Un_duplicate2:
     "F \<in> A LeadsTo (A' Un C Un C) ==> F \<in> A LeadsTo (A' Un C)"
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
     "[| F \<in> A LeadsTo C; F \<in> B LeadsTo C |] ==> F \<in> (A Un B) LeadsTo C"
apply (subst Un_eq_Union)
apply (rule LeadsTo_Union)
apply (auto dest: LeadsTo_type [THEN subsetD])
done

(*Lets us look at the starting state*)
lemma single_LeadsTo_I: 
    "[|(!!s. s \<in> A ==> F:{s} LeadsTo B); F \<in> program|]==>F \<in> A LeadsTo B"
apply (subst UN_singleton [symmetric], rule LeadsTo_UN, auto)
done

lemma subset_imp_LeadsTo: "[| A <= B; F \<in> program |] ==> F \<in> A LeadsTo B"
apply (simp (no_asm_simp) add: LeadsTo_def)
apply (blast intro: subset_imp_leadsTo)
done

lemma empty_LeadsTo: "F:0 LeadsTo A <-> F \<in> program"
by (auto dest: LeadsTo_type [THEN subsetD]
            intro: empty_subsetI [THEN subset_imp_LeadsTo])
declare empty_LeadsTo [iff]

lemma LeadsTo_state: "F \<in> A LeadsTo state <-> F \<in> program"
by (auto dest: LeadsTo_type [THEN subsetD] simp add: LeadsTo_eq)
declare LeadsTo_state [iff]

lemma LeadsTo_weaken_R: "[| F \<in> A LeadsTo A';  A'<=B'|] ==> F \<in> A LeadsTo B'"
apply (unfold LeadsTo_def)
apply (auto intro: leadsTo_weaken_R)
done

lemma LeadsTo_weaken_L: "[| F \<in> A LeadsTo A'; B <= A |] ==> F \<in> B LeadsTo A'"
apply (unfold LeadsTo_def)
apply (auto intro: leadsTo_weaken_L)
done

lemma LeadsTo_weaken: "[| F \<in> A LeadsTo A'; B<=A; A'<=B' |] ==> F \<in> B LeadsTo B'"
by (blast intro: LeadsTo_weaken_R LeadsTo_weaken_L LeadsTo_Trans)

lemma Always_LeadsTo_weaken: 
"[| F \<in> Always(C);  F \<in> A LeadsTo A'; C Int B <= A;   C Int A' <= B' |]  
      ==> F \<in> B LeadsTo B'"
apply (blast dest: Always_LeadsToI intro: LeadsTo_weaken Always_LeadsToD)
done

(** Two theorems for "proof lattices" **)

lemma LeadsTo_Un_post: "F \<in> A LeadsTo B ==> F:(A Un B) LeadsTo B"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_Un subset_imp_LeadsTo)

lemma LeadsTo_Trans_Un: "[| F \<in> A LeadsTo B;  F \<in> B LeadsTo C |]  
      ==> F \<in> (A Un B) LeadsTo C"
apply (blast intro: LeadsTo_Un subset_imp_LeadsTo LeadsTo_weaken_L LeadsTo_Trans dest: LeadsTo_type [THEN subsetD])
done

(** Distributive laws **)
lemma LeadsTo_Un_distrib: "(F \<in> (A Un B) LeadsTo C)  <-> (F \<in> A LeadsTo C & F \<in> B LeadsTo C)"
by (blast intro: LeadsTo_Un LeadsTo_weaken_L)

lemma LeadsTo_UN_distrib: "(F \<in> (\<Union>i \<in> I. A(i)) LeadsTo B) <->  (\<forall>i \<in> I. F \<in> A(i) LeadsTo B) & F \<in> program"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_UN LeadsTo_weaken_L)

lemma LeadsTo_Union_distrib: "(F \<in> Union(S) LeadsTo B)  <->  (\<forall>A \<in> S. F \<in> A LeadsTo B) & F \<in> program"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_Union LeadsTo_weaken_L)

(** More rules using the premise "Always(I)" **)

lemma EnsuresI: "[| F:(A-B) Co (A Un B);  F \<in> transient (A-B) |] ==> F \<in> A Ensures B"
apply (simp add: Ensures_def Constrains_eq_constrains)
apply (blast intro: ensuresI constrains_weaken transient_strengthen dest: constrainsD2)
done

lemma Always_LeadsTo_Basis: "[| F \<in> Always(I); F \<in> (I Int (A-A')) Co (A Un A');  
         F \<in> transient (I Int (A-A')) |]    
  ==> F \<in> A LeadsTo A'"
apply (rule Always_LeadsToI, assumption)
apply (blast intro: EnsuresI LeadsTo_Basis Always_ConstrainsD [THEN Constrains_weaken] transient_strengthen)
done

(*Set difference: maybe combine with leadsTo_weaken_L??
  This is the most useful form of the "disjunction" rule*)
lemma LeadsTo_Diff:
     "[| F \<in> (A-B) LeadsTo C;  F \<in> (A Int B) LeadsTo C |] ==> F \<in> A LeadsTo C"
by (blast intro: LeadsTo_Un LeadsTo_weaken)

lemma LeadsTo_UN_UN:  
     "[|(!!i. i \<in> I ==> F \<in> A(i) LeadsTo A'(i)); F \<in> program |]  
      ==> F \<in> (\<Union>i \<in> I. A(i)) LeadsTo (\<Union>i \<in> I. A'(i))"
apply (rule LeadsTo_Union, auto) 
apply (blast intro: LeadsTo_weaken_R)
done

(*Binary union version*)
lemma LeadsTo_Un_Un:
  "[| F \<in> A LeadsTo A'; F \<in> B LeadsTo B' |] ==> F:(A Un B) LeadsTo (A' Un B')"
by (blast intro: LeadsTo_Un LeadsTo_weaken_R)

(** The cancellation law **)

lemma LeadsTo_cancel2: "[| F \<in> A LeadsTo(A' Un B); F \<in> B LeadsTo B' |] ==> F \<in> A LeadsTo (A' Un B')"
by (blast intro: LeadsTo_Un_Un subset_imp_LeadsTo LeadsTo_Trans dest: LeadsTo_type [THEN subsetD])

lemma Un_Diff: "A Un (B - A) = A Un B"
by auto

lemma LeadsTo_cancel_Diff2: "[| F \<in> A LeadsTo (A' Un B); F \<in> (B-A') LeadsTo B' |] ==> F \<in> A LeadsTo (A' Un B')"
apply (rule LeadsTo_cancel2)
prefer 2 apply assumption
apply (simp (no_asm_simp) add: Un_Diff)
done

lemma LeadsTo_cancel1: "[| F \<in> A LeadsTo (B Un A'); F \<in> B LeadsTo B' |] ==> F \<in> A LeadsTo (B' Un A')"
apply (simp add: Un_commute)
apply (blast intro!: LeadsTo_cancel2)
done

lemma Diff_Un2: "(B - A) Un A = B Un A"
by auto

lemma LeadsTo_cancel_Diff1: "[| F \<in> A LeadsTo (B Un A'); F \<in> (B-A') LeadsTo B' |] ==> F \<in> A LeadsTo (B' Un A')"
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
lemma PSP_Stable: "[| F \<in> A LeadsTo A';  F \<in> Stable(B) |]==> F:(A Int B) LeadsTo (A' Int B)"
apply (simp add: LeadsTo_def Stable_eq_stable, clarify)
apply (drule psp_stable, assumption)
apply (simp add: Int_ac)
done

lemma PSP_Stable2: "[| F \<in> A LeadsTo A'; F \<in> Stable(B) |] ==> F \<in> (B Int A) LeadsTo (B Int A')"
apply (simp (no_asm_simp) add: PSP_Stable Int_ac)
done

lemma PSP: "[| F \<in> A LeadsTo A'; F \<in> B Co B'|]==> F \<in> (A Int B') LeadsTo ((A' Int B) Un (B' - B))"
apply (simp (no_asm_use) add: LeadsTo_def Constrains_eq_constrains)
apply (blast dest: psp intro: leadsTo_weaken)
done

lemma PSP2: "[| F \<in> A LeadsTo A'; F \<in> B Co B' |]==> F:(B' Int A) LeadsTo ((B Int A') Un (B' - B))"
by (simp (no_asm_simp) add: PSP Int_ac)

lemma PSP_Unless: 
"[| F \<in> A LeadsTo A'; F \<in> B Unless B'|]==> F:(A Int B) LeadsTo ((A' Int B) Un B')"
apply (unfold Unless_def)
apply (drule PSP, assumption)
apply (blast intro: LeadsTo_Diff LeadsTo_weaken subset_imp_LeadsTo)
done

(*** Induction rules ***)

(** Meta or object quantifier ????? **)
lemma LeadsTo_wf_induct: "[| wf(r);      
         \<forall>m \<in> I. F \<in> (A Int f-``{m}) LeadsTo                      
                            ((A Int f-``(converse(r) `` {m})) Un B);  
         field(r)<=I; A<=f-``I; F \<in> program |]  
      ==> F \<in> A LeadsTo B"
apply (simp (no_asm_use) add: LeadsTo_def)
apply auto
apply (erule_tac I = I and f = f in leadsTo_wf_induct, safe)
apply (drule_tac [2] x = m in bspec, safe)
apply (rule_tac [2] A' = "reachable (F) Int (A Int f -`` (converse (r) ``{m}) Un B) " in leadsTo_weaken_R)
apply (auto simp add: Int_assoc) 
done


lemma LessThan_induct: "[| \<forall>m \<in> nat. F:(A Int f-``{m}) LeadsTo ((A Int f-``m) Un B);  
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

lemma Completion: "[| F \<in> A LeadsTo (A' Un C);  F \<in> A' Co (A' Un C);  
         F \<in> B LeadsTo (B' Un C);  F \<in> B' Co (B' Un C) |]  
      ==> F \<in> (A Int B) LeadsTo ((A' Int B') Un C)"
apply (simp (no_asm_use) add: LeadsTo_def Constrains_eq_constrains Int_Un_distrib)
apply (blast intro: completion leadsTo_weaken)
done

lemma Finite_completion_aux:
     "[| I \<in> Fin(X);F \<in> program |]  
      ==> (\<forall>i \<in> I. F \<in> (A(i)) LeadsTo (A'(i) Un C)) -->   
          (\<forall>i \<in> I. F \<in> (A'(i)) Co (A'(i) Un C)) -->  
          F \<in> (\<Inter>i \<in> I. A(i)) LeadsTo ((\<Inter>i \<in> I. A'(i)) Un C)"
apply (erule Fin_induct)
apply (auto simp del: INT_simps simp add: Inter_0)
apply (rule Completion, auto) 
apply (simp del: INT_simps add: INT_extend_simps)
apply (blast intro: Constrains_INT)
done

lemma Finite_completion: 
     "[| I \<in> Fin(X); !!i. i \<in> I ==> F \<in> A(i) LeadsTo (A'(i) Un C);  
         !!i. i \<in> I ==> F \<in> A'(i) Co (A'(i) Un C);  
         F \<in> program |]    
      ==> F \<in> (\<Inter>i \<in> I. A(i)) LeadsTo ((\<Inter>i \<in> I. A'(i)) Un C)"
by (blast intro: Finite_completion_aux [THEN mp, THEN mp])

lemma Stable_completion: 
     "[| F \<in> A LeadsTo A';  F \<in> Stable(A');    
         F \<in> B LeadsTo B';  F \<in> Stable(B') |]  
    ==> F \<in> (A Int B) LeadsTo (A' Int B')"
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

ML
{*
val LeadsTo_eq = thm "LeadsTo_eq";
val LeadsTo_type = thm "LeadsTo_type";
val Always_LeadsTo_pre = thm "Always_LeadsTo_pre";
val Always_LeadsTo_post = thm "Always_LeadsTo_post";
val Always_LeadsToI = thm "Always_LeadsToI";
val Always_LeadsToD = thm "Always_LeadsToD";
val LeadsTo_Basis = thm "LeadsTo_Basis";
val LeadsTo_Trans = thm "LeadsTo_Trans";
val LeadsTo_Union = thm "LeadsTo_Union";
val leadsTo_imp_LeadsTo = thm "leadsTo_imp_LeadsTo";
val LeadsTo_Un_duplicate = thm "LeadsTo_Un_duplicate";
val LeadsTo_Un_duplicate2 = thm "LeadsTo_Un_duplicate2";
val LeadsTo_UN = thm "LeadsTo_UN";
val LeadsTo_Un = thm "LeadsTo_Un";
val single_LeadsTo_I = thm "single_LeadsTo_I";
val subset_imp_LeadsTo = thm "subset_imp_LeadsTo";
val empty_LeadsTo = thm "empty_LeadsTo";
val LeadsTo_state = thm "LeadsTo_state";
val LeadsTo_weaken_R = thm "LeadsTo_weaken_R";
val LeadsTo_weaken_L = thm "LeadsTo_weaken_L";
val LeadsTo_weaken = thm "LeadsTo_weaken";
val Always_LeadsTo_weaken = thm "Always_LeadsTo_weaken";
val LeadsTo_Un_post = thm "LeadsTo_Un_post";
val LeadsTo_Trans_Un = thm "LeadsTo_Trans_Un";
val LeadsTo_Un_distrib = thm "LeadsTo_Un_distrib";
val LeadsTo_UN_distrib = thm "LeadsTo_UN_distrib";
val LeadsTo_Union_distrib = thm "LeadsTo_Union_distrib";
val EnsuresI = thm "EnsuresI";
val Always_LeadsTo_Basis = thm "Always_LeadsTo_Basis";
val LeadsTo_Diff = thm "LeadsTo_Diff";
val LeadsTo_UN_UN = thm "LeadsTo_UN_UN";
val LeadsTo_Un_Un = thm "LeadsTo_Un_Un";
val LeadsTo_cancel2 = thm "LeadsTo_cancel2";
val Un_Diff = thm "Un_Diff";
val LeadsTo_cancel_Diff2 = thm "LeadsTo_cancel_Diff2";
val LeadsTo_cancel1 = thm "LeadsTo_cancel1";
val Diff_Un2 = thm "Diff_Un2";
val LeadsTo_cancel_Diff1 = thm "LeadsTo_cancel_Diff1";
val LeadsTo_empty = thm "LeadsTo_empty";
val PSP_Stable = thm "PSP_Stable";
val PSP_Stable2 = thm "PSP_Stable2";
val PSP = thm "PSP";
val PSP2 = thm "PSP2";
val PSP_Unless = thm "PSP_Unless";
val LeadsTo_wf_induct = thm "LeadsTo_wf_induct";
val LessThan_induct = thm "LessThan_induct";
val Completion = thm "Completion";
val Finite_completion = thm "Finite_completion";
val Stable_completion = thm "Stable_completion";
val Finite_stable_completion = thm "Finite_stable_completion";


(*proves "ensures/leadsTo" properties when the program is specified*)
fun gen_ensures_tac(cs,ss) sact = 
    SELECT_GOAL
      (EVERY [REPEAT (Always_Int_tac 1),
              etac Always_LeadsTo_Basis 1 
                  ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
                  REPEAT (ares_tac [LeadsTo_Basis, leadsTo_Basis,
                                    EnsuresI, ensuresI] 1),
              (*now there are two subgoals: co & transient*)
              simp_tac (ss addsimps !program_defs_ref) 2,
              res_inst_tac [("act", sact)] transientI 2,
                 (*simplify the command's domain*)
              simp_tac (ss addsimps [domain_def]) 3, 
              (* proving the domain part *)
             clarify_tac cs 3, dtac Cla.swap 3, force_tac (cs,ss) 4,
             rtac ReplaceI 3, force_tac (cs,ss) 3, force_tac (cs,ss) 4,
             asm_full_simp_tac ss 3, rtac conjI 3, simp_tac ss 4,
             REPEAT (rtac state_update_type 3),
             gen_constrains_tac (cs,ss) 1,
             ALLGOALS (clarify_tac cs),
             ALLGOALS (asm_full_simp_tac (ss addsimps [st_set_def])),
                        ALLGOALS (clarify_tac cs),
            ALLGOALS (asm_lr_simp_tac ss)]);

fun ensures_tac sact = gen_ensures_tac (claset(), simpset()) sact;
*}


method_setup ensures_tac = {*
    fn args => fn ctxt =>
        Method.goal_args' (Scan.lift Args.name) 
           (gen_ensures_tac (local_clasimpset_of ctxt))
           args ctxt *}
    "for proving progress properties"


end
