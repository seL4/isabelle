(*  Title:      HOL/UNITY/PPROD.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

val rinst = read_instantiate_sg (sign_of thy);

(*** General lemmas ***)

Goal "x:C ==> (A Times C <= B Times C) = (A <= B)";
by (Blast_tac 1);
qed "Times_subset_cancel2";

Goal "x:C ==> (A Times C = B Times C) = (A = B)";
by (blast_tac (claset() addEs [equalityE]) 1);
qed "Times_eq_cancel2";

Goal "Union(B) Times A = (UN C:B. C Times A)";
by (Blast_tac 1);
qed "Times_Union2";

Goal "Domain (Union S) = (UN A:S. Domain A)";
by (Blast_tac 1);
qed "Domain_Union";

(** RTimes: the product of two relations **)

Goal "(((a,b), (a',b')) : A RTimes B) = ((a,a'):A & (b,b'):B)";
by (simp_tac (simpset() addsimps [RTimes_def]) 1);
qed "mem_RTimes_iff";
AddIffs [mem_RTimes_iff]; 

Goalw [RTimes_def] "[| A<=C;  B<=D |] ==> A RTimes B <= C RTimes D";
by Auto_tac;
qed "RTimes_mono";

Goal "{} RTimes B = {}";
by Auto_tac;
qed "RTimes_empty1"; 

Goal "A RTimes {} = {}";
by Auto_tac;
qed "RTimes_empty2"; 

Goal "Id RTimes Id = Id";
by Auto_tac;
qed "RTimes_Id"; 

Addsimps [RTimes_empty1, RTimes_empty2, RTimes_Id]; 

Goal "Domain (r RTimes s) = Domain r Times Domain s";
by (auto_tac (claset(), simpset() addsimps [Domain_iff]));
qed "Domain_RTimes"; 

Goal "Range (r RTimes s) = Range r Times Range s";
by (auto_tac (claset(), simpset() addsimps [Range_iff]));
qed "Range_RTimes"; 

Goal "(r RTimes s) ^^ (A Times B) = r^^A Times s^^B";
by (auto_tac (claset(), simpset() addsimps [Image_iff]));
qed "Image_RTimes"; 


Goal "- (UNIV Times A) = UNIV Times (-A)";
by Auto_tac;
qed "Compl_Times_UNIV1"; 

Goal "- (A Times UNIV) = (-A) Times UNIV";
by Auto_tac;
qed "Compl_Times_UNIV2"; 

Addsimps [Compl_Times_UNIV1, Compl_Times_UNIV2]; 


(**** Lcopy ****)

(*** Basic properties ***)

Goal "Init (Lcopy F) = Init F Times UNIV";
by (simp_tac (simpset() addsimps [Lcopy_def]) 1);
qed "Init_Lcopy";

Goal "Id : (%act. act RTimes Id) `` Acts F";
by (rtac image_eqI 1);
by (rtac Id_in_Acts 2);
by Auto_tac;
val lemma = result();

Goal "Acts (Lcopy F) = (%act. act RTimes Id) `` Acts F";
by (auto_tac (claset() addSIs [lemma], 
	      simpset() addsimps [Lcopy_def]));
qed "Acts_Lcopy";

Addsimps [Init_Lcopy];

Goalw [Lcopy_def, SKIP_def] "Lcopy SKIP = SKIP";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Lcopy_SKIP";

Addsimps [Lcopy_SKIP];


(*** Safety: constrains, stable ***)

(** In most cases, C = UNIV.  The generalization isn't of obvious value. **)

Goal "x: C ==> \
\     (Lcopy F : constrains (A Times C) (B Times C)) = (F : constrains A B)";
by (auto_tac (claset(), simpset() addsimps [constrains_def, Lcopy_def]));
by (Blast_tac 1);
qed "Lcopy_constrains";

Goal "Lcopy F : constrains A B ==> F : constrains (Domain A) (Domain B)";
by (auto_tac (claset(), simpset() addsimps [constrains_def, Lcopy_def]));
by (Blast_tac 1);
qed "Lcopy_constrains_Domain";

Goal "x: C ==> (Lcopy F : stable (A Times C)) = (F : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, Lcopy_constrains]) 1);
qed "Lcopy_stable";

Goal "(Lcopy F : invariant (A Times UNIV)) = (F : invariant A)";
by (asm_simp_tac (simpset() addsimps [Times_subset_cancel2,
				      invariant_def, Lcopy_stable]) 1);
qed "Lcopy_invariant";

(** Substitution Axiom versions: Constrains, Stable **)

Goal "p : reachable (Lcopy F) ==> fst p : reachable F";
by (etac reachable.induct 1);
by (auto_tac
    (claset() addIs reachable.intrs,
     simpset() addsimps [Acts_Lcopy]));
qed "reachable_Lcopy_fst";

Goal "(a,b) : reachable (Lcopy F) ==> a : reachable F";
by (force_tac (claset() addSDs [reachable_Lcopy_fst], simpset()) 1);
qed "reachable_LcopyD";

Goal "reachable (Lcopy F) = reachable F Times UNIV";
by (rtac equalityI 1);
by (force_tac (claset() addSDs [reachable_LcopyD], simpset()) 1);
by (Clarify_tac 1);
by (etac reachable.induct 1);
by (ALLGOALS (force_tac (claset() addIs reachable.intrs, 
			 simpset() addsimps [Acts_Lcopy])));
qed "reachable_Lcopy_eq";

Goal "(Lcopy F : Constrains (A Times UNIV) (B Times UNIV)) =  \
\     (F : Constrains A B)";
by (simp_tac
    (simpset() addsimps [Constrains_def, reachable_Lcopy_eq, 
			 Lcopy_constrains, Sigma_Int_distrib1 RS sym]) 1);
qed "Lcopy_Constrains";

Goal "(Lcopy F : Stable (A Times UNIV)) = (F : Stable A)";
by (simp_tac (simpset() addsimps [Stable_def, Lcopy_Constrains]) 1);
qed "Lcopy_Stable";


(*** Progress: transient, ensures ***)

Goal "(Lcopy F : transient (A Times UNIV)) = (F : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [transient_def, Times_subset_cancel2, 
				  Domain_RTimes, Image_RTimes, Lcopy_def]));
qed "Lcopy_transient";

Goal "(Lcopy F : ensures (A Times UNIV) (B Times UNIV)) = \
\     (F : ensures A B)";
by (simp_tac
    (simpset() addsimps [ensures_def, Lcopy_constrains, Lcopy_transient, 
			 Sigma_Un_distrib1 RS sym, 
			 Sigma_Diff_distrib1 RS sym]) 1);
qed "Lcopy_ensures";

Goal "F : leadsTo A B ==> Lcopy F : leadsTo (A Times UNIV) (B Times UNIV)";
by (etac leadsTo_induct 1);
by (asm_simp_tac (simpset() addsimps [leadsTo_UN, Times_Union2]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (asm_simp_tac (simpset() addsimps [leadsTo_Basis, Lcopy_ensures]) 1);
qed "leadsTo_imp_Lcopy_leadsTo";

Goal "Lcopy F : ensures A B ==> F : ensures (Domain A) (Domain B)";
by (full_simp_tac
    (simpset() addsimps [ensures_def, Lcopy_constrains, Lcopy_transient, 
			 Domain_Un_eq RS sym,
			 Sigma_Un_distrib1 RS sym, 
			 Sigma_Diff_distrib1 RS sym]) 1);
by (safe_tac (claset() addSDs [Lcopy_constrains_Domain]));
by (etac constrains_weaken_L 1);
by (Blast_tac 1);
(*NOT able to prove this:
Lcopy F : ensures A B ==> F : ensures (Domain A) (Domain B)
 1. [| Lcopy F : transient (A - B);
       F : constrains (Domain (A - B)) (Domain (A Un B)) |]
    ==> F : transient (Domain A - Domain B)
**)


Goal "Lcopy F : leadsTo AU BU ==> F : leadsTo (Domain AU) (Domain BU)";
by (etac leadsTo_induct 1);
by (full_simp_tac (simpset() addsimps [Domain_Union]) 3);
by (blast_tac (claset() addIs [leadsTo_UN]) 3);
by (blast_tac (claset() addIs [leadsTo_Trans]) 2);
by (rtac leadsTo_Basis 1);
(*...and so CANNOT PROVE THIS*)


(*This also seems impossible to prove??*)
Goal "(Lcopy F : leadsTo (A Times UNIV) (B Times UNIV)) = \
\     (F : leadsTo A B)";



(**** PPROD ****)

(*** Basic properties ***)

Goalw [PPROD_def, lift_prog_def]
     "Init (PPROD I F) = {f. ALL i:I. f i : Init F}";
by Auto_tac;
qed "Init_PPROD";

Goalw [lift_act_def] "lift_act i Id = Id";
by Auto_tac;
qed "lift_act_Id";
Addsimps [lift_act_Id];

Goalw [lift_act_def]
    "((f,f') : lift_act i act) = (EX s'. f' = f(i := s') & (f i, s') : act)";
by (Blast_tac 1);
qed "lift_act_eq";
AddIffs [lift_act_eq];

Goal "Acts (PPROD I F) = insert Id (UN i:I. lift_act i `` Acts F)";
by (auto_tac (claset(),
	      simpset() addsimps [PPROD_def, lift_prog_def, Acts_JN]));
qed "Acts_PPROD";

Addsimps [Init_PPROD];

Goal "PPROD I SKIP = SKIP";
by (rtac program_equalityI 1);
by (auto_tac (claset(),
	      simpset() addsimps [PPROD_def, lift_prog_def, 
				  SKIP_def, Acts_JN]));
qed "PPROD_SKIP";

Goal "PPROD {} F = SKIP";
by (simp_tac (simpset() addsimps [PPROD_def]) 1);
qed "PPROD_empty";

Addsimps [PPROD_SKIP, PPROD_empty];

Goalw [PPROD_def]  "PPROD (insert i I) F = (lift_prog i F) Join (PPROD I F)";
by Auto_tac;
qed "PPROD_insert";


(*** Safety: constrains, stable ***)

val subsetCE' = rinst
            [("c", "(%u. ?s)(i:=?s')")] subsetCE;

Goal "i : I ==>  \
\     (PPROD I F : constrains {f. f i : A} {f. f i : B})  =  \
\     (F : constrains A B)";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, lift_prog_def, PPROD_def,
				  Acts_JN]));
by (REPEAT (Blast_tac 2));
by (force_tac (claset() addSEs [subsetCE', allE, ballE], simpset()) 1);
qed "PPROD_constrains";

Goal "[| PPROD I F : constrains AA BB;  i: I |] \
\     ==> F : constrains (Applyall AA i) (Applyall BB i)";
by (auto_tac (claset(), 
	      simpset() addsimps [Applyall_def, constrains_def, 
				  lift_prog_def, PPROD_def, Acts_JN]));
by (force_tac (claset() addSIs [rinst [("x", "?ff(i := ?u)")] image_eqI]
			addSEs [rinst [("c", "?ff(i := ?u)")] subsetCE, ballE],
	       simpset()) 1);
qed "PPROD_constrains_projection";


Goal "i : I ==> (PPROD I F : stable {f. f i : A}) = (F : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, PPROD_constrains]) 1);
qed "PPROD_stable";

Goal "i : I ==> (PPROD I F : invariant {f. f i : A}) = (F : invariant A)";
by (auto_tac (claset(),
	      simpset() addsimps [invariant_def, PPROD_stable]));
qed "PPROD_invariant";


(** Substitution Axiom versions: Constrains, Stable **)

Goal "[| f : reachable (PPROD I F);  i : I |] ==> f i : reachable F";
by (etac reachable.induct 1);
by (auto_tac
    (claset() addIs reachable.intrs,
     simpset() addsimps [Acts_PPROD]));
qed "reachable_PPROD";

Goal "reachable (PPROD I F) <= {f. ALL i:I. f i : reachable F}";
by (force_tac (claset() addSDs [reachable_PPROD], simpset()) 1);
qed "reachable_PPROD_subset1";

Goal "[| i ~: I;  A : reachable F |]     \
\  ==> ALL f. f : reachable (PPROD I F)  \
\             --> f(i:=A) : reachable (lift_prog i F Join PPROD I F)";
by (etac reachable.induct 1);
by (ALLGOALS Clarify_tac);
by (etac reachable.induct 1);
(*Init, Init case*)
by (force_tac (claset() addIs reachable.intrs,
	       simpset() addsimps [lift_prog_def]) 1);
(*Init of F, action of PPROD F case*)
br reachable.Acts 1;
by (force_tac (claset(), simpset() addsimps [Acts_Join]) 1);
ba 1;
by (force_tac (claset() addIs [ext], simpset() addsimps [Acts_PPROD]) 1);
(*induction over the 2nd "reachable" assumption*)
by (eres_inst_tac [("xa","f")] reachable.induct 1);
(*Init of PPROD F, action of F case*)
by (res_inst_tac [("act","lift_act i act")] reachable.Acts 1);
by (force_tac (claset(), simpset() addsimps [lift_prog_def, Acts_Join]) 1);
by (force_tac (claset() addIs [reachable.Init], simpset()) 1);
by (force_tac (claset() addIs [ext], simpset() addsimps [lift_act_def]) 1);
(*last case: an action of PPROD I F*)
br reachable.Acts 1;
by (force_tac (claset(), simpset() addsimps [Acts_Join]) 1);
ba 1;
by (force_tac (claset() addIs [ext], simpset() addsimps [Acts_PPROD]) 1);
qed_spec_mp "reachable_lift_Join_PPROD";


(*The index set must be finite: otherwise infinitely many copies of F can
  perform actions, and PPROD can never catch up in finite time.*)
Goal "finite I ==> {f. ALL i:I. f i : reachable F} <= reachable (PPROD I F)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (force_tac (claset() addDs [reachable_lift_Join_PPROD], 
	       simpset() addsimps [PPROD_insert]) 1);
qed "reachable_PPROD_subset2";

Goal "finite I ==> reachable (PPROD I F) = {f. ALL i:I. f i : reachable F}";
by (REPEAT_FIRST (ares_tac [equalityI,
			    reachable_PPROD_subset1, 
			    reachable_PPROD_subset2]));
qed "reachable_PPROD_eq";


Goal "i: I ==> Applyall {f. (ALL i:I. f i : R) & f i : A} i = R Int A";
by (force_tac (claset(), simpset() addsimps [Applyall_def]) 1);
qed "Applyall_Int";


Goal "[| i: I;  finite I |]  \
\     ==> (PPROD I F : Constrains {f. f i : A} {f. f i : B}) =  \
\         (F : Constrains A B)";
by (auto_tac
    (claset(),
     simpset() addsimps [Constrains_def, Collect_conj_eq RS sym,
			 reachable_PPROD_eq]));
bd PPROD_constrains_projection 1;
ba 1;
by (asm_full_simp_tac (simpset() addsimps [Applyall_Int]) 1);
by (auto_tac (claset(), 
              simpset() addsimps [constrains_def, lift_prog_def, PPROD_def,
                                  Acts_JN]));
by (REPEAT (blast_tac (claset() addIs reachable.intrs) 1));
qed "PPROD_Constrains";


Goal "[| i: I;  finite I |]  \
\     ==> (PPROD I F : Stable {f. f i : A}) = (F : Stable A)";
by (asm_simp_tac (simpset() addsimps [Stable_def, PPROD_Constrains]) 1);
qed "PPROD_Stable";



