(*  Title:      ZF/UNITY/Comp.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   1998  University of Cambridge
Composition
From Chandy and Sanders, "Reasoning About Program Composition"

Revised by Sidi Ehmety on January 2001

*)

(*** component and strict_component relations ***)

Goalw [component_def]
     "H component F | H component G ==> H component (F Join G)";
by Auto_tac;
by (res_inst_tac [("x", "Ga Join G")] exI 1);
by (res_inst_tac [("x", "G Join F")] exI 2);
by (auto_tac (claset(), simpset() addsimps Join_ac));
qed "componentI";

Goalw [component_def]
     "G:program ==> (F component G) <-> \
\  (Init(G) <= Init(F) & Acts(F) <= Acts(G) & AllowedActs(G) <= AllowedActs(F))";
by Auto_tac;
by (rtac exI 1);
by (rtac program_equalityI 1);
by Auto_tac;
qed "component_eq_subset";

Goalw [component_def] 
   "F:program ==> SKIP component F";
by (res_inst_tac [("x", "F")] exI 1);
by (force_tac (claset() addIs [Join_SKIP_left], simpset()) 1);
qed "component_SKIP";

Goalw [component_def] 
"F:program ==> F component F";
by (res_inst_tac  [("x", "F")] exI 1);
by (force_tac (claset() addIs [Join_SKIP_right], simpset()) 1);
qed "component_refl";

Addsimps [component_SKIP, component_refl];

Goal "F component SKIP ==> programify(F) = SKIP";
by (rtac program_equalityI 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [component_eq_subset])));
by (Blast_tac 1);
qed "SKIP_minimal";

Goalw [component_def] "F component (F Join G)";
by (Blast_tac 1);
qed "component_Join1";

Goalw [component_def] "G component (F Join G)";
by (simp_tac (simpset() addsimps [Join_commute]) 1);
by (Blast_tac 1);
qed "component_Join2";

Goal "F component G ==> F Join G = G";
by (auto_tac (claset(), simpset() 
        addsimps [component_def, Join_left_absorb]));
qed "Join_absorb1";

Goal "G component F ==> F Join G = F";
by (auto_tac (claset(), simpset() addsimps Join_ac@[component_def]));
qed "Join_absorb2";

Goal "H:program==>(JOIN(I,F) component H) <-> (ALL i:I. F(i) component H)";
by (case_tac "I=0" 1);
by (Force_tac 1);
by (asm_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by Auto_tac;
by (dres_inst_tac [("c", "xb"), ("A", "AllowedActs(H)")] subsetD 2);
by (REPEAT(blast_tac (claset() addSEs [not_emptyE]) 1));
qed "JN_component_iff";

Goalw [component_def] "i:I ==> F(i) component (JN i:I. (F(i)))";
by (blast_tac (claset() addIs [JN_absorb]) 1);
qed "component_JN";

Goalw [component_def] "[| F component G; G component H |] ==> F component H";
by (blast_tac (claset() addIs [Join_assoc RS sym]) 1);
qed "component_trans";

Goal "[| F:program; G:program |] ==>(F component G & G  component F) --> F = G";
by (asm_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by (Clarify_tac 1);
by (rtac program_equalityI 1);
by Auto_tac;
qed "component_antisym";

Goal "H:program ==> ((F Join G) component H) <-> (F component H & G component H)";
by (asm_simp_tac (simpset() addsimps [component_eq_subset]) 1);
by (Blast_tac 1);
qed "Join_component_iff";

Goal "[| F component G; G:A co B; F:program |] ==> F : A co B";
by (ftac constrainsD2 1);
by (rotate_tac ~1 1);
by (auto_tac (claset(), 
              simpset() addsimps [constrains_def, component_eq_subset]));
qed "component_constrains";

(* Used in Guar.thy to show that programs are partially ordered*)
(* bind_thm ("program_less_le", strict_component_def RS meta_eq_to_obj_eq);*)

(*** preserves ***)

val prems = Goalw [preserves_def] 
"ALL z. F:stable({s:state. f(s) = z})  ==> F:preserves(f)";
by Auto_tac;
by (blast_tac (claset() addDs [stableD2]) 1);
qed "preserves_aux";
bind_thm("preservesI", allI RS preserves_aux);

Goalw [preserves_def, stable_def, constrains_def]
     "[| F:preserves(f);  act : Acts(F);  <s,t> : act |] ==> f(s) = f(t)";
by (subgoal_tac "s:state & t:state" 1);
by (blast_tac (claset() addSDs [Acts_type RS subsetD]) 2);
by Auto_tac;
by (dres_inst_tac [("x", "f(s)")] spec 1);
by (dres_inst_tac [("x", "act")] bspec 1);
by Auto_tac;
qed "preserves_imp_eq";

Goalw [preserves_def]
"(F Join G : preserves(v)) <->  \
\     (programify(F) : preserves(v) & programify(G) : preserves(v))";
by (auto_tac (claset(), simpset() addsimps [INT_iff]));
qed "Join_preserves";
 
Goal "(JOIN(I,F): preserves(v)) <-> (ALL i:I. programify(F(i)):preserves(v))";
by (auto_tac (claset(), simpset() addsimps [JN_stable, preserves_def, INT_iff]));
qed "JN_preserves";

Goal "SKIP : preserves(v)";
by (auto_tac (claset(), simpset() addsimps [preserves_def, INT_iff]));
qed "SKIP_preserves";

AddIffs [Join_preserves, JN_preserves, SKIP_preserves];

(** Added by Sidi **)
(** component_of **)

(*  component_of is stronger than component *)
Goalw [component_def, component_of_def]
"F component_of H ==> F component H";
by (Blast_tac 1);
qed "component_of_imp_component";

(* component_of satisfies many of component's properties *)
Goalw [component_of_def]
"F:program ==> F component_of F";
by (res_inst_tac [("x", "SKIP")] exI 1);
by Auto_tac;
qed "component_of_refl";

Goalw [component_of_def]
"F:program ==>SKIP component_of F";
by Auto_tac;
by (res_inst_tac [("x", "F")] exI 1);
by Auto_tac;
qed "component_of_SKIP";
Addsimps [component_of_refl, component_of_SKIP];

Goalw [component_of_def]
"[| F component_of G; G component_of H |] ==> F component_of H";
by (blast_tac (claset() addIs [Join_assoc RS sym]) 1);
qed "component_of_trans";

(** localize **)
Goalw [localize_def]
 "Init(localize(v,F)) = Init(F)";
by (Simp_tac 1);
qed "localize_Init_eq";

Goalw [localize_def]
 "Acts(localize(v,F)) = Acts(F)";
by (Simp_tac 1);
qed "localize_Acts_eq";

Goalw [localize_def]
 "AllowedActs(localize(v,F)) = AllowedActs(F) Int (UN G:preserves(v). Acts(G))";
by (rtac equalityI 1);
by (auto_tac (claset() addDs [Acts_type RS subsetD], simpset()));
qed "localize_AllowedActs_eq";

AddIffs [localize_Init_eq, localize_Acts_eq, localize_AllowedActs_eq];

