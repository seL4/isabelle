(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

set proof_timing;


(*** General lemmas ***)

Goal "UNIV Times UNIV = UNIV";
by Auto_tac;
qed "UNIV_Times_UNIV"; 
Addsimps [UNIV_Times_UNIV];

Goal "- (UNIV Times A) = UNIV Times (-A)";
by Auto_tac;
qed "Compl_Times_UNIV1"; 

Goal "- (A Times UNIV) = (-A) Times UNIV";
by Auto_tac;
qed "Compl_Times_UNIV2"; 

Addsimps [Compl_Times_UNIV1, Compl_Times_UNIV2]; 


(*** The abstract type of programs ***)

val rep_ss = simpset() addsimps 
                [Init_def, Acts_def, mk_program_def, Program_def, Rep_Program, 
		 Rep_Program_inverse, Abs_Program_inverse];


Goal "Id : Acts F";
by (cut_inst_tac [("x", "F")] Rep_Program 1);
by (auto_tac (claset(), rep_ss));
qed "Id_in_Acts";
AddIffs [Id_in_Acts];

Goal "insert Id (Acts F) = Acts F";
by (simp_tac (simpset() addsimps [insert_absorb, Id_in_Acts]) 1);
qed "insert_Id_Acts";
AddIffs [insert_Id_Acts];

(** Inspectors for type "program" **)

Goal "Init (mk_program (init,acts)) = init";
by (auto_tac (claset(), rep_ss));
qed "Init_eq";

Goal "Acts (mk_program (init,acts)) = insert Id acts";
by (auto_tac (claset(), rep_ss));
qed "Acts_eq";

Addsimps [Acts_eq, Init_eq];


(** The notation of equality for type "program" **)

Goal "[| Init F = Init G; Acts F = Acts G |] ==> F = G";
by (subgoals_tac ["EX x. Rep_Program F = x",
		  "EX x. Rep_Program G = x"] 1);
by (REPEAT (Blast_tac 2));
by (Clarify_tac 1);
by (auto_tac (claset(), rep_ss));
by (REPEAT (dres_inst_tac [("f", "Abs_Program")] arg_cong 1));
by (asm_full_simp_tac rep_ss 1);
qed "program_equalityI";

val [major,minor] =
Goal "[| F = G; [| Init F = Init G; Acts F = Acts G |] ==> P |] ==> P";
by (rtac minor 1);
by (auto_tac (claset(), simpset() addsimps [major]));
qed "program_equalityE";


(*** These rules allow "lazy" definition expansion 
     They avoid expanding the full program, which is a large expression
***)

Goal "F == mk_program (init,acts) ==> Init F = init";
by Auto_tac;
qed "def_prg_Init";

(*The program is not expanded, but its Init and Acts are*)
val [rew] = goal thy
    "[| F == mk_program (init,acts) |] \
\    ==> Init F = init & Acts F = insert Id acts";
by (rewtac rew);
by Auto_tac;
qed "def_prg_simps";

(*An action is expanded only if a pair of states is being tested against it*)
Goal "[| act == {(s,s'). P s s'} |] ==> ((s,s') : act) = P s s'";
by Auto_tac;
qed "def_act_simp";

fun simp_of_act def = def RS def_act_simp;

(*A set is expanded only if an element is being tested against it*)
Goal "A == B ==> (x : A) = (x : B)";
by Auto_tac;
qed "def_set_simp";

fun simp_of_set def = def RS def_set_simp;


(*** co ***)

(*These operators are not overloaded, but their operands are sets, and 
  ultimately there's a risk of reaching equality, which IS overloaded*)
overload_1st_set "UNITY.constrains";
overload_1st_set "UNITY.stable";
overload_1st_set "UNITY.unless";

val prems = Goalw [constrains_def]
    "(!!act s s'. [| act: Acts F;  (s,s') : act;  s: A |] ==> s': A') \
\    ==> F : A co A'";
by (blast_tac (claset() addIs prems) 1);
qed "constrainsI";

Goalw [constrains_def]
    "[| F : A co A'; act: Acts F;  (s,s'): act;  s: A |] ==> s': A'";
by (Blast_tac 1);
qed "constrainsD";

Goalw [constrains_def] "F : {} co B";
by (Blast_tac 1);
qed "constrains_empty";

Goalw [constrains_def] "F : A co UNIV";
by (Blast_tac 1);
qed "constrains_UNIV";
AddIffs [constrains_empty, constrains_UNIV];

(*monotonic in 2nd argument*)
Goalw [constrains_def]
    "[| F : A co A'; A'<=B' |] ==> F : A co B'";
by (Blast_tac 1);
qed "constrains_weaken_R";

(*anti-monotonic in 1st argument*)
Goalw [constrains_def]
    "[| F : A co A'; B<=A |] ==> F : B co A'";
by (Blast_tac 1);
qed "constrains_weaken_L";

Goalw [constrains_def]
   "[| F : A co A'; B<=A; A'<=B' |] ==> F : B co B'";
by (Blast_tac 1);
qed "constrains_weaken";

(** Union **)

Goalw [constrains_def]
    "[| F : A co A'; F : B co B' |] ==> F : (A Un B) co (A' Un B')";
by (Blast_tac 1);
qed "constrains_Un";

Goalw [constrains_def]
    "ALL i:I. F : (A i) co (A' i) ==> F : (UN i:I. A i) co (UN i:I. A' i)";
by (Blast_tac 1);
qed "ball_constrains_UN";

(** Intersection **)

Goalw [constrains_def]
    "[| F : A co A'; F : B co B' |] ==> F : (A Int B) co (A' Int B')";
by (Blast_tac 1);
qed "constrains_Int";

Goalw [constrains_def]
    "ALL i:I. F : (A i) co (A' i) ==> F : (INT i:I. A i) co (INT i:I. A' i)";
by (Blast_tac 1);
qed "ball_constrains_INT";

Goalw [constrains_def] "F : A co A' ==> A <= A'";
by Auto_tac;
qed "constrains_imp_subset";

(*The reasoning is by subsets since "co" refers to single actions
  only.  So this rule isn't that useful.*)
Goalw [constrains_def]
    "[| F : A co B; F : B co C |] ==> F : A co C";
by (Blast_tac 1);
qed "constrains_trans";

Goalw [constrains_def]
   "[| F : A co (A' Un B); F : B co B' |] ==> F : A co (A' Un B')";
by (Clarify_tac 1);
by (Blast_tac 1);
qed "constrains_cancel";


(*** unless ***)

Goalw [unless_def] "F : (A-B) co (A Un B) ==> F : A unless B";
by (assume_tac 1);
qed "unlessI";

Goalw [unless_def] "F : A unless B ==> F : (A-B) co (A Un B)";
by (assume_tac 1);
qed "unlessD";


(*** stable ***)

Goalw [stable_def] "F : A co A ==> F : stable A";
by (assume_tac 1);
qed "stableI";

Goalw [stable_def] "F : stable A ==> F : A co A";
by (assume_tac 1);
qed "stableD";

Goalw [stable_def, constrains_def] "stable UNIV = UNIV";
by Auto_tac;
qed "stable_UNIV";
Addsimps [stable_UNIV];

(** Union **)

Goalw [stable_def]
    "[| F : stable A; F : stable A' |] ==> F : stable (A Un A')";
by (blast_tac (claset() addIs [constrains_Un]) 1);
qed "stable_Un";

Goalw [stable_def]
    "ALL i:I. F : stable (A i) ==> F : stable (UN i:I. A i)";
by (blast_tac (claset() addIs [ball_constrains_UN]) 1);
qed "ball_stable_UN";

(** Intersection **)

Goalw [stable_def]
    "[| F : stable A; F : stable A' |] ==> F : stable (A Int A')";
by (blast_tac (claset() addIs [constrains_Int]) 1);
qed "stable_Int";

Goalw [stable_def]
    "ALL i:I. F : stable (A i) ==> F : stable (INT i:I. A i)";
by (blast_tac (claset() addIs [ball_constrains_INT]) 1);
qed "ball_stable_INT";

Goalw [stable_def, constrains_def]
    "[| F : stable C; F : A co (C Un A') |] ==> F : (C Un A) co (C Un A')";
by (Blast_tac 1);
qed "stable_constrains_Un";

Goalw [stable_def, constrains_def]
  "[| F : stable C; F :  (C Int A) co  A' |] ==> F : (C Int A) co (C Int A')";
by (Blast_tac 1);
qed "stable_constrains_Int";

(*[| F : stable C; F :  co (C Int A) A |] ==> F : stable (C Int A)*)
bind_thm ("stable_constrains_stable", stable_constrains_Int RS stableI);


(*** invariant ***)

Goal "[| Init F<=A;  F: stable A |] ==> F : invariant A";
by (asm_simp_tac (simpset() addsimps [invariant_def]) 1);
qed "invariantI";

(*Could also say "invariant A Int invariant B <= invariant (A Int B)"*)
Goal "[| F : invariant A;  F : invariant B |] ==> F : invariant (A Int B)";
by (auto_tac (claset(), simpset() addsimps [invariant_def, stable_Int]));
qed "invariant_Int";


(*** increasing ***)

Goalw [increasing_def, stable_def, constrains_def]
     "mono g ==> increasing f <= increasing (g o f)";
by Auto_tac;
by (blast_tac (claset() addIs [monoD, order_trans]) 1);
qed "mono_increasing_o";

Goalw [increasing_def]
     "increasing f <= {F. ALL z::nat. F: stable {s. z < f s}}";
by (simp_tac (simpset() addsimps [Suc_le_eq RS sym]) 1);
by (Blast_tac 1);
qed "increasing_stable_less";


(** The Elimination Theorem.  The "free" m has become universally quantified!
    Should the premise be !!m instead of ALL m ?  Would make it harder to use
    in forward proof. **)

Goalw [constrains_def]
    "[| ALL m:M. F : {s. s x = m} co (B m) |] \
\    ==> F : {s. s x : M} co (UN m:M. B m)";
by (Blast_tac 1);
qed "elimination";

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
Goalw [constrains_def]
    "(ALL m:M. F : {m} co (B m)) ==> F : M co (UN m:M. B m)";
by (Blast_tac 1);
qed "elimination_sing";



(*** Theoretical Results from Section 6 ***)

Goalw [constrains_def, strongest_rhs_def]
    "F : A co (strongest_rhs F A )";
by (Blast_tac 1);
qed "constrains_strongest_rhs";

Goalw [constrains_def, strongest_rhs_def]
    "F : A co B ==> strongest_rhs F A <= B";
by (Blast_tac 1);
qed "strongest_rhs_is_strongest";
