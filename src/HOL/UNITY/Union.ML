(*  Title:      HOL/UNITY/Union.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs
*)

Goal "k:I ==> (INT i:I. A i) Int A k = (INT i:I. A i)";
by (Blast_tac 1);
qed "INT_absorb2";


val rinst = read_instantiate_sg (sign_of thy);

Addcongs [UN_cong, INT_cong];

(** SKIP **)

Goal "States (SKIP A) = A";
by (simp_tac (simpset() addsimps [SKIP_def]) 1);
qed "States_SKIP";

Goal "Init (SKIP A) = A";
by (simp_tac (simpset() addsimps [SKIP_def]) 1);
qed "Init_SKIP";

Goal "Acts (SKIP A) = {diag A}";
by (simp_tac (simpset() addsimps [SKIP_def]) 1);
qed "Acts_SKIP";

Addsimps [States_SKIP, Init_SKIP, Acts_SKIP];

Goal "reachable (SKIP A) = A";
by (force_tac (claset() addEs [reachable.induct]
			addIs reachable.intrs, simpset()) 1);
qed "reachable_SKIP";

Addsimps [reachable_SKIP];


(** Join **)

Goal "States (F Join G) = States F Int States G";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "States_Join";

Goal "Init (F Join G) = Init F Int Init G";
by (auto_tac (claset() addIs [impOfSubs Init_subset_States],
	      simpset() addsimps [Join_def]));
qed "Init_Join";

Goal "States F = States G ==> Acts (F Join G) = Acts F Un Acts G";
by (subgoal_tac "Acts F Un Acts G <= Pow (States G Times States G)" 1);
by (blast_tac (claset() addEs [equalityE] 
                        addDs [impOfSubs Acts_subset_Pow_States]) 2);
by (auto_tac (claset(), simpset() addsimps [Join_def]));
qed "Acts_Join";


(** JN **)

Goalw [JOIN_def, SKIP_def] "(JN i:{}. F i) = SKIP UNIV";
by Auto_tac;
qed "JN_empty";
Addsimps [JN_empty];

Goal "States (JN i:I. F i) = (INT i:I. States (F i))";
by (simp_tac (simpset() addsimps [JOIN_def]) 1);
qed "States_JN";

Goal "Init (JN i:I. F i) = (INT i:I. Init (F i))";
by (auto_tac (claset() addIs [impOfSubs Init_subset_States],
	      simpset() addsimps [JOIN_def]));
qed "Init_JN";

(*If I={} then the LHS is (SKIP UNIV) while the RHS is {}.*)
Goalw [eqStates_def]
     "[| eqStates I F; i: I |] ==> Acts (JN i:I. F i) = (UN i:I. Acts (F i))";
by (Clarify_tac 1);
by (subgoal_tac "(UN i:I. Acts (F i)) <= Pow (St Times St)" 1);
by (blast_tac (claset() addEs [equalityE] 
                        addDs [impOfSubs Acts_subset_Pow_States]) 2);
by (auto_tac (claset(), simpset() addsimps [JOIN_def]));
qed "Acts_JN";

Goal "eqStates I F \
\     ==> Acts (JN i:I. F i) = \
\         (if I={} then {diag UNIV} else (UN i:I. Acts (F i)))";
by (force_tac (claset(), simpset() addsimps [Acts_JN]) 1);
qed "Acts_JN_if";

Addsimps [States_Join, Init_Join, States_JN, Init_JN];


Goal "(JN x:insert j I. F x) = (F j) Join (JN x:I. F x)";
by (rtac program_equalityI 1);
by (ALLGOALS Asm_simp_tac);
by (asm_simp_tac 
    (simpset() addsimps [JOIN_def, Join_def, Acts_eq_raw,
			 image_UNION, image_Un, image_image, Int_assoc]) 1);
qed "JN_insert";
Addsimps[JN_insert];

Goal "k:I ==> A k Join (JN i:I. A i) = (JN i:I. A i)";
by (stac (JN_insert RS sym) 1);
by (asm_simp_tac (simpset() addsimps [insert_absorb]) 1);
qed "JN_absorb";


Goalw [eqStates_def] "eqStates {} F";
by (Simp_tac 1);
qed "eqStates_empty";

Goalw [eqStates_def]
    "[| eqStates I F; States (F i) = (INT i: I. States (F i)) |] \
\    ==> eqStates (insert i I) F";
by Auto_tac;
qed "eqStates_insertI";

Goalw [eqStates_def]
    "eqStates (insert i I) F = \
\    (eqStates I F & (I={} | States (F i) = (INT i: I. States (F i))))";
by Auto_tac;
qed "eqStates_insert_eq";

Addsimps [eqStates_empty, eqStates_insert_eq];


(** Algebraic laws **)

Goal "F Join G = G Join F";
by (simp_tac (simpset() addsimps [Join_def, Un_commute, Int_commute]) 1);
qed "Join_commute";

Goal "(F Join G) Join H = F Join (G Join H)";
by (rtac program_equalityI 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps Un_ac@[Int_assoc])));
by (asm_simp_tac 
    (simpset() addsimps Un_ac@Int_ac@[Join_def, Acts_eq_raw,
				      image_Un, image_image]) 1);
by (Blast_tac 1);
qed "Join_assoc";
 
Goalw [Join_def, SKIP_def] "States F <= A ==> (SKIP A) Join F = F";
by (rtac program_equalityI 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps 
		   Int_ac@[Acts_subset_Pow_States RS restrict_rel_image, 
			   Acts_eq_raw, insert_absorb, Int_absorb1])));
by (blast_tac (claset() addIs [impOfSubs Init_subset_States]) 1);
qed "Join_SKIP_left";

Goal "States F <= A ==> F Join (SKIP A) = F";
by (stac Join_commute 1);
by (asm_simp_tac (simpset() addsimps [Join_SKIP_left]) 1);
qed "Join_SKIP_right";

Addsimps [Join_SKIP_left, Join_SKIP_right];

Goalw [Join_def] "F Join F = F";
by (rtac program_equalityI 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps 
		   [insert_absorb, Acts_subset_Pow_States RS Acts_eq])));
by (blast_tac (claset() addIs [impOfSubs Init_subset_States]) 1);
qed "Join_absorb";

Addsimps [Join_absorb];

Goal "(JN i: I Un J. A i) = ((JN i: I. A i) Join (JN i:J. A i))";
by (rtac program_equalityI 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [INT_Un])));
by (asm_simp_tac 
    (simpset() addsimps Int_ac@
                        [JOIN_def, Join_def, Acts_eq_raw, UN_Un, INT_Un, 
			 image_UNION, image_Un, image_image]) 1);
qed "JN_Join";

Goal "i: I ==> (JN i:I. c) = c";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [Acts_JN, eqStates_def]));
qed "JN_constant";

Goal "(JN i:I. A i Join B i) = (JN i:I. A i)  Join  (JN i:I. B i)";
by (rtac program_equalityI 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [INT_Int_distrib])));
by (asm_simp_tac 
    (simpset() addsimps [JOIN_def, Join_def, Acts_eq_raw, image_UNION, 
			 rinst [("A","%x. States (A x) Int States (B x)")] 
			     INT_absorb2, 
			 image_Un, image_image]) 1);
by (asm_simp_tac (simpset() addsimps [INT_Int_distrib RS sym] @ Int_ac) 1);
by (Blast_tac 1);
qed "JN_Join_distrib";

Goal "i : I ==> (JN i:I. A i Join B) = ((JN i:I. A i) Join B)";
by (asm_simp_tac (simpset() addsimps [JN_Join_distrib, JN_constant]) 1);
qed "JN_Join_miniscope";


(*** Safety: constrains, stable, FP ***)

Goal "[| F : constrains A B;  G : constrains A B |] \
\     ==> F Join G : constrains A B";
by (auto_tac (claset(),
	      simpset() addsimps [constrains_def, Join_def, Acts_eq_raw, 
				  image_Un]));
by (REPEAT (force_tac (claset() addSEs [ballE], simpset()) 1));
qed "constrains_imp_Join_constrains";

Goal "States F = States G ==> \
\     F Join G : constrains A B = (F : constrains A B & G : constrains A B)";
by (auto_tac (claset(), simpset() addsimps [constrains_def, Acts_Join]));
qed "constrains_Join";

Goal "[| i : I;  ALL i:I. F i : constrains A B |] \
\     ==> (JN i:I. F i) : constrains A B";
by (full_simp_tac (simpset() addsimps [constrains_def, JOIN_def, Acts_eq_raw, 
				  image_Un]) 1);
by Safe_tac;
by (REPEAT (force_tac (claset() addSEs [ballE], simpset()) 1));
qed "constrains_imp_JN_constrains";

Goal "[| i : I;  eqStates I F |] \
\     ==> (JN i:I. F i) : constrains A B = (ALL i:I. F i : constrains A B)";
by (auto_tac (claset(), simpset() addsimps [constrains_def, Acts_JN]));
qed "constrains_JN";

    (**FAILS, I think; see 5.4.1, Substitution Axiom.
       The problem is to relate reachable (F Join G) with 
       reachable F and reachable G

    Goalw [Constrains_def]
	"(JN i:I. F i) : Constrains A B = (ALL i:I. F i : Constrains A B)";
    by (simp_tac (simpset() addsimps [constrains_JN]) 1);
    by (Blast_tac 1);
    qed "Constrains_JN";

    Goal "F Join G : Constrains A B = (Constrains F A B & Constrains G A B)";
    by (auto_tac
	(claset(),
	 simpset() addsimps [Constrains_def, constrains_Join]));
    qed "Constrains_Join";
    **)

Goal "[| F : constrains A A';  G : constrains B B';  States F = States G |] \
\     ==> F Join G : constrains (A Int B) (A' Un B')";
by (asm_simp_tac (simpset() addsimps [constrains_Join]) 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "constrains_Join_weaken";

Goal "[| i : I;  eqStates I F |]  \
\     ==> (JN i:I. F i) : stable A = (ALL i:I. F i : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, constrains_JN]) 1);
qed "stable_JN";

Goal "[| ALL i:I. F i : invariant A;  i : I;  eqStates I F |]  \
\      ==> (JN i:I. F i) : invariant A";
by (asm_full_simp_tac (simpset() addsimps [invariant_def, stable_JN]) 1);
by (Blast_tac 1);
bind_thm ("invariant_JN_I", ballI RS result());

Goal "States F = States G \
\     ==> F Join G : stable A = (F : stable A & G : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, constrains_Join]) 1);
qed "stable_Join";

Goal "[| F : invariant A; G : invariant A; States F = States G |]  \
\     ==> F Join G : invariant A";
by (asm_full_simp_tac (simpset() addsimps [invariant_def, stable_Join]) 1);
by (Blast_tac 1);
qed "invariant_JoinI";

Goal "[| i : I;  eqStates I F |]  \
\      ==> FP (JN i:I. F i) = (INT i:I. FP (F i))";
by (asm_simp_tac (simpset() addsimps [FP_def, stable_JN, INTER_def]) 1);
qed "FP_JN";


(*** Progress: transient, ensures ***)


Goal "[| (JN i:I. F i) : transient A;  i: I |] ==> EX i:I. F i : transient A";
by (full_simp_tac (simpset() addsimps [transient_def, JOIN_def, Acts_eq_raw, 
				  Int_absorb1, restrict_rel_def]) 1);
by Safe_tac;
by (REPEAT (blast_tac (claset() addSIs [rev_bexI]) 1));
qed "transient_JN_imp_transient";

Goal "[| i : I;  eqStates I F |]  \
\     ==> (JN i:I. F i) : transient A = (EX i:I. F i : transient A)";
by (auto_tac (claset() addSIs [transient_JN_imp_transient], simpset()));
by (auto_tac (claset(), simpset() addsimps [transient_def, Acts_JN]));
qed "transient_JN";

Goal "F Join G : transient A ==> \
\     F : transient A | G : transient A";
by (full_simp_tac (simpset() addsimps [transient_def, Join_def, Acts_eq_raw, 
				       restrict_rel_def]) 1);
by Safe_tac;
(*delete act:Acts F possibility*)
by (rtac FalseE 3);  
(*delete act:Acts G possibility*)
by (thin_tac "~ (EX act:Acts G. ?P act)" 2);
by (REPEAT (blast_tac (claset() addSIs [rev_bexI]) 1));
qed "transient_Join_imp_transient";

Goal "States F = States G  \
\     ==> (F Join G : transient A) = (F : transient A | G : transient A)";
by (auto_tac (claset() addSIs [transient_Join_imp_transient], simpset()));
by (auto_tac (claset(), simpset() addsimps [transient_def, Acts_Join]));
qed "transient_Join";

Goal "[| i : I;  eqStates I F |]  \
\     ==> (JN i:I. F i) : ensures A B = \
\         ((ALL i:I. F i : constrains (A-B) (A Un B)) & \
\          (EX i:I. F i : ensures A B))";
by (auto_tac (claset(),
	      simpset() addsimps [ensures_def, constrains_JN, transient_JN]));
qed "ensures_JN";

Goalw [ensures_def]
     "States F = States G  \
\     ==> F Join G : ensures A B =     \
\         (F : constrains (A-B) (A Un B) & \
\          G : constrains (A-B) (A Un B) & \
\          (F : ensures A B | G : ensures A B))";
by (auto_tac (claset(),
	      simpset() addsimps [constrains_Join, transient_Join]));
qed "ensures_Join";

Goal "[| F : stable A;  G : constrains A A';  \
\        States F = States G; A <= States G |] \
\    ==> F Join G : constrains A A'";
by (forward_tac [constrains_imp_subset] 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, constrains_def,
					   ball_Un, Acts_Join]) 1);
by (Blast_tac 1);
qed "stable_constrains_Join";

(*Premise for G cannot use Invariant because  Stable F A  is weaker than
  G : stable A *)
Goal "[| F : stable A;  G : invariant A;  \
\        States F = States G |] ==> F Join G : Invariant A";
by (asm_full_simp_tac (simpset() addsimps [Invariant_def, invariant_def, 
					   Stable_eq_stable, stable_Join]) 1);
by (force_tac(claset() addIs [stable_reachable, stable_Int],
	      simpset() addsimps [Acts_Join]) 1);
qed "stable_Join_Invariant";

Goal "[| F : stable A;  G : ensures A B;  \
\        States F = States G |] ==> F Join G : ensures A B";
by (asm_simp_tac (simpset() addsimps [ensures_Join]) 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, ensures_def]) 1);
by (etac constrains_weaken 1);
by Auto_tac;
qed "ensures_stable_Join1";

(*As above, but exchanging the roles of F and G*)
Goal "[| F : ensures A B;  G : stable A;  \
\        States F = States G |] ==> F Join G : ensures A B";
by (stac Join_commute 1);
by (dtac sym 1);
by (blast_tac (claset() addIs [ensures_stable_Join1]) 1);
qed "ensures_stable_Join2";


(** Diff and localTo **)


Goal "States (Diff F acts) = States F";
by (simp_tac (simpset() addsimps [Diff_def]) 1);
qed "States_Diff";

Goal "Init (Diff F acts) = Init F";
by (auto_tac (claset() addIs [impOfSubs Init_subset_States],
	      simpset() addsimps [Diff_def]));
qed "Init_Diff";

Goal "Acts (Diff F acts) = insert (diag (States F)) (Acts F - acts)";
by (subgoal_tac "Acts F - acts <= Pow (States F Times States F)" 1);
by (blast_tac (claset() addEs [equalityE] 
                        addDs [impOfSubs Acts_subset_Pow_States]) 2);
by (auto_tac (claset(), simpset() addsimps [Diff_def]));
qed "Acts_Diff";

Addsimps [States_Diff, Init_Diff, Acts_Diff];


Goalw [Join_def] "States F = States G ==> F Join (Diff G (Acts F)) = F Join G";
by (rtac program_equalityI 1);
by (auto_tac (claset(), simpset() addsimps [insert_absorb]));
qed "Join_Diff2";

Goalw [Disjoint_def] "States F = States G ==> Disjoint F (Diff G (Acts F))";
by Auto_tac;
qed "Diff_Disjoint";

Goalw [Disjoint_def] "Disjoint F G ==> States F = States G";
by Auto_tac;
qed "Disjoint_States_eq";

Goal "[| F Join G : v localTo F;  Disjoint F G |] \
\     ==> G : (INT z. stable {s. v s = z})";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, Disjoint_def,
			 Acts_Join, stable_def, constrains_def]) 1);
by (Blast_tac 1);
qed "localTo_imp_stable";

Goal "[| F Join G : v localTo F;  (s,s') : act;  \
\        act : Acts G;  Disjoint F G  |] ==> v s' = v s";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, Disjoint_def,
			 Acts_Join, stable_def, constrains_def]) 1);
by (Blast_tac 1);
qed "localTo_imp_equals";

Goalw [localTo_def, stable_def, constrains_def]
     "v localTo F <= (f o v) localTo F";
by (Clarify_tac 1);
by (force_tac (claset() addSEs [allE, ballE], simpset()) 1);
qed "localTo_imp_o_localTo";


(*** Higher-level rules involving localTo and Join ***)

Goal "[| F : constrains {s. P (v s) (w s)} {s. P' (v s) (w s)};   \
\        F Join G : v localTo F;       \
\        F Join G : w localTo F;       \
\        Disjoint F G |]               \
\     ==> F Join G : constrains {s. P (v s) (w s)} {s. P' (v s) (w s)}";
by (auto_tac (claset(), 
	      simpset() addsimps [constrains_def, 
				  Disjoint_States_eq RS Acts_Join]));
by (REPEAT_FIRST (dtac localTo_imp_equals THEN' REPEAT1 o atac));
by (subgoal_tac "xa : States F" 1);
by (force_tac
    (claset() addSDs [Disjoint_States_eq,impOfSubs Acts_subset_Pow_States], 
     simpset()) 2);
by (Force_tac 1);
qed "constrains_localTo_constrains2";

Goalw [stable_def]
     "[| F : stable {s. P (v s) (w s)};   \
\        F Join G : v localTo F;       \
\        F Join G : w localTo F;       \
\        Disjoint F G |]               \
\     ==> F Join G : stable {s. P (v s) (w s)}";
by (blast_tac (claset() addIs [constrains_localTo_constrains2]) 1);
qed "stable_localTo_stable2";


Goal "(UN k. {s. f s = k}) = UNIV";
by (Blast_tac 1);
qed "UN_eq_UNIV";

Goal "[| F : stable {s. v s <= w s};   \
\        F Join G : v localTo F;       \
\        F Join G : Increasing w;      \
\        Disjoint F G |]               \
\     ==> F Join G : Stable {s. v s <= w s}";
by (safe_tac (claset() addSDs [localTo_imp_stable]));
by (rewrite_goals_tac [stable_def, Stable_def, Increasing_def]);
by (subgoal_tac "ALL k: UNIV. ?H : Constrains ({s. v s = k} Int ?AA) ?AA" 1);
by (dtac ball_Constrains_UN 1);
by (full_simp_tac (simpset() addsimps [UN_eq_UNIV]) 1);
by (rtac ballI 1);
by (subgoal_tac "F Join G : constrains ({s. v s = k} Int {s. v s <= w s}) \
\                                      ({s. v s = k} Un {s. v s <= w s})" 1);
by (asm_simp_tac
    (simpset() addsimps [Disjoint_States_eq RS constrains_Join]) 2);
by (blast_tac (claset() addIs [constrains_weaken]) 2);
by (dtac (constrains_imp_Constrains RS Constrains_Int) 1 THEN etac INT_D 1);
by (etac Constrains_weaken 2);
by Auto_tac;
qed "Increasing_localTo_Stable";
