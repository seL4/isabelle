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

Goal "Init SKIP = UNIV";
by (simp_tac (simpset() addsimps [SKIP_def]) 1);
qed "Init_SKIP";

Goal "Acts SKIP = {Id}";
by (simp_tac (simpset() addsimps [SKIP_def]) 1);
qed "Acts_SKIP";

Addsimps [Init_SKIP, Acts_SKIP];

Goal "reachable SKIP = UNIV";
by (force_tac (claset() addEs [reachable.induct]
			addIs reachable.intrs, simpset()) 1);
qed "reachable_SKIP";

Addsimps [reachable_SKIP];


(** Join **)

Goal "Init (F Join G) = Init F Int Init G";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Init_Join";

Goal "Acts (F Join G) = Acts F Un Acts G";
by (auto_tac (claset(), simpset() addsimps [Join_def]));
qed "Acts_Join";

Addsimps [Init_Join];


(** JN **)

Goalw [JOIN_def, SKIP_def] "(JN i:{}. F i) = SKIP";
by Auto_tac;
qed "JN_empty";
Addsimps [JN_empty];

Goal "(JN x:insert a A. B x) = (B a) Join (JN x:A. B x)";
by (rtac program_equalityI 1);
by (ALLGOALS (simp_tac (simpset() addsimps [JOIN_def, Join_def])));
qed "JN_insert";
Addsimps[JN_empty, JN_insert];

Goal "Init (JN i:I. F i) = (INT i:I. Init (F i))";
by (simp_tac (simpset() addsimps [JOIN_def]) 1);
qed "Init_JN";

Goal "Acts (JN i:I. F i) = insert Id (UN i:I. Acts (F i))";
by (auto_tac (claset(), simpset() addsimps [JOIN_def]));
qed "Acts_JN";

Addsimps [Init_JN];

val prems = Goalw [JOIN_def]
    "[| A=B;  !!x. x:B ==> F(x) = G(x) |] ==> \
\    (JN x:A. F(x)) = (JN x:B. G(x))";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "JN_cong";

Addcongs [JN_cong];


(** Algebraic laws **)

Goal "F Join G = G Join F";
by (simp_tac (simpset() addsimps [Join_def, Un_commute, Int_commute]) 1);
qed "Join_commute";

Goal "(F Join G) Join H = F Join (G Join H)";
by (simp_tac (simpset() addsimps Un_ac@[Join_def, Int_assoc]) 1);
qed "Join_assoc";
 
Goalw [Join_def, SKIP_def] "SKIP Join F = F";
by (rtac program_equalityI 1);
by (ALLGOALS (simp_tac (simpset() addsimps [insert_absorb])));
qed "Join_SKIP_left";

Goalw [Join_def, SKIP_def] "F Join SKIP = F";
by (rtac program_equalityI 1);
by (ALLGOALS (simp_tac (simpset() addsimps [insert_absorb])));
qed "Join_SKIP_right";

Addsimps [Join_SKIP_left, Join_SKIP_right];

Goalw [Join_def] "F Join F = F";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Join_absorb";

Addsimps [Join_absorb];



(*** JN laws ***)



Goal "i : I ==> (JN i:I. A i Join B) = ((JN i:I. A i) Join B)";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [Acts_JN, Acts_Join]));
qed "JN_Join_miniscope";

Goal "k:I ==> A k Join (JN i:I. A i) = (JN i:I. A i)";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [Acts_JN, Acts_Join]));
qed "JN_absorb";

Goal "(JN i: I Un J. A i) = ((JN i: I. A i) Join (JN i:J. A i))";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [Acts_JN, Acts_Join]));
qed "JN_Join";

Goal "i: I ==> (JN i:I. c) = c";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [Acts_JN]));
qed "JN_constant";

Goal "(JN i:I. A i Join B i) = (JN i:I. A i)  Join  (JN i:I. B i)";
by (auto_tac (claset() addSIs [program_equalityI],
	      simpset() addsimps [Acts_JN, Acts_Join]));
qed "JN_Join_distrib";


(*** Safety: constrains, stable, FP ***)

Goalw [constrains_def, JOIN_def]
    "i : I ==> \
\    (JN i:I. F i) : constrains A B = (ALL i:I. F i : constrains A B)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "constrains_JN";

Goal "F Join G : constrains A B =  \
\     (F : constrains A B & G : constrains A B)";
by (auto_tac
    (claset(),
     simpset() addsimps [constrains_def, Join_def]));
qed "constrains_Join";

Goal "[| i : I;  ALL i:I. F i : constrains A B |] \
\     ==> (JN i:I. F i) : constrains A B";
by (full_simp_tac (simpset() addsimps [constrains_def, Acts_JN]) 1);
by (Blast_tac 1);
qed "constrains_imp_JN_constrains";

Goal "[| i : I;  compatible (F``I) |] \
\     ==> (JN i:I. F i) : constrains A B = (ALL i:I. F i : constrains A B)";
by (asm_simp_tac (simpset() addsimps [constrains_def, Acts_JN]) 1);
by (Blast_tac 1);
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


Goal "[| F : constrains A A';  G : constrains B B' |] \
\     ==> F Join G : constrains (A Int B) (A' Un B')";
by (simp_tac (simpset() addsimps [constrains_Join]) 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "constrains_Join_weaken";

Goal "i : I ==> \
\     (JN i:I. F i) : stable A = (ALL i:I. F i : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, constrains_JN]) 1);
qed "stable_JN";

Goal "[| ALL i:I. F i : invariant A;  i : I |]  \
\      ==> (JN i:I. F i) : invariant A";
by (asm_full_simp_tac (simpset() addsimps [invariant_def, stable_JN]) 1);
by (Blast_tac 1);
bind_thm ("invariant_JN_I", ballI RS result());

Goal "F Join G : stable A = \
\     (F : stable A & G : stable A)";
by (simp_tac (simpset() addsimps [stable_def, constrains_Join]) 1);
qed "stable_Join";

Goal "[| F : invariant A; G : invariant A |]  \
\     ==> F Join G : invariant A";
by (full_simp_tac (simpset() addsimps [invariant_def, stable_Join]) 1);
by (Blast_tac 1);
qed "invariant_JoinI";

Goal "i : I ==> FP (JN i:I. F i) = (INT i:I. FP (F i))";
by (asm_simp_tac (simpset() addsimps [FP_def, stable_JN, INTER_def]) 1);
qed "FP_JN";


(*** Progress: transient, ensures ***)

Goal "i : I ==> \
\   (JN i:I. F i) : transient A = (EX i:I. F i : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [transient_def, JOIN_def]));
qed "transient_JN";

Goal "F Join G : transient A = \
\     (F : transient A | G : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [bex_Un, transient_def,
				  Join_def]));
qed "transient_Join";

Goal "i : I ==> \
\     (JN i:I. F i) : ensures A B = \
\     ((ALL i:I. F i : constrains (A-B) (A Un B)) & \
\      (EX i:I. F i : ensures A B))";
by (auto_tac (claset(),
	      simpset() addsimps [ensures_def, constrains_JN, transient_JN]));
qed "ensures_JN";

Goalw [ensures_def]
     "F Join G : ensures A B =     \
\     (F : constrains (A-B) (A Un B) & \
\      G : constrains (A-B) (A Un B) & \
\      (F : ensures A B | G : ensures A B))";
by (auto_tac (claset(),
	      simpset() addsimps [constrains_Join, transient_Join]));
qed "ensures_Join";

Goalw [stable_def, constrains_def, Join_def]
    "[| F : stable A;  G : constrains A A' |] \
\    ==> F Join G : constrains A A'";
by (asm_full_simp_tac (simpset() addsimps [ball_Un]) 1);
by (Blast_tac 1);
qed "stable_constrains_Join";

(*Premise for G cannot use Invariant because  Stable F A  is weaker than
  G : stable A *)
Goal "[| F : stable A;  G : invariant A |] ==> F Join G : Invariant A";
by (full_simp_tac (simpset() addsimps [Invariant_def, invariant_def, 
				       Stable_eq_stable, stable_Join]) 1);
by (force_tac(claset() addIs [stable_reachable, stable_Int],
	      simpset() addsimps [Acts_Join]) 1);
qed "stable_Join_Invariant";

Goal "[| F : stable A;  G : ensures A B |] ==> F Join G : ensures A B";
by (asm_simp_tac (simpset() addsimps [ensures_Join]) 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, ensures_def]) 1);
by (etac constrains_weaken 1);
by Auto_tac;
qed "ensures_stable_Join1";

(*As above, but exchanging the roles of F and G*)
Goal "[| F : ensures A B;  G : stable A |] ==> F Join G : ensures A B";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [ensures_stable_Join1]) 1);
qed "ensures_stable_Join2";


(** Diff and localTo **)

Goalw [Join_def, Diff_def] "F Join (Diff G (Acts F)) = F Join G";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Join_Diff2";

Goalw [Diff_def, Disjoint_def] "Disjoint F (Diff G (Acts F))";
by Auto_tac;
qed "Diff_Disjoint";

Goal "[| F Join G : v localTo F;  Disjoint F G |] \
\     ==> G : (INT z. stable {s. v s = z})";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, Diff_def, Disjoint_def,
			 Acts_Join, stable_def, constrains_def]) 1);
by (Blast_tac 1);
qed "localTo_imp_stable";

Goal "[| F Join G : v localTo F;  (s,s') : act;  \
\        act : Acts G;  Disjoint F G |] ==> v s' = v s";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, Diff_def, Disjoint_def,
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
by (auto_tac (claset(), simpset() addsimps [constrains_def, Acts_Join]));
by (REPEAT_FIRST (dtac localTo_imp_equals THEN' REPEAT1 o atac));
by Auto_tac;
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
by (asm_simp_tac (simpset() addsimps [constrains_Join]) 2);
by (blast_tac (claset() addIs [constrains_weaken]) 2);
by (dtac (constrains_imp_Constrains RS Constrains_Int) 1 THEN etac INT_D 1);
by (etac Constrains_weaken 2);
by Auto_tac;
qed "Increasing_localTo_Stable";
