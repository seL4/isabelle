(*  Title:      HOL/UNITY/Union.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unions of programs

From Misra's Chapter 5: Asynchronous Compositions of Programs
*)

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

(** SKIP and safety properties **)

Goalw [constrains_def] "(SKIP : A co B) = (A<=B)";
by Auto_tac;
qed "SKIP_in_constrains_iff";
AddIffs [SKIP_in_constrains_iff];

Goalw [Constrains_def] "(SKIP : A Co B) = (A<=B)";
by Auto_tac;
qed "SKIP_in_Constrains_iff";
AddIffs [SKIP_in_Constrains_iff];

Goalw [stable_def] "SKIP : stable A";
by Auto_tac;
qed "SKIP_in_stable";
AddIffs [SKIP_in_stable, SKIP_in_stable RS stable_imp_Stable];


(** Join **)

Goal "Init (F Join G) = Init F Int Init G";
by (simp_tac (simpset() addsimps [Join_def]) 1);
qed "Init_Join";

Goal "Acts (F Join G) = Acts F Un Acts G";
by (auto_tac (claset(), simpset() addsimps [Join_def]));
qed "Acts_Join";

Addsimps [Init_Join, Acts_Join];


(** JN **)

Goalw [JOIN_def, SKIP_def] "(JN i:{}. F i) = SKIP";
by Auto_tac;
qed "JN_empty";
Addsimps [JN_empty];

Goal "(JN i:insert a I. F i) = (F a) Join (JN i:I. F i)";
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

Addsimps [Init_JN, Acts_JN];

val prems = Goalw [JOIN_def]
    "[| I=J;  !!i. i:J ==> F i = G i |] ==> \
\    (JN i:I. F i) = (JN i:J. G i)";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "JN_cong";

Addcongs [JN_cong];


(** Algebraic laws **)

Goal "F Join G = G Join F";
by (simp_tac (simpset() addsimps [Join_def, Un_commute, Int_commute]) 1);
qed "Join_commute";

Goal "A Join (B Join C) = B Join (A Join C)";
by (simp_tac (simpset() addsimps Un_ac@Int_ac@[Join_def]) 1);
qed "Join_left_commute";

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

Goalw [Join_def] "F Join (F Join G) = F Join G";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Join_left_absorb";

(*Join is an AC-operator*)
val Join_ac = [Join_assoc, Join_left_absorb, Join_commute, Join_left_commute];


(*** JN laws ***)

(*Also follows by JN_insert and insert_absorb, but the proof is longer*)
Goal "k:I ==> F k Join (JN i:I. F i) = (JN i:I. F i)";
by (auto_tac (claset() addSIs [program_equalityI], simpset()));
qed "JN_absorb";

Goal "(JN i: I Un J. F i) = ((JN i: I. F i) Join (JN i:J. F i))";
by (auto_tac (claset() addSIs [program_equalityI], simpset()));
qed "JN_Un";

Goal "(JN i:I. c) = (if I={} then SKIP else c)";
by (auto_tac (claset() addSIs [program_equalityI], simpset()));
qed "JN_constant";

Goal "(JN i:I. F i Join G i) = (JN i:I. F i)  Join  (JN i:I. G i)";
by (auto_tac (claset() addSIs [program_equalityI], simpset()));
qed "JN_Join_distrib";

Goal "i : I ==> (JN i:I. F i Join G) = ((JN i:I. F i) Join G)";
by (asm_simp_tac (simpset() addsimps [JN_Join_distrib, JN_constant]) 1);
by Auto_tac;
qed "JN_Join_miniscope";


(*** Safety: co, stable, FP ***)

(*Fails if I={} because it collapses to SKIP : A co B*)
Goalw [constrains_def, JOIN_def]
    "i : I ==> (JN i:I. F i) : A co B = (ALL i:I. F i : A co B)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "JN_constrains";

Goal "(F Join G : A co B) = (F : A co B & G : A co B)";
by (auto_tac
    (claset(),
     simpset() addsimps [constrains_def, Join_def]));
qed "Join_constrains";

(*Analogous weak versions FAIL; see Misra [1994] 5.4.1, Substitution Axiom.
  reachable (F Join G) could be much bigger than reachable F, reachable G
*)


Goal "[| F : A co A';  G : B co B' |] \
\     ==> F Join G : (A Int B) co (A' Un B')";
by (simp_tac (simpset() addsimps [Join_constrains]) 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "Join_constrains_weaken";

Goal "[| ALL i:I. F i : A i co A' i;  i: I |] \
\     ==> (JN i:I. F i) : (INT i:I. A i) co (UN i:I. A' i)";
by (asm_simp_tac (simpset() addsimps [JN_constrains]) 1);
by (blast_tac (claset() addIs [constrains_weaken]) 1);
qed "JN_constrains_weaken";

Goal "i : I ==> \
\     (JN i:I. F i) : stable A = (ALL i:I. F i : stable A)";
by (asm_simp_tac (simpset() addsimps [stable_def, JN_constrains]) 1);
qed "JN_stable";

Goal "[| ALL i:I. F i : invariant A;  i : I |]  \
\      ==> (JN i:I. F i) : invariant A";
by (asm_full_simp_tac (simpset() addsimps [invariant_def, JN_stable]) 1);
by (Blast_tac 1);
bind_thm ("invariant_JN_I", ballI RS result());

Goal "(F Join G : stable A) = \
\     (F : stable A & G : stable A)";
by (simp_tac (simpset() addsimps [stable_def, Join_constrains]) 1);
qed "Join_stable";

Goal "(F Join G : increasing f) = \
\     (F : increasing f & G : increasing f)";
by (simp_tac (simpset() addsimps [increasing_def, Join_stable]) 1);
by (Blast_tac 1);
qed "Join_increasing";

Goal "[| F : invariant A; G : invariant A |]  \
\     ==> F Join G : invariant A";
by (full_simp_tac (simpset() addsimps [invariant_def, Join_stable]) 1);
by (Blast_tac 1);
qed "invariant_JoinI";

Goal "i : I ==> FP (JN i:I. F i) = (INT i:I. FP (F i))";
by (asm_simp_tac (simpset() addsimps [FP_def, JN_stable, INTER_def]) 1);
qed "FP_JN";


(*** Progress: transient, ensures ***)

Goal "i : I ==> \
\   (JN i:I. F i) : transient A = (EX i:I. F i : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [transient_def, JOIN_def]));
qed "JN_transient";

Goal "F Join G : transient A = \
\     (F : transient A | G : transient A)";
by (auto_tac (claset(),
	      simpset() addsimps [bex_Un, transient_def,
				  Join_def]));
qed "Join_transient";

Goal "i : I ==> \
\     (JN i:I. F i) : A ensures B = \
\     ((ALL i:I. F i : (A-B) co (A Un B)) & \
\      (EX i:I. F i : A ensures B))";
by (auto_tac (claset(),
	      simpset() addsimps [ensures_def, JN_constrains, JN_transient]));
qed "JN_ensures";

Goalw [ensures_def]
     "F Join G : A ensures B =     \
\     (F : (A-B) co (A Un B) & G : (A-B) co (A Un B) & \
\      (F : transient (A-B) | G : transient (A-B)))";
by (auto_tac (claset(),
	      simpset() addsimps [Join_constrains, Join_transient]));
qed "Join_ensures";

Goalw [stable_def, constrains_def, Join_def]
    "[| F : stable A;  G : A co A' |] \
\    ==> F Join G : A co A'";
by (asm_full_simp_tac (simpset() addsimps [ball_Un]) 1);
by (Blast_tac 1);
qed "stable_Join_constrains";

(*Premise for G cannot use Always because  F: Stable A  is weaker than
  G : stable A *)
Goal "[| F : stable A;  G : invariant A |] ==> F Join G : Always A";
by (full_simp_tac (simpset() addsimps [Always_def, invariant_def, 
				       Stable_eq_stable, Join_stable]) 1);
by (force_tac(claset() addIs [stable_reachable, stable_Int],
	      simpset()) 1);
qed "stable_Join_Always";

Goal "[| F : stable A;  G : A ensures B |] ==> F Join G : A ensures B";
by (asm_simp_tac (simpset() addsimps [Join_ensures]) 1);
by (asm_full_simp_tac (simpset() addsimps [stable_def, ensures_def]) 1);
by (etac constrains_weaken 1);
by Auto_tac;
qed "stable_Join_ensures1";

(*As above, but exchanging the roles of F and G*)
Goal "[| F : A ensures B;  G : stable A |] ==> F Join G : A ensures B";
by (stac Join_commute 1);
by (blast_tac (claset() addIs [stable_Join_ensures1]) 1);
qed "stable_Join_ensures2";


(** Diff and localTo **)

Goalw [Diff_def] "F Join (Diff UNIV G (Acts F)) = F Join G";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Join_Diff2";

Goalw [Diff_def]
   "Diff C (F Join G) (Acts H) = (Diff C F (Acts H)) Join (Diff C G (Acts H))";
by (rtac program_equalityI 1);
by Auto_tac;
qed "Diff_Join_distrib";

Goalw [Diff_def] "Diff C F (Acts F) = mk_program(Init F, {})";
by Auto_tac;
qed "Diff_self_eq";

Goalw [Diff_def, Disjoint_def] "Disjoint C F (Diff C G (Acts F))";
by (force_tac (claset(), 
	       simpset() addsimps [Restrict_imageI, 
				   sym RSN (2,Restrict_imageI)]) 1);
qed "Diff_Disjoint";

Goalw [Disjoint_def]
     "[| A <= B; Disjoint A F G |] ==> Disjoint B F G";
by (blast_tac (claset() addIs [Restrict_eq_mono RSN (2,Restrict_imageI)]) 1);
qed "Disjoint_mono";

(*** localTo ***)

Goalw [LOCALTO_def, Diff_def, stable_def, constrains_def]
     "A <= B ==> v localTo[B] F <= v localTo[A] F";
by Auto_tac;
by (dres_inst_tac [("x", "v xc")] spec 1);
by (dres_inst_tac [("x", "Restrict B xa")] bspec 1);
by Auto_tac;
by (blast_tac (claset() addIs [Restrict_eq_mono RSN (2,Restrict_imageI)]) 1);
qed "localTo_anti_mono";

bind_thm ("localTo_UNIV_imp_localTo", 
	  impOfSubs (subset_UNIV RS localTo_anti_mono));

Goalw [LocalTo_def]
     "G : v localTo[UNIV] F ==> G : v LocalTo F";
by (blast_tac (claset() addDs [impOfSubs localTo_anti_mono]) 1);
qed "localTo_imp_LocalTo";

Goalw [LOCALTO_def, stable_def, constrains_def]
     "v localTo[C] F <= (f o v) localTo[C] F";
by (Clarify_tac 1);
by (force_tac (claset() addSEs [allE, ballE], simpset()) 1);
qed "localTo_imp_o_localTo";

(*NOT USED*)
Goalw [LOCALTO_def, stable_def, constrains_def]
     "(%s. x) localTo[C] F = UNIV";
by (Blast_tac 1);
qed "triv_localTo_eq_UNIV";

Goal "(F Join G : v localTo[C] H) = \
\     (F : v localTo[C] H  &  G : v localTo[C] H)";
by (simp_tac (simpset() addsimps [LOCALTO_def, Diff_Join_distrib,
				  stable_def, Join_constrains]) 1);
by (Blast_tac 1);
qed "Join_localTo";

Goal "F : v localTo[C] F";
by (simp_tac 
    (simpset() addsimps [LOCALTO_def, stable_def, constrains_def, 
			 Diff_self_eq]) 1);
qed "self_localTo";

Goal "(F Join G : v localTo[C] F) = (G : v localTo[C] F)";
by (simp_tac (simpset() addsimps [Join_localTo, self_localTo]) 1);
qed "self_Join_localTo";

Goal "(F Join G : v LocalTo F) = (G : v LocalTo F)";
by (simp_tac (simpset() addsimps [self_Join_localTo, LocalTo_def,
				  Join_left_absorb]) 1);
qed "self_Join_LocalTo";



(*** Higher-level rules involving localTo and Join ***)

Goal "[| F : {s. P (v s)} co {s. P' (v s)};  G : v localTo[C] F |]  \
\     ==> G : C Int {s. P (v s)} co {s. P' (v s)}";
by (ftac constrains_imp_subset 1);
by (auto_tac (claset(), 
	      simpset() addsimps [LOCALTO_def, stable_def, constrains_def,
				  Diff_def]));
by (case_tac "Restrict C act: Restrict C `` Acts F" 1);
by (blast_tac (claset() addSEs [equalityE]) 1);
by (subgoal_tac "v x = v xa" 1);
by (Force_tac 1);
by (thin_tac "ALL act: ?A. ?P act" 1);
by (dtac spec 1);
by (dres_inst_tac [("x", "Restrict C act")] bspec 1);
by Auto_tac;
qed "constrains_localTo_constrains";

Goalw [LOCALTO_def, stable_def, constrains_def, Diff_def]
     "[| G : v localTo[C] F;  G : w localTo[C] F |]  \
\     ==> G : (%s. (v s, w s)) localTo[C] F";
by (Blast_tac 1);
qed "localTo_pairfun";

Goal "[| F : {s. P (v s) (w s)} co {s. P' (v s) (w s)};   \
\        G : v localTo[C] F;       \
\        G : w localTo[C] F |]               \
\     ==> G : C Int {s. P (v s) (w s)} co {s. P' (v s) (w s)}";
by (res_inst_tac [("A", "C Int {s. (%(x,y). P x y) (v s, w s)}"),
		  ("A'", "{s. (%(x,y). P' x y) (v s, w s)}")] 
    constrains_weaken 1);
by (rtac (localTo_pairfun RSN (2, constrains_localTo_constrains)) 1);
by Auto_tac;
qed "constrains_localTo_constrains2";

(*Used just once, in Client.ML.  Having F in the conclusion is silly.*)
Goalw [stable_def]
     "[| F : stable {s. P (v s) (w s)};   \
\        G : v localTo[UNIV] F;  G : w localTo[UNIV] F |]               \
\     ==> F Join G : stable {s. P (v s) (w s)}";
by (asm_simp_tac (simpset() addsimps [Join_constrains]) 1);
by (blast_tac (claset() addIs [constrains_localTo_constrains2 RS 
			       constrains_weaken]) 1);
qed "stable_localTo_stable2";

(*Used just in Client.ML.  Generalize to arbitrary C?*)
Goal "[| F : stable {s. v s <= w s};   \
\        G : v localTo[UNIV] F;       \
\        F Join G : Increasing w |]               \
\     ==> F Join G : Stable {s. v s <= w s}";
by (auto_tac (claset(), 
	      simpset() addsimps [stable_def, Stable_def, Increasing_def, 
		    Constrains_def, Join_constrains, all_conj_distrib]));
by (blast_tac (claset() addIs [constrains_weaken]) 1);
(*The G case remains; proved like constrains_localTo_constrains*)
by (auto_tac (claset(), 
              simpset() addsimps [LOCALTO_def, stable_def, constrains_def,
                                  Diff_def]));
by (case_tac "act: Acts F" 1);
by (Blast_tac 1);
by (thin_tac "ALL act:Acts F. ?P act" 1);
by (thin_tac "ALL z. ALL act:Acts F. ?P z act" 1);
by (dres_inst_tac [("x", "v xa")] spec 1 THEN dtac bspec 1 THEN rtac DiffI 1);
by (assume_tac 1);
by (Blast_tac 1);
by (subgoal_tac "v x = v xa" 1);
by Auto_tac;
qed "Increasing_localTo_Stable";
