(* 
    File:	 TLA/TLA.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

Lemmas and tactics for temporal reasoning.
*)

(* Specialize intensional introduction/elimination rules to temporal formulas *)

qed_goal "tempI" TLA.thy "(!!sigma. (sigma |= (F::temporal))) ==> F"
  (fn [prem] => [ REPEAT (resolve_tac [prem,intI] 1) ]);

qed_goal "tempD" TLA.thy "F::temporal ==> (sigma |= F)"
  (fn [prem] => [ REPEAT (resolve_tac [prem,intD] 1) ]);


(* ======== Functions to "unlift" temporal implications into HOL rules ====== *)

(* Basic unlifting introduces a parameter "sigma" and applies basic rewrites, e.g.
   F .= G    gets   (sigma |= F) = (sigma |= G)
   F .-> G   gets   (sigma |= F) --> (sigma |= G)
*)
fun temp_unlift th = rewrite_rule intensional_rews (th RS tempD);

(* F .-> G   becomes   sigma |= F  ==>  sigma |= G *)
fun temp_mp th = zero_var_indexes ((temp_unlift th) RS mp);

(* F .-> G   becomes   [| sigma |= F; sigma |= G ==> R |] ==> R 
   so that it can be used as an elimination rule
*)
fun temp_impE th = zero_var_indexes ((temp_unlift th) RS impE);

(* F .& G .-> H  becomes  [| sigma |= F; sigma |= G |] ==> sigma |= H *)
fun temp_conjmp th = zero_var_indexes (conjI RS (temp_mp th));

(* F .& G .-> H  becomes  [| sigma |= F; sigma |= G; (sigma |= H ==> R) |] ==> R *)
fun temp_conjimpE th = zero_var_indexes (conjI RS (temp_impE th));

(* Turn  F .= G  into meta-level rewrite rule  F == G *)
fun temp_rewrite th = (rewrite_rule intensional_rews (th RS inteq_reflection));


(* Update classical reasoner---will be updated once more below! *)

AddSIs [tempI];
AddDs [tempD];

val temp_cs = action_cs addSIs [tempI] addDs [tempD];
val temp_css = (temp_cs,simpset());

(* ========================================================================= *)
section "Init";

(* Push logical connectives through Init. *)
qed_goal "Init_true" TLA.thy "Init(#True) .= #True"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

qed_goal "Init_false" TLA.thy "Init(#False) .= #False"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

qed_goal "Init_not" TLA.thy "Init(.~P) .= (.~Init(P))"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

qed_goal "Init_and" TLA.thy "Init(P .& Q) .= (Init(P) .& Init(Q))"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

qed_goal "Init_or" TLA.thy "Init(P .| Q) .= (Init(P) .| Init(Q))"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

qed_goal "Init_imp" TLA.thy "Init(P .-> Q) .= (Init(P) .-> Init(Q))"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

qed_goal "Init_iff" TLA.thy "Init(P .= Q) .= (Init(P) .= Init(Q))"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

qed_goal "Init_all" TLA.thy "Init(RALL x. P(x)) .= (RALL x. Init(P(x)))"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

qed_goal "Init_ex" TLA.thy "Init(REX x. P(x)) .= (REX x. Init(P(x)))"
  (fn _ => [ auto_tac (temp_css addsimps2 [Init_def]) ]);

val Init_simps = map temp_rewrite
                     [Init_true,Init_false,Init_not,Init_and,Init_or,
		      Init_imp,Init_iff,Init_all,Init_ex];


(* Temporal lemmas *)

qed_goalw "DmdAct" TLA.thy [dmd_def,boxact_def] "(<>(F::action)) .= (<> Init F)"
  (fn _ => [auto_tac (temp_css addsimps2 Init_simps)]);


(* ------------------------------------------------------------------------- *)
(***           "Simple temporal logic": only [] and <>                     ***)
(* ------------------------------------------------------------------------- *)
section "Simple temporal logic";

(* ------------------------ STL2 ------------------------------------------- *)
bind_thm("STL2", reflT);
bind_thm("STL2D", temp_mp STL2);

(* The action variants. *)
qed_goalw "STL2b" TLA.thy [boxact_def] "[]P .-> Init P"
   (fn _ => [rtac STL2 1]);
bind_thm("STL2bD", temp_mp STL2b);
(* see also STL2b_pr below: "[]P .-> Init(P .& P`)" *)

(* Dual versions for <> *)
qed_goalw "ImplDmd" TLA.thy [dmd_def] "F .-> <>F"
   (fn _ => [ auto_tac (temp_css addSDs2 [STL2D]) ]);
bind_thm ("ImplDmdD", temp_mp ImplDmd);

qed_goalw "InitDmd" TLA.thy [dmd_def] "Init(P) .-> <>P"
   (fn _ => [ auto_tac (temp_css addsimps2 Init_simps addSDs2 [STL2bD]) ]);
bind_thm("InitDmdD", temp_mp InitDmd);


(* ------------------------ STL3 ------------------------------------------- *)
qed_goal "STL3" TLA.thy "([][]F) .= ([]F)"
   (fn _ => [auto_tac (temp_css addIs2 [temp_mp transT,temp_mp STL2])]);

(* corresponding elimination rule introduces double boxes: 
   [| (sigma |= []F); (sigma |= [][]F) ==> PROP W |] ==> PROP W
*)
bind_thm("dup_boxE", make_elim((temp_unlift STL3) RS iffD2));
bind_thm("dup_boxD", (temp_unlift STL3) RS iffD1);

(* dual versions for <> *)
qed_goalw "DmdDmd" TLA.thy [dmd_def] "(<><>F) .= (<>F)"
   (fn _ => [ auto_tac (temp_css addsimps2 [STL3]) ]);
bind_thm("dup_dmdE", make_elim((temp_unlift DmdDmd) RS iffD2));
bind_thm("dup_dmdD", (temp_unlift DmdDmd) RS iffD1);


(* ------------------------ STL4 ------------------------------------------- *)
qed_goal "STL4" TLA.thy "(F .-> G)  ==> ([]F .-> []G)"
   (fn [prem] => [Auto_tac,
		  rtac ((temp_mp normalT) RS mp) 1,
		  REPEAT (ares_tac [prem, necT RS tempD] 1)
		 ]);

(* A more practical variant as an (unlifted) elimination rule *)
qed_goal "STL4E" TLA.thy 
         "[| (sigma |= []F); F .-> G |] ==> (sigma |= []G)"
   (fn prems => [ REPEAT (resolve_tac (prems @ [temp_mp STL4]) 1) ]);

(* see also STL4Edup below, which allows an auxiliary boxed formula:
       []A /\ F => G
     -----------------
     []A /\ []F => []G
*)

(* The dual versions for <> *)
qed_goalw "DmdImpl" TLA.thy [dmd_def]
   "(F .-> G) ==> (<>F .-> <>G)"
   (fn [prem] => [fast_tac (temp_cs addSIs [int_mp prem] addSEs [STL4E]) 1]);

qed_goal "DmdImplE" TLA.thy
   "[| (sigma |= <>F); F .-> G |] ==> (sigma |= <>G)"
   (fn prems => [ REPEAT (resolve_tac (prems @ [temp_mp DmdImpl]) 1) ]);


(* ------------------------ STL5 ------------------------------------------- *)
qed_goal "STL5" TLA.thy "([]F .& []G) .= ([](F .& G))"
   (fn _ => [Auto_tac,
	     subgoal_tac "sigma |= [](G .-> (F .& G))" 1,
	     etac ((temp_mp normalT) RS mp) 1, atac 1,
	     ALLGOALS (fast_tac (temp_cs addSEs [STL4E]))
	    ]);
(* rewrite rule to split conjunctions under boxes *)
bind_thm("split_box_conj", (temp_unlift STL5) RS sym);

(* the corresponding elimination rule allows to combine boxes in the hypotheses
   (NB: F and G must have the same type, i.e., both actions or temporals.)
*)
qed_goal "box_conjE" TLA.thy
   "[| (sigma |= []F); (sigma |= []G); (sigma |= [](F.&G)) ==> PROP R |] ==> PROP R"
   (fn prems => [ REPEAT (resolve_tac
			   (prems @ [(temp_unlift STL5) RS iffD1, conjI]) 1) ]);

(* Define a tactic that tries to merge all boxes in an antecedent. The definition is
   a bit kludgy: how do you simulate "double elim-resolution"?
   Note: If there are boxed hypotheses of different types, the tactic may delete the 
         wrong formulas. We therefore also define less polymorphic tactics for
         temporals and actions.
*)
qed_goal "box_thin" TLA.thy "[| (sigma |= []F); PROP W |] ==> PROP W"
  (fn prems => [resolve_tac prems 1]);

fun merge_box_tac i =
   REPEAT_DETERM (EVERY [etac box_conjE i, atac i, etac box_thin i]);

qed_goal "temp_box_conjE" TLA.thy
   "[| (sigma |= [](F::temporal)); (sigma |= []G); (sigma |= [](F.&G)) ==> PROP R |] ==> PROP R"
   (fn prems => [ REPEAT (resolve_tac
			   (prems @ [(temp_unlift STL5) RS iffD1, conjI]) 1) ]);
qed_goal "temp_box_thin" TLA.thy "[| (sigma |= [](F::temporal)); PROP W |] ==> PROP W"
  (fn prems => [resolve_tac prems 1]);
fun merge_temp_box_tac i =
   REPEAT_DETERM (EVERY [etac temp_box_conjE i, atac i, etac temp_box_thin i]);

qed_goal "act_box_conjE" TLA.thy
   "[| (sigma |= [](A::action)); (sigma |= []B); (sigma |= [](A.&B)) ==> PROP R |] ==> PROP R"
   (fn prems => [ REPEAT (resolve_tac
			   (prems @ [(temp_unlift STL5) RS iffD1, conjI]) 1) ]);
qed_goal "act_box_thin" TLA.thy "[| (sigma |= [](A::action)); PROP W |] ==> PROP W"
  (fn prems => [resolve_tac prems 1]);
fun merge_act_box_tac i =
   REPEAT_DETERM (EVERY [etac act_box_conjE i, atac i, etac act_box_thin i]);

(* rewrite rule to push universal quantification through box:
      (sigma |= [](RALL x. F x)) = (! x. (sigma |= []F x))
*)
bind_thm("all_box", standard((temp_unlift allT) RS sym));


qed_goal "DmdOr" TLA.thy "(<>(F .| G)) .= (<>F .| <>G)"
   (fn _ => [auto_tac (temp_css addsimps2 [dmd_def,split_box_conj]),
             TRYALL (EVERY' [etac swap, 
                             merge_box_tac, 
                             fast_tac (temp_cs addSEs [STL4E])])
            ]);

qed_goal "exT" TLA.thy "(REX x. <>(F x)) .= (<>(REX x. F x))"
   (fn _ => [ auto_tac (temp_css addsimps2 [dmd_def,temp_rewrite Not_rex,all_box]) ]);

bind_thm("ex_dmd", standard((temp_unlift exT) RS sym));
	     

qed_goal "STL4Edup" TLA.thy
   "!!sigma. [| (sigma |= []A); (sigma |= []F); F .& []A .-> G |] ==> (sigma |= []G)"
   (fn _ => [etac dup_boxE 1,
	     merge_box_tac 1,
	     etac STL4E 1,
	     atac 1
	    ]);

qed_goalw "DmdImpl2" TLA.thy [dmd_def]
   "!!sigma. [| (sigma |= <>F); (sigma |= [](F .-> G)) |] ==> (sigma |= <>G)"
   (fn _ => [Auto_tac,
	     etac notE 1,
	     merge_box_tac 1,
	     fast_tac (temp_cs addSEs [STL4E]) 1
	    ]);

qed_goal "InfImpl" TLA.thy
   "[| (sigma |= []<>F); (sigma |= []G); F .& G .-> H |] ==> (sigma |= []<>H)"
   (fn [prem1,prem2,prem3] 
       => [cut_facts_tac [prem1,prem2] 1,
	   eres_inst_tac [("F","G")] dup_boxE 1,
	   merge_box_tac 1,
	   fast_tac (temp_cs addSEs [STL4E,DmdImpl2] addSIs [int_mp prem3]) 1
	  ]);

(* ------------------------ STL6 ------------------------------------------- *)
(* Used in the proof of STL6, but useful in itself. *)
qed_goalw "BoxDmdT" TLA.thy [dmd_def] "[]F .& <>G .-> <>([]F .& G)"
  (fn _ => [ Auto_tac,
             etac dup_boxE 1,
	     merge_box_tac 1,
             etac swap 1,
             fast_tac (temp_cs addSEs [STL4E]) 1 ]);
bind_thm("BoxDmd", temp_conjmp BoxDmdT);

(* weaker than BoxDmd, but more polymorphic (and often just right) *)
qed_goalw "BoxDmdT2" TLA.thy [dmd_def] "<>F .& []G .-> <>(F .& G)"
  (fn _ => [ Auto_tac,
	     merge_box_tac 1,
             fast_tac (temp_cs addSEs [notE,STL4E]) 1
	   ]);

qed_goal "STL6" TLA.thy "<>[]F .& <>[]G .-> <>[](F .& G)"
  (fn _ => [auto_tac (temp_css addsimps2 [symmetric (temp_rewrite STL5)]),
	    etac (temp_conjimpE linT) 1, atac 1, etac thin_rl 1,
	    rtac ((temp_unlift DmdDmd) RS iffD1) 1,
	    etac disjE 1,
	    etac DmdImplE 1, rtac BoxDmdT 1,
	    (* the second subgoal needs commutativity of .&, which complicates the proof *)
	    etac DmdImplE 1,
	    Auto_tac,
	    etac (temp_conjimpE BoxDmdT) 1, atac 1, etac thin_rl 1,
	    fast_tac (temp_cs addSEs [DmdImplE]) 1
	   ]);


(* ------------------------ True / False ----------------------------------------- *)
section "Simplification of constants";

qed_goal "BoxTrue" TLA.thy "[](#True)"
   (fn _ => [ fast_tac (temp_cs addSIs [necT]) 1 ]);

qed_goal "BoxTrue_simp" TLA.thy "([](#True)) .= #True"
   (fn _ => [ fast_tac (temp_cs addSIs [BoxTrue RS tempD]) 1 ]);

qed_goal "DmdFalse_simp" TLA.thy "(<>(#False)) .= #False"
   (fn _ => [ auto_tac (temp_css addsimps2 [dmd_def, BoxTrue_simp]) ]);

qed_goal "DmdTrue_simp" TLA.thy "(<>((#True)::temporal)) .= #True"
   (fn _ => [ fast_tac (temp_cs addSIs [ImplDmdD]) 1 ]);

qed_goal "DmdActTrue_simp" TLA.thy "(<>((#True)::action)) .= #True"
   (fn _ => [ auto_tac (temp_css addsimps2 Init_simps addSIs2 [InitDmdD]) ]);

qed_goal "BoxFalse_simp" TLA.thy "([]((#False)::temporal)) .= #False"
   (fn _ => [ fast_tac (temp_cs addSDs [STL2D]) 1 ]);

qed_goal "BoxActFalse_simp" TLA.thy "([]((#False)::action)) .= #False"
   (fn _ => [ auto_tac (temp_css addsimps2 Init_simps addSDs2 [STL2bD]) ]);

qed_goal "BoxConst_simp" TLA.thy "([]((#P)::temporal)) .= #P"
   (fn _ => [rtac tempI 1,
             case_tac "P" 1,
             auto_tac (temp_css addsimps2 [BoxTrue_simp,BoxFalse_simp])
            ]);

qed_goal "BoxActConst_simp" TLA.thy "([]((#P)::action)) .= #P"
   (fn _ => [rtac tempI 1,
             case_tac "P" 1,
             auto_tac (temp_css addsimps2 [BoxTrue_simp,BoxActFalse_simp])
            ]);

qed_goal "DmdConst_simp" TLA.thy "(<>((#P)::temporal)) .= #P"
   (fn _ => [rtac tempI 1,
             case_tac "P" 1,
             auto_tac (temp_css addsimps2 [DmdTrue_simp,DmdFalse_simp])
            ]);

qed_goal "DmdActConst_simp" TLA.thy "(<>((#P)::action)) .= #P"
   (fn _ => [rtac tempI 1,
             case_tac "P" 1,
             auto_tac (temp_css addsimps2 [DmdActTrue_simp,DmdFalse_simp])
            ]);

val temp_simps = map temp_rewrite
                  [BoxTrue_simp,DmdFalse_simp,DmdTrue_simp,
		   DmdActTrue_simp, BoxFalse_simp, BoxActFalse_simp,
		   BoxConst_simp,BoxActConst_simp,DmdConst_simp,DmdActConst_simp];

(* Make these rewrites active by default *)
Addsimps temp_simps;
val temp_css = temp_css addsimps2 temp_simps;
val temp_cs = temp_cs addss (empty_ss addsimps temp_simps);


(* ------------------------ Further rewrites ----------------------------------------- *)
section "Further rewrites";

qed_goalw "NotBox" TLA.thy [dmd_def] "(.~[]F) .= (<>.~F)"
   (fn _ => [ Auto_tac ]);

qed_goalw "NotDmd" TLA.thy [dmd_def] "(.~<>F) .= ([].~F)"
   (fn _ => [ Auto_tac ]);

(* These are not by default included in temp_css, because they could be harmful,
   e.g. []F .& .~[]F becomes []F .& <>.~F !! *)
val more_temp_simps =  (map temp_rewrite [STL3, DmdDmd, NotBox, NotDmd])
                       @ (map (fn th => (temp_unlift th) RS eq_reflection)
		         [NotBox, NotDmd]);

qed_goal "BoxDmdBox" TLA.thy "([]<>[]F) .= (<>[]F)"
   (fn _ => [ auto_tac (temp_css addSDs2 [STL2D]),
              rtac ccontr 1,
              subgoal_tac "sigma |= <>[][]F .& <>[].~[]F" 1,
              etac thin_rl 1,
              Auto_tac,
	      etac (temp_conjimpE STL6) 1, atac 1,
	      Asm_full_simp_tac 1,
	      ALLGOALS (asm_full_simp_tac (simpset() addsimps more_temp_simps))
	    ]);

qed_goalw "DmdBoxDmd" TLA.thy [dmd_def] "(<>[]<>F) .= ([]<>F)"
  (fn _ => [auto_tac (temp_css addsimps2 [temp_rewrite (rewrite_rule [dmd_def] BoxDmdBox)])]);

val more_temp_simps = more_temp_simps @ (map temp_rewrite [BoxDmdBox, DmdBoxDmd]);


(* ------------------------ Miscellaneous ----------------------------------- *)

qed_goal "BoxOr" TLA.thy 
   "!!sigma. [| (sigma |= []F .| []G) |] ==> (sigma |= [](F .| G))"
   (fn _ => [ fast_tac (temp_cs addSEs [STL4E]) 1 ]);

qed_goal "DBImplBD" TLA.thy "<>[](F::temporal) .-> []<>F"
  (fn _ => [Auto_tac,
	    rtac ccontr 1,
	    old_auto_tac (temp_css addsimps2 more_temp_simps 
			           addEs2 [temp_conjimpE STL6])
	   ]);

(* Although the script is the same, the derivation isn't polymorphic and doesn't
   work for other types of formulas (uses STL2).
*)
qed_goal "DBImplBDAct" TLA.thy "<>[](A::action) .-> []<>A"
  (fn _ => [Auto_tac,
	    rtac ccontr 1,
	    old_auto_tac (temp_css addsimps2 more_temp_simps addEs2 [temp_conjimpE STL6])
	   ]);

qed_goal "BoxDmdDmdBox" TLA.thy
   "!!sigma. [| (sigma |= []<>F); (sigma |= <>[]G) |] ==> (sigma |= []<>(F .& G))"
   (fn _ => [rtac ccontr 1,
	     rewrite_goals_tac more_temp_simps,
	     etac (temp_conjimpE STL6) 1, atac 1,
	     subgoal_tac "sigma |= <>[].~F" 1,
	     SELECT_GOAL (auto_tac (temp_css addsimps2 [dmd_def])) 1,
	     fast_tac (temp_cs addEs [DmdImplE,STL4E]) 1
	    ]);


(* ------------------------------------------------------------------------- *)
(***          TLA-specific theorems: primed formulas                       ***)
(* ------------------------------------------------------------------------- *)
section "priming";

(* ------------------------ TLA2 ------------------------------------------- *)
qed_goal "STL2bD_pr" TLA.thy
  "!!sigma. (sigma |= []P) ==> (sigma |= Init(P .& P`))"
  (fn _ => [rewrite_goals_tac Init_simps,
	    fast_tac (temp_cs addSIs [temp_mp primeI, STL2bD]) 1]);

(* Auxiliary lemma allows priming of boxed actions *)
qed_goal "BoxPrime" TLA.thy "[]P .-> [](P .& P`)"
  (fn _ => [Auto_tac,
	    etac dup_boxE 1,
	    auto_tac (temp_css addsimps2 [boxact_def]
		               addSIs2 [STL2bD_pr] addSEs2 [STL4E])
	   ]);

qed_goal "TLA2" TLA.thy "P .& P` .-> Q  ==>  []P .-> []Q"
  (fn prems => [fast_tac (temp_cs addSIs prems addDs [temp_mp BoxPrime] addEs [STL4E]) 1]);

qed_goal "TLA2E" TLA.thy 
   "[| (sigma |= []P); P .& P` .-> Q |] ==> (sigma |= []Q)"
   (fn prems => [REPEAT (resolve_tac (prems @ (prems RL [temp_mp TLA2])) 1)]);

qed_goalw "DmdPrime" TLA.thy [dmd_def] "(<>P`) .-> (<>P)"
   (fn _ => [ fast_tac (temp_cs addSEs [TLA2E]) 1 ]);


(* ------------------------ INV1, stable --------------------------------------- *)
section "stable, invariant";

qed_goal "ind_rule" TLA.thy
   "[| (sigma |= []H); (sigma |= Init(P)); H .-> (Init(P) .& .~[]F .-> Init(P`) .& F) |] \
\   ==> (sigma |= []F)"
   (fn prems => [rtac ((temp_mp indT) RS mp) 1,
		 REPEAT (resolve_tac (prems @ (prems RL [STL4E])) 1)]);
		 

qed_goalw "INV1" TLA.thy [stable_def,boxact_def] 
  "Init(P) .& stable(P) .-> []P"
  (fn _ => [auto_tac (temp_css addsimps2 Init_simps addEs2 [ind_rule])]);
bind_thm("INV1I", temp_conjmp INV1);

qed_goalw "StableL" TLA.thy [stable_def]
   "(P .& A .-> P`) ==> ([]A .-> stable(P))"
   (fn [prem] => [fast_tac (temp_cs addSIs [action_mp prem] addSEs [STL4E]) 1]);

qed_goal "Stable" TLA.thy
   "[| (sigma |= []A); P .& A .-> P` |] ==> (sigma |= stable P)"
   (fn prems => [ REPEAT (resolve_tac (prems @ [temp_mp StableL]) 1) ]);

(* Generalization of INV1 *)
qed_goalw "StableBox" TLA.thy [stable_def]
   "!!sigma. (sigma |= stable P) ==> (sigma |= [](Init P .-> []P))"
   (fn _ => [etac dup_boxE 1,
	     auto_tac (temp_css addsimps2 [stable_def] addEs2 [STL4E, INV1I])
	    ]);
     
(* useful for WF2 / SF2 *)
qed_goal "DmdStable" TLA.thy 
   "!!sigma. [| (sigma |= stable P); (sigma |= <>P) |] ==> (sigma |= <>[]P)"
   (fn _ => [rtac DmdImpl2 1,
	     etac StableBox 2,
	     auto_tac (temp_css addsimps2 [DmdAct])
	    ]);

(* ---------------- (Semi-)automatic invariant tactics ---------------------- *)

(* inv_tac reduces goals of the form ... ==> sigma |= []P *)
fun inv_tac css =
   SELECT_GOAL
     (EVERY [auto_tac css,
             TRY (merge_box_tac 1),
             rtac INV1I 1, (* fail if the goal is not a box *)
             TRYALL (etac Stable)]);

(* auto_inv_tac applies inv_tac and then tries to attack the subgoals;
   in simple cases it may be able to handle goals like MyProg .-> []Inv.
   In these simple cases the simplifier seems to be more useful than the
   auto-tactic, which applies too much propositional logic and simplifies
   too late.
*)

fun auto_inv_tac ss =
  SELECT_GOAL
    ((inv_tac (claset(),ss) 1) THEN
     (TRYALL (action_simp_tac (ss addsimps [Init_def,square_def]) [] [])));


qed_goalw "unless" TLA.thy [dmd_def]
   "!!sigma. (sigma |= [](P .-> P` .| Q`)) ==> (sigma |= stable P .| <>Q`)"
   (fn _ => [action_simp_tac (simpset()) [disjCI] [] 1,
	     merge_box_tac 1,
	     fast_tac (temp_cs addSEs [Stable]) 1
	    ]);


(* --------------------- Recursive expansions --------------------------------------- *)
section "recursive expansions";

(* Recursive expansions of [] and <>, restricted to state predicates to avoid looping *)
qed_goal "BoxRec" TLA.thy "([]$P) .= (Init($P) .& ([]P$))"
   (fn _ => [auto_tac (temp_css addSIs2 [STL2bD]),
	     fast_tac (temp_cs addSEs [TLA2E]) 1,
	     auto_tac (temp_css addsimps2 [stable_def] addSEs2 [INV1I,STL4E])
	    ]);

qed_goalw "DmdRec" TLA.thy [dmd_def] "(<>$P) .= (Init($P) .| (<>P$))"
   (fn _ => [Auto_tac,
	     etac notE 1,
	     SELECT_GOAL (auto_tac (temp_css addsimps2 (stable_def::Init_simps)
				             addIs2 [INV1I] addEs2 [STL4E])) 1,
	     SELECT_GOAL (auto_tac (temp_css addsimps2 Init_simps addSDs2 [STL2bD])) 1,
	     fast_tac (temp_cs addSEs [notE,TLA2E]) 1
	    ]);

qed_goal "DmdRec2" TLA.thy
   "!!sigma. [| (sigma |= <>($P)); (sigma |= [](.~P$)) |] ==> (sigma |= Init($P))"
   (fn _ => [dtac ((temp_unlift DmdRec) RS iffD1) 1,
	     SELECT_GOAL (auto_tac (temp_css addsimps2 [dmd_def])) 1
	    ]);

(* The "=>" part of the following is a little intricate. *)
qed_goal "InfinitePrime" TLA.thy "([]<>$P) .= ([]<>P$)"
   (fn _ => [Auto_tac,
	     rtac classical 1,
	     rtac (temp_mp DBImplBDAct) 1,
	     subgoal_tac "sigma |= <>[]$P" 1,
	     fast_tac (temp_cs addSEs [DmdImplE,TLA2E]) 1,
	     subgoal_tac "sigma |= <>[](<>$P .& [].~P$)" 1,
	     SELECT_GOAL (auto_tac (temp_css addsimps2 [boxact_def]
				             addSEs2 [DmdImplE,STL4E,DmdRec2])) 1,
	     SELECT_GOAL (auto_tac (temp_css addSIs2 [temp_mp STL6] addsimps2 more_temp_simps)) 1,
	     fast_tac (temp_cs addIs [temp_mp DmdPrime] addSEs [STL4E]) 1
	    ]);

(* ------------------------ fairness ------------------------------------------- *)
section "fairness";

(* alternative definitions of fairness *)
qed_goalw "WF_alt" TLA.thy [WF_def,dmd_def] 
   "WF(A)_v .= (([]<>.~$(Enabled(<A>_v))) .| []<><A>_v)"
   (fn _ => [ fast_tac temp_cs 1 ]);

qed_goalw "SF_alt" TLA.thy [SF_def,dmd_def]
   "SF(A)_v .= ((<>[].~$(Enabled(<A>_v))) .| []<><A>_v)"
   (fn _ => [ fast_tac temp_cs 1 ]);

(* theorems to "box" fairness conditions *)
qed_goal "BoxWFI" TLA.thy
   "!!sigma. (sigma |= WF(A)_v) ==> (sigma |= []WF(A)_v)"
   (fn _ => [ auto_tac (temp_css addsimps2 (temp_rewrite WF_alt::more_temp_simps) addSIs2 [BoxOr]) ]);

qed_goal "WF_Box" TLA.thy "([]WF(A)_v) .= WF(A)_v"
  (fn prems => [ fast_tac (temp_cs addSIs [BoxWFI] addSDs [STL2D]) 1 ]);

qed_goal "BoxSFI" TLA.thy
   "!!sigma. (sigma |= SF(A)_v) ==> (sigma |= []SF(A)_v)"
   (fn _ => [ auto_tac (temp_css addsimps2 (temp_rewrite SF_alt::more_temp_simps) addSIs2 [BoxOr]) ]);

qed_goal "SF_Box" TLA.thy "([]SF(A)_v) .= SF(A)_v"
  (fn prems => [ fast_tac (temp_cs addSIs [BoxSFI] addSDs [STL2D]) 1 ]);

val more_temp_simps = more_temp_simps @ (map temp_rewrite [WF_Box, SF_Box]);

qed_goalw "SFImplWF" TLA.thy [SF_def,WF_def]
  "!!sigma. (sigma |= SF(A)_v) ==> (sigma |= WF(A)_v)"
  (fn _ => [ fast_tac (temp_cs addSDs [temp_mp DBImplBDAct]) 1 ]);

(* A tactic that "boxes" all fairness conditions. Apply more_temp_simps to "unbox". *)
val box_fair_tac = SELECT_GOAL (REPEAT (dresolve_tac [BoxWFI,BoxSFI] 1));


(* ------------------------------ leads-to ------------------------------ *)

section "~>";

qed_goalw "leadsto_init" TLA.thy [leadsto]
   "!!sigma. [| (sigma |= Init P); (sigma |= P ~> Q) |] ==> (sigma |= <>Q)"
   (fn _ => [ fast_tac (temp_cs addSDs [temp_mp STL2]) 1 ]);

qed_goalw "streett_leadsto" TLA.thy [leadsto]
   "([]<>P .-> []<>Q) .= (<>(P ~> Q))"
   (fn _ => [Auto_tac,
             asm_full_simp_tac (simpset() addsimps boxact_def::more_temp_simps) 1,
             SELECT_GOAL (auto_tac (temp_css addSEs2 [DmdImplE,STL4E] 
                                             addsimps2 Init_simps)) 1,
             SELECT_GOAL (auto_tac (temp_css addSIs2 [ImplDmdD] addSEs2 [STL4E])) 1,
             subgoal_tac "sigma |= []<><>Q" 1,
             asm_full_simp_tac (simpset() addsimps more_temp_simps) 1,
             rewtac (temp_rewrite DmdAct),
             dtac BoxDmdDmdBox 1, atac 1,
             auto_tac (temp_css addSEs2 [DmdImplE,STL4E])
            ]);

qed_goal "leadsto_infinite" TLA.thy
   "!!sigma. [| (sigma |= []<>P); (sigma |= P ~> Q) |] ==> (sigma |= []<>Q)"
   (fn _ => [rtac ((temp_unlift streett_leadsto) RS iffD2 RS mp) 1,
             auto_tac (temp_css addSIs2 [ImplDmdD])
            ]);

(* In particular, strong fairness is a Streett condition. The following
   rules are sometimes easier to use than WF2 or SF2 below.
*)
qed_goalw "leadsto_SF" TLA.thy [SF_def]
  "!!sigma. (sigma |= $(Enabled(<A>_v)) ~> <A>_v) ==> sigma |= SF(A)_v"
  (fn _ => [step_tac temp_cs 1,
            rtac leadsto_infinite 1,
            ALLGOALS atac
           ]);

bind_thm("leadsto_WF", leadsto_SF RS SFImplWF);

(* introduce an invariant into the proof of a leadsto assertion.
   []I => ((P ~> Q)  =  (P /\ I ~> Q))
*)
qed_goalw "INV_leadsto" TLA.thy [leadsto]
   "!!sigma. [| (sigma |= []I); (sigma |= (P .& I) ~> Q) |] ==> (sigma |= P ~> Q)"
   (fn _ => [etac STL4Edup 1, atac 1,
	     auto_tac (temp_css addsimps2 [Init_def] addSDs2 [STL2bD])
	    ]);

qed_goalw "leadsto_classical" TLA.thy [leadsto,dmd_def]
   "!!sigma. (sigma |= [](Init P .& [].~Q .-> <>Q)) ==> (sigma |= P ~> Q)"
   (fn _ => [fast_tac (temp_cs addSEs [STL4E]) 1]);

qed_goalw "leadsto_false" TLA.thy [leadsto]
  "(P ~> #False) .= ([] .~P)"
  (fn _ => [ auto_tac (temp_css addsimps2 boxact_def::Init_simps) ]);

(* basic leadsto properties, cf. Unity *)

qed_goal "ImplLeadsto" TLA.thy
   "!!sigma. (sigma |= [](P .-> Q)) ==> (sigma |= (P ~> Q))"
   (fn _ => [etac INV_leadsto 1, rewtac leadsto,
	     rtac (temp_unlift necT) 1,
	     auto_tac (temp_css addSIs2 [InitDmdD] addsimps2 [Init_def])
	    ]);

qed_goal "EnsuresLeadsto" TLA.thy
   "A .& P .-> Q` ==> []A .-> (P ~> Q)"
   (fn [prem] => [auto_tac (temp_css addSEs2 [INV_leadsto]),
		  rewtac leadsto,
 		  auto_tac (temp_css addSIs2 [temp_unlift necT]),
		  rtac (temp_mp DmdPrime) 1, rtac InitDmdD 1,
		  auto_tac (action_css addsimps2 [Init_def] addSIs2 [action_mp prem])
		 ]);

qed_goalw "EnsuresLeadsto2" TLA.thy [leadsto]
   "!!sigma. sigma |= [](P .-> Q`) ==> sigma |= P ~> Q"
   (fn _ => [subgoal_tac "sigma |= []Init(P .-> Q`)" 1,
             etac STL4E 1,
             auto_tac (temp_css addsimps2 boxact_def::Init_simps 
                                addIs2 [(temp_mp InitDmd) RS (temp_mp DmdPrime)])
            ]);
             
qed_goal "EnsuresInfinite" TLA.thy
   "[| (sigma |= []<>P); (sigma |= []A); A .& P .-> Q` |] ==> (sigma |= []<>Q)"
   (fn prems => [REPEAT (resolve_tac (prems @ [leadsto_infinite,
					       temp_mp EnsuresLeadsto]) 1)]);

(*** Gronning's lattice rules (taken from TLP) ***)
section "Lattice rules";

qed_goalw "LatticeReflexivity" TLA.thy [leadsto] "F ~> F"
   (fn _ => [REPEAT (resolve_tac [necT,InitDmd] 1)]);

qed_goalw "LatticeTransitivity" TLA.thy [leadsto]
   "!!sigma. [| (sigma |= G ~> H); (sigma |= F ~> G) |] ==> (sigma |= F ~> H)"
   (fn _ => [etac dup_boxE 1,  (* [][](Init G .-> H) *)
	     merge_box_tac 1,
	     auto_tac (temp_css addSEs2 [STL4E]),
	     rewtac (temp_rewrite DmdAct),
	     subgoal_tac "sigmaa |= <><> Init H" 1,
	     asm_full_simp_tac (simpset() addsimps more_temp_simps) 1,
	     fast_tac (temp_cs addSEs [DmdImpl2]) 1
	    ]);

qed_goalw "LatticeDisjunctionElim1" TLA.thy [leadsto]
   "!!sigma. (sigma |= (F .| G) ~> H) ==> (sigma |= F ~> H)"
   (fn _ => [ auto_tac (temp_css addsimps2 [Init_def] addSEs2 [STL4E]) ]);

qed_goalw "LatticeDisjunctionElim2" TLA.thy [leadsto]
   "!!sigma. (sigma |= (F .| G) ~> H) ==> (sigma |= G ~> H)"
   (fn _ => [ auto_tac (temp_css addsimps2 [Init_def] addSEs2 [STL4E]) ]);

qed_goalw "LatticeDisjunctionIntro" TLA.thy [leadsto]
   "!!sigma. [| (sigma |= F ~> H); (sigma |= G ~> H) |] ==> (sigma |= (F .| G) ~> H)"
   (fn _ => [merge_box_tac 1,
	     auto_tac (temp_css addsimps2 [Init_def] addSEs2 [STL4E])
	    ]);

qed_goal "LatticeDiamond" TLA.thy
   "!!sigma. [| (sigma |= B ~> D); (sigma |= A ~> (B .| C)); (sigma |= C ~> D) |]  \
\            ==> (sigma |= A ~> D)"
   (fn _ => [subgoal_tac "sigma |= (B .| C) ~> D" 1,
	     eres_inst_tac [("G", "B .| C")] LatticeTransitivity 1,
	     ALLGOALS (fast_tac (temp_cs addSIs [LatticeDisjunctionIntro]))
	    ]);

qed_goal "LatticeTriangle" TLA.thy
   "!!sigma. [| (sigma |= B ~> D); (sigma |= A ~> (B .| D)) |] ==> (sigma |= A ~> D)"
   (fn _ => [subgoal_tac "sigma |= (B .| D) ~> D" 1,
	     eres_inst_tac [("G", "B .| D")] LatticeTransitivity 1, atac 1,
	     auto_tac (temp_css addSIs2 [LatticeDisjunctionIntro] addIs2 [ImplLeadsto])
	    ]);

(*** Lamport's fairness rules ***)
section "Fairness rules";

qed_goalw "WF1" TLA.thy [leadsto]
   "[| P .& N  .-> P` .| Q`;   \
\      P .& N .& <A>_v .-> Q`;   \
\      P .& N .-> $(Enabled(<A>_v)) |]   \
\  ==> []N .& WF(A)_v .-> (P ~> Q)"
   (fn [prem1,prem2,prem3]
	 => [auto_tac (temp_css addSDs2 [BoxWFI]),
	     etac STL4Edup 1, atac 1,
	     Auto_tac,
	     subgoal_tac "sigmaa |= [](P .-> P` .| Q`)" 1,
	     auto_tac (temp_css addSDs2 [unless]),
	     etac (temp_conjimpE INV1) 1, atac 1,
	     merge_box_tac 1,
	     rtac STL2D 1,
	     rtac EnsuresInfinite 1, atac 2,
	     SELECT_GOAL (old_auto_tac (temp_css addsimps2 [WF_alt])) 1,
	     atac 2,
	     subgoal_tac "sigmaa |= [][]$(Enabled(<A>_v))" 1,
	     merge_box_tac 1,
	     SELECT_GOAL (auto_tac (temp_css addsimps2 [dmd_def])) 1,
	     SELECT_GOAL ((rewtac (temp_rewrite STL3)) THEN
			  (auto_tac (temp_css addSEs2 [STL4E] addSIs2 [action_mp prem3]))) 1,
	     fast_tac (action_cs addSIs [action_mp prem2]) 1,
	     fast_tac (temp_cs addIs [temp_mp DmdPrime]) 1,
	     fast_tac (temp_cs addSEs [STL4E] addSIs [action_mp prem1]) 1
	    ]);

(* Sometimes easier to use; designed for action B rather than state predicate Q *)
qed_goalw "WF_leadsto" TLA.thy [leadsto]
   "[| N .& P .-> $Enabled (<A>_v);            \
\      N .& <A>_v .-> B;                  \ 
\      [](N .& [.~A]_v) .-> stable P  |]  \
\   ==> []N .& WF(A)_v .-> (P ~> B)"
   (fn [prem1,prem2,prem3]
       => [auto_tac (temp_css addSDs2 [BoxWFI]),
           etac STL4Edup 1, atac 1,
           Auto_tac,
           subgoal_tac "sigmaa |= <><A>_v" 1,
           SELECT_GOAL (auto_tac (temp_css addSEs2 [DmdImpl2,STL4E] addSIs2 [action_mp prem2])) 1,
           rtac classical 1,
           rtac STL2D 1,
           auto_tac (temp_css addsimps2 WF_def::more_temp_simps addSEs2 [mp]),
           rtac ImplDmdD 1,
           rtac (temp_mp (prem1 RS STL4)) 1,
           auto_tac (temp_css addsimps2 [split_box_conj]),
           etac INV1I 1,
           merge_act_box_tac 1,
           auto_tac (temp_css addsimps2 [temp_rewrite not_angle] addSEs2 [temp_mp prem3])
          ]);

qed_goalw "SF1" TLA.thy [leadsto]
   "[| P .& N  .-> P` .| Q`;   \
\      P .& N .& <A>_v .-> Q`;   \
\      []P .& []N .& []F .-> <>$(Enabled(<A>_v)) |]   \
\  ==> []N .& SF(A)_v .& []F .-> (P ~> Q)"
   (fn [prem1,prem2,prem3] =>
                [auto_tac (temp_css addSDs2 [BoxSFI]),
		 eres_inst_tac [("F","F")] dup_boxE 1,
		 merge_temp_box_tac 1,
		 etac STL4Edup 1, atac 1,
		 Auto_tac,
		 subgoal_tac "sigmaa |= [](P .-> P` .| Q`)" 1,
		 auto_tac (temp_css addSDs2 [unless]),
		 etac (temp_conjimpE INV1) 1, atac 1,
		 merge_act_box_tac 1,
		 rtac STL2D 1,
		 rtac EnsuresInfinite 1, atac 2,
		 SELECT_GOAL (old_auto_tac (temp_css addsimps2 [SF_alt])) 1,
		 atac 2,
		 subgoal_tac "sigmaa |= []<>$(Enabled(<A>_v))" 1,
		 SELECT_GOAL (auto_tac (temp_css addsimps2 [dmd_def])) 1,
		 eres_inst_tac [("F","F")] dup_boxE 1,
		 etac STL4Edup 1, atac 1,
		 fast_tac (temp_cs addSEs [STL4E] addSIs [temp_mp prem3]) 1,
		 fast_tac (action_cs addSIs [action_mp prem2]) 1,
		 fast_tac (temp_cs addIs [temp_mp DmdPrime]) 1,
		 fast_tac (temp_cs addSEs [STL4E] addSIs [action_mp prem1]) 1
		]);

qed_goal "WF2" TLA.thy
   "[| N .& <B>_f .-> <M>_g;   \
\      P .& P` .& <N .& A>_f .-> B;   \
\      P .& $(Enabled(<M>_g)) .-> $(Enabled(<A>_f));   \
\      [](N .& [.~B]_f) .& WF(A)_f .& []F .& <>[]($(Enabled(<M>_g))) .-> <>[]P |]   \
\  ==> []N .& WF(A)_f .& []F .-> WF(M)_g"
   (fn [prem1,prem2,prem3,prem4]
       => [Auto_tac,
	   case_tac "sigma |= <>[]$Enabled(<M>_g)" 1,
	   SELECT_GOAL (auto_tac (temp_css addsimps2 [WF_def,dmd_def])) 2,
	   case_tac "sigma |= <>[][.~B]_f" 1,
	   subgoal_tac "sigma |= <>[]P" 1,
	   asm_full_simp_tac (simpset() addsimps [WF_def]) 1,
	   rtac (temp_mp (prem1 RS DmdImpl RS STL4)) 1,
	   eres_inst_tac [("V","sigma |= <>[][.~B]_f")] thin_rl 1,
	   etac (temp_conjimpE STL6) 1, atac 1,
	   subgoal_tac "sigma |= <>[]$Enabled(<A>_f)" 1,
	   dtac mp 1, atac 1,
	   subgoal_tac "sigma |= <>([]N .& []P .& []<><A>_f)" 1,
	   rtac ((temp_unlift DmdBoxDmd) RS iffD1) 1,
	   eres_inst_tac [("F","[]N .& []P .& []<><A>_f")] DmdImplE 1,
	   SELECT_GOAL Auto_tac 1,
	   dres_inst_tac [("P","P")] (temp_mp BoxPrime) 1,
	   merge_act_box_tac 1,
	   etac InfImpl 1, atac 1,
	   SELECT_GOAL (auto_tac (temp_css addsimps2 [angle_def] addSIs2 [action_mp prem2])) 1,
	   etac BoxDmd 1,
	   dres_inst_tac [("F","<><A>_f"),("G","[]P")] BoxDmd 1, atac 1,
	   eres_inst_tac [("F","[]<><A>_f .& []P")] DmdImplE 1,
	   SELECT_GOAL Auto_tac 1,
	   rtac (temp_mp (prem3 RS STL4 RS DmdImpl)) 1,
	   fast_tac (temp_cs addIs [STL4E,DmdImplE]) 1,
	   etac (temp_conjimpE STL6) 1, atac 1,
	   eres_inst_tac [("V","sigma |= <>[][.~ B]_f")] thin_rl 1,
	   dtac BoxWFI 1,
	   eres_inst_tac [("F","N")] dup_boxE 1,
	   eres_inst_tac [("F","F")] dup_boxE 1,
	   merge_temp_box_tac 1,
	   dtac BoxDmd 1, atac 1,
	   eres_inst_tac [("V","sigma |= <>[]($Enabled (<M>_g) .& [.~ B]_f)")] thin_rl 1,
	   rtac dup_dmdD 1,
	   rtac (temp_mp (prem4 RS DmdImpl)) 1,
	   etac DmdImplE 1,
	   SELECT_GOAL
	     (auto_tac (temp_css addsimps2 [symmetric(temp_rewrite STL5), temp_rewrite STL3]
		                 addIs2 [(temp_unlift WF_Box) RS iffD1, temp_mp ImplDmd])) 1,
	   asm_full_simp_tac (simpset() addsimps (WF_def::more_temp_simps)) 1,
	   etac InfImpl 1, atac 1,
	   SELECT_GOAL (auto_tac (temp_css addSIs2 [action_mp prem1])) 1,
	   ALLGOALS (asm_full_simp_tac (simpset() addsimps [square_def,angle_def]))
	  ]);

qed_goal "SF2" TLA.thy
   "[| N .& <B>_f .-> <M>_g;   \
\      P .& P` .& <N .& A>_f .-> B;   \
\      P .& $(Enabled(<M>_g)) .-> $(Enabled(<A>_f));   \
\      [](N .& [.~B]_f) .& SF(A)_f .& []F .& []<>($(Enabled(<M>_g))) .-> <>[]P |]   \
\  ==> []N .& SF(A)_f .& []F .-> SF(M)_g"
   (fn [prem1,prem2,prem3,prem4]
       => [Auto_tac,
	   case_tac "sigma |= []<>$Enabled(<M>_g)" 1,
	   SELECT_GOAL (auto_tac (temp_css addsimps2 [SF_def,dmd_def])) 2,
	   case_tac "sigma |= <>[][.~B]_f" 1,
	   subgoal_tac "sigma |= <>[]P" 1,
	   asm_full_simp_tac (simpset() addsimps [SF_def]) 1,
	   rtac (temp_mp (prem1 RS DmdImpl RS STL4)) 1,
	   eres_inst_tac [("V","sigma |= <>[][.~B]_f")] thin_rl 1,
	   dtac BoxDmdDmdBox 1, atac 1,
	   subgoal_tac "sigma |= []<>$Enabled(<A>_f)" 1,
	   dtac mp 1, atac 1,
	   subgoal_tac "sigma |= <>([]N .& []P .& []<><A>_f)" 1,
	   rtac ((temp_unlift DmdBoxDmd) RS iffD1) 1,
	   eres_inst_tac [("F","[]N .& []P .& []<><A>_f")] DmdImplE 1,
	   SELECT_GOAL Auto_tac 1,
	   dres_inst_tac [("P","P")] (temp_mp BoxPrime) 1,
	   merge_act_box_tac 1,
	   etac InfImpl 1, atac 1,
	   SELECT_GOAL (auto_tac (temp_css addsimps2 [angle_def] addSIs2 [action_mp prem2])) 1,
	   etac BoxDmd 1,
	   dres_inst_tac [("F","<><A>_f"),("G","[]P")] BoxDmd 1, atac 1,
	   eres_inst_tac [("F","[]<><A>_f .& []P")] DmdImplE 1,
	   SELECT_GOAL Auto_tac 1,
	   rtac (temp_mp (prem3 RS DmdImpl RS STL4)) 1,
	   fast_tac (temp_cs addEs [STL4E,DmdImplE]) 1,
	   dtac BoxSFI 1,
	   eres_inst_tac [("F","N")] dup_boxE 1,
	   eres_inst_tac [("F","F")] dup_boxE 1,
	   eres_inst_tac [("F","<>$Enabled (<M>_g)")] dup_boxE 1,
	   merge_temp_box_tac 1,
	   dtac (temp_conjmp BoxDmdT2) 1, atac 1,
	   rtac dup_dmdD 1,
	   rtac (temp_mp (prem4 RS DmdImpl)) 1,
	   SELECT_GOAL
	     (auto_tac (temp_css addsimps2 [symmetric(temp_rewrite STL5), temp_rewrite STL3]
		                 addIs2 [(temp_unlift WF_Box) RS iffD1, temp_mp ImplDmd]
			         addSEs2 [DmdImplE])) 1,
	   asm_full_simp_tac (simpset() addsimps (SF_def::more_temp_simps)) 1,
	   eres_inst_tac [("F",".~ [.~ B]_f")] InfImpl 1, atac 1,
	   SELECT_GOAL (auto_tac (temp_css addSIs2 [action_mp prem1])) 1,
	   ALLGOALS (asm_full_simp_tac (simpset() addsimps [square_def,angle_def]))
	  ]);

(* ------------------------------------------------------------------------- *)
(***           Liveness proofs by well-founded orderings                   ***)
(* ------------------------------------------------------------------------- *)
section "Well-founded orderings";

qed_goal "wf_dmd" TLA.thy
  "[| (wf r);  \
\     !!x. sigma |= [](F x .-> <>G .| <>(REX y. #((y,x):r) .& F y))   \
\  |] ==> sigma |= [](F x .-> <>G)"
  (fn prem1::prems => 
         [cut_facts_tac [prem1] 1,
          etac wf_induct 1,
          subgoal_tac "sigma |= []((REX y. #((y,x):r) .& F y) .-> <>G)" 1,
	  cut_facts_tac prems 1,
	  etac STL4Edup 1, atac 1,
	  Auto_tac, etac swap 1, atac 1,
	  rtac dup_dmdD 1,
	  etac DmdImpl2 1, atac 1,
	  subgoal_tac "sigma |= [](RALL y. #((y,x):r) .& F y .-> <>G)" 1,
	  fast_tac (temp_cs addSEs [STL4E]) 1,
	  auto_tac (temp_css addsimps2 [all_box]),
	  etac allE 1, etac impCE 1,
	  rtac (temp_unlift necT) 1,
	  auto_tac (temp_css addSEs2 [STL4E])
         ]);

(* Special case: leadsto via well-foundedness *)
qed_goalw "wf_leadsto" TLA.thy [leadsto]
  "[| (wf r);  \
\     !!x. sigma |= P x ~> (Q .| (REX y. #((y,x):r) .& P y))   \
\  |] ==> sigma |= P x ~> Q"
  (fn prems => [REPEAT (resolve_tac (wf_dmd::prems) 1),
		resolve_tac (prems RL [STL4E]) 1,
		auto_tac (temp_css addsimps2 [temp_rewrite DmdOr]),
                fast_tac temp_cs 1,
		etac swap 1,
		rewtac (temp_rewrite DmdAct),
		auto_tac (temp_css addsimps2 [Init_def] addSEs2 [DmdImplE])
	       ]);

(* If r is well-founded, state function v cannot decrease forever *)
qed_goal "wf_not_box_decrease" TLA.thy
  "!!r. wf r ==> [][ {[v$, $v]} .: #r ]_v .-> <>[][#False]_v"
  (fn _ => [Auto_tac,
            subgoal_tac "ALL x. (sigma |= [](Init($v .= #x) .-> <>[][#False]_v))" 1,
            etac allE 1,
            dtac STL2D 1,
            auto_tac (temp_css addsimps2 [Init_def]),
            etac wf_dmd 1,
            etac dup_boxE 1,
            etac STL4E 1,
            action_simp_tac (simpset() addsimps [con_abs]) [tempI] [] 1,
            case_tac "sigma |= <>[][#False]_v" 1,
            ALLGOALS Asm_full_simp_tac,
            rewrite_goals_tac more_temp_simps,
            dtac STL2D 1,
            subgoal_tac "sigma |= <>(REX y. #((y, xa) : r) .& ($v .= #y))" 1,
            SELECT_GOAL (auto_tac (temp_css addsimps2 [DmdAct,Init_def] 
                                            addEs2 [DmdImplE])) 1,
            subgoal_tac "sigma |= (stable ($v .= #xa) .| <>(REX y. #((y, xa) : r) .& $v .= #y)`)" 1,
            case_tac "sigma |= stable ($v .= #xa)" 1,
            SELECT_GOAL (auto_tac (temp_css addIs2 [temp_mp DmdPrime])) 2,
            SELECT_GOAL (rewrite_goals_tac ((symmetric (temp_rewrite NotBox))::action_rews)) 1,
            etac swap 1,
            subgoal_tac "sigma |= []($v .= #xa)" 1,
            dres_inst_tac [("P", "$v .= #xa")] (temp_mp BoxPrime) 1,
            SELECT_GOAL (auto_tac (temp_css addEs2 [STL4E] addsimps2 [square_def])) 1,
            SELECT_GOAL (auto_tac (temp_css addSIs2 [INV1I] addsimps2 [Init_def])) 1,
            old_auto_tac (temp_css addsimps2 [square_def] addSIs2 [unless] addSEs2 [STL4E])
           ]);

(* "wf ?r  ==>  <>[][{[?v$, $?v]} .: #?r]_?v .-> <>[][#False]_?v" *)
bind_thm("wf_not_dmd_box_decrease",
         standard(rewrite_rule more_temp_simps (wf_not_box_decrease RS DmdImpl)));

(* If there are infinitely many steps where v decreases w.r.t. r, then there
   have to be infinitely many non-stuttering steps where v doesn't decrease.
*)
qed_goal "wf_box_dmd_decrease" TLA.thy
  "wf r ==> []<>({[v$, $v]} .: #r) .-> []<><.~({[v$, $v]} .: #r)>_v"
  (fn [prem] => [Auto_tac,
                 rtac ccontr 1,
                 asm_full_simp_tac 
                   (simpset() addsimps ([action_rewrite not_angle] @ more_temp_simps)) 1,
                 dtac (prem RS (temp_mp wf_not_dmd_box_decrease)) 1,
                 dtac BoxDmdDmdBox 1, atac 1,
                 subgoal_tac "sigma |= []<>((#False)::action)" 1,
                 SELECT_GOAL Auto_tac 1,
                 etac STL4E 1,
                 rtac DmdImpl 1,
                 auto_tac (action_css addsimps2 [square_def] addSEs2 [prem RS wf_irrefl])
                ]);

(* In particular, for natural numbers, if n decreases infinitely often
   then it has to increase infinitely often.
*)
qed_goal "nat_box_dmd_decrease" TLA.thy
  "!!n::nat stfun. []<>(n$ .< $n) .-> []<>($n .< n$)"
  (fn _ => [Auto_tac,
            subgoal_tac "sigma |= []<><.~( {[n$,$n]} .: #less_than)>_n" 1,
            etac thin_rl 1, etac STL4E 1, rtac DmdImpl 1,
            SELECT_GOAL (auto_tac (claset(), simpset() addsimps [angle_def])) 1,
            rtac nat_less_cases 1,
            Auto_tac,
            rtac (temp_mp wf_box_dmd_decrease) 1,
            auto_tac (claset() addSEs [STL4E] addSIs [DmdImpl], simpset())
           ]);

(* ------------------------------------------------------------------------- *)
(***           Flexible quantification over state variables                ***)
(* ------------------------------------------------------------------------- *)
section "Flexible quantification";

qed_goal "aallI" TLA.thy 
  "(!!x. base_var x ==> sigma |= F x) ==> sigma |= (AALL x. F(x))"
  (fn prems => [auto_tac (temp_css addsimps2 [aall_def] addSEs2 [eexE] addSDs2 prems)]);

qed_goal "aallE" TLA.thy
   "[| sigma |= (AALL x. F(x));  (!!sigma. sigma |= F(x) ==> P sigma) |] \
\   ==> (P sigma)::bool"
   (fn prems => [cut_facts_tac prems 1,
		 resolve_tac prems 1,
		 rewrite_goals_tac (aall_def::intensional_rews),
		 etac swap 1,
		 auto_tac (temp_css addSIs2 [temp_mp eexI])
		]);

(* monotonicity of quantification *)
qed_goal "eex_mono" TLA.thy
  "[| sigma |= EEX x. F(x); !!x. F(x) .-> G(x) |] ==> sigma |= EEX x. G(x)"
  (fn [min,maj] => [cut_facts_tac [min] 1,
                    etac eexE 1,
                    REPEAT (ares_tac (map temp_mp [eexI,maj]) 1)
                   ]);

qed_goal "aall_mono" TLA.thy
  "[| sigma |= AALL x. F(x); !!x. F(x) .-> G(x) |] ==> sigma |= AALL x. G(x)"
  (fn [min,maj] => [cut_facts_tac [min] 1,
                    fast_tac (temp_cs addSIs [aallI, temp_mp maj]
                                      addEs [aallE]) 1
                   ]);

(* ----------------------------------------------------------------------
   example of a history variable: existence of a clock

goal TLA.thy "(EEX h. Init($h .= #True) .& [](h$ .~= $h))";
by (rtac tempI 1);
by (rtac historyI 1);
by (rewrite_goals_tac action_rews);
by (TRYALL (rtac impI));
by (TRYALL (etac conjE));
by (assume_tac 3);
by (Asm_full_simp_tac 3);
by (auto_tac (temp_css addSIs2 [(temp_unlift Init_true) RS iffD2, temp_unlift BoxTrue]));
(** solved **)

---------------------------------------------------------------------- *)
