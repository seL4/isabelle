(* 
    File:	 TLA/TLA.ML
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

Lemmas and tactics for temporal reasoning.
*)

(* Specialize intensional introduction/elimination rules for temporal formulas *)

qed_goal "tempI" TLA.thy "(!!sigma. sigma |= (F::temporal)) ==> |- F"
  (fn [prem] => [ REPEAT (resolve_tac [prem,intI] 1) ]);

qed_goal "tempD" TLA.thy "|- (F::temporal) ==> sigma |= F"
  (fn [prem] => [ rtac (prem RS intD) 1 ]);


(* ======== Functions to "unlift" temporal theorems ====== *)

(* The following functions are specialized versions of the corresponding
   functions defined in Intensional.ML in that they introduce a
   "world" parameter of type "behavior".
*)
fun temp_unlift th = 
    (rewrite_rule action_rews (th RS tempD))
    handle _ => action_unlift th;

(* Turn  |- F = G  into meta-level rewrite rule  F == G *)
val temp_rewrite = int_rewrite;

fun temp_use th = 
    case (concl_of th) of
      Const _ $ (Const ("Intensional.Valid", _) $ _) =>
              ((flatten (temp_unlift th)) handle _ => th)
    | _ => th;

(* Update classical reasoner---will be updated once more below! *)

AddSIs [tempI];
AddDs [tempD];

val temp_css = (claset(), simpset());
val temp_cs = op addss temp_css;

(* Modify the functions that add rules to simpsets, classical sets,
   and clasimpsets in order to accept "lifted" theorems
*)

local
  fun try_rewrite th =
      (temp_rewrite th) handle _ => temp_use th
in
  val op addsimps = fn (ss, ts) => ss addsimps (map try_rewrite ts)
  val op addsimps2 = fn (css, ts) => css addsimps2 (map try_rewrite ts)
end;

val op addSIs = fn (cs, ts) => cs addSIs (map temp_use ts);
val op addSEs = fn (cs, ts) => cs addSEs (map temp_use ts);
val op addSDs = fn (cs, ts) => cs addSDs (map temp_use ts);
val op addIs = fn (cs, ts) => cs addIs (map temp_use ts);
val op addEs = fn (cs, ts) => cs addEs (map temp_use ts);
val op addDs = fn (cs, ts) => cs addDs (map temp_use ts);

val op addSIs2 = fn (css, ts) => css addSIs2 (map temp_use ts);
val op addSEs2 = fn (css, ts) => css addSEs2 (map temp_use ts);
val op addSDs2 = fn (css, ts) => css addSDs2 (map temp_use ts);
val op addIs2 = fn (css, ts) => css addIs2 (map temp_use ts);
val op addEs2 = fn (css, ts) => css addEs2 (map temp_use ts);
val op addDs2 = fn (css, ts) => css addDs2 (map temp_use ts);


(* ------------------------------------------------------------------------- *)
(***           "Simple temporal logic": only [] and <>                     ***)
(* ------------------------------------------------------------------------- *)
section "Simple temporal logic";

(* []~F == []~Init F *)
bind_thm("boxNotInit", rewrite_rule Init_simps (read_instantiate [("F", "LIFT ~F")] boxInit));

qed_goalw "dmdInit" TLA.thy [dmd_def] "TEMP <>F == TEMP <> Init F"
  (fn _ => [rewtac (read_instantiate [("F", "LIFT ~F")] boxInit),
            simp_tac (simpset() addsimps Init_simps) 1]);

bind_thm("dmdNotInit", rewrite_rule Init_simps (read_instantiate [("F", "LIFT ~F")] dmdInit));

(* boxInit and dmdInit cannot be used as rewrites, because they loop.
   Non-looping instances for state predicates and actions are occasionally useful.
*)
bind_thm("boxInit_stp", read_instantiate [("'a","state")] boxInit);
bind_thm("boxInit_act", read_instantiate [("'a","state * state")] boxInit);
bind_thm("dmdInit_stp", read_instantiate [("'a","state")] dmdInit);
bind_thm("dmdInit_act", read_instantiate [("'a","state * state")] dmdInit);

(* The symmetric equations can be used to get rid of Init *)
bind_thm("boxInitD", symmetric boxInit);
bind_thm("dmdInitD", symmetric dmdInit);
bind_thm("boxNotInitD", symmetric boxNotInit);
bind_thm("dmdNotInitD", symmetric dmdNotInit);

val Init_simps = Init_simps @ [boxInitD, dmdInitD, boxNotInitD, dmdNotInitD];

(* ------------------------ STL2 ------------------------------------------- *)
bind_thm("STL2", reflT);

(* The "polymorphic" (generic) variant *)
qed_goal "STL2_gen" TLA.thy "|- []F --> Init F"
  (fn _ => [rewtac (read_instantiate [("F", "F")] boxInit),
            rtac STL2 1]);

(* see also STL2_pr below: "|- []P --> Init P & Init (P`)" *)


(* Dual versions for <> *)
qed_goalw "InitDmd" TLA.thy [dmd_def] "|- F --> <> F"
   (fn _ => [ auto_tac (temp_css addSDs2 [STL2]) ]);

qed_goal "InitDmd_gen" TLA.thy "|- Init F --> <>F"
   (fn _ => [Clarsimp_tac 1,
             dtac (temp_use InitDmd) 1,
             asm_full_simp_tac (simpset() addsimps [dmdInitD]) 1]);


(* ------------------------ STL3 ------------------------------------------- *)
qed_goal "STL3" TLA.thy "|- ([][]F) = ([]F)"
   (K [force_tac (temp_css addEs2 [transT,STL2]) 1]);

(* corresponding elimination rule introduces double boxes: 
   [| (sigma |= []F); (sigma |= [][]F) ==> PROP W |] ==> PROP W
*)
bind_thm("dup_boxE", make_elim((temp_unlift STL3) RS iffD2));
bind_thm("dup_boxD", (temp_unlift STL3) RS iffD1);

(* dual versions for <> *)
qed_goalw "DmdDmd" TLA.thy [dmd_def] "|- (<><>F) = (<>F)"
   (fn _ => [ auto_tac (temp_css addsimps2 [STL3]) ]);
bind_thm("dup_dmdE", make_elim((temp_unlift DmdDmd) RS iffD2));
bind_thm("dup_dmdD", (temp_unlift DmdDmd) RS iffD1);


(* ------------------------ STL4 ------------------------------------------- *)
qed_goal "STL4" TLA.thy "|- F --> G  ==> |- []F --> []G"
   (fn [prem] => [Clarsimp_tac 1,
		  rtac (temp_use normalT) 1,
                  rtac (temp_use (prem RS necT)) 1,
		  atac 1
		 ]);

(* Unlifted version as an elimination rule *)
qed_goal "STL4E" TLA.thy 
         "[| sigma |= []F; |- F --> G |] ==> sigma |= []G"
   (fn prems => [ REPEAT (resolve_tac (prems @ [temp_use STL4]) 1) ]);

qed_goal "STL4_gen" TLA.thy "|- Init F --> Init G ==> |- []F --> []G"
   (fn [prem] => [rtac (rewrite_rule [boxInitD] (prem RS STL4)) 1]);

qed_goal "STL4E_gen" TLA.thy
         "[| sigma |= []F; |- Init F --> Init G |] ==> sigma |= []G"
   (fn prems => [ REPEAT (resolve_tac (prems @ [temp_use STL4_gen]) 1) ]);

(* see also STL4Edup below, which allows an auxiliary boxed formula:
       []A /\ F => G
     -----------------
     []A /\ []F => []G
*)

(* The dual versions for <> *)
qed_goalw "DmdImpl" TLA.thy [dmd_def]
   "|- F --> G ==> |- <>F --> <>G"
   (fn [prem] => [fast_tac (temp_cs addSIs [prem] addSEs [STL4E]) 1]);

qed_goal "DmdImplE" TLA.thy
   "[| sigma |= <>F; |- F --> G |] ==> sigma |= <>G"
   (fn prems => [ REPEAT (resolve_tac (prems @ [temp_use DmdImpl]) 1) ]);


(* ------------------------ STL5 ------------------------------------------- *)
qed_goal "STL5" TLA.thy "|- ([]F & []G) = ([](F & G))"
   (fn _ => [Auto_tac,
	     subgoal_tac "sigma |= [](G --> (F & G))" 1,
	     etac (temp_use normalT) 1, atac 1,
	     ALLGOALS (fast_tac (temp_cs addSEs [STL4E]))
	    ]);
(* rewrite rule to split conjunctions under boxes *)
bind_thm("split_box_conj", (temp_unlift STL5) RS sym);

(* the corresponding elimination rule allows to combine boxes in the hypotheses
   (NB: F and G must have the same type, i.e., both actions or temporals.)
   Use "addSE2" etc. if you want to add this to a claset, otherwise it will loop!
*)
qed_goal "box_conjE" TLA.thy
   "[| sigma |= []F; sigma |= []G; sigma |= [](F&G) ==> PROP R |] ==> PROP R"
   (fn prems => [ REPEAT (resolve_tac
			   (prems @ [(temp_unlift STL5) RS iffD1, conjI]) 1) ]);

(* Instances of box_conjE for state predicates, actions, and temporals
   in case the general rule is "too polymorphic".
*)
bind_thm("box_conjE_temp", read_instantiate [("'a","behavior")] box_conjE);
bind_thm("box_conjE_stp", read_instantiate [("'a","state")] box_conjE);
bind_thm("box_conjE_act", read_instantiate [("'a","state * state")] box_conjE);

(* Define a tactic that tries to merge all boxes in an antecedent. The definition is
   a bit kludgy in order to simulate "double elim-resolution".
*)

Goal "[| sigma |= []F; PROP W |] ==> PROP W";
by (atac 1);
val box_thin = result();

fun merge_box_tac i =
   REPEAT_DETERM (EVERY [etac box_conjE i, atac i, etac box_thin i]);

fun merge_temp_box_tac i =
   REPEAT_DETERM (EVERY [etac box_conjE_temp i, atac i, 
                         eres_inst_tac [("'a","behavior")] box_thin i]);

fun merge_stp_box_tac i =
   REPEAT_DETERM (EVERY [etac box_conjE_stp i, atac i, 
                         eres_inst_tac [("'a","state")] box_thin i]);

fun merge_act_box_tac i =
   REPEAT_DETERM (EVERY [etac box_conjE_act i, atac i, 
                         eres_inst_tac [("'a","state * state")] box_thin i]);


(* rewrite rule to push universal quantification through box:
      (sigma |= [](! x. F x)) = (! x. (sigma |= []F x))
*)
bind_thm("all_box", standard((temp_unlift allT) RS sym));


qed_goal "DmdOr" TLA.thy "|- (<>(F | G)) = (<>F | <>G)"
   (fn _ => [auto_tac (temp_css addsimps2 [dmd_def,split_box_conj]),
             TRYALL (EVERY' [etac swap, 
                             merge_box_tac, 
                             fast_tac (temp_cs addSEs [STL4E])])
            ]);

qed_goal "exT" TLA.thy "|- (? x. <>(F x)) = (<>(? x. F x))"
   (fn _ => [ auto_tac (temp_css addsimps2 [dmd_def,Not_Rex,all_box]) ]);

bind_thm("ex_dmd", standard((temp_unlift exT) RS sym));
	     

qed_goal "STL4Edup" TLA.thy
   "!!sigma. [| sigma |= []A; sigma |= []F; |- F & []A --> G |] ==> sigma |= []G"
   (fn _ => [etac dup_boxE 1,
	     merge_box_tac 1,
	     etac STL4E 1,
	     atac 1
	    ]);

qed_goalw "DmdImpl2" TLA.thy [dmd_def]
   "!!sigma. [| sigma |= <>F; sigma |= [](F --> G) |] ==> sigma |= <>G"
   (fn _ => [Auto_tac,
	     etac notE 1,
	     merge_box_tac 1,
	     fast_tac (temp_cs addSEs [STL4E]) 1
	    ]);

qed_goal "InfImpl" TLA.thy
   "[| sigma |= []<>F; sigma |= []G; |- F & G --> H |] ==> sigma |= []<>H"
   (fn [prem1,prem2,prem3] 
       => [cut_facts_tac [prem1,prem2] 1,
	   eres_inst_tac [("F","G")] dup_boxE 1,
	   merge_box_tac 1,
	   fast_tac (temp_cs addSEs [STL4E,DmdImpl2] addSIs [prem3]) 1
	  ]);

(* ------------------------ STL6 ------------------------------------------- *)
(* Used in the proof of STL6, but useful in itself. *)
qed_goalw "BoxDmd" TLA.thy [dmd_def] "|- []F & <>G --> <>([]F & G)"
  (fn _ => [ Clarsimp_tac 1,
             etac dup_boxE 1,
	     merge_box_tac 1,
             etac swap 1,
             fast_tac (temp_cs addSEs [STL4E]) 1 ]);

(* weaker than BoxDmd, but more polymorphic (and often just right) *)
qed_goalw "BoxDmd_simple" TLA.thy [dmd_def] "|- []F & <>G --> <>(F & G)"
  (fn _ => [ Clarsimp_tac 1,
	     merge_box_tac 1,
             fast_tac (temp_cs addSEs [notE,STL4E]) 1
	   ]);

qed_goalw "BoxDmd2_simple" TLA.thy [dmd_def] "|- []F & <>G --> <>(G & F)"
  (fn _ => [ Clarsimp_tac 1,
	     merge_box_tac 1,
             fast_tac (temp_cs addSEs [notE,STL4E]) 1
	   ]);

qed_goal "DmdImpldup" TLA.thy 
   "[| sigma |= []A; sigma |= <>F; |- []A & F --> G |] ==> sigma |= <>G"
   (fn [p1,p2,p3] => [rtac ((p2 RS (p1 RS (temp_use BoxDmd))) RS DmdImplE) 1,
                      rtac p3 1]);

qed_goal "STL6" TLA.thy "|- <>[]F & <>[]G --> <>[](F & G)"
  (fn _ => [auto_tac (temp_css addsimps2 [symmetric (temp_rewrite STL5)]),
	    dtac (temp_use linT) 1, atac 1, etac thin_rl 1,
	    rtac ((temp_unlift DmdDmd) RS iffD1) 1,
	    etac disjE 1,
	    etac DmdImplE 1, rtac BoxDmd 1,
	    (* the second subgoal needs commutativity of &, which complicates the proof *)
	    etac DmdImplE 1,
	    Auto_tac,
	    dtac (temp_use BoxDmd) 1, atac 1, etac thin_rl 1,
	    fast_tac (temp_cs addSEs [DmdImplE]) 1
	   ]);


(* ------------------------ True / False ----------------------------------------- *)
section "Simplification of constants";

qed_goal "BoxConst" TLA.thy "|- ([]#P) = #P"
  (fn _ => [rtac tempI 1,
            case_tac "P" 1,
            auto_tac (temp_css addSIs2 [necT] addDs2 [STL2_gen] 
                               addsimps2 Init_simps)
           ]);

qed_goalw "DmdConst" TLA.thy [dmd_def] "|- (<>#P) = #P"
  (fn _ => [case_tac "P" 1,
            ALLGOALS (asm_full_simp_tac (simpset() addsimps [BoxConst]))
           ]);

val temp_simps = map temp_rewrite [BoxConst, DmdConst];

(* Make these rewrites active by default *)
Addsimps temp_simps;
val temp_css = temp_css addsimps2 temp_simps;
val temp_cs = op addss temp_css;


(* ------------------------ Further rewrites ----------------------------------------- *)
section "Further rewrites";

qed_goalw "NotBox" TLA.thy [dmd_def] "|- (~[]F) = (<>~F)"
   (fn _ => [ Simp_tac 1 ]);

qed_goalw "NotDmd" TLA.thy [dmd_def] "|- (~<>F) = ([]~F)"
   (fn _ => [ Simp_tac 1 ]);

(* These are not by default included in temp_css, because they could be harmful,
   e.g. []F & ~[]F becomes []F & <>~F !! *)
val more_temp_simps =  (map temp_rewrite [STL3, DmdDmd, NotBox, NotDmd])
                       @ (map (fn th => (temp_unlift th) RS eq_reflection)
		         [NotBox, NotDmd]);

qed_goal "BoxDmdBox" TLA.thy "|- ([]<>[]F) = (<>[]F)"
   (fn _ => [ auto_tac (temp_css addSDs2 [STL2]),
              rtac ccontr 1,
              subgoal_tac "sigma |= <>[][]F & <>[]~[]F" 1,
              etac thin_rl 1,
              Auto_tac,
	      dtac (temp_use STL6) 1, atac 1,
	      Asm_full_simp_tac 1,
	      ALLGOALS (asm_full_simp_tac (simpset() addsimps more_temp_simps))
	    ]);

qed_goalw "DmdBoxDmd" TLA.thy [dmd_def] "|- (<>[]<>F) = ([]<>F)"
  (fn _ => [ auto_tac (temp_css addsimps2 [rewrite_rule [dmd_def] BoxDmdBox]) ]);

val more_temp_simps = more_temp_simps @ (map temp_rewrite [BoxDmdBox, DmdBoxDmd]);


(* ------------------------ Miscellaneous ----------------------------------- *)

qed_goal "BoxOr" TLA.thy 
   "!!sigma. [| sigma |= []F | []G |] ==> sigma |= [](F | G)"
   (fn _ => [ fast_tac (temp_cs addSEs [STL4E]) 1 ]);

(* "persistently implies infinitely often" *)
qed_goal "DBImplBD" TLA.thy "|- <>[]F --> []<>F"
  (fn _ => [Clarsimp_tac 1,
	    rtac ccontr 1,
            asm_full_simp_tac (simpset() addsimps more_temp_simps) 1,
            dtac (temp_use STL6) 1, atac 1,
            Asm_full_simp_tac 1
	   ]);

qed_goal "BoxDmdDmdBox" TLA.thy
   "|- []<>F & <>[]G --> []<>(F & G)"
   (fn _ => [Clarsimp_tac 1,
             rtac ccontr 1,
	     rewrite_goals_tac more_temp_simps,
	     dtac (temp_use STL6) 1, atac 1,
	     subgoal_tac "sigma |= <>[]~F" 1,
	     force_tac (temp_css addsimps2 [dmd_def]) 1,
	     fast_tac (temp_cs addEs [DmdImplE,STL4E]) 1
	    ]);


(* ------------------------------------------------------------------------- *)
(***          TLA-specific theorems: primed formulas                       ***)
(* ------------------------------------------------------------------------- *)
section "priming";

(* ------------------------ TLA2 ------------------------------------------- *)
qed_goal "STL2_pr" TLA.thy
  "|- []P --> Init P & Init P`"
  (fn _ => [fast_tac (temp_cs addSIs [primeI, STL2_gen]) 1]);

(* Auxiliary lemma allows priming of boxed actions *)
qed_goal "BoxPrime" TLA.thy "|- []P --> []($P & P$)"
  (fn _ => [Clarsimp_tac 1,
	    etac dup_boxE 1,
            rewtac boxInit_act,
            etac STL4E 1,
	    auto_tac (temp_css addsimps2 Init_simps addSDs2 [STL2_pr])
	   ]);

qed_goal "TLA2" TLA.thy "|- $P & P$ --> A  ==>  |- []P --> []A"
  (fn prems => [Clarsimp_tac 1,
                dtac (temp_use BoxPrime) 1,
                auto_tac (temp_css addsimps2 [Init_stp_act_rev] addSIs2 prems addSEs2 [STL4E])
               ]);

qed_goal "TLA2E" TLA.thy 
   "[| sigma |= []P; |- $P & P$ --> A |] ==> sigma |= []A"
   (fn prems => [REPEAT (resolve_tac (prems @ (prems RL [temp_use TLA2])) 1)]);

qed_goalw "DmdPrime" TLA.thy [dmd_def] "|- (<>P`) --> (<>P)"
   (fn _ => [ fast_tac (temp_cs addSEs [TLA2E]) 1 ]);

bind_thm("PrimeDmd", (temp_use InitDmd_gen) RS (temp_use DmdPrime));

(* ------------------------ INV1, stable --------------------------------------- *)
section "stable, invariant";

qed_goal "ind_rule" TLA.thy
   "[| sigma |= []H; sigma |= Init P; |- H --> (Init P & ~[]F --> Init(P`) & F) |] \
\   ==> sigma |= []F"
   (fn prems => [rtac (temp_use indT) 1,
		 REPEAT (resolve_tac (prems @ (prems RL [STL4E])) 1)]);

qed_goalw "box_stp_act" TLA.thy [boxInit_act] "|- ([]$P) = ([]P)"
  (K [simp_tac (simpset() addsimps Init_simps) 1]);
bind_thm("box_stp_actI", zero_var_indexes ((temp_use box_stp_act) RS iffD2));
bind_thm("box_stp_actD", zero_var_indexes ((temp_use box_stp_act) RS iffD1));

val more_temp_simps = (temp_rewrite box_stp_act)::more_temp_simps;

qed_goalw "INV1" TLA.thy [stable_def,boxInit_stp,boxInit_act] 
  "|- (Init P) --> (stable P) --> []P"
  (K [Clarsimp_tac 1,
      etac ind_rule 1,
      auto_tac (temp_css addsimps2 Init_simps addEs2 [ind_rule])
     ]);

qed_goalw "StableT" TLA.thy [stable_def]
   "|- $P & A --> P` ==> |- []A --> stable P"
   (fn [prem] => [fast_tac (temp_cs addSEs [STL4E] addIs [prem]) 1]);

qed_goal "Stable" TLA.thy
   "[| sigma |= []A; |- $P & A --> P` |] ==> sigma |= stable P"
   (fn prems => [ REPEAT (resolve_tac (prems @ [temp_use StableT]) 1) ]);

(* Generalization of INV1 *)
qed_goalw "StableBox" TLA.thy [stable_def]
   "|- (stable P) --> [](Init P --> []P)"
   (K [Clarsimp_tac 1,
       etac dup_boxE 1,
       force_tac (temp_css addsimps2 [stable_def] addEs2 [STL4E, INV1]) 1]);

qed_goal "DmdStable" TLA.thy 
   "|- (stable P) & <>P --> <>[]P"
   (fn _ => [Clarsimp_tac 1,
             rtac DmdImpl2 1,
	     etac (temp_use StableBox) 2,
	     asm_simp_tac (simpset() addsimps [dmdInitD]) 1
	    ]);

(* ---------------- (Semi-)automatic invariant tactics ---------------------- *)

(* inv_tac reduces goals of the form ... ==> sigma |= []P *)
fun inv_tac css = SELECT_GOAL
     (EVERY [auto_tac css,
             TRY (merge_box_tac 1),
             rtac (temp_use INV1) 1, (* fail if the goal is not a box *)
             TRYALL (etac Stable)]);

(* auto_inv_tac applies inv_tac and then tries to attack the subgoals;
   in simple cases it may be able to handle goals like |- MyProg --> []Inv.
   In these simple cases the simplifier seems to be more useful than the
   auto-tactic, which applies too much propositional logic and simplifies
   too late.
*)

fun auto_inv_tac ss = SELECT_GOAL
    ((inv_tac (claset(),ss) 1) THEN
     (TRYALL (action_simp_tac (ss addsimps [Init_stp,Init_act]) [] [squareE])));


qed_goalw "unless" TLA.thy [dmd_def]
   "|- []($P --> P` | Q`) --> (stable P) | <>Q"
   (fn _ => [clarsimp_tac (temp_css addSDs2 [BoxPrime]) 1,
	     merge_box_tac 1,
             etac swap 1,
	     fast_tac (temp_cs addSEs [Stable]) 1
	    ]);


(* --------------------- Recursive expansions --------------------------------------- *)
section "recursive expansions";

(* Recursive expansions of [] and <> for state predicates *)
qed_goal "BoxRec" TLA.thy "|- ([]P) = (Init P & []P`)"
   (fn _ => [auto_tac (temp_css addSIs2 [STL2_gen]),
	     fast_tac (temp_cs addSEs [TLA2E]) 1,
	     auto_tac (temp_css addsimps2 [stable_def] addSEs2 [INV1,STL4E])
	    ]);

qed_goalw "DmdRec" TLA.thy [dmd_def, temp_rewrite BoxRec] "|- (<>P) = (Init P | <>P`)" 
  (K [ auto_tac (temp_css addsimps2 Init_simps) ]);

qed_goal "DmdRec2" TLA.thy
 "!!sigma. [| sigma |= <>P; sigma |= []~P` |] ==> sigma |= Init P"
   (K [ force_tac (temp_css addsimps2 [DmdRec,dmd_def]) 1]);

(* The "-->" part of the following is a little intricate. *)
qed_goal "InfinitePrime" TLA.thy "|- ([]<>P) = ([]<>P`)"
   (fn _ => [Auto_tac,
	     rtac classical 1,
	     rtac (temp_use DBImplBD) 1,
	     subgoal_tac "sigma |= <>[]P" 1,
	     fast_tac (temp_cs addSEs [DmdImplE,TLA2E]) 1,
	     subgoal_tac "sigma |= <>[](<>P & []~P`)" 1,
	     force_tac (temp_css addsimps2 [boxInit_stp]
			             addSEs2 [DmdImplE,STL4E,DmdRec2]) 1,
	     force_tac (temp_css addSIs2 [STL6] addsimps2 more_temp_simps) 1,
	     fast_tac (temp_cs addIs [DmdPrime] addSEs [STL4E]) 1
	    ]);

qed_goal "InfiniteEnsures" TLA.thy
   "[| sigma |= []N; sigma |= []<>A; |- A & N --> P` |] ==> sigma |= []<>P"
   (fn prems => [rewtac (temp_rewrite InfinitePrime),
                 rtac InfImpl 1,
                 REPEAT (resolve_tac prems 1)
                ]);

(* ------------------------ fairness ------------------------------------------- *)
section "fairness";

(* alternative definitions of fairness *)
qed_goalw "WF_alt" TLA.thy [WF_def,dmd_def] 
   "|- WF(A)_v = ([]<>~Enabled(<A>_v) | []<><A>_v)"
   (fn _ => [ fast_tac temp_cs 1 ]);

qed_goalw "SF_alt" TLA.thy [SF_def,dmd_def]
   "|- SF(A)_v = (<>[]~Enabled(<A>_v) | []<><A>_v)"
   (fn _ => [ fast_tac temp_cs 1 ]);

(* theorems to "box" fairness conditions *)
qed_goal "BoxWFI" TLA.thy "|- WF(A)_v --> []WF(A)_v"
   (fn _ => [ auto_tac (temp_css addsimps2 (WF_alt::more_temp_simps) 
                                 addSIs2 [BoxOr]) ]);

qed_goal "WF_Box" TLA.thy "|- ([]WF(A)_v) = WF(A)_v"
  (fn prems => [ fast_tac (temp_cs addSIs [BoxWFI] addSDs [STL2]) 1 ]);

qed_goal "BoxSFI" TLA.thy "|- SF(A)_v --> []SF(A)_v"
   (fn _ => [ auto_tac (temp_css addsimps2 (SF_alt::more_temp_simps) 
                                 addSIs2 [BoxOr]) ]);

qed_goal "SF_Box" TLA.thy "|- ([]SF(A)_v) = SF(A)_v"
  (fn prems => [ fast_tac (temp_cs addSIs [BoxSFI] addSDs [STL2]) 1 ]);

val more_temp_simps = more_temp_simps @ (map temp_rewrite [WF_Box, SF_Box]);

qed_goalw "SFImplWF" TLA.thy [SF_def,WF_def] "|- SF(A)_v --> WF(A)_v"
  (fn _ => [ fast_tac (temp_cs addSDs [DBImplBD]) 1 ]);

(* A tactic that "boxes" all fairness conditions. Apply more_temp_simps to "unbox". *)
val box_fair_tac = SELECT_GOAL (REPEAT (dresolve_tac [BoxWFI,BoxSFI] 1));


(* ------------------------------ leads-to ------------------------------ *)

section "~>";

qed_goalw "leadsto_init" TLA.thy [leadsto_def]
   "|- (Init F) & (F ~> G) --> <>G"
   (fn _ => [ auto_tac (temp_css addSDs2 [STL2]) ]);

(* |- F & (F ~> G) --> <>G *)
bind_thm("leadsto_init_temp", 
         rewrite_rule Init_simps (read_instantiate [("'a","behavior")] leadsto_init));

qed_goalw "streett_leadsto" TLA.thy [leadsto_def]
   "|- ([]<>Init F --> []<>G) = (<>(F ~> G))" (K [
             Auto_tac,
             asm_full_simp_tac (simpset() addsimps more_temp_simps) 1,
             fast_tac (temp_cs addSEs [DmdImplE,STL4E]) 1,
             fast_tac (temp_cs addSIs [InitDmd] addSEs [STL4E]) 1,
             subgoal_tac "sigma |= []<><>G" 1,
             asm_full_simp_tac (simpset() addsimps more_temp_simps) 1,
             dtac (temp_use BoxDmdDmdBox) 1, atac 1,
             fast_tac (temp_cs addSEs [DmdImplE,STL4E]) 1
            ]);

qed_goal "leadsto_infinite" TLA.thy
   "|- []<>F & (F ~> G) --> []<>G"
   (fn _ => [Clarsimp_tac 1,
             etac ((temp_use InitDmd) RS 
                   ((temp_unlift streett_leadsto) RS iffD2 RS mp)) 1,
             asm_simp_tac (simpset() addsimps [dmdInitD]) 1
            ]);

(* In particular, strong fairness is a Streett condition. The following
   rules are sometimes easier to use than WF2 or SF2 below.
*)
qed_goalw "leadsto_SF" TLA.thy [SF_def]
  "|- (Enabled(<A>_v) ~> <A>_v) --> SF(A)_v"
  (K [clarsimp_tac (temp_css addSEs2 [leadsto_infinite]) 1]);

qed_goal "leadsto_WF" TLA.thy 
  "|- (Enabled(<A>_v) ~> <A>_v) --> WF(A)_v"
  (K [ clarsimp_tac (temp_css addSIs2 [SFImplWF, leadsto_SF]) 1 ]);

(* introduce an invariant into the proof of a leadsto assertion.
   []I --> ((P ~> Q)  =  (P /\ I ~> Q))
*)
qed_goalw "INV_leadsto" TLA.thy [leadsto_def]
   "|- []I & (P & I ~> Q) --> (P ~> Q)"
   (fn _ => [Clarsimp_tac 1,
             etac STL4Edup 1, atac 1,
	     auto_tac (temp_css addsimps2 Init_simps addSDs2 [STL2_gen])
	    ]);

qed_goalw "leadsto_classical" TLA.thy [leadsto_def,dmd_def]
   "|- (Init F & []~G ~> G) --> (F ~> G)"
   (fn _ => [force_tac (temp_css addsimps2 Init_simps addSEs2 [STL4E]) 1]);

qed_goalw "leadsto_false" TLA.thy [leadsto_def]
  "|- (F ~> #False) = ([]~F)"
  (fn _ => [ simp_tac (simpset() addsimps [boxNotInitD]) 1 ]);

qed_goalw "leadsto_exists" TLA.thy [leadsto_def]
  "|- ((? x. F x) ~> G) = (!x. (F x ~> G))"
  (K [auto_tac (temp_css addsimps2 allT::Init_simps addSEs2 [STL4E])]);


(* basic leadsto properties, cf. Unity *)

qed_goalw "ImplLeadsto_gen" TLA.thy [leadsto_def]
   "|- [](Init F --> Init G) --> (F ~> G)"
   (fn _ => [auto_tac (temp_css addSIs2 [InitDmd_gen] 
                                addSEs2 [STL4E_gen] addsimps2 Init_simps)
	    ]);

bind_thm("ImplLeadsto",
         rewrite_rule Init_simps 
             (read_instantiate [("'a","behavior"), ("'b","behavior")] ImplLeadsto_gen));

qed_goal "ImplLeadsto_simple" TLA.thy
  "|- F --> G ==> |- F ~> G"
  (fn [prem] => [auto_tac (temp_css addsimps2 [Init_def] 
                                    addSIs2 [ImplLeadsto_gen,necT,prem])]);

qed_goalw "EnsuresLeadsto" TLA.thy [leadsto_def]
   "|- A & $P --> Q` ==> |- []A --> (P ~> Q)" (fn [prem] => [
		  clarsimp_tac (temp_css addSEs2 [INV_leadsto]) 1, 
                  etac STL4E_gen 1,
                  auto_tac (temp_css addsimps2 Init_defs
                                     addSIs2 [PrimeDmd, prem])
                 ]);

qed_goalw "EnsuresLeadsto2" TLA.thy [leadsto_def]
   "|- []($P --> Q`) --> (P ~> Q)"
   (fn _ => [Clarsimp_tac 1,
             etac STL4E_gen 1,
             auto_tac (temp_css addsimps2 Init_simps addSIs2 [PrimeDmd])
            ]);

qed_goalw "ensures" TLA.thy [leadsto_def]
  "[| |- $P & N --> P` | Q`; \
\     |- ($P & N) & A --> Q` \
\  |] ==> |- []N & []([]P --> <>A) --> (P ~> Q)"
  (fn [p1,p2] => [Clarsimp_tac 1,
                  etac STL4Edup 1, atac 1,
                  Clarsimp_tac 1,
                  subgoal_tac "sigmaa |= []($P --> P` | Q`)" 1,
                   dtac (temp_use unless) 1,
                   clarsimp_tac (temp_css addSDs2 [INV1]) 1,
                   rtac ((temp_use (p2 RS DmdImpl)) RS (temp_use DmdPrime)) 1,
                   force_tac (temp_css addSIs2 [BoxDmd_simple]
                                       addsimps2 [split_box_conj,box_stp_act]) 1,
                  force_tac (temp_css addEs2 [STL4E] addDs2 [p1]) 1
                 ]);

qed_goal "ensures_simple" TLA.thy
  "[| |- $P & N --> P` | Q`; \
\     |- ($P & N) & A --> Q` \
\  |] ==> |- []N & []<>A --> (P ~> Q)"
  (fn prems => [Clarsimp_tac 1,
                rtac (temp_use ensures) 1,
                TRYALL (ares_tac prems),
                force_tac (temp_css addSEs2 [STL4E]) 1
               ]);

qed_goal "EnsuresInfinite" TLA.thy
   "[| sigma |= []<>P; sigma |= []A; |- A & $P --> Q` |] ==> sigma |= []<>Q"
   (fn prems => [REPEAT (resolve_tac (prems @ [temp_use leadsto_infinite,
					       temp_use EnsuresLeadsto]) 1)]);


(*** Gronning's lattice rules (taken from TLP) ***)
section "Lattice rules";

qed_goalw "LatticeReflexivity" TLA.thy [leadsto_def] "|- F ~> F"
   (fn _ => [REPEAT (resolve_tac [necT,InitDmd_gen] 1)]);

qed_goalw "LatticeTransitivity" TLA.thy [leadsto_def]
   "|- (G ~> H) & (F ~> G) --> (F ~> H)"
   (fn _ => [Clarsimp_tac 1,
             etac dup_boxE 1,  (* [][](Init G --> H) *)
	     merge_box_tac 1,
	     clarsimp_tac (temp_css addSEs2 [STL4E]) 1,
             rtac dup_dmdD 1,
             subgoal_tac "sigmaa |= <>Init G" 1,
             etac DmdImpl2 1, atac 1,
             asm_simp_tac (simpset() addsimps [dmdInitD]) 1
	    ]);

qed_goalw "LatticeDisjunctionElim1" TLA.thy [leadsto_def]
   "|- (F | G ~> H) --> (F ~> H)"
   (fn _ => [ auto_tac (temp_css addsimps2 Init_simps addSEs2 [STL4E]) ]);

qed_goalw "LatticeDisjunctionElim2" TLA.thy [leadsto_def]
   "|- (F | G ~> H) --> (G ~> H)"
   (fn _ => [ auto_tac (temp_css addsimps2 Init_simps addSEs2 [STL4E]) ]);

qed_goalw "LatticeDisjunctionIntro" TLA.thy [leadsto_def]
   "|- (F ~> H) & (G ~> H) --> (F | G ~> H)"
   (fn _ => [Clarsimp_tac 1,
             merge_box_tac 1,
	     auto_tac (temp_css addsimps2 Init_simps addSEs2 [STL4E])
	    ]);

qed_goal "LatticeDisjunction" TLA.thy
   "|- (F | G ~> H) = ((F ~> H) & (G ~> H))"
   (fn _ => [auto_tac (temp_css addIs2 [LatticeDisjunctionIntro,
                                LatticeDisjunctionElim1, LatticeDisjunctionElim2])]);

qed_goal "LatticeDiamond" TLA.thy
   "|- (A ~> B | C) & (B ~> D) & (C ~> D) --> (A ~> D)"
   (fn _ => [Clarsimp_tac 1,
             subgoal_tac "sigma |= (B | C) ~> D" 1,
	     eres_inst_tac [("G", "LIFT (B | C)")] (temp_use LatticeTransitivity) 1,
	     ALLGOALS (fast_tac (temp_cs addSIs [LatticeDisjunctionIntro]))
	    ]);

qed_goal "LatticeTriangle" TLA.thy
   "|- (A ~> D | B) & (B ~> D) --> (A ~> D)"
   (fn _ => [Clarsimp_tac 1,
             subgoal_tac "sigma |= (D | B) ~> D" 1,
	     eres_inst_tac [("G", "LIFT (D | B)")] (temp_use LatticeTransitivity) 1, atac 1,
	     auto_tac (temp_css addSIs2 [LatticeDisjunctionIntro] 
                                addIs2 [LatticeReflexivity])
	    ]);

qed_goal "LatticeTriangle2" TLA.thy
   "|- (A ~> B | D) & (B ~> D) --> (A ~> D)"
   (fn _ => [Clarsimp_tac 1,
             subgoal_tac "sigma |= B | D ~> D" 1,
	     eres_inst_tac [("G", "LIFT (B | D)")] (temp_use LatticeTransitivity) 1, atac 1,
	     auto_tac (temp_css addSIs2 [LatticeDisjunctionIntro] 
                                addIs2 [LatticeReflexivity])
	    ]);

(*** Lamport's fairness rules ***)
section "Fairness rules";

qed_goal "WF1" TLA.thy
   "[| |- $P & N  --> P` | Q`;   \
\      |- ($P & N) & <A>_v --> Q`;   \
\      |- $P & N --> $(Enabled(<A>_v)) |]   \
\  ==> |- []N & WF(A)_v --> (P ~> Q)"  (fn prems => [
             clarsimp_tac (temp_css addSDs2 [BoxWFI]) 1,
             rtac (temp_use ensures) 1,
             TRYALL (ares_tac prems),
             etac STL4Edup 1, atac 1,
             clarsimp_tac (temp_css addsimps2 [WF_def]) 1,
             rtac (temp_use STL2) 1,
             clarsimp_tac (temp_css addSEs2 [mp] addSIs2 [InitDmd]) 1,
             resolve_tac ((map temp_use (prems RL [STL4])) RL [box_stp_actD]) 1,
             asm_simp_tac (simpset() addsimps [split_box_conj,box_stp_actI]) 1
            ]);

(* Sometimes easier to use; designed for action B rather than state predicate Q *)
qed_goalw "WF_leadsto" TLA.thy [leadsto_def]
   "[| |- N & $P --> $Enabled (<A>_v);            \
\      |- N & <A>_v --> B;                  \ 
\      |- [](N & [~A]_v) --> stable P  |]  \
\   ==> |- []N & WF(A)_v --> (P ~> B)"
   (fn [prem1,prem2,prem3]
       => [clarsimp_tac (temp_css addSDs2 [BoxWFI]) 1,
           etac STL4Edup 1, atac 1,
           Clarsimp_tac 1,
           rtac (temp_use (prem2 RS DmdImpl)) 1,
           rtac (temp_use BoxDmd_simple) 1, atac 1,
           rtac classical 1,
           rtac (temp_use STL2) 1,
           clarsimp_tac (temp_css addsimps2 [WF_def] addSEs2 [mp] addSIs2 [InitDmd]) 1,
           rtac ((temp_use (prem1 RS STL4)) RS box_stp_actD) 1,
           asm_simp_tac (simpset() addsimps [split_box_conj,box_stp_act]) 1,
           etac (temp_use INV1) 1,
           rtac (temp_use prem3) 1,
           asm_full_simp_tac (simpset() addsimps [split_box_conj,temp_use NotDmd,not_angle]) 1
          ]);

qed_goal "SF1" TLA.thy
   "[| |- $P & N  --> P` | Q`;   \
\      |- ($P & N) & <A>_v --> Q`;   \
\      |- []P & []N & []F --> <>Enabled(<A>_v) |]   \
\  ==> |- []N & SF(A)_v & []F --> (P ~> Q)"
   (fn prems => [
             clarsimp_tac (temp_css addSDs2 [BoxSFI]) 1,
             rtac (temp_use ensures) 1,
             TRYALL (ares_tac prems),
             eres_inst_tac [("F","F")] dup_boxE 1,
             merge_temp_box_tac 1,
             etac STL4Edup 1, atac 1,
             clarsimp_tac (temp_css addsimps2 [SF_def]) 1,
             rtac (temp_use STL2) 1, etac mp 1,
             resolve_tac (map temp_use (prems RL [STL4])) 1,
             asm_simp_tac (simpset() addsimps [split_box_conj, STL3]) 1
            ]);

qed_goal "WF2" TLA.thy
   "[| |- N & <B>_f --> <M>_g;   \
\      |- $P & P` & <N & A>_f --> B;   \
\      |- P & Enabled(<M>_g) --> Enabled(<A>_f);   \
\      |- [](N & [~B]_f) & WF(A)_f & []F & <>[]Enabled(<M>_g) --> <>[]P |]   \
\  ==> |- []N & WF(A)_f & []F --> WF(M)_g"
(fn [prem1,prem2,prem3,prem4] => [
	   clarsimp_tac (temp_css addSDs2 [BoxWFI, (temp_use BoxDmdBox) RS iffD2] 
                            addsimps2 [read_instantiate [("A","M")] WF_def]) 1,
           eres_inst_tac [("F","F")] dup_boxE 1,
           merge_temp_box_tac 1,
           etac STL4Edup 1, atac 1,
           clarsimp_tac (temp_css addSIs2 [(temp_use BoxDmd_simple) RS (temp_use (prem1 RS DmdImpl))]) 1,
           rtac classical 1,
           subgoal_tac "sigmaa |= <>(($P & P` & N) & <A>_f)" 1,
           force_tac (temp_css addsimps2 [angle_def] addSIs2 [prem2] addSEs2 [DmdImplE]) 1,
           rtac (temp_use (rewrite_rule [temp_rewrite DmdDmd] (BoxDmd_simple RS DmdImpl))) 1,
           asm_full_simp_tac (simpset() addsimps [temp_use NotDmd, not_angle]) 1,
           merge_act_box_tac 1,
           forward_tac [temp_use prem4] 1, TRYALL atac,
           dtac (temp_use STL6) 1, atac 1, 
           eres_inst_tac [("V","sigmaa |= <>[]P")] thin_rl 1,
           eres_inst_tac [("V","sigmaa |= []F")] thin_rl 1,
           dtac (temp_use BoxWFI) 1,
           eres_inst_tac [("F", "ACT N & [~B]_f")] dup_boxE 1,
           merge_temp_box_tac 1,
           etac DmdImpldup 1, atac 1,
           auto_tac (temp_css addsimps2 [split_box_conj,STL3,WF_Box,box_stp_act]),
           force_tac (temp_css addSEs2 [read_instantiate [("P","P")] TLA2E]) 1,
           rtac (temp_use STL2) 1,
           force_tac (temp_css addsimps2 [WF_def,split_box_conj] addSEs2 [mp] 
                               addSIs2 [InitDmd, prem3 RS STL4]) 1
	  ]);

qed_goal "SF2" TLA.thy
   "[| |- N & <B>_f --> <M>_g;   \
\      |- $P & P` & <N & A>_f --> B;   \
\      |- P & Enabled(<M>_g) --> Enabled(<A>_f);   \
\      |- [](N & [~B]_f) & SF(A)_f & []F & []<>Enabled(<M>_g) --> <>[]P |]   \
\  ==> |- []N & SF(A)_f & []F --> SF(M)_g"
(fn [prem1,prem2,prem3,prem4] => [
	   clarsimp_tac (temp_css addSDs2 [BoxSFI] 
                            addsimps2 [read_instantiate [("A","M")] SF_def]) 1,
           eres_inst_tac [("F","F")] dup_boxE 1,
           eres_inst_tac [("F","TEMP <>Enabled(<M>_g)")] dup_boxE 1,
           merge_temp_box_tac 1,
           etac STL4Edup 1, atac 1,
           clarsimp_tac (temp_css addSIs2 [(temp_use BoxDmd_simple) RS (temp_use (prem1 RS DmdImpl))]) 1,
           rtac classical 1,
           subgoal_tac "sigmaa |= <>(($P & P` & N) & <A>_f)" 1,
           force_tac (temp_css addsimps2 [angle_def] addSIs2 [prem2] addSEs2 [DmdImplE]) 1,
           rtac (temp_use (rewrite_rule [temp_rewrite DmdDmd] (BoxDmd_simple RS DmdImpl))) 1,
           asm_full_simp_tac (simpset() addsimps [temp_use NotDmd, not_angle]) 1,
           merge_act_box_tac 1,
           forward_tac [temp_use prem4] 1, TRYALL atac,
           eres_inst_tac [("V","sigmaa |= []F")] thin_rl 1,
           dtac (temp_use BoxSFI) 1,
           eres_inst_tac [("F","TEMP <>Enabled(<M>_g)")] dup_boxE 1,
           eres_inst_tac [("F", "ACT N & [~B]_f")] dup_boxE 1,
           merge_temp_box_tac 1,
           etac DmdImpldup 1, atac 1,
           auto_tac (temp_css addsimps2 [split_box_conj,STL3,SF_Box,box_stp_act]),
           force_tac (temp_css addSEs2 [read_instantiate [("P","P")] TLA2E]) 1,
           rtac (temp_use STL2) 1,
           force_tac (temp_css addsimps2 [SF_def,split_box_conj] addSEs2 [mp,InfImpl] 
                               addSIs2 [prem3]) 1
	  ]);

(* ------------------------------------------------------------------------- *)
(***           Liveness proofs by well-founded orderings                   ***)
(* ------------------------------------------------------------------------- *)
section "Well-founded orderings";

qed_goal "wf_leadsto" TLA.thy
  "[| wf r;  \
\     !!x. sigma |= F x ~> (G | (? y. #((y,x):r) & F y))   \
\  |] ==> sigma |= F x ~> G"
  (fn p1::prems =>
     [rtac (p1 RS wf_induct) 1,
      rtac (temp_use LatticeTriangle) 1,
      resolve_tac prems 1,
      auto_tac (temp_css addsimps2 [leadsto_exists]),
      case_tac "(y,x):r" 1,
       Force_tac 1,
      force_tac (temp_css addsimps2 leadsto_def::Init_simps addSIs2 [necT]) 1]);

(* If r is well-founded, state function v cannot decrease forever *)
qed_goal "wf_not_box_decrease" TLA.thy
  "!!r. wf r ==> |- [][ (v`, $v) : #r ]_v --> <>[][#False]_v"
  (fn _ => [Clarsimp_tac 1,
            rtac ccontr 1,
            subgoal_tac "sigma |= (? x. v=#x) ~> #False" 1,
             dtac ((temp_use leadsto_false) RS iffD1 RS (temp_use STL2_gen)) 1,
             force_tac (temp_css addsimps2 Init_defs) 1,
            clarsimp_tac (temp_css addsimps2 [leadsto_exists,not_square]@more_temp_simps) 1,
            etac wf_leadsto 1,
            rtac (temp_use ensures_simple) 1, TRYALL atac,
            auto_tac (temp_css addsimps2 [square_def,angle_def])
           ]);

(* "wf r  ==>  |- <>[][ (v`, $v) : #r ]_v --> <>[][#False]_v" *)
bind_thm("wf_not_dmd_box_decrease",
         standard(rewrite_rule more_temp_simps (wf_not_box_decrease RS DmdImpl)));

(* If there are infinitely many steps where v decreases, then there
   have to be infinitely many non-stuttering steps where v doesn't decrease.
*)
qed_goal "wf_box_dmd_decrease" TLA.thy
  "wf r ==> |- []<>((v`, $v) : #r) --> []<><(v`, $v) ~: #r>_v"
  (fn [prem] => [
            Clarsimp_tac 1,
            rtac ccontr 1,
            asm_full_simp_tac (simpset() addsimps not_angle::more_temp_simps) 1,
            dtac (prem RS (temp_use wf_not_dmd_box_decrease)) 1,
            dtac (temp_use BoxDmdDmdBox) 1, atac 1,
            subgoal_tac "sigma |= []<>((#False)::action)" 1,
            Force_tac 1,
            etac STL4E 1,
            rtac DmdImpl 1,
            force_tac (temp_css addIs2 [prem RS wf_irrefl]) 1
           ]);

(* In particular, for natural numbers, if n decreases infinitely often
   then it has to increase infinitely often.
*)
qed_goal "nat_box_dmd_decrease" TLA.thy
  "!!n::nat stfun. |- []<>(n` < $n) --> []<>($n < n`)"
  (K [Clarsimp_tac 1,
      subgoal_tac "sigma |= []<><~( (n`,$n) : #less_than )>_n" 1,
      etac thin_rl 1, etac STL4E 1, rtac DmdImpl 1,
      clarsimp_tac (temp_css addsimps2 [angle_def]) 1,
      rtac nat_less_cases 1,
      Auto_tac,
      rtac (temp_use wf_box_dmd_decrease) 1,
      auto_tac (temp_css addSEs2 [STL4E,DmdImplE])
     ]);


(* ------------------------------------------------------------------------- *)
(***           Flexible quantification over state variables                ***)
(* ------------------------------------------------------------------------- *)
section "Flexible quantification";

qed_goal "aallI" TLA.thy 
  "[| basevars vs; (!!x. basevars (x,vs) ==> sigma |= F x) |] ==> sigma |= (AALL x. F x)"
  (fn [prem1,prem2] => [auto_tac (temp_css addsimps2 [aall_def] addSEs2 [eexE] 
                                   addSIs2 [prem1] addSDs2 [prem2])]);

qed_goalw "aallE" TLA.thy [aall_def] "|- (AALL x. F x) --> F x"
   (K [Clarsimp_tac 1, etac swap 1,
       force_tac (temp_css addSIs2 [eexI]) 1]);

(* monotonicity of quantification *)
qed_goal "eex_mono" TLA.thy
  "[| sigma |= EEX x. F x; !!x. sigma |= F x --> G x |] ==> sigma |= EEX x. G x"
  (fn [min,maj] => [rtac (unit_base RS (min RS eexE)) 1,
                    rtac (temp_use eexI) 1,
                    etac ((rewrite_rule intensional_rews maj) RS mp) 1
                   ]);

qed_goal "aall_mono" TLA.thy
  "[| sigma |= AALL x. F(x); !!x. sigma |= F(x) --> G(x) |] ==> sigma |= AALL x. G(x)"
  (fn [min,maj] => [rtac (unit_base RS aallI) 1,
                    rtac ((rewrite_rule intensional_rews maj) RS mp) 1,
                    rtac (min RS (temp_use aallE)) 1
                   ]);

(* Derived history introduction rule *)
qed_goal "historyI" TLA.thy
  "[| sigma |= Init I; sigma |= []N; basevars vs; \
\     (!!h. basevars(h,vs) ==> |- I & h = ha --> HI h); \
\     (!!h s t. [| basevars(h,vs); N (s,t); h t = hb (h s) (s,t) |] ==> HN h (s,t)) \
\  |] ==> sigma |= EEX h. Init (HI h) & [](HN h)" 
  (fn [p1,p2,p3,p4,p5] 
   => [rtac ((temp_use history) RS eexE) 1,
       rtac p3 1,
       rtac (temp_use eexI) 1,
       Clarsimp_tac 1, rtac conjI 1,
       cut_facts_tac [p2] 2,
       merge_box_tac 2,
       force_tac (temp_css addSEs2 [STL4E,p5]) 2,
       cut_facts_tac [p1] 1,
       force_tac (temp_css addsimps2 Init_defs addSEs2 [p4]) 1
      ]);

(* ----------------------------------------------------------------------
   example of a history variable: existence of a clock

Goal "|- EEX h. Init(h = #True) & [](h` = (~$h))";
by (rtac tempI 1);
by (rtac historyI 1);
by (REPEAT (force_tac (temp_css addsimps2 Init_defs addIs2 [unit_base, necT]) 1));
(** solved **)

---------------------------------------------------------------------- *)

