(* 
    File:	 TLA/TLA.ML
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

Lemmas and tactics for temporal reasoning.
*)

(* Specialize intensional introduction/elimination rules for temporal formulas *)

val [prem] = goal thy "(!!sigma. sigma |= (F::temporal)) ==> |- F";
by (REPEAT (resolve_tac [prem,intI] 1));
qed "tempI";

val [prem] = goal thy "|- (F::temporal) ==> sigma |= F";
by (rtac (prem RS intD) 1);
qed "tempD";


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
bind_thm("boxNotInit", 
         rewrite_rule Init_simps (read_instantiate [("F", "LIFT ~F")] boxInit));

Goalw [dmd_def] "TEMP <>F == TEMP <> Init F";
by (rewtac (read_instantiate [("F", "LIFT ~F")] boxInit));
by (simp_tac (simpset() addsimps Init_simps) 1);
qed "dmdInit";

bind_thm("dmdNotInit", 
         rewrite_rule Init_simps (read_instantiate [("F", "LIFT ~F")] dmdInit));

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
Goal "|- []F --> Init F";
by (rewtac (read_instantiate [("F", "F")] boxInit));
by (rtac STL2 1);
qed "STL2_gen";

(* see also STL2_pr below: "|- []P --> Init P & Init (P`)" *)


(* Dual versions for <> *)
Goalw [dmd_def] "|- F --> <> F";
by (auto_tac (temp_css addSDs2 [STL2]));
qed "InitDmd";

Goal "|- Init F --> <>F";
by (Clarsimp_tac 1);
by (dtac (temp_use InitDmd) 1);
by (asm_full_simp_tac (simpset() addsimps [dmdInitD]) 1);
qed "InitDmd_gen";


(* ------------------------ STL3 ------------------------------------------- *)
Goal "|- ([][]F) = ([]F)";
by (force_tac (temp_css addEs2 [transT,STL2]) 1);
qed "STL3";

(* corresponding elimination rule introduces double boxes: 
   [| (sigma |= []F); (sigma |= [][]F) ==> PROP W |] ==> PROP W
*)
bind_thm("dup_boxE", make_elim((temp_unlift STL3) RS iffD2));
bind_thm("dup_boxD", (temp_unlift STL3) RS iffD1);

(* dual versions for <> *)
Goal "|- (<><>F) = (<>F)";
by (auto_tac (temp_css addsimps2 [dmd_def,STL3]));
qed "DmdDmd";
bind_thm("dup_dmdE", make_elim((temp_unlift DmdDmd) RS iffD2));
bind_thm("dup_dmdD", (temp_unlift DmdDmd) RS iffD1);


(* ------------------------ STL4 ------------------------------------------- *)
val [prem] = goal thy "|- F --> G  ==> |- []F --> []G";
by (Clarsimp_tac 1);
by (rtac (temp_use normalT) 1);
by (rtac (temp_use (prem RS necT)) 1);
by (atac 1);
qed "STL4";

(* Unlifted version as an elimination rule *)
val prems = goal thy "[| sigma |= []F; |- F --> G |] ==> sigma |= []G";
by (REPEAT (resolve_tac (prems @ [temp_use STL4]) 1));
qed "STL4E";

val [prem] = goal thy "|- Init F --> Init G ==> |- []F --> []G";
by (rtac (rewrite_rule [boxInitD] (prem RS STL4)) 1);
qed "STL4_gen";

val prems = goal thy
   "[| sigma |= []F; |- Init F --> Init G |] ==> sigma |= []G";
by (REPEAT (resolve_tac (prems @ [temp_use STL4_gen]) 1));
qed "STL4E_gen";

(* see also STL4Edup below, which allows an auxiliary boxed formula:
       []A /\ F => G
     -----------------
     []A /\ []F => []G
*)

(* The dual versions for <> *)
val [prem] = goalw thy [dmd_def]
   "|- F --> G ==> |- <>F --> <>G";
by (fast_tac (temp_cs addSIs [prem] addSEs [STL4E]) 1);
qed "DmdImpl";

val prems = goal thy "[| sigma |= <>F; |- F --> G |] ==> sigma |= <>G";
by (REPEAT (resolve_tac (prems @ [temp_use DmdImpl]) 1));
qed "DmdImplE";


(* ------------------------ STL5 ------------------------------------------- *)
Goal "|- ([]F & []G) = ([](F & G))";
by Auto_tac;
by (subgoal_tac "sigma |= [](G --> (F & G))" 1);
by (etac (temp_use normalT) 1);
by (ALLGOALS (fast_tac (temp_cs addSEs [STL4E])));
qed "STL5";

(* rewrite rule to split conjunctions under boxes *)
bind_thm("split_box_conj", (temp_unlift STL5) RS sym);

(* the corresponding elimination rule allows to combine boxes in the hypotheses
   (NB: F and G must have the same type, i.e., both actions or temporals.)
   Use "addSE2" etc. if you want to add this to a claset, otherwise it will loop!
*)
val prems = goal thy
   "[| sigma |= []F; sigma |= []G; sigma |= [](F&G) ==> PROP R |] ==> PROP R";
by (REPEAT (resolve_tac (prems @ [(temp_unlift STL5) RS iffD1, conjI]) 1));
qed "box_conjE";

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


Goal "|- (<>(F | G)) = (<>F | <>G)";
by (auto_tac (temp_css addsimps2 [dmd_def,split_box_conj]));
by (ALLGOALS (EVERY' [etac contrapos_np, 
                      merge_box_tac, 
                      fast_tac (temp_cs addSEs [STL4E])]));
qed "DmdOr";

Goal "|- (EX x. <>(F x)) = (<>(EX x. F x))";
by (auto_tac (temp_css addsimps2 [dmd_def,Not_Rex,all_box]));
qed "exT";

bind_thm("ex_dmd", standard((temp_unlift exT) RS sym));
	     

Goal "!!sigma. [| sigma |= []A; sigma |= []F; |- F & []A --> G |] ==> sigma |= []G";
by (etac dup_boxE 1);
by (merge_box_tac 1);
by (etac STL4E 1);
by (atac 1);
qed "STL4Edup";

Goalw [dmd_def]
   "!!sigma. [| sigma |= <>F; sigma |= [](F --> G) |] ==> sigma |= <>G";
by Auto_tac;
by (etac notE 1);
by (merge_box_tac 1);
by (fast_tac (temp_cs addSEs [STL4E]) 1);
qed "DmdImpl2";

val [prem1,prem2,prem3] = goal thy
  "[| sigma |= []<>F; sigma |= []G; |- F & G --> H |] ==> sigma |= []<>H";
by (cut_facts_tac [prem1,prem2] 1);
by (eres_inst_tac [("F","G")] dup_boxE 1);
by (merge_box_tac 1);
by (fast_tac (temp_cs addSEs [STL4E,DmdImpl2] addSIs [prem3]) 1);
qed "InfImpl";

(* ------------------------ STL6 ------------------------------------------- *)
(* Used in the proof of STL6, but useful in itself. *)
Goalw [dmd_def] "|- []F & <>G --> <>([]F & G)";
by (Clarsimp_tac 1);
by (etac dup_boxE 1);
by (merge_box_tac 1);
by (etac contrapos_np 1);
by (fast_tac (temp_cs addSEs [STL4E]) 1);
qed "BoxDmd";

(* weaker than BoxDmd, but more polymorphic (and often just right) *)
Goalw [dmd_def] "|- []F & <>G --> <>(F & G)";
by (Clarsimp_tac 1);
by (merge_box_tac 1);
by (fast_tac (temp_cs addSEs [notE,STL4E]) 1);
qed "BoxDmd_simple";

Goalw [dmd_def] "|- []F & <>G --> <>(G & F)";
by (Clarsimp_tac 1);
by (merge_box_tac 1);
by (fast_tac (temp_cs addSEs [notE,STL4E]) 1);
qed "BoxDmd2_simple";

val [p1,p2,p3] = goal thy
   "[| sigma |= []A; sigma |= <>F; |- []A & F --> G |] ==> sigma |= <>G";
by (rtac ((p2 RS (p1 RS (temp_use BoxDmd))) RS DmdImplE) 1);
by (rtac p3 1);
qed "DmdImpldup";

Goal "|- <>[]F & <>[]G --> <>[](F & G)";
by (auto_tac (temp_css addsimps2 [symmetric (temp_rewrite STL5)]));
by (dtac (temp_use linT) 1);
by (atac 1); 
by (etac thin_rl 1);
by (rtac ((temp_unlift DmdDmd) RS iffD1) 1);
by (etac disjE 1);
by (etac DmdImplE 1);
by (rtac BoxDmd 1);
by (etac DmdImplE 1);
by Auto_tac;
by (dtac (temp_use BoxDmd) 1); 
by (atac 1); 
by (etac thin_rl 1);
by (fast_tac (temp_cs addSEs [DmdImplE]) 1);
qed "STL6";


(* ------------------------ True / False ----------------------------------------- *)
section "Simplification of constants";

Goal "|- ([]#P) = #P";
by (rtac tempI 1);
by (case_tac "P" 1);
by (auto_tac (temp_css addSIs2 [necT] addDs2 [STL2_gen] 
                       addsimps2 Init_simps));
qed "BoxConst";

Goalw [dmd_def] "|- (<>#P) = #P";
by (case_tac "P" 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [BoxConst])));
qed "DmdConst";

val temp_simps = map temp_rewrite [BoxConst, DmdConst];

(* Make these rewrites active by default *)
Addsimps temp_simps;
val temp_css = temp_css addsimps2 temp_simps;
val temp_cs = op addss temp_css;


(* ------------------------ Further rewrites ----------------------------------------- *)
section "Further rewrites";

Goalw [dmd_def] "|- (~[]F) = (<>~F)";
by (Simp_tac 1);
qed "NotBox";

Goalw [dmd_def] "|- (~<>F) = ([]~F)";
by (Simp_tac 1);
qed "NotDmd";

(* These are not by default included in temp_css, because they could be harmful,
   e.g. []F & ~[]F becomes []F & <>~F !! *)
val more_temp_simps =  (map temp_rewrite [STL3, DmdDmd, NotBox, NotDmd])
                       @ (map (fn th => (temp_unlift th) RS eq_reflection)
		         [NotBox, NotDmd]);

Goal "|- ([]<>[]F) = (<>[]F)";
by (auto_tac (temp_css addSDs2 [STL2]));
by (rtac ccontr 1);
by (subgoal_tac "sigma |= <>[][]F & <>[]~[]F" 1);
by (etac thin_rl 1);
by Auto_tac;
by (dtac (temp_use STL6) 1); 
by (atac 1);
by (Asm_full_simp_tac 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps more_temp_simps)));
qed "BoxDmdBox";

Goalw [dmd_def] "|- (<>[]<>F) = ([]<>F)";
by (auto_tac (temp_css addsimps2 [rewrite_rule [dmd_def] BoxDmdBox]));
qed "DmdBoxDmd";

val more_temp_simps = more_temp_simps @ (map temp_rewrite [BoxDmdBox, DmdBoxDmd]);


(* ------------------------ Miscellaneous ----------------------------------- *)

Goal "!!sigma. [| sigma |= []F | []G |] ==> sigma |= [](F | G)";
by (fast_tac (temp_cs addSEs [STL4E]) 1);
qed "BoxOr";

(* "persistently implies infinitely often" *)
Goal "|- <>[]F --> []<>F";
by (Clarsimp_tac 1);
by (rtac ccontr 1);
by (asm_full_simp_tac (simpset() addsimps more_temp_simps) 1);
by (dtac (temp_use STL6) 1); 
by (atac 1);
by (Asm_full_simp_tac 1);
qed "DBImplBD";

Goal "|- []<>F & <>[]G --> []<>(F & G)";
by (Clarsimp_tac 1);
by (rtac ccontr 1);
by (rewrite_goals_tac more_temp_simps);
by (dtac (temp_use STL6) 1);
by (atac 1);
by (subgoal_tac "sigma |= <>[]~F" 1);
 by (force_tac (temp_css addsimps2 [dmd_def]) 1);
by (fast_tac (temp_cs addEs [DmdImplE,STL4E]) 1);
qed "BoxDmdDmdBox";


(* ------------------------------------------------------------------------- *)
(***          TLA-specific theorems: primed formulas                       ***)
(* ------------------------------------------------------------------------- *)
section "priming";

(* ------------------------ TLA2 ------------------------------------------- *)
Goal "|- []P --> Init P & Init P`";
by (fast_tac (temp_cs addSIs [primeI, STL2_gen]) 1);
qed "STL2_pr";

(* Auxiliary lemma allows priming of boxed actions *)
Goal "|- []P --> []($P & P$)";
by (Clarsimp_tac 1);
by (etac dup_boxE 1);
by (rewtac boxInit_act);
by (etac STL4E 1);
by (auto_tac (temp_css addsimps2 Init_simps addSDs2 [STL2_pr]));
qed "BoxPrime";

val prems = goal thy "|- $P & P$ --> A  ==>  |- []P --> []A";
by (Clarsimp_tac 1);
by (dtac (temp_use BoxPrime) 1);
by (auto_tac (temp_css addsimps2 [Init_stp_act_rev] 
                       addSIs2 prems addSEs2 [STL4E]));
qed "TLA2";

val prems = goal thy 
  "[| sigma |= []P; |- $P & P$ --> A |] ==> sigma |= []A";
by (REPEAT (resolve_tac (prems @ (prems RL [temp_use TLA2])) 1));
qed "TLA2E";

Goalw [dmd_def] "|- (<>P`) --> (<>P)";
by (fast_tac (temp_cs addSEs [TLA2E]) 1);
qed "DmdPrime";

bind_thm("PrimeDmd", (temp_use InitDmd_gen) RS (temp_use DmdPrime));

(* ------------------------ INV1, stable --------------------------------------- *)
section "stable, invariant";

val prems = goal thy
   "[| sigma |= []H; sigma |= Init P; |- H --> (Init P & ~[]F --> Init(P`) & F) |] \
\   ==> sigma |= []F";
by (rtac (temp_use indT) 1);
by (REPEAT (resolve_tac (prems @ (prems RL [STL4E])) 1));
qed "ind_rule";

Goalw [boxInit_act] "|- ([]$P) = ([]P)";
by (simp_tac (simpset() addsimps Init_simps) 1);
qed "box_stp_act";
bind_thm("box_stp_actI", zero_var_indexes ((temp_use box_stp_act) RS iffD2));
bind_thm("box_stp_actD", zero_var_indexes ((temp_use box_stp_act) RS iffD1));

val more_temp_simps = (temp_rewrite box_stp_act)::more_temp_simps;

Goalw [stable_def,boxInit_stp,boxInit_act] 
  "|- (Init P) --> (stable P) --> []P";
by (Clarsimp_tac 1);
by (etac ind_rule 1);
by (auto_tac (temp_css addsimps2 Init_simps addEs2 [ind_rule]));
qed "INV1";

Goalw [stable_def]
   "!!P. |- $P & A --> P` ==> |- []A --> stable P";
by (fast_tac (temp_cs addSEs [STL4E]) 1);
qed "StableT";

val prems = goal thy
   "[| sigma |= []A; |- $P & A --> P` |] ==> sigma |= stable P";
by (REPEAT (resolve_tac (prems @ [temp_use StableT]) 1));
qed "Stable";

(* Generalization of INV1 *)
Goalw [stable_def] "|- (stable P) --> [](Init P --> []P)";
by (Clarsimp_tac 1);
by (etac dup_boxE 1);
by (force_tac (temp_css addsimps2 [stable_def] addEs2 [STL4E, INV1]) 1);
qed "StableBox";

Goal "|- (stable P) & <>P --> <>[]P";
by (Clarsimp_tac 1);
by (rtac DmdImpl2 1);
by (etac (temp_use StableBox) 2);
by (asm_simp_tac (simpset() addsimps [dmdInitD]) 1);
qed "DmdStable";

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


Goalw [dmd_def] "|- []($P --> P` | Q`) --> (stable P) | <>Q";
by (clarsimp_tac (temp_css addSDs2 [BoxPrime]) 1);
by (merge_box_tac 1);
by (etac contrapos_np 1);
by (fast_tac (temp_cs addSEs [Stable]) 1);
qed "unless";


(* --------------------- Recursive expansions --------------------------------------- *)
section "recursive expansions";

(* Recursive expansions of [] and <> for state predicates *)
Goal "|- ([]P) = (Init P & []P`)";
by (auto_tac (temp_css addSIs2 [STL2_gen]));
by (fast_tac (temp_cs addSEs [TLA2E]) 1);
by (auto_tac (temp_css addsimps2 [stable_def] addSEs2 [INV1,STL4E]));
qed "BoxRec";

Goalw [dmd_def, temp_rewrite BoxRec] "|- (<>P) = (Init P | <>P`)";
by (auto_tac (temp_css addsimps2 Init_simps));
qed "DmdRec";

Goal "!!sigma. [| sigma |= <>P; sigma |= []~P` |] ==> sigma |= Init P";
by (force_tac (temp_css addsimps2 [DmdRec,dmd_def]) 1);
qed "DmdRec2";

Goal "|- ([]<>P) = ([]<>P`)";
by Auto_tac;
by (rtac classical 1);
by (rtac (temp_use DBImplBD) 1);
by (subgoal_tac "sigma |= <>[]P" 1);
 by (fast_tac (temp_cs addSEs [DmdImplE,TLA2E]) 1);
 by (subgoal_tac "sigma |= <>[](<>P & []~P`)" 1);
  by (force_tac (temp_css addsimps2 [boxInit_stp]
                          addSEs2 [DmdImplE,STL4E,DmdRec2]) 1);
 by (force_tac (temp_css addSIs2 [STL6] addsimps2 more_temp_simps) 1);
by (fast_tac (temp_cs addIs [DmdPrime] addSEs [STL4E]) 1);
qed "InfinitePrime";

val prems = goalw thy [temp_rewrite InfinitePrime]
  "[| sigma |= []N; sigma |= []<>A; |- A & N --> P` |] ==> sigma |= []<>P";
by (rtac InfImpl 1);
by (REPEAT (resolve_tac prems 1));
qed "InfiniteEnsures";

(* ------------------------ fairness ------------------------------------------- *)
section "fairness";

(* alternative definitions of fairness *)
Goalw [WF_def,dmd_def] 
  "|- WF(A)_v = ([]<>~Enabled(<A>_v) | []<><A>_v)";
by (fast_tac temp_cs 1);
qed "WF_alt";

Goalw [SF_def,dmd_def]
  "|- SF(A)_v = (<>[]~Enabled(<A>_v) | []<><A>_v)";
by (fast_tac temp_cs 1);
qed "SF_alt";

(* theorems to "box" fairness conditions *)
Goal "|- WF(A)_v --> []WF(A)_v";
by (auto_tac (temp_css addsimps2 (WF_alt::more_temp_simps) 
                       addSIs2 [BoxOr]));
qed "BoxWFI";

Goal "|- ([]WF(A)_v) = WF(A)_v";
by (fast_tac (temp_cs addSIs [BoxWFI] addSDs [STL2]) 1);
qed "WF_Box";

Goal "|- SF(A)_v --> []SF(A)_v";
by (auto_tac (temp_css addsimps2 (SF_alt::more_temp_simps) 
                       addSIs2 [BoxOr]));
qed "BoxSFI";

Goal "|- ([]SF(A)_v) = SF(A)_v";
by (fast_tac (temp_cs addSIs [BoxSFI] addSDs [STL2]) 1);
qed "SF_Box";

val more_temp_simps = more_temp_simps @ (map temp_rewrite [WF_Box, SF_Box]);

Goalw [SF_def,WF_def] "|- SF(A)_v --> WF(A)_v";
by (fast_tac (temp_cs addSDs [DBImplBD]) 1);
qed "SFImplWF";

(* A tactic that "boxes" all fairness conditions. Apply more_temp_simps to "unbox". *)
val box_fair_tac = SELECT_GOAL (REPEAT (dresolve_tac [BoxWFI,BoxSFI] 1));


(* ------------------------------ leads-to ------------------------------ *)

section "~>";

Goalw  [leadsto_def] "|- (Init F) & (F ~> G) --> <>G";
by (auto_tac (temp_css addSDs2 [STL2]));
qed "leadsto_init";

(* |- F & (F ~> G) --> <>G *)
bind_thm("leadsto_init_temp", 
         rewrite_rule Init_simps (read_instantiate [("'a","behavior")] leadsto_init));

Goalw [leadsto_def] "|- ([]<>Init F --> []<>G) = (<>(F ~> G))";
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps more_temp_simps) 1);
by (fast_tac (temp_cs addSEs [DmdImplE,STL4E]) 1);
by (fast_tac (temp_cs addSIs [InitDmd] addSEs [STL4E]) 1);
by (subgoal_tac "sigma |= []<><>G" 1);
by (asm_full_simp_tac (simpset() addsimps more_temp_simps) 1);
by (dtac (temp_use BoxDmdDmdBox) 1); 
by (atac 1);
by (fast_tac (temp_cs addSEs [DmdImplE,STL4E]) 1);
qed "streett_leadsto";

Goal "|- []<>F & (F ~> G) --> []<>G";
by (Clarsimp_tac 1);
by (etac ((temp_use InitDmd) RS 
          ((temp_unlift streett_leadsto) RS iffD2 RS mp)) 1);
by (asm_simp_tac (simpset() addsimps [dmdInitD]) 1);
qed "leadsto_infinite";

(* In particular, strong fairness is a Streett condition. The following
   rules are sometimes easier to use than WF2 or SF2 below.
*)
Goalw [SF_def] "|- (Enabled(<A>_v) ~> <A>_v) --> SF(A)_v";
by (clarsimp_tac (temp_css addSEs2 [leadsto_infinite]) 1);
qed "leadsto_SF";

Goal "|- (Enabled(<A>_v) ~> <A>_v) --> WF(A)_v";
by (clarsimp_tac (temp_css addSIs2 [SFImplWF, leadsto_SF]) 1);
qed "leadsto_WF";

(* introduce an invariant into the proof of a leadsto assertion.
   []I --> ((P ~> Q)  =  (P /\ I ~> Q))
*)
Goalw [leadsto_def] "|- []I & (P & I ~> Q) --> (P ~> Q)";
by (Clarsimp_tac 1);
by (etac STL4Edup 1); 
by (atac 1);
by (auto_tac (temp_css addsimps2 Init_simps addSDs2 [STL2_gen]));
qed "INV_leadsto";

Goalw [leadsto_def,dmd_def]
  "|- (Init F & []~G ~> G) --> (F ~> G)";
by (force_tac (temp_css addsimps2 Init_simps addSEs2 [STL4E]) 1);
qed "leadsto_classical";

Goalw [leadsto_def] "|- (F ~> #False) = ([]~F)";
by (simp_tac (simpset() addsimps [boxNotInitD]) 1);
qed "leadsto_false";

Goalw [leadsto_def] "|- ((EX x. F x) ~> G) = (ALL x. (F x ~> G))";
by (auto_tac (temp_css addsimps2 allT::Init_simps addSEs2 [STL4E]));
qed "leadsto_exists";

(* basic leadsto properties, cf. Unity *)

Goalw [leadsto_def] "|- [](Init F --> Init G) --> (F ~> G)";
by (auto_tac (temp_css addSIs2 [InitDmd_gen] addSEs2 [STL4E_gen]
                       addsimps2 Init_simps));
qed "ImplLeadsto_gen";

bind_thm("ImplLeadsto",
         rewrite_rule Init_simps 
             (read_instantiate [("'a","behavior"), ("'b","behavior")] ImplLeadsto_gen));

Goal "!!F G. |- F --> G ==> |- F ~> G";
by (auto_tac (temp_css addsimps2 [Init_def] 
                       addSIs2 [ImplLeadsto_gen,necT]));
qed "ImplLeadsto_simple";

val [prem] = goalw thy [leadsto_def]
  "|- A & $P --> Q` ==> |- []A --> (P ~> Q)";
by (clarsimp_tac (temp_css addSEs2 [INV_leadsto]) 1); 
by (etac STL4E_gen 1);
by (auto_tac (temp_css addsimps2 Init_defs addSIs2 [PrimeDmd,prem]));
qed "EnsuresLeadsto";

Goalw  [leadsto_def] "|- []($P --> Q`) --> (P ~> Q)";
by (Clarsimp_tac 1);
by (etac STL4E_gen 1);
by (auto_tac (temp_css addsimps2 Init_simps addSIs2 [PrimeDmd]));
qed "EnsuresLeadsto2";

val [p1,p2] = goalw thy [leadsto_def]
  "[| |- $P & N --> P` | Q`; \
\     |- ($P & N) & A --> Q` \
\  |] ==> |- []N & []([]P --> <>A) --> (P ~> Q)";
by (Clarsimp_tac 1);
by (etac STL4Edup 1); 
by (atac 1);
by (Clarsimp_tac 1);
by (subgoal_tac "sigmaa |= []($P --> P` | Q`)" 1);
 by (dtac (temp_use unless) 1);
 by (clarsimp_tac (temp_css addSDs2 [INV1]) 1);
 by (rtac ((temp_use (p2 RS DmdImpl)) RS (temp_use DmdPrime)) 1);
 by (force_tac (temp_css addSIs2 [BoxDmd_simple]
                         addsimps2 [split_box_conj,box_stp_act]) 1);
by (force_tac (temp_css addEs2 [STL4E] addDs2 [p1]) 1);
qed "ensures";

val prems = goal thy
  "[| |- $P & N --> P` | Q`; \
\     |- ($P & N) & A --> Q` \
\  |] ==> |- []N & []<>A --> (P ~> Q)";
by (Clarsimp_tac 1);
by (rtac (temp_use ensures) 1);
by (TRYALL (ares_tac prems));
by (force_tac (temp_css addSEs2 [STL4E]) 1);
qed "ensures_simple";

val prems = goal thy
  "[| sigma |= []<>P; sigma |= []A; |- A & $P --> Q` |] ==> sigma |= []<>Q";
by (REPEAT (resolve_tac (prems @ 
                         (map temp_use [leadsto_infinite, EnsuresLeadsto])) 1));
qed "EnsuresInfinite";


(*** Gronning's lattice rules (taken from TLP) ***)
section "Lattice rules";

Goalw [leadsto_def] "|- F ~> F";
by (REPEAT (resolve_tac [necT,InitDmd_gen] 1));
qed "LatticeReflexivity";

Goalw [leadsto_def] "|- (G ~> H) & (F ~> G) --> (F ~> H)";
by (Clarsimp_tac 1);
by (etac dup_boxE 1);  (* [][](Init G --> H) *)
by (merge_box_tac 1);
by (clarsimp_tac (temp_css addSEs2 [STL4E]) 1);
by (rtac dup_dmdD 1);
by (subgoal_tac "sigmaa |= <>Init G" 1);
 by (etac DmdImpl2 1); 
 by (atac 1);
by (asm_simp_tac (simpset() addsimps [dmdInitD]) 1);
qed "LatticeTransitivity";

Goalw [leadsto_def] "|- (F | G ~> H) --> (F ~> H)";
by (auto_tac (temp_css addsimps2 Init_simps addSEs2 [STL4E]));
qed "LatticeDisjunctionElim1";

Goalw [leadsto_def] "|- (F | G ~> H) --> (G ~> H)";
by (auto_tac (temp_css addsimps2 Init_simps addSEs2 [STL4E]));
qed "LatticeDisjunctionElim2";

Goalw [leadsto_def] "|- (F ~> H) & (G ~> H) --> (F | G ~> H)";
by (Clarsimp_tac 1);
by (merge_box_tac 1);
by (auto_tac (temp_css addsimps2 Init_simps addSEs2 [STL4E]));
qed "LatticeDisjunctionIntro";

Goal "|- (F | G ~> H) = ((F ~> H) & (G ~> H))";
by (auto_tac (temp_css addIs2 [LatticeDisjunctionIntro,
                               LatticeDisjunctionElim1, LatticeDisjunctionElim2]));
qed "LatticeDisjunction";

Goal "|- (A ~> B | C) & (B ~> D) & (C ~> D) --> (A ~> D)";
by (Clarsimp_tac 1);
by (subgoal_tac "sigma |= (B | C) ~> D" 1);
by (eres_inst_tac [("G", "LIFT (B | C)")] (temp_use LatticeTransitivity) 1);
by (ALLGOALS (fast_tac (temp_cs addSIs [LatticeDisjunctionIntro])));
qed "LatticeDiamond";

Goal "|- (A ~> D | B) & (B ~> D) --> (A ~> D)";
by (Clarsimp_tac 1);
by (subgoal_tac "sigma |= (D | B) ~> D" 1);
by (eres_inst_tac [("G", "LIFT (D | B)")] (temp_use LatticeTransitivity) 1); 
by (atac 1);
by (auto_tac (temp_css addIs2 [LatticeDisjunctionIntro,LatticeReflexivity]));
qed "LatticeTriangle";

Goal "|- (A ~> B | D) & (B ~> D) --> (A ~> D)";
by (Clarsimp_tac 1);
by (subgoal_tac "sigma |= B | D ~> D" 1);
by (eres_inst_tac [("G", "LIFT (B | D)")] (temp_use LatticeTransitivity) 1); 
by (atac 1);
by (auto_tac (temp_css addIs2 [LatticeDisjunctionIntro,LatticeReflexivity]));
qed "LatticeTriangle2";

(*** Lamport's fairness rules ***)
section "Fairness rules";

val prems = goal thy
  "[| |- $P & N  --> P` | Q`;   \
\     |- ($P & N) & <A>_v --> Q`;   \
\     |- $P & N --> $(Enabled(<A>_v)) |]   \
\ ==> |- []N & WF(A)_v --> (P ~> Q)";
by (clarsimp_tac (temp_css addSDs2 [BoxWFI]) 1);
by (rtac (temp_use ensures) 1);
by (TRYALL (ares_tac prems));
by (etac STL4Edup 1); 
by (atac 1);
by (clarsimp_tac (temp_css addsimps2 [WF_def]) 1);
by (rtac (temp_use STL2) 1);
by (clarsimp_tac (temp_css addSEs2 [mp] addSIs2 [InitDmd]) 1);
by (resolve_tac ((map temp_use (prems RL [STL4])) RL [box_stp_actD]) 1);
by (asm_simp_tac (simpset() addsimps [split_box_conj,box_stp_actI]) 1);
qed "WF1";

(* Sometimes easier to use; designed for action B rather than state predicate Q *)
val [prem1,prem2,prem3] = goalw thy [leadsto_def]
  "[| |- N & $P --> $Enabled (<A>_v);            \
\     |- N & <A>_v --> B;                  \ 
\     |- [](N & [~A]_v) --> stable P  |]  \
\  ==> |- []N & WF(A)_v --> (P ~> B)";
by (clarsimp_tac (temp_css addSDs2 [BoxWFI]) 1);
by (etac STL4Edup 1); 
by (atac 1);
by (Clarsimp_tac 1);
by (rtac (temp_use (prem2 RS DmdImpl)) 1);
by (rtac (temp_use BoxDmd_simple) 1); 
by (atac 1);
by (rtac classical 1);
by (rtac (temp_use STL2) 1);
by (clarsimp_tac (temp_css addsimps2 [WF_def] addSEs2 [mp] addSIs2 [InitDmd]) 1);
by (rtac ((temp_use (prem1 RS STL4)) RS box_stp_actD) 1);
by (asm_simp_tac (simpset() addsimps [split_box_conj,box_stp_act]) 1);
by (etac (temp_use INV1) 1);
by (rtac (temp_use prem3) 1);
by (asm_full_simp_tac (simpset() addsimps [split_box_conj,temp_use NotDmd,not_angle]) 1);
qed "WF_leadsto";

val prems = goal thy
  "[| |- $P & N  --> P` | Q`;   \
\     |- ($P & N) & <A>_v --> Q`;   \
\     |- []P & []N & []F --> <>Enabled(<A>_v) |]   \
\ ==> |- []N & SF(A)_v & []F --> (P ~> Q)";
by (clarsimp_tac (temp_css addSDs2 [BoxSFI]) 1);
by (rtac (temp_use ensures) 1);
by (TRYALL (ares_tac prems));
by (eres_inst_tac [("F","F")] dup_boxE 1);
by (merge_temp_box_tac 1);
by (etac STL4Edup 1); 
by (atac 1);
by (clarsimp_tac (temp_css addsimps2 [SF_def]) 1);
by (rtac (temp_use STL2) 1); 
by (etac mp 1);
by (resolve_tac (map temp_use (prems RL [STL4])) 1);
by (asm_simp_tac (simpset() addsimps [split_box_conj, STL3]) 1);
qed "SF1";

val [prem1,prem2,prem3,prem4] = goal thy
  "[| |- N & <B>_f --> <M>_g;   \
\     |- $P & P` & <N & A>_f --> B;   \
\     |- P & Enabled(<M>_g) --> Enabled(<A>_f);   \
\     |- [](N & [~B]_f) & WF(A)_f & []F & <>[]Enabled(<M>_g) --> <>[]P |]   \
\ ==> |- []N & WF(A)_f & []F --> WF(M)_g";
by (clarsimp_tac (temp_css addSDs2 [BoxWFI, (temp_use BoxDmdBox) RS iffD2] 
                           addsimps2 [read_instantiate [("A","M")] WF_def]) 1);
by (eres_inst_tac [("F","F")] dup_boxE 1);
by (merge_temp_box_tac 1);
by (etac STL4Edup 1); 
by (atac 1);
by (clarsimp_tac (temp_css addSIs2
         [(temp_use BoxDmd_simple) RS (temp_use (prem1 RS DmdImpl))]) 1);
by (rtac classical 1);
by (subgoal_tac "sigmaa |= <>(($P & P` & N) & <A>_f)" 1);
 by (force_tac (temp_css addsimps2 [angle_def] addSIs2 [prem2] addSEs2 [DmdImplE]) 1);
by (rtac (temp_use (rewrite_rule [temp_rewrite DmdDmd] (BoxDmd_simple RS DmdImpl))) 1);
by (asm_full_simp_tac (simpset() addsimps [temp_use NotDmd, not_angle]) 1);
by (merge_act_box_tac 1);
by (forward_tac [temp_use prem4] 1); 
by (TRYALL atac);
by (dtac (temp_use STL6) 1); 
by (atac 1);
by (eres_inst_tac [("V","sigmaa |= <>[]P")] thin_rl 1);
by (eres_inst_tac [("V","sigmaa |= []F")] thin_rl 1);
by (dtac (temp_use BoxWFI) 1);
by (eres_inst_tac [("F", "ACT N & [~B]_f")] dup_boxE 1);
by (merge_temp_box_tac 1);
by (etac DmdImpldup 1); 
by (atac 1);
by (auto_tac (temp_css addsimps2 [split_box_conj,STL3,WF_Box,box_stp_act]));
 by (force_tac (temp_css addSEs2 [read_instantiate [("P","P")] TLA2E]) 1);
by (rtac (temp_use STL2) 1);
by (force_tac (temp_css addsimps2 [WF_def,split_box_conj] addSEs2 [mp] 
                        addSIs2 [InitDmd, prem3 RS STL4]) 1);
qed "WF2";

val [prem1,prem2,prem3,prem4] = goal thy
  "[| |- N & <B>_f --> <M>_g;   \
\     |- $P & P` & <N & A>_f --> B;   \
\     |- P & Enabled(<M>_g) --> Enabled(<A>_f);   \
\     |- [](N & [~B]_f) & SF(A)_f & []F & []<>Enabled(<M>_g) --> <>[]P |]   \
\ ==> |- []N & SF(A)_f & []F --> SF(M)_g";
by (clarsimp_tac (temp_css addSDs2 [BoxSFI] 
                           addsimps2 [read_instantiate [("A","M")] SF_def]) 1);
by (eres_inst_tac [("F","F")] dup_boxE 1);
by (eres_inst_tac [("F","TEMP <>Enabled(<M>_g)")] dup_boxE 1);
by (merge_temp_box_tac 1);
by (etac STL4Edup 1); 
by (atac 1);
by (clarsimp_tac (temp_css addSIs2
        [(temp_use BoxDmd_simple) RS (temp_use (prem1 RS DmdImpl))]) 1);
by (rtac classical 1);
by (subgoal_tac "sigmaa |= <>(($P & P` & N) & <A>_f)" 1);
 by (force_tac (temp_css addsimps2 [angle_def] addSIs2 [prem2] addSEs2 [DmdImplE]) 1);
by (rtac (temp_use (rewrite_rule [temp_rewrite DmdDmd] (BoxDmd_simple RS DmdImpl))) 1);
by (asm_full_simp_tac (simpset() addsimps [temp_use NotDmd, not_angle]) 1);
by (merge_act_box_tac 1);
by (forward_tac [temp_use prem4] 1); 
by (TRYALL atac);
by (eres_inst_tac [("V","sigmaa |= []F")] thin_rl 1);
by (dtac (temp_use BoxSFI) 1);
by (eres_inst_tac [("F","TEMP <>Enabled(<M>_g)")] dup_boxE 1);
by (eres_inst_tac [("F", "ACT N & [~B]_f")] dup_boxE 1);
by (merge_temp_box_tac 1);
by (etac DmdImpldup 1); 
by (atac 1);
by (auto_tac (temp_css addsimps2 [split_box_conj,STL3,SF_Box,box_stp_act]));
 by (force_tac (temp_css addSEs2 [read_instantiate [("P","P")] TLA2E]) 1);
by (rtac (temp_use STL2) 1);
by (force_tac (temp_css addsimps2 [SF_def,split_box_conj] addSEs2 [mp,InfImpl] 
                        addSIs2 [prem3]) 1);
qed "SF2";

(* ------------------------------------------------------------------------- *)
(***           Liveness proofs by well-founded orderings                   ***)
(* ------------------------------------------------------------------------- *)
section "Well-founded orderings";

val p1::prems = goal thy
  "[| wf r;  \
\     !!x. sigma |= F x ~> (G | (EX y. #((y,x):r) & F y))   \
\  |] ==> sigma |= F x ~> G";
by (rtac (p1 RS wf_induct) 1);
by (rtac (temp_use LatticeTriangle) 1);
by (resolve_tac prems 1);
by (auto_tac (temp_css addsimps2 [leadsto_exists]));
by (case_tac "(y,x):r" 1);
 by (Force_tac 1);
by (force_tac (temp_css addsimps2 leadsto_def::Init_simps addSIs2 [necT]) 1);
qed "wf_leadsto";

(* If r is well-founded, state function v cannot decrease forever *)
Goal "!!r. wf r ==> |- [][ (v`, $v) : #r ]_v --> <>[][#False]_v";
by (Clarsimp_tac 1);
by (rtac ccontr 1);
by (subgoal_tac "sigma |= (EX x. v=#x) ~> #False" 1);
 by (dtac ((temp_use leadsto_false) RS iffD1 RS (temp_use STL2_gen)) 1);
 by (force_tac (temp_css addsimps2 Init_defs) 1);
by (clarsimp_tac (temp_css addsimps2 [leadsto_exists,not_square]@more_temp_simps) 1);
by (etac wf_leadsto 1);
by (rtac (temp_use ensures_simple) 1); 
by (TRYALL atac);
by (auto_tac (temp_css addsimps2 [square_def,angle_def]));
qed "wf_not_box_decrease";

(* "wf r  ==>  |- <>[][ (v`, $v) : #r ]_v --> <>[][#False]_v" *)
bind_thm("wf_not_dmd_box_decrease",
         standard(rewrite_rule more_temp_simps (wf_not_box_decrease RS DmdImpl)));

(* If there are infinitely many steps where v decreases, then there
   have to be infinitely many non-stuttering steps where v doesn't decrease.
*)
val [prem] = goal thy
  "wf r ==> |- []<>((v`, $v) : #r) --> []<><(v`, $v) ~: #r>_v";
by (Clarsimp_tac 1);
by (rtac ccontr 1);
by (asm_full_simp_tac (simpset() addsimps not_angle::more_temp_simps) 1);
by (dtac (prem RS (temp_use wf_not_dmd_box_decrease)) 1);
by (dtac (temp_use BoxDmdDmdBox) 1); 
by (atac 1);
by (subgoal_tac "sigma |= []<>((#False)::action)" 1);
 by (Force_tac 1);
by (etac STL4E 1);
by (rtac DmdImpl 1);
by (force_tac (temp_css addIs2 [prem RS wf_irrefl]) 1);
qed "wf_box_dmd_decrease";

(* In particular, for natural numbers, if n decreases infinitely often
   then it has to increase infinitely often.
*)
Goal "!!n::nat stfun. |- []<>(n` < $n) --> []<>($n < n`)";
by (Clarsimp_tac 1);
by (subgoal_tac "sigma |= []<><~( (n`,$n) : #less_than )>_n" 1);
 by (etac thin_rl 1); 
 by (etac STL4E 1); 
 by (rtac DmdImpl 1);
 by (clarsimp_tac (temp_css addsimps2 [angle_def]) 1);
 by (rtac nat_less_cases 1);
 by Auto_tac;
by (rtac (temp_use wf_box_dmd_decrease) 1);
by (auto_tac (temp_css addSEs2 [STL4E,DmdImplE]));
qed "nat_box_dmd_decrease";


(* ------------------------------------------------------------------------- *)
(***           Flexible quantification over state variables                ***)
(* ------------------------------------------------------------------------- *)
section "Flexible quantification";

val [prem1,prem2] = goal thy
  "[| basevars vs; (!!x. basevars (x,vs) ==> sigma |= F x) |]\
\  ==> sigma |= (AALL x. F x)";
by (auto_tac (temp_css addsimps2 [aall_def] addSEs2 [eexE] 
                       addSIs2 [prem1] addSDs2 [prem2]));
qed "aallI";

Goalw [aall_def] "|- (AALL x. F x) --> F x";
by (Clarsimp_tac 1);
by (etac contrapos_np 1);
by (force_tac (temp_css addSIs2 [eexI]) 1);
qed "aallE";

(* monotonicity of quantification *)
val [min,maj] = goal thy
  "[| sigma |= EEX x. F x; !!x. sigma |= F x --> G x |] ==> sigma |= EEX x. G x";
by (rtac (unit_base RS (min RS eexE)) 1);
by (rtac (temp_use eexI) 1);
by (etac ((rewrite_rule intensional_rews maj) RS mp) 1);
qed "eex_mono";

val [min,maj] = goal thy
  "[| sigma |= AALL x. F(x); !!x. sigma |= F(x) --> G(x) |] ==> sigma |= AALL x. G(x)";
by (rtac (unit_base RS aallI) 1);
by (rtac ((rewrite_rule intensional_rews maj) RS mp) 1);
by (rtac (min RS (temp_use aallE)) 1);
qed "aall_mono";

(* Derived history introduction rule *)
val [p1,p2,p3,p4,p5] = goal thy
  "[| sigma |= Init I; sigma |= []N; basevars vs; \
\     (!!h. basevars(h,vs) ==> |- I & h = ha --> HI h); \
\     (!!h s t. [| basevars(h,vs); N (s,t); h t = hb (h s) (s,t) |] ==> HN h (s,t)) \
\  |] ==> sigma |= EEX h. Init (HI h) & [](HN h)";
by (rtac ((temp_use history) RS eexE) 1);
 by (rtac p3 1);
by (rtac (temp_use eexI) 1);
by (Clarsimp_tac 1); 
by (rtac conjI 1);
by (cut_facts_tac [p2] 2);
by (merge_box_tac 2);
by (force_tac (temp_css addSEs2 [STL4E,p5]) 2);
by (cut_facts_tac [p1] 1);
by (force_tac (temp_css addsimps2 Init_defs addSEs2 [p4]) 1);
qed "historyI";

(* ----------------------------------------------------------------------
   example of a history variable: existence of a clock

Goal "|- EEX h. Init(h = #True) & [](h` = (~$h))";
by (rtac tempI 1);
by (rtac historyI 1);
by (REPEAT (force_tac (temp_css addsimps2 Init_defs addIs2 [unit_base, necT]) 1));
(** solved **)

---------------------------------------------------------------------- *)
