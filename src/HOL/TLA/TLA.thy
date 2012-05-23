(*  Title:      HOL/TLA/TLA.thy
    Author:     Stephan Merz
    Copyright:  1998 University of Munich
*)

header {* The temporal level of TLA *}

theory TLA
imports Init
begin

consts
  (** abstract syntax **)
  Box        :: "('w::world) form => temporal"
  Dmd        :: "('w::world) form => temporal"
  leadsto    :: "['w::world form, 'v::world form] => temporal"
  Stable     :: "stpred => temporal"
  WF         :: "[action, 'a stfun] => temporal"
  SF         :: "[action, 'a stfun] => temporal"

  (* Quantification over (flexible) state variables *)
  EEx        :: "('a stfun => temporal) => temporal"       (binder "Eex " 10)
  AAll       :: "('a stfun => temporal) => temporal"       (binder "Aall " 10)

  (** concrete syntax **)
syntax
  "_Box"     :: "lift => lift"                        ("([]_)" [40] 40)
  "_Dmd"     :: "lift => lift"                        ("(<>_)" [40] 40)
  "_leadsto" :: "[lift,lift] => lift"                 ("(_ ~> _)" [23,22] 22)
  "_stable"  :: "lift => lift"                        ("(stable/ _)")
  "_WF"      :: "[lift,lift] => lift"                 ("(WF'(_')'_(_))" [0,60] 55)
  "_SF"      :: "[lift,lift] => lift"                 ("(SF'(_')'_(_))" [0,60] 55)

  "_EEx"     :: "[idts, lift] => lift"                ("(3EEX _./ _)" [0,10] 10)
  "_AAll"    :: "[idts, lift] => lift"                ("(3AALL _./ _)" [0,10] 10)

translations
  "_Box"      ==   "CONST Box"
  "_Dmd"      ==   "CONST Dmd"
  "_leadsto"  ==   "CONST leadsto"
  "_stable"   ==   "CONST Stable"
  "_WF"       ==   "CONST WF"
  "_SF"       ==   "CONST SF"
  "_EEx v A"  ==   "Eex v. A"
  "_AAll v A" ==   "Aall v. A"

  "sigma |= []F"         <= "_Box F sigma"
  "sigma |= <>F"         <= "_Dmd F sigma"
  "sigma |= F ~> G"      <= "_leadsto F G sigma"
  "sigma |= stable P"    <= "_stable P sigma"
  "sigma |= WF(A)_v"     <= "_WF A v sigma"
  "sigma |= SF(A)_v"     <= "_SF A v sigma"
  "sigma |= EEX x. F"    <= "_EEx x F sigma"
  "sigma |= AALL x. F"    <= "_AAll x F sigma"

syntax (xsymbols)
  "_Box"     :: "lift => lift"                        ("(\<box>_)" [40] 40)
  "_Dmd"     :: "lift => lift"                        ("(\<diamond>_)" [40] 40)
  "_leadsto" :: "[lift,lift] => lift"                 ("(_ \<leadsto> _)" [23,22] 22)
  "_EEx"     :: "[idts, lift] => lift"                ("(3\<exists>\<exists> _./ _)" [0,10] 10)
  "_AAll"    :: "[idts, lift] => lift"                ("(3\<forall>\<forall> _./ _)" [0,10] 10)

syntax (HTML output)
  "_EEx"     :: "[idts, lift] => lift"                ("(3\<exists>\<exists> _./ _)" [0,10] 10)
  "_AAll"    :: "[idts, lift] => lift"                ("(3\<forall>\<forall> _./ _)" [0,10] 10)

axiomatization where
  (* Definitions of derived operators *)
  dmd_def:      "\<And>F. TEMP <>F  ==  TEMP ~[]~F"

axiomatization where
  boxInit:      "\<And>F. TEMP []F  ==  TEMP []Init F" and
  leadsto_def:  "\<And>F G. TEMP F ~> G  ==  TEMP [](Init F --> <>G)" and
  stable_def:   "\<And>P. TEMP stable P  ==  TEMP []($P --> P$)" and
  WF_def:       "TEMP WF(A)_v  ==  TEMP <>[] Enabled(<A>_v) --> []<><A>_v" and
  SF_def:       "TEMP SF(A)_v  ==  TEMP []<> Enabled(<A>_v) --> []<><A>_v" and
  aall_def:     "TEMP (AALL x. F x)  ==  TEMP ~ (EEX x. ~ F x)"

axiomatization where
(* Base axioms for raw TLA. *)
  normalT:    "\<And>F G. |- [](F --> G) --> ([]F --> []G)" and    (* polymorphic *)
  reflT:      "\<And>F. |- []F --> F" and         (* F::temporal *)
  transT:     "\<And>F. |- []F --> [][]F" and     (* polymorphic *)
  linT:       "\<And>F G. |- <>F & <>G --> (<>(F & <>G)) | (<>(G & <>F))" and
  discT:      "\<And>F. |- [](F --> <>(~F & <>F)) --> (F --> []<>F)" and
  primeI:     "\<And>P. |- []P --> Init P`" and
  primeE:     "\<And>P F. |- [](Init P --> []F) --> Init P` --> (F --> []F)" and
  indT:       "\<And>P F. |- [](Init P & ~[]F --> Init P` & F) --> Init P --> []F" and
  allT:       "\<And>F. |- (ALL x. [](F x)) = ([](ALL x. F x))"

axiomatization where
  necT:       "\<And>F. |- F ==> |- []F"      (* polymorphic *)

axiomatization where
(* Flexible quantification: refinement mappings, history variables *)
  eexI:       "|- F x --> (EEX x. F x)" and
  eexE:       "[| sigma |= (EEX x. F x); basevars vs;
                 (!!x. [| basevars (x, vs); sigma |= F x |] ==> (G sigma)::bool)
              |] ==> G sigma" and
  history:    "|- EEX h. Init(h = ha) & [](!x. $h = #x --> h` = hb x)"


(* Specialize intensional introduction/elimination rules for temporal formulas *)

lemma tempI: "(!!sigma. sigma |= (F::temporal)) ==> |- F"
  apply (rule intI)
  apply (erule meta_spec)
  done

lemma tempD: "|- (F::temporal) ==> sigma |= F"
  by (erule intD)


(* ======== Functions to "unlift" temporal theorems ====== *)

ML {*
(* The following functions are specialized versions of the corresponding
   functions defined in theory Intensional in that they introduce a
   "world" parameter of type "behavior".
*)
fun temp_unlift th =
  (rewrite_rule @{thms action_rews} (th RS @{thm tempD})) handle THM _ => action_unlift th;

(* Turn  |- F = G  into meta-level rewrite rule  F == G *)
val temp_rewrite = int_rewrite

fun temp_use th =
  case (concl_of th) of
    Const _ $ (Const (@{const_name Intensional.Valid}, _) $ _) =>
            ((flatten (temp_unlift th)) handle THM _ => th)
  | _ => th;

fun try_rewrite th = temp_rewrite th handle THM _ => temp_use th;
*}

attribute_setup temp_unlift = {* Scan.succeed (Thm.rule_attribute (K temp_unlift)) *}
attribute_setup temp_rewrite = {* Scan.succeed (Thm.rule_attribute (K temp_rewrite)) *}
attribute_setup temp_use = {* Scan.succeed (Thm.rule_attribute (K temp_use)) *}
attribute_setup try_rewrite = {* Scan.succeed (Thm.rule_attribute (K try_rewrite)) *}


(* Update classical reasoner---will be updated once more below! *)

declare tempI [intro!]
declare tempD [dest]

(* Modify the functions that add rules to simpsets, classical sets,
   and clasimpsets in order to accept "lifted" theorems
*)

(* ------------------------------------------------------------------------- *)
(***           "Simple temporal logic": only [] and <>                     ***)
(* ------------------------------------------------------------------------- *)
section "Simple temporal logic"

(* []~F == []~Init F *)
lemmas boxNotInit = boxInit [of "LIFT ~F", unfolded Init_simps] for F

lemma dmdInit: "TEMP <>F == TEMP <> Init F"
  apply (unfold dmd_def)
  apply (unfold boxInit [of "LIFT ~F"])
  apply (simp (no_asm) add: Init_simps)
  done

lemmas dmdNotInit = dmdInit [of "LIFT ~F", unfolded Init_simps] for F

(* boxInit and dmdInit cannot be used as rewrites, because they loop.
   Non-looping instances for state predicates and actions are occasionally useful.
*)
lemmas boxInit_stp = boxInit [where 'a = state]
lemmas boxInit_act = boxInit [where 'a = "state * state"]
lemmas dmdInit_stp = dmdInit [where 'a = state]
lemmas dmdInit_act = dmdInit [where 'a = "state * state"]

(* The symmetric equations can be used to get rid of Init *)
lemmas boxInitD = boxInit [symmetric]
lemmas dmdInitD = dmdInit [symmetric]
lemmas boxNotInitD = boxNotInit [symmetric]
lemmas dmdNotInitD = dmdNotInit [symmetric]

lemmas Init_simps = Init_simps boxInitD dmdInitD boxNotInitD dmdNotInitD

(* ------------------------ STL2 ------------------------------------------- *)
lemmas STL2 = reflT

(* The "polymorphic" (generic) variant *)
lemma STL2_gen: "|- []F --> Init F"
  apply (unfold boxInit [of F])
  apply (rule STL2)
  done

(* see also STL2_pr below: "|- []P --> Init P & Init (P`)" *)


(* Dual versions for <> *)
lemma InitDmd: "|- F --> <> F"
  apply (unfold dmd_def)
  apply (auto dest!: STL2 [temp_use])
  done

lemma InitDmd_gen: "|- Init F --> <>F"
  apply clarsimp
  apply (drule InitDmd [temp_use])
  apply (simp add: dmdInitD)
  done


(* ------------------------ STL3 ------------------------------------------- *)
lemma STL3: "|- ([][]F) = ([]F)"
  by (auto elim: transT [temp_use] STL2 [temp_use])

(* corresponding elimination rule introduces double boxes:
   [| (sigma |= []F); (sigma |= [][]F) ==> PROP W |] ==> PROP W
*)
lemmas dup_boxE = STL3 [temp_unlift, THEN iffD2, elim_format]
lemmas dup_boxD = STL3 [temp_unlift, THEN iffD1]

(* dual versions for <> *)
lemma DmdDmd: "|- (<><>F) = (<>F)"
  by (auto simp add: dmd_def [try_rewrite] STL3 [try_rewrite])

lemmas dup_dmdE = DmdDmd [temp_unlift, THEN iffD2, elim_format]
lemmas dup_dmdD = DmdDmd [temp_unlift, THEN iffD1]


(* ------------------------ STL4 ------------------------------------------- *)
lemma STL4:
  assumes "|- F --> G"
  shows "|- []F --> []G"
  apply clarsimp
  apply (rule normalT [temp_use])
   apply (rule assms [THEN necT, temp_use])
  apply assumption
  done

(* Unlifted version as an elimination rule *)
lemma STL4E: "[| sigma |= []F; |- F --> G |] ==> sigma |= []G"
  by (erule (1) STL4 [temp_use])

lemma STL4_gen: "|- Init F --> Init G ==> |- []F --> []G"
  apply (drule STL4)
  apply (simp add: boxInitD)
  done

lemma STL4E_gen: "[| sigma |= []F; |- Init F --> Init G |] ==> sigma |= []G"
  by (erule (1) STL4_gen [temp_use])

(* see also STL4Edup below, which allows an auxiliary boxed formula:
       []A /\ F => G
     -----------------
     []A /\ []F => []G
*)

(* The dual versions for <> *)
lemma DmdImpl:
  assumes prem: "|- F --> G"
  shows "|- <>F --> <>G"
  apply (unfold dmd_def)
  apply (fastforce intro!: prem [temp_use] elim!: STL4E [temp_use])
  done

lemma DmdImplE: "[| sigma |= <>F; |- F --> G |] ==> sigma |= <>G"
  by (erule (1) DmdImpl [temp_use])

(* ------------------------ STL5 ------------------------------------------- *)
lemma STL5: "|- ([]F & []G) = ([](F & G))"
  apply auto
  apply (subgoal_tac "sigma |= [] (G --> (F & G))")
     apply (erule normalT [temp_use])
     apply (fastforce elim!: STL4E [temp_use])+
  done

(* rewrite rule to split conjunctions under boxes *)
lemmas split_box_conj = STL5 [temp_unlift, symmetric]


(* the corresponding elimination rule allows to combine boxes in the hypotheses
   (NB: F and G must have the same type, i.e., both actions or temporals.)
   Use "addSE2" etc. if you want to add this to a claset, otherwise it will loop!
*)
lemma box_conjE:
  assumes "sigma |= []F"
     and "sigma |= []G"
  and "sigma |= [](F&G) ==> PROP R"
  shows "PROP R"
  by (rule assms STL5 [temp_unlift, THEN iffD1] conjI)+

(* Instances of box_conjE for state predicates, actions, and temporals
   in case the general rule is "too polymorphic".
*)
lemmas box_conjE_temp = box_conjE [where 'a = behavior]
lemmas box_conjE_stp = box_conjE [where 'a = state]
lemmas box_conjE_act = box_conjE [where 'a = "state * state"]

(* Define a tactic that tries to merge all boxes in an antecedent. The definition is
   a bit kludgy in order to simulate "double elim-resolution".
*)

lemma box_thin: "[| sigma |= []F; PROP W |] ==> PROP W" .

ML {*
fun merge_box_tac i =
   REPEAT_DETERM (EVERY [etac @{thm box_conjE} i, atac i, etac @{thm box_thin} i])

fun merge_temp_box_tac ctxt i =
   REPEAT_DETERM (EVERY [etac @{thm box_conjE_temp} i, atac i,
                         eres_inst_tac ctxt [(("'a", 0), "behavior")] @{thm box_thin} i])

fun merge_stp_box_tac ctxt i =
   REPEAT_DETERM (EVERY [etac @{thm box_conjE_stp} i, atac i,
                         eres_inst_tac ctxt [(("'a", 0), "state")] @{thm box_thin} i])

fun merge_act_box_tac ctxt i =
   REPEAT_DETERM (EVERY [etac @{thm box_conjE_act} i, atac i,
                         eres_inst_tac ctxt [(("'a", 0), "state * state")] @{thm box_thin} i])
*}

method_setup merge_box = {* Scan.succeed (K (SIMPLE_METHOD' merge_box_tac)) *}
method_setup merge_temp_box = {* Scan.succeed (SIMPLE_METHOD' o merge_temp_box_tac) *}
method_setup merge_stp_box = {* Scan.succeed (SIMPLE_METHOD' o merge_stp_box_tac) *}
method_setup merge_act_box = {* Scan.succeed (SIMPLE_METHOD' o merge_act_box_tac) *}

(* rewrite rule to push universal quantification through box:
      (sigma |= [](! x. F x)) = (! x. (sigma |= []F x))
*)
lemmas all_box = allT [temp_unlift, symmetric]

lemma DmdOr: "|- (<>(F | G)) = (<>F | <>G)"
  apply (auto simp add: dmd_def split_box_conj [try_rewrite])
  apply (erule contrapos_np, merge_box, fastforce elim!: STL4E [temp_use])+
  done

lemma exT: "|- (EX x. <>(F x)) = (<>(EX x. F x))"
  by (auto simp: dmd_def Not_Rex [try_rewrite] all_box [try_rewrite])

lemmas ex_dmd = exT [temp_unlift, symmetric]

lemma STL4Edup: "!!sigma. [| sigma |= []A; sigma |= []F; |- F & []A --> G |] ==> sigma |= []G"
  apply (erule dup_boxE)
  apply merge_box
  apply (erule STL4E)
  apply assumption
  done

lemma DmdImpl2: 
    "!!sigma. [| sigma |= <>F; sigma |= [](F --> G) |] ==> sigma |= <>G"
  apply (unfold dmd_def)
  apply auto
  apply (erule notE)
  apply merge_box
  apply (fastforce elim!: STL4E [temp_use])
  done

lemma InfImpl:
  assumes 1: "sigma |= []<>F"
    and 2: "sigma |= []G"
    and 3: "|- F & G --> H"
  shows "sigma |= []<>H"
  apply (insert 1 2)
  apply (erule_tac F = G in dup_boxE)
  apply merge_box
  apply (fastforce elim!: STL4E [temp_use] DmdImpl2 [temp_use] intro!: 3 [temp_use])
  done

(* ------------------------ STL6 ------------------------------------------- *)
(* Used in the proof of STL6, but useful in itself. *)
lemma BoxDmd: "|- []F & <>G --> <>([]F & G)"
  apply (unfold dmd_def)
  apply clarsimp
  apply (erule dup_boxE)
  apply merge_box
  apply (erule contrapos_np)
  apply (fastforce elim!: STL4E [temp_use])
  done

(* weaker than BoxDmd, but more polymorphic (and often just right) *)
lemma BoxDmd_simple: "|- []F & <>G --> <>(F & G)"
  apply (unfold dmd_def)
  apply clarsimp
  apply merge_box
  apply (fastforce elim!: notE STL4E [temp_use])
  done

lemma BoxDmd2_simple: "|- []F & <>G --> <>(G & F)"
  apply (unfold dmd_def)
  apply clarsimp
  apply merge_box
  apply (fastforce elim!: notE STL4E [temp_use])
  done

lemma DmdImpldup:
  assumes 1: "sigma |= []A"
    and 2: "sigma |= <>F"
    and 3: "|- []A & F --> G"
  shows "sigma |= <>G"
  apply (rule 2 [THEN 1 [THEN BoxDmd [temp_use]], THEN DmdImplE])
  apply (rule 3)
  done

lemma STL6: "|- <>[]F & <>[]G --> <>[](F & G)"
  apply (auto simp: STL5 [temp_rewrite, symmetric])
  apply (drule linT [temp_use])
   apply assumption
  apply (erule thin_rl)
  apply (rule DmdDmd [temp_unlift, THEN iffD1])
  apply (erule disjE)
   apply (erule DmdImplE)
   apply (rule BoxDmd)
  apply (erule DmdImplE)
  apply auto
  apply (drule BoxDmd [temp_use])
   apply assumption
  apply (erule thin_rl)
  apply (fastforce elim!: DmdImplE [temp_use])
  done


(* ------------------------ True / False ----------------------------------------- *)
section "Simplification of constants"

lemma BoxConst: "|- ([]#P) = #P"
  apply (rule tempI)
  apply (cases P)
   apply (auto intro!: necT [temp_use] dest: STL2_gen [temp_use] simp: Init_simps)
  done

lemma DmdConst: "|- (<>#P) = #P"
  apply (unfold dmd_def)
  apply (cases P)
  apply (simp_all add: BoxConst [try_rewrite])
  done

lemmas temp_simps [temp_rewrite, simp] = BoxConst DmdConst


(* ------------------------ Further rewrites ----------------------------------------- *)
section "Further rewrites"

lemma NotBox: "|- (~[]F) = (<>~F)"
  by (simp add: dmd_def)

lemma NotDmd: "|- (~<>F) = ([]~F)"
  by (simp add: dmd_def)

(* These are not declared by default, because they could be harmful,
   e.g. []F & ~[]F becomes []F & <>~F !! *)
lemmas more_temp_simps1 =
  STL3 [temp_rewrite] DmdDmd [temp_rewrite] NotBox [temp_rewrite] NotDmd [temp_rewrite]
  NotBox [temp_unlift, THEN eq_reflection]
  NotDmd [temp_unlift, THEN eq_reflection]

lemma BoxDmdBox: "|- ([]<>[]F) = (<>[]F)"
  apply (auto dest!: STL2 [temp_use])
  apply (rule ccontr)
  apply (subgoal_tac "sigma |= <>[][]F & <>[]~[]F")
   apply (erule thin_rl)
   apply auto
    apply (drule STL6 [temp_use])
     apply assumption
    apply simp
   apply (simp_all add: more_temp_simps1)
  done

lemma DmdBoxDmd: "|- (<>[]<>F) = ([]<>F)"
  apply (unfold dmd_def)
  apply (auto simp: BoxDmdBox [unfolded dmd_def, try_rewrite])
  done

lemmas more_temp_simps2 = more_temp_simps1 BoxDmdBox [temp_rewrite] DmdBoxDmd [temp_rewrite]


(* ------------------------ Miscellaneous ----------------------------------- *)

lemma BoxOr: "!!sigma. [| sigma |= []F | []G |] ==> sigma |= [](F | G)"
  by (fastforce elim!: STL4E [temp_use])

(* "persistently implies infinitely often" *)
lemma DBImplBD: "|- <>[]F --> []<>F"
  apply clarsimp
  apply (rule ccontr)
  apply (simp add: more_temp_simps2)
  apply (drule STL6 [temp_use])
   apply assumption
  apply simp
  done

lemma BoxDmdDmdBox: "|- []<>F & <>[]G --> []<>(F & G)"
  apply clarsimp
  apply (rule ccontr)
  apply (unfold more_temp_simps2)
  apply (drule STL6 [temp_use])
   apply assumption
  apply (subgoal_tac "sigma |= <>[]~F")
   apply (force simp: dmd_def)
  apply (fastforce elim: DmdImplE [temp_use] STL4E [temp_use])
  done


(* ------------------------------------------------------------------------- *)
(***          TLA-specific theorems: primed formulas                       ***)
(* ------------------------------------------------------------------------- *)
section "priming"

(* ------------------------ TLA2 ------------------------------------------- *)
lemma STL2_pr: "|- []P --> Init P & Init P`"
  by (fastforce intro!: STL2_gen [temp_use] primeI [temp_use])

(* Auxiliary lemma allows priming of boxed actions *)
lemma BoxPrime: "|- []P --> []($P & P$)"
  apply clarsimp
  apply (erule dup_boxE)
  apply (unfold boxInit_act)
  apply (erule STL4E)
  apply (auto simp: Init_simps dest!: STL2_pr [temp_use])
  done

lemma TLA2:
  assumes "|- $P & P$ --> A"
  shows "|- []P --> []A"
  apply clarsimp
  apply (drule BoxPrime [temp_use])
  apply (auto simp: Init_stp_act_rev [try_rewrite] intro!: assms [temp_use]
    elim!: STL4E [temp_use])
  done

lemma TLA2E: "[| sigma |= []P; |- $P & P$ --> A |] ==> sigma |= []A"
  by (erule (1) TLA2 [temp_use])

lemma DmdPrime: "|- (<>P`) --> (<>P)"
  apply (unfold dmd_def)
  apply (fastforce elim!: TLA2E [temp_use])
  done

lemmas PrimeDmd = InitDmd_gen [temp_use, THEN DmdPrime [temp_use]]

(* ------------------------ INV1, stable --------------------------------------- *)
section "stable, invariant"

lemma ind_rule:
   "[| sigma |= []H; sigma |= Init P; |- H --> (Init P & ~[]F --> Init(P`) & F) |]  
    ==> sigma |= []F"
  apply (rule indT [temp_use])
   apply (erule (2) STL4E)
  done

lemma box_stp_act: "|- ([]$P) = ([]P)"
  by (simp add: boxInit_act Init_simps)

lemmas box_stp_actI = box_stp_act [temp_use, THEN iffD2]
lemmas box_stp_actD = box_stp_act [temp_use, THEN iffD1]

lemmas more_temp_simps3 = box_stp_act [temp_rewrite] more_temp_simps2

lemma INV1: 
  "|- (Init P) --> (stable P) --> []P"
  apply (unfold stable_def boxInit_stp boxInit_act)
  apply clarsimp
  apply (erule ind_rule)
   apply (auto simp: Init_simps elim: ind_rule)
  done

lemma StableT: 
    "!!P. |- $P & A --> P` ==> |- []A --> stable P"
  apply (unfold stable_def)
  apply (fastforce elim!: STL4E [temp_use])
  done

lemma Stable: "[| sigma |= []A; |- $P & A --> P` |] ==> sigma |= stable P"
  by (erule (1) StableT [temp_use])

(* Generalization of INV1 *)
lemma StableBox: "|- (stable P) --> [](Init P --> []P)"
  apply (unfold stable_def)
  apply clarsimp
  apply (erule dup_boxE)
  apply (force simp: stable_def elim: STL4E [temp_use] INV1 [temp_use])
  done

lemma DmdStable: "|- (stable P) & <>P --> <>[]P"
  apply clarsimp
  apply (rule DmdImpl2)
   prefer 2
   apply (erule StableBox [temp_use])
  apply (simp add: dmdInitD)
  done

(* ---------------- (Semi-)automatic invariant tactics ---------------------- *)

ML {*
(* inv_tac reduces goals of the form ... ==> sigma |= []P *)
fun inv_tac ctxt =
  SELECT_GOAL
    (EVERY
     [auto_tac ctxt,
      TRY (merge_box_tac 1),
      rtac (temp_use @{thm INV1}) 1, (* fail if the goal is not a box *)
      TRYALL (etac @{thm Stable})]);

(* auto_inv_tac applies inv_tac and then tries to attack the subgoals
   in simple cases it may be able to handle goals like |- MyProg --> []Inv.
   In these simple cases the simplifier seems to be more useful than the
   auto-tactic, which applies too much propositional logic and simplifies
   too late.
*)
fun auto_inv_tac ctxt =
  SELECT_GOAL
    (inv_tac ctxt 1 THEN
      (TRYALL (action_simp_tac
        (simpset_of ctxt addsimps [@{thm Init_stp}, @{thm Init_act}]) [] [@{thm squareE}])));
*}

method_setup invariant = {*
  Method.sections Clasimp.clasimp_modifiers >> (K (SIMPLE_METHOD' o inv_tac))
*}

method_setup auto_invariant = {*
  Method.sections Clasimp.clasimp_modifiers >> (K (SIMPLE_METHOD' o auto_inv_tac))
*}

lemma unless: "|- []($P --> P` | Q`) --> (stable P) | <>Q"
  apply (unfold dmd_def)
  apply (clarsimp dest!: BoxPrime [temp_use])
  apply merge_box
  apply (erule contrapos_np)
  apply (fastforce elim!: Stable [temp_use])
  done


(* --------------------- Recursive expansions --------------------------------------- *)
section "recursive expansions"

(* Recursive expansions of [] and <> for state predicates *)
lemma BoxRec: "|- ([]P) = (Init P & []P`)"
  apply (auto intro!: STL2_gen [temp_use])
   apply (fastforce elim!: TLA2E [temp_use])
  apply (auto simp: stable_def elim!: INV1 [temp_use] STL4E [temp_use])
  done

lemma DmdRec: "|- (<>P) = (Init P | <>P`)"
  apply (unfold dmd_def BoxRec [temp_rewrite])
  apply (auto simp: Init_simps)
  done

lemma DmdRec2: "!!sigma. [| sigma |= <>P; sigma |= []~P` |] ==> sigma |= Init P"
  apply (force simp: DmdRec [temp_rewrite] dmd_def)
  done

lemma InfinitePrime: "|- ([]<>P) = ([]<>P`)"
  apply auto
   apply (rule classical)
   apply (rule DBImplBD [temp_use])
   apply (subgoal_tac "sigma |= <>[]P")
    apply (fastforce elim!: DmdImplE [temp_use] TLA2E [temp_use])
   apply (subgoal_tac "sigma |= <>[] (<>P & []~P`)")
    apply (force simp: boxInit_stp [temp_use]
      elim!: DmdImplE [temp_use] STL4E [temp_use] DmdRec2 [temp_use])
   apply (force intro!: STL6 [temp_use] simp: more_temp_simps3)
  apply (fastforce intro: DmdPrime [temp_use] elim!: STL4E [temp_use])
  done

lemma InfiniteEnsures:
  "[| sigma |= []N; sigma |= []<>A; |- A & N --> P` |] ==> sigma |= []<>P"
  apply (unfold InfinitePrime [temp_rewrite])
  apply (rule InfImpl)
    apply assumption+
  done

(* ------------------------ fairness ------------------------------------------- *)
section "fairness"

(* alternative definitions of fairness *)
lemma WF_alt: "|- WF(A)_v = ([]<>~Enabled(<A>_v) | []<><A>_v)"
  apply (unfold WF_def dmd_def)
  apply fastforce
  done

lemma SF_alt: "|- SF(A)_v = (<>[]~Enabled(<A>_v) | []<><A>_v)"
  apply (unfold SF_def dmd_def)
  apply fastforce
  done

(* theorems to "box" fairness conditions *)
lemma BoxWFI: "|- WF(A)_v --> []WF(A)_v"
  by (auto simp: WF_alt [try_rewrite] more_temp_simps3 intro!: BoxOr [temp_use])

lemma WF_Box: "|- ([]WF(A)_v) = WF(A)_v"
  by (fastforce intro!: BoxWFI [temp_use] dest!: STL2 [temp_use])

lemma BoxSFI: "|- SF(A)_v --> []SF(A)_v"
  by (auto simp: SF_alt [try_rewrite] more_temp_simps3 intro!: BoxOr [temp_use])

lemma SF_Box: "|- ([]SF(A)_v) = SF(A)_v"
  by (fastforce intro!: BoxSFI [temp_use] dest!: STL2 [temp_use])

lemmas more_temp_simps = more_temp_simps3 WF_Box [temp_rewrite] SF_Box [temp_rewrite]

lemma SFImplWF: "|- SF(A)_v --> WF(A)_v"
  apply (unfold SF_def WF_def)
  apply (fastforce dest!: DBImplBD [temp_use])
  done

(* A tactic that "boxes" all fairness conditions. Apply more_temp_simps to "unbox". *)
ML {*
val box_fair_tac = SELECT_GOAL (REPEAT (dresolve_tac [@{thm BoxWFI}, @{thm BoxSFI}] 1))
*}


(* ------------------------------ leads-to ------------------------------ *)

section "~>"

lemma leadsto_init: "|- (Init F) & (F ~> G) --> <>G"
  apply (unfold leadsto_def)
  apply (auto dest!: STL2 [temp_use])
  done

(* |- F & (F ~> G) --> <>G *)
lemmas leadsto_init_temp = leadsto_init [where 'a = behavior, unfolded Init_simps]

lemma streett_leadsto: "|- ([]<>Init F --> []<>G) = (<>(F ~> G))"
  apply (unfold leadsto_def)
  apply auto
    apply (simp add: more_temp_simps)
    apply (fastforce elim!: DmdImplE [temp_use] STL4E [temp_use])
   apply (fastforce intro!: InitDmd [temp_use] elim!: STL4E [temp_use])
  apply (subgoal_tac "sigma |= []<><>G")
   apply (simp add: more_temp_simps)
  apply (drule BoxDmdDmdBox [temp_use])
   apply assumption
  apply (fastforce elim!: DmdImplE [temp_use] STL4E [temp_use])
  done

lemma leadsto_infinite: "|- []<>F & (F ~> G) --> []<>G"
  apply clarsimp
  apply (erule InitDmd [temp_use, THEN streett_leadsto [temp_unlift, THEN iffD2, THEN mp]])
  apply (simp add: dmdInitD)
  done

(* In particular, strong fairness is a Streett condition. The following
   rules are sometimes easier to use than WF2 or SF2 below.
*)
lemma leadsto_SF: "|- (Enabled(<A>_v) ~> <A>_v) --> SF(A)_v"
  apply (unfold SF_def)
  apply (clarsimp elim!: leadsto_infinite [temp_use])
  done

lemma leadsto_WF: "|- (Enabled(<A>_v) ~> <A>_v) --> WF(A)_v"
  by (clarsimp intro!: SFImplWF [temp_use] leadsto_SF [temp_use])

(* introduce an invariant into the proof of a leadsto assertion.
   []I --> ((P ~> Q)  =  (P /\ I ~> Q))
*)
lemma INV_leadsto: "|- []I & (P & I ~> Q) --> (P ~> Q)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply (erule STL4Edup)
   apply assumption
  apply (auto simp: Init_simps dest!: STL2_gen [temp_use])
  done

lemma leadsto_classical: "|- (Init F & []~G ~> G) --> (F ~> G)"
  apply (unfold leadsto_def dmd_def)
  apply (force simp: Init_simps elim!: STL4E [temp_use])
  done

lemma leadsto_false: "|- (F ~> #False) = ([]~F)"
  apply (unfold leadsto_def)
  apply (simp add: boxNotInitD)
  done

lemma leadsto_exists: "|- ((EX x. F x) ~> G) = (ALL x. (F x ~> G))"
  apply (unfold leadsto_def)
  apply (auto simp: allT [try_rewrite] Init_simps elim!: STL4E [temp_use])
  done

(* basic leadsto properties, cf. Unity *)

lemma ImplLeadsto_gen: "|- [](Init F --> Init G) --> (F ~> G)"
  apply (unfold leadsto_def)
  apply (auto intro!: InitDmd_gen [temp_use]
    elim!: STL4E_gen [temp_use] simp: Init_simps)
  done

lemmas ImplLeadsto =
  ImplLeadsto_gen [where 'a = behavior and 'b = behavior, unfolded Init_simps]

lemma ImplLeadsto_simple: "!!F G. |- F --> G ==> |- F ~> G"
  by (auto simp: Init_def intro!: ImplLeadsto_gen [temp_use] necT [temp_use])

lemma EnsuresLeadsto:
  assumes "|- A & $P --> Q`"
  shows "|- []A --> (P ~> Q)"
  apply (unfold leadsto_def)
  apply (clarsimp elim!: INV_leadsto [temp_use])
  apply (erule STL4E_gen)
  apply (auto simp: Init_defs intro!: PrimeDmd [temp_use] assms [temp_use])
  done

lemma EnsuresLeadsto2: "|- []($P --> Q`) --> (P ~> Q)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply (erule STL4E_gen)
  apply (auto simp: Init_simps intro!: PrimeDmd [temp_use])
  done

lemma ensures:
  assumes 1: "|- $P & N --> P` | Q`"
    and 2: "|- ($P & N) & A --> Q`"
  shows "|- []N & []([]P --> <>A) --> (P ~> Q)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply (erule STL4Edup)
   apply assumption
  apply clarsimp
  apply (subgoal_tac "sigmaa |= [] ($P --> P` | Q`) ")
   apply (drule unless [temp_use])
   apply (clarsimp dest!: INV1 [temp_use])
  apply (rule 2 [THEN DmdImpl, temp_use, THEN DmdPrime [temp_use]])
   apply (force intro!: BoxDmd_simple [temp_use]
     simp: split_box_conj [try_rewrite] box_stp_act [try_rewrite])
  apply (force elim: STL4E [temp_use] dest: 1 [temp_use])
  done

lemma ensures_simple:
  "[| |- $P & N --> P` | Q`;  
      |- ($P & N) & A --> Q`  
   |] ==> |- []N & []<>A --> (P ~> Q)"
  apply clarsimp
  apply (erule (2) ensures [temp_use])
  apply (force elim!: STL4E [temp_use])
  done

lemma EnsuresInfinite:
    "[| sigma |= []<>P; sigma |= []A; |- A & $P --> Q` |] ==> sigma |= []<>Q"
  apply (erule leadsto_infinite [temp_use])
  apply (erule EnsuresLeadsto [temp_use])
  apply assumption
  done


(*** Gronning's lattice rules (taken from TLP) ***)
section "Lattice rules"

lemma LatticeReflexivity: "|- F ~> F"
  apply (unfold leadsto_def)
  apply (rule necT InitDmd_gen)+
  done

lemma LatticeTransitivity: "|- (G ~> H) & (F ~> G) --> (F ~> H)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply (erule dup_boxE) (* [][] (Init G --> H) *)
  apply merge_box
  apply (clarsimp elim!: STL4E [temp_use])
  apply (rule dup_dmdD)
  apply (subgoal_tac "sigmaa |= <>Init G")
   apply (erule DmdImpl2)
   apply assumption
  apply (simp add: dmdInitD)
  done

lemma LatticeDisjunctionElim1: "|- (F | G ~> H) --> (F ~> H)"
  apply (unfold leadsto_def)
  apply (auto simp: Init_simps elim!: STL4E [temp_use])
  done

lemma LatticeDisjunctionElim2: "|- (F | G ~> H) --> (G ~> H)"
  apply (unfold leadsto_def)
  apply (auto simp: Init_simps elim!: STL4E [temp_use])
  done

lemma LatticeDisjunctionIntro: "|- (F ~> H) & (G ~> H) --> (F | G ~> H)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply merge_box
  apply (auto simp: Init_simps elim!: STL4E [temp_use])
  done

lemma LatticeDisjunction: "|- (F | G ~> H) = ((F ~> H) & (G ~> H))"
  by (auto intro: LatticeDisjunctionIntro [temp_use]
    LatticeDisjunctionElim1 [temp_use]
    LatticeDisjunctionElim2 [temp_use])

lemma LatticeDiamond: "|- (A ~> B | C) & (B ~> D) & (C ~> D) --> (A ~> D)"
  apply clarsimp
  apply (subgoal_tac "sigma |= (B | C) ~> D")
  apply (erule_tac G = "LIFT (B | C)" in LatticeTransitivity [temp_use])
   apply (fastforce intro!: LatticeDisjunctionIntro [temp_use])+
  done

lemma LatticeTriangle: "|- (A ~> D | B) & (B ~> D) --> (A ~> D)"
  apply clarsimp
  apply (subgoal_tac "sigma |= (D | B) ~> D")
   apply (erule_tac G = "LIFT (D | B)" in LatticeTransitivity [temp_use])
  apply assumption
  apply (auto intro: LatticeDisjunctionIntro [temp_use] LatticeReflexivity [temp_use])
  done

lemma LatticeTriangle2: "|- (A ~> B | D) & (B ~> D) --> (A ~> D)"
  apply clarsimp
  apply (subgoal_tac "sigma |= B | D ~> D")
   apply (erule_tac G = "LIFT (B | D)" in LatticeTransitivity [temp_use])
   apply assumption
  apply (auto intro: LatticeDisjunctionIntro [temp_use] LatticeReflexivity [temp_use])
  done

(*** Lamport's fairness rules ***)
section "Fairness rules"

lemma WF1:
  "[| |- $P & N  --> P` | Q`;    
      |- ($P & N) & <A>_v --> Q`;    
      |- $P & N --> $(Enabled(<A>_v)) |]    
  ==> |- []N & WF(A)_v --> (P ~> Q)"
  apply (clarsimp dest!: BoxWFI [temp_use])
  apply (erule (2) ensures [temp_use])
  apply (erule (1) STL4Edup)
  apply (clarsimp simp: WF_def)
  apply (rule STL2 [temp_use])
  apply (clarsimp elim!: mp intro!: InitDmd [temp_use])
  apply (erule STL4 [temp_use, THEN box_stp_actD [temp_use]])
  apply (simp add: split_box_conj box_stp_actI)
  done

(* Sometimes easier to use; designed for action B rather than state predicate Q *)
lemma WF_leadsto:
  assumes 1: "|- N & $P --> $Enabled (<A>_v)"
    and 2: "|- N & <A>_v --> B"
    and 3: "|- [](N & [~A]_v) --> stable P"
  shows "|- []N & WF(A)_v --> (P ~> B)"
  apply (unfold leadsto_def)
  apply (clarsimp dest!: BoxWFI [temp_use])
  apply (erule (1) STL4Edup)
  apply clarsimp
  apply (rule 2 [THEN DmdImpl, temp_use])
  apply (rule BoxDmd_simple [temp_use])
   apply assumption
  apply (rule classical)
  apply (rule STL2 [temp_use])
  apply (clarsimp simp: WF_def elim!: mp intro!: InitDmd [temp_use])
  apply (rule 1 [THEN STL4, temp_use, THEN box_stp_actD])
  apply (simp (no_asm_simp) add: split_box_conj [try_rewrite] box_stp_act [try_rewrite])
  apply (erule INV1 [temp_use])
  apply (rule 3 [temp_use])
  apply (simp add: split_box_conj [try_rewrite] NotDmd [temp_use] not_angle [try_rewrite])
  done

lemma SF1:
  "[| |- $P & N  --> P` | Q`;    
      |- ($P & N) & <A>_v --> Q`;    
      |- []P & []N & []F --> <>Enabled(<A>_v) |]    
  ==> |- []N & SF(A)_v & []F --> (P ~> Q)"
  apply (clarsimp dest!: BoxSFI [temp_use])
  apply (erule (2) ensures [temp_use])
  apply (erule_tac F = F in dup_boxE)
  apply merge_temp_box
  apply (erule STL4Edup)
  apply assumption
  apply (clarsimp simp: SF_def)
  apply (rule STL2 [temp_use])
  apply (erule mp)
  apply (erule STL4 [temp_use])
  apply (simp add: split_box_conj [try_rewrite] STL3 [try_rewrite])
  done

lemma WF2:
  assumes 1: "|- N & <B>_f --> <M>_g"
    and 2: "|- $P & P` & <N & A>_f --> B"
    and 3: "|- P & Enabled(<M>_g) --> Enabled(<A>_f)"
    and 4: "|- [](N & [~B]_f) & WF(A)_f & []F & <>[]Enabled(<M>_g) --> <>[]P"
  shows "|- []N & WF(A)_f & []F --> WF(M)_g"
  apply (clarsimp dest!: BoxWFI [temp_use] BoxDmdBox [temp_use, THEN iffD2]
    simp: WF_def [where A = M])
  apply (erule_tac F = F in dup_boxE)
  apply merge_temp_box
  apply (erule STL4Edup)
   apply assumption
  apply (clarsimp intro!: BoxDmd_simple [temp_use, THEN 1 [THEN DmdImpl, temp_use]])
  apply (rule classical)
  apply (subgoal_tac "sigmaa |= <> (($P & P` & N) & <A>_f)")
   apply (force simp: angle_def intro!: 2 [temp_use] elim!: DmdImplE [temp_use])
  apply (rule BoxDmd_simple [THEN DmdImpl, unfolded DmdDmd [temp_rewrite], temp_use])
  apply (simp add: NotDmd [temp_use] not_angle [try_rewrite])
  apply merge_act_box
  apply (frule 4 [temp_use])
     apply assumption+
  apply (drule STL6 [temp_use])
   apply assumption
  apply (erule_tac V = "sigmaa |= <>[]P" in thin_rl)
  apply (erule_tac V = "sigmaa |= []F" in thin_rl)
  apply (drule BoxWFI [temp_use])
  apply (erule_tac F = "ACT N & [~B]_f" in dup_boxE)
  apply merge_temp_box
  apply (erule DmdImpldup)
   apply assumption
  apply (auto simp: split_box_conj [try_rewrite] STL3 [try_rewrite]
    WF_Box [try_rewrite] box_stp_act [try_rewrite])
   apply (force elim!: TLA2E [where P = P, temp_use])
  apply (rule STL2 [temp_use])
  apply (force simp: WF_def split_box_conj [try_rewrite]
    elim!: mp intro!: InitDmd [temp_use] 3 [THEN STL4, temp_use])
  done

lemma SF2:
  assumes 1: "|- N & <B>_f --> <M>_g"
    and 2: "|- $P & P` & <N & A>_f --> B"
    and 3: "|- P & Enabled(<M>_g) --> Enabled(<A>_f)"
    and 4: "|- [](N & [~B]_f) & SF(A)_f & []F & []<>Enabled(<M>_g) --> <>[]P"
  shows "|- []N & SF(A)_f & []F --> SF(M)_g"
  apply (clarsimp dest!: BoxSFI [temp_use] simp: 2 [try_rewrite] SF_def [where A = M])
  apply (erule_tac F = F in dup_boxE)
  apply (erule_tac F = "TEMP <>Enabled (<M>_g) " in dup_boxE)
  apply merge_temp_box
  apply (erule STL4Edup)
   apply assumption
  apply (clarsimp intro!: BoxDmd_simple [temp_use, THEN 1 [THEN DmdImpl, temp_use]])
  apply (rule classical)
  apply (subgoal_tac "sigmaa |= <> (($P & P` & N) & <A>_f)")
   apply (force simp: angle_def intro!: 2 [temp_use] elim!: DmdImplE [temp_use])
  apply (rule BoxDmd_simple [THEN DmdImpl, unfolded DmdDmd [temp_rewrite], temp_use])
  apply (simp add: NotDmd [temp_use] not_angle [try_rewrite])
  apply merge_act_box
  apply (frule 4 [temp_use])
     apply assumption+
  apply (erule_tac V = "sigmaa |= []F" in thin_rl)
  apply (drule BoxSFI [temp_use])
  apply (erule_tac F = "TEMP <>Enabled (<M>_g)" in dup_boxE)
  apply (erule_tac F = "ACT N & [~B]_f" in dup_boxE)
  apply merge_temp_box
  apply (erule DmdImpldup)
   apply assumption
  apply (auto simp: split_box_conj [try_rewrite] STL3 [try_rewrite]
    SF_Box [try_rewrite] box_stp_act [try_rewrite])
   apply (force elim!: TLA2E [where P = P, temp_use])
  apply (rule STL2 [temp_use])
  apply (force simp: SF_def split_box_conj [try_rewrite]
    elim!: mp InfImpl [temp_use] intro!: 3 [temp_use])
  done

(* ------------------------------------------------------------------------- *)
(***           Liveness proofs by well-founded orderings                   ***)
(* ------------------------------------------------------------------------- *)
section "Well-founded orderings"

lemma wf_leadsto:
  assumes 1: "wf r"
    and 2: "!!x. sigma |= F x ~> (G | (EX y. #((y,x):r) & F y))    "
  shows "sigma |= F x ~> G"
  apply (rule 1 [THEN wf_induct])
  apply (rule LatticeTriangle [temp_use])
   apply (rule 2)
  apply (auto simp: leadsto_exists [try_rewrite])
  apply (case_tac "(y,x) :r")
   apply force
  apply (force simp: leadsto_def Init_simps intro!: necT [temp_use])
  done

(* If r is well-founded, state function v cannot decrease forever *)
lemma wf_not_box_decrease: "!!r. wf r ==> |- [][ (v`, $v) : #r ]_v --> <>[][#False]_v"
  apply clarsimp
  apply (rule ccontr)
  apply (subgoal_tac "sigma |= (EX x. v=#x) ~> #False")
   apply (drule leadsto_false [temp_use, THEN iffD1, THEN STL2_gen [temp_use]])
   apply (force simp: Init_defs)
  apply (clarsimp simp: leadsto_exists [try_rewrite] not_square [try_rewrite] more_temp_simps)
  apply (erule wf_leadsto)
  apply (rule ensures_simple [temp_use])
   apply (auto simp: square_def angle_def)
  done

(* "wf r  ==>  |- <>[][ (v`, $v) : #r ]_v --> <>[][#False]_v" *)
lemmas wf_not_dmd_box_decrease =
  wf_not_box_decrease [THEN DmdImpl, unfolded more_temp_simps]

(* If there are infinitely many steps where v decreases, then there
   have to be infinitely many non-stuttering steps where v doesn't decrease.
*)
lemma wf_box_dmd_decrease:
  assumes 1: "wf r"
  shows "|- []<>((v`, $v) : #r) --> []<><(v`, $v) ~: #r>_v"
  apply clarsimp
  apply (rule ccontr)
  apply (simp add: not_angle [try_rewrite] more_temp_simps)
  apply (drule 1 [THEN wf_not_dmd_box_decrease [temp_use]])
  apply (drule BoxDmdDmdBox [temp_use])
   apply assumption
  apply (subgoal_tac "sigma |= []<> ((#False) ::action)")
   apply force
  apply (erule STL4E)
  apply (rule DmdImpl)
  apply (force intro: 1 [THEN wf_irrefl, temp_use])
  done

(* In particular, for natural numbers, if n decreases infinitely often
   then it has to increase infinitely often.
*)
lemma nat_box_dmd_decrease: "!!n::nat stfun. |- []<>(n` < $n) --> []<>($n < n`)"
  apply clarsimp
  apply (subgoal_tac "sigma |= []<><~ ((n`,$n) : #less_than) >_n")
   apply (erule thin_rl)
   apply (erule STL4E)
   apply (rule DmdImpl)
   apply (clarsimp simp: angle_def [try_rewrite])
  apply (rule wf_box_dmd_decrease [temp_use])
   apply (auto elim!: STL4E [temp_use] DmdImplE [temp_use])
  done


(* ------------------------------------------------------------------------- *)
(***           Flexible quantification over state variables                ***)
(* ------------------------------------------------------------------------- *)
section "Flexible quantification"

lemma aallI:
  assumes 1: "basevars vs"
    and 2: "(!!x. basevars (x,vs) ==> sigma |= F x)"
  shows "sigma |= (AALL x. F x)"
  by (auto simp: aall_def elim!: eexE [temp_use] intro!: 1 dest!: 2 [temp_use])

lemma aallE: "|- (AALL x. F x) --> F x"
  apply (unfold aall_def)
  apply clarsimp
  apply (erule contrapos_np)
  apply (force intro!: eexI [temp_use])
  done

(* monotonicity of quantification *)
lemma eex_mono:
  assumes 1: "sigma |= EEX x. F x"
    and 2: "!!x. sigma |= F x --> G x"
  shows "sigma |= EEX x. G x"
  apply (rule unit_base [THEN 1 [THEN eexE]])
  apply (rule eexI [temp_use])
  apply (erule 2 [unfolded intensional_rews, THEN mp])
  done

lemma aall_mono:
  assumes 1: "sigma |= AALL x. F(x)"
    and 2: "!!x. sigma |= F(x) --> G(x)"
  shows "sigma |= AALL x. G(x)"
  apply (rule unit_base [THEN aallI])
  apply (rule 2 [unfolded intensional_rews, THEN mp])
  apply (rule 1 [THEN aallE [temp_use]])
  done

(* Derived history introduction rule *)
lemma historyI:
  assumes 1: "sigma |= Init I"
    and 2: "sigma |= []N"
    and 3: "basevars vs"
    and 4: "!!h. basevars(h,vs) ==> |- I & h = ha --> HI h"
    and 5: "!!h s t. [| basevars(h,vs); N (s,t); h t = hb (h s) (s,t) |] ==> HN h (s,t)"
  shows "sigma |= EEX h. Init (HI h) & [](HN h)"
  apply (rule history [temp_use, THEN eexE])
  apply (rule 3)
  apply (rule eexI [temp_use])
  apply clarsimp
  apply (rule conjI)
   prefer 2
   apply (insert 2)
   apply merge_box
   apply (force elim!: STL4E [temp_use] 5 [temp_use])
  apply (insert 1)
  apply (force simp: Init_defs elim!: 4 [temp_use])
  done

(* ----------------------------------------------------------------------
   example of a history variable: existence of a clock
*)

lemma "|- EEX h. Init(h = #True) & [](h` = (~$h))"
  apply (rule tempI)
  apply (rule historyI)
  apply (force simp: Init_defs intro!: unit_base [temp_use] necT [temp_use])+
  done

end
