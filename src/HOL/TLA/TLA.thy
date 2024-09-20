(*  Title:      HOL/TLA/TLA.thy
    Author:     Stephan Merz
    Copyright:  1998 University of Munich
*)

section \<open>The temporal level of TLA\<close>

theory TLA
imports Init
begin

consts
  (** abstract syntax **)
  Box        :: "('w::world) form \<Rightarrow> temporal"
  Dmd        :: "('w::world) form \<Rightarrow> temporal"
  leadsto    :: "['w::world form, 'v::world form] \<Rightarrow> temporal"
  Stable     :: "stpred \<Rightarrow> temporal"
  WF         :: "[action, 'a stfun] \<Rightarrow> temporal"
  SF         :: "[action, 'a stfun] \<Rightarrow> temporal"

  (* Quantification over (flexible) state variables *)
  EEx        :: "('a stfun \<Rightarrow> temporal) \<Rightarrow> temporal"       (binder \<open>Eex \<close> 10)
  AAll       :: "('a stfun \<Rightarrow> temporal) \<Rightarrow> temporal"       (binder \<open>Aall \<close> 10)

  (** concrete syntax **)
syntax
  "_Box"     :: "lift \<Rightarrow> lift"                        (\<open>(\<box>_)\<close> [40] 40)
  "_Dmd"     :: "lift \<Rightarrow> lift"                        (\<open>(\<diamond>_)\<close> [40] 40)
  "_leadsto" :: "[lift,lift] \<Rightarrow> lift"                 (\<open>(_ \<leadsto> _)\<close> [23,22] 22)
  "_stable"  :: "lift \<Rightarrow> lift"                        (\<open>(stable/ _)\<close>)
  "_WF"      :: "[lift,lift] \<Rightarrow> lift"                 (\<open>(WF'(_')'_(_))\<close> [0,60] 55)
  "_SF"      :: "[lift,lift] \<Rightarrow> lift"                 (\<open>(SF'(_')'_(_))\<close> [0,60] 55)

  "_EEx"     :: "[idts, lift] \<Rightarrow> lift"                (\<open>(3\<exists>\<exists> _./ _)\<close> [0,10] 10)
  "_AAll"    :: "[idts, lift] \<Rightarrow> lift"                (\<open>(3\<forall>\<forall> _./ _)\<close> [0,10] 10)

translations
  "_Box"      ==   "CONST Box"
  "_Dmd"      ==   "CONST Dmd"
  "_leadsto"  ==   "CONST leadsto"
  "_stable"   ==   "CONST Stable"
  "_WF"       ==   "CONST WF"
  "_SF"       ==   "CONST SF"
  "_EEx v A"  ==   "Eex v. A"
  "_AAll v A" ==   "Aall v. A"

  "sigma \<Turnstile> \<box>F"         <= "_Box F sigma"
  "sigma \<Turnstile> \<diamond>F"         <= "_Dmd F sigma"
  "sigma \<Turnstile> F \<leadsto> G"      <= "_leadsto F G sigma"
  "sigma \<Turnstile> stable P"    <= "_stable P sigma"
  "sigma \<Turnstile> WF(A)_v"     <= "_WF A v sigma"
  "sigma \<Turnstile> SF(A)_v"     <= "_SF A v sigma"
  "sigma \<Turnstile> \<exists>\<exists>x. F"    <= "_EEx x F sigma"
  "sigma \<Turnstile> \<forall>\<forall>x. F"    <= "_AAll x F sigma"

axiomatization where
  (* Definitions of derived operators *)
  dmd_def:      "\<And>F. TEMP \<diamond>F  ==  TEMP \<not>\<box>\<not>F"

axiomatization where
  boxInit:      "\<And>F. TEMP \<box>F  ==  TEMP \<box>Init F" and
  leadsto_def:  "\<And>F G. TEMP F \<leadsto> G  ==  TEMP \<box>(Init F \<longrightarrow> \<diamond>G)" and
  stable_def:   "\<And>P. TEMP stable P  ==  TEMP \<box>($P \<longrightarrow> P$)" and
  WF_def:       "TEMP WF(A)_v  ==  TEMP \<diamond>\<box> Enabled(<A>_v) \<longrightarrow> \<box>\<diamond><A>_v" and
  SF_def:       "TEMP SF(A)_v  ==  TEMP \<box>\<diamond> Enabled(<A>_v) \<longrightarrow> \<box>\<diamond><A>_v" and
  aall_def:     "TEMP (\<forall>\<forall>x. F x)  ==  TEMP \<not> (\<exists>\<exists>x. \<not> F x)"

axiomatization where
(* Base axioms for raw TLA. *)
  normalT:    "\<And>F G. \<turnstile> \<box>(F \<longrightarrow> G) \<longrightarrow> (\<box>F \<longrightarrow> \<box>G)" and    (* polymorphic *)
  reflT:      "\<And>F. \<turnstile> \<box>F \<longrightarrow> F" and         (* F::temporal *)
  transT:     "\<And>F. \<turnstile> \<box>F \<longrightarrow> \<box>\<box>F" and     (* polymorphic *)
  linT:       "\<And>F G. \<turnstile> \<diamond>F \<and> \<diamond>G \<longrightarrow> (\<diamond>(F \<and> \<diamond>G)) \<or> (\<diamond>(G \<and> \<diamond>F))" and
  discT:      "\<And>F. \<turnstile> \<box>(F \<longrightarrow> \<diamond>(\<not>F \<and> \<diamond>F)) \<longrightarrow> (F \<longrightarrow> \<box>\<diamond>F)" and
  primeI:     "\<And>P. \<turnstile> \<box>P \<longrightarrow> Init P`" and
  primeE:     "\<And>P F. \<turnstile> \<box>(Init P \<longrightarrow> \<box>F) \<longrightarrow> Init P` \<longrightarrow> (F \<longrightarrow> \<box>F)" and
  indT:       "\<And>P F. \<turnstile> \<box>(Init P \<and> \<not>\<box>F \<longrightarrow> Init P` \<and> F) \<longrightarrow> Init P \<longrightarrow> \<box>F" and
  allT:       "\<And>F. \<turnstile> (\<forall>x. \<box>(F x)) = (\<box>(\<forall> x. F x))"

axiomatization where
  necT:       "\<And>F. \<turnstile> F \<Longrightarrow> \<turnstile> \<box>F"      (* polymorphic *)

axiomatization where
(* Flexible quantification: refinement mappings, history variables *)
  eexI:       "\<turnstile> F x \<longrightarrow> (\<exists>\<exists>x. F x)" and
  eexE:       "\<lbrakk> sigma \<Turnstile> (\<exists>\<exists>x. F x); basevars vs;
                 (\<And>x. \<lbrakk> basevars (x, vs); sigma \<Turnstile> F x \<rbrakk> \<Longrightarrow> (G sigma)::bool)
              \<rbrakk> \<Longrightarrow> G sigma" and
  history:    "\<turnstile> \<exists>\<exists>h. Init(h = ha) \<and> \<box>(\<forall>x. $h = #x \<longrightarrow> h` = hb x)"


(* Specialize intensional introduction/elimination rules for temporal formulas *)

lemma tempI [intro!]: "(\<And>sigma. sigma \<Turnstile> (F::temporal)) \<Longrightarrow> \<turnstile> F"
  apply (rule intI)
  apply (erule meta_spec)
  done

lemma tempD [dest]: "\<turnstile> (F::temporal) \<Longrightarrow> sigma \<Turnstile> F"
  by (erule intD)


(* ======== Functions to "unlift" temporal theorems ====== *)

ML \<open>
(* The following functions are specialized versions of the corresponding
   functions defined in theory Intensional in that they introduce a
   "world" parameter of type "behavior".
*)
fun temp_unlift ctxt th =
  (rewrite_rule ctxt @{thms action_rews} (th RS @{thm tempD}))
    handle THM _ => action_unlift ctxt th;

(* Turn  \<turnstile> F = G  into meta-level rewrite rule  F == G *)
val temp_rewrite = int_rewrite

fun temp_use ctxt th =
  case Thm.concl_of th of
    Const _ $ (Const (\<^const_name>\<open>Intensional.Valid\<close>, _) $ _) =>
            ((flatten (temp_unlift ctxt th)) handle THM _ => th)
  | _ => th;

fun try_rewrite ctxt th = temp_rewrite ctxt th handle THM _ => temp_use ctxt th;
\<close>

attribute_setup temp_unlift =
  \<open>Scan.succeed (Thm.rule_attribute [] (temp_unlift o Context.proof_of))\<close>
attribute_setup temp_rewrite =
  \<open>Scan.succeed (Thm.rule_attribute [] (temp_rewrite o Context.proof_of))\<close>
attribute_setup temp_use =
  \<open>Scan.succeed (Thm.rule_attribute [] (temp_use o Context.proof_of))\<close>
attribute_setup try_rewrite =
  \<open>Scan.succeed (Thm.rule_attribute [] (try_rewrite o Context.proof_of))\<close>


(* ------------------------------------------------------------------------- *)
(***           "Simple temporal logic": only \<box> and \<diamond>                     ***)
(* ------------------------------------------------------------------------- *)
section "Simple temporal logic"

(* \<box>\<not>F == \<box>\<not>Init F *)
lemmas boxNotInit = boxInit [of "LIFT \<not>F", unfolded Init_simps] for F

lemma dmdInit: "TEMP \<diamond>F == TEMP \<diamond> Init F"
  apply (unfold dmd_def)
  apply (unfold boxInit [of "LIFT \<not>F"])
  apply (simp (no_asm) add: Init_simps)
  done

lemmas dmdNotInit = dmdInit [of "LIFT \<not>F", unfolded Init_simps] for F

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
lemma STL2_gen: "\<turnstile> \<box>F \<longrightarrow> Init F"
  apply (unfold boxInit [of F])
  apply (rule STL2)
  done

(* see also STL2_pr below: "\<turnstile> \<box>P \<longrightarrow> Init P & Init (P`)" *)


(* Dual versions for \<diamond> *)
lemma InitDmd: "\<turnstile> F \<longrightarrow> \<diamond> F"
  apply (unfold dmd_def)
  apply (auto dest!: STL2 [temp_use])
  done

lemma InitDmd_gen: "\<turnstile> Init F \<longrightarrow> \<diamond>F"
  apply clarsimp
  apply (drule InitDmd [temp_use])
  apply (simp add: dmdInitD)
  done


(* ------------------------ STL3 ------------------------------------------- *)
lemma STL3: "\<turnstile> (\<box>\<box>F) = (\<box>F)"
  by (auto elim: transT [temp_use] STL2 [temp_use])

(* corresponding elimination rule introduces double boxes:
   \<lbrakk> (sigma \<Turnstile> \<box>F); (sigma \<Turnstile> \<box>\<box>F) \<Longrightarrow> PROP W \<rbrakk> \<Longrightarrow> PROP W
*)
lemmas dup_boxE = STL3 [temp_unlift, THEN iffD2, elim_format]
lemmas dup_boxD = STL3 [temp_unlift, THEN iffD1]

(* dual versions for \<diamond> *)
lemma DmdDmd: "\<turnstile> (\<diamond>\<diamond>F) = (\<diamond>F)"
  by (auto simp add: dmd_def [try_rewrite] STL3 [try_rewrite])

lemmas dup_dmdE = DmdDmd [temp_unlift, THEN iffD2, elim_format]
lemmas dup_dmdD = DmdDmd [temp_unlift, THEN iffD1]


(* ------------------------ STL4 ------------------------------------------- *)
lemma STL4:
  assumes "\<turnstile> F \<longrightarrow> G"
  shows "\<turnstile> \<box>F \<longrightarrow> \<box>G"
  apply clarsimp
  apply (rule normalT [temp_use])
   apply (rule assms [THEN necT, temp_use])
  apply assumption
  done

(* Unlifted version as an elimination rule *)
lemma STL4E: "\<lbrakk> sigma \<Turnstile> \<box>F; \<turnstile> F \<longrightarrow> G \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<box>G"
  by (erule (1) STL4 [temp_use])

lemma STL4_gen: "\<turnstile> Init F \<longrightarrow> Init G \<Longrightarrow> \<turnstile> \<box>F \<longrightarrow> \<box>G"
  apply (drule STL4)
  apply (simp add: boxInitD)
  done

lemma STL4E_gen: "\<lbrakk> sigma \<Turnstile> \<box>F; \<turnstile> Init F \<longrightarrow> Init G \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<box>G"
  by (erule (1) STL4_gen [temp_use])

(* see also STL4Edup below, which allows an auxiliary boxed formula:
       \<box>A /\ F => G
     -----------------
     \<box>A /\ \<box>F => \<box>G
*)

(* The dual versions for \<diamond> *)
lemma DmdImpl:
  assumes prem: "\<turnstile> F \<longrightarrow> G"
  shows "\<turnstile> \<diamond>F \<longrightarrow> \<diamond>G"
  apply (unfold dmd_def)
  apply (fastforce intro!: prem [temp_use] elim!: STL4E [temp_use])
  done

lemma DmdImplE: "\<lbrakk> sigma \<Turnstile> \<diamond>F; \<turnstile> F \<longrightarrow> G \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<diamond>G"
  by (erule (1) DmdImpl [temp_use])

(* ------------------------ STL5 ------------------------------------------- *)
lemma STL5: "\<turnstile> (\<box>F \<and> \<box>G) = (\<box>(F \<and> G))"
  apply auto
  apply (subgoal_tac "sigma \<Turnstile> \<box> (G \<longrightarrow> (F \<and> G))")
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
  assumes "sigma \<Turnstile> \<box>F"
     and "sigma \<Turnstile> \<box>G"
  and "sigma \<Turnstile> \<box>(F\<and>G) \<Longrightarrow> PROP R"
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

lemma box_thin: "\<lbrakk> sigma \<Turnstile> \<box>F; PROP W \<rbrakk> \<Longrightarrow> PROP W" .

ML \<open>
fun merge_box_tac ctxt i =
   REPEAT_DETERM (EVERY [eresolve_tac ctxt @{thms box_conjE} i, assume_tac ctxt i,
    eresolve_tac ctxt @{thms box_thin} i])

fun merge_temp_box_tac ctxt i =
  REPEAT_DETERM (EVERY [eresolve_tac ctxt @{thms box_conjE_temp} i, assume_tac ctxt i,
    Rule_Insts.eres_inst_tac ctxt [((("'a", 0), Position.none), "behavior")] [] @{thm box_thin} i])

fun merge_stp_box_tac ctxt i =
  REPEAT_DETERM (EVERY [eresolve_tac ctxt @{thms box_conjE_stp} i, assume_tac ctxt i,
    Rule_Insts.eres_inst_tac ctxt [((("'a", 0), Position.none), "state")] [] @{thm box_thin} i])

fun merge_act_box_tac ctxt i =
  REPEAT_DETERM (EVERY [eresolve_tac ctxt @{thms box_conjE_act} i, assume_tac ctxt i,
    Rule_Insts.eres_inst_tac ctxt [((("'a", 0), Position.none), "state * state")] [] @{thm box_thin} i])
\<close>

method_setup merge_box = \<open>Scan.succeed (SIMPLE_METHOD' o merge_box_tac)\<close>
method_setup merge_temp_box = \<open>Scan.succeed (SIMPLE_METHOD' o merge_temp_box_tac)\<close>
method_setup merge_stp_box = \<open>Scan.succeed (SIMPLE_METHOD' o merge_stp_box_tac)\<close>
method_setup merge_act_box = \<open>Scan.succeed (SIMPLE_METHOD' o merge_act_box_tac)\<close>

(* rewrite rule to push universal quantification through box:
      (sigma \<Turnstile> \<box>(\<forall>x. F x)) = (\<forall>x. (sigma \<Turnstile> \<box>F x))
*)
lemmas all_box = allT [temp_unlift, symmetric]

lemma DmdOr: "\<turnstile> (\<diamond>(F \<or> G)) = (\<diamond>F \<or> \<diamond>G)"
  apply (auto simp add: dmd_def split_box_conj [try_rewrite])
  apply (erule contrapos_np, merge_box, fastforce elim!: STL4E [temp_use])+
  done

lemma exT: "\<turnstile> (\<exists>x. \<diamond>(F x)) = (\<diamond>(\<exists>x. F x))"
  by (auto simp: dmd_def Not_Rex [try_rewrite] all_box [try_rewrite])

lemmas ex_dmd = exT [temp_unlift, symmetric]

lemma STL4Edup: "\<And>sigma. \<lbrakk> sigma \<Turnstile> \<box>A; sigma \<Turnstile> \<box>F; \<turnstile> F \<and> \<box>A \<longrightarrow> G \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<box>G"
  apply (erule dup_boxE)
  apply merge_box
  apply (erule STL4E)
  apply assumption
  done

lemma DmdImpl2:
    "\<And>sigma. \<lbrakk> sigma \<Turnstile> \<diamond>F; sigma \<Turnstile> \<box>(F \<longrightarrow> G) \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<diamond>G"
  apply (unfold dmd_def)
  apply auto
  apply (erule notE)
  apply merge_box
  apply (fastforce elim!: STL4E [temp_use])
  done

lemma InfImpl:
  assumes 1: "sigma \<Turnstile> \<box>\<diamond>F"
    and 2: "sigma \<Turnstile> \<box>G"
    and 3: "\<turnstile> F \<and> G \<longrightarrow> H"
  shows "sigma \<Turnstile> \<box>\<diamond>H"
  apply (insert 1 2)
  apply (erule_tac F = G in dup_boxE)
  apply merge_box
  apply (fastforce elim!: STL4E [temp_use] DmdImpl2 [temp_use] intro!: 3 [temp_use])
  done

(* ------------------------ STL6 ------------------------------------------- *)
(* Used in the proof of STL6, but useful in itself. *)
lemma BoxDmd: "\<turnstile> \<box>F \<and> \<diamond>G \<longrightarrow> \<diamond>(\<box>F \<and> G)"
  apply (unfold dmd_def)
  apply clarsimp
  apply (erule dup_boxE)
  apply merge_box
  apply (erule contrapos_np)
  apply (fastforce elim!: STL4E [temp_use])
  done

(* weaker than BoxDmd, but more polymorphic (and often just right) *)
lemma BoxDmd_simple: "\<turnstile> \<box>F \<and> \<diamond>G \<longrightarrow> \<diamond>(F \<and> G)"
  apply (unfold dmd_def)
  apply clarsimp
  apply merge_box
  apply (fastforce elim!: notE STL4E [temp_use])
  done

lemma BoxDmd2_simple: "\<turnstile> \<box>F \<and> \<diamond>G \<longrightarrow> \<diamond>(G \<and> F)"
  apply (unfold dmd_def)
  apply clarsimp
  apply merge_box
  apply (fastforce elim!: notE STL4E [temp_use])
  done

lemma DmdImpldup:
  assumes 1: "sigma \<Turnstile> \<box>A"
    and 2: "sigma \<Turnstile> \<diamond>F"
    and 3: "\<turnstile> \<box>A \<and> F \<longrightarrow> G"
  shows "sigma \<Turnstile> \<diamond>G"
  apply (rule 2 [THEN 1 [THEN BoxDmd [temp_use]], THEN DmdImplE])
  apply (rule 3)
  done

lemma STL6: "\<turnstile> \<diamond>\<box>F \<and> \<diamond>\<box>G \<longrightarrow> \<diamond>\<box>(F \<and> G)"
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

lemma BoxConst: "\<turnstile> (\<box>#P) = #P"
  apply (rule tempI)
  apply (cases P)
   apply (auto intro!: necT [temp_use] dest: STL2_gen [temp_use] simp: Init_simps)
  done

lemma DmdConst: "\<turnstile> (\<diamond>#P) = #P"
  apply (unfold dmd_def)
  apply (cases P)
  apply (simp_all add: BoxConst [try_rewrite])
  done

lemmas temp_simps [temp_rewrite, simp] = BoxConst DmdConst


(* ------------------------ Further rewrites ----------------------------------------- *)
section "Further rewrites"

lemma NotBox: "\<turnstile> (\<not>\<box>F) = (\<diamond>\<not>F)"
  by (simp add: dmd_def)

lemma NotDmd: "\<turnstile> (\<not>\<diamond>F) = (\<box>\<not>F)"
  by (simp add: dmd_def)

(* These are not declared by default, because they could be harmful,
   e.g. \<box>F & \<not>\<box>F becomes \<box>F & \<diamond>\<not>F !! *)
lemmas more_temp_simps1 =
  STL3 [temp_rewrite] DmdDmd [temp_rewrite] NotBox [temp_rewrite] NotDmd [temp_rewrite]
  NotBox [temp_unlift, THEN eq_reflection]
  NotDmd [temp_unlift, THEN eq_reflection]

lemma BoxDmdBox: "\<turnstile> (\<box>\<diamond>\<box>F) = (\<diamond>\<box>F)"
  apply (auto dest!: STL2 [temp_use])
  apply (rule ccontr)
  apply (subgoal_tac "sigma \<Turnstile> \<diamond>\<box>\<box>F \<and> \<diamond>\<box>\<not>\<box>F")
   apply (erule thin_rl)
   apply auto
    apply (drule STL6 [temp_use])
     apply assumption
    apply simp
   apply (simp_all add: more_temp_simps1)
  done

lemma DmdBoxDmd: "\<turnstile> (\<diamond>\<box>\<diamond>F) = (\<box>\<diamond>F)"
  apply (unfold dmd_def)
  apply (auto simp: BoxDmdBox [unfolded dmd_def, try_rewrite])
  done

lemmas more_temp_simps2 = more_temp_simps1 BoxDmdBox [temp_rewrite] DmdBoxDmd [temp_rewrite]


(* ------------------------ Miscellaneous ----------------------------------- *)

lemma BoxOr: "\<And>sigma. \<lbrakk> sigma \<Turnstile> \<box>F \<or> \<box>G \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<box>(F \<or> G)"
  by (fastforce elim!: STL4E [temp_use])

(* "persistently implies infinitely often" *)
lemma DBImplBD: "\<turnstile> \<diamond>\<box>F \<longrightarrow> \<box>\<diamond>F"
  apply clarsimp
  apply (rule ccontr)
  apply (simp add: more_temp_simps2)
  apply (drule STL6 [temp_use])
   apply assumption
  apply simp
  done

lemma BoxDmdDmdBox: "\<turnstile> \<box>\<diamond>F \<and> \<diamond>\<box>G \<longrightarrow> \<box>\<diamond>(F \<and> G)"
  apply clarsimp
  apply (rule ccontr)
  apply (unfold more_temp_simps2)
  apply (drule STL6 [temp_use])
   apply assumption
  apply (subgoal_tac "sigma \<Turnstile> \<diamond>\<box>\<not>F")
   apply (force simp: dmd_def)
  apply (fastforce elim: DmdImplE [temp_use] STL4E [temp_use])
  done


(* ------------------------------------------------------------------------- *)
(***          TLA-specific theorems: primed formulas                       ***)
(* ------------------------------------------------------------------------- *)
section "priming"

(* ------------------------ TLA2 ------------------------------------------- *)
lemma STL2_pr: "\<turnstile> \<box>P \<longrightarrow> Init P \<and> Init P`"
  by (fastforce intro!: STL2_gen [temp_use] primeI [temp_use])

(* Auxiliary lemma allows priming of boxed actions *)
lemma BoxPrime: "\<turnstile> \<box>P \<longrightarrow> \<box>($P \<and> P$)"
  apply clarsimp
  apply (erule dup_boxE)
  apply (unfold boxInit_act)
  apply (erule STL4E)
  apply (auto simp: Init_simps dest!: STL2_pr [temp_use])
  done

lemma TLA2:
  assumes "\<turnstile> $P \<and> P$ \<longrightarrow> A"
  shows "\<turnstile> \<box>P \<longrightarrow> \<box>A"
  apply clarsimp
  apply (drule BoxPrime [temp_use])
  apply (auto simp: Init_stp_act_rev [try_rewrite] intro!: assms [temp_use]
    elim!: STL4E [temp_use])
  done

lemma TLA2E: "\<lbrakk> sigma \<Turnstile> \<box>P; \<turnstile> $P \<and> P$ \<longrightarrow> A \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<box>A"
  by (erule (1) TLA2 [temp_use])

lemma DmdPrime: "\<turnstile> (\<diamond>P`) \<longrightarrow> (\<diamond>P)"
  apply (unfold dmd_def)
  apply (fastforce elim!: TLA2E [temp_use])
  done

lemmas PrimeDmd = InitDmd_gen [temp_use, THEN DmdPrime [temp_use]]

(* ------------------------ INV1, stable --------------------------------------- *)
section "stable, invariant"

lemma ind_rule:
   "\<lbrakk> sigma \<Turnstile> \<box>H; sigma \<Turnstile> Init P; \<turnstile> H \<longrightarrow> (Init P \<and> \<not>\<box>F \<longrightarrow> Init(P`) \<and> F) \<rbrakk>
    \<Longrightarrow> sigma \<Turnstile> \<box>F"
  apply (rule indT [temp_use])
   apply (erule (2) STL4E)
  done

lemma box_stp_act: "\<turnstile> (\<box>$P) = (\<box>P)"
  by (simp add: boxInit_act Init_simps)

lemmas box_stp_actI = box_stp_act [temp_use, THEN iffD2]
lemmas box_stp_actD = box_stp_act [temp_use, THEN iffD1]

lemmas more_temp_simps3 = box_stp_act [temp_rewrite] more_temp_simps2

lemma INV1:
  "\<turnstile> (Init P) \<longrightarrow> (stable P) \<longrightarrow> \<box>P"
  apply (unfold stable_def boxInit_stp boxInit_act)
  apply clarsimp
  apply (erule ind_rule)
   apply (auto simp: Init_simps elim: ind_rule)
  done

lemma StableT:
    "\<And>P. \<turnstile> $P \<and> A \<longrightarrow> P` \<Longrightarrow> \<turnstile> \<box>A \<longrightarrow> stable P"
  apply (unfold stable_def)
  apply (fastforce elim!: STL4E [temp_use])
  done

lemma Stable: "\<lbrakk> sigma \<Turnstile> \<box>A; \<turnstile> $P \<and> A \<longrightarrow> P` \<rbrakk> \<Longrightarrow> sigma \<Turnstile> stable P"
  by (erule (1) StableT [temp_use])

(* Generalization of INV1 *)
lemma StableBox: "\<turnstile> (stable P) \<longrightarrow> \<box>(Init P \<longrightarrow> \<box>P)"
  apply (unfold stable_def)
  apply clarsimp
  apply (erule dup_boxE)
  apply (force simp: stable_def elim: STL4E [temp_use] INV1 [temp_use])
  done

lemma DmdStable: "\<turnstile> (stable P) \<and> \<diamond>P \<longrightarrow> \<diamond>\<box>P"
  apply clarsimp
  apply (rule DmdImpl2)
   prefer 2
   apply (erule StableBox [temp_use])
  apply (simp add: dmdInitD)
  done

(* ---------------- (Semi-)automatic invariant tactics ---------------------- *)

ML \<open>
(* inv_tac reduces goals of the form ... \<Longrightarrow> sigma \<Turnstile> \<box>P *)
fun inv_tac ctxt =
  SELECT_GOAL
    (EVERY
     [auto_tac ctxt,
      TRY (merge_box_tac ctxt 1),
      resolve_tac ctxt [temp_use ctxt @{thm INV1}] 1, (* fail if the goal is not a box *)
      TRYALL (eresolve_tac ctxt @{thms Stable})]);

(* auto_inv_tac applies inv_tac and then tries to attack the subgoals
   in simple cases it may be able to handle goals like \<turnstile> MyProg \<longrightarrow> \<box>Inv.
   In these simple cases the simplifier seems to be more useful than the
   auto-tactic, which applies too much propositional logic and simplifies
   too late.
*)
fun auto_inv_tac ctxt =
  SELECT_GOAL
    (inv_tac ctxt 1 THEN
      (TRYALL (action_simp_tac
        (ctxt addsimps [@{thm Init_stp}, @{thm Init_act}]) [] [@{thm squareE}])));
\<close>

method_setup invariant = \<open>
  Method.sections Clasimp.clasimp_modifiers >> (K (SIMPLE_METHOD' o inv_tac))
\<close>

method_setup auto_invariant = \<open>
  Method.sections Clasimp.clasimp_modifiers >> (K (SIMPLE_METHOD' o auto_inv_tac))
\<close>

lemma unless: "\<turnstile> \<box>($P \<longrightarrow> P` \<or> Q`) \<longrightarrow> (stable P) \<or> \<diamond>Q"
  apply (unfold dmd_def)
  apply (clarsimp dest!: BoxPrime [temp_use])
  apply merge_box
  apply (erule contrapos_np)
  apply (fastforce elim!: Stable [temp_use])
  done


(* --------------------- Recursive expansions --------------------------------------- *)
section "recursive expansions"

(* Recursive expansions of \<box> and \<diamond> for state predicates *)
lemma BoxRec: "\<turnstile> (\<box>P) = (Init P \<and> \<box>P`)"
  apply (auto intro!: STL2_gen [temp_use])
   apply (fastforce elim!: TLA2E [temp_use])
  apply (auto simp: stable_def elim!: INV1 [temp_use] STL4E [temp_use])
  done

lemma DmdRec: "\<turnstile> (\<diamond>P) = (Init P \<or> \<diamond>P`)"
  apply (unfold dmd_def BoxRec [temp_rewrite])
  apply (auto simp: Init_simps)
  done

lemma DmdRec2: "\<And>sigma. \<lbrakk> sigma \<Turnstile> \<diamond>P; sigma \<Turnstile> \<box>\<not>P` \<rbrakk> \<Longrightarrow> sigma \<Turnstile> Init P"
  apply (force simp: DmdRec [temp_rewrite] dmd_def)
  done

lemma InfinitePrime: "\<turnstile> (\<box>\<diamond>P) = (\<box>\<diamond>P`)"
  apply auto
   apply (rule classical)
   apply (rule DBImplBD [temp_use])
   apply (subgoal_tac "sigma \<Turnstile> \<diamond>\<box>P")
    apply (fastforce elim!: DmdImplE [temp_use] TLA2E [temp_use])
   apply (subgoal_tac "sigma \<Turnstile> \<diamond>\<box> (\<diamond>P \<and> \<box>\<not>P`)")
    apply (force simp: boxInit_stp [temp_use]
      elim!: DmdImplE [temp_use] STL4E [temp_use] DmdRec2 [temp_use])
   apply (force intro!: STL6 [temp_use] simp: more_temp_simps3)
  apply (fastforce intro: DmdPrime [temp_use] elim!: STL4E [temp_use])
  done

lemma InfiniteEnsures:
  "\<lbrakk> sigma \<Turnstile> \<box>N; sigma \<Turnstile> \<box>\<diamond>A; \<turnstile> A \<and> N \<longrightarrow> P` \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<box>\<diamond>P"
  apply (unfold InfinitePrime [temp_rewrite])
  apply (rule InfImpl)
    apply assumption+
  done

(* ------------------------ fairness ------------------------------------------- *)
section "fairness"

(* alternative definitions of fairness *)
lemma WF_alt: "\<turnstile> WF(A)_v = (\<box>\<diamond>\<not>Enabled(<A>_v) \<or> \<box>\<diamond><A>_v)"
  apply (unfold WF_def dmd_def)
  apply fastforce
  done

lemma SF_alt: "\<turnstile> SF(A)_v = (\<diamond>\<box>\<not>Enabled(<A>_v) \<or> \<box>\<diamond><A>_v)"
  apply (unfold SF_def dmd_def)
  apply fastforce
  done

(* theorems to "box" fairness conditions *)
lemma BoxWFI: "\<turnstile> WF(A)_v \<longrightarrow> \<box>WF(A)_v"
  by (auto simp: WF_alt [try_rewrite] more_temp_simps3 intro!: BoxOr [temp_use])

lemma WF_Box: "\<turnstile> (\<box>WF(A)_v) = WF(A)_v"
  by (fastforce intro!: BoxWFI [temp_use] dest!: STL2 [temp_use])

lemma BoxSFI: "\<turnstile> SF(A)_v \<longrightarrow> \<box>SF(A)_v"
  by (auto simp: SF_alt [try_rewrite] more_temp_simps3 intro!: BoxOr [temp_use])

lemma SF_Box: "\<turnstile> (\<box>SF(A)_v) = SF(A)_v"
  by (fastforce intro!: BoxSFI [temp_use] dest!: STL2 [temp_use])

lemmas more_temp_simps = more_temp_simps3 WF_Box [temp_rewrite] SF_Box [temp_rewrite]

lemma SFImplWF: "\<turnstile> SF(A)_v \<longrightarrow> WF(A)_v"
  apply (unfold SF_def WF_def)
  apply (fastforce dest!: DBImplBD [temp_use])
  done

(* A tactic that "boxes" all fairness conditions. Apply more_temp_simps to "unbox". *)
ML \<open>
fun box_fair_tac ctxt =
  SELECT_GOAL (REPEAT (dresolve_tac ctxt [@{thm BoxWFI}, @{thm BoxSFI}] 1))
\<close>


(* ------------------------------ leads-to ------------------------------ *)

section "\<leadsto>"

lemma leadsto_init: "\<turnstile> (Init F) \<and> (F \<leadsto> G) \<longrightarrow> \<diamond>G"
  apply (unfold leadsto_def)
  apply (auto dest!: STL2 [temp_use])
  done

(* \<turnstile> F & (F \<leadsto> G) \<longrightarrow> \<diamond>G *)
lemmas leadsto_init_temp = leadsto_init [where 'a = behavior, unfolded Init_simps]

lemma streett_leadsto: "\<turnstile> (\<box>\<diamond>Init F \<longrightarrow> \<box>\<diamond>G) = (\<diamond>(F \<leadsto> G))"
  apply (unfold leadsto_def)
  apply auto
    apply (simp add: more_temp_simps)
    apply (fastforce elim!: DmdImplE [temp_use] STL4E [temp_use])
   apply (fastforce intro!: InitDmd [temp_use] elim!: STL4E [temp_use])
  apply (subgoal_tac "sigma \<Turnstile> \<box>\<diamond>\<diamond>G")
   apply (simp add: more_temp_simps)
  apply (drule BoxDmdDmdBox [temp_use])
   apply assumption
  apply (fastforce elim!: DmdImplE [temp_use] STL4E [temp_use])
  done

lemma leadsto_infinite: "\<turnstile> \<box>\<diamond>F \<and> (F \<leadsto> G) \<longrightarrow> \<box>\<diamond>G"
  apply clarsimp
  apply (erule InitDmd [temp_use, THEN streett_leadsto [temp_unlift, THEN iffD2, THEN mp]])
  apply (simp add: dmdInitD)
  done

(* In particular, strong fairness is a Streett condition. The following
   rules are sometimes easier to use than WF2 or SF2 below.
*)
lemma leadsto_SF: "\<turnstile> (Enabled(<A>_v) \<leadsto> <A>_v) \<longrightarrow> SF(A)_v"
  apply (unfold SF_def)
  apply (clarsimp elim!: leadsto_infinite [temp_use])
  done

lemma leadsto_WF: "\<turnstile> (Enabled(<A>_v) \<leadsto> <A>_v) \<longrightarrow> WF(A)_v"
  by (clarsimp intro!: SFImplWF [temp_use] leadsto_SF [temp_use])

(* introduce an invariant into the proof of a leadsto assertion.
   \<box>I \<longrightarrow> ((P \<leadsto> Q)  =  (P /\ I \<leadsto> Q))
*)
lemma INV_leadsto: "\<turnstile> \<box>I \<and> (P \<and> I \<leadsto> Q) \<longrightarrow> (P \<leadsto> Q)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply (erule STL4Edup)
   apply assumption
  apply (auto simp: Init_simps dest!: STL2_gen [temp_use])
  done

lemma leadsto_classical: "\<turnstile> (Init F \<and> \<box>\<not>G \<leadsto> G) \<longrightarrow> (F \<leadsto> G)"
  apply (unfold leadsto_def dmd_def)
  apply (force simp: Init_simps elim!: STL4E [temp_use])
  done

lemma leadsto_false: "\<turnstile> (F \<leadsto> #False) = (\<box>\<not>F)"
  apply (unfold leadsto_def)
  apply (simp add: boxNotInitD)
  done

lemma leadsto_exists: "\<turnstile> ((\<exists>x. F x) \<leadsto> G) = (\<forall>x. (F x \<leadsto> G))"
  apply (unfold leadsto_def)
  apply (auto simp: allT [try_rewrite] Init_simps elim!: STL4E [temp_use])
  done

(* basic leadsto properties, cf. Unity *)

lemma ImplLeadsto_gen: "\<turnstile> \<box>(Init F \<longrightarrow> Init G) \<longrightarrow> (F \<leadsto> G)"
  apply (unfold leadsto_def)
  apply (auto intro!: InitDmd_gen [temp_use]
    elim!: STL4E_gen [temp_use] simp: Init_simps)
  done

lemmas ImplLeadsto =
  ImplLeadsto_gen [where 'a = behavior and 'b = behavior, unfolded Init_simps]

lemma ImplLeadsto_simple: "\<And>F G. \<turnstile> F \<longrightarrow> G \<Longrightarrow> \<turnstile> F \<leadsto> G"
  by (auto simp: Init_def intro!: ImplLeadsto_gen [temp_use] necT [temp_use])

lemma EnsuresLeadsto:
  assumes "\<turnstile> A \<and> $P \<longrightarrow> Q`"
  shows "\<turnstile> \<box>A \<longrightarrow> (P \<leadsto> Q)"
  apply (unfold leadsto_def)
  apply (clarsimp elim!: INV_leadsto [temp_use])
  apply (erule STL4E_gen)
  apply (auto simp: Init_defs intro!: PrimeDmd [temp_use] assms [temp_use])
  done

lemma EnsuresLeadsto2: "\<turnstile> \<box>($P \<longrightarrow> Q`) \<longrightarrow> (P \<leadsto> Q)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply (erule STL4E_gen)
  apply (auto simp: Init_simps intro!: PrimeDmd [temp_use])
  done

lemma ensures:
  assumes 1: "\<turnstile> $P \<and> N \<longrightarrow> P` \<or> Q`"
    and 2: "\<turnstile> ($P \<and> N) \<and> A \<longrightarrow> Q`"
  shows "\<turnstile> \<box>N \<and> \<box>(\<box>P \<longrightarrow> \<diamond>A) \<longrightarrow> (P \<leadsto> Q)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply (erule STL4Edup)
   apply assumption
  apply clarsimp
  apply (subgoal_tac "sigmaa \<Turnstile> \<box>($P \<longrightarrow> P` \<or> Q`) ")
   apply (drule unless [temp_use])
   apply (clarsimp dest!: INV1 [temp_use])
  apply (rule 2 [THEN DmdImpl, temp_use, THEN DmdPrime [temp_use]])
   apply (force intro!: BoxDmd_simple [temp_use]
     simp: split_box_conj [try_rewrite] box_stp_act [try_rewrite])
  apply (force elim: STL4E [temp_use] dest: 1 [temp_use])
  done

lemma ensures_simple:
  "\<lbrakk> \<turnstile> $P \<and> N \<longrightarrow> P` \<or> Q`;
      \<turnstile> ($P \<and> N) \<and> A \<longrightarrow> Q`
   \<rbrakk> \<Longrightarrow> \<turnstile> \<box>N \<and> \<box>\<diamond>A \<longrightarrow> (P \<leadsto> Q)"
  apply clarsimp
  apply (erule (2) ensures [temp_use])
  apply (force elim!: STL4E [temp_use])
  done

lemma EnsuresInfinite:
    "\<lbrakk> sigma \<Turnstile> \<box>\<diamond>P; sigma \<Turnstile> \<box>A; \<turnstile> A \<and> $P \<longrightarrow> Q` \<rbrakk> \<Longrightarrow> sigma \<Turnstile> \<box>\<diamond>Q"
  apply (erule leadsto_infinite [temp_use])
  apply (erule EnsuresLeadsto [temp_use])
  apply assumption
  done


(*** Gronning's lattice rules (taken from TLP) ***)
section "Lattice rules"

lemma LatticeReflexivity: "\<turnstile> F \<leadsto> F"
  apply (unfold leadsto_def)
  apply (rule necT InitDmd_gen)+
  done

lemma LatticeTransitivity: "\<turnstile> (G \<leadsto> H) \<and> (F \<leadsto> G) \<longrightarrow> (F \<leadsto> H)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply (erule dup_boxE) (* \<box>\<box>(Init G \<longrightarrow> H) *)
  apply merge_box
  apply (clarsimp elim!: STL4E [temp_use])
  apply (rule dup_dmdD)
  apply (subgoal_tac "sigmaa \<Turnstile> \<diamond>Init G")
   apply (erule DmdImpl2)
   apply assumption
  apply (simp add: dmdInitD)
  done

lemma LatticeDisjunctionElim1: "\<turnstile> (F \<or> G \<leadsto> H) \<longrightarrow> (F \<leadsto> H)"
  apply (unfold leadsto_def)
  apply (auto simp: Init_simps elim!: STL4E [temp_use])
  done

lemma LatticeDisjunctionElim2: "\<turnstile> (F \<or> G \<leadsto> H) \<longrightarrow> (G \<leadsto> H)"
  apply (unfold leadsto_def)
  apply (auto simp: Init_simps elim!: STL4E [temp_use])
  done

lemma LatticeDisjunctionIntro: "\<turnstile> (F \<leadsto> H) \<and> (G \<leadsto> H) \<longrightarrow> (F \<or> G \<leadsto> H)"
  apply (unfold leadsto_def)
  apply clarsimp
  apply merge_box
  apply (auto simp: Init_simps elim!: STL4E [temp_use])
  done

lemma LatticeDisjunction: "\<turnstile> (F \<or> G \<leadsto> H) = ((F \<leadsto> H) \<and> (G \<leadsto> H))"
  by (auto intro: LatticeDisjunctionIntro [temp_use]
    LatticeDisjunctionElim1 [temp_use]
    LatticeDisjunctionElim2 [temp_use])

lemma LatticeDiamond: "\<turnstile> (A \<leadsto> B \<or> C) \<and> (B \<leadsto> D) \<and> (C \<leadsto> D) \<longrightarrow> (A \<leadsto> D)"
  apply clarsimp
  apply (subgoal_tac "sigma \<Turnstile> (B \<or> C) \<leadsto> D")
  apply (erule_tac G = "LIFT (B \<or> C)" in LatticeTransitivity [temp_use])
   apply (fastforce intro!: LatticeDisjunctionIntro [temp_use])+
  done

lemma LatticeTriangle: "\<turnstile> (A \<leadsto> D \<or> B) \<and> (B \<leadsto> D) \<longrightarrow> (A \<leadsto> D)"
  apply clarsimp
  apply (subgoal_tac "sigma \<Turnstile> (D \<or> B) \<leadsto> D")
   apply (erule_tac G = "LIFT (D \<or> B)" in LatticeTransitivity [temp_use])
  apply assumption
  apply (auto intro: LatticeDisjunctionIntro [temp_use] LatticeReflexivity [temp_use])
  done

lemma LatticeTriangle2: "\<turnstile> (A \<leadsto> B \<or> D) \<and> (B \<leadsto> D) \<longrightarrow> (A \<leadsto> D)"
  apply clarsimp
  apply (subgoal_tac "sigma \<Turnstile> B \<or> D \<leadsto> D")
   apply (erule_tac G = "LIFT (B \<or> D)" in LatticeTransitivity [temp_use])
   apply assumption
  apply (auto intro: LatticeDisjunctionIntro [temp_use] LatticeReflexivity [temp_use])
  done

(*** Lamport's fairness rules ***)
section "Fairness rules"

lemma WF1:
  "\<lbrakk> \<turnstile> $P \<and> N  \<longrightarrow> P` \<or> Q`;
      \<turnstile> ($P \<and> N) \<and> <A>_v \<longrightarrow> Q`;
      \<turnstile> $P \<and> N \<longrightarrow> $(Enabled(<A>_v)) \<rbrakk>
  \<Longrightarrow> \<turnstile> \<box>N \<and> WF(A)_v \<longrightarrow> (P \<leadsto> Q)"
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
  assumes 1: "\<turnstile> N \<and> $P \<longrightarrow> $Enabled (<A>_v)"
    and 2: "\<turnstile> N \<and> <A>_v \<longrightarrow> B"
    and 3: "\<turnstile> \<box>(N \<and> [\<not>A]_v) \<longrightarrow> stable P"
  shows "\<turnstile> \<box>N \<and> WF(A)_v \<longrightarrow> (P \<leadsto> B)"
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
  "\<lbrakk> \<turnstile> $P \<and> N  \<longrightarrow> P` \<or> Q`;
      \<turnstile> ($P \<and> N) \<and> <A>_v \<longrightarrow> Q`;
      \<turnstile> \<box>P \<and> \<box>N \<and> \<box>F \<longrightarrow> \<diamond>Enabled(<A>_v) \<rbrakk>
  \<Longrightarrow> \<turnstile> \<box>N \<and> SF(A)_v \<and> \<box>F \<longrightarrow> (P \<leadsto> Q)"
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
  assumes 1: "\<turnstile> N \<and> <B>_f \<longrightarrow> <M>_g"
    and 2: "\<turnstile> $P \<and> P` \<and> <N \<and> A>_f \<longrightarrow> B"
    and 3: "\<turnstile> P \<and> Enabled(<M>_g) \<longrightarrow> Enabled(<A>_f)"
    and 4: "\<turnstile> \<box>(N \<and> [\<not>B]_f) \<and> WF(A)_f \<and> \<box>F \<and> \<diamond>\<box>Enabled(<M>_g) \<longrightarrow> \<diamond>\<box>P"
  shows "\<turnstile> \<box>N \<and> WF(A)_f \<and> \<box>F \<longrightarrow> WF(M)_g"
  apply (clarsimp dest!: BoxWFI [temp_use] BoxDmdBox [temp_use, THEN iffD2]
    simp: WF_def [where A = M])
  apply (erule_tac F = F in dup_boxE)
  apply merge_temp_box
  apply (erule STL4Edup)
   apply assumption
  apply (clarsimp intro!: BoxDmd_simple [temp_use, THEN 1 [THEN DmdImpl, temp_use]])
  apply (rule classical)
  apply (subgoal_tac "sigmaa \<Turnstile> \<diamond> (($P \<and> P` \<and> N) \<and> <A>_f)")
   apply (force simp: angle_def intro!: 2 [temp_use] elim!: DmdImplE [temp_use])
  apply (rule BoxDmd_simple [THEN DmdImpl, unfolded DmdDmd [temp_rewrite], temp_use])
  apply (simp add: NotDmd [temp_use] not_angle [try_rewrite])
  apply merge_act_box
  apply (frule 4 [temp_use])
     apply assumption+
  apply (drule STL6 [temp_use])
   apply assumption
  apply (erule_tac V = "sigmaa \<Turnstile> \<diamond>\<box>P" in thin_rl)
  apply (erule_tac V = "sigmaa \<Turnstile> \<box>F" in thin_rl)
  apply (drule BoxWFI [temp_use])
  apply (erule_tac F = "ACT N \<and> [\<not>B]_f" in dup_boxE)
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
  assumes 1: "\<turnstile> N \<and> <B>_f \<longrightarrow> <M>_g"
    and 2: "\<turnstile> $P \<and> P` \<and> <N \<and> A>_f \<longrightarrow> B"
    and 3: "\<turnstile> P \<and> Enabled(<M>_g) \<longrightarrow> Enabled(<A>_f)"
    and 4: "\<turnstile> \<box>(N \<and> [\<not>B]_f) \<and> SF(A)_f \<and> \<box>F \<and> \<box>\<diamond>Enabled(<M>_g) \<longrightarrow> \<diamond>\<box>P"
  shows "\<turnstile> \<box>N \<and> SF(A)_f \<and> \<box>F \<longrightarrow> SF(M)_g"
  apply (clarsimp dest!: BoxSFI [temp_use] simp: 2 [try_rewrite] SF_def [where A = M])
  apply (erule_tac F = F in dup_boxE)
  apply (erule_tac F = "TEMP \<diamond>Enabled (<M>_g) " in dup_boxE)
  apply merge_temp_box
  apply (erule STL4Edup)
   apply assumption
  apply (clarsimp intro!: BoxDmd_simple [temp_use, THEN 1 [THEN DmdImpl, temp_use]])
  apply (rule classical)
  apply (subgoal_tac "sigmaa \<Turnstile> \<diamond> (($P \<and> P` \<and> N) \<and> <A>_f)")
   apply (force simp: angle_def intro!: 2 [temp_use] elim!: DmdImplE [temp_use])
  apply (rule BoxDmd_simple [THEN DmdImpl, unfolded DmdDmd [temp_rewrite], temp_use])
  apply (simp add: NotDmd [temp_use] not_angle [try_rewrite])
  apply merge_act_box
  apply (frule 4 [temp_use])
     apply assumption+
  apply (erule_tac V = "sigmaa \<Turnstile> \<box>F" in thin_rl)
  apply (drule BoxSFI [temp_use])
  apply (erule_tac F = "TEMP \<diamond>Enabled (<M>_g)" in dup_boxE)
  apply (erule_tac F = "ACT N \<and> [\<not>B]_f" in dup_boxE)
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
    and 2: "\<And>x. sigma \<Turnstile> F x \<leadsto> (G \<or> (\<exists>y. #((y,x)\<in>r) \<and> F y))    "
  shows "sigma \<Turnstile> F x \<leadsto> G"
  apply (rule 1 [THEN wf_induct])
  apply (rule LatticeTriangle [temp_use])
   apply (rule 2)
  apply (auto simp: leadsto_exists [try_rewrite])
  apply (case_tac "(y,x) \<in> r")
   apply force
  apply (force simp: leadsto_def Init_simps intro!: necT [temp_use])
  done

(* If r is well-founded, state function v cannot decrease forever *)
lemma wf_not_box_decrease: "\<And>r. wf r \<Longrightarrow> \<turnstile> \<box>[ (v`, $v) \<in> #r ]_v \<longrightarrow> \<diamond>\<box>[#False]_v"
  apply clarsimp
  apply (rule ccontr)
  apply (subgoal_tac "sigma \<Turnstile> (\<exists>x. v=#x) \<leadsto> #False")
   apply (drule leadsto_false [temp_use, THEN iffD1, THEN STL2_gen [temp_use]])
   apply (force simp: Init_defs)
  apply (clarsimp simp: leadsto_exists [try_rewrite] not_square [try_rewrite] more_temp_simps)
  apply (erule wf_leadsto)
  apply (rule ensures_simple [temp_use])
   apply (auto simp: square_def angle_def)
  done

(* "wf r  \<Longrightarrow>  \<turnstile> \<diamond>\<box>[ (v`, $v) : #r ]_v \<longrightarrow> \<diamond>\<box>[#False]_v" *)
lemmas wf_not_dmd_box_decrease =
  wf_not_box_decrease [THEN DmdImpl, unfolded more_temp_simps]

(* If there are infinitely many steps where v decreases, then there
   have to be infinitely many non-stuttering steps where v doesn't decrease.
*)
lemma wf_box_dmd_decrease:
  assumes 1: "wf r"
  shows "\<turnstile> \<box>\<diamond>((v`, $v) \<in> #r) \<longrightarrow> \<box>\<diamond><(v`, $v) \<notin> #r>_v"
  apply clarsimp
  apply (rule ccontr)
  apply (simp add: not_angle [try_rewrite] more_temp_simps)
  apply (drule 1 [THEN wf_not_dmd_box_decrease [temp_use]])
  apply (drule BoxDmdDmdBox [temp_use])
   apply assumption
  apply (subgoal_tac "sigma \<Turnstile> \<box>\<diamond> ((#False) ::action)")
   apply force
  apply (erule STL4E)
  apply (rule DmdImpl)
  apply (force intro: 1 [THEN wf_irrefl, temp_use])
  done

(* In particular, for natural numbers, if n decreases infinitely often
   then it has to increase infinitely often.
*)
lemma nat_box_dmd_decrease: "\<And>n::nat stfun. \<turnstile> \<box>\<diamond>(n` < $n) \<longrightarrow> \<box>\<diamond>($n < n`)"
  apply clarsimp
  apply (subgoal_tac "sigma \<Turnstile> \<box>\<diamond><\<not> ((n`,$n) \<in> #less_than)>_n")
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
    and 2: "(\<And>x. basevars (x,vs) \<Longrightarrow> sigma \<Turnstile> F x)"
  shows "sigma \<Turnstile> (\<forall>\<forall>x. F x)"
  by (auto simp: aall_def elim!: eexE [temp_use] intro!: 1 dest!: 2 [temp_use])

lemma aallE: "\<turnstile> (\<forall>\<forall>x. F x) \<longrightarrow> F x"
  apply (unfold aall_def)
  apply clarsimp
  apply (erule contrapos_np)
  apply (force intro!: eexI [temp_use])
  done

(* monotonicity of quantification *)
lemma eex_mono:
  assumes 1: "sigma \<Turnstile> \<exists>\<exists>x. F x"
    and 2: "\<And>x. sigma \<Turnstile> F x \<longrightarrow> G x"
  shows "sigma \<Turnstile> \<exists>\<exists>x. G x"
  apply (rule unit_base [THEN 1 [THEN eexE]])
  apply (rule eexI [temp_use])
  apply (erule 2 [unfolded intensional_rews, THEN mp])
  done

lemma aall_mono:
  assumes 1: "sigma \<Turnstile> \<forall>\<forall>x. F(x)"
    and 2: "\<And>x. sigma \<Turnstile> F(x) \<longrightarrow> G(x)"
  shows "sigma \<Turnstile> \<forall>\<forall>x. G(x)"
  apply (rule unit_base [THEN aallI])
  apply (rule 2 [unfolded intensional_rews, THEN mp])
  apply (rule 1 [THEN aallE [temp_use]])
  done

(* Derived history introduction rule *)
lemma historyI:
  assumes 1: "sigma \<Turnstile> Init I"
    and 2: "sigma \<Turnstile> \<box>N"
    and 3: "basevars vs"
    and 4: "\<And>h. basevars(h,vs) \<Longrightarrow> \<turnstile> I \<and> h = ha \<longrightarrow> HI h"
    and 5: "\<And>h s t. \<lbrakk> basevars(h,vs); N (s,t); h t = hb (h s) (s,t) \<rbrakk> \<Longrightarrow> HN h (s,t)"
  shows "sigma \<Turnstile> \<exists>\<exists>h. Init (HI h) \<and> \<box>(HN h)"
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

lemma "\<turnstile> \<exists>\<exists>h. Init(h = #True) \<and> \<box>(h` = (\<not>$h))"
  apply (rule tempI)
  apply (rule historyI)
  apply (force simp: Init_defs intro!: unit_base [temp_use] necT [temp_use])+
  done

end
