(*  Title:      HOL/Datatype_Examples/IsaFoR_Datatypes.thy
    Author:     Rene Thiemann, UIBK
    Copyright   2014

Benchmark consisting of datatypes defined in IsaFoR.
*)

header {* Benchmark Consisting of Datatypes Defined in IsaFoR *}

theory IsaFoR_Datatypes
imports Real
begin

datatype_new (discs_sels) ('f, 'l) lab =
    Lab "('f, 'l) lab" 'l
  | FunLab "('f, 'l) lab" "('f, 'l) lab list"
  | UnLab 'f
  | Sharp "('f, 'l) lab"

datatype_new (discs_sels) 'f projL = Projection "(('f \<times> nat) \<times> nat) list"

datatype_new (discs_sels) ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"
datatype_new (discs_sels) ('f, 'v) ctxt =
    Hole ("\<box>")
  | More 'f "('f, 'v) term list" "('f, 'v) ctxt" "('f, 'v) term list"

type_synonym ('f, 'v) rule = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) trs  = "('f, 'v) rule set"

type_synonym ('f, 'v) rules = "('f, 'v) rule list"
type_synonym ('f, 'l, 'v) ruleLL  = "(('f, 'l) lab, 'v) rule"
type_synonym ('f, 'l, 'v) trsLL   = "(('f, 'l) lab, 'v) rules"
type_synonym ('f, 'l, 'v) termsLL = "(('f, 'l) lab, 'v) term list"

datatype_new (discs_sels) pos = Empty ("\<epsilon>") | PCons "nat" "pos" (infixr "<#" 70)

type_synonym  ('f, 'v) prseq = "(pos \<times> ('f, 'v) rule \<times> bool \<times> ('f, 'v) term) list"
type_synonym  ('f, 'v) rseq = "(pos \<times> ('f, 'v) rule \<times> ('f, 'v) term) list"

type_synonym ('f, 'l, 'v) rseqL   = "((('f, 'l) lab, 'v) rule \<times> (('f, 'l) lab, 'v) rseq) list"
type_synonym ('f, 'l, 'v) dppLL   =
  "bool \<times> bool \<times> ('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) trsLL \<times>
  ('f, 'l, 'v) termsLL \<times>
  ('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) trsLL"

type_synonym ('f, 'l, 'v) qreltrsLL =
  "bool \<times> ('f, 'l, 'v) termsLL \<times> ('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) trsLL"

type_synonym ('f, 'l, 'v) qtrsLL =
  "bool \<times> ('f, 'l, 'v) termsLL \<times> ('f, 'l, 'v) trsLL"

datatype_new (discs_sels) location = H | A | B | R

type_synonym ('f, 'v) forb_pattern = "('f, 'v) ctxt \<times> ('f, 'v) term \<times> location"
type_synonym ('f, 'v) forb_patterns = "('f, 'v) forb_pattern set"

type_synonym ('f, 'l, 'v) fptrsLL =
  "(('f, 'l) lab, 'v) forb_pattern list \<times> ('f, 'l, 'v) trsLL"

type_synonym ('f, 'l, 'v) prob = "('f, 'l, 'v) qreltrsLL + ('f, 'l, 'v) dppLL"

type_synonym ('f, 'a) lpoly_inter = "'f \<times> nat \<Rightarrow> ('a \<times> 'a list)"
type_synonym ('f, 'a) lpoly_interL = "(('f \<times> nat) \<times> ('a \<times> 'a list)) list"

type_synonym 'v monom = "('v \<times> nat) list"
type_synonym ('v, 'a) poly = "('v monom \<times> 'a) list"
type_synonym ('f, 'a) poly_inter_list = "(('f \<times> nat) \<times> (nat, 'a) poly) list"
type_synonym 'a vec = "'a list"
type_synonym 'a mat = "'a vec list"

datatype_new (discs_sels) arctic = MinInfty | Num_arc int
datatype_new (discs_sels) 'a arctic_delta = MinInfty_delta | Num_arc_delta 'a
datatype_new (discs_sels) order_tag = Lex | Mul

type_synonym 'f status_prec_repr = "(('f \<times> nat) \<times> (nat \<times> order_tag)) list"

datatype_new (discs_sels) af_entry =
    Collapse nat
  | AFList "nat list"

type_synonym 'f afs_list = "(('f \<times> nat) \<times> af_entry) list"
type_synonym 'f prec_weight_repr = "(('f \<times> nat) \<times> (nat \<times> nat \<times> (nat list option))) list \<times> nat"

datatype_new (discs_sels) 'f redtriple_impl =
    Int_carrier "('f, int) lpoly_interL"
  | Int_nl_carrier "('f, int) poly_inter_list"
  | Rat_carrier "('f, rat) lpoly_interL"
  | Rat_nl_carrier rat "('f, rat) poly_inter_list"
  | Real_carrier "('f, real) lpoly_interL"
  | Real_nl_carrier real "('f, real) poly_inter_list"
  | Arctic_carrier "('f, arctic) lpoly_interL"
  | Arctic_rat_carrier "('f, rat arctic_delta) lpoly_interL"
  | Int_mat_carrier nat nat "('f, int mat) lpoly_interL"
  | Rat_mat_carrier nat nat "('f, rat mat) lpoly_interL"
  | Real_mat_carrier nat nat "('f, real mat) lpoly_interL"
  | Arctic_mat_carrier nat "('f, arctic mat) lpoly_interL"
  | Arctic_rat_mat_carrier nat "('f, rat arctic_delta mat) lpoly_interL"
  | RPO "'f status_prec_repr" "'f afs_list"
  | KBO "'f prec_weight_repr" "'f afs_list"

datatype_new (discs_sels) list_order_type = MS_Ext | Max_Ext | Min_Ext  | Dms_Ext
type_synonym 'f scnp_af = "(('f \<times> nat) \<times> (nat \<times> nat) list) list"

datatype_new (discs_sels) 'f root_redtriple_impl = SCNP list_order_type "'f scnp_af" "'f redtriple_impl"

type_synonym 'f sig_map_list = "(('f \<times> nat) \<times> 'f list) list"
type_synonym ('f, 'v) uncurry_info = "'f \<times> 'f sig_map_list \<times> ('f, 'v) rules \<times> ('f, 'v) rules"

datatype_new (discs_sels) arithFun =
    Arg nat
  | Const nat
  | Sum "arithFun list"
  | Max "arithFun list"
  | Min "arithFun list"
  | Prod "arithFun list"
  | IfEqual arithFun arithFun arithFun arithFun

datatype_new (discs_sels) 'f sl_inter = SL_Inter nat "(('f \<times> nat) \<times> arithFun) list"
datatype_new (discs_sels) ('f, 'v) sl_variant =
    Rootlab "('f \<times> nat) option"
  | Finitelab "'f sl_inter"
  | QuasiFinitelab "'f sl_inter" 'v

type_synonym ('f, 'v) crit_pair_joins = "(('f, 'v) term \<times> ('f, 'v) rseq \<times> ('f, 'v) term \<times> ('f, 'v) rseq) list"

datatype_new (discs_sels) 'f join_info = Guided "('f, string) crit_pair_joins" | Join_NF | Join_BFS nat

type_synonym unknown_info = string

type_synonym dummy_prf = unit

datatype_new (discs_sels) ('f, 'v) complex_constant_removal_prf = Complex_Constant_Removal_Proof
  "('f, 'v) term"
  "(('f, 'v) rule \<times> ('f, 'v) rule) list"

datatype_new (discs_sels) ('f, 'v) cond_constraint =
    CC_cond bool "('f, 'v) rule"
  | CC_rewr "('f, 'v) term" "('f, 'v) term"
  | CC_impl "('f, 'v) cond_constraint list" "('f, 'v) cond_constraint"
  | CC_all 'v "('f, 'v) cond_constraint"

type_synonym ('f, 'v, 'w) gsubstL = "('v \<times> ('f, 'w) term) list"
type_synonym ('f, 'v) substL = "('f, 'v, 'v) gsubstL"

datatype_new (discs_sels) ('f, 'v) cond_constraint_prf =
    Final
  | Delete_Condition "('f, 'v) cond_constraint" "('f, 'v) cond_constraint_prf"
  | Different_Constructor "('f, 'v) cond_constraint"
  | Same_Constructor "('f, 'v) cond_constraint" "('f, 'v) cond_constraint" "('f, 'v) cond_constraint_prf"
  | Variable_Equation 'v "('f, 'v) term" "('f, 'v) cond_constraint" "('f, 'v) cond_constraint_prf"
  | Funarg_Into_Var "('f, 'v) cond_constraint" nat 'v "('f, 'v) cond_constraint" "('f, 'v) cond_constraint_prf"
  | Simplify_Condition "('f, 'v) cond_constraint" "('f, 'v) substL" "('f, 'v) cond_constraint" "('f, 'v) cond_constraint_prf"
  | Induction "('f, 'v) cond_constraint" "('f, 'v) cond_constraint list" "(('f, 'v) rule \<times> (('f, 'v) term \<times> 'v list) list \<times> ('f, 'v) cond_constraint \<times> ('f, 'v) cond_constraint_prf) list"

datatype_new (discs_sels) ('f, 'v) cond_red_pair_prf =
  Cond_Red_Pair_Prf
    'f "(('f, 'v) cond_constraint \<times> ('f, 'v) rules \<times> ('f, 'v) cond_constraint_prf) list" nat nat

datatype_new (discs_sels) ('q, 'f) ta_rule = TA_rule 'f "'q list" 'q ("_ _ \<rightarrow> _")
datatype_new (discs_sels) ('q, 'f) tree_automaton = Tree_Automaton "'q list" "('q, 'f) ta_rule list" "('q \<times> 'q) list"
datatype_new (discs_sels) 'q ta_relation =
    Decision_Proc
  | Id_Relation
  | Some_Relation "('q \<times> 'q) list"

datatype_new (discs_sels) boundstype = Roof | Match
datatype_new (discs_sels) ('f, 'q) bounds_info = Bounds_Info boundstype nat "'q list" "('q, 'f \<times> nat) tree_automaton" "'q ta_relation"

datatype_new (discs_sels) ('f, 'v) pat_eqv_prf =
    Pat_Dom_Renaming "('f, 'v) substL"
  | Pat_Irrelevant "('f, 'v) substL" "('f, 'v) substL"
  | Pat_Simplify "('f, 'v) substL" "('f, 'v) substL"

datatype_new (discs_sels) pat_rule_pos = Pat_Base | Pat_Pump | Pat_Close

datatype_new (discs_sels) ('f, 'v) pat_rule_prf =
    Pat_OrigRule "('f, 'v) rule" bool
  | Pat_InitPump "('f, 'v) pat_rule_prf" "('f, 'v) substL" "('f, 'v) substL"
  | Pat_InitPumpCtxt "('f, 'v) pat_rule_prf" "('f, 'v) substL" pos 'v
  | Pat_Equiv "('f, 'v) pat_rule_prf" bool "('f, 'v) pat_eqv_prf"
  | Pat_Narrow "('f, 'v) pat_rule_prf" "('f, 'v) pat_rule_prf" pos
  | Pat_Inst "('f, 'v) pat_rule_prf" "('f, 'v) substL" pat_rule_pos
  | Pat_Rewr "('f, 'v) pat_rule_prf" "('f, 'v) term \<times> ('f, 'v) rseq" pat_rule_pos 'v
  | Pat_Exp_Sigma "('f, 'v) pat_rule_prf" nat

datatype_new (discs_sels) ('f, 'v) non_loop_prf =
    Non_Loop_Prf "('f, 'v) pat_rule_prf" "('f, 'v) substL" "('f, 'v) substL" nat nat pos

datatype_new (discs_sels) ('f, 'l, 'v) problem =
    SN_TRS "('f, 'l, 'v) qreltrsLL"
  | SN_FP_TRS "('f, 'l, 'v) fptrsLL"
  | Finite_DPP "('f, 'l, 'v) dppLL"
  | Unknown_Problem unknown_info
  | Not_SN_TRS "('f, 'l, 'v) qtrsLL"
  | Not_RelSN_TRS "('f, 'l, 'v) qreltrsLL"
  | Infinite_DPP "('f, 'l, 'v) dppLL"
  | Not_SN_FP_TRS "('f, 'l, 'v) fptrsLL"

declare [[bnf_timing]]

datatype_new (discs_sels) ('f, 'l, 'v, 'a, 'b, 'c, 'd, 'e) generic_assm_proof =
    SN_assm_proof "('f, 'l, 'v) qreltrsLL" 'a
  | Finite_assm_proof "('f, 'l, 'v) dppLL" 'b
  | SN_FP_assm_proof "('f, 'l, 'v) fptrsLL" 'c
  | Not_SN_assm_proof "('f, 'l, 'v) qtrsLL" 'a
  | Infinite_assm_proof "('f, 'l, 'v) dppLL" 'b
  | Not_RelSN_assm_proof "('f, 'l, 'v) qreltrsLL" 'c
  | Not_SN_FP_assm_proof "('f, 'l, 'v) fptrsLL" 'd
  | Unknown_assm_proof unknown_info 'e

type_synonym ('f, 'l, 'v, 'a, 'b, 'c, 'd) assm_proof = "('f, 'l, 'v, 'a, 'b, 'c, dummy_prf, 'd) generic_assm_proof"

datatype_new (discs_sels) ('f, 'l, 'v) assm =
    SN_assm "('f, 'l, 'v) problem list" "('f, 'l, 'v) qreltrsLL"
  | SN_FP_assm "('f, 'l, 'v) problem list" "('f, 'l, 'v) fptrsLL"
  | Finite_assm "('f, 'l, 'v) problem list" "('f, 'l, 'v) dppLL"
  | Unknown_assm "('f, 'l, 'v) problem list" unknown_info
  | Not_SN_assm "('f, 'l, 'v) problem list" "('f, 'l, 'v) qtrsLL"
  | Not_RelSN_assm "('f, 'l, 'v) problem list" "('f, 'l, 'v) qreltrsLL"
  | Not_SN_FP_assm "('f, 'l, 'v) problem list" "('f, 'l, 'v) fptrsLL"
  | Infinite_assm "('f, 'l, 'v) problem list" "('f, 'l, 'v) dppLL"

fun satisfied :: "('f, 'l, 'v) problem \<Rightarrow> bool" where
  "satisfied (SN_TRS t) = (t = t)"
| "satisfied (SN_FP_TRS t) = (t \<noteq> t)"
| "satisfied (Finite_DPP d) = (d \<noteq> d)"
| "satisfied (Unknown_Problem s) = (s = ''foo'')"
| "satisfied (Not_SN_TRS (nfs, q, r)) = (length q = length r)"
| "satisfied (Not_RelSN_TRS (nfs, q, r, rw)) = (r = rw)"
| "satisfied (Infinite_DPP d) = (d = d)"
| "satisfied (Not_SN_FP_TRS t) = (t = t)"

fun collect_assms :: "('tp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('dpp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('fptp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('unk \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('f, 'l, 'v, 'tp, 'dpp, 'fptp, 'unk) assm_proof \<Rightarrow> ('f, 'l, 'v) assm list" where
  "collect_assms tp dpp fptp unk (SN_assm_proof t prf) = tp prf"
| "collect_assms tp dpp fptp unk (SN_FP_assm_proof t prf) = fptp prf"
| "collect_assms tp dpp fptp unk (Finite_assm_proof d prf) = dpp prf"
| "collect_assms tp dpp fptp unk (Unknown_assm_proof p prf) = unk prf"
| "collect_assms _ _ _ _ _ = []"

fun collect_neg_assms :: "('tp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('dpp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('rtp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('fptp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('unk \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('f, 'l, 'v, 'tp, 'dpp, 'rtp, 'fptp, 'unk) generic_assm_proof \<Rightarrow> ('f, 'l, 'v) assm list" where
  "collect_neg_assms tp dpp rtp fptp unk (Not_SN_assm_proof t prf) = tp prf"
| "collect_neg_assms tp dpp rtp fptp unk (Infinite_assm_proof d prf) = dpp prf"
| "collect_neg_assms tp dpp rtp fptp unk (Not_RelSN_assm_proof t prf) = rtp prf"
| "collect_neg_assms tp dpp rtp fptp unk (Not_SN_FP_assm_proof t prf) = fptp prf"
| "collect_neg_assms tp dpp rtp fptp unk (Unknown_assm_proof p prf) = unk prf"
| "collect_neg_assms tp dpp rtp fptp unk _ = []"

datatype_new (discs_sels) ('f, 'l, 'v) dp_nontermination_proof =
    DP_Loop "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) prseq" "(('f, 'l) lab, 'v) substL" "(('f, 'l) lab, 'v) ctxt"
  | DP_Nonloop "(('f, 'l) lab, 'v) non_loop_prf"
  | DP_Rule_Removal "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) dp_nontermination_proof"
  | DP_Q_Increase "('f, 'l, 'v) termsLL" "('f, 'l, 'v) dp_nontermination_proof"
  | DP_Q_Reduction "('f, 'l, 'v) termsLL" "('f, 'l, 'v) dp_nontermination_proof"
  | DP_Termination_Switch "('f, 'l) lab join_info" "('f, 'l, 'v) dp_nontermination_proof"
  | DP_Instantiation "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_nontermination_proof"
  | DP_Rewriting "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) ruleLL" "(('f, 'l) lab, 'v) rule" pos "('f, 'l, 'v) dp_nontermination_proof"
  | DP_Narrowing "('f, 'l, 'v) ruleLL" pos "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_nontermination_proof"
  | DP_Assume_Infinite  "('f, 'l, 'v) dppLL"
      "('f, 'l, 'v, ('f, 'l, 'v) trs_nontermination_proof,
       ('f, 'l, 'v) dp_nontermination_proof,
       ('f, 'l, 'v) reltrs_nontermination_proof,
       ('f, 'l, 'v) fp_nontermination_proof,
       ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"
and ('f, 'l, 'v) "trs_nontermination_proof" =
    TRS_Loop "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) rseq" "(('f, 'l) lab, 'v) substL" "(('f, 'l) lab, 'v) ctxt"
  | TRS_Not_Well_Formed
  | TRS_Rule_Removal "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_nontermination_proof"
  | TRS_String_Reversal "('f, 'l, 'v) trs_nontermination_proof"
  | TRS_DP_Trans "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_nontermination_proof"
  | TRS_Nonloop "(('f, 'l) lab, 'v) non_loop_prf"
  | TRS_Q_Increase "('f, 'l, 'v) termsLL" "('f, 'l, 'v) trs_nontermination_proof"
  | TRS_Assume_Not_SN  "('f, 'l, 'v) qtrsLL"
      "('f, 'l, 'v, ('f, 'l, 'v) trs_nontermination_proof,
       ('f, 'l, 'v) dp_nontermination_proof,
       ('f, 'l, 'v) reltrs_nontermination_proof,
       ('f, 'l, 'v) fp_nontermination_proof,
       ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"
and ('f, 'l, 'v)"reltrs_nontermination_proof" =
    Rel_Loop "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) prseq" "(('f, 'l) lab, 'v) substL" "(('f, 'l) lab, 'v) ctxt"
  | Rel_Not_Well_Formed
  | Rel_Rule_Removal "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) reltrs_nontermination_proof"
  | Rel_R_Not_SN "('f, 'l, 'v) trs_nontermination_proof"
  | Rel_TRS_Assume_Not_SN  "('f, 'l, 'v) qreltrsLL"
      "('f, 'l, 'v, ('f, 'l, 'v) trs_nontermination_proof,
       ('f, 'l, 'v) dp_nontermination_proof,
       ('f, 'l, 'v) reltrs_nontermination_proof,
       ('f, 'l, 'v) fp_nontermination_proof,
       ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"
and ('f, 'l, 'v) "fp_nontermination_proof" =
    FPTRS_Loop "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) rseq" "(('f, 'l) lab, 'v) substL" "(('f, 'l) lab, 'v) ctxt"
  | FPTRS_Rule_Removal "('f, 'l, 'v) trsLL" "('f, 'l, 'v) fp_nontermination_proof"
  | FPTRS_Assume_Not_SN  "('f, 'l, 'v) fptrsLL"
      "('f, 'l, 'v, ('f, 'l, 'v) trs_nontermination_proof,
       ('f, 'l, 'v) dp_nontermination_proof,
       ('f, 'l, 'v) reltrs_nontermination_proof,
       ('f, 'l, 'v) fp_nontermination_proof,
       ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"
and ('f, 'l, 'v) neg_unknown_proof =
    Assume_NT_Unknown unknown_info
      "('f, 'l, 'v, ('f, 'l, 'v) trs_nontermination_proof,
       ('f, 'l, 'v) dp_nontermination_proof,
       ('f, 'l, 'v) reltrs_nontermination_proof,
       ('f, 'l, 'v) fp_nontermination_proof,
       ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"

datatype_new (discs_sels) ('f, 'l, 'v) dp_termination_proof =
    P_is_Empty
  | Subterm_Criterion_Proc "('f, 'l) lab projL" "('f, 'l, 'v) rseqL"
      "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Redpair_Proc "('f, 'l) lab root_redtriple_impl + ('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL"  "('f, 'l, 'v) dp_termination_proof"
  | Redpair_UR_Proc "('f, 'l) lab root_redtriple_impl + ('f, 'l) lab redtriple_impl"
      "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Usable_Rules_Proc "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Dep_Graph_Proc "(('f, 'l, 'v) dp_termination_proof option \<times> ('f, 'l, 'v) trsLL) list"
  | Mono_Redpair_Proc "('f, 'l) lab redtriple_impl"
      "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Mono_Redpair_UR_Proc "('f, 'l) lab redtriple_impl"
      "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Size_Change_Subterm_Proc "((('f, 'l) lab, 'v) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list"
  | Size_Change_Redpair_Proc "('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL option"
      "((('f, 'l) lab, 'v) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list"
  | Uncurry_Proc "nat option" "(('f, 'l) lab, 'v) uncurry_info"
      "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Fcc_Proc "('f, 'l) lab" "(('f, 'l) lab, 'v) ctxt list"
      "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Split_Proc
      "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) dp_termination_proof" "('f, 'l, 'v) dp_termination_proof"
  | Semlab_Proc
      "(('f, 'l) lab, 'v) sl_variant" "('f, 'l, 'v) trsLL"
      "(('f, 'l) lab, 'v) term list" "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) dp_termination_proof"
  | Switch_Innermost_Proc "('f, 'l) lab join_info" "('f, 'l, 'v) dp_termination_proof"
  | Rewriting_Proc
      "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) ruleLL"
      "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) ruleLL" pos "('f, 'l, 'v) dp_termination_proof"
  | Instantiation_Proc "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Forward_Instantiation_Proc
      "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) dp_termination_proof"
  | Narrowing_Proc "('f, 'l, 'v) ruleLL" pos "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Assume_Finite
      "('f, 'l, 'v) dppLL" "('f, 'l, 'v, ('f, 'l, 'v) trs_termination_proof, ('f, 'l, 'v) dp_termination_proof, ('f, 'l, 'v) fptrs_termination_proof, ('f, 'l, 'v) unknown_proof) assm_proof list"
  | Unlab_Proc "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
  | Q_Reduction_Proc "('f, 'l, 'v) termsLL" "('f, 'l, 'v) dp_termination_proof"
  | Complex_Constant_Removal_Proc "(('f, 'l) lab, 'v) complex_constant_removal_prf" "('f, 'l, 'v) dp_termination_proof"
  | General_Redpair_Proc
      "('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL"
      "(('f, 'l) lab, 'v) cond_red_pair_prf" "('f, 'l, 'v) dp_termination_proof list"
  | To_Trs_Proc "('f, 'l, 'v) trs_termination_proof"
and ('f, 'l, 'v) trs_termination_proof =
    DP_Trans bool bool "(('f, 'l) lab, 'v) rules" "('f, 'l, 'v) dp_termination_proof"
  | Rule_Removal "('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
  | String_Reversal "('f, 'l, 'v) trs_termination_proof"
  | Bounds "(('f, 'l) lab, 'v) bounds_info"
  | Uncurry "(('f, 'l) lab, 'v) uncurry_info" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
  | Semlab
      "(('f, 'l) lab, 'v) sl_variant" "(('f, 'l) lab, 'v) term list"
      "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
  | R_is_Empty
  | Fcc "(('f, 'l) lab, 'v) ctxt list" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
  | Split "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof" "('f, 'l, 'v) trs_termination_proof"
  | Switch_Innermost "('f, 'l) lab join_info" "('f, 'l, 'v) trs_termination_proof"
  | Drop_Equality "('f, 'l, 'v) trs_termination_proof"
  | Remove_Nonapplicable_Rules "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
  | Assume_SN "('f, 'l, 'v) qreltrsLL" "('f, 'l, 'v, ('f, 'l, 'v) trs_termination_proof, ('f, 'l, 'v) dp_termination_proof, ('f, 'l, 'v) fptrs_termination_proof, ('f, 'l, 'v) unknown_proof) assm_proof list"
and ('f, 'l, 'v) unknown_proof =
    Assume_Unknown unknown_info "('f, 'l, 'v, ('f, 'l, 'v) trs_termination_proof, ('f, 'l, 'v) dp_termination_proof, ('f, 'l, 'v) fptrs_termination_proof, ('f, 'l, 'v) unknown_proof) assm_proof list"
and ('f, 'l, 'v) fptrs_termination_proof =
    Assume_FP_SN "('f, 'l, 'v) fptrsLL" "('f, 'l, 'v, ('f, 'l, 'v) trs_termination_proof, ('f, 'l, 'v) dp_termination_proof, ('f, 'l, 'v) fptrs_termination_proof, ('f, 'l, 'v) unknown_proof) assm_proof list"

end
