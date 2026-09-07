(*  Title:      HOL/Tools/SMT/alethe/alethe_replay_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University of Freiburg
    Author:     Pascal Walter, University of Freiburg
    Author:     Hanna Lachnitt, Stanford University

Proof method for replaying Alethe proofs.
*)

signature ALETHE_REPLAY_METHODS =
sig

  (*
  Could be included in the future:
   let, bind_let
   nary_elim
   eq_symmetric
  *)
  datatype alethe_rule =
   (*input: a repeated (normalized) assumption or an assumption in a subproof*)
   Normalized_Input | Local_Input |
   (*Used to introduce skolem constants*)
   Definition |
   (*Subproof:*)
   Subproof |
   (*Quantifiers:*)
   Forall_Inst | Qnt_Rm_Unused | Qnt_Join | Onepoint | Bind | Sko_Forall | Sko_Ex |
   (*Boolean Constants*)
   False | True |
   (*Conjunction:*)
   And | Not_And | And_Pos | And_Neg |
   (*Disjunction:*)
   Or | Or_Pos | Not_Or | Or_Neg |
   (*Implication:*)
   Implies | Implies_Neg1 | Implies_Neg2 | Implies_Pos | Not_Implies1 | Not_Implies2 |
   (*Equivalence:*)
   Equiv_neg1 | Equiv_pos1 | Equiv_pos2 | Equiv_neg2 | Not_Equiv1 | Not_Equiv2 | Equiv1 | Equiv2 |
   (*If-then-else:*)
   ITE_Pos1 | ITE_Pos2 | ITE_Neg1 | ITE_Neg2 | Not_ITE1 | Not_ITE2 | ITE_Intro | ITE1 | ITE2 |
   (*Equality:*)
   Eq_Congruent | Eq_Reflexive | Eq_Transitive | Eq_Congruent_Pred | Trans | Refl | Cong |
   (*xor:*)
   Xor_Pos1 | Xor_Pos2 | Xor_Neg1 | Xor_Neg2 | Xor1 | Xor2 | Not_Xor1 | Not_Xor2 |
   (*Arithmetic:*)
   LA_Disequality | LA_Generic | LA_Tautology | LIA_Generic | LA_Totality | LA_RW_Eq |
   NLA_Generic | LA_Mult_Pos | LA_Mult_Neg | Poly_Simp | Poly_Simp_Rel |
   (*Resolution:*)
   Theory_Resolution | Resolution |
   (*Simplification Rules*)
   Bool_Simplify | Or_Simplify | Not_Simplify | And_Simplify | Equiv_Simplify |
   Implies_Simplify | Connective_Def | Minus_Simplify | Unary_Minus_Simplify | Comp_Simplify |
   Eq_Simplify | ITE_Simplify | Sum_Simplify | Prod_Simplify | Div_Simplify | RARE_Rewrite | Evaluate |
   Qnt_Simplify | Not_Not | Tautological_Clause | Distinct_Elim |
   Miniscope_Distribute | Miniscope_Split | Miniscope_ITE |
   AC_Simp | ACI_Simp |
   (*Extended rules*)
   Symm | Not_Symm | Reordering | Shuffle | Contraction |
   And_Intro |
   (*Other Rules*)
   Other_Rule of string |
   Hole | Trust |
   Bfun_Elim |
   Qnt_CNF |
   (*For compression*)
   Theory_Resolution2 | Weakening |
   (*Unsupported rule*)
   Unsupported

  val requires_subproof_assms : string list -> string -> bool
  val requires_local_input: string list -> string -> bool

  val string_of_alethe_rule: alethe_rule -> string

  type alethe_tac_step_args = Proof.context -> thm list -> term list -> term -> thm
  type alethe_tac_context_args = Proof.context -> thm list -> term list -> term -> thm
  type alethe_tac_args = Proof.context -> thm list -> term -> Alethe_Node.tactic_args option -> thm
  type alethe_tac_context_args_and_arg = Proof.context -> thm list -> term list -> term -> Alethe_Node.tactic_args option -> thm
  type alethe_tac_step_args_and_arg = Proof.context -> thm list -> term list -> term -> Alethe_Node.tactic_args option -> thm
  type alethe_tac = Proof.context -> thm list -> term -> thm

  val bind: alethe_tac_context_args
  val and_rule: alethe_tac_args
  val and_neg_rule: alethe_tac
  val and_pos: alethe_tac_args
  val rewrite_and_simplify: alethe_tac
  val rewrite_bool_simplify: alethe_tac
  val rewrite_comp_simplify: alethe_tac
  val rewrite_minus_simplify: alethe_tac
  val rewrite_not_simplify: alethe_tac
  val rewrite_eq_simplify: alethe_tac
  val rewrite_equiv_simplify: alethe_tac
  val rewrite_implies_simplify: alethe_tac
  val rewrite_or_simplify: alethe_tac
  val cong: alethe_tac_args
  val equality_ordered_cong: alethe_tac_args
  val rewrite_connective_def: alethe_tac
  val distinct_elim: alethe_tac
  val eq_congruent: alethe_tac
  val eq_congruent_pred: alethe_tac
  val eq_reflexive: alethe_tac
  val eq_transitive: alethe_tac
  val equiv1: alethe_tac
  val equiv2: alethe_tac
  val equiv_neg1: alethe_tac
  val equiv_neg2: alethe_tac
  val equiv_pos1: alethe_tac
  val equiv_pos2: alethe_tac
  val xor_pos1: alethe_tac
  val xor_pos2: alethe_tac
  val xor_neg1: alethe_tac
  val xor_neg2: alethe_tac
  val xor1: alethe_tac
  val xor2: alethe_tac
  val not_xor1: alethe_tac
  val not_xor2: alethe_tac
  val true_rule: alethe_tac
  val false_rule: alethe_tac
  val forall_inst: alethe_tac_args
  val implies_rules: alethe_tac
  val implies_neg1: alethe_tac
  val implies_neg2: alethe_tac
  val implies_pos: alethe_tac
  val ite1: alethe_tac
  val ite2: alethe_tac
  val ite_intro: alethe_tac
  val ite_neg1: alethe_tac
  val ite_neg2: alethe_tac
  val ite_pos1: alethe_tac
  val ite_pos2: alethe_tac
  val rewrite_ite_simplify: alethe_tac
  val la_disequality: alethe_tac
  val la_generic: alethe_tac_args
  val la_rw_eq: alethe_tac
  val lia_generic: alethe_tac
  val la_mult_pos: alethe_tac
  val la_mult_neg: alethe_tac
  val poly_simp: alethe_tac
  val poly_simp_rel: alethe_tac
  val refl: alethe_tac_args
  val normalized_input: alethe_tac_args
  val not_and_rule: alethe_tac
  val not_equiv1: alethe_tac
  val not_equiv2: alethe_tac
  val not_implies1: alethe_tac
  val not_implies2: alethe_tac
  val not_ite1: alethe_tac
  val not_ite2: alethe_tac
  val not_not: alethe_tac
  val not_or_rule: alethe_tac_args
  val or: alethe_tac
  val or_neg_rule: alethe_tac_args
  val or_pos_rule: alethe_tac
  val theory_resolution2: alethe_tac
  val prod_simplify: alethe_tac
  val div_simplify: alethe_tac
  val qnt_join: alethe_tac
  val qnt_rm_unused: alethe_tac
  val onepoint: alethe_tac
  val qnt_simplify: alethe_tac
  val rare_rewrite: alethe_tac
  val evaluate: alethe_tac
  val unit_res: alethe_tac
  val sko_ex: alethe_tac
  val sko_forall: alethe_tac
  val subproof: alethe_tac
  val ordered_subproof: alethe_tac
  val sum_simplify: alethe_tac
  val tautological_clause: alethe_tac
  val AC_rule: alethe_tac
  val ACI_rule: alethe_tac
  val bfun_elim: alethe_tac
  val qnt_cnf: alethe_tac
  val trans: alethe_tac
  val strict_trans: alethe_tac (*assumes assumptions in the right order*)
  val symm: alethe_tac
  val not_symm: alethe_tac
  val reordering: alethe_tac
  val shuffle: alethe_tac_step_args_and_arg
  val contraction: alethe_tac
  val miniscope_distribute: alethe_tac
  val miniscope_split: alethe_tac
  val miniscope_ITE: alethe_tac
  val and_intro: alethe_tac
  val trust: alethe_tac
  val hole: alethe_tac
  val weakening: alethe_tac

  (*Extension to declare new alethe rules*)
  val declare_alethe_rule: string -> alethe_tac_step_args -> Context.generic -> Context.generic
  val rm_alethe_rule: string -> Context.generic -> Context.generic
  val get_alethe_tac: string -> Context.generic -> alethe_tac_step_args option
  val print_alethe_tac: Context.generic -> Pretty.T

  (*Useful lifting of tactics*)
  val REPEAT_CHANGED: ('a -> tactic) -> 'a -> tactic
  val TRY': ('a -> tactic) -> 'a -> tactic
  val REPEAT': ('a -> tactic) -> 'a -> tactic
  val REPEAT_DETERM_N': int -> ('a -> tactic) -> 'a -> tactic

  val simplify_tac: Proof.context -> thm list -> int -> tactic
  val replay_error: Proof.context -> string -> alethe_rule -> thm list -> term list -> term -> 'a

  val sort_disj_and_equality_in_term: Proof.context -> conv
end;


structure Alethe_Replay_Methods: ALETHE_REPLAY_METHODS =
struct

(*TODO: remove, but to prepare transition to next isabelle*)
nonfix addsimps
nonfix addsimprocs
(*end*)

open SMT_Config
fun debug_msg ctxt = alethe_debug_msg ctxt "alethe_replay_methods"
fun debug_msg_tac' ctxt verbosity str = K (SMT_Config.alethe_debug_msg_tac ctxt "alethe_replay_methods" verbosity str)

type alethe_tac_step_args = Proof.context -> thm list -> term list -> term -> thm
type alethe_tac_context_args = Proof.context -> thm list -> term list -> term -> thm
type alethe_tac_args = Proof.context -> thm list -> term -> Alethe_Node.tactic_args option -> thm
type alethe_tac_context_args_and_arg = Proof.context -> thm list -> term list -> term -> Alethe_Node.tactic_args option -> thm
type alethe_tac_step_args_and_arg = Proof.context -> thm list -> term list -> term -> Alethe_Node.tactic_args option -> thm
type alethe_tac = Proof.context -> thm list -> term -> thm

datatype alethe_rule =
   (*normalized_input: a repeated (normalized) assumption or an assumption in a subproof*)
   Normalized_Input | Local_Input |
   (*Used to introduce skolem constants*)
   Definition |
   (*Subproof:*)
   Subproof |
   (*Quantifiers:*)
   Forall_Inst | Qnt_Rm_Unused | Qnt_Join | Onepoint | Bind | Sko_Forall | Sko_Ex |
   (*Boolean Constants*)
   False | True |
   (*Conjunction:*)
   And | Not_And | And_Pos | And_Neg |
   (*Disjunction:*)
   Or | Or_Pos | Not_Or | Or_Neg |
   (*Implication:*)
   Implies | Implies_Neg1 | Implies_Neg2 | Implies_Pos | Not_Implies1 | Not_Implies2 |
   (*Equivalence:*)
   Equiv_neg1 | Equiv_pos1 | Equiv_pos2 | Equiv_neg2 | Not_Equiv1 | Not_Equiv2 | Equiv1 | Equiv2 |
   (*If-then-else:*)
   ITE_Pos1 | ITE_Pos2 | ITE_Neg1 | ITE_Neg2 | Not_ITE1 | Not_ITE2 | ITE_Intro | ITE1 | ITE2 |
   (*Equality:*)
   Eq_Congruent | Eq_Reflexive | Eq_Transitive | Eq_Congruent_Pred | Trans | Refl | Cong |
   (*xor:*)
   Xor_Pos1 | Xor_Pos2 | Xor_Neg1 | Xor_Neg2 | Xor1 | Xor2 | Not_Xor1 | Not_Xor2 |
   (*Arithmetic:*)
   LA_Disequality | LA_Generic | LA_Tautology | LIA_Generic | LA_Totality | LA_RW_Eq |
   NLA_Generic | LA_Mult_Pos | LA_Mult_Neg | Poly_Simp | Poly_Simp_Rel |
   (*Resolution:*)
   Theory_Resolution | Resolution |
   (*Simplification Rules*)
   Bool_Simplify | Or_Simplify | Not_Simplify | And_Simplify | Equiv_Simplify |
   Implies_Simplify | Connective_Def | Minus_Simplify | Unary_Minus_Simplify | Comp_Simplify |
   Eq_Simplify | ITE_Simplify | Sum_Simplify | Prod_Simplify | Div_Simplify | RARE_Rewrite | Evaluate |
   Qnt_Simplify | Not_Not | Tautological_Clause | Distinct_Elim |
   AC_Simp | ACI_Simp |
   (*Extended rules*)
   Symm | Not_Symm | Reordering | Shuffle | Contraction |
   Miniscope_Distribute | Miniscope_Split | Miniscope_ITE |
   And_Intro |
   (*Other Rules*)
   Other_Rule of string |
   Hole | Trust |
   Bfun_Elim |
   Qnt_CNF |
   (*For compression*)
   Theory_Resolution2 | Weakening |
   (*Unsupported rule*)
   Unsupported

fun string_of_alethe_rule Bind = "Bind"
  | string_of_alethe_rule Cong = "Cong"
  | string_of_alethe_rule Refl = "Refl"
  | string_of_alethe_rule Equiv1 = "Equiv1"
  | string_of_alethe_rule Equiv2 = "Equiv2"
  | string_of_alethe_rule Equiv_pos1 = "Equiv_pos1"
  | string_of_alethe_rule Equiv_pos2 = "Equiv_pos2"
  | string_of_alethe_rule Equiv_neg1 = "Equiv_neg1"
  | string_of_alethe_rule Equiv_neg2 = "Equiv_neg2"
  | string_of_alethe_rule Sko_Forall = "Sko_Forall"
  | string_of_alethe_rule Sko_Ex = "Sko_Ex"
  | string_of_alethe_rule Eq_Reflexive = "Eq_Reflexive"
  | string_of_alethe_rule Theory_Resolution = "Theory_Resolution"
  | string_of_alethe_rule Theory_Resolution2 = "Theory_Resolution2"
  | string_of_alethe_rule Forall_Inst = "forall_inst"
  | string_of_alethe_rule Or = "Or"
  | string_of_alethe_rule Not_Or = "Not_Or"
  | string_of_alethe_rule Resolution = "Resolution"
  | string_of_alethe_rule Eq_Congruent = "eq_congruent"
  | string_of_alethe_rule Trans = "trans"
  | string_of_alethe_rule True = "true"
  | string_of_alethe_rule False = "false"
  | string_of_alethe_rule And = "and"
  | string_of_alethe_rule And_Pos = "and_pos"
  | string_of_alethe_rule Not_And = "not_and"
  | string_of_alethe_rule And_Neg = "and_neg"
  | string_of_alethe_rule Or_Pos = "or_pos"
  | string_of_alethe_rule Or_Neg = "or_neg"
  | string_of_alethe_rule AC_Simp = "ac_simp"
  | string_of_alethe_rule ACI_Simp = "aci_simp"
  | string_of_alethe_rule Not_Equiv1 = "not_equiv1"
  | string_of_alethe_rule Not_Equiv2 = "not_equiv2"
  | string_of_alethe_rule Xor_Pos1 = "xor_pos1"
  | string_of_alethe_rule Xor_Pos2 = "xor_pos2"
  | string_of_alethe_rule Xor_Neg1 = "xor_neg1"
  | string_of_alethe_rule Xor_Neg2 = "xor_neg2"
  | string_of_alethe_rule Xor1 = "xor1"
  | string_of_alethe_rule Xor2 = "xor2"
  | string_of_alethe_rule Not_Xor1 = "not_xor1"
  | string_of_alethe_rule Not_Xor2 = "not_xor2"
  | string_of_alethe_rule Not_Implies1 = "not_implies1"
  | string_of_alethe_rule Not_Implies2 = "not_implies2"
  | string_of_alethe_rule Implies_Neg1 = "implies_neg1"
  | string_of_alethe_rule Implies_Neg2 = "implies_neg2"
  | string_of_alethe_rule Implies = "implies"
  | string_of_alethe_rule Bfun_Elim = "bfun_elim"
  | string_of_alethe_rule ITE1 = "ite1"
  | string_of_alethe_rule ITE2 = "ite2"
  | string_of_alethe_rule Not_ITE1 = "not_ite1"
  | string_of_alethe_rule Not_ITE2 = "not_ite2"
  | string_of_alethe_rule ITE_Pos1 = "ite_pos1"
  | string_of_alethe_rule ITE_Pos2 = "ite_pos2"
  | string_of_alethe_rule ITE_Neg1 = "ite_neg1"
  | string_of_alethe_rule ITE_Neg2 = "ite_neg2"
  | string_of_alethe_rule ITE_Intro = "ite_intro"
  | string_of_alethe_rule LA_Disequality = "la_disequality"
  | string_of_alethe_rule LA_Generic = "la_generic"
  | string_of_alethe_rule LIA_Generic = "lia_generic"
  | string_of_alethe_rule LA_Tautology = "la_tautology"
  | string_of_alethe_rule LA_RW_Eq = "la_rw_eq"
  | string_of_alethe_rule LA_Totality = "LA_Totality"
  | string_of_alethe_rule NLA_Generic = "nla_generic"
  | string_of_alethe_rule LA_Mult_Pos = "la_mult_pos"
  | string_of_alethe_rule LA_Mult_Neg = "la_mult_neg"
  | string_of_alethe_rule Poly_Simp = "poly_simp"
  | string_of_alethe_rule Poly_Simp_Rel = "poly_simp_rel"
  | string_of_alethe_rule Eq_Transitive = "eq_transitive"
  | string_of_alethe_rule Qnt_Rm_Unused = "qnt_remove_unused"
  | string_of_alethe_rule Onepoint = "onepoint"
  | string_of_alethe_rule Qnt_Join = "qnt_join"
  | string_of_alethe_rule Eq_Congruent_Pred = "eq_congruent_pred"
  | string_of_alethe_rule Normalized_Input = Alethe_Proof.normalized_input_rule
  | string_of_alethe_rule Local_Input = Alethe_Proof.local_input_rule
  | string_of_alethe_rule Subproof = "subproof"
  | string_of_alethe_rule Bool_Simplify = "bool_simplify"
  | string_of_alethe_rule Equiv_Simplify = "equiv_simplify"
  | string_of_alethe_rule Eq_Simplify = "eq_simplify"
  | string_of_alethe_rule Not_Simplify = "not_simplify"
  | string_of_alethe_rule And_Simplify = "and_simplify"
  | string_of_alethe_rule Or_Simplify = "or_simplify"
  | string_of_alethe_rule ITE_Simplify = "ite_simplify"
  | string_of_alethe_rule Implies_Simplify = "implies_simplify"
  | string_of_alethe_rule Connective_Def = "connective_def"
  | string_of_alethe_rule Minus_Simplify = "minus_simplify"
  | string_of_alethe_rule Sum_Simplify = "sum_simplify"
  | string_of_alethe_rule Prod_Simplify = "prod_simplify"
  | string_of_alethe_rule Div_Simplify = "div_simplify"
  | string_of_alethe_rule RARE_Rewrite = "rare_rewrite"
  | string_of_alethe_rule Evaluate = "evaluate"
  | string_of_alethe_rule Comp_Simplify = "comp_simplify"
  | string_of_alethe_rule Qnt_Simplify = "qnt_simplify"
  | string_of_alethe_rule Symm = "symm"
  | string_of_alethe_rule Not_Symm = "not_symm"
  | string_of_alethe_rule Reordering = "reordering"
  | string_of_alethe_rule Shuffle = "shuffle"
  | string_of_alethe_rule Contraction = "contraction"
  | string_of_alethe_rule Miniscope_Distribute = "miniscope_distribute"
  | string_of_alethe_rule Miniscope_Split = "miniscope_split"
  | string_of_alethe_rule Miniscope_ITE = "miniscope_ITE"
  | string_of_alethe_rule And_Intro = "and_intro"
  | string_of_alethe_rule Not_Not = Alethe_Proof.not_not_rule
  | string_of_alethe_rule Tautological_Clause = "tautology"
  | string_of_alethe_rule Distinct_Elim = "distinct_elim"
  | string_of_alethe_rule Qnt_CNF = "qnt_cnf"
  | string_of_alethe_rule Trust = "trust"
  | string_of_alethe_rule (Other_Rule r) = r
  | string_of_alethe_rule r = "Unknown rule: " ^ \<^make_string> r

fun debug_rule_tac' ctxt verbosity rule str = debug_msg_tac' ctxt verbosity ("Reconstruct " ^ (string_of_alethe_rule rule) ^ ": " ^ str)

(** Context Extension for Rules **)
(*We currently do not distinguish between the extension required for each solver. Maybe later
it will be needed.*)
type alethe_rule_ext = {rules: (string * alethe_tac_step_args) list}

fun mk_alethe_rule_ext rules : alethe_rule_ext =
   {rules=rules}

val empty_data = mk_alethe_rule_ext []

fun merge_data ({rules=rules1}:alethe_rule_ext, {rules=rules2}:alethe_rule_ext) : alethe_rule_ext =
  mk_alethe_rule_ext (AList.merge (op =) (fn _ => true) (rules1, rules2))

structure Data = Generic_Data
(
  type T = alethe_rule_ext
  val empty = empty_data
  val merge = merge_data
)

fun declare_alethe_rule rule tac context =
  let
    val {rules} = Data.get context
  in
    Data.map
      (K (mk_alethe_rule_ext (AList.update (op =) (rule, tac) rules)))
      context
  end

fun rm_alethe_rule stgy context =
  let
    val {rules} = Data.get context
  in
    Data.map
      (K (mk_alethe_rule_ext (AList.delete (op =) stgy rules)))
      context
  end

fun get_alethe_tac rule context =
  let
    val {rules} = Data.get context
  in
    AList.lookup (op =) rules rule
  end

fun print_alethe_tac context =
  let
    val {rules} = Data.get context
  in
    rules
    |> map (fn (a, b) => a ^ "->" ^ @{make_string} b)
    |> map Pretty.str
    |> Pretty.big_list "Declared alethe rules:\n"
  end


(** Tactics for Reconstruction **)
(* General Notes:
t is usually the goal as a term
thms are usually just the premises of the rule as a list of theorems.
*)

fun replay_error ctxt msg rule thms args t =
  SMT_Replay_Methods.replay_error ctxt msg (string_of_alethe_rule rule) thms args t

(* utility function *)

fun eqsubst_all ctxt thms =
   K ((REPEAT o HEADGOAL) (EqSubst.eqsubst_asm_tac ctxt [0] thms))
   THEN' K ((REPEAT o HEADGOAL) (EqSubst.eqsubst_tac ctxt [0] thms))

fun get_solver_name (SOME (Solver_Name name)) = name
  | get_solver_name _ = "unknown solver name"

(*Very useful helper function, I really don't understand why this is not defined in conversion.ML*)
fun print_conv (str : string) ct = (ignore str; (*@{print} (str, ct, Thm.term_of ct);*) Conv.all_conv ct)

(*
We were told that emptying and filling the context back and forth could be improved.
We tried (by saving two contexts), but did not observe any improvement.
*)
fun simplify_tac ctxt thms =
  ctxt
  |> Simplifier.empty_simpset
  |> Simplifier.put_simpset HOL_basic_ss
  |> Simplifier.add_simps (@{thms simp_thms} @ thms)
  |> Simplifier.asm_full_simp_tac

(*This is a weaker simplification form. It is weaker, but is also less likely to loop*)
fun partial_simplify_tac ctxt thms =
  ctxt
  |> Simplifier.empty_simpset
  |> Simplifier.put_simpset HOL_basic_ss
  |> Simplifier.add_simps (@{thms simp_thms} @ thms)
  |> Simplifier.full_simp_tac

fun partial_simplify_tac_with_cong cong simprocs ctxt thms =
  ctxt
  |> Simplifier.empty_simpset
  |> put_simpset HOL_basic_ss
  |> Simplifier.add_simps (@{thms simp_thms} @ thms)
  |> Simplifier.add_cong cong
  |> fold Simplifier.add_proc simprocs
  |> Simplifier.full_simp_tac

(* sko_forall requires the assumptions to be able to prove the equivalence in case of double
skolemization. See comment below. *)
fun requires_subproof_assms _ t =
  member (op =) ["sko_forall", "sko_ex", "refl"] t

fun requires_local_input _ t =
  member (op =) [Alethe_Proof.local_input_rule] t

val try_provers = SMT_Replay_Methods.try_provers

fun TRY' tac = fn i => TRY (tac i)
fun REPEAT' tac = fn i => REPEAT (tac i)
fun REPEAT_CHANGED tac = fn i => REPEAT (CHANGED (tac i))
fun REPEAT_DETERM_N' k tac = fn i => REPEAT_DETERM_N k (tac i)
fun DETERM' tac = fn i => DETERM (tac i)

fun extract_single_premise rule ctxt thm t =
  (case thm of
    [thm] => thm
  | thms => replay_error ctxt "Expected only one premise" rule thms [] t)


(* Bind *)

val bind_thms =
  [@{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<forall>x. P x) = (\<forall>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>x. P x) = (\<exists>y. Q y)\<close> by blast}]

fun extract_quantified_names_q (_ $ Abs (name, _, t)) =
   apfst (cons name) (extract_quantified_names_q t)
  | extract_quantified_names_q t = ([], t)

fun extract_forall_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, ty, t)) =
   (name, ty) :: (extract_forall_quantified_names_q t)
  | extract_forall_quantified_names_q _ = []

fun extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs (name, _, t)) =
      name :: (extract_all_forall_exists_quantified_names_q t)
  | extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, _, t)) =
      name :: (extract_all_forall_exists_quantified_names_q t)
  | extract_all_forall_exists_quantified_names_q (t $ u) =
      extract_all_forall_exists_quantified_names_q t @ extract_all_forall_exists_quantified_names_q u
  | extract_all_forall_exists_quantified_names_q _ = []

fun bind ctxt [thms] context_ass t =
  (SMT_Replay_Methods.prove ctxt t (fn _ =>
    REPEAT_DETERM_N' (length context_ass div 2) (resolve_tac ctxt bind_thms)
    THEN' (resolve_tac ctxt [thms]
      THEN_ALL_NEW TRY' (eq_assume_tac ORELSE' resolve_tac ctxt @{thms refl})))
  handle (Fail msg) => replay_error ctxt msg Bind [thms] [] t)
  | bind ctxt thms _ t = replay_error ctxt "invalid application" Bind thms [] t


(* Congruence/Refl *)

fun cong ctxt thms t args = try_provers (get_solver_name args) ctxt
    (string_of_alethe_rule Cong) [
  ("basic", SMT_Replay_Methods.cong_basic ctxt thms),
  ("unfolding then reflexivity", SMT_Replay_Methods.cong_unfolding_trivial ctxt thms),
  ("unfolding then auto", SMT_Replay_Methods.cong_unfolding_first ctxt thms),
  ("full", SMT_Replay_Methods.cong_full ctxt thms)] thms [] t

fun refl ctxt thms t args =
  (case find_first (fn thm => t = Thm.full_prop_of thm) thms of
      SOME thm => thm
    | NONE =>
        (case try (fn t => SMT_Replay_Methods.match_instantiate ctxt t @{thm refl}) t of
          NONE => cong ctxt thms t args
        | SOME thm => thm))

(* Instantiation *)

fun forall_inst ctxt _ t (SOME (Insts insts)) =
  let
    fun instantiate_and_solve i ({context = ctxt, prems = [prem], ...}: Subgoal.focus) =
        let
          val t_prem = Thm.prop_of prem
          val quants = t_prem
            |> SMT_Replay_Methods.dest_prop
            |> extract_forall_quantified_names_q
          val insts = quants
            |> map (Symtab.lookup insts o fst)
            |> drop_suffix is_none

          fun instantiate_with inst prem =
            Drule.infer_instantiate' ctxt [NONE, inst] @{thm spec} OF [prem]
          val inst_thm =
            fold instantiate_with
              (map (Option.map (Thm.cterm_of ctxt)) insts)
              prem
        in
           (Method.insert_tac ctxt [inst_thm]
           THEN' TRY' (fn i => eq_assume_tac i)
           THEN' TRY' (partial_simplify_tac ctxt @{thms eq_commute ac_simps})

           (*https://gitlab.uliege.be/verit/verit/-/issues?show=eyJpaWQiOiI0MSIsImZ1bGxfcGF0aCI6InZlcml0L3Zlcml0IiwiaWQiOjM4NjI4fQ%3D%3D
           the blast tac is not useful for cvc5, but veriT did instantiate quantifiers not on outmost
           level without specifying how. Therefore we need blast.

           Important: there is actually a real example we got from Peter Lammich where we needed
           the blast call, see the test file.*)
           THEN' TRY' (Blast.blast_tac ctxt)) i
        end
     | instantiate_and_solve _ ({context = ctxt, prems = thms, ...}: Subgoal.focus) =
         replay_error ctxt "invalid application" Forall_Inst thms [] t
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      match_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}]]
      THEN' (fn i => Subgoal.FOCUS (instantiate_and_solve i) ctxt i))
  end
 | forall_inst ctxt _ t _ = replay_error ctxt "invalid application" Forall_Inst [] [] t


(* Or *)

fun or _ (thm :: _) _ = thm
  | or ctxt thms t = replay_error ctxt "invalid application" Or thms [] t


(* Skolemization *)

fun extract_rewrite_rule_assumption thms =
  let
    fun is_rewrite_rule thm =
      (case Thm.prop_of thm of
        \<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ Free _) => true
      | _ => false)
    fun is_context_rule thm =
      (case Thm.prop_of thm of
        \<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Free _ $ Free _) => true
      | _ => false)
    val (ctxt_eq, other) = List.partition is_context_rule thms
    val (rew, other) = List.partition is_rewrite_rule other
  in
    (ctxt_eq, rew, other)
  end

(*
Without compression, we have to rewrite skolems only once. However, it can happen than the same
skolem constant is used multiple times with a different name under the forall.

For strictness, we use the multiple rewriting only when compressing is activated.
*)
local
  fun rewrite_all_skolems ctxt_eq thm_indirect ctxt ((_,SOME thm) :: thms) =
     let
       val rewrite_sk_thms =
         map_filter (try (fn tm => tm OF [thm])) thm_indirect
       val multiple_rew = if SMT_Config.compress_alethe_proofs ctxt then REPEAT_CHANGED else I
     in
       multiple_rew (EqSubst.eqsubst_tac ctxt [0] rewrite_sk_thms
         THEN' SOLVED' (K (HEADGOAL (partial_simplify_tac ctxt (ctxt_eq @ @{thms eq_commute}))))
       )
       THEN' rewrite_all_skolems ctxt_eq thm_indirect ctxt thms
     end
   | rewrite_all_skolems ctxt_eq thm_indirect ctxt ((_,NONE) :: thms) =
       rewrite_all_skolems ctxt_eq thm_indirect ctxt thms
   | rewrite_all_skolems _ _ _ [] = K all_tac

   fun extract_var_name (thm :: thms) =
       let val name = Thm.concl_of thm
         |> SMT_Replay_Methods.dest_prop
         |> HOLogic.dest_eq
         |> fst
         |> (fn Const(_,_) $ Abs(name, _, _) => [(name,@{thm sym} OF [thm])]
             | _ => [])
       in name :: extract_var_name thms end
    | extract_var_name [] = []

fun skolem_tac extractor thms1 ctxt prems t =
  let

    val (ctxt_eq, rew, other) = extract_rewrite_rule_assumption prems

    fun ordered_definitions () =
      let
        val var_order = extractor t
        val thm_names_with_var = extract_var_name rew |> flat
      in map (fn v => (v, AList.lookup (op =) thm_names_with_var v)) var_order end
    (*veriT produces longer terms for skolem function like
    SK1 = eps x. P x
    SK2 = eps y. Q x (eps x. P x)

    instead of the shorter:
    SK1 = eps x. P x
    SK2 = eps y. Q x SK1

    When the option --proof-with-sharing is activated, we take care of this during parsing, but
    if not (and especially if using check_smt), we need to fold SK1 into SK2. As we cannot know
    whether the option was used, we always rewrite.
    *)
    fun fold_definition [] _ = []
      | fold_definition ((v, NONE) :: xs) acc = (v, NONE) :: fold_definition xs acc
      | fold_definition ((v, SOME thm) :: xs) acc =
        let
          val acc' = (thm COMP @{thm eq_commute[THEN iffD1]}) :: acc
          val simp_ctxt =
           ctxt
           |> Simplifier.empty_simpset
           |> Simplifier.put_simpset HOL_basic_ss
           |> Simplifier.add_simps acc
        in ((v, SOME (Simplifier.full_simplify simp_ctxt thm)) :: fold_definition xs acc') end
    val defs = fold_definition (ordered_definitions ()) [] (*The skolem definitions are stored in the context*)
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      rewrite_all_skolems ctxt_eq thms1 ctxt defs
      THEN' (TRY' (eqsubst_all ctxt (map (fn thm => thm RS sym) other)) (*Skolems can be nested in veriT proofs:*)
      THEN_ALL_NEW TRY' (resolve_tac ctxt @{thms refl})
       (*If the above hasn't worked try unfolding + simplifier *)
      THEN' K (unfold_tac ctxt ctxt_eq)
      THEN' TRY' (partial_simplify_tac ctxt @{thms eq_commute})))
  end
in

fun sko_forall ctxt prems t =
  skolem_tac extract_all_forall_exists_quantified_names_q
    @{thms alethe_sko_forall_indirect2 alethe_sko_ex_indirect2} ctxt prems t

fun sko_ex ctxt prems t =
  skolem_tac extract_all_forall_exists_quantified_names_q
    @{thms alethe_sko_ex_indirect2 alethe_sko_forall_indirect2} ctxt prems t

end

fun eq_reflexive ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t @{thm refl}

local
  fun not_not_prove ctxt _ =
    K (unfold_tac ctxt @{thms not_not})
    THEN' match_tac ctxt @{thms alethe_or_simplify_1}

  fun tautological_clause_prove ctxt _ = resolve_tac ctxt @{thms TrueI}

  val theory_resolution2_lemma = @{lemma \<open>a \<Longrightarrow> a = b \<Longrightarrow> b\<close> by blast}

in

fun prove_abstract abstracter tac ctxt thms t =
  let

    val t_eta_long_eq = Thm.eta_long_conversion (Object_Logic.dest_judgment ctxt (Thm.cterm_of ctxt t))
    val (_, t_eta_long) = Logic.dest_equals (Thm.prop_of t_eta_long_eq)
    val _ = debug_msg ctxt middle (fn () => \<^print> ("Current goal (term) as thm before abstraction",t_eta_long))

    val thms_eta_long = map (Conv.fconv_rule Thm.eta_long_conversion) thms
    val _ = (if null thms_eta_long then () else debug_msg ctxt middle (fn () => \<^print> ("Premises after being abstracted",thms_eta_long)))
    val abstract_thm =
      (SMT_Replay_Methods.prove_abstract ctxt thms_eta_long t_eta_long tac (
        fold_map (abstracter o SMT_Replay_Methods.dest_thm) thms_eta_long ##>>
        abstracter (SMT_Replay_Methods.dest_prop t_eta_long)))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("Current goal (term) as thm after abstraction",abstract_thm))

  in
    @{thm alethe_Pure_trans} OF [t_eta_long_eq, abstract_thm]
  end

val not_not = prove_abstract SMT_Replay_Methods.abstract_bool_shallow not_not_prove

val tautological_clause =
  prove_abstract SMT_Replay_Methods.abstract_bool_shallow tautological_clause_prove

val unit_res = prove_abstract SMT_Replay_Methods.abstract_bool_shallow SMT_Replay_Methods.prop_tac2

(*match_instantiate does not work*)
fun theory_resolution2 ctxt prems t =
  SMT_Replay_Methods.prove ctxt t (fn _ => match_tac ctxt [theory_resolution2_lemma OF prems])

end

(*Modulo implicit reordering. Needed for veriT when checking external problems + proofs.*)
fun is_same_assms_eq_ac (Abs (_, _, u)) (Abs (_, _, u')) =
     is_same_assms_eq_ac u u' (*the name cannot be relevant due to implicit eta-contraction*)
  | is_same_assms_eq_ac (Free (var, _)) (Free (var', _)) = var = var'
  | is_same_assms_eq_ac (Bound var) (Bound var') = var = var'
  | is_same_assms_eq_ac (Const (var, _)) (Const (var', _)) = var = var'
  | is_same_assms_eq_ac (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ u $ v) (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ u' $ v') =
    (is_same_assms_eq_ac u u' andalso is_same_assms_eq_ac v v') orelse
    (is_same_assms_eq_ac u v' andalso is_same_assms_eq_ac v u')
  | is_same_assms_eq_ac (u $ v) (u' $ v') =
    (is_same_assms_eq_ac u u' andalso is_same_assms_eq_ac v v')
  | is_same_assms_eq_ac _ _ = false

fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of

fun normalized_input ctxt prems t args =
  let
    (* External problems only: Retrieve correct assertion for this assume *)
    val all_assms = SMT_Config.alethe_no_provided_assms ctxt
    val termify = Thm.prop_of #> (fn x => single (0, x)) #> SMT_Translate.eta_expand ctxt Termtab.empty #> hd #> snd
    val normalized =
       let val thy = Proof_Context.theory_of (Simplifier.empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy (Named_Theorems.get ctxt \<^named_theorems>\<open>cvc5_normalized_input\<close>) [] (*TODO: This is now done twice, there should at least be a check below if this is already enough*)
        #> Object_Logic.atomize_term ctxt
        #> HOLogic.mk_Trueprop
      end
    val solver_name = get_solver_name args
    fun check_implicit_reordering t' p = (if solver_name = "verit" then is_same_assms_eq_ac t' p else t' = p)
    fun matched_assm () =
      (case find_first (check_implicit_reordering (normalized t) o normalized o termify) prems of
        SOME thm => [thm]
      | NONE => [])
    val m_assm = matched_assm ()

    val prems =
      if all_assms andalso not (null m_assm)
      then
        let val _ = SMT_Config.trace_msg ctxt (pretty ("warning: could not find assumption, had to add all premises"))
        in m_assm end
      else prems
    val _ = debug_msg ctxt low (fn () => \<^print> ("showing normalized input, premises",prems))

  in
    (SMT_Replay_Methods.prove ctxt t (fn _ =>
      Method.insert_tac ctxt prems
      THEN' debug_msg_tac' ctxt high "normalized input after inserting premises"
      THEN' TRY' (K (unfold_tac ctxt (@{thms SMT.trigger_def SMT.alethe_id_def} @ Named_Theorems.get ctxt \<^named_theorems>\<open>nat_normalized_input\<close>)))
      THEN' debug_msg_tac' ctxt high "normalized input after unfolding triggers and nat_normalized_input"
      THEN' TRY' (partial_simplify_tac ctxt (@{thms eq_commute} @ Named_Theorems.get ctxt \<^named_theorems>\<open>cvc5_normalized_input\<close>))
      THEN' debug_msg_tac' ctxt high "normalized input after simplifying eq_commute and cvc5_normalized_input"
    ))
end

local
  val true_rule_thm = @{lemma \<open>True\<close> by blast}
  val false_rule_thm = @{lemma \<open>\<not>False\<close> by blast}
in
  fun true_rule ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t true_rule_thm
  fun false_rule ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t false_rule_thm
end

(* Transitivity *)

(*cvc5 is not using this at the moment (see cvc5_replay_methods)*)

val trans_bool_thm =
  @{lemma \<open>P = Q \<Longrightarrow> Q \<Longrightarrow> P\<close> by blast}

fun trans ctxt thms t =
  let

    val prop_of = HOLogic.dest_Trueprop o Thm.full_prop_of
    fun combine_thms [thm1, thm2] =
          (case (prop_of thm1, prop_of thm2) of
            (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2,
             Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t3 $ t4) =>
            if t2 aconv t3 then thm1 RSN (1, thm2 RSN (2, @{thm trans}))
            else if t2 aconv t4 then thm1 RSN ((1, ((thm2 RS sym)) RSN (2, @{thm trans})))
            else if t1 aconv t4 then thm2 RSN (1, thm1 RSN (2, @{thm trans}))
            else if t1 aconv t3 then (thm2 RS sym) RSN (1, thm1 RSN (2, @{thm trans}))
            else raise Fail "invalid trans theorem"
          | _ => trans_bool_thm OF [thm1, thm2])
      | combine_thms (thm1 :: thm2 :: thms) =
          combine_thms (combine_thms [thm1, thm2] :: thms)
      | combine_thms thms = replay_error ctxt "invalid bind application" Trans thms [] t
     val t' = Thm.eta_long_conversion (Object_Logic.dest_judgment ctxt (Thm.cterm_of ctxt t))
     val (_, t2) = Logic.dest_equals (Thm.prop_of t')
     val thms = map (Conv.fconv_rule Thm.eta_long_conversion) thms
     val trans_thm = combine_thms thms
     val _ = debug_msg ctxt high (fn () => \<^print> ("trans_thm ",trans_thm))

  in
     ((case (prop_of trans_thm, t2) of
       (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ _,
        Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t3 $ _) =>
       if t1 aconv t3 then trans_thm else trans_thm RS sym
      | _ => trans_thm (*to be on the safe side*)))
  end

fun strict_trans ctxt [] t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    (match_tac ctxt @{thms refl}))
 | strict_trans ctxt prems t =
     let
        fun trans_steps [] = replay_error ctxt "invalid application in strict version" Trans [] [] t
          | trans_steps [prem] = prem
          | trans_steps (prem1::prem2::prems) = (@{thm trans} OF [prem1, prem2])::prems |> trans_steps
     in
       SMT_Replay_Methods.prove ctxt t (fn _ => match_tac ctxt (trans_steps prems |> single))
     end

fun AC_rule ctxt thms t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    Method.insert_tac ctxt thms
    THEN' REPEAT_ALL_NEW (partial_simplify_tac ctxt @{thms eq_commute}
    THEN' TRY' (simplify_tac ctxt @{thms ac_simps conj_ac})
    THEN' TRY' (assume_tac ctxt)
    THEN' TRY' (Classical.fast_tac ctxt)))

local
  val idempotency_thms =
   @{thms Groups.group_add_class.diff_0_right
   Groups.monoid_add_class.add_0_right Groups.group_add_class.add.group_left_neutral
   Rings.mult_zero_class.mult_zero_left Rings.mult_zero_class.mult_zero_right
   } (*TODO Hanna: Add bit-vector theorems if necessary. FINAL TEST: Not clear if it helps to add some of these or not.*)
  fun aci_simps_extra_thms ctxt = (Named_Theorems.get ctxt @{named_theorems alethe_aci_simp})
in

fun ACI_rule ctxt thms t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    Method.insert_tac ctxt thms
    THEN' debug_msg_tac' ctxt high "aci_simp before commute"
    THEN' REPEAT_ALL_NEW (partial_simplify_tac ctxt @{thms eq_commute}
    THEN' debug_msg_tac' ctxt high "aci_simp before simplification"
    THEN' TRY' (simplify_tac ctxt (idempotency_thms @ aci_simps_extra_thms ctxt @ @{thms ac_simps conj_ac}))
    THEN' debug_msg_tac' ctxt high "aci_simp after simplification"
    THEN' TRY' (assume_tac ctxt)
    THEN' TRY' (Classical.fast_tac ctxt)))
end


(* And/Or *)

local
  fun not_and_rule_prove ctxt prems =
    Method.insert_tac ctxt prems
    THEN' K (unfold_tac ctxt @{thms de_Morgan_conj})
    THEN_ALL_NEW TRY' (assume_tac ctxt)

  fun or_intro_prove ctxt k =
    (REPEAT_DETERM_N' k (match_tac ctxt @{thms disjI2}))
    THEN' (SOLVED' (match_tac ctxt @{thms disjI1} THEN' assume_tac ctxt) ORELSE' (assume_tac ctxt))

  fun and_dest_prove ctxt k =
    REPEAT_DETERM_N' k (dmatch_tac ctxt @{thms conjunct2})
    THEN' (SOLVED' (dmatch_tac ctxt @{thms conjunct1} THEN' assume_tac ctxt) ORELSE' (assume_tac ctxt))

  fun or_pos_prove ctxt _ =
    match_tac ctxt @{thms alethe_farkas(1)}
    THEN' assume_tac ctxt

  fun and_rule_prove k ctxt prems =
    Method.insert_tac ctxt prems
    THEN' and_dest_prove ctxt k

  fun and_neg_rule_prove ctxt _ =
    match_tac ctxt @{thms alethe_and_neg}
    THEN' K (unfold_tac ctxt @{thms de_Morgan_conj})
    THEN' TRY' (assume_tac ctxt)

  fun prover tac = prove_abstract SMT_Replay_Methods.abstract_prop tac

in

fun and_rule ctxt prems t (SOME (Index k)) = (prover (and_rule_prove k)) ctxt prems t
  | and_rule ctxt _ t _ = SMT_Replay_Methods.prove ctxt t (fn _ => K no_tac)

val not_and_rule = prover not_and_rule_prove

val or_pos_rule = prover or_pos_prove

val and_neg_rule = prover and_neg_rule_prove

fun not_or_rule ctxt prems t (SOME (Index k)) =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    let
      val ct_prem = 
        Thm.prop_of (hd prems)
        |> HOLogic.dest_not o HOLogic.dest_Trueprop
        |> Thm.cterm_of ctxt
      val ct_concl = 
        t
        |> HOLogic.dest_not o HOLogic.dest_Trueprop
        |> Thm.cterm_of ctxt
      val x = Drule.infer_instantiate' ctxt [SOME ct_prem, SOME ct_concl] @{thm contrapos_nn}
    in
      resolve_tac ctxt [x]
      THEN' (resolve_tac ctxt prems)
      THEN' (or_intro_prove ctxt k)
    end)
  | not_or_rule ctxt _ t _ = SMT_Replay_Methods.prove ctxt t (fn _ => fn _ => no_tac)

fun or_neg_rule ctxt _ t (SOME (Index k)) =
      SMT_Replay_Methods.prove ctxt t (fn _ => match_tac ctxt @{thms alethe_or_neg} THEN' or_intro_prove ctxt k)
  | or_neg_rule ctxt _ t _ = SMT_Replay_Methods.prove ctxt t (fn _ => K no_tac)

fun and_pos ctxt _ t (SOME (Index k)) =
      SMT_Replay_Methods.prove ctxt t (fn _ =>
      resolve_tac ctxt [@{lemma "(A \<Longrightarrow> B) \<Longrightarrow> (\<not>A \<or> B)" by blast}]
      THEN' (and_dest_prove ctxt k))
  | and_pos ctxt _ t _ = SMT_Replay_Methods.prove ctxt t (fn _ =>
      REPEAT_CHANGED (resolve_tac ctxt @{thms alethe_and_pos})
      THEN' TRY' (assume_tac ctxt))
end

(* Equivalence Transformation *)

local
  fun prove_equiv equiv_thm ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [equiv_thm OF [thm]]
        THEN' TRY' (assume_tac ctxt))
    | prove_equiv _ ctxt thms t = replay_error ctxt "invalid application in some equiv rule" Unsupported thms [] t
in

val not_equiv1 = prove_equiv @{lemma \<open>\<not>(A \<longleftrightarrow> B) \<Longrightarrow> A \<or> B\<close> by blast}
val not_equiv2 = prove_equiv @{lemma \<open>\<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<or> \<not>B\<close> by blast}
val equiv1 = prove_equiv @{lemma \<open>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<or> B\<close> by blast}
val equiv2 = prove_equiv @{lemma \<open>(A \<longleftrightarrow> B) \<Longrightarrow> A \<or> \<not>B\<close> by blast}
val not_implies1 = prove_equiv @{lemma \<open>\<not>(A \<longrightarrow> B) \<Longrightarrow> A\<close> by blast}
val not_implies2 = prove_equiv @{lemma \<open>\<not>(A \<longrightarrow>B) \<Longrightarrow> \<not>B\<close> by blast}

end

fun weakening ctxt [prem] t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    Method.insert_tac ctxt [prem]
    THEN' resolve_tac ctxt [@{lemma \<open>\<And>A B. A \<Longrightarrow> (\<not>B \<Longrightarrow> \<not>A) \<Longrightarrow> B\<close> by blast}]
    THEN' assume_tac ctxt
    THEN' REPEAT' (dresolve_tac ctxt @{thms de_Morgan_disj[THEN iffD1]}
      THEN' eresolve_tac ctxt @{thms conjE})
    THEN' REPEAT' (resolve_tac ctxt @{thms de_Morgan_disj[THEN iffD2]}
      THEN' resolve_tac ctxt @{thms conjI} THEN' REPEAT' (assume_tac ctxt))
    THEN' REPEAT' (assume_tac ctxt)) |
 weakening ctxt thms t = replay_error ctxt "invalid application" Weakening thms [] t


(* Equivalence Lemma *)
(*equiv_pos2 is very important for performance. We have tried various tactics, including
a specialisation of SMT_Replay_Methods.match_instantiate, but there never was a measurable
and consistent gain.*)
local
  fun prove_equiv_pos_neg2 thm ctxt _ t =
    SMT_Replay_Methods.match_instantiate ctxt t thm
in

val equiv_pos1_thm = @{lemma \<open>\<not>(a \<longleftrightarrow> b) \<or> a \<or> \<not>b\<close> by blast+}
val equiv_pos1 = prove_equiv_pos_neg2 equiv_pos1_thm

val equiv_pos2_thm = @{lemma \<open>\<And>a b. (a \<noteq> b) \<or> \<not>a \<or> b\<close> by blast+}
val equiv_pos2 = prove_equiv_pos_neg2 equiv_pos2_thm

val equiv_neg1_thm = @{lemma \<open>(a \<longleftrightarrow> b) \<or> \<not>a \<or> \<not>b\<close> by blast+}
val equiv_neg1 = prove_equiv_pos_neg2 equiv_neg1_thm

val equiv_neg2_thm = @{lemma \<open>(a \<longleftrightarrow> b) \<or> a \<or> b\<close> by blast}
val equiv_neg2 = prove_equiv_pos_neg2 equiv_neg2_thm

end

(* xor Transformation *)
local
 fun prove_xor xor_thm ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [xor_thm OF [thm]]
        THEN' TRY' (assume_tac ctxt))
    | prove_xor _ ctxt thms t = replay_error ctxt "invalid application in some xor rule" Unsupported thms [] t
in

val xor1_thm = @{lemma \<open>\<not>(a = b) \<Longrightarrow> a \<or> b\<close> by blast}
val xor1 = prove_xor xor1_thm

val xor2_thm = @{lemma \<open>\<not>(a = b) \<Longrightarrow> \<not>a \<or> \<not>b\<close> by blast}
val xor2 = prove_xor xor2_thm

val not_xor1_thm = @{lemma \<open>\<not>(\<not>(a = b)) \<Longrightarrow> a \<or> \<not>b\<close> by blast}
val not_xor1 = prove_xor not_xor1_thm

val not_xor2_thm = @{lemma \<open>\<not>(\<not>(a = b)) \<Longrightarrow> \<not>a \<or> b\<close> by blast}
val not_xor2 = prove_xor not_xor2_thm

end


(* xor Lemma *)
local
  fun prove_xor thm ctxt _ t =
    SMT_Replay_Methods.match_instantiate ctxt t thm
in

val xor_pos1_thm = @{lemma \<open>\<not>(\<not>(a = b)) \<or> a \<or> b\<close> by blast}
val xor_pos1 = prove_xor xor_pos1_thm

val xor_pos2_thm = @{lemma \<open>\<not>(\<not>(a = b)) \<or> \<not>a \<or> \<not>b\<close> by blast}
val xor_pos2 = prove_xor xor_pos2_thm

val xor_neg1_thm = @{lemma \<open>\<not>(a = b) \<or> a \<or> \<not>b\<close> by blast}
val xor_neg1 = prove_xor xor_neg1_thm

val xor_neg2_thm = @{lemma \<open>\<not>(a = b) \<or> \<not>a \<or> b\<close> by blast}
val xor_neg2 = prove_xor xor_neg2_thm

end


local
  fun implies_pos_neg_term ctxt thm (\<^term>\<open>Trueprop\<close> $
         (\<^term>\<open>HOL.disj\<close> $ (\<^term>\<open>HOL.implies\<close> $ a $ b) $ _)) =
         Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm
     | implies_pos_neg_term ctxt thm t =
        replay_error ctxt "invalid application in Implies" Unsupported [thm] [] t

  fun prove_implies_pos_neg thm ctxt _ t =
    let val thm = implies_pos_neg_term ctxt thm t
    in
      SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [thm]
        THEN' TRY' (assume_tac ctxt))
    end
in


fun distinct_elim ctxt _ t =
let
  fun extract_clauses thm =
    REPEAT_CHANGED (resolve_tac ctxt @{thms alethe_distinct_elim_1(1)})
    THEN' (resolve_tac ctxt @{thms alethe_distinct_elim_1(2)})
    THEN' (resolve_tac ctxt @{thms alethe_distinct_elim_1(3)})
    THEN' (match_tac ctxt thm)
    THEN_ALL_NEW (assume_tac ctxt)
in
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  SOLVED'
    (TRY' (
        (resolve_tac ctxt @{thms alethe_distinct_elim_two_clauses})
      ORELSE'
        (resolve_tac ctxt @{thms alethe_distinct_elim_0}
        THEN' (REPEAT_DETERM_N' 2 (extract_clauses @{thms alethe_distinct_elim_2}))))
      THEN' TRY' (resolve_tac ctxt @{thms refl}))
    ORELSE' (Classical.fast_tac ctxt)
  )
end


(* Implication *)

fun implies_pos ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt @{thms alethe_implies_pos})

val implies_neg1_thm = @{lemma \<open>(a \<longrightarrow> b) \<or> a\<close> by blast}
val implies_neg1 = prove_implies_pos_neg implies_neg1_thm

val implies_neg2_thm = @{lemma \<open>(a \<longrightarrow> b) \<or> \<not>b\<close> by blast}
val implies_neg2 = prove_implies_pos_neg implies_neg2_thm

val implies_thm = @{lemma \<open>(a \<longrightarrow> b) \<Longrightarrow> \<not>a \<or> b\<close> by blast}

(*<eigentlich will man backwards proven, aber zu dem Zeitpunkt war das reordering der conclusion
noch nicht klar, ausserdem einfacher zu debuggen

Um es backwards zu machen:

resolve_tac ctxt [implies_thm OF prems]

Koennte man am schluss aendern

*)
fun implies_rules ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [implies_thm OF prems]
  THEN' TRY' (assume_tac ctxt))

end


(* BFun *)

local
  val bfun_theorems = @{thms alethe_bfun_elim}
in

fun bfun_elim ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt prems
  THEN' TRY' (eqsubst_all ctxt bfun_theorems)
  THEN' TRY' (assume_tac ctxt)
  THEN' TRY' (partial_simplify_tac ctxt @{thms ac_simps eq_commute all_conj_distrib ex_disj_distrib}))

end


(* If-Then-Else *)

local
  fun prove_ite ite_thm thm ctxt =
  resolve_tac ctxt [ite_thm OF [thm]]
  THEN' TRY' (assume_tac ctxt)

  fun prove_by_resolve ctxt thm t = SMT_Replay_Methods.prove ctxt t (fn _ => resolve_tac ctxt thm)
in

val ite_pos1_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<or> x \<or> Q\<close> by auto}

fun ite_pos1 ctxt _ = prove_by_resolve ctxt [ite_pos1_thm]

val ite_pos2_thms =
  @{lemma \<open>\<not>(if x then P else Q) \<or> \<not>x \<or> P\<close> \<open>\<not>(if \<not>x then P else Q) \<or> x \<or> P\<close> by auto}

fun ite_pos2 ctxt _ = prove_by_resolve ctxt ite_pos2_thms

val ite_neg1_thms =
  @{lemma \<open>(if x then P else Q) \<or> x \<or> \<not>Q\<close> \<open>(if x then P else \<not>Q) \<or> x \<or> Q\<close> by auto}

fun ite_neg1 ctxt _ = prove_by_resolve ctxt ite_neg1_thms

val ite_neg2_thms =
  @{lemma \<open>(if x then P else Q) \<or> \<not>x \<or> \<not>P\<close> \<open>(if \<not>x then P else Q) \<or> x \<or> \<not>P\<close>
          \<open>(if x then \<not>P else Q) \<or> \<not>x \<or> P\<close> \<open>(if \<not>x then \<not>P else Q) \<or> x \<or> P\<close>
      by auto}

fun ite_neg2 ctxt _ t = prove_by_resolve ctxt ite_neg2_thms t

val ite1_thm =
  @{lemma \<open>(if x then P else Q) \<Longrightarrow> x \<or> Q\<close> by (auto split: if_splits) }

fun ite1 ctxt thm t = SMT_Replay_Methods.prove ctxt t
  (fn _ => prove_ite ite1_thm (extract_single_premise ITE1 ctxt thm t) ctxt)

val ite2_thm =
  @{lemma \<open>(if x then P else Q) \<Longrightarrow> \<not>x \<or> P\<close> by (auto split: if_splits) }

fun ite2 ctxt thm t = SMT_Replay_Methods.prove ctxt t
  (fn _ => prove_ite ite2_thm (extract_single_premise ITE2 ctxt thm t) ctxt)

val not_ite1_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<Longrightarrow> x \<or> \<not>Q\<close> by (auto split: if_splits) }

fun not_ite1 ctxt thm t = SMT_Replay_Methods.prove ctxt t
  (fn _ => prove_ite not_ite1_thm (extract_single_premise Not_ITE1 ctxt thm t) ctxt)

val not_ite2_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<Longrightarrow> \<not>x \<or> \<not>P\<close> by (auto split: if_splits) }

fun not_ite2 ctxt thm t = SMT_Replay_Methods.prove ctxt t
  (fn _ => prove_ite not_ite2_thm (extract_single_premise Not_ITE2 ctxt thm t) ctxt)

(*ite_intro can introduce new terms that are in the proof exactly the sames as the old one, but are
not internally, hence the possible reordering.

FINAL TEST: after updating this in 2026, I did not find any example that needed anything
besides the first rule. The rest is kept as legacy though, because there are very few
case of this rule in our tests.*)
fun ite_intro ctxt _ t =
  let
    fun simplify_ite ctxt thms cong =
      ctxt
      |> Simplifier.empty_simpset
      |> put_simpset HOL_basic_ss
      |> Simplifier.add_simps (thms @ @{thms simp_thms})
      |> cong ? (Raw_Simplifier.add_eqcong @{thm alethe_ite_if_cong})
      |> Simplifier.full_simp_tac
    val use_cong = true
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      simplify_ite ctxt @{thms alethe_ite_intro(1-4)} (not use_cong)
      THEN' TRY' (simplify_ite ctxt @{thms alethe_ite_intro(1-6)} (not use_cong))
      THEN' TRY' (simplify_ite ctxt @{thms if_cancel} use_cong)
      THEN' TRY' (simplify_ite ctxt @{thms eq_commute} use_cong))
  end
end


(* Quantifiers *)

local
  (**)
  fun term_contains v (t $ u) =
        t = v orelse v = u orelse term_contains v t orelse term_contains v u
    | term_contains v (s as Abs (_, _, xs)) =
        v = s orelse term_contains v xs
    | term_contains v t = v = t

  fun repeat_rewrite_bottom_up1 ctxt thms1 ctrm =
      if fastype_of (ctrm |> Thm.term_of) <> @{typ bool} then Conv.all_conv ctrm
      else
        ctrm
        |> (case ctrm |> Thm.term_of of
              _ $ _ =>
               Conv.fun_conv (repeat_rewrite_bottom_up1 ctxt thms1)
               then_conv Conv.try_conv (Conv.arg_conv (Conv.rewrs_conv thms1))
               then_conv Conv.try_conv (Conv.rewrs_conv thms1)
           | Abs _ => Conv.try_conv (Conv.abs_conv (fn (_, ctxt) => repeat_rewrite_bottom_up1 ctxt thms1) ctxt)
           | _ => Conv.try_conv (Conv.rewrs_conv thms1))

  fun repeat_until_fixpoint_conv ctxt conv =
    Conv.repeat_conv (Conv.changed_conv (Conv.top_sweep_conv conv ctxt))
  fun repeat_until_fixpoint_conv2 ctxt thms =
    Conv.repeat_conv (Conv.changed_conv (Conv.top_sweep_rewrs_conv thms ctxt))
  fun find_independent_terms dest thms (v, ctxt) t =
    let
      val disjs =
        dest (Thm.term_of t)
        |> filter_out (term_contains (Thm.term_of v))
        |> map (Thm.cterm_of ctxt)
      fun move_term_to_the_beginning (ct :: cts) =
          print_conv "before moving out"
          then_conv repeat_until_fixpoint_conv2 ctxt (map (Drule.infer_instantiate' ctxt [NONE, SOME ct]) thms)
          then_conv print_conv "after moving 1 out" then_conv move_term_to_the_beginning cts
       | move_term_to_the_beginning [] = Conv.all_conv
    in
      t
      |> (move_term_to_the_beginning disjs then_conv print_conv "after moving out")
    end
  (*for miniscoping we go over the term recursively and if we detect a conjunction/disjunction with a term
   that does not depend on the variables, we move it to the front and rewrite the entire thing
   with rewr_conv outside of the quantifier.*)
  fun miniscope_term ctxt t =
    (case t |> Thm.term_of of
      \<^Const_>\<open>HOL.All _\<close> $ _ =>
        (*Conv.try_conv*) (Conv.arg_conv (Conv.abs_conv (find_independent_terms HOLogic.disjuncts
        @{thms disj_left_commute[THEN eq_reflection] disj_commute[THEN eq_reflection]}) ctxt)
        then_conv Conv.try_conv
           (repeat_until_fixpoint_conv ctxt
             (K (Conv.rewr_conv @{lemma \<open>\<And>P1 Q1. \<forall>x::'d1. (P1::bool) \<or> (Q1::'d1 \<Rightarrow> bool) x \<equiv> P1 \<or> (\<forall>x::'d1. Q1 x)\<close> by auto})))
        then_conv Conv.fun_conv (miniscope_term ctxt)
        then_conv Conv.arg_conv (miniscope_term ctxt)) t
     | \<^Const_>\<open>HOL.Ex _\<close> $ _ =>
        Conv.try_conv (Conv.arg_conv (Conv.abs_conv (find_independent_terms HOLogic.conjuncts
        @{thms conj_left_commute[THEN eq_reflection] conj_commute[THEN eq_reflection]}) ctxt)
        then_conv Conv.try_conv
           (repeat_until_fixpoint_conv ctxt
             (K (Conv.rewr_conv @{lemma \<open>\<And>P1 Q1. \<exists>x::'d1. (P1::bool) \<and> (Q1::'d1 \<Rightarrow> bool) x \<equiv> P1 \<and> (\<exists>x::'d1. Q1 x)\<close> by auto})))
        then_conv Conv.fun_conv (miniscope_term ctxt)
        then_conv Conv.arg_conv (miniscope_term ctxt)) t
    | _ $ _ => Conv.try_conv (Conv.fun_conv (miniscope_term ctxt) then_conv Conv.arg_conv (miniscope_term ctxt)) t
    | Abs _ => Conv.try_conv (Conv.abs_conv (fn (_, ctxt) => miniscope_term ctxt) ctxt) t
    | _ => Conv.all_conv t)

  fun imp_conv_all_premises ctxt f t =
    (case Thm.term_of t of
      (\<^Const_>\<open>Pure.imp\<close> $ _) $ _ =>
        t
        |> (Conv.fun_conv (imp_conv_all_premises ctxt f) then_conv Conv.arg_conv (imp_conv_all_premises ctxt f))
    | (\<^Const_>\<open>Pure.all _\<close> $ _) => (Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => imp_conv_all_premises ctxt f) ctxt)) t
    | (\<^Const_>\<open>Trueprop\<close> $ _) => HOLogic.Trueprop_conv (imp_conv_all_premises ctxt f) t
    | _ => f ctxt t)

  fun miniscope ctxt =
    (*HOLogic.Trueprop_conv (Conv.arg_conv (miniscope_term ctxt) then_conv Conv.fun_conv (Conv.arg_conv (miniscope_term ctxt)))*)
    imp_conv_all_premises ctxt miniscope_term

  fun imp_conv_only_concl ctxt f t =
    (case Thm.term_of t of
      (\<^Const_>\<open>Pure.imp\<close> $ _) $ _ => Conv.arg_conv (imp_conv_only_concl ctxt f) t
    | (\<^Const_>\<open>Pure.all _\<close> $ _) => (Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => imp_conv_only_concl ctxt f) ctxt)) t
    | (\<^Const_>\<open>Trueprop\<close> $ _) => HOLogic.Trueprop_conv (imp_conv_only_concl ctxt f) t
    | _ => f ctxt t)

  fun miniscope_conclusion ctxt = (imp_conv_only_concl ctxt miniscope_term)

  val all_comm = @{lemma "\<And>P Q. (\<forall>x y. P x y) \<equiv> (\<forall>y x. P x y)" by (subst all_comm)}
  fun plunge_down ctxt str ctrm =
   (case Thm.term_of ctrm of
     _ $ Abs (v, _, _) =>
       ctrm
       |> (if String.isPrefix v str
          then Conv.try_conv (Conv.rewr_conv all_comm)
             then_conv Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => plunge_down ctxt str) ctxt)
          else Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => plunge_down ctxt str) ctxt))
   | _ => Conv.all_conv ctrm)

  fun match_coefficients _ [] ctrm = Conv.all_conv ctrm
    | match_coefficients ctxt (x :: xs) ctrm =
       (case Thm.term_of ctrm of
         _ $ Abs (v, _, _) =>
           ctrm
           |>
             (if x = v
             then Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => match_coefficients ctxt xs) ctxt)
             else plunge_down ctxt v then_conv match_coefficients ctxt (x :: xs))
       | _ => Conv.all_conv ctrm)

   fun extract_outmost_forall_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, _, t)) =
         name :: (extract_outmost_forall_quantified_names_q t)
     | extract_outmost_forall_quantified_names_q _ = []

  (*even though not allowed in the standard, some quantifiers from the right might be missing
  in the left.*)
  fun match_names_between_left_and_right ctxt cterm =
    let
      val lvars =
        cterm
        |> Thm.term_of
        |> HOLogic.dest_Trueprop
        |> HOLogic.dest_disj
        |> hd
        |> HOLogic.dest_not
        |> extract_outmost_forall_quantified_names_q
      val rvars =
        cterm
        |> Thm.term_of
        |> HOLogic.dest_Trueprop
        |> HOLogic.dest_disj
        |> (hd o tl)
        |> extract_outmost_forall_quantified_names_q
      val lhs_only_var =
        lvars
        |> filter_out (member (op =) rvars)
      val shared_lvars =
        lvars
        |> filter (member (op =) rvars)
      fun plunge_down_lhs_only [] = Conv.all_conv
        | plunge_down_lhs_only (str :: xs) = plunge_down ctxt str then_conv plunge_down_lhs_only xs
    in
      (print_conv "start plunging_down" then_conv
        HOLogic.Trueprop_conv (Conv.fun_conv (Conv.arg_conv (Conv.arg_conv (print_conv "plugingdownin" then_conv (if null lhs_only_var then Conv.all_conv
       else plunge_down_lhs_only lhs_only_var)))))
      then_conv print_conv "after plunging_down" then_conv
      HOLogic.Trueprop_conv (Conv.arg_conv (match_coefficients ctxt shared_lvars))) cterm
    end
  val rm_unused = @{lemma \<open>(\<forall>x. P) = P\<close> \<open>(\<exists>x. P) = P\<close> by blast+}
  val cnf_conclusion_tac =
    Subgoal.FOCUS (fn {context = ctxt', concl, ...} =>
    let
      val cnf = CNF.make_cnf_thm ctxt' (concl |> HOLogic.dest_judgment |> Thm.term_of)
    in
      HEADGOAL (resolve_tac ctxt' [@{thm iffD2} OF [cnf]])
    end)

fun sort_disj ctxt t =
  let
    val disjs =
      HOLogic.disjuncts t
      |> sort Term_Ord.term_ord
    fun commute_last last =
      repeat_rewrite_bottom_up1 ctxt
        (map (Drule.infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt last)])
          @{thms disj_left_commute[THEN eq_reflection] disj_commute[THEN eq_reflection]})
    fun reorder_disj [] = Conv.all_conv
      | reorder_disj (last :: []) =
          commute_last last then_conv print_conv "after moving to final last"
      | reorder_disj (last :: others) =
          commute_last last then_conv print_conv "after moving to last"
          then_conv Conv.try_conv (Conv.arg_conv (reorder_disj others))
  in
    reorder_disj disjs
    then_conv repeat_until_fixpoint_conv2 ctxt
      @{thms disj_absorb[THEN eq_reflection] disj_left_absorb[THEN eq_reflection]}
  end

  fun sort_eq_conv t1 t2 =
    (case Term_Ord.term_ord (t1, t2) of
      LESS => Conv.rewr_conv @{thm eq_commute[THEN eq_reflection]}
    | _ => Conv.all_conv)


  (*The core of qnt_cnf:
    1. we match the name of the quantifiers left and right (the being a subset of the other). This
    is not necessary but makes the tactic call later more robust and faster.
    2. we transform \<not>P \<or> Q in P \<Longrightarrow> Q
    2a. fast path: if there are no quantifiers in Q, we rely on the simplifier to do unit
    propagation and derive false. This is much faster and avoids the exponential blow-up
    that appears otherwise (we saw trivial goals taking ~10s just because of the size of the term).
    3. we miniscope P and transform it into CNF (including replacement of implication that
    CNF.cnf_rewrite_tac does not do) and split the conjunctions.
    4. we check if we have an assumption.
    5. if not we sort the term.
    6. finally we check again if we have an assumption.
    7. if not solved, we call metis.


  Some historical notes:
    a. In Isabelle2025 and earlier we simply called blast/metis/meson and hoped for the best.

    b. last tactic: initially we used blast or metis at the end. Both failed (especially the latter
       means that metis is incomplete).

       We switched to fast, but this failed because it would
       timeout in some theories because of intro rule. As there is no way to empty the context
       (unlike the simplifier), this was not a solution.

       So we tried the simplifier... which failed
       at reordering within terms in practice: it worked on some example, but only if the CNF could
       be undone (reintroducing implications in order to use cong rules). Also it simplified some
       real examples to true if the variable was renamed.

       Therefore, we switched to doing the proof by hand.

       Sorting with conversion is extremely stupid, but well...

    c. We tried a lot of things to make the unfolding/conversion stuff faster, we never managed,
       including rewriting ourselves and using the fact that we know in what order we should do
       it.

    d. The motivation from the fast path comes from avoiding the exponential blow which we
       observed several times.
  *)

  fun simplify_tac_no_simps ctxt thms =
    ctxt
    |> Simplifier.empty_simpset
    |> Simplifier.put_simpset HOL_basic_ss
    |> Simplifier.add_simps thms
    |> Simplifier.asm_full_simp_tac


  fun reorder_prefix_to _ [] ctrm = Conv.all_conv ctrm
   | reorder_prefix_to ctxt (str :: xs) ctrm =
     (case (Thm.term_of ctrm) of
       _ $ Abs (v, _, _) =>
         if String.isPrefix v str
         then
           Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => reorder_prefix_to ctxt xs) ctxt) ctrm
         else
           (plunge_down ctxt v then_conv reorder_prefix_to ctxt (str :: xs)) ctrm
     | _ => Conv.all_conv ctrm)

  fun extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs (name, _, t)) =
        name :: (extract_all_forall_exists_quantified_names_q t)
    | extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, _, t)) =
        name :: (extract_all_forall_exists_quantified_names_q t)
    | extract_all_forall_exists_quantified_names_q _ = []
  fun reorder_quantifer ctxt prop =
    let val strs =
      prop
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq
      |> fst
      |> extract_all_forall_exists_quantified_names_q
    in
      CONVERSION (HOLogic.Trueprop_conv (Conv.arg_conv (reorder_prefix_to ctxt strs)))
    end

  (*unit propagation is sufficient (at least it is, when the conclusion is a single disjunction.

  We rewrite assumptions entirely so a = b, should only be used when replacing "a=b" by True.
  Also because veriT, we try a=b and b=a.*)
  fun try_early_simp_solve {context, concl, prems, ...} =
    let
      val vars =
        concl
        |> Thm.term_of
        |> HOLogic.dest_Trueprop
        |> extract_outmost_forall_quantified_names_q

      fun simplify_tac_with_cong simprocs ctxt thms =
        ctxt
        |> Simplifier.empty_simpset
        |> Simplifier.put_simpset HOL_basic_ss
        |> Simplifier.add_simps (@{thms simp_thms} @ thms)
        |> fold Simplifier.add_proc simprocs
        |> fold Simplifier.add_cong @{thms imp_cong}
        |> Simplifier.asm_full_simp_tac


      fun try_OF thm1 thm2 =
          (thm1 OF [thm2])
          |> single
        handle THM _ => []
      fun only_rewrite {context, prems=nprems, ...} =
        let val rewr_prems = ((take (length nprems - 1) nprems)
         @ maps (try_OF @{lemma \<open>\<And>a b. a = b \<equiv> True \<Longrightarrow> b = a \<equiv> True\<close> by (auto simp: eq_commute)})
           ((take (length nprems - 1) nprems)))
        in
          Method.insert_tac context [List.last nprems]
          (*the simplifier does not always rewrite assumptions*)
          THEN' (eqsubst_all context rewr_prems)
          THEN' simplify_tac_with_cong [] context
            (rewr_prems @ @{thms conj_assoc eq_commute if_True if_False})
          |> TRY'
          |> HEADGOAL
        end
    in
        if null vars
        then HEADGOAL (TRY' (
         resolve_tac context @{thms ccontr}
         THEN' (eqsubst_all context @{thms de_Morgan_disj[THEN eq_reflection]
           SMT.alethe_Box_def[THEN eq_reflection] not_not[THEN eq_reflection]})
         THEN' REPEAT' (eresolve_tac context [@{lemma \<open>P \<and> Q \<Longrightarrow> (P \<equiv> True \<Longrightarrow> Q \<equiv> True \<Longrightarrow> R) \<Longrightarrow> R\<close> by blast}])
         THEN' REPEAT' (eresolve_tac context
             @{lemma \<open>\<not>P \<equiv> True \<Longrightarrow> (P \<equiv> False \<Longrightarrow> R) \<Longrightarrow> R\<close>
             \<open>\<And>P Q R. (P \<and> Q) \<equiv> True \<Longrightarrow> (P \<equiv> True \<Longrightarrow> Q \<equiv> True \<Longrightarrow> R) \<Longrightarrow> R\<close>by blast+}
             )
         THEN' Method.insert_tac context prems
         THEN' (eqsubst_all context @{thms de_Morgan_disj[THEN eq_reflection]
           SMT.alethe_Box_def[THEN eq_reflection] not_not[THEN eq_reflection]})
         THEN' Subgoal.FOCUS only_rewrite context))
       else all_tac
      end
in

fun sort_disj_and_equality_in_term ctxt ctrm =
  ctrm
  |> (case (Thm.term_of ctrm) of
       _ $ Abs (_, _, _) =>
         Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => sort_disj_and_equality_in_term ctxt) ctxt)
    | t as (@{term \<open>HOL.disj\<close>} $ _) $ _ =>
        Conv.try_conv (Conv.fun_conv (sort_disj_and_equality_in_term ctxt))
        then_conv Conv.arg_conv (sort_disj_and_equality_in_term ctxt)
        then_conv sort_disj ctxt t
    | (@{term \<open>HOL.eq\<close>} $ t1) $ t2 =>
        Conv.fun_conv (sort_disj_and_equality_in_term ctxt)
        then_conv Conv.arg_conv (sort_disj_and_equality_in_term ctxt)
        then_conv sort_eq_conv t1 t2
    | _ $ _ =>
        Conv.arg_conv (sort_disj_and_equality_in_term ctxt) then_conv
        Conv.fun_conv (sort_disj_and_equality_in_term ctxt)
    | _ => Conv.all_conv)

fun qnt_cnf_tac ctxt =
  (debug_msg_tac' ctxt high "qnt_cnf start") THEN'
  (*step 1*)
  CONVERSION (match_names_between_left_and_right ctxt)
  THEN' REPEAT' (resolve_tac ctxt [@{lemma \<open>\<And>P Q. (\<And>x. \<not>P x \<or> Q x) \<Longrightarrow> \<not>(\<forall>x. P x) \<or> (\<forall>y. Q y)\<close> by blast}])
  (*step 2*)
  THEN' (*alethe_Box to make sure we don't conjE too much later*)
   (resolve_tac ctxt
    @{lemma
       \<open>\<And>a b A B. (SMT.alethe_Box (\<not>a \<and> \<not>b) \<Longrightarrow> A \<and> B) \<Longrightarrow> \<not>\<not>(a \<or> b) \<or> A \<and> B\<close>
       \<open>\<And>a A. (a \<Longrightarrow> A) \<Longrightarrow> \<not>a \<or> A\<close> by (auto simp: SMT.alethe_Box_def)})
  (*step 2a*)
  THEN' TRY' (SOLVED' (Subgoal.FOCUS try_early_simp_solve ctxt))
  (*step 3*)
  THEN' TRY' (eqsubst_all ctxt
    @{thms nnf_simps(4)[THEN eq_reflection] if_bool_eq_conj[THEN eq_reflection]
     imp_conv_disj[THEN eq_reflection] de_Morgan_conj[THEN eq_reflection] not_not[THEN eq_reflection]
    disj_assoc[THEN eq_reflection]})
  THEN' REPEAT' (eresolve_tac ctxt @{thms conjE})
  THEN' TRY' (CONVERSION (Conv.try_conv (Conv.top_sweep_rewrs_conv @{thms SMT.alethe_Box_def[THEN eq_reflection]} ctxt)))
  THEN' TRY' (DETERM' (CNF.cnf_rewrite_tac ctxt))
  THEN' TRY' (eqsubst_all ctxt (@{thms all_conj_distrib[THEN eq_reflection]}))
  THEN' REPEAT' (eresolve_tac ctxt @{thms conjE})
  THEN' TRY' (DETERM' (CONVERSION (miniscope ctxt)))
  THEN' TRY' (simplify_tac_no_simps ctxt (@{thms disj_assoc}))
  THEN' TRY' (CNF.cnf_rewrite_tac ctxt)
  THEN' TRY' (cnf_conclusion_tac ctxt) (*there is no method in CNF for that*)
  THEN' TRY' (eqsubst_all ctxt (@{thms all_conj_distrib[THEN eq_reflection]}))
  THEN' TRY' (CONVERSION (miniscope_conclusion ctxt))
  (*step 4*)
  THEN' TRY' (assume_tac ctxt)
  THEN' TRY' (CONVERSION (sort_disj_and_equality_in_term ctxt))
  THEN' TRY' (assume_tac ctxt)
  THEN' TRY' (REPEAT' (eresolve_tac ctxt @{thms conjE}))
  THEN' TRY' (REPEAT' (resolve_tac ctxt @{thms conjI}))
  THEN' TRY' (assume_tac ctxt)
  (*step 5*)
  THEN' TRY' (REPEAT' (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt []))

fun qnt_rm_unused ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  K (unfold_tac ctxt rm_unused)
  THEN' (debug_msg_tac' ctxt high "qnt_rm_unused")
  THEN' TRY' (SUBGOAL (fn (prop, i) => reorder_quantifer ctxt prop i))
  THEN' TRY' (resolve_tac ctxt @{thms refl})
  )

local
  fun aconv_untyped (tm1, tm2) =
    pointer_eq (tm1, tm2) orelse
      (case (tm1, tm2) of
        (t1 $ u1, t2 $ u2) => aconv_untyped (t1, t2) andalso aconv_untyped (u1, u2)
      | (Abs (_, _, t1), Abs (_, _, t2)) => aconv_untyped (t1, t2)
      | (Const (a, _), Const (b, _)) => a = b
      | (Free (x, _), Free (y, _)) => x = y
      | (Var ((xi,_), _), Var ((yj,_), _)) => xi = yj
      | (Bound i, Bound j) => i = j
      | _ => false);
  fun subst_var_untyped [] = I
    | subst_var_untyped pairs =
        let fun substf u =
              case AList.lookup aconv_untyped pairs u of
                  SOME u' => u'
                | NONE => (case u of Abs(a,T,t) => Abs(a, T, substf t)
                                   | t$u' => substf t $ substf u'
                                   | _ => u)
        in substf end;
  val to_upper = String.implode o (map Char.toUpper) o String.explode
  fun resolve_and_instantiate_onepoint n1 (i, j: term) insts {context, params, ...} =
    let
       val i =
         (case i of
           Var ((n2, _), _) => if n1 = to_upper n2 then j else i
         | _ => i) (*veriT: j or i; cvc5: only j*)
         |> Term.subst_free insts
         |> subst_var_untyped (map (fn (x, t) => (Var ((x, 0), @{typ dummy}), Thm.term_of t)) params)
         |> Thm.cterm_of context

       val thms = map (Drule.infer_instantiate' context [SOME i])
           @{thms alethe_onepoint2_all alethe_onepoint2_ex}

    in
      resolve_tac context thms 1
    end
  fun onepoint_combine_quant ctxt (n1 :: bounds1) (n2 :: bounds2) (i :: insts) past_ints =
      TRY' (if n1 = n2
        then resolve_tac ctxt @{thms alethe_onepoint(1,3)}
         THEN' onepoint_combine_quant ctxt bounds1 bounds2 (i :: insts) past_ints
       else Subgoal.FOCUS (resolve_and_instantiate_onepoint n1 i past_ints) ctxt
         THEN' onepoint_combine_quant ctxt bounds1 (n2 :: bounds2) insts (past_ints @ [i]))
    | onepoint_combine_quant ctxt (n1 :: bounds1) [] (i :: insts) past_ints =
      Subgoal.FOCUS (resolve_and_instantiate_onepoint n1 i past_ints) ctxt
      THEN' onepoint_combine_quant ctxt bounds1 [] insts (past_ints @ [i])
    | onepoint_combine_quant _ _ _ _ _ = K all_tac

  fun extract_implications
     (Const (\<^const_name>\<open>Pure.imp\<close>,_) $
       (Const (\<^const_name>\<open>Trueprop\<close>,_) $ (Const (\<^const_name>\<open>HOL.eq\<close>,_) $ u $ v)) $
       t) = (u, v) :: extract_implications t
    | extract_implications _ = []

  val extract_instantiations =
    Thm.prop_of
    #> extract_implications

  fun onepoint_quants ctxt prems t =
    let
      val insts = extract_instantiations prems
      val (t1, t2) =
        t
        |> Thm.cterm_of ctxt
        |> Thm.term_of o Object_Logic.dest_judgment ctxt
        |> HOLogic.dest_eq
    in
       (*on external variable, names can change from BOUND to bOUND.*)
       onepoint_combine_quant ctxt
         (extract_quantified_names_q t1 |> fst |> map to_upper)
         (extract_quantified_names_q t2 |> fst |> map to_upper)
         insts
    end
in
fun onepoint ctxt [prem] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  onepoint_quants ctxt prem t []
  THEN' REPEAT' (resolve_tac ctxt @{thms refl})
  THEN_ALL_NEW
    (*cheap version: hope that nothing got reorder and simp will solve the goal. Otherwise,
    try to move all equalities out of the quantifiers rewrite them with @{thm alethe_rewrite_in_imp}
    and only afterwards try metis.*)
    ((SOLVED' (
      (ctxt
      |> Simplifier.empty_simpset
      |> Simplifier.put_simpset HOL_basic_ss
      |> Simplifier.add_simps @{thms simp_thms all_simps ex_simps de_Morgan_conj
        not_all not_ex de_Morgan_disj disj_not1 triv_forall_equality eq_commute
        alethe_onepoint_simp alethe_imp_commute}
      |> Simplifier.add_cong @{thm alethe_rewrite_in_imp}
      |> fold Simplifier.add_proc [@{simproc defined_All}, @{simproc defined_Ex}]
      |> Simplifier.asm_full_simp_tac)))
    ORELSE'
      (*
      This part becomes really messy:
        - veriT can still reorder equalities, so we need something stronger
        than just reordering the implication as done above.
        - simp can destroy the structure
        - metis is not always able to solve the goal, even if it falls within
        the fragment of logic where it for sure should be able to.
      *)
      REPEAT' (SOLVED' (SOLVED' (Meson.meson_tac ctxt []) (*meson sometimes does nothing*)
        ORELSE' Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt []
        ORELSE' K (Clasimp.auto_tac ctxt)))))


end

fun qnt_join ctxt _ t = SMT_Replay_Methods.prove ctxt t Classical.fast_tac

(*qnt_cnf is one of the most complicated rules to reconstruct:

  1) no tactic works: metis is incomplete even if it should be in the fragment;
  blast sometimes fails.

  2) the description of the rule is incorrect: not all --> operators are replaced and not all parts
  of the formula are transformed into CNF.

  3) as the tactic does not transform the entire formula as CNF and it is not documented how deep
  this goes, we cannot assume that we get only one disjunction (we really saw having one conjunction
  in the conclusion)

In the old version we had a mix of metis/blast. We then improved the reconstruction but lost some
of the problems. Therefore, we try to be faithful and make the reconstruction as simple as possible
for the tactics we use, see the comments in qnt_cnf_tac.

In essence, we follow the approach from carcara: CNF transformation, then distribution of forall
quantifiers.
*)
fun qnt_cnf ctxt _ t = SMT_Replay_Methods.prove ctxt t qnt_cnf_tac

fun qnt_simplify ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
      partial_simplify_tac ctxt [])

end

(* Equality *)

fun eq_transitive ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  REPEAT_CHANGED (resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF @{thms impI}])
  THEN' REPEAT' (resolve_tac ctxt @{thms impI})
  THEN' REPEAT' (eresolve_tac ctxt @{thms conjI})
  THEN' REPEAT' (fn i => dresolve_tac ctxt @{thms alethe_eq_transitive} i THEN assume_tac ctxt (i+1))
  THEN' resolve_tac ctxt @{thms refl})


(*
In essence, congruence, eq_congruent_pred, and eq_congruent are all the same. The idea is to iterate
over the term, identify which terms needs to be rewritten, and we rewrite it.

For congruence we do two different things:

  1. usually, we simply go over the term in a conversion and check if there is a lemma that can be
  used for rewriting. Complexity here comes from the fact that we need to be careful with lambda /
  non-reduced terms.

  We experimented with various versions and found that we need to avoid iterating over the entire
  term. Therefore, we calculate the size of the term and don't try to rewrite if the term is
  smaller than the smallest term to rewrite. However, the size calculation is only useful if you
  need to go over the full term, which the standard does not allow for now. Therefore, we removed
  it again and simplified the procedure.


  2. otherwise, we look for things (%x. f x) = (%x. g x), a = b |> (%x. f x) a = (%x. g x) b. For
  eq_congruent_pred we don't have an issue because we simply avoid unfolding the lambda terms and
  keep them as constants. This does not work for cong, because we cannot refold the terms in the
  assumptions.

*)
local
  fun find_rew rews t t' =
    (case AList.lookup (fn ((a,b), (c,d))=> a aconv c andalso b aconv d) rews (t, t') of
      SOME thm => SOME (thm COMP @{thm symmetric})
    | NONE =>
      (case AList.lookup (fn ((a,b), (c,d))=> a aconv c andalso b aconv d) rews (t', t) of
        SOME thm => SOME thm
      | NONE => NONE))
  fun strict_find_rew rews t t' =
    (case AList.lookup (fn ((a,b), (c,d))=> a aconv c andalso b aconv d) rews (t', t) of
      SOME thm => SOME thm
    | NONE => NONE)

  fun eq_pred_conv rews t ctxt ctrm =
    (case find_rew rews t (Thm.term_of ctrm) of
      SOME thm => Conv.rewr_conv thm ctrm
    | NONE =>
      (case t of
        f $ arg =>
          (Conv.fun_conv (eq_pred_conv rews f ctxt) then_conv
             Conv.arg_conv (eq_pred_conv rews arg ctxt)) ctrm
      | Abs (_, _, f) => Conv.abs_conv (eq_pred_conv rews f o snd) ctxt ctrm
      | _ => Conv.all_conv ctrm))

  fun throwing_CONVERSION cv i st = Seq.single (Conv.gconv_rule cv i st)
  fun eq_pred_rewrite_tac ({context = ctxt, prems, concl, ...}: Subgoal.focus) =
    let
      val rews = prems
        |> map_filter (try (apfst (HOLogic.dest_eq o Thm.term_of o Object_Logic.dest_judgment ctxt o
             Thm.cconcl_of) o `(fn x => x)))
        |> map (apsnd (fn x => @{thm eq_reflection} OF [x]))
      fun conv_left conv = Conv.arg_conv (Conv.arg_conv conv)
      fun conv_left_neg conv = Conv.arg_conv (Conv.arg_conv (Conv.arg_conv conv))
      val (t1, conv_term) =
        (case Thm.term_of (Object_Logic.dest_judgment ctxt concl) of
          Const(_, _) $ (Const(\<^const_name>\<open>HOL.Not\<close>, _) $ t1) $ _ => (t1, conv_left)
        | Const(_, _) $ t1 $ (Const(\<^const_name>\<open>HOL.Not\<close>, _) $ _) => (t1, conv_left_neg)
        | Const(_, _) $ t1 $ _ => (t1, conv_left)
        | t1 => (t1, conv_left))
    in
      throwing_CONVERSION (conv_term (eq_pred_conv rews t1 ctxt))
    end

  (*CVC Note: 
    Prior to boxing lambda terms, the following places contained a beta_eta normalization:
          1. only_replace: (Thm.term_of ctrm)
          2. cong_conv: t'
          3. cong_conv: rews
    In case some normalization issue still occurs, additional considerations have to be made here*)
  fun only_replace rews t ctrm =
    (case strict_find_rew rews t (Thm.term_of ctrm) of
      SOME thm => Conv.rewr_conv thm ctrm
    | NONE => Conv.no_conv ctrm)

  fun cong_cong_conv rews t ty ctxt =
    (case t of
      f $ arg =>
        Conv.try_conv
          (Conv.fun_conv (only_replace rews f else_conv cong_cong_conv rews f ty ctxt)
          then_conv
            (if fastype_of arg = ty
             then
               Conv.arg_conv (only_replace rews arg)
               else_conv Conv.arg_conv (cong_cong_conv rews arg ty ctxt)
             else Conv.try_conv (Conv.arg_conv (only_replace rews arg))))
    | _ => Conv.all_conv)

  exception no_lambda

  fun cong_conv ctxt prems t =
    let
      val t' = t
        |> Thm.term_of
        |> HOLogic.dest_Trueprop
        |> HOLogic.dest_eq
        |> snd

      val rews = prems
        |> map_filter (try (apfst (
            HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.term_of o Thm.cconcl_of) o
            `(fn x => x)))
        |> filter_out (fn ((a, b), _) => a = b)
        |> map (apsnd (fn x => @{thm eq_reflection} OF [x]))
    in
      (case rews of
        [] => Conv.all_conv t
      | _ =>
          t
          |> HOLogic.Trueprop_conv (HOLogic.eq_conv
               (cong_cong_conv rews t' (fastype_of t') ctxt)
               Conv.all_conv))
    end
in

fun eq_congruent_pred ctxt _ t =
   SMT_Replay_Methods.prove ctxt t (fn _ =>
   REPEAT' (resolve_tac ctxt [@{thm disj_not1[of \<open>_ = _\<close>]} RSN (1, @{thm iffD2}) OF @{thms impI}])
   THEN' (fn i => Subgoal.FOCUS (fn focus => eq_pred_rewrite_tac focus i) ctxt i)
   THEN' (resolve_tac ctxt @{thms refl excluded_middle excluded_middle[of \<open>\<not>_\<close>, unfolded not_not]}
     ORELSE' assume_tac ctxt))

val eq_congruent = eq_congruent_pred

fun equality_ordered_cong ctxt prems t _ =
   SMT_Replay_Methods.prove ctxt t (fn _ =>
     TRY' (CONVERSION (cong_conv ctxt prems)
     THEN' (resolve_tac ctxt @{thms refl})))

end


(* Subproof *)


(*
The reconstruction of subproof changed a lot over time, thanks to the stricter assumptions.
There are currently three paths:
  1. The most efficient which might however not work if the conclusion of
  the subproof is A & B

  2. The second step where we unify with the premise and the we enable
  reordering of equalities assuming

  3. We hammer on the goal.


*)
fun ordered_subproof ctxt [prem] t =
     SMT_Replay_Methods.prove ctxt t (fn _ =>
      SOLVED' (
        REPEAT' (DETERM' (match_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}],
            @{thm disj_not1[of \<open>\<not>_\<close>, unfolded not_not]} RSN (1, @{thm iffD2}) OF [@{thm impI}]])
          THEN' (TRY' o SOLVED') (match_tac ctxt [prem]
            THEN_ALL_NEW eq_assume_tac))))
  | ordered_subproof ctxt prems t =
      replay_error ctxt "invalid application, only one assumption expected" Subproof prems [] t

fun subproof ctxt [prem] t =
     SMT_Replay_Methods.prove ctxt t (fn _ =>
      SOLVED' (REPEAT' (resolve_tac ctxt @{thms alethe_and_neg(2)})
        THEN' TRY' (resolve_tac ctxt [prem])
        THEN' REPEAT' eq_assume_tac)
      ORELSE' SOLVED' (
        REPEAT' (resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}],
           @{thm disj_not1[of \<open>\<not>_\<close>, unfolded not_not]} RSN (1, @{thm iffD2}) OF [@{thm impI}]])
        THEN' resolve_tac ctxt [prem]
        THEN_ALL_NEW (eq_assume_tac
          ORELSE'
            SOLVED' ((partial_simplify_tac ctxt @{thms eq_commute ac_simps}
            THEN' TRY' eq_assume_tac)))
          THEN' TRY' eq_assume_tac)
      ORELSE' TRY' (Method.insert_tac ctxt [prem]
        THEN' TRY' (partial_simplify_tac ctxt @{thms eq_commute ac_simps})
        THEN' TRY' (Blast.blast_tac ctxt)))
  | subproof ctxt prems t =
      replay_error ctxt "invalid application, only one assumption expected" Subproof prems [] t


(* Simplifying Steps *)

(* The reconstruction is a bit tricky: At first we only rewrite only based on the rules that are
passed as argument. Then we simply use simp_thms to reconstruct all the proofs (and these theorems
cover all the simplification below).
*)
local
  fun rewrite_only_thms ctxt thms =
    ctxt
    |> Simplifier.empty_simpset
    |> Simplifier.put_simpset HOL_basic_ss
    |> Simplifier.add_simps thms
    |> Simplifier.full_simp_tac

  fun rewrite_thms ctxt thms =
    ctxt
    |> Simplifier.empty_simpset
    |> Simplifier.put_simpset HOL_basic_ss
    |> Raw_Simplifier.add_eqcong @{thm eq_reflection[OF imp_cong]}
    |> Simplifier.add_simps (thms @ @{thms simp_thms})
    |> Simplifier.full_simp_tac

  fun chain_rewrite_thms ctxt thms =
    TRY' (rewrite_only_thms ctxt thms)
    THEN' TRY' (rewrite_thms ctxt thms)

  fun chain_rewrite_two_step_with_ac_simps ctxt thms1 thms2 =
    TRY' (rewrite_only_thms ctxt thms1)
    THEN' TRY' (rewrite_thms ctxt thms2)

in
fun rewrite_bool_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_thms ctxt @{thms alethe_bool_simplify conj_assoc}))

fun rewrite_and_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt @{thms alethe_and_simplify alethe_and_simplify1}
     @{thms alethe_and_simplify}))

(*
Currently the tactic does not support steps like
  (P False \<or> P True \<or> \<not> P False) = True
hence the fast at the end.
*)
fun rewrite_or_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt @{thms alethe_or_simplify alethe_or_simplify_1}
    @{thms alethe_or_simplify})
    THEN' TRY' (REPEAT' (match_tac ctxt @{thms alethe_and_pos}) THEN' (assume_tac ctxt))
    THEN' TRY' (Classical.fast_tac ctxt))

fun rewrite_not_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms ctxt @{thms alethe_not_simplify}))

fun rewrite_equiv_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms ctxt @{thms alethe_equiv_simplify}))

fun rewrite_eq_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt
      @{thms alethe_eq_simplify}
      (Named_Theorems.get ctxt @{named_theorems ac_simps})))

fun rewrite_implies_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    (rewrite_only_thms ctxt @{thms alethe_implies_simplify}))

fun rewrite_connective_def ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
 ((*K (print_tac ctxt "before1")THEN'*)
      match_tac ctxt @{thms alethe_connective_def}
  (*    THEN' K (print_tac ctxt "after step 1")*)
)
ORELSE'
 ((*K (print_tac ctxt "before2")THEN'*)
    K (unfold_tac ctxt @{thms not_ex not_not not_all})
      (*THEN' K (print_tac ctxt "after step 0")*)

     THEN' REPEAT' (match_tac ctxt @{thms alethe_connective_def_forall})
    (*  THEN' K (print_tac ctxt "after step 2")*)

      THEN' K (unfold_tac ctxt @{thms not_not })
     (*   THEN' K (print_tac ctxt "after step 3")*)

      THEN' TRY' (resolve_tac ctxt @{thms refl})
     (*   THEN' K (print_tac ctxt "after step 4")*)
)
)

fun rewrite_minus_simplify ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      chain_rewrite_two_step_with_ac_simps ctxt
         @{thms arith_simps alethe_minus_simplify}
         (Named_Theorems.get ctxt @{named_theorems ac_simps} @
          @{thms numerals arith_simps arith_special
             numeral_class.numeral.numeral_One}))

fun rewrite_comp_simplify ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
        chain_rewrite_thms ctxt @{thms alethe_comp_simplify})

fun rewrite_ite_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms ctxt @{thms alethe_ite_simplify}))

end


(* Simplifications *)

local
  fun simplify_arith ctxt thms = partial_simplify_tac ctxt
    (thms @ Named_Theorems.get ctxt @{named_theorems ac_simps} @ @{thms arith_simps})
  fun simplify_arith_ifcong ctxt thms = partial_simplify_tac_with_cong @{thm if_weak_cong}
    [@{simproc int_div_cancel_numeral_factors}, @{simproc int_combine_numerals},
         @{simproc divide_cancel_numeral_factor}, @{simproc divide_cancel_factor},
         @{simproc intle_cancel_numerals}, @{simproc intless_cancel_numerals}, @{simproc inteq_cancel_numerals},
         @{simproc field_combine_numerals},
         @{simproc ring_le_cancel_numeral_factor},
         @{simproc Numeral_Simprocs.semiring_assoc_fold},
         @{simproc Numeral_Simprocs.field_divide_cancel_numeral_factor},
         @{simproc Numeral_Simprocs.field_eq_cancel_numeral_factor}]
     ctxt
    (thms @ Named_Theorems.get ctxt @{named_theorems ac_simps} @ @{thms arith_simps})
in

fun sum_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    simplify_arith ctxt @{thms alethe_sum_simplify arith_special}
    )

fun prod_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    simplify_arith ctxt @{thms alethe_prod_simplify}
    )

fun div_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    simplify_arith_ifcong ctxt @{thms alethe_div_simplify}
    )

end

fun rare_rewrite ctxt prems t = (
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    Method.insert_tac ctxt prems
    THEN' K (print_tac ctxt "use cvc5 extension for better success rate")
    THEN' TRY' (K (Clasimp.auto_tac ctxt)
    THEN' TRY' (Code_Simp.dynamic_tac ctxt)
)))

val evaluate = rare_rewrite

(* Arithmetics *)
local
val la_rw_eq_thm = @{lemma \<open>((a :: 'a :: linorder) = b) = ((a \<le> b) \<and> (b \<le> a))\<close> by auto}
in
fun la_rw_eq ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t la_rw_eq_thm

fun la_generic_prove args ctxt _ = SMT_Replay_Arith.la_farkas args ctxt

fun la_generic ctxt _ t args =
  prove_abstract (SMT_Replay_Methods.abstract_arith_shallow ctxt) (la_generic_prove args) ctxt [] t

fun lia_generic ctxt _ t =
  SMT_Replay_Methods.prove_arith_rewrite SMT_Replay_Methods.abstract_neq ctxt t

fun la_disequality ctxt _ t =
  SMT_Replay_Methods.match_instantiate ctxt t @{thm alethe_la_disequality}

(*Oct 18: I am not done here yet but it works already*)
fun la_mult_pos ctxt _ t =
let
 (* val (rel,(factor,l,r)) = la_mult_extract t*)
(*  val _ = @{print}("factor",(Thm.cterm_of ctxt factor))
  val _ = @{print}("lemma",infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt factor),NONE,NONE] @{thm alethe_la_mult_pos_less} )
  val _ = @{print}("lemma",infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt factor),SOME (Thm.cterm_of ctxt l),SOME (Thm.cterm_of ctxt r)] @{thm alethe_la_mult_pos_less} )
*)
in
 (* SMT_Replay_Methods.prove ctxt t (fn _ => match_tac ctxt [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt factor),NONE,NONE] @{thm alethe_la_mult_pos_less} ]))*)
  SMT_Replay_Methods.prove ctxt t (fn _ =>
(*K (print_tac ctxt "la_mult")
THEN'*) match_tac ctxt @{thms alethe_la_mult_pos}
THEN' TRY' (assume_tac ctxt)
(*THEN' K (print_tac ctxt "la_mult 1")*)
THEN' Simplifier.full_simp_tac ctxt
(*THEN' K (print_tac ctxt "la_mult 2")*)

)

end

fun la_mult_neg ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
(*K (print_tac ctxt "la_mult")
THEN'*) match_tac ctxt @{thms alethe_la_mult_neg}
THEN' TRY' (assume_tac ctxt)
(*THEN' K (print_tac ctxt "la_mult 1")*)
THEN' Simplifier.full_simp_tac ctxt
(*THEN' K (print_tac ctxt "la_mult 2")*)

)
end

fun poly_simp ctxt _ =
  let
    (*push of_int through arithmetic operators first*)
    val of_int_push_thms = @{thms of_int_add of_int_diff of_int_mult of_int_minus
      of_int_numeral of_int_neg_numeral of_int_1 of_int_0 of_int_of_nat_eq}
    fun push_of_int_tac ctxt =
      ctxt
      |> Simplifier.empty_simpset
      |> Simplifier.put_simpset HOL_basic_ss
      |> Simplifier.add_simps of_int_push_thms
      |> Simplifier.full_simp_tac
    fun simplify_tac ctxt thms =
      ctxt
      |> Simplifier.empty_simpset
      |> Simplifier.put_simpset HOL_basic_ss
      |> Simplifier.add_simps (@{thms simp_thms} @ thms)
      |> (Simplifier.add_cong @{thm if_weak_cong})
      |> fold Simplifier.add_proc [@{simproc int_div_cancel_numeral_factors}, @{simproc int_combine_numerals},
           @{simproc divide_cancel_numeral_factor}, @{simproc divide_cancel_factor},
           @{simproc intle_cancel_numerals}, @{simproc intless_cancel_numerals}, @{simproc inteq_cancel_numerals},
           @{simproc field_combine_numerals},
           @{simproc ring_le_cancel_numeral_factor},
           @{simproc HOL.NO_MATCH}, @{simproc Numeral_Simprocs.semiring_assoc_fold},
           @{simproc Numeral_Simprocs.field_divide_cancel_numeral_factor},
           @{simproc Numeral_Simprocs.field_eq_cancel_numeral_factor}]
      |> Simplifier.full_simp_tac
    fun simplify_tac_with_background_simp ctxt thms =
      ctxt
      |> Simplifier.add_simps thms
      |> Simplifier.full_simp_tac
    val tac = (fn _ => fn _ =>
        SOLVED' (
        TRY' (push_of_int_tac ctxt)
        THEN' TRY' (debug_msg_tac' ctxt high "pushed of_int to leaves before poly simp")
        THEN' TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems alethe_poly_norm}))
        THEN' TRY' (debug_msg_tac' ctxt high "tried to solve poly simp with custom simplify tac"))
        (*if the previous does not solve, use full simplification power with the current content*)
      ORELSE'
        TRY' (simplify_tac_with_background_simp ctxt []
        THEN' TRY' (debug_msg_tac' ctxt high "tried full simplifier power on current arith_poly_norm step"))
      THEN' TRY' (Code_Simp.dynamic_tac ctxt)
      THEN' TRY' (debug_msg_tac' ctxt high "tried code evaluation on arith_poly_norm step since nothing else worked"))
  in
    prove_abstract (SMT_Replay_Methods.abstract_for_poly_norm ctxt) tac ctxt []
  end

local
  val lemma = @{lemma "((a::'a::{field}) \<noteq> 0 \<and> b \<noteq> 0) \<Longrightarrow> (a / b \<noteq> 0)" by simp}
  val poly_simp_rel_assms_thms = @{thms divide_eq_0_iff ring_char_0_class.neg_numeral_neq_zero zero_neq_one_class.one_neq_zero ring_char_0_class.neg_one_neq_zero semiring_char_0_class.numeral_neq_zero}
in
fun poly_simp_rel ctxt [thm] t =
        SMT_Replay_Methods.prove ctxt t (fn _ => (
         (resolve_tac ctxt [@{lemma "P \<Longrightarrow> P \<longrightarrow> Q \<Longrightarrow> Q" by simp} OF [thm]] )
         THEN' debug_msg_tac' ctxt high "poly_simp_rel before applying lemma"
         THEN' TRY' (resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems alethe_poly_simp_rel}))
         THEN' debug_msg_tac' ctxt high "poly_simp_rel after applying lemma"
         THEN' TRY' (assume_tac ctxt)
         (*
         Non bv case:
         For constants cx and cy you'd have to prove that: ((cx > 0) = (cy > 0)), cx \<noteq> 0, cy \<noteq> 0
         For one of the cases you only need to prove the latter two.

         Bv case:
         You need to show odd cx, odd cy, cx * (x1 - x2) = 1 and cy * (x1 - x2) = 1
         *)
         THEN' REPEAT' (SOLVED' (partial_simplify_tac ctxt (@{thms alethe_poly_simp_rel_simps} @ @{thms arith_simps} @ (Named_Theorems.get ctxt @{named_theorems alethe_poly_simp_rel_bv_simps}))))
         THEN' debug_msg_tac' ctxt high "poly_simp_rel after first try of resolving premises"

         THEN' REPEAT'
            (TRY' (resolve_tac ctxt [lemma])
             THEN' TRY' (resolve_tac ctxt @{thms conjI})
             THEN' resolve_tac ctxt poly_simp_rel_assms_thms
             )
         THEN' debug_msg_tac' ctxt high "poly_simp_rel after resolving premises"
         ))
  | poly_simp_rel ctxt thms t = replay_error ctxt "invalid application in some poly_simp_rel rule" Unsupported thms [] t
end

(* Symm and Not_Symm*)

local
  fun prove_symm symm_thm ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [symm_thm OF [thm]]
        THEN' TRY' (assume_tac ctxt))
    | prove_symm _ ctxt thms t = replay_error ctxt "invalid application in some symm rule" Unsupported thms [] t
in
  val symm_thm =
  @{lemma \<open>(B = A) \<Longrightarrow> A = B\<close> by blast }
  val symm = prove_symm symm_thm

  val not_symm_thm =
  @{lemma \<open>\<not>(B = A) \<Longrightarrow> \<not>(A = B)\<close> by blast }
  val not_symm = prove_symm not_symm_thm
end

(* Shuffling Clauses and Arguments of Nary Commutative Operators *)

fun reordering (ctxt : Proof.context) [thm] t =
    if Term.size_of_term t > 100
    then
      prove_abstract SMT_Replay_Methods.abstract_bool_shallow (fn ctxt => fn [thm] => (
        Method.insert_tac ctxt [thm]
        THEN' match_tac ctxt @{thms ccontr}
        THEN' K (unfold_tac ctxt @{thms de_Morgan_disj})
        THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
        THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})
        THEN' REPEAT'(ematch_tac ctxt @{thms notE} THEN' TRY' (assume_tac ctxt))
        )) ctxt [thm] t
    else
      SMT_Replay_Methods.prove ctxt t (fn _ => (
        Method.insert_tac ctxt [thm]
        THEN' match_tac ctxt @{thms ccontr}
        THEN' K (unfold_tac ctxt @{thms de_Morgan_disj})
        THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
        THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})
        THEN' REPEAT'(ematch_tac ctxt @{thms notE} THEN' TRY' (assume_tac ctxt))
        ))
  | reordering ctxt thms t =
    replay_error ctxt "Too many or no premises in some reordering rule" Unsupported thms [] t

local

fun simplify_shuffle_tac ctxt thms =
  ctxt
  |> Simplifier.empty_simpset
  |> Simplifier.put_simpset HOL_basic_ss
  |> Simplifier.add_simps thms
  |> Simplifier.asm_full_simp_tac


in

fun shuffle ctxt _ _ t (SOME (CommOp @{term "HOL.conj"})) =
      (prove_abstract (SMT_Replay_Methods.abstract_shuffle @{term "HOL.conj"}) (fn ctxt => fn _ =>
        simplify_shuffle_tac ctxt @{thms Lattices.conj.commute Lattices.conj.left_commute conj_assoc}) ctxt [] t)
  | shuffle ctxt _ _ t (SOME (CommOp @{term "HOL.disj"})) =
      (prove_abstract (SMT_Replay_Methods.abstract_shuffle @{term "HOL.disj"}) (fn ctxt => fn _ =>
        simplify_shuffle_tac ctxt @{thms Lattices.disj.commute Lattices.disj.left_commute disj_assoc}) ctxt [] t)
  | shuffle ctxt thms _ t _ =
      replay_error ctxt "Unsupported commutative operator in shuffle rule" Unsupported thms [] t
end

fun contraction ctxt [prem] t =
  if Term.size_of_term t < 100
  then
    SMT_Replay_Methods.prove ctxt t (fn _ => (
       Method.insert_tac ctxt [prem]
       THEN' match_tac ctxt @{thms ccontr}
       THEN' K (unfold_tac ctxt @{thms de_Morgan_disj})
       THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
       THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})
       THEN' REPEAT'(ematch_tac ctxt @{thms notE} THEN' TRY' (assume_tac ctxt))
       ))
   else
    (*cvc5 produces steps with a lot of repetition (think about: 60 times the same literal).
    In those cases, the simplifier is much faster, because it can reduce the size
    of the term.*)
    prove_abstract SMT_Replay_Methods.abstract_bool_shallow (fn ctxt => fn prems => (
       Method.insert_tac ctxt prems
       THEN' simplify_tac ctxt @{thms disj.commute disj.left_commute})) ctxt [prem] t
| contraction ctxt thms t = replay_error ctxt "Unsupported commutative operator in contraction rule" Unsupported thms [] t


fun miniscope_distribute ctxt _ t =
 SMT_Replay_Methods.prove ctxt t (fn _ => (
    debug_rule_tac' ctxt high Miniscope_Distribute "start" THEN'
    REPEAT_CHANGED(
      K (unfold_tac ctxt @{thms alethe_miniscope_distribute})
      THEN' TRY' (debug_rule_tac' ctxt high Miniscope_Distribute "applied lemma"))
    THEN' debug_rule_tac' ctxt high Miniscope_Distribute "after repeating application of lemma"
    THEN' TRY' (resolve_tac ctxt @{thms refl})))

fun miniscope_split ctxt _ t =
 SMT_Replay_Methods.prove ctxt t (fn _ => (
    debug_rule_tac' ctxt high Miniscope_Split "start" THEN'
    REPEAT_CHANGED (
      K (unfold_tac ctxt @{thms alethe_miniscope_split})
      THEN' TRY' (debug_rule_tac' ctxt high Miniscope_Split "applied lemma"))
    THEN' debug_rule_tac' ctxt high Miniscope_Split "after repeating application of lemma"
    THEN' TRY' (resolve_tac ctxt @{thms refl})
    THEN' TRY' (blast_tac ctxt) (*variable reordering*)
))

fun miniscope_ITE ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ => (
    eqsubst_all ctxt @{thms alethe_miniscope_ITE}
    THEN' TRY' (resolve_tac ctxt @{thms refl})))

fun and_intro ctxt thms t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt thms
  THEN' REPEAT'
   ((match_tac ctxt [@{thm conjI}])
     THEN' TRY' (assume_tac ctxt))
  THEN' TRY' (assume_tac ctxt))

fun hole ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
   Method.insert_tac ctxt prems
   THEN' SOLVED' (
     resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems cvc5_holes_pre})
     THEN_ALL_NEW assume_tac ctxt)
   ORELSE' Clasimp.force_tac (Simplifier.add_simps (Named_Theorems.get ctxt @{named_theorems cvc5_holes_simp})
       ctxt))

fun trust ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ => (
    Skip_Proof.cheat_tac ctxt))
end;
