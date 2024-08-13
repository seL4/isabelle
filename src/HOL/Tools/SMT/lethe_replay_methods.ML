(*  Title:      HOL/Tools/SMT/lethe_replay_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg

Proof method for replaying veriT proofs.
*)

signature LETHE_REPLAY_METHODS =
sig


  datatype verit_rule =
     False | True |

     (*input: a repeated (normalized) assumption of  assumption of in a subproof*)
     Normalized_Input | Local_Input |
     (*Subproof:*)
     Subproof |
     (*Conjunction:*)
     And | Not_And | And_Pos | And_Neg |
     (*Disjunction""*)
     Or | Or_Pos | Not_Or | Or_Neg |
     (*Disjunction:*)
     Implies | Implies_Neg1 | Implies_Neg2 | Implies_Pos | Not_Implies1 | Not_Implies2 |
     (*Equivalence:*)
     Equiv_neg1 | Equiv_pos1 | Equiv_pos2 | Equiv_neg2 | Not_Equiv1 | Not_Equiv2 | Equiv1 | Equiv2 |
     (*If-then-else:*)
     ITE_Pos1 | ITE_Pos2 | ITE_Neg1 | ITE_Neg2 | Not_ITE1 | Not_ITE2 | ITE_Intro | ITE1 | ITE2 |
     (*Equality:*)
     Eq_Congruent | Eq_Reflexive | Eq_Transitive | Eq_Congruent_Pred | Trans |  Refl |  Cong |
     (*Arithmetics:*)
     LA_Disequality | LA_Generic | LA_Tautology |  LIA_Generic | LA_Totality | LA_RW_Eq |
     NLA_Generic |
     (*Quantifiers:*)
     Forall_Inst | Qnt_Rm_Unused | Qnt_Join | Onepoint | Bind | Skolem_Forall | Skolem_Ex |
     (*Resolution:*)
     Theory_Resolution | Resolution |
     (*Temporary rules, that the verit developers want to remove:*)
     AC_Simp |
     Bfun_Elim |
     Qnt_CNF |
     (*Used to introduce skolem constants*)
     Definition |
     (*Former cong rules*)
     Bool_Simplify | Or_Simplify | Not_Simplify | And_Simplify | Equiv_Simplify |
     Implies_Simplify | Connective_Def | Minus_Simplify | Comp_Simplify |
     Eq_Simplify | ITE_Simplify | Sum_Simplify | Prod_Simplify | All_Simplify |
     Qnt_Simplify | Not_Not | Tautological_Clause | Duplicate_Literals |
     (*Unsupported rule*)
     Unsupported |
     (*For compression*)
     Theory_Resolution2 |
     (*Extended rules*)
     Symm | Not_Symm | Reordering | Tmp_Quantifier_Simplify |
     (*CVC5 to support new rules declared later (like BV rules)*)
     Other_Rule of string |
     Hole

  val requires_subproof_assms : string list -> string -> bool
  val requires_local_input: string list -> string -> bool

  val string_of_verit_rule: verit_rule -> string

  type lethe_tac_args = Proof.context -> thm list -> term list -> term -> thm
  type lethe_tac = Proof.context -> thm list -> term -> thm
  type lethe_tac2 = Proof.context -> thm list -> term list -> term Symtab.table -> term -> thm
  val bind: lethe_tac_args
  val and_rule: lethe_tac
  val and_neg_rule: lethe_tac
  val and_pos: lethe_tac
  val rewrite_and_simplify: lethe_tac
  val rewrite_bool_simplify: lethe_tac
  val rewrite_comp_simplify: lethe_tac
  val rewrite_minus_simplify: lethe_tac
  val rewrite_not_simplify: lethe_tac
  val rewrite_eq_simplify: lethe_tac
  val rewrite_equiv_simplify: lethe_tac
  val rewrite_implies_simplify: lethe_tac
  val rewrite_or_simplify: lethe_tac
  val cong: string -> lethe_tac
  val rewrite_connective_def: lethe_tac
  val duplicate_literals: lethe_tac
  val eq_congruent: lethe_tac
  val eq_congruent_pred: lethe_tac
  val eq_reflexive: lethe_tac
  val eq_transitive: lethe_tac
  val equiv1: lethe_tac
  val equiv2: lethe_tac
  val equiv_neg1: lethe_tac
  val equiv_neg2: lethe_tac
  val equiv_pos1: lethe_tac
  val equiv_pos2: lethe_tac
  val false_rule: lethe_tac
  val forall_inst: lethe_tac2
  val implies_rules: lethe_tac
  val implies_neg1: lethe_tac
  val implies_neg2: lethe_tac
  val implies_pos: lethe_tac
  val ite1: lethe_tac
  val ite2: lethe_tac
  val ite_intro: lethe_tac
  val ite_neg1: lethe_tac
  val ite_neg2: lethe_tac
  val ite_pos1: lethe_tac
  val ite_pos2: lethe_tac
  val rewrite_ite_simplify: lethe_tac
  val la_disequality: lethe_tac
  val la_generic: lethe_tac_args
  val la_rw_eq: lethe_tac
  val lia_generic: lethe_tac
  val refl: string -> lethe_tac
  val normalized_input: lethe_tac
  val not_and_rule: lethe_tac
  val not_equiv1: lethe_tac
  val not_equiv2: lethe_tac
  val not_implies1: lethe_tac
  val not_implies2: lethe_tac
  val not_ite1: lethe_tac
  val not_ite2: lethe_tac
  val not_not: lethe_tac
  val not_or_rule: lethe_tac
  val or: lethe_tac
  val or_neg_rule: lethe_tac
  val or_pos_rule: lethe_tac
  val theory_resolution2: lethe_tac
  val prod_simplify: lethe_tac
  val qnt_join: lethe_tac
  val qnt_rm_unused: lethe_tac
  val onepoint: lethe_tac
  val qnt_simplify: lethe_tac
  val all_simplify: lethe_tac
  val unit_res: lethe_tac
  val skolem_ex: lethe_tac
  val skolem_forall: lethe_tac
  val subproof: lethe_tac
  val sum_simplify: lethe_tac
  val tautological_clause: lethe_tac
  val tmp_AC_rule: lethe_tac
  val bfun_elim: lethe_tac
  val qnt_cnf: lethe_tac
  val trans: lethe_tac
  val symm: lethe_tac
  val not_symm: lethe_tac
  val reordering: lethe_tac


  (*Extension to declare new alethe rules*)
  val declare_alethe_rule:  string -> lethe_tac_args -> Context.generic -> Context.generic
  val rm_alethe_rule: string -> Context.generic -> Context.generic
  val get_alethe_tac: string -> Context.generic -> lethe_tac_args option
  val print_alethe_tac: Context.generic -> Pretty.T

  (*Useful lifting of tactics*)
  val REPEAT_CHANGED: ('a -> tactic) -> 'a -> tactic
  val TRY': ('a -> tactic) -> 'a -> tactic

  val simplify_tac: Proof.context -> thm list -> int -> tactic
  val replay_error: Proof.context -> string -> verit_rule -> thm list -> term -> 'a

end;


structure Lethe_Replay_Methods: LETHE_REPLAY_METHODS =
struct

type lethe_tac_args = Proof.context -> thm list -> term list -> term -> thm
type lethe_tac = Proof.context -> thm list -> term -> thm
type lethe_tac2 = Proof.context -> thm list -> term list -> term Symtab.table -> term -> thm

(*Some general comments on the proof format:
  1. Double negations are not always removed. This means for example that the equivalence rules
     cannot assume that the double negations have already been removed. Therefore, we match the
     term, instantiate the theorem, then use simp (to remove double negations), and finally use
     assumption.
  2. The reconstruction for rule forall_inst is buggy and tends to be very fragile, because the rule
     is doing much more that is supposed to do. Moreover types can make trivial goals (for the
     boolean structure) impossible to prove.
  3. Duplicate literals are sometimes removed, mostly by the SAT solver.

  Rules unsupported on purpose:
    * Distinct_Elim, XOR, let (we don't need them).
    * deep_skolemize (because it is not clear if verit still generates using it).
*)


datatype verit_rule =
   False | True |

   (*input: a repeated (normalized) assumption of  assumption of in a subproof*)
   Normalized_Input | Local_Input |
   (*Subproof:*)
   Subproof |
   (*Conjunction:*)
   And | Not_And | And_Pos | And_Neg |
   (*Disjunction""*)
   Or | Or_Pos | Not_Or | Or_Neg |
   (*Disjunction:*)
   Implies | Implies_Neg1 | Implies_Neg2 | Implies_Pos | Not_Implies1 | Not_Implies2 |
   (*Equivalence:*)
   Equiv_neg1 | Equiv_pos1 | Equiv_pos2 | Equiv_neg2 | Not_Equiv1 | Not_Equiv2 | Equiv1 | Equiv2 |
   (*If-then-else:*)
   ITE_Pos1 | ITE_Pos2 | ITE_Neg1 | ITE_Neg2 | Not_ITE1 | Not_ITE2 | ITE_Intro | ITE1 | ITE2 |
   (*Equality:*)
   Eq_Congruent | Eq_Reflexive | Eq_Transitive | Eq_Congruent_Pred | Trans |  Refl |  Cong |
   (*Arithmetics:*)
   LA_Disequality | LA_Generic | LA_Tautology |  LIA_Generic | LA_Totality | LA_RW_Eq |
   NLA_Generic |
   (*Quantifiers:*)
   Forall_Inst | Qnt_Rm_Unused | Qnt_Join | Onepoint | Bind | Skolem_Forall | Skolem_Ex |
   (*Resolution:*)
   Theory_Resolution | Resolution |
   (*Temporary rules, that the verit developpers want to remove:*)
   AC_Simp |
   Bfun_Elim |
   Qnt_CNF |
   (*Used to introduce skolem constants*)
   Definition |
   (*Former cong rules*)
   Bool_Simplify | Or_Simplify | Not_Simplify | And_Simplify | Equiv_Simplify |
   Implies_Simplify | Connective_Def | Minus_Simplify | Comp_Simplify |
   Eq_Simplify | ITE_Simplify | Sum_Simplify | Prod_Simplify | All_Simplify |
   Qnt_Simplify | Not_Not | Tautological_Clause | Duplicate_Literals |
   (*Unsupported rule*)
   Unsupported |
   (*For compression*)
   Theory_Resolution2 |
   (*Extended rules*)
   Symm | Not_Symm | Reordering | Tmp_Quantifier_Simplify |
   (*CVC5*)
   Other_Rule of string |
   Hole

fun string_of_verit_rule Bind = "Bind"
  | string_of_verit_rule Cong = "Cong"
  | string_of_verit_rule Refl = "Refl"
  | string_of_verit_rule Equiv1 = "Equiv1"
  | string_of_verit_rule Equiv2 = "Equiv2"
  | string_of_verit_rule Equiv_pos1 = "Equiv_pos1"
  | string_of_verit_rule Equiv_pos2 = "Equiv_pos2"
  | string_of_verit_rule Equiv_neg1 = "Equiv_neg1"
  | string_of_verit_rule Equiv_neg2 = "Equiv_neg2"
  | string_of_verit_rule Skolem_Forall = "Skolem_Forall"
  | string_of_verit_rule Skolem_Ex = "Skolem_Ex"
  | string_of_verit_rule Eq_Reflexive = "Eq_Reflexive"
  | string_of_verit_rule Theory_Resolution = "Theory_Resolution"
  | string_of_verit_rule Theory_Resolution2 = "Theory_Resolution2"
  | string_of_verit_rule Forall_Inst = "forall_inst"
  | string_of_verit_rule Or = "Or"
  | string_of_verit_rule Not_Or = "Not_Or"
  | string_of_verit_rule Resolution = "Resolution"
  | string_of_verit_rule Eq_Congruent = "eq_congruent"
  | string_of_verit_rule Trans = "trans"
  | string_of_verit_rule False = "false"
  | string_of_verit_rule And = "and"
  | string_of_verit_rule And_Pos = "and_pos"
  | string_of_verit_rule Not_And = "not_and"
  | string_of_verit_rule And_Neg = "and_neg"
  | string_of_verit_rule Or_Pos = "or_pos"
  | string_of_verit_rule Or_Neg = "or_neg"
  | string_of_verit_rule AC_Simp = "ac_simp"
  | string_of_verit_rule Not_Equiv1 = "not_equiv1"
  | string_of_verit_rule Not_Equiv2 = "not_equiv2"
  | string_of_verit_rule Not_Implies1 = "not_implies1"
  | string_of_verit_rule Not_Implies2 = "not_implies2"
  | string_of_verit_rule Implies_Neg1 = "implies_neg1"
  | string_of_verit_rule Implies_Neg2 = "implies_neg2"
  | string_of_verit_rule Implies = "implies"
  | string_of_verit_rule Bfun_Elim = "bfun_elim"
  | string_of_verit_rule ITE1 = "ite1"
  | string_of_verit_rule ITE2 = "ite2"
  | string_of_verit_rule Not_ITE1 = "not_ite1"
  | string_of_verit_rule Not_ITE2 = "not_ite2"
  | string_of_verit_rule ITE_Pos1 = "ite_pos1"
  | string_of_verit_rule ITE_Pos2 = "ite_pos2"
  | string_of_verit_rule ITE_Neg1 = "ite_neg1"
  | string_of_verit_rule ITE_Neg2 = "ite_neg2"
  | string_of_verit_rule ITE_Intro = "ite_intro"
  | string_of_verit_rule LA_Disequality = "la_disequality"
  | string_of_verit_rule LA_Generic = "la_generic"
  | string_of_verit_rule LIA_Generic = "lia_generic"
  | string_of_verit_rule LA_Tautology = "la_tautology"
  | string_of_verit_rule LA_RW_Eq = "la_rw_eq"
  | string_of_verit_rule LA_Totality = "LA_Totality"
  | string_of_verit_rule NLA_Generic = "nla_generic"
  | string_of_verit_rule Eq_Transitive = "eq_transitive"
  | string_of_verit_rule Qnt_Rm_Unused = "qnt_remove_unused"
  | string_of_verit_rule Onepoint = "onepoint"
  | string_of_verit_rule Qnt_Join = "qnt_join"
  | string_of_verit_rule Eq_Congruent_Pred = "eq_congruent_pred"
  | string_of_verit_rule Normalized_Input = Lethe_Proof.normalized_input_rule
  | string_of_verit_rule Local_Input = Lethe_Proof.local_input_rule
  | string_of_verit_rule Subproof = "subproof"
  | string_of_verit_rule Bool_Simplify = "bool_simplify"
  | string_of_verit_rule Equiv_Simplify = "equiv_simplify"
  | string_of_verit_rule Eq_Simplify = "eq_simplify"
  | string_of_verit_rule Not_Simplify = "not_simplify"
  | string_of_verit_rule And_Simplify = "and_simplify"
  | string_of_verit_rule Or_Simplify = "or_simplify"
  | string_of_verit_rule ITE_Simplify = "ite_simplify"
  | string_of_verit_rule Implies_Simplify = "implies_simplify"
  | string_of_verit_rule Connective_Def = "connective_def"
  | string_of_verit_rule Minus_Simplify = "minus_simplify"
  | string_of_verit_rule Sum_Simplify = "sum_simplify"
  | string_of_verit_rule Prod_Simplify = "prod_simplify"
  | string_of_verit_rule All_Simplify = "all_simplify"
  | string_of_verit_rule Comp_Simplify = "comp_simplify"
  | string_of_verit_rule Qnt_Simplify = "qnt_simplify"
  | string_of_verit_rule Symm = "symm"
  | string_of_verit_rule Not_Symm = "not_symm"
  | string_of_verit_rule Reordering = "reordering"
  | string_of_verit_rule Not_Not = Lethe_Proof.not_not_rule
  | string_of_verit_rule Tautological_Clause = "tautology"
  | string_of_verit_rule Duplicate_Literals = Lethe_Proof.contract_rule
  | string_of_verit_rule Qnt_CNF = "qnt_cnf"
  | string_of_verit_rule (Other_Rule r) = r
  | string_of_verit_rule r = "Unknown rule: " ^ \<^make_string> r

(** Context Extension for Rules **)
(*We currently do not distinguish between the extension required for each solver. Maybe later
it will be needed.*)
type alethe_rule_ext = {rules: (string * lethe_tac_args) list}

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
(**)
fun replay_error ctxt msg rule thms t =
  SMT_Replay_Methods.replay_error ctxt msg (string_of_verit_rule rule) thms t

(* utility function *)

fun eqsubst_all ctxt thms =
   K ((REPEAT o HEADGOAL) (EqSubst.eqsubst_asm_tac ctxt [0] thms))
   THEN' K ((REPEAT o HEADGOAL) (EqSubst.eqsubst_tac ctxt [0] thms))

fun simplify_tac ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
  |> Simplifier.asm_full_simp_tac

(* sko_forall requires the assumptions to be able to prove the equivalence in case of double
skolemization. See comment below. *)
fun requires_subproof_assms _ t =
  member (op =) ["refl", "sko_forall", "sko_ex", "cong"] t

fun requires_local_input _ t =
  member (op =) [Lethe_Proof.local_input_rule] t

(*This is a weaker simplification form. It is weaker, but is also less likely to loop*)
fun partial_simplify_tac ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
  |> Simplifier.full_simp_tac

val try_provers = SMT_Replay_Methods.try_provers

fun TRY' tac = fn i => TRY (tac i)
fun REPEAT' tac = fn i => REPEAT (tac i)
fun REPEAT_CHANGED tac = fn i => REPEAT (CHANGED (tac i))


(* Bind *)

(*The bind rule is non-obvious due to the handling of quantifiers:
  "\<And>x y a. x = y ==> (\<forall>b. P a b x) \<longleftrightarrow> (\<forall>b. P' a b y)"
  ------------------------------------------------------
            \<forall>a. (\<forall>b x. P a b x) \<longleftrightarrow> (\<forall>b y. P' a b y)
is a valid application.*)

val bind_thms =
  [@{lemma \<open>(\<And>x x'. x = x' \<Longrightarrow> P x = Q x') \<Longrightarrow> (\<forall>x. P x) = (\<forall>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x x'. x = x' \<Longrightarrow> P x = Q x') \<Longrightarrow> (\<exists>x. P x) = (\<exists>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x x'. x = x' \<Longrightarrow> P x = Q x') \<Longrightarrow> (\<exists>x. P x = Q x)\<close> by blast},
   @{lemma \<open>(\<And>x x'. x = x' \<Longrightarrow> P x = Q x') \<Longrightarrow> (\<forall>x. P x = Q x)\<close> by blast}]

val bind_thms_same_name =
  [@{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<forall>x. P x) = (\<forall>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>x. P x) = (\<exists>y. Q y)\<close> by blast},
   @{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<exists>x. P x = Q x)\<close> by blast},
   @{lemma \<open>(\<And>x. P x = Q x) \<Longrightarrow> (\<forall>x. P x = Q x)\<close> by blast}]

fun extract_quantified_names_q (_ $ Abs (name, _, t)) =
   apfst (curry (op ::) name) (extract_quantified_names_q t)
  | extract_quantified_names_q t = ([], t)

fun extract_forall_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, ty, t)) =
   (name,  ty) :: (extract_forall_quantified_names_q t)
  | extract_forall_quantified_names_q _ = []

fun extract_all_forall_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, _, t)) =
      name :: (extract_all_forall_quantified_names_q t)
  | extract_all_forall_quantified_names_q (t $ u) =
      extract_all_forall_quantified_names_q t @ extract_all_forall_quantified_names_q u
  | extract_all_forall_quantified_names_q _ = []

val extract_quantified_names_ba =
  SMT_Replay_Methods.dest_prop
  #> extract_quantified_names_q
  ##> HOLogic.dest_eq
  ##> fst
  ##> extract_quantified_names_q
  ##> fst

val extract_quantified_names =
  extract_quantified_names_ba
  #> (op @)

val extract_all_forall_quantified_names =
  SMT_Replay_Methods.dest_prop
  #> HOLogic.dest_eq
  #> fst
  #> extract_all_forall_quantified_names_q


fun extract_all_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs (name, _, t)) =
      name :: (extract_all_exists_quantified_names_q t)
  | extract_all_exists_quantified_names_q (t $ u) =
      extract_all_exists_quantified_names_q t @ extract_all_exists_quantified_names_q u
  | extract_all_exists_quantified_names_q _ = []

val extract_all_exists_quantified_names =
  SMT_Replay_Methods.dest_prop
  #> HOLogic.dest_eq
  #> fst
  #> extract_all_exists_quantified_names_q


fun extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs (name, _, t)) =
      name :: (extract_all_forall_exists_quantified_names_q t)
  | extract_all_forall_exists_quantified_names_q (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, _, t)) =
      name :: (extract_all_forall_exists_quantified_names_q t)
  | extract_all_forall_exists_quantified_names_q (t $ u) =
      extract_all_forall_exists_quantified_names_q t @ extract_all_forall_exists_quantified_names_q u
  | extract_all_forall_exists_quantified_names_q _ = []

val extract_bind_names =
   HOLogic.dest_eq
   #> apply2 (fn (Free (name, _)) => name)

fun combine_quant ctxt ((n1, n2) :: bounds) (n1' :: formula) =
    TRY' (if n1 = n1'
     then if n1 <> n2
       then
         resolve_tac ctxt bind_thms
         THEN' TRY'(resolve_tac ctxt [@{thm refl}])
         THEN' combine_quant ctxt bounds formula
       else resolve_tac ctxt bind_thms_same_name THEN' combine_quant ctxt bounds formula
     else resolve_tac ctxt @{thms allI} THEN' combine_quant ctxt ((n1, n2) :: bounds) formula)
  | combine_quant _ _ _ = K all_tac

fun bind_quants ctxt args t =
  combine_quant ctxt (map extract_bind_names args) (extract_quantified_names t)

fun generalize_prems_q [] prems = prems
  | generalize_prems_q (_ :: quants) prems =
      generalize_prems_q quants (@{thm spec} OF [prems])

fun generalize_prems t = generalize_prems_q (fst (extract_quantified_names_ba t))

fun bind ctxt [prems] args t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    bind_quants ctxt args t
    THEN' TRY' (SOLVED' (resolve_tac ctxt [generalize_prems t prems]
      THEN_ALL_NEW TRY' (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms refl}))))
 | bind ctxt thms _ t = replay_error ctxt "invalid bind application" Bind thms t


(* Congruence/Refl *)

fun cong name ctxt thms = try_provers name ctxt
    (string_of_verit_rule Cong) [
  ("basic", SMT_Replay_Methods.cong_basic ctxt thms),
  ("unfolding then reflexivity", SMT_Replay_Methods.cong_unfolding_trivial ctxt thms),
  ("unfolding then auto", SMT_Replay_Methods.cong_unfolding_first ctxt thms),
  ("full", SMT_Replay_Methods.cong_full ctxt thms)] thms

fun refl name ctxt thm t =
  (case find_first (fn thm => t = Thm.full_prop_of thm) thm of
      SOME thm => thm
    | NONE =>
        (case try (fn t => SMT_Replay_Methods.match_instantiate ctxt t @{thm refl}) t of
          NONE => cong name ctxt thm t
        | SOME thm => thm))

(* Instantiation *)

local
fun dropWhile _ [] = []
  | dropWhile f (x :: xs) = if f x then dropWhile f xs else x :: xs
in

fun forall_inst ctxt _ _ insts t =
  let
    fun instantiate_and_solve i ({context = ctxt, prems = [prem], ...}: Subgoal.focus) =
        let
          val t = Thm.prop_of prem
          val quants = t
            |> SMT_Replay_Methods.dest_prop
            |> extract_forall_quantified_names_q
          val insts = map (Symtab.lookup insts o fst) (rev quants)
            |> dropWhile (curry (op =) NONE)
            |> rev
          fun option_map _ NONE = NONE
            | option_map f (SOME a) = SOME (f a)
          fun instantiate_with inst prem =
            Drule.infer_instantiate' ctxt [NONE, inst] @{thm spec} OF [prem]
          val inst_thm =
            fold instantiate_with
              (map (option_map (Thm.cterm_of ctxt)) insts)
              prem
        in
           (Method.insert_tac ctxt [inst_thm]
           THEN' TRY' (fn i => assume_tac ctxt i)
           THEN' TRY' (partial_simplify_tac ctxt @{thms eq_commute ac_simps})
           THEN' TRY' (blast_tac ctxt)) i
        end
     | instantiate_and_solve _ ({context = ctxt, prems = thms, ...}: Subgoal.focus) =
         replay_error ctxt "invalid application" Forall_Inst thms t
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      match_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}]]
      THEN' (fn i => Subgoal.FOCUS (instantiate_and_solve i) ctxt i))
  end
end


(* Or *)

fun or _ (thm :: _) _ = thm
  | or ctxt thms t = replay_error ctxt "invalid bind application" Or thms t


(* Implication *)

val implies_pos_thm =
  [@{lemma \<open>\<not>(A \<longrightarrow> B) \<or> \<not>A \<or> B\<close> by blast},
  @{lemma \<open>\<not>(\<not>A \<longrightarrow> B) \<or> A \<or> B\<close> by blast}]

fun implies_pos ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt implies_pos_thm)

(* Skolemization *)
local
  fun split _ [] = ([], [])
    | split f (a :: xs) =
        split f xs
        |> (if f a then apfst (curry (op ::) a) else apsnd (curry (op ::) a))
in
fun extract_rewrite_rule_assumption _ thms =
  let
    fun is_rewrite_rule thm =
      (case Thm.prop_of thm of
        \<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ Free(_, _)) => true
      | _ => false)
    fun is_context_rule thm =
      (case Thm.prop_of thm of
        \<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Free(_, _) $ Free(_, _)) => true
      | _ => false)
    val (ctxt_eq, other) =
      thms
      |> split is_context_rule
    val (rew, other) =
      other
      |> split is_rewrite_rule
  in
    (ctxt_eq, rew, other)
  end
end
(*
Without compression, we have to rewrite skolems only once. However, it can happen than the same
skolem constant is used multiple times with a different name under the forall.

For strictness, we use the multiple rewriting only when compressing is activated.
*)
local
  fun rewrite_all_skolems thm_indirect ctxt ((v,SOME thm) :: thms) =
     let
       val rewrite_sk_thms =
         List.mapPartial (fn tm => SOME (tm OF [thm]) handle THM _ => NONE) thm_indirect
       val multiple_rew = if SMT_Config.compress_verit_proofs ctxt then REPEAT_CHANGED else fn x => x
     in
       multiple_rew (EqSubst.eqsubst_tac ctxt [0] rewrite_sk_thms
         THEN' SOLVED' (K (HEADGOAL (partial_simplify_tac ctxt (@{thms eq_commute})))))
       THEN' rewrite_all_skolems thm_indirect ctxt thms
     end
   | rewrite_all_skolems thm_indirect ctxt ((_,NONE) :: thms) = rewrite_all_skolems thm_indirect ctxt thms
   | rewrite_all_skolems _ _ [] = K (all_tac)

   fun extract_var_name (thm :: thms) =
       let val name = Thm.concl_of thm
         |> SMT_Replay_Methods.dest_prop
         |> HOLogic.dest_eq
         |> fst
         |> (fn Const(_,_) $ Abs(name, _, _) => [(name,@{thm sym} OF [thm])]
             | _ => [])
       in name :: extract_var_name thms end
    | extract_var_name [] = []

fun skolem_tac extractor thm1 thm2 ctxt thms t  =
  let
    val (ctxt_eq, ts, other) = extract_rewrite_rule_assumption ctxt thms

    fun ordered_definitions () =
      let
        val var_order = extractor t
        val thm_names_with_var = extract_var_name ts |> flat
      in map (fn v => (v, AList.lookup (op =) thm_names_with_var v)) var_order end
  in
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      K (unfold_tac ctxt ctxt_eq)
      THEN' rewrite_all_skolems thm2 ctxt (ordered_definitions ())
      THEN' (eqsubst_all ctxt (map (fn thm => thm RS sym) other))
      THEN_ALL_NEW TRY' (resolve_tac ctxt @{thms refl})
      THEN' K (unfold_tac ctxt ctxt_eq)
      THEN' TRY' (partial_simplify_tac ctxt (@{thms eq_commute})))
  end
in

val skolem_forall =
  skolem_tac extract_all_forall_exists_quantified_names_q @{thm verit_sko_forall_indirect}
    @{thms verit_sko_forall_indirect2  verit_sko_ex_indirect2}

val skolem_ex =
  skolem_tac extract_all_forall_exists_quantified_names_q @{thm verit_sko_ex_indirect}
    @{thms verit_sko_ex_indirect2 verit_sko_forall_indirect2}

end

fun eq_reflexive ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t @{thm refl}

local
  fun not_not_prove ctxt _ =
    K (unfold_tac ctxt @{thms not_not})
    THEN' match_tac ctxt @{thms verit_or_simplify_1}

  fun duplicate_literals_prove ctxt prems =
    Method.insert_tac ctxt prems
    THEN' match_tac ctxt @{thms ccontr}
    THEN' K (unfold_tac ctxt @{thms de_Morgan_disj not_not})
    THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
    THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})
    THEN' REPEAT' (ematch_tac ctxt @{thms notE} THEN' TRY' (assume_tac ctxt))

  fun tautological_clause_prove ctxt _ =
    match_tac ctxt @{thms verit_or_neg}
    THEN' K (unfold_tac ctxt @{thms not_not disj_assoc[symmetric]})
    THEN' TRY' (match_tac ctxt @{thms notE} THEN_ALL_NEW assume_tac ctxt)

  val theory_resolution2_lemma = @{lemma \<open>a \<Longrightarrow> a = b \<Longrightarrow> b\<close> by blast}

in

fun prove_abstract abstracter tac ctxt thms t =
  let
    val thms = map (Conv.fconv_rule Thm.eta_long_conversion) thms
    val t' = Thm.eta_long_conversion (Object_Logic.dest_judgment ctxt (Thm.cterm_of ctxt t))
    val (_, t2) = Logic.dest_equals (Thm.prop_of t')
    val thm =
      SMT_Replay_Methods.prove_abstract ctxt thms t2 tac (
        fold_map (abstracter o SMT_Replay_Methods.dest_thm) thms ##>>
        abstracter (SMT_Replay_Methods.dest_prop t2))
  in
    @{thm verit_Pure_trans} OF [t', thm]
  end

val not_not = prove_abstract SMT_Replay_Methods.abstract_bool_shallow not_not_prove

val tautological_clause =
  prove_abstract SMT_Replay_Methods.abstract_bool_shallow tautological_clause_prove

val duplicate_literals =
  prove_abstract SMT_Replay_Methods.abstract_bool_shallow duplicate_literals_prove

val unit_res = prove_abstract SMT_Replay_Methods.abstract_bool_shallow SMT_Replay_Methods.prop_tac

(*match_instantiate does not work*)
fun theory_resolution2 ctxt prems t =
  SMT_Replay_Methods.prove ctxt t (fn _ => match_tac ctxt [theory_resolution2_lemma OF prems])

end


fun normalized_input ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt prems
  THEN' TRY' (K (unfold_tac ctxt @{thms SMT.trigger_def}))
  THEN' TRY' (partial_simplify_tac ctxt @{thms eq_commute}))

val false_rule_thm = @{lemma \<open>\<not>False\<close> by blast}

fun false_rule ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t false_rule_thm


(* Transitivity *)

val trans_bool_thm =
  @{lemma \<open>P = Q \<Longrightarrow> Q \<Longrightarrow> P\<close> by blast}

fun trans ctxt thms t =
  let
    val prop_of = HOLogic.dest_Trueprop o Thm.full_prop_of
    fun combine_thms [thm1, thm2] =
          (case (prop_of thm1, prop_of thm2) of
            ((Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2),
             (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t3 $ t4)) =>
            if t2 aconv t3 then thm1 RSN (1, thm2 RSN (2, @{thm trans}))
            else if t2 aconv t4 then thm1 RSN ((1, ((thm2 RS sym)) RSN (2, @{thm trans})))
            else if t1 aconv t4 then thm2 RSN (1, thm1 RSN (2, @{thm trans}))
            else raise Fail "invalid trans theorem"
          | _ => trans_bool_thm OF [thm1, thm2])
      | combine_thms (thm1 :: thm2 :: thms) =
          combine_thms (combine_thms [thm1, thm2] :: thms)
      | combine_thms thms = replay_error ctxt "invalid bind application" Trans thms t
     val t' = Thm.eta_long_conversion (Object_Logic.dest_judgment ctxt (Thm.cterm_of ctxt t))
     val (_, t2) = Logic.dest_equals (Thm.prop_of t')
     val thms = map (Conv.fconv_rule Thm.eta_long_conversion) thms
     val trans_thm = combine_thms thms
  in
     (case (prop_of trans_thm, t2) of
       ((Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ _),
             (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t3 $ _)) =>
       if t1 aconv t3 then trans_thm else trans_thm RS sym
      | _ => trans_thm (*to be on the safe side*))
  end


fun tmp_AC_rule ctxt thms t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    Method.insert_tac ctxt thms
    THEN' REPEAT_ALL_NEW (partial_simplify_tac ctxt @{thms eq_commute}
    THEN' TRY' (simplify_tac ctxt @{thms ac_simps conj_ac})
    THEN' TRY' (Classical.fast_tac ctxt)))


(* And/Or *)

local
  fun not_and_rule_prove ctxt prems =
     Method.insert_tac ctxt prems
     THEN' K (unfold_tac ctxt @{thms de_Morgan_conj})
     THEN_ALL_NEW TRY' (assume_tac ctxt)

  fun or_pos_prove ctxt _ =
     K (unfold_tac ctxt @{thms de_Morgan_disj not_not})
     THEN' match_tac ctxt @{thms verit_and_pos verit_farkas}
     THEN' K (unfold_tac ctxt @{thms de_Morgan_conj de_Morgan_disj not_not})
     THEN' TRY' (assume_tac ctxt)

  fun not_or_rule_prove ctxt prems =
     Method.insert_tac ctxt prems
     THEN' K (unfold_tac ctxt @{thms de_Morgan_disj not_not})
     THEN' TRY' (REPEAT' (match_tac ctxt @{thms conjI}))
     THEN_ALL_NEW ((REPEAT' (ematch_tac ctxt @{thms conjE}))
       THEN' TRY' (assume_tac ctxt))

  fun and_rule_prove ctxt prems =
     Method.insert_tac ctxt prems
     THEN' (fn i => REPEAT (dresolve_tac ctxt @{thms conjE} i THEN assume_tac ctxt (i+1)))
     THEN' TRY' (assume_tac ctxt)

  fun and_neg_rule_prove ctxt _ =
     match_tac ctxt @{thms verit_and_neg}
     THEN' K (unfold_tac ctxt @{thms de_Morgan_conj not_not})
     THEN' TRY' (assume_tac ctxt)

  fun prover tac = prove_abstract SMT_Replay_Methods.abstract_prop tac

in

val and_rule = prover and_rule_prove

val not_and_rule = prover not_and_rule_prove

val not_or_rule = prover not_or_rule_prove

val or_pos_rule = prover or_pos_prove

val and_neg_rule = prover and_neg_rule_prove

val or_neg_rule = prove_abstract SMT_Replay_Methods.abstract_bool (fn ctxt => fn _ =>
  resolve_tac ctxt @{thms verit_or_neg}
  THEN' K (unfold_tac ctxt @{thms not_not})
  THEN_ALL_NEW
    (REPEAT'
      (SOLVED' (match_tac ctxt @{thms disjI1} THEN_ALL_NEW assume_tac ctxt)
       ORELSE' (match_tac ctxt @{thms disjI2} THEN' TRY' (assume_tac ctxt)))))

fun and_pos ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  REPEAT_CHANGED (resolve_tac ctxt @{thms verit_and_pos})
  THEN' TRY' (assume_tac ctxt))

end


(* Equivalence Transformation *)

local
  fun prove_equiv equiv_thm ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [equiv_thm OF [thm]]
        THEN' TRY' (assume_tac ctxt))
    | prove_equiv _ ctxt thms t = replay_error ctxt "invalid application in some equiv rule" Unsupported thms t
in

val not_equiv1 = prove_equiv @{lemma \<open>\<not>(A \<longleftrightarrow> B) \<Longrightarrow> A \<or> B\<close> by blast}
val not_equiv2 = prove_equiv @{lemma \<open>\<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<or> \<not>B\<close> by blast}
val equiv1  = prove_equiv @{lemma \<open>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<or> B\<close> by blast}
val equiv2 = prove_equiv @{lemma \<open>(A \<longleftrightarrow> B) \<Longrightarrow> A \<or> \<not>B\<close> by blast}
val not_implies1 = prove_equiv @{lemma \<open>\<not>(A \<longrightarrow> B) \<Longrightarrow> A\<close> by blast}
val not_implies2 = prove_equiv @{lemma \<open>\<not>(A \<longrightarrow>B) \<Longrightarrow> \<not>B\<close> by blast}

end


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


local
  fun implies_pos_neg_term ctxt thm (\<^term>\<open>Trueprop\<close> $
         (\<^term>\<open>HOL.disj\<close> $ (\<^term>\<open>HOL.implies\<close> $ a $ b) $ _)) =
         Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a, b]) thm
     | implies_pos_neg_term ctxt thm  t =
        replay_error ctxt "invalid application in Implies" Unsupported [thm] t

  fun prove_implies_pos_neg thm ctxt _ t =
    let val thm = implies_pos_neg_term ctxt thm t
    in
      SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [thm]
        THEN' TRY' (assume_tac ctxt))
    end
in

val implies_neg1_thm = @{lemma \<open>(a \<longrightarrow> b) \<or> a\<close> by blast}
val implies_neg1  = prove_implies_pos_neg implies_neg1_thm

val implies_neg2_thm = @{lemma \<open>(a \<longrightarrow> b) \<or> \<not>b\<close> by blast}
val implies_neg2 = prove_implies_pos_neg implies_neg2_thm

val implies_thm = @{lemma \<open>(a \<longrightarrow> b) \<Longrightarrow> \<not>a \<or> b\<close> by blast}
fun implies_rules ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt [implies_thm OF prems]
  THEN' TRY' (assume_tac ctxt))

end


(* BFun *)

local
  val bfun_theorems = @{thms verit_bfun_elim}
in

fun bfun_elim ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt prems
  THEN' TRY' (eqsubst_all ctxt bfun_theorems)
  THEN' TRY' (simplify_tac ctxt @{thms eq_commute all_conj_distrib ex_disj_distrib}))

end


(* If-Then-Else *)

local
  fun prove_ite ite_thm thm ctxt =
  resolve_tac ctxt [ite_thm OF [thm]]
  THEN' TRY' (assume_tac ctxt)
in

val ite_pos1_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<or> x \<or> Q\<close> by auto}

fun ite_pos1 ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  resolve_tac ctxt [ite_pos1_thm])

val ite_pos2_thms =
  @{lemma \<open>\<not>(if x then P else Q) \<or> \<not>x \<or> P\<close> \<open>\<not>(if \<not>x then P else Q) \<or> x \<or> P\<close> by auto}

fun ite_pos2 ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ => resolve_tac ctxt ite_pos2_thms)

val ite_neg1_thms =
  @{lemma \<open>(if x then P else Q) \<or> x \<or> \<not>Q\<close> \<open>(if x then P else \<not>Q) \<or> x \<or> Q\<close> by auto}

fun ite_neg1 ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ => resolve_tac ctxt ite_neg1_thms)

val ite_neg2_thms =
  @{lemma \<open>(if x then P else Q) \<or> \<not>x \<or> \<not>P\<close> \<open>(if \<not>x then P else Q) \<or> x \<or> \<not>P\<close>
          \<open>(if x then \<not>P else Q) \<or> \<not>x \<or> P\<close> \<open>(if \<not>x then \<not>P else Q) \<or> x \<or> P\<close>
      by auto}

fun ite_neg2 ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ => resolve_tac ctxt ite_neg2_thms)

val ite1_thm =
  @{lemma \<open>(if x then P else Q) \<Longrightarrow> x \<or> Q\<close> by (auto split: if_splits) }

fun ite1 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ => prove_ite ite1_thm thm ctxt)

val ite2_thm =
  @{lemma \<open>(if x then P else Q) \<Longrightarrow> \<not>x \<or> P\<close> by (auto split: if_splits) }

fun ite2 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ => prove_ite ite2_thm thm ctxt)

val not_ite1_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<Longrightarrow> x \<or> \<not>Q\<close> by (auto split: if_splits) }

fun not_ite1 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ => prove_ite not_ite1_thm thm ctxt)

val not_ite2_thm =
  @{lemma \<open>\<not>(if x then P else Q) \<Longrightarrow> \<not>x \<or> \<not>P\<close> by (auto split: if_splits) }

fun not_ite2 ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ => prove_ite not_ite2_thm thm ctxt)

(*ite_intro can introduce new terms that are in the proof exactly the sames as the old one, but are
not internally, hence the possible reordering.*)
fun ite_intro ctxt _ t =
  let
    fun simplify_ite ctxt thms =
      ctxt
      |> empty_simpset
      |> put_simpset HOL_basic_ss
      |> (fn ctxt => ctxt addsimps thms @ @{thms if_True if_False refl simp_thms if_cancel})
      |> Raw_Simplifier.add_eqcong @{thm verit_ite_if_cong}
      |> Simplifier.full_simp_tac
  in
    SMT_Replay_Methods.prove ctxt t (fn _ => simplify_ite ctxt []
       THEN' TRY' (simplify_ite ctxt @{thms eq_commute}))
  end
end


(* Quantifiers *)

local
  val rm_unused = @{lemma \<open>(\<forall>x. P) = P\<close> \<open>(\<exists>x. P) = P\<close> by blast+}

  fun qnt_cnf_tac ctxt =
    simplify_tac ctxt @{thms de_Morgan_conj de_Morgan_disj imp_conv_disj
      iff_conv_conj_imp if_bool_eq_disj ex_simps all_simps ex_disj_distrib
      verit_connective_def(3) all_conj_distrib}
    THEN' TRY' (Blast.blast_tac ctxt)
in
fun qnt_rm_unused ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  K (unfold_tac ctxt rm_unused))

fun onepoint ctxt prems t = SMT_Replay_Methods.prove ctxt t (fn _ =>
  Method.insert_tac ctxt prems
  THEN' Simplifier.full_simp_tac (put_simpset HOL_basic_ss (empty_simpset ctxt)
    addsimps @{thms HOL.simp_thms HOL.all_simps}
    |> Simplifier.add_proc @{simproc HOL.defined_All}
    |> Simplifier.add_proc @{simproc HOL.defined_Ex})
  THEN' TRY' (Blast.blast_tac ctxt)
  THEN' TRY' (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt []))

fun qnt_join ctxt _ t = SMT_Replay_Methods.prove ctxt t Classical.fast_tac

fun qnt_cnf ctxt _ t = SMT_Replay_Methods.prove ctxt t qnt_cnf_tac

fun qnt_simplify ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
      partial_simplify_tac ctxt [])

end

(* Equality *)

fun eq_transitive ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn  _ =>
  REPEAT_CHANGED (resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF @{thms impI}])
  THEN' REPEAT' (resolve_tac ctxt @{thms impI})
  THEN' REPEAT' (eresolve_tac ctxt @{thms conjI})
  THEN' REPEAT' (fn i => dresolve_tac ctxt @{thms verit_eq_transitive} i THEN assume_tac ctxt (i+1))
  THEN' resolve_tac ctxt @{thms refl})

local
  fun find_rew rews t t' =
    (case AList.lookup (op =) rews (t, t') of
      SOME thm => SOME (thm COMP @{thm symmetric})
    | NONE =>
      (case AList.lookup (op =) rews (t', t) of
        SOME thm => SOME thm
      | NONE => NONE))

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
    fun throwing_CONVERSION cv i st = Seq.single (Conv.gconv_rule cv i st)
    in
      throwing_CONVERSION (conv_term (eq_pred_conv rews t1 ctxt))
    end
in

fun eq_congruent_pred ctxt _ t =
   SMT_Replay_Methods.prove ctxt t (fn _ =>
   REPEAT' (resolve_tac ctxt [@{thm disj_not1[of \<open>_ = _\<close>]} RSN (1, @{thm iffD2}) OF @{thms impI}])
   THEN' (fn i => Subgoal.FOCUS (fn focus => eq_pred_rewrite_tac focus i) ctxt i)
   THEN' (resolve_tac ctxt @{thms refl excluded_middle excluded_middle[of \<open>\<not>_\<close>, unfolded not_not]}
     ORELSE' assume_tac ctxt))

val eq_congruent = eq_congruent_pred

end


(* Subproof *)

fun subproof ctxt [prem] t =
     SMT_Replay_Methods.prove ctxt t (fn _ =>
      (REPEAT' (resolve_tac ctxt [@{thm disj_not1} RSN (1, @{thm iffD2}) OF [@{thm impI}],
           @{thm disj_not1[of \<open>\<not>_\<close>, unfolded not_not]} RSN (1, @{thm iffD2}) OF [@{thm impI}]])
        THEN' resolve_tac ctxt [prem]
        THEN_ALL_NEW assume_tac ctxt
        THEN' TRY' (assume_tac ctxt))
      ORELSE' TRY' (Method.insert_tac ctxt [prem] THEN' Blast.blast_tac ctxt))
  | subproof ctxt prems t =
      replay_error ctxt "invalid application, only one assumption expected" Subproof prems t


(* Simplifying Steps *)

(* The reconstruction is a bit tricky: At first we only rewrite only based on the rules that are
passed as argument. Then we simply use simp_thms to reconstruct all the proofs (and these theorems
cover all the simplification below).
*)
local
  fun rewrite_only_thms ctxt thms =
    ctxt
    |> empty_simpset
    |> put_simpset HOL_basic_ss
    |> (fn ctxt => ctxt addsimps thms)
    |> Simplifier.full_simp_tac
  fun rewrite_only_thms_tmp ctxt thms =
    rewrite_only_thms ctxt thms
    THEN' TRY' (K (Clasimp.auto_tac ctxt)) (*TODO: TEMP until cvc5 produces fine grained simplification steps *)

  fun rewrite_thms ctxt thms =
    ctxt
    |> empty_simpset
    |> put_simpset HOL_basic_ss
    |> Raw_Simplifier.add_eqcong @{thm eq_reflection[OF imp_cong]}
    |> (fn ctxt => ctxt addsimps thms addsimps @{thms simp_thms})
    |> Simplifier.full_simp_tac

  fun chain_rewrite_thms ctxt thms =
    TRY' (rewrite_only_thms ctxt thms)
    THEN' TRY' (rewrite_thms ctxt thms)
    THEN' TRY' (K (Clasimp.auto_tac ctxt)) (*TODO: TEMP until cvc5 produces fine grained simplification steps *)

  fun chain_rewrite_two_step_with_ac_simps ctxt thms1 thms2 =
    TRY' (rewrite_only_thms ctxt thms1)
    THEN' TRY' (rewrite_thms ctxt thms2)
    THEN' TRY' (K (Clasimp.auto_tac ctxt)) (*TODO: TEMP until cvc5 produces fine grained simplification steps *)

  fun chain_rewrite_thms_two_step ctxt thms1 thms2 thms3 thms4 =
    chain_rewrite_two_step_with_ac_simps ctxt thms1 thms2
    THEN' TRY' (chain_rewrite_two_step_with_ac_simps ctxt thms3 thms4)

  val imp_refl = @{lemma \<open>(P \<longrightarrow> P) = True\<close> by blast}

in
fun rewrite_bool_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_thms ctxt @{thms verit_bool_simplify}))

fun rewrite_and_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt @{thms verit_and_simplify verit_and_simplify1}
     @{thms verit_and_simplify}))

fun rewrite_or_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt @{thms verit_or_simplify verit_or_simplify_1}
    @{thms verit_or_simplify})
    THEN' TRY' (REPEAT' (match_tac ctxt @{thms verit_and_pos}) THEN' assume_tac ctxt))

fun rewrite_not_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms_tmp ctxt @{thms verit_not_simplify}))

fun rewrite_equiv_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms_tmp ctxt @{thms verit_equiv_simplify}))

fun rewrite_eq_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (chain_rewrite_two_step_with_ac_simps ctxt
      @{thms verit_eq_simplify}
      (Named_Theorems.get ctxt @{named_theorems ac_simps})))

fun rewrite_implies_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    (rewrite_only_thms_tmp ctxt @{thms verit_implies_simplify}))

(* It is more efficient to first fold the implication symbols.
   That is however not enough when symbols appears within
   expressions, hence we also unfold implications in the
   other direction. *)
fun rewrite_connective_def ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      chain_rewrite_thms_two_step ctxt
        (imp_refl :: @{thms not_not verit_connective_def[symmetric]})
        (@{thms verit_connective_def[symmetric]})
        (imp_refl :: @{thms not_not verit_connective_def})
        (@{thms verit_connective_def}))

fun rewrite_minus_simplify ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
      chain_rewrite_two_step_with_ac_simps ctxt
         @{thms arith_simps verit_minus_simplify}
         (Named_Theorems.get ctxt @{named_theorems ac_simps} @
          @{thms numerals arith_simps arith_special
             numeral_class.numeral.numeral_One}))

fun rewrite_comp_simplify ctxt _ t =
    SMT_Replay_Methods.prove ctxt t (fn _ =>
        chain_rewrite_thms ctxt @{thms verit_comp_simplify})

fun rewrite_ite_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
   (rewrite_only_thms_tmp ctxt @{thms verit_ite_simplify}))
end


(* Simplifications *)

local
  fun simplify_arith ctxt thms = partial_simplify_tac ctxt
    (thms @ Named_Theorems.get ctxt @{named_theorems ac_simps} @ @{thms arith_simps})
in

fun sum_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    simplify_arith ctxt @{thms verit_sum_simplify arith_special}
    THEN' TRY' (K (Clasimp.auto_tac ctxt))) (*TODO: TEMP until cvc5 produces fine grained simplification steps *)

fun prod_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    simplify_arith ctxt @{thms verit_prod_simplify}
    THEN' TRY' (K (Clasimp.auto_tac ctxt))) (*TODO: TEMP until cvc5 produces fine grained simplification steps *)
end

fun all_simplify ctxt _ t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
     TRY' (K (Clasimp.auto_tac ctxt))) (*TODO: TEMP until cvc5 produces fine grained simplification steps *)

(* Arithmetics *)
local

val la_rw_eq_thm = @{lemma \<open>(a :: nat) = b \<or> (a \<le> b) \<or> (a \<ge> b)\<close> by auto}
in
fun la_rw_eq ctxt _ t = SMT_Replay_Methods.match_instantiate ctxt t la_rw_eq_thm

fun la_generic_prove args ctxt _ = SMT_Replay_Arith.la_farkas args ctxt

fun la_generic ctxt _ args =
  prove_abstract (SMT_Replay_Methods.abstract_arith_shallow ctxt) (la_generic_prove args) ctxt []

fun lia_generic ctxt _ t =
  SMT_Replay_Methods.prove_arith_rewrite SMT_Replay_Methods.abstract_neq ctxt t

fun la_disequality ctxt _ t =
  SMT_Replay_Methods.match_instantiate ctxt t @{thm verit_la_disequality}

end


(* Symm and Not_Symm*)

local
  fun prove_symm symm_thm ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>
        Method.insert_tac ctxt [symm_thm OF [thm]]
        THEN' TRY' (assume_tac ctxt))
    | prove_symm _  ctxt thms t = replay_error ctxt "invalid application in some symm rule" Unsupported thms t
in
  val symm_thm =
  @{lemma \<open>(B = A) \<Longrightarrow> A = B\<close> by blast }
  val symm = prove_symm symm_thm

  val not_symm_thm =
  @{lemma \<open>\<not>(B = A) \<Longrightarrow> \<not>(A = B)\<close> by blast }
  val not_symm = prove_symm not_symm_thm
end

(* Reordering *)
local
  fun prove_reordering ctxt [thm] t = SMT_Replay_Methods.prove ctxt t (fn _ =>(
      Method.insert_tac ctxt [thm]
      THEN' match_tac ctxt @{thms ccontr}
      THEN' K (unfold_tac ctxt @{thms de_Morgan_disj})
      THEN' TRY o CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
      THEN' CHANGED_PROP o REPEAT_ALL_NEW (ematch_tac ctxt @{thms disjE})
      THEN' REPEAT'(ematch_tac ctxt @{thms notE} THEN' TRY' (assume_tac ctxt))
      ))
    | prove_reordering ctxt thms t =
        replay_error ctxt "invalid application in some reordering rule" Unsupported thms t
in
  val reordering = prove_reordering
end

end;
