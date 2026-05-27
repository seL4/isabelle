(*  Title:      HOL/Tools/SMT/alethe/cvc5_replay_methods.ML
    Author:     Mathias Fleury, JKU, Uni Freiburg
    Author:     Hanna Lachnitt, Stanford University

Proof method for replaying cvc5 proofs.
*)

signature CVC5_REPLAY_METHODS =
sig
  (*methods for verit proof rules*)
  val method_for: string -> Proof.context -> thm list -> term list -> term list -> term ->
     Alethe_Node.tactic_args option -> thm

  val cvc5_rule_of : string -> Alethe_Replay_Methods.alethe_rule
  val choose : Context.generic ->
      Alethe_Replay_Methods.alethe_rule ->
        Proof.context ->
          thm list ->
            term list ->
              term list -> term -> tactic_args option -> thm
  val discharge: Proof.context -> thm list -> term -> thm
end;


structure CVC5_Replay_Methods: CVC5_REPLAY_METHODS =
struct

open Alethe_Replay_Methods

fun cvc5_rule_of "bind" = Bind
  | cvc5_rule_of "cong" = Cong
  | cvc5_rule_of "refl" = Refl
  | cvc5_rule_of "equiv1" = Equiv1
  | cvc5_rule_of "equiv2" = Equiv2
  | cvc5_rule_of "equiv_pos1" = Equiv_pos1
   (*Equiv_pos2 covered below*)
  | cvc5_rule_of "equiv_neg1" = Equiv_neg1
  | cvc5_rule_of "equiv_neg2" = Equiv_neg2
  | cvc5_rule_of "sko_forall" = Sko_Forall
  | cvc5_rule_of "sko_ex" = Sko_Ex
  | cvc5_rule_of "eq_reflexive" = Eq_Reflexive
  | cvc5_rule_of "forall_inst" = Forall_Inst
  | cvc5_rule_of "implies_pos" = Implies_Pos
  | cvc5_rule_of "or" = Or
  | cvc5_rule_of "not_or" = Not_Or
  | cvc5_rule_of "resolution" = Resolution
  | cvc5_rule_of "trans" = Trans
  | cvc5_rule_of "false" = False
  | cvc5_rule_of "ac_simp" = AC_Simp
  | cvc5_rule_of "aci_simp" = ACI_Simp
  | cvc5_rule_of "and" = And
  | cvc5_rule_of "not_and" = Not_And
  | cvc5_rule_of "and_pos" = And_Pos
  | cvc5_rule_of "and_neg" = And_Neg
  | cvc5_rule_of "or_pos" = Or_Pos
  | cvc5_rule_of "or_neg" = Or_Neg
  | cvc5_rule_of "not_equiv1" = Not_Equiv1
  | cvc5_rule_of "not_equiv2" = Not_Equiv2
  | cvc5_rule_of "not_implies1" = Not_Implies1
  | cvc5_rule_of "not_implies2" = Not_Implies2
  | cvc5_rule_of "xor_pos1" = Xor_Pos1
  | cvc5_rule_of "xor_pos2" = Xor_Pos2
  | cvc5_rule_of "xor_neg1" = Xor_Neg1
  | cvc5_rule_of "xor_neg2" = Xor_Neg2
  | cvc5_rule_of "xor1" = Xor1
  | cvc5_rule_of "xor2" = Xor2
  | cvc5_rule_of "not_xor1" = Not_Xor1
  | cvc5_rule_of "not_xor2" = Not_Xor2
  | cvc5_rule_of "implies_neg1" = Implies_Neg1
  | cvc5_rule_of "implies_neg2" = Implies_Neg2
  | cvc5_rule_of "implies" = Implies
  | cvc5_rule_of "bfun_elim" = Bfun_Elim
  | cvc5_rule_of "ite1" = ITE1
  | cvc5_rule_of "ite2" = ITE2
  | cvc5_rule_of "not_ite1" = Not_ITE1
  | cvc5_rule_of "not_ite2" = Not_ITE2
  | cvc5_rule_of "ite_pos1" = ITE_Pos1
  | cvc5_rule_of "ite_pos2" = ITE_Pos2
  | cvc5_rule_of "ite_neg1" = ITE_Neg1
  | cvc5_rule_of "ite_neg2" = ITE_Neg2
  | cvc5_rule_of "la_disequality" = LA_Disequality
  | cvc5_rule_of "lia_generic" = LIA_Generic
  | cvc5_rule_of "la_generic" = LA_Generic
  | cvc5_rule_of "la_tautology" = LA_Tautology
  | cvc5_rule_of "la_totality" = LA_Totality
  | cvc5_rule_of "la_rw_eq"= LA_RW_Eq
  | cvc5_rule_of "nla_generic"= NLA_Generic
  | cvc5_rule_of "la_mult_pos"= LA_Mult_Pos
  | cvc5_rule_of "la_mult_neg"= LA_Mult_Neg
  | cvc5_rule_of "poly_simp"= Poly_Simp
  | cvc5_rule_of "poly_simp_rel"= Poly_Simp_Rel
  | cvc5_rule_of "eq_transitive" = Eq_Transitive
  | cvc5_rule_of "qnt_rm_unused" = Qnt_Rm_Unused
  | cvc5_rule_of "onepoint" = Onepoint
  | cvc5_rule_of "qnt_join" = Qnt_Join
  | cvc5_rule_of "subproof" = Subproof
  | cvc5_rule_of "bool_simplify" = Bool_Simplify
  | cvc5_rule_of "or_simplify" = Or_Simplify
  | cvc5_rule_of "ite_simplify" = ITE_Simplify
  | cvc5_rule_of "and_simplify" = And_Simplify
  | cvc5_rule_of "not_simplify" = Not_Simplify
  | cvc5_rule_of "equiv_simplify" = Equiv_Simplify
  | cvc5_rule_of "eq_simplify" = Eq_Simplify
  | cvc5_rule_of "implies_simplify" = Implies_Simplify
  | cvc5_rule_of "connective_def" = Connective_Def
  | cvc5_rule_of "minus_simplify" = Minus_Simplify
  | cvc5_rule_of "sum_simplify" = Sum_Simplify
  | cvc5_rule_of "prod_simplify" = Prod_Simplify
  | cvc5_rule_of "div_simplify" = Div_Simplify
  | cvc5_rule_of "comp_simplify" = Comp_Simplify
  | cvc5_rule_of "qnt_simplify" = Qnt_Simplify
  | cvc5_rule_of "tautology" = Tautological_Clause
  | cvc5_rule_of "qnt_cnf" = Qnt_CNF
  | cvc5_rule_of "symm" = Symm
  | cvc5_rule_of "not_symm" = Not_Symm
  | cvc5_rule_of "reordering" = Reordering
  | cvc5_rule_of "shuffle" = Shuffle
  | cvc5_rule_of "contraction" = Contraction
  | cvc5_rule_of "miniscope_distribute" = Miniscope_Distribute
  | cvc5_rule_of "miniscope_split" = Miniscope_Split
  | cvc5_rule_of "miniscope_ITE" = Miniscope_ITE
  | cvc5_rule_of "and_intro" = And_Intro
  | cvc5_rule_of "distinct_elim" = Distinct_Elim
  | cvc5_rule_of "unary_minus_simplify" = Unary_Minus_Simplify
  | cvc5_rule_of "trust" = Trust
  | cvc5_rule_of "weakening" = Weakening
  | cvc5_rule_of r =
     if r = Alethe_Proof.normalized_input_rule then Normalized_Input
     else if r = Alethe_Proof.local_input_rule then Local_Input
     else if r = Alethe_Proof.skolem_def then Definition
     else if r = Alethe_Proof.not_not_rule then Not_Not
     else if r = Alethe_Proof.ite_intro_rule then ITE_Intro (* veriT only *)
     else if r = Alethe_Proof.eq_congruent_rule then Eq_Congruent
     else if r = Alethe_Proof.eq_congruent_pred_rule then Eq_Congruent_Pred
     else if r = Alethe_Proof.theory_resolution2_rule then Theory_Resolution2
     else if r = Alethe_Proof.th_resolution_rule then Theory_Resolution
     else if r = Alethe_Proof.equiv_pos2_rule then Equiv_pos2
     else if r = Alethe_Proof.hole orelse r = "undefined" then Hole
     else Other_Rule r

fun qnt_simplify ctxt _ t = SMT_Replay_Methods.prove ctxt t (fn _ =>
      K (Clasimp.auto_tac ctxt))


(* Mapping rules to tactics and hide away not needed arguments *)

(*arguments are: ctxt thms/prems step_args context_assignment t/goal args*)
fun ignore_args       f ctxt prems _ _ goal _ = f ctxt prems goal
fun include_step_args f ctxt prems step_args _ goal _ = f ctxt prems step_args goal
fun include_context_ass f ctxt prems _ context_ass goal _ = f ctxt prems context_ass goal
fun include_args f ctxt prems _ _ goal args = f ctxt prems goal args
fun include_step_and_tactic_args f ctxt prems step_args _ goal args = f ctxt prems step_args goal args


fun choose _ And = include_args and_rule
  | choose _ And_Neg = ignore_args and_neg_rule
  | choose _ And_Pos = include_args and_pos
  | choose _ And_Simplify = ignore_args rewrite_and_simplify
  | choose _ Bind = include_context_ass bind
  | choose _ Bool_Simplify = ignore_args rewrite_bool_simplify
  | choose _ Comp_Simplify = ignore_args rewrite_comp_simplify
  | choose _ Cong = include_args equality_ordered_cong
  | choose _ Connective_Def = ignore_args rewrite_connective_def
  | choose _ Distinct_Elim = ignore_args distinct_elim
  | choose _ Eq_Congruent = ignore_args eq_congruent
  | choose _ Eq_Congruent_Pred = ignore_args eq_congruent_pred
  | choose _ Eq_Reflexive = ignore_args eq_reflexive
  | choose _ Eq_Simplify = ignore_args rewrite_eq_simplify
  | choose _ Eq_Transitive = ignore_args eq_transitive
  | choose _ Equiv1 = ignore_args equiv1
  | choose _ Equiv2 = ignore_args equiv2
  | choose _ Equiv_neg1 = ignore_args equiv_neg1
  | choose _ Equiv_neg2 = ignore_args equiv_neg2
  | choose _ Equiv_pos1 = ignore_args equiv_pos1
  | choose _ Equiv_pos2 = ignore_args equiv_pos2
  | choose _ Equiv_Simplify = ignore_args rewrite_equiv_simplify
  | choose _ False = ignore_args false_rule
  | choose _ Forall_Inst = include_args forall_inst
  | choose _ Implies = ignore_args implies_rules
  | choose _ Implies_Neg1 = ignore_args implies_neg1
  | choose _ Implies_Neg2 = ignore_args implies_neg2
  | choose _ Implies_Pos = ignore_args implies_pos
  | choose _ Implies_Simplify = ignore_args rewrite_implies_simplify
  | choose _ ITE1 = ignore_args ite1
  | choose _ ITE2 = ignore_args ite2
  | choose _ ITE_Intro = ignore_args ite_intro
  | choose _ ITE_Neg1 = ignore_args ite_neg1
  | choose _ ITE_Neg2 = ignore_args ite_neg2
  | choose _ ITE_Pos1 = ignore_args ite_pos1
  | choose _ ITE_Pos2 = ignore_args ite_pos2
  | choose _ ITE_Simplify = ignore_args rewrite_ite_simplify
  | choose _ LA_Disequality = ignore_args la_disequality
  | choose _ LA_Generic = include_args la_generic
  | choose _ LA_RW_Eq = ignore_args la_rw_eq
  | choose _ LA_Tautology = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose _ LA_Totality = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose _ LIA_Generic = ignore_args lia_generic
  | choose _ LA_Mult_Pos = ignore_args la_mult_pos
  | choose _ LA_Mult_Neg = ignore_args la_mult_neg
  | choose _ Poly_Simp = ignore_args poly_simp
  | choose _ Poly_Simp_Rel = ignore_args poly_simp_rel
  | choose _ Local_Input = include_args refl
  | choose _ Minus_Simplify = ignore_args rewrite_minus_simplify
  | choose _ NLA_Generic = ignore_args SMT_Replay_Methods.arith_th_lemma_wo_shallow
  | choose _ Normalized_Input = include_args normalized_input
  | choose _ Not_And = ignore_args not_and_rule
  | choose _ Not_Equiv1 = ignore_args not_equiv1
  | choose _ Not_Equiv2 = ignore_args not_equiv2
  | choose _ Xor_Pos1 = ignore_args xor_pos1
  | choose _ Xor_Pos2 = ignore_args xor_pos2
  | choose _ Xor_Neg1 = ignore_args xor_neg1
  | choose _ Xor_Neg2 = ignore_args xor_neg2
  | choose _ Xor1 = ignore_args xor1
  | choose _ Xor2 = ignore_args xor2
  | choose _ Not_Xor1 = ignore_args not_xor1
  | choose _ Not_Xor2 = ignore_args not_xor2
  | choose _ Not_Implies1 = ignore_args not_implies1
  | choose _ Not_Implies2 = ignore_args not_implies2
  | choose _ Not_ITE1 = ignore_args not_ite1
  | choose _ Not_ITE2 = ignore_args not_ite2
  | choose _ Not_Not = ignore_args not_not
  | choose _ Not_Or = include_args not_or_rule
  | choose _ Not_Simplify = ignore_args rewrite_not_simplify
  | choose _ Or = ignore_args or
  | choose _ Or_Neg = include_args or_neg_rule
  | choose _ Or_Pos = ignore_args or_pos_rule
  | choose _ Or_Simplify = ignore_args rewrite_or_simplify
  | choose _ Theory_Resolution2 = ignore_args theory_resolution2
  | choose _ Prod_Simplify = ignore_args prod_simplify
  | choose _ Div_Simplify = ignore_args div_simplify
  | choose _ Qnt_Join = ignore_args qnt_join
  | choose _ Qnt_Rm_Unused = ignore_args qnt_rm_unused
  | choose _ Onepoint = ignore_args onepoint
  | choose _ Qnt_Simplify = ignore_args qnt_simplify
  | choose _ Refl = include_args refl
  | choose _ Resolution = ignore_args unit_res
  | choose _ Sko_Ex = ignore_args sko_ex
  | choose _ Sko_Forall = ignore_args sko_forall
  | choose _ Subproof = ignore_args ordered_subproof
  | choose _ Sum_Simplify = ignore_args sum_simplify
  | choose _ Tautological_Clause = ignore_args tautological_clause
  | choose _ Theory_Resolution = ignore_args unit_res
  | choose _ AC_Simp = ignore_args AC_rule
  | choose _ ACI_Simp = ignore_args ACI_rule
  | choose _ Bfun_Elim = ignore_args bfun_elim
  | choose _ Qnt_CNF = ignore_args qnt_cnf
  | choose _ Trans = ignore_args strict_trans
  | choose _ Symm = ignore_args symm
  | choose _ Not_Symm = ignore_args not_symm
  | choose _ Reordering = ignore_args reordering
  | choose _ Shuffle = include_step_and_tactic_args shuffle
  | choose _ Contraction = ignore_args contraction
  | choose _ Miniscope_Distribute = ignore_args miniscope_distribute
  | choose _ Miniscope_Split = ignore_args miniscope_split
  | choose _ Miniscope_ITE = ignore_args miniscope_ITE
  | choose _ And_Intro = ignore_args and_intro
  | choose _ Unary_Minus_Simplify = ignore_args rewrite_minus_simplify
  | choose _ Trust = ignore_args trust
  | choose _ Weakening = ignore_args weakening
  | choose ctxt (Other_Rule r) =
    (case get_alethe_tac r ctxt of
      NONE => ignore_args hole(*unsupported (string_of_alethe_rule x)*)
    | SOME a => include_step_args a)
  | choose _ Hole = ignore_args hole
  | choose _ RARE_Rewrite = ignore_args rare_rewrite
  | choose _ Evaluate = ignore_args evaluate
  | choose _ r = (@{print} ("unknown rule, using hole", r); ignore_args hole)
(*unsupported (string_of_alethe_rule r)*)

fun with_tracing rule method ctxt prems step_args context_assignment t args =
  let val _ = SMT_Replay_Methods.trace_goal ctxt rule prems step_args t
  in method ctxt prems step_args context_assignment t args end

fun method_for rule ctxt = with_tracing rule (choose (Context.Proof ctxt) (cvc5_rule_of rule)) ctxt

fun discharge ctxt [thm] t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
    resolve_tac ctxt [thm] THEN_ALL_NEW (resolve_tac ctxt @{thms refl}))

end;
