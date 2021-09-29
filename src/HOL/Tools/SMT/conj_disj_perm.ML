(*  Title:      HOL/Tools/SMT/conj_disj_perm.ML
    Author:     Sascha Boehme, TU Muenchen

Tactic to prove equivalence of permutations of conjunctions and disjunctions.
*)

signature CONJ_DISJ_PERM =
sig
  val conj_disj_perm_tac: Proof.context -> int -> tactic
end

structure Conj_Disj_Perm: CONJ_DISJ_PERM =
struct

fun with_assumption ct f =
  let val ct' = Thm.apply \<^cterm>\<open>HOL.Trueprop\<close> ct
  in Thm.implies_intr ct' (f (Thm.assume ct')) end

fun eq_from_impls thm1 thm2 = thm2 INCR_COMP (thm1 INCR_COMP @{thm iffI})

fun add_lit thm = Termtab.update (HOLogic.dest_Trueprop (Thm.prop_of thm), thm)

val ndisj1_rule = @{lemma "\<not>(P \<or> Q) \<Longrightarrow> \<not>P" by auto}
val ndisj2_rule = @{lemma "\<not>(P \<or> Q) \<Longrightarrow> \<not>Q" by auto}

fun explode_thm thm =
  (case HOLogic.dest_Trueprop (Thm.prop_of thm) of
    \<^Const_>\<open>conj for _ _\<close> => explode_conj_thm @{thm conjunct1} @{thm conjunct2} thm
  | \<^Const_>\<open>Not for \<^Const_>\<open>disj for _ _\<close>\<close> => explode_conj_thm ndisj1_rule ndisj2_rule thm
  | \<^Const_>\<open>Not for \<^Const_>\<open>Not for _\<close>\<close> => explode_thm (thm RS @{thm notnotD})
  | _ => add_lit thm)

and explode_conj_thm rule1 rule2 thm lits =
  explode_thm (thm RS rule1) (explode_thm (thm RS rule2) (add_lit thm lits))

val not_false_rule = @{lemma "\<not>False" by auto}
fun explode thm = explode_thm thm (add_lit not_false_rule (add_lit @{thm TrueI} Termtab.empty))

fun find_dual_lit lits (\<^Const_>\<open>Not for t\<close>, thm) = Termtab.lookup lits t |> Option.map (pair thm)
  | find_dual_lit _ _ = NONE

fun find_dual_lits lits = Termtab.get_first (find_dual_lit lits) lits

val not_not_rule = @{lemma "P \<Longrightarrow> \<not>\<not>P" by auto}
val ndisj_rule = @{lemma "\<not>P \<Longrightarrow> \<not>Q \<Longrightarrow> \<not>(P \<or> Q)" by auto}

fun join lits t =
  (case Termtab.lookup lits t of
    SOME thm => thm
  | NONE => join_term lits t)

and join_term lits \<^Const_>\<open>conj for t u\<close> = @{thm conjI} OF (map (join lits) [t, u])
  | join_term lits \<^Const_>\<open>Not for \<^Const_>\<open>HOL.disj for t u\<close>\<close> =
      ndisj_rule OF (map (join lits o HOLogic.mk_not) [t, u])
  | join_term lits \<^Const_>\<open>Not for \<^Const>\<open>Not for t\<close>\<close> = join lits t RS not_not_rule
  | join_term _ t = raise TERM ("join_term", [t])

fun prove_conj_disj_imp ct cu = with_assumption ct (fn thm => join (explode thm) (Thm.term_of cu))

fun prove_conj_disj_eq (clhs, crhs) =
  let
    val thm1 = prove_conj_disj_imp clhs crhs
    val thm2 = prove_conj_disj_imp crhs clhs
  in eq_from_impls thm1 thm2 end

val not_not_false_rule = @{lemma "\<not>\<not>False \<Longrightarrow> P" by auto}
val not_true_rule = @{lemma "\<not>True \<Longrightarrow> P" by auto}

fun prove_any_imp ct =
  (case Thm.term_of ct of
    \<^Const_>\<open>False\<close> => @{thm FalseE}
  | \<^Const_>\<open>Not for \<^Const>\<open>Not for \<^Const>\<open>False\<close>\<close>\<close> => not_not_false_rule
  | \<^Const_>\<open>Not for \<^Const>\<open>True\<close>\<close> => not_true_rule
  | _ => raise CTERM ("prove_any_imp", [ct]))

fun prove_contradiction_imp ct =
  with_assumption ct (fn thm =>
    let val lits = explode thm
    in
      (case Termtab.lookup lits \<^Const>\<open>False\<close> of
        SOME thm' => thm' RS @{thm FalseE}
      | NONE =>
          (case Termtab.lookup lits \<^Const>\<open>Not for \<^Const>\<open>True\<close>\<close> of
            SOME thm' => thm' RS not_true_rule
          | NONE =>
              (case find_dual_lits lits of
                SOME (not_lit_thm, lit_thm) => @{thm notE} OF [not_lit_thm, lit_thm]
              | NONE => raise CTERM ("prove_contradiction", [ct]))))
    end)

fun prove_contradiction_eq to_right (clhs, crhs) =
  let
    val thm1 = if to_right then prove_contradiction_imp clhs else prove_any_imp clhs
    val thm2 = if to_right then prove_any_imp crhs else prove_contradiction_imp crhs
  in eq_from_impls thm1 thm2 end

val contrapos_rule = @{lemma "(\<not>P) = (\<not>Q) \<Longrightarrow> P = Q" by auto}
fun contrapos prove cp = contrapos_rule OF [prove (apply2 (Thm.apply \<^cterm>\<open>HOL.Not\<close>) cp)]

datatype kind = True | False | Conj | Disj | Other

fun choose t _ _ _ \<^Const_>\<open>True\<close> = t
  | choose _ f _ _ \<^Const_>\<open>False\<close> = f
  | choose _ _ c _ \<^Const_>\<open>conj for _ _\<close> = c
  | choose _ _ _ d \<^Const_>\<open>disj for _ _\<close> = d
  | choose _ _ _ _ _ = Other

fun kind_of \<^Const_>\<open>Not for t\<close> = choose False True Disj Conj t
  | kind_of t = choose True False Conj Disj t

fun prove_conj_disj_perm ct cp =
  (case apply2 (kind_of o Thm.term_of) cp of
    (Conj, Conj) => prove_conj_disj_eq cp
  | (Disj, Disj) => contrapos prove_conj_disj_eq cp
  | (Conj, False) => prove_contradiction_eq true cp
  | (False, Conj) => prove_contradiction_eq false cp
  | (Disj, True) => contrapos (prove_contradiction_eq true) cp
  | (True, Disj) => contrapos (prove_contradiction_eq false) cp
  | _ => raise CTERM ("prove_conj_disj_perm", [ct]))

fun conj_disj_perm_tac ctxt = CSUBGOAL (fn (ct, i) => 
  (case Thm.term_of ct of
    \<^Const_>\<open>Trueprop for \<^Const>\<open>HOL.eq \<^Type>\<open>bool\<close> for _ _\<close>\<close> =>
      resolve_tac ctxt [prove_conj_disj_perm ct (Thm.dest_binop (Thm.dest_arg ct))] i
  | _ => no_tac))

end;
