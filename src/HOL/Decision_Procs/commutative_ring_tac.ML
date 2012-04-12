(*  Title:      HOL/Decision_Procs/commutative_ring_tac.ML
    Author:     Amine Chaieb

Tactic for solving equalities over commutative rings.
*)

signature COMMUTATIVE_RING_TAC =
sig
  val tac: Proof.context -> int -> tactic
end

structure Commutative_Ring_Tac: COMMUTATIVE_RING_TAC =
struct

(* Zero and One of the commutative ring *)
fun cring_zero T = Const (@{const_name Groups.zero}, T);
fun cring_one T = Const (@{const_name Groups.one}, T);

(* reification functions *)
(* add two polynom expressions *)
fun polT t = Type (@{type_name Commutative_Ring.pol}, [t]);
fun polexT t = Type (@{type_name Commutative_Ring.polex}, [t]);

(* pol *)
fun pol_Pc t = Const (@{const_name Commutative_Ring.pol.Pc}, t --> polT t);
fun pol_Pinj t = Const (@{const_name Commutative_Ring.pol.Pinj}, HOLogic.natT --> polT t --> polT t);
fun pol_PX t = Const (@{const_name Commutative_Ring.pol.PX}, polT t --> HOLogic.natT --> polT t --> polT t);

(* polex *)
fun polex_add t = Const (@{const_name Commutative_Ring.polex.Add}, polexT t --> polexT t --> polexT t);
fun polex_sub t = Const (@{const_name Commutative_Ring.polex.Sub}, polexT t --> polexT t --> polexT t);
fun polex_mul t = Const (@{const_name Commutative_Ring.polex.Mul}, polexT t --> polexT t --> polexT t);
fun polex_neg t = Const (@{const_name Commutative_Ring.polex.Neg}, polexT t --> polexT t);
fun polex_pol t = Const (@{const_name Commutative_Ring.polex.Pol}, polT t --> polexT t);
fun polex_pow t = Const (@{const_name Commutative_Ring.polex.Pow}, polexT t --> HOLogic.natT --> polexT t);

(* reification of polynoms : primitive cring expressions *)
fun reif_pol T vs (t as Free _) =
      let
        val one = @{term "1::nat"};
        val i = find_index (fn t' => t' = t) vs
      in if i = 0
        then pol_PX T $ (pol_Pc T $ cring_one T)
          $ one $ (pol_Pc T $ cring_zero T)
        else pol_Pinj T $ HOLogic.mk_nat i
          $ (pol_PX T $ (pol_Pc T $ cring_one T)
            $ one $ (pol_Pc T $ cring_zero T))
        end
  | reif_pol T vs t = pol_Pc T $ t;

(* reification of polynom expressions *)
fun reif_polex T vs (Const (@{const_name Groups.plus}, _) $ a $ b) =
      polex_add T $ reif_polex T vs a $ reif_polex T vs b
  | reif_polex T vs (Const (@{const_name Groups.minus}, _) $ a $ b) =
      polex_sub T $ reif_polex T vs a $ reif_polex T vs b
  | reif_polex T vs (Const (@{const_name Groups.times}, _) $ a $ b) =
      polex_mul T $ reif_polex T vs a $ reif_polex T vs b
  | reif_polex T vs (Const (@{const_name Groups.uminus}, _) $ a) =
      polex_neg T $ reif_polex T vs a
  | reif_polex T vs (Const (@{const_name Power.power}, _) $ a $ n) =
      polex_pow T $ reif_polex T vs a $ n
  | reif_polex T vs t = polex_pol T $ reif_pol T vs t;

(* reification of the equation *)
val cr_sort = @{sort "comm_ring_1"};

fun reif_eq thy (eq as Const(@{const_name HOL.eq}, Type("fun", [T, _])) $ lhs $ rhs) =
      if Sign.of_sort thy (T, cr_sort) then
        let
          val fs = Misc_Legacy.term_frees eq;
          val cvs = cterm_of thy (HOLogic.mk_list T fs);
          val clhs = cterm_of thy (reif_polex T fs lhs);
          val crhs = cterm_of thy (reif_polex T fs rhs);
          val ca = ctyp_of thy T;
        in (ca, cvs, clhs, crhs) end
      else error ("reif_eq: not an equation over " ^ Syntax.string_of_sort_global thy cr_sort)
  | reif_eq _ _ = error "reif_eq: not an equation";

(* The cring tactic *)
(* Attention: You have to make sure that no t^0 is in the goal!! *)
(* Use simply rewriting t^0 = 1 *)
val cring_simps =
  [@{thm mkPX_def}, @{thm mkPinj_def}, @{thm sub_def}, @{thm power_add},
    @{thm even_def}, @{thm pow_if}, sym OF [@{thm power_add}]];

fun tac ctxt = SUBGOAL (fn (g, i) =>
  let
    val thy = Proof_Context.theory_of ctxt;
    val cring_ss = Simplifier.simpset_of ctxt  (*FIXME really the full simpset!?*)
      addsimps cring_simps;
    val (ca, cvs, clhs, crhs) = reif_eq thy (HOLogic.dest_Trueprop g)
    val norm_eq_th =
      simplify cring_ss (instantiate' [SOME ca] [SOME clhs, SOME crhs, SOME cvs] @{thm norm_eq})
  in
    cut_tac norm_eq_th i
    THEN (simp_tac cring_ss i)
    THEN (simp_tac cring_ss i)
  end);

end;
