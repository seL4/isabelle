(*
  Title:     Normalisation method for locale cring
  Id:        $Id$
  Author:    Clemens Ballarin
  Copyright: TU Muenchen
*)

(*** Term order for commutative rings ***)

fun ring_ord a =
  find_index_eq a ["CRing.ring.zero", "CRing.ring.add", "CRing.a_inv",
  "CRing.minus", "Group.monoid.one", "Group.monoid.mult"];

fun termless_ring (a, b) = (Term.term_lpo ring_ord (a, b) = LESS);

val cring_ss = HOL_ss settermless termless_ring;

fun cring_normalise ctxt = let
    fun ring_filter t = (case HOLogic.dest_Trueprop t of
        Const ("CRing.ring_axioms", _) $ Free (s, _) => [s]
      | _ => [])
      handle TERM _ => [];
    fun comm_filter t = (case HOLogic.dest_Trueprop t of
        Const ("Group.comm_monoid_axioms", _) $ Free (s, _) => [s]
      | _ => [])
      handle TERM _ => [];

    val prems = ProofContext.prems_of ctxt;
    val rings = List.concat (map (ring_filter o #prop o rep_thm) prems);
    val comms = List.concat (map (comm_filter o #prop o rep_thm) prems);
    val non_comm_rings = rings \\ comms;
    val comm_rings = rings inter_string comms;
    val _ = tracing
      ("Non-commutative rings in proof context: " ^ commas non_comm_rings ^
       "\nCommutative rings in proof context: " ^ commas comm_rings);
    val simps =
      List.concat (map (fn s => ProofContext.get_thms ctxt (Name (s ^ ".ring_simprules")))
        non_comm_rings) @
      List.concat (map (fn s => ProofContext.get_thms ctxt (Name (s ^ ".cring_simprules")))
        comm_rings);
  in Method.SIMPLE_METHOD' HEADGOAL (asm_full_simp_tac (cring_ss addsimps simps))
  end;

(*
val ring_ss = HOL_basic_ss settermless termless_ring addsimps
  [a_assoc, l_zero, l_neg, a_comm, m_assoc, l_one, l_distr, m_comm, minus_def,
   r_zero, r_neg, r_neg2, r_neg1, minus_add, minus_minus, minus0,
   a_lcomm, m_lcomm, (*r_one,*) r_distr, l_null, r_null, l_minus, r_minus];
*)
