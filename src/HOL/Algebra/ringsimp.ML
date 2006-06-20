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
    fun filter p t = (case HOLogic.dest_Trueprop t of
        Const (p', _) $ Free (s, _) => if p = p' then [s] else []
      | _ => [])
      handle TERM _ => [];
    fun filter21 p t = (case HOLogic.dest_Trueprop t of
        Const (p', _) $ Free (s, _) $ _ => if p = p' then [s] else []
      | _ => [])
      handle TERM _ => [];
    fun filter22 p t = (case HOLogic.dest_Trueprop t of
        Const (p', _) $ _ $ Free (s, _) => if p = p' then [s] else []
      | _ => [])
      handle TERM _ => [];
    fun filter31 p t = (case HOLogic.dest_Trueprop t of
        Const (p', _) $ Free (s, _) $ _ $ _ => if p = p' then [s] else []
      | _ => [])
      handle TERM _ => [];
    fun filter32 p t = (case HOLogic.dest_Trueprop t of
        Const (p', _) $ _ $ Free (s, _) $ _ => if p = p' then [s] else []
      | _ => [])
      handle TERM _ => [];

    val prems = ProofContext.prems_of ctxt;
    val non_comm_rings = List.concat (map (filter "CRing.ring" o #prop o rep_thm) prems);
    val comm_rings = List.concat (map (filter "CRing.cring" o #prop o rep_thm) prems) @
        List.concat (map (filter "CRing.domain" o #prop o rep_thm) prems) @
        List.concat (map (filter21 "Module.module" o #prop o rep_thm) prems) @
        List.concat (map (filter21 "Module.algebra" o #prop o rep_thm) prems) @
        List.concat (map (filter22 "Module.algebra" o #prop o rep_thm) prems) @
        List.concat (map (filter "UnivPoly.UP_cring" o #prop o rep_thm) prems) @
        List.concat (map (filter "UnivPoly.UP_domain" o #prop o rep_thm) prems) @
        List.concat (map (filter31 "CRing.ring_hom_cring" o #prop o rep_thm) prems) @
        List.concat (map (filter32 "CRing.ring_hom_cring" o #prop o rep_thm) prems);
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
