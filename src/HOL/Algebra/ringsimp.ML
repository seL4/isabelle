(*
  Title:     Normalisation method for locale cring
  Id:        $Id$
  Author:    Clemens Ballarin
  Copyright: TU Muenchen
*)

local

(*** Lexicographic path order on terms.

  See Baader & Nipkow, Term rewriting, CUP 1998.
  Without variables.  Const, Var, Bound, Free and Abs are treated all as
  constants.

  f_ord maps strings to integers and serves two purposes:
  - Predicate on constant symbols.  Those that are not recognised by f_ord
    must be mapped to ~1.
  - Order on the recognised symbols.  These must be mapped to distinct
    integers >= 0.

***)

fun dest_hd f_ord (Const (a, T)) = 
      let val ord = f_ord a in
        if ord = ~1 then ((1, ((a, 0), T)), 0) else ((0, (("", ord), T)), 0)
      end
  | dest_hd _ (Free (a, T)) = ((1, ((a, 0), T)), 0)
  | dest_hd _ (Var v) = ((1, v), 1)
  | dest_hd _ (Bound i) = ((1, (("", i), Term.dummyT)), 2)
  | dest_hd _ (Abs (_, T, _)) = ((1, (("", 0), T)), 3);

fun term_lpo f_ord (s, t) =
  let val (f, ss) = strip_comb s and (g, ts) = strip_comb t in
    if forall (fn si => term_lpo f_ord (si, t) = LESS) ss
    then case hd_ord f_ord (f, g) of
	GREATER =>
	  if forall (fn ti => term_lpo f_ord (s, ti) = GREATER) ts
	  then GREATER else LESS
      | EQUAL =>
	  if forall (fn ti => term_lpo f_ord (s, ti) = GREATER) ts
	  then list_ord (term_lpo f_ord) (ss, ts)
	  else LESS
      | LESS => LESS
    else GREATER
  end
and hd_ord f_ord (f, g) = case (f, g) of
    (Abs (_, T, t), Abs (_, U, u)) =>
      (case term_lpo f_ord (t, u) of EQUAL => Term.typ_ord (T, U) | ord => ord)
  | (_, _) => prod_ord (prod_ord int_ord
                  (prod_ord Term.indexname_ord Term.typ_ord)) int_ord
                (dest_hd f_ord f, dest_hd f_ord g)

in

(*** Term order for commutative rings ***)

fun ring_ord a =
  find_index_eq a ["CRing.ring.zero", "CRing.ring.add", "Cring.ring.a_inv",
  "CRing.ring.minus", "Group.monoid.one", "Group.semigroup.mult"];

fun termless_ring (a, b) = (term_lpo ring_ord (a, b) = LESS);

val cring_ss = HOL_ss settermless termless_ring;

fun cring_normalise ctxt = let
    fun filter t = (case HOLogic.dest_Trueprop t of
        Const ("CRing.cring_axioms", _) $ Free (s, _) => [s]
      | _ => [])
      handle TERM _ => [];
    val insts = flat (map (filter o #prop o rep_thm)
      (ProofContext.prems_of ctxt));
val _ = warning ("Rings in proof context: " ^ implode insts);
    val simps =
      flat (map (fn s => ProofContext.get_thms ctxt (s ^ ".cring_simprules"))
        insts);
  in Method.SIMPLE_METHOD' HEADGOAL (asm_full_simp_tac (cring_ss addsimps simps))
  end;

(*
val ring_ss = HOL_basic_ss settermless termless_ring addsimps
  [a_assoc, l_zero, l_neg, a_comm, m_assoc, l_one, l_distr, m_comm, minus_def,
   r_zero, r_neg, r_neg2, r_neg1, minus_add, minus_minus, minus0,
   a_lcomm, m_lcomm, (*r_one,*) r_distr, l_null, r_null, l_minus, r_minus];
*)

end;