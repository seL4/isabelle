(*  Title:      Provers/split_paired_all.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Derived rule for turning meta-level surjective pairing into split rule:

           p == (fst p, snd p)
 --------------------------------------
  !!a b. PROP (a, b) == !! x. PROP P x

*)

signature SPLIT_PAIRED_ALL =
sig
  val rule: thm -> thm
end;

structure SplitPairedAll: SPLIT_PAIRED_ALL =
struct


fun all x T t = Term.all T $ Abs (x, T, t);

infixr ==>;
val op ==> = Logic.mk_implies;


fun rule raw_surj_pair =
  let
    val ct = Thm.cterm_of (Thm.sign_of_thm raw_surj_pair);

    val surj_pair = Drule.unvarify raw_surj_pair;
    val used = Term.add_term_names (#prop (Thm.rep_thm surj_pair), []);

    val (p, con $ _ $ _) = Logic.dest_equals (#prop (rep_thm surj_pair));
    val pT as Type (_, [aT, bT]) = fastype_of p;

    val P = Free (variant used "P", pT --> propT);
    val x_name = variant used "x";
    val x = Free (x_name, pT);
    val a = variant used "a";
    val b = variant used "b";

   (*"P x == P (fst x, snd x)"*)
   val lem1 =
     Thm.combination (Thm.reflexive (ct P)) surj_pair
     |> Thm.forall_intr (ct p)
     |> Thm.forall_elim (ct x);

   (*"!!a b. PROP (a, b) ==> PROP P x"*)
   val lem2 = prove_goalw_cterm [lem1]
     (ct (all a aT (all b bT (P $ (con $ Bound 1 $ Bound 0))) ==> P $ x))
     (fn prems => [resolve_tac prems 1]);

   (*"!!a b. PROP (a, b) ==> !! x. PROP P x"*)
   val lem3 = prove_goalw_cterm []
     (ct (all a aT (all b bT (P $ (con $ Bound 1 $ Bound 0))) ==> all x_name pT (P $ Bound 0)))
     (fn prems => [rtac lem2 1, resolve_tac prems 1]);

   (*"!! x. PROP P x ==> !!a b. PROP (a, b)"*)
   val lem4 = prove_goalw_cterm []
     (ct (all x_name pT (P $ Bound 0) ==> all a aT (all a bT (P $ (con $ Bound 1 $ Bound 0)))))
     (fn prems => [resolve_tac prems 1]);
  in standard (Thm.equal_intr lem4 lem3) end;


end;
