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
  val rule_params: string -> string -> thm -> thm
  val rule: thm -> thm
end;

structure SplitPairedAll: SPLIT_PAIRED_ALL =
struct


fun all x T t = Term.all T $ Abs (x, T, t);

infixr ==>;
val op ==> = Logic.mk_implies;


fun rule_params a b raw_surj_pair =
  let
    val ct = Thm.cterm_of (Thm.sign_of_thm raw_surj_pair);

    val surj_pair = Drule.unvarify (standard raw_surj_pair);
    val used = Term.add_term_names (#prop (Thm.rep_thm surj_pair), []);

    val (p, con $ _ $ _) = Logic.dest_equals (#prop (rep_thm surj_pair));
    val pT as Type (_, [aT, bT]) = fastype_of p;
    val P = Free (variant used "P", pT --> propT);

   (*"!!a b. PROP (a, b)"*)
   val all_a_b = all a aT (all b bT (P $ (con $ Bound 1 $ Bound 0)));
   (*"!!x. PROP P x"*)
   val all_x = all "x" pT (P $ Bound 0);

   (*lemma "P p == P (fst p, snd p)"*)
   val lem1 = Thm.combination (Thm.reflexive (ct P)) surj_pair;

   (*lemma "(!!a b. PROP P (a,b)) ==> PROP P p"*)
   val lem2 = prove_goalw_cterm [lem1] (ct (all_a_b ==> P $ p))
     (fn prems => [resolve_tac prems 1]);

   (*lemma "(!!a b. PROP P (a,b)) ==> !!x. PROP P x"*)
   val lem3 = prove_goalw_cterm [] (ct (all_a_b ==> all_x))
     (fn prems => [rtac lem2 1, resolve_tac prems 1]);

   (*lemma "(!!x. PROP P x) ==> !!a b. PROP P (a,b)"*)
   val lem4 = prove_goalw_cterm [] (ct (all_x ==> all_a_b))
     (fn prems => [resolve_tac prems 1]);
  in standard (Thm.equal_intr lem4 lem3) end;

val rule = rule_params "a" "b";


end;
