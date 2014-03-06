(*  Title:      HOL/Tools/coinduction.ML
    Author:     Johannes Hölzl, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Coinduction method that avoids some boilerplate compared to coinduct.
*)

signature COINDUCTION =
sig
  val coinduction_tac: Proof.context -> term list -> thm option -> thm list -> cases_tactic
  val setup: theory -> theory
end;

structure Coinduction : COINDUCTION =
struct

open Ctr_Sugar_Util
open Ctr_Sugar_General_Tactics

fun filter_in_out _ [] = ([], [])
  | filter_in_out P (x :: xs) = (let
      val (ins, outs) = filter_in_out P xs;
    in
      if P x then (x :: ins, outs) else (ins, x :: outs)
    end);

fun ALLGOALS_SKIP skip tac st =
  let fun doall n = if n = skip then all_tac else tac n THEN doall (n - 1)
  in doall (nprems_of st) st  end;

fun THEN_ALL_NEW_SKIP skip tac1 tac2 i st =
  st |> (tac1 i THEN (fn st' =>
    Seq.INTERVAL tac2 (i + skip) (i + nprems_of st' - nprems_of st) st'));

fun DELETE_PREMS_AFTER skip tac i st =
  let
    val n = nth (prems_of st) (i - 1) |> Logic.strip_assums_hyp |> length;
  in
    (THEN_ALL_NEW_SKIP skip tac (REPEAT_DETERM_N n o etac thin_rl)) i st
  end;

fun coinduction_tac ctxt raw_vars opt_raw_thm prems st =
  let
    val lhs_of_eq = HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst;
    fun find_coinduct t = 
      Induct.find_coinductP ctxt t @
      (try (Induct.find_coinductT ctxt o fastype_of o lhs_of_eq) t |> the_default [])
    val raw_thm = case opt_raw_thm
      of SOME raw_thm => raw_thm
       | NONE => st |> prems_of |> hd |> Logic.strip_assums_concl |> find_coinduct |> hd;
    val skip = Integer.max 1 (Rule_Cases.get_consumes raw_thm) - 1
    val cases = Rule_Cases.get raw_thm |> fst
  in
    NO_CASES (HEADGOAL (
      Object_Logic.rulify_tac ctxt THEN'
      Method.insert_tac prems THEN'
      Object_Logic.atomize_prems_tac ctxt THEN'
      DELETE_PREMS_AFTER skip (Subgoal.FOCUS (fn {concl, context = ctxt, params, prems, ...} =>
        let
          val vars = raw_vars @ map (term_of o snd) params;
          val names_ctxt = ctxt
            |> fold Variable.declare_names vars
            |> fold Variable.declare_thm (raw_thm :: prems);
          val thm_concl = Thm.cprop_of raw_thm |> strip_imp_concl;
          val (rhoTs, rhots) = Thm.match (thm_concl, concl)
            |>> map (pairself typ_of)
            ||> map (pairself term_of);
          val xs = hd (Thm.prems_of raw_thm) |> HOLogic.dest_Trueprop |> strip_comb |> snd
            |> map (subst_atomic_types rhoTs);
          val raw_eqs = map (fn x => (x, AList.lookup op aconv rhots x |> the)) xs;
          val ((names, ctxt), Ts) = map_split (apfst fst o dest_Var o fst) raw_eqs
            |>> (fn names => Variable.variant_fixes names names_ctxt) ;
          val eqs =
            map3 (fn name => fn T => fn (_, rhs) =>
              HOLogic.mk_eq (Free (name, T), rhs))
            names Ts raw_eqs;
          val phi = eqs @ map (HOLogic.dest_Trueprop o prop_of) prems
            |> try (Library.foldr1 HOLogic.mk_conj)
            |> the_default @{term True}
            |> list_exists_free vars
            |> Term.map_abs_vars (Variable.revert_fixed ctxt)
            |> fold_rev Term.absfree (names ~~ Ts)
            |> certify ctxt;
          val thm = cterm_instantiate_pos [SOME phi] raw_thm;
          val e = length eqs;
          val p = length prems;
        in
          HEADGOAL (EVERY' [rtac thm,
            EVERY' (map (fn var =>
              rtac (cterm_instantiate_pos [NONE, SOME (certify ctxt var)] exI)) vars),
            if p = 0 then CONJ_WRAP' (K (rtac refl)) eqs
            else REPEAT_DETERM_N e o (rtac conjI THEN' rtac refl) THEN' CONJ_WRAP' rtac prems,
            K (ALLGOALS_SKIP skip
               (REPEAT_DETERM_N (length vars) o (etac exE THEN' rotate_tac ~1) THEN'
               DELETE_PREMS_AFTER 0 (Subgoal.FOCUS (fn {prems, params, context = ctxt, ...} =>
                 (case prems of
                   [] => all_tac
                 | inv::case_prems =>
                     let
                       val (init, last) = funpow_yield (p + e - 1) HOLogic.conj_elim inv;
                       val inv_thms = init @ [last];
                       val eqs = take e inv_thms;
                       fun is_local_var t = 
                         member (fn (t, (_, t')) => t aconv (term_of t')) params t;
                        val (eqs, assms') = filter_in_out (is_local_var o lhs_of_eq o prop_of) eqs;
                        val assms = assms' @ drop e inv_thms
                      in
                        HEADGOAL (Method.insert_tac (assms @ case_prems)) THEN
                        unfold_thms_tac ctxt eqs
                      end)) ctxt)))])
        end) ctxt) THEN'
      K (prune_params_tac ctxt))) st
    |> Seq.maps (fn (_, st) =>
      CASES (Rule_Cases.make_common (Proof_Context.theory_of ctxt, prop_of st) cases) all_tac st)
  end;

local

val ruleN = "rule"
val arbitraryN = "arbitrary"
fun single_rule [rule] = rule
  | single_rule _ = error "Single rule expected";

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- Scan.repeat arg :|--
    (fn names => Scan.peek (fn context => Scan.succeed (names |> map (fn name =>
      (case get (Context.proof_of context) name of SOME x => x
      | NONE => error ("No rule for " ^ k ^ " " ^ quote name))))));

fun rule get_type get_pred =
  named_rule Induct.typeN (Args.type_name {proper = false, strict = false}) get_type ||
  named_rule Induct.predN (Args.const false) get_pred ||
  named_rule Induct.setN (Args.const false) get_pred ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.thms;

val coinduct_rule = rule Induct.lookup_coinductT Induct.lookup_coinductP >> single_rule;

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ arbitraryN || Args.$$$ Induct.typeN ||
    Args.$$$ Induct.predN || Args.$$$ Induct.setN || Args.$$$ ruleN) -- Args.colon)) scan;

val arbitrary = Scan.optional (Scan.lift (Args.$$$ arbitraryN -- Args.colon) |--
  Scan.repeat1 (unless_more_args Args.term)) [];

in

val setup =
  Method.setup @{binding coinduction}
    (arbitrary -- Scan.option coinduct_rule >>
      (fn (arbitrary, opt_rule) => fn ctxt =>
        RAW_METHOD_CASES (fn facts =>
          Seq.DETERM (coinduction_tac ctxt arbitrary opt_rule facts))))
    "coinduction on types or predicates/sets";

end;

end;

