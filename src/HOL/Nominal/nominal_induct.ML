(*  ID:         $Id$
    Author:     Christian Urban and Makarius

The nominal induct proof method.
*)

structure NominalInduct:
sig
  val nominal_induct_tac: Proof.context -> (string option * term) option list ->
    (string * typ) list -> (string * typ) list list -> thm ->
    thm list -> int -> RuleCases.cases_tactic
  val nominal_induct_method: Method.src -> Proof.context -> Method.method
end =
struct


(* proper tuples -- nested left *)

fun tupleT Ts = HOLogic.unitT |> fold (fn T => fn U => HOLogic.mk_prodT (U, T)) Ts;
fun tuple ts = HOLogic.unit |> fold (fn t => fn u => HOLogic.mk_prod (u, t)) ts;

fun tuple_fun Ts (xi, T) =
  Library.funpow (length Ts) HOLogic.mk_split
    (Var (xi, (HOLogic.unitT :: Ts) ---> Term.range_type T));

val split_all_tuples =
  Simplifier.full_simplify (HOL_basic_ss addsimps
    [split_conv, split_paired_all, unit_all_eq1, thm "fresh_unit_elim", thm "fresh_prod_elim"]);


(* prepare rule *)

(*conclusion: ?P fresh_struct ... insts*)
fun inst_rule thy insts fresh rule =
  let
    val vars = InductAttrib.vars_of (Thm.concl_of rule);
    val m = length vars and n = length insts;
    val _ = if m >= n + 2 then () else error "Too few variables in conclusion of rule";
    val P :: x :: ys = vars;
    val zs = Library.drop (m - n - 2, ys);

    val subst =
      (P, tuple_fun (map #2 fresh) (Term.dest_Var P)) ::
      (x, tuple (map Free fresh)) ::
      List.mapPartial (fn (z, SOME t) => SOME (z, t) | _ => NONE) (zs ~~ insts);
  in
    rule
    |> Drule.cterm_instantiate (map (pairself (Thm.cterm_of thy)) subst)
  end;

fun rename_params_prems xs rule =
  let
    val cert = Thm.cterm_of (Thm.theory_of_thm rule);
    val (As, C) = Logic.strip_horn (Thm.prop_of rule);
    val prop = Logic.list_implies (map (curry Logic.list_rename_params xs) As, C);
  in Thm.equal_elim (Thm.reflexive (cert prop)) rule end;


(* nominal_induct_tac *)

fun nominal_induct_tac ctxt def_insts fresh fixing rule facts =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val ((insts, defs), defs_ctxt) = InductMethod.add_defs def_insts ctxt;
    val atomized_defs = map ObjectLogic.atomize_thm defs;

    val finish_rule =
      split_all_tuples
      #> rename_params_prems (map (ProofContext.revert_skolem defs_ctxt o #1) fresh);
    fun rule_cases r = RuleCases.make false (SOME (Thm.prop_of r)) (InductMethod.rulified_term r);
  in
    (fn i => fn st =>
      rule
      |> `RuleCases.get
      ||> inst_rule thy insts fresh
      |> RuleCases.consume defs facts
      |> Seq.maps (fn ((cases, (k, more_facts)), r) =>
        (CONJUNCTS (ALLGOALS (fn j =>
            Method.insert_tac (more_facts @ atomized_defs) j
            THEN InductMethod.fix_tac defs_ctxt k (Library.nth_list fixing (j - 1)) j))
          THEN' InductMethod.atomize_tac) i st |> Seq.maps (fn st' =>
            InductMethod.guess_instance (finish_rule r) i st'
            |> Seq.maps (fn r' =>
              CASES (rule_cases r' cases)
                (Tactic.rtac r' i THEN
                  PRIMSEQ (ProofContext.exports defs_ctxt ctxt)) st'))))
    THEN_ALL_NEW_CASES InductMethod.rulify_tac
  end;


(* concrete syntax *)

local

val freshN = "fresh";
val fixingN = "fixing";
val ruleN = "rule";

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.local_term >> SOME;

val def_inst =
  ((Scan.lift (Args.name --| (Args.$$$ "\\<equiv>" || Args.$$$ "==")) >> SOME)
      -- Args.local_term) >> SOME ||
    inst >> Option.map (pair NONE);

val free = Scan.state -- Args.local_term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ ProofContext.string_of_term ctxt t));

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ freshN || Args.$$$ fixingN || Args.$$$ ruleN) -- Args.colon)) scan;


val def_insts = Scan.repeat (unless_more_args def_inst);

val fresh = Scan.optional (Scan.lift (Args.$$$ freshN -- Args.colon) |--
  Scan.repeat (unless_more_args free)) [];

val fixing = Scan.optional (Scan.lift (Args.$$$ fixingN -- Args.colon) |--
  Args.and_list1 (Scan.repeat (unless_more_args free))) [];

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.colon) |-- Attrib.local_thm;

in

fun nominal_induct_method src =
  Method.syntax (def_insts -- fresh -- fixing -- rule_spec) src
  #> (fn (ctxt, (((x, y), z), w)) =>
    Method.RAW_METHOD_CASES (fn facts =>
      HEADGOAL (nominal_induct_tac ctxt x y z w facts)));

end;

end;
