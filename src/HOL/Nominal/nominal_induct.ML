(*  ID:         $Id$
    Author:     Christian Urban and Makarius

The nominal induct proof method.
*)

structure NominalInduct:
sig
  val nominal_induct_tac: Proof.context -> (string option * term) option list list ->
    (string * typ) list -> (string * typ) list list -> thm list ->
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

(*conclusions: ?P avoiding_struct ... insts*)
fun inst_mutual_rule thy insts avoiding rules =
  let
    val (concls, rule) =
      (case RuleCases.mutual_rule rules of
        NONE => error "Failed to join given rules into one mutual rule"
      | SOME res => res);
    val (cases, consumes) = RuleCases.get rule;

    val l = length rules;
    val _ =
      if length insts = l then ()
      else error ("Bad number of instantiations for " ^ string_of_int l ^ " rules");

    fun subst inst rule =
      let
        val vars = InductAttrib.vars_of (Thm.concl_of rule);
        val m = length vars and n = length inst;
        val _ = if m >= n + 2 then () else error "Too few variables in conclusion of rule";
        val P :: x :: ys = vars;
        val zs = Library.drop (m - n - 2, ys);
      in
        (P, tuple_fun (map #2 avoiding) (Term.dest_Var P)) ::
        (x, tuple (map Free avoiding)) ::
        List.mapPartial (fn (z, SOME t) => SOME (z, t) | _ => NONE) (zs ~~ inst)
      end;
     val substs =
       map2 subst insts rules |> List.concat |> distinct (op =)
       |> map (pairself (Thm.cterm_of thy));
  in (((cases, concls), consumes), Drule.cterm_instantiate substs rule) end;

fun rename_params_rule internal xs rule =
  let
    val tune =
      if internal then Syntax.internal
      else fn x => the_default x (try Syntax.dest_internal x);
    val n = length xs;
    fun rename prem =
      let
        val ps = Logic.strip_params prem;
        val p = length ps;
        val ys =
          if p < n then []
          else map (tune o #1) (Library.take (p - n, ps)) @ xs;
      in Logic.list_rename_params (ys, prem) end;
    fun rename_prems prop =
      let val (As, C) = Logic.strip_horn (Thm.prop_of rule)
      in Logic.list_implies (map rename As, C) end;
  in Thm.equal_elim (Thm.reflexive (Drule.cterm_fun rename_prems (Thm.cprop_of rule))) rule end;


(* nominal_induct_tac *)

fun nominal_induct_tac ctxt def_insts avoiding fixings rules facts =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val ((insts, defs), defs_ctxt) = fold_map InductMethod.add_defs def_insts ctxt |>> split_list;
    val atomized_defs = map (map ObjectLogic.atomize_thm) defs;

    val finish_rule =
      split_all_tuples
      #> rename_params_rule true (map (ProofContext.revert_skolem defs_ctxt o fst) avoiding);
    fun rule_cases r = RuleCases.make_nested true (Thm.prop_of r) (InductMethod.rulified_term r);
  in
    (fn i => fn st =>
      rules
      |> inst_mutual_rule thy insts avoiding
      |> RuleCases.consume (List.concat defs) facts
      |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
          (CONJUNCTS (ALLGOALS
            (Method.insert_tac (more_facts @ nth_list atomized_defs (j - 1))
              THEN' InductMethod.fix_tac defs_ctxt
                (nth concls (j - 1) + more_consumes)
                (nth_list fixings (j - 1))))
          THEN' InductMethod.inner_atomize_tac) j))
        THEN' InductMethod.atomize_tac) i st |> Seq.maps (fn st' =>
            InductMethod.guess_instance
              (finish_rule (InductMethod.internalize more_consumes rule)) i st'
            |> Seq.maps (fn rule' =>
              CASES (rule_cases rule' cases)
                (Tactic.rtac (rename_params_rule false [] rule') i THEN
                  PRIMSEQ (ProofContext.exports defs_ctxt ctxt)) st'))))
    THEN_ALL_NEW_CASES InductMethod.rulify_tac
  end;


(* concrete syntax *)

local

val avoidingN = "avoiding";
val fixingN = "fixing";
val ruleN = "rule";

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val def_inst =
  ((Scan.lift (Args.name --| (Args.$$$ "\\<equiv>" || Args.$$$ "==")) >> SOME)
      -- Args.term) >> SOME ||
    inst >> Option.map (pair NONE);

val free = Scan.state -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ ProofContext.string_of_term (Context.proof_of ctxt) t));

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ avoidingN || Args.$$$ fixingN || Args.$$$ ruleN) -- Args.colon)) scan;


val avoiding = Scan.optional (Scan.lift (Args.$$$ avoidingN -- Args.colon) |--
  Scan.repeat (unless_more_args free)) [];

val fixing = Scan.optional (Scan.lift (Args.$$$ fixingN -- Args.colon) |--
  Args.and_list (Scan.repeat (unless_more_args free))) [];

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.colon) |-- Attrib.thms;

in

fun nominal_induct_method src =
  Method.syntax
   (Args.and_list (Scan.repeat (unless_more_args def_inst)) --
    avoiding -- fixing -- rule_spec) src
  #> (fn (ctxt, (((x, y), z), w)) =>
    Method.RAW_METHOD_CASES (fn facts =>
      HEADGOAL (nominal_induct_tac ctxt x y z w facts)));

end;

end;
