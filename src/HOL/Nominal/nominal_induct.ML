(*  ID:         $Id$
    Author:     Christian Urban

The nominal induct proof method (cf. ~~/src/Provers/induct_method.ML).
*)

structure NominalInduct:
sig
  val nominal_induct_tac: Proof.context -> (string option * term) option list ->
    term list -> (string * typ) list list -> thm -> thm list -> int -> RuleCases.cases_tactic
  val nominal_induct_method: Method.src -> Proof.context -> Method.method
end =
struct


(** misc tools **)

fun nth_list xss i = nth xss i handle Subscript => [];

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then raise ERROR_MESSAGE msg else (Library.drop (m - n, xs) ~~ ys) end;

fun prep_inst thy tune (tm, ts) =
  let
    val cert = Thm.cterm_of thy;
    fun prep_var (x, SOME t) =
          let
            val cx = cert x;
            val {T = xT, thy, ...} = Thm.rep_cterm cx;
            val ct = cert (tune t);
          in
            if Sign.typ_instance thy (#T (Thm.rep_cterm ct), xT) then SOME (cx, ct)
            else raise ERROR_MESSAGE (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Display.pretty_cterm ct, Pretty.str " ::", Pretty.brk 1,
              Display.pretty_ctyp (#T (Thm.crep_cterm ct))]))
          end
      | prep_var (_, NONE) = NONE;
    val xs = InductAttrib.vars_of tm;
  in
    align_right "Rule has fewer variables than instantiations given" xs ts
    |> List.mapPartial prep_var
  end;

fun add_defs def_insts =
  let
    fun add (SOME (SOME x, t)) ctxt =
          let val ((lhs, def), ctxt') = ProofContext.add_def (x, t) ctxt
          in ((SOME (Free lhs), [def]), ctxt') end
      | add (SOME (NONE, t)) ctxt = ((SOME t, []), ctxt)
      | add NONE ctxt = ((NONE, []), ctxt);
  in fold_map add def_insts #> apfst (split_list #> apsnd List.concat) end;



(** nominal_induct_tac **)

fun make_fresh [] = HOLogic.unit
  | make_fresh [t] = t
  | make_fresh ts = foldr1 HOLogic.mk_prod ts;

val split_fresh =
  Simplifier.full_simplify (HOL_basic_ss addsimps [split_paired_all, unit_all_eq1]);

fun nominal_induct_tac ctxt def_insts fresh fixing rule facts =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val ((insts, defs), defs_ctxt) = add_defs def_insts ctxt;
    val atomized_defs = map ObjectLogic.atomize_thm defs;

    fun inst_rule r =
      Drule.cterm_instantiate
        (prep_inst thy (InductMethod.atomize_term thy)
          (Thm.concl_of r, insts @ [SOME (make_fresh fresh)])) r;

    fun rule_cases r = RuleCases.make false (SOME (Thm.prop_of r)) (InductMethod.rulified_term r);
  in
    SUBGOAL_CASES (fn (goal, i) => fn st =>
      rule
      |> inst_rule
      |> `RuleCases.get
      |> RuleCases.consume defs facts
      |> Seq.maps (fn ((cases, (k, more_facts)), r) =>
        (CONJUNCTS (ALLGOALS (fn j =>
            Method.insert_tac (more_facts @ atomized_defs) j
            THEN InductMethod.fix_tac defs_ctxt k (nth_list fixing (j - 1)) j))
          THEN' InductMethod.atomize_tac) i st |> Seq.maps (fn st' =>
            InductMethod.guess_instance (split_fresh r) i st'
            |> Seq.maps (fn r' =>
              CASES (rule_cases r' cases)
                (Tactic.rtac r' i THEN
                  PRIMSEQ (ProofContext.exports defs_ctxt ctxt)) st'))))
    THEN_ALL_NEW_CASES InductMethod.rulify_tac
  end;



(** concrete syntax **)

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
  Scan.repeat (unless_more_args Args.local_term)) [];

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
