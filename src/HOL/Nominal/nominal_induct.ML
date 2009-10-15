(*  Author:     Christian Urban and Makarius

The nominal induct proof method.
*)

structure NominalInduct:
sig
  val nominal_induct_tac: Proof.context -> (binding option * term) option list list ->
    (string * typ) list -> (string * typ) list list -> thm list ->
    thm list -> int -> RuleCases.cases_tactic
  val nominal_induct_method: (Proof.context -> Proof.method) context_parser
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
    [split_conv, split_paired_all, unit_all_eq1, @{thm fresh_unit_elim}, @{thm fresh_prod_elim}] @
    @{thms fresh_star_unit_elim} @ @{thms fresh_star_prod_elim});


(* prepare rule *)

fun inst_mutual_rule ctxt insts avoiding rules =
  let
    val (nconcls, joined_rule) = RuleCases.strict_mutual_rule ctxt rules;
    val concls = Logic.dest_conjunctions (Thm.concl_of joined_rule);
    val (cases, consumes) = RuleCases.get joined_rule;

    val l = length rules;
    val _ =
      if length insts = l then ()
      else error ("Bad number of instantiations for " ^ string_of_int l ^ " rules");

    fun subst inst concl =
      let
        val vars = Induct.vars_of concl;
        val m = length vars and n = length inst;
        val _ = if m >= n + 2 then () else error "Too few variables in conclusion of rule";
        val P :: x :: ys = vars;
        val zs = Library.drop (m - n - 2, ys);
      in
        (P, tuple_fun (map #2 avoiding) (Term.dest_Var P)) ::
        (x, tuple (map Free avoiding)) ::
        map_filter (fn (z, SOME t) => SOME (z, t) | _ => NONE) (zs ~~ inst)
      end;
     val substs =
       map2 subst insts concls |> flat |> distinct (op =)
       |> map (pairself (Thm.cterm_of (ProofContext.theory_of ctxt)));
  in 
    (((cases, nconcls), consumes), Drule.cterm_instantiate substs joined_rule) 
  end;

fun rename_params_rule internal xs rule =
  let
    val tune =
      if internal then Name.internal
      else fn x => the_default x (try Name.dest_internal x);
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

    val ((insts, defs), defs_ctxt) = fold_map Induct.add_defs def_insts ctxt |>> split_list;
    val atomized_defs = map (map (Conv.fconv_rule ObjectLogic.atomize)) defs;

    val finish_rule =
      split_all_tuples
      #> rename_params_rule true
        (map (Name.clean o ProofContext.revert_skolem defs_ctxt o fst) avoiding);
    fun rule_cases r = RuleCases.make_nested true (Thm.prop_of r) (Induct.rulified_term r);
  in
    (fn i => fn st =>
      rules
      |> inst_mutual_rule ctxt insts avoiding
      |> RuleCases.consume (flat defs) facts
      |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
          (CONJUNCTS (ALLGOALS
            (Method.insert_tac (more_facts @ nth_list atomized_defs (j - 1))
              THEN' Induct.fix_tac defs_ctxt
                (nth concls (j - 1) + more_consumes)
                (nth_list fixings (j - 1))))
          THEN' Induct.inner_atomize_tac) j))
        THEN' Induct.atomize_tac) i st |> Seq.maps (fn st' =>
            Induct.guess_instance ctxt
              (finish_rule (Induct.internalize more_consumes rule)) i st'
            |> Seq.maps (fn rule' =>
              CASES (rule_cases rule' cases)
                (Tactic.rtac (rename_params_rule false [] rule') i THEN
                  PRIMITIVE (singleton (ProofContext.export defs_ctxt ctxt))) st'))))
    THEN_ALL_NEW_CASES Induct.rulify_tac
  end;


(* concrete syntax *)

local

structure P = OuterParse;

val avoidingN = "avoiding";
val fixingN = "arbitrary";  (* to be consistent with induct; hopefully this changes again *)
val ruleN = "rule";

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val def_inst =
  ((Scan.lift (Args.binding --| (Args.$$$ "\<equiv>" || Args.$$$ "==")) >> SOME)
      -- Args.term) >> SOME ||
    inst >> Option.map (pair NONE);

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ avoidingN || Args.$$$ fixingN || Args.$$$ ruleN) -- Args.colon)) scan;


val avoiding = Scan.optional (Scan.lift (Args.$$$ avoidingN -- Args.colon) |--
  Scan.repeat (unless_more_args free)) [];

val fixing = Scan.optional (Scan.lift (Args.$$$ fixingN -- Args.colon) |--
  P.and_list' (Scan.repeat (unless_more_args free))) [];

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.colon) |-- Attrib.thms;

in

val nominal_induct_method =
  P.and_list' (Scan.repeat (unless_more_args def_inst)) --
  avoiding -- fixing -- rule_spec >>
  (fn (((x, y), z), w) => fn ctxt =>
    RAW_METHOD_CASES (fn facts =>
      HEADGOAL (nominal_induct_tac ctxt x y z w facts)));

end;

end;
