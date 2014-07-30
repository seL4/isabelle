(*  Title:      HOL/Tools/SMT2/verit_proof.ML
    Author:     Mathias Fleury, ENS Rennes
    Author:     Sascha Boehme, TU Muenchen

VeriT proofs: parsing and abstract syntax tree.
*)

signature VERIT_PROOF =
sig
  (*proofs*)
  datatype veriT_step = VeriT_Step of {
    id: int,
    rule: string,
    prems: string list,
    concl: term,
    fixes: string list}

  (*proof parser*)
  val parse: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> veriT_step list * Proof.context

  val verit_step_prefix : string
  val verit_proof_input_rule: string
  val verit_rewrite : string
end;

structure VeriT_Proof: VERIT_PROOF =
struct

open SMTLIB2_Proof

(* proof rules *)

datatype veriT_node = VeriT_Node of {
  id: int,
  rule: string,
  prems: string list,
  concl: term,
  bounds: string list}

fun mk_node id rule prems concl bounds =
  VeriT_Node {id = id, rule = rule, prems = prems, concl = concl, bounds = bounds}

(*two structures needed*)
datatype veriT_step = VeriT_Step of {
  id: int,
  rule: string,
  prems: string list,
  concl: term,
  fixes: string list}

fun mk_step id rule prems concl fixes =
  VeriT_Step {id = id, rule = rule, prems = prems, concl = concl, fixes = fixes}

val verit_step_prefix = ".c"
val verit_proof_input_rule = "input"
val verit_rewrite = "rewrite"

(* proof parser *)

fun node_of p cx =
  ([], cx)
  ||>> with_fresh_names (term_of p)
  ||>> next_id
  |>> (fn ((prems, (t, ns)), id) => mk_node id verit_proof_input_rule prems t ns)

(*in order to get Z3-style quantification*)
fun fix_quantification (SMTLIB2.S (SMTLIB2.Sym "forall" :: l)) =
    let
      val (quantified_vars, t) = split_last (map fix_quantification l)
    in
      SMTLIB2.S (SMTLIB2.Sym "forall" :: SMTLIB2.S quantified_vars :: t :: [])
    end
  | fix_quantification (SMTLIB2.S (SMTLIB2.Sym "exists" :: l)) =
    let val (quantified_vars, t) = split_last (map fix_quantification l)
    in
      SMTLIB2.S (SMTLIB2.Sym "exists" :: SMTLIB2.S quantified_vars :: t :: [])
    end
  | fix_quantification (SMTLIB2.S l) = SMTLIB2.S (map fix_quantification l)
  | fix_quantification x = x

fun parse_proof cx =
  let
    fun rotate_pair (a, (b, c)) = ((a, b), c)
    fun get_id (SMTLIB2.S [SMTLIB2.Sym "set", SMTLIB2.Sym id, SMTLIB2.S l]) = (id, l)
      | get_id t = raise Fail ("unrecognized VeriT Proof" ^ PolyML.makestring t)
    fun change_id_to_number x = (unprefix verit_step_prefix #> Int.fromString #> the) x
    fun parse_rule (SMTLIB2.Sym rule :: l) = (rule, l)
    fun parse_source (SMTLIB2.Key "clauses" :: SMTLIB2.S source ::l) =
        (SOME (map (fn (SMTLIB2.Sym id) => id) source), l)
      | parse_source l = (NONE, l)
    fun skip_args (SMTLIB2.Key "args" :: SMTLIB2.S _ :: l) = l
      | skip_args l = l

    fun parse_conclusion [SMTLIB2.Key "conclusion", SMTLIB2.S concl] = concl

    fun make_or_from_clausification l =
      foldl1 (fn ((concl1, bounds1), (concl2, bounds2)) => (HOLogic.mk_disj (concl1, concl2),
        bounds1 @ bounds2)) l
    (*the conclusion is empty, ie no false*)
    fun to_node ((((id, rule), prems), ([], cx))) = (mk_node id rule (the_default [] prems)
          @{const False} [], cx)
      | to_node ((((id, rule), prems), (concls, cx))) =
        let val (concl, bounds) = make_or_from_clausification concls in
          (mk_node id rule (the_default [] prems) concl bounds, cx) end
  in
    get_id
    #>> change_id_to_number
    ##> parse_rule
    #> rotate_pair
    ##> parse_source
    #> rotate_pair
    ##> skip_args
    ##> parse_conclusion
    ##> map fix_quantification
    ##> (fn terms => fold_map (fn t => fn cx => node_of t cx) terms cx)
    ##> apfst (map (fn (VeriT_Node {concl, bounds,...}) => (concl, bounds)))
    #> to_node
  end


(* overall proof parser *)
fun parse typs funs lines ctxt =
  let
    val (u, env) =
     fold_map (fn l => fn cx => parse_proof cx l) (map (fn f => SMTLIB2.parse [f]) lines)
     (empty_context ctxt typs funs)
    val t =
     map (fn (VeriT_Node {id, rule, prems, concl, bounds, ...}) =>
       mk_step id rule prems concl bounds) u
  in
    (t, ctxt_of env)
  end

end;
