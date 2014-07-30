(*  Title:      HOL/Tools/SMT2/veriT_proof.ML
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

  val veriT_step_prefix : string
  val veriT_input_rule: string
  val veriT_rewrite_rule : string
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

val veriT_step_prefix = ".c"
val veriT_input_rule = "input"
val veriT_rewrite_rule = "__rewrite" (*arbitrary*)
val veriT_proof_ite_elim_rule = "tmp_ite_elim"
val veriT_var_suffix = "v"
val veriT_tmp_skolemize = "tmp_skolemize"

(* proof parser *)

fun node_of p cx =
  ([], cx)
  ||>> with_fresh_names (term_of p)
  ||>> next_id
  |>> (fn ((prems, (t, ns)), id) => mk_node id veriT_input_rule prems t ns)

(*in order to get Z3-style quantification*)
fun fix_quantification (SMTLIB2.S (SMTLIB2.Sym "forall" :: l)) =
    let val (quantified_vars, t) = split_last (map fix_quantification l)
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

fun replace_bound_var_by_free_var (q $ Abs (var, ty, u)) free_var replaced n =
    (case List.find (fn v => String.isPrefix v var) free_var of
      NONE => q $ Abs (var, ty, replace_bound_var_by_free_var u free_var replaced (n+1))
    | SOME _ => 
      replace_bound_var_by_free_var u free_var ((n, Free (var ^ veriT_var_suffix, ty)) :: replaced)
        (n+1))
  | replace_bound_var_by_free_var (Bound n) _ replaced_vars _ =
    (case List.find (curry (op =) n o fst) replaced_vars of
      NONE => Bound n
    | SOME (_, var) => var)
  | replace_bound_var_by_free_var (u $ v) free_vars replaced n =
    replace_bound_var_by_free_var u free_vars replaced n $
      replace_bound_var_by_free_var v free_vars replaced n
  | replace_bound_var_by_free_var u _ _ _ = u

fun find_type_in_formula (Abs(v, ty, u)) var_name =
    if var_name = v then SOME ty else find_type_in_formula u var_name
  | find_type_in_formula (u $ v) var_name =
    (case find_type_in_formula u var_name of
      NONE => find_type_in_formula v var_name
    | a => a)
  | find_type_in_formula _ _ = NONE


fun update_ctxt cx bounds concl =
  fold_index (fn (_, a) => fn b => update_binding a b) 
    (map (fn s => ((s, Term (Free (s ^ "__" ^ veriT_var_suffix,
    the_default dummyT (find_type_in_formula concl s)))))) bounds) cx

fun update_step cx (st as VeriT_Node {id, rule, prems, concl, bounds}) =
  if rule = veriT_proof_ite_elim_rule then
    (mk_node id rule prems concl bounds, update_ctxt cx bounds concl)
  else if rule = veriT_tmp_skolemize then
    let
      val concl' = replace_bound_var_by_free_var concl bounds [] 0
    in
      (mk_node id rule prems concl' [], update_ctxt cx bounds concl)
    end
  else
    (st, cx)

fun fix_subproof_steps number_of_steps ((((id, rule), prems), subproof), ((step_concl, bounds),
    cx)) =
  let
    fun inline_assumption assumption assumption_id (st as VeriT_Node {id, rule, prems, concl,
        bounds}) =
      if List.find (curry (op =) assumption_id) prems <> NONE then
         mk_node (id + number_of_steps) rule (filter_out (curry (op =) assumption_id) prems)
           ((Const ("Pure.imp", @{typ "prop => prop => prop"}) $ assumption) $ concl)
           bounds
      else
        st
    fun inline_assumption_in_conclusion concl (VeriT_Node {rule, concl = assumption,...} :: l) =
        if rule = veriT_input_rule then
          inline_assumption_in_conclusion
            (Const (@{const_name Pure.imp}, @{typ "prop => prop => prop"}) $ assumption $ concl) l
        else
          inline_assumption_in_conclusion concl l
      | inline_assumption_in_conclusion concl [] = concl
    fun find_assumption_and_inline (VeriT_Node {id, rule, prems, concl, bounds} :: l) =
        if rule = veriT_input_rule then
          map (inline_assumption step_concl (veriT_step_prefix ^ string_of_int id)) l
        else
          (mk_node (id + number_of_steps) rule prems concl bounds) :: find_assumption_and_inline l
      | find_assumption_and_inline [] = []
  in
    (find_assumption_and_inline subproof,
     (((((id, rule), prems), inline_assumption_in_conclusion step_concl subproof), bounds), cx))
  end

(*
(set id rule :clauses(...) :args(..) :conclusion (...)).
or
(set id subproof (set ...) :conclusion (...)).
*)

fun parse_proof_step number_of_steps cx =
  let
    fun rotate_pair (a, (b, c)) = ((a, b), c)
    fun get_id (SMTLIB2.S [SMTLIB2.Sym "set", SMTLIB2.Sym id, SMTLIB2.S l]) = (id, l)
      | get_id t = raise Fail ("unrecognized VeriT Proof" ^ PolyML.makestring t)
    fun change_id_to_number x = (unprefix veriT_step_prefix #> Int.fromString #> the) x
    fun parse_rule (SMTLIB2.Sym rule :: l) = (rule, l)
    fun parse_source (SMTLIB2.Key "clauses" :: SMTLIB2.S source ::l) =
        (SOME (map (fn (SMTLIB2.Sym id) => id) source), l)
      | parse_source l = (NONE, l)
    fun parse_subproof cx ((subproof_step as SMTLIB2.S (SMTLIB2.Sym "set" :: _)) :: l) =
        let val (step, cx') = parse_proof_step number_of_steps cx subproof_step in
          apfst (apfst (cons step)) (parse_subproof cx' l)
        end
      | parse_subproof cx l = (([], cx), l)

    fun skip_args (SMTLIB2.Key "args" :: SMTLIB2.S _ :: l) = l
      | skip_args l = l

    fun parse_conclusion (SMTLIB2.Key "conclusion" :: SMTLIB2.S concl :: []) = concl

    fun make_or_from_clausification l =
      foldl1 (fn ((concl1, bounds1), (concl2, bounds2)) => (HOLogic.mk_disj (concl1, concl2),
        bounds1 @ bounds2)) l
    fun to_node (((((id, rule), prems), concl), bounds), cx) = (mk_node id rule
        (the_default [] prems) concl bounds, cx)
  in
    get_id
    #>> change_id_to_number
    ##> parse_rule
    #> rotate_pair
    ##> parse_source
    #> rotate_pair
    ##> skip_args
    ##> parse_subproof cx
    #> rotate_pair
    ##> parse_conclusion
    ##> map fix_quantification
    #> (fn ((((id, rule), prems), (subproof, cx)), terms) =>
         (((((id, rule), prems), subproof), fold_map (fn t => fn cx => node_of t cx) terms cx)))
    ##> apfst ((map (fn (VeriT_Node {concl, bounds,...}) => (concl, bounds))))
    (*the conclusion is the empty list, ie no false is written, we have to add it.*)
    ##> (apfst (fn [] => (@{const False}, [])
                 | concls => make_or_from_clausification concls))
    #> fix_subproof_steps number_of_steps
    ##> to_node
    #> (fn (subproof, (step, cx)) => (subproof @ [step], cx))
    #> (fn (steps, cx) => update_step cx (List.last steps))
  end

fun seperate_into_lines_and_subproof lines =
  let
    fun count ("(" :: l) n = count l (n+1)
      | count (")" :: l) n = count l (n-1)
      | count (_ :: l) n = count l n
      | count [] n = n
    fun seperate (line :: l) actual_lines m =
        let val n = count (raw_explode line) 0 in
          if m + n = 0 then
            [actual_lines ^ line] :: seperate l "" 0
          else seperate l (actual_lines ^ line) (m + n)
      end
      | seperate [] _ 0 = []
  in
    seperate lines "" 0
  end

 (*VeriT adds @ before every variable.*)
fun remove_all_at (SMTLIB2.Sym v :: l) =
    SMTLIB2.Sym (if nth_string v 0 = "@" then String.extract (v, 1, NONE) else v) :: remove_all_at l
  | remove_all_at (SMTLIB2.S l :: l') = SMTLIB2.S (remove_all_at l) :: remove_all_at l'
  | remove_all_at (SMTLIB2.Key v :: l) = SMTLIB2.Key v :: remove_all_at l
  | remove_all_at (v :: l) = v :: remove_all_at l
  | remove_all_at [] = []

fun replace_all_by_exist (Const (@{const_name Pure.all}, ty) $ Abs (var, ty', u)) bounds =
    (case List.find (fn v => String.isPrefix v var) bounds of
        NONE => (Const (@{const_name Pure.all}, ty) $ Abs (var, ty', replace_all_by_exist u bounds))
      | SOME _ => Const (@{const_name HOL.Ex}, (ty' --> @{typ bool}) --> @{typ bool}) $
        Abs (var ^ veriT_var_suffix, ty', replace_all_by_exist u bounds))
  | replace_all_by_exist (@{term "Trueprop"} $ g) bounds = replace_all_by_exist g bounds
  | replace_all_by_exist (f $ g) bounds =
    replace_all_by_exist f bounds $ replace_all_by_exist g bounds
  | replace_all_by_exist (Abs (var, ty, u)) bounds = Abs (var, ty, replace_all_by_exist u bounds)
  | replace_all_by_exist f _ = f


fun correct_veriT_steps num_of_steps (st as VeriT_Node {id = id, rule = rule, prems = prems,
     concl = concl, bounds = bounds}) =
  if rule = "tmp_ite_elim" then
    let
      val concl' = replace_bound_var_by_free_var concl bounds [] 0
    in
      [mk_node (num_of_steps + id) rule prems (@{term "Trueprop"} $
                  replace_all_by_exist concl bounds) [],
       mk_node id veriT_tmp_skolemize (veriT_step_prefix ^ (string_of_int (num_of_steps + id)) ::
          []) concl' []]
    end
  else
    [st]



(* overall proof parser *)
fun parse typs funs lines ctxt =
  let
    val smtlib2_lines_without_at = 
      remove_all_at (map SMTLIB2.parse (seperate_into_lines_and_subproof lines))
    val (u, env) =
      fold_map (fn l => fn cx => parse_proof_step (length lines) cx l) smtlib2_lines_without_at
      (empty_context ctxt typs funs)
    val t = map (correct_veriT_steps (1 + length u)) u |> flat
    fun node_to_step (VeriT_Node {id, rule, prems, concl, bounds, ...}) = 
      mk_step id rule prems concl bounds
   in
    (map node_to_step t, ctxt_of env)
  end

end;
