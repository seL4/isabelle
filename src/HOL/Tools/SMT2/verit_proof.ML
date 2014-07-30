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
val veriT_tmp_ite_elim_rule = "tmp_ite_elim"
val veriT_tmp_skolemize = "tmp_skolemize"
val veriT_alpha_conv = "tmp_alphaconv"

fun mk_string_id id = veriT_step_prefix ^ (string_of_int id)

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

fun replace_bound_var_by_free_var (q $ Abs (var, ty, u)) free_var =
    (case List.find (fn v => String.isPrefix v var) free_var of
      NONE => q $ Abs (var, ty, replace_bound_var_by_free_var u free_var)
    | SOME _ => replace_bound_var_by_free_var (Term.subst_bound (Free (var, ty), u)) free_var)
  | replace_bound_var_by_free_var (u $ v) free_vars = replace_bound_var_by_free_var u free_vars $
     replace_bound_var_by_free_var v free_vars
  | replace_bound_var_by_free_var u _ = u

fun find_type_in_formula (Abs(v, ty, u)) var_name =
    if String.isPrefix var_name v then SOME ty else find_type_in_formula u var_name
  | find_type_in_formula (u $ v) var_name =
    (case find_type_in_formula u var_name of
      NONE => find_type_in_formula v var_name
    | a => a)
  | find_type_in_formula _ _ = NONE

fun add_bound_variables_to_ctxt cx bounds concl =
    fold (fn a => fn b => update_binding a b)
      (map (fn s => ((s, Term (Free (s, the_default dummyT (find_type_in_formula concl s))))))
       bounds) cx

fun update_step_and_cx (st as VeriT_Node {id, rule, prems, concl, bounds}) cx =
  if rule = veriT_tmp_ite_elim_rule then
    (mk_node id rule prems concl bounds, add_bound_variables_to_ctxt cx bounds concl)
  else if rule = veriT_tmp_skolemize then
    let
      val concl' = replace_bound_var_by_free_var concl bounds
    in
      (mk_node id rule prems concl' [], add_bound_variables_to_ctxt cx bounds concl)
    end
  else
    (st, cx)

(*FIXME: using a reference would be better to know th numbers of the steps to add*)
fun fix_subproof_steps number_of_steps ((((id, rule), prems), subproof), ((step_concl, bounds),
    cx)) =
  let
    fun mk_prop_of_term concl = (fastype_of concl = @{typ "bool"} ?
      curry (op $) @{term "Trueprop"}) concl
    fun inline_assumption assumption assumption_id (st as VeriT_Node {id, rule, prems, concl,
        bounds}) =
      if List.find (curry (op =) assumption_id) prems <> NONE then
        mk_node (id + number_of_steps) rule (filter_out (curry (op =) assumption_id) prems)
          (Const ("Pure.imp", @{typ "prop"} --> @{typ "prop"} --> @{typ "prop"})
          $ mk_prop_of_term assumption $ mk_prop_of_term concl) bounds
      else
        st
    fun find_input_steps_and_inline [] last_step_number = ([], last_step_number)
      | find_input_steps_and_inline (VeriT_Node {id = id', rule, prems, concl, bounds} :: steps)
          last_step_number =
        if rule = veriT_input_rule then
          find_input_steps_and_inline (map (inline_assumption concl (mk_string_id id')) steps)
            last_step_number
        else
          apfst (cons (mk_node (id' + id + number_of_steps) rule prems concl bounds))
            (find_input_steps_and_inline steps (id' + id + number_of_steps))
    val (subproof', last_step_number) = find_input_steps_and_inline subproof ~1
    val prems' =
      if last_step_number = ~1 then prems
      else
        (case prems of
          NONE => SOME [mk_string_id last_step_number]
        | SOME l => SOME (string_of_int last_step_number :: l))
  in
    (subproof', (((((id, rule), prems'), step_concl), bounds), cx))
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
        let val (subproof_steps, cx') = parse_proof_step number_of_steps cx subproof_step in
          apfst (apfst (curry (op @) subproof_steps)) (parse_subproof cx' l)
        end
      | parse_subproof cx l = (([], cx), l)
    fun skip_args (SMTLIB2.Key "args" :: SMTLIB2.S _ :: l) = l
      | skip_args l = l
    fun parse_conclusion (SMTLIB2.Key "conclusion" :: SMTLIB2.S concl :: []) = concl
    fun make_or_from_clausification l =
      foldl1 (fn ((concl1, bounds1), (concl2, bounds2)) =>
        (HOLogic.mk_disj (perhaps (try HOLogic.dest_Trueprop) concl1,
        perhaps (try HOLogic.dest_Trueprop) concl2), bounds1 @ bounds2)) l
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
    #> (fn (steps, cx) => fold_map update_step_and_cx steps cx)
  end


(*function related to parsing and general transformation*)

(*subproofs are written on multiple lines: SMTLIB can not parse then, because parentheses are
unbalanced on each line*)
fun seperate_into_steps lines =
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

fun find_in_which_step_defined var (VeriT_Node {id, bounds, ...} :: l) =
    (case List.find (fn v => String.isPrefix v var) bounds of
      NONE => find_in_which_step_defined var l
    | SOME _ => id)
  | find_in_which_step_defined var _ = raise Fail ("undefined " ^ var)

(*Yes every case is possible: the introduced var is not on a special size of the equality sign.*)
fun find_ite_var_in_term (Const ("HOL.If", _) $ _ $
      (Const ("HOL.eq", _) $ Free (var1, _) $ Free (var2, _) ) $
      (Const ("HOL.eq", _) $ Free (var3, _) $ Free (var4, _) )) =
    let
      fun get_number_of_ite_transformed_var var =
        perhaps (try (unprefix "ite")) var
        |> Int.fromString
      fun is_equal_and_has_correct_substring var var' var'' =
        if var = var' andalso String.isPrefix "ite" var then SOME var'
        else if var = var'' andalso String.isPrefix "ite" var then SOME var'' else NONE
      val var1_introduced_var = is_equal_and_has_correct_substring var1 var3 var4
      val var2_introduced_var = is_equal_and_has_correct_substring var3 var1 var2
    in
      (case (var1_introduced_var, var2_introduced_var) of
        (SOME a, SOME b) =>
          (*ill-generated case, might be possible when applying the rule to max a a. Only if the
          variable have been introduced before. Probably an impossible edge case*)
          (case (get_number_of_ite_transformed_var a, get_number_of_ite_transformed_var b) of
            (SOME a, SOME b) => if a < b then var2_introduced_var else var1_introduced_var
            (*Otherwise, it is a name clase between a parameter name and the introduced variable.
             Or the name convention has been changed.*)
          | (NONE, SOME _) => var2_introduced_var
          | (SOME _, NONE) => var2_introduced_var)
      | (_, SOME _) => var2_introduced_var
      | (SOME _, _) => var1_introduced_var)
    end
  | find_ite_var_in_term (Const (@{const_name "If"}, _) $ _ $
      (Const (@{const_name "HOL.eq"}, _) $ Free (var, _) $ _ ) $
      (Const (@{const_name "HOL.eq"}, _) $ Free (var', _) $ _ )) =
    if var = var' then SOME var else NONE
  | find_ite_var_in_term (Const (@{const_name "If"}, _) $ _ $
      (Const (@{const_name "HOL.eq"}, _) $ _ $ Free (var, _)) $
      (Const (@{const_name "HOL.eq"}, _) $ _ $ Free (var', _))) =
    if var = var' then SOME var else NONE
  | find_ite_var_in_term (p $ q) =
    (case find_ite_var_in_term p of
      NONE => find_ite_var_in_term q
    | x => x)
  | find_ite_var_in_term (Abs (_, _, body)) = find_ite_var_in_term body
  | find_ite_var_in_term _ = NONE


fun correct_veriT_step num_of_steps steps (st as VeriT_Node {id, rule, prems, concl, bounds}) =
  if rule = "tmp_ite_elim" then
    if bounds = [] then
      (*if the introduced var has already been defined,
        adding the definition as a dependency*)
      let
        val SOME var = find_ite_var_in_term concl
        val new_dep = find_in_which_step_defined var steps
      in
        VeriT_Node {id = id, rule = rule, prems = (mk_string_id new_dep) :: prems,
          concl = concl, bounds = bounds}
      end
    else
      (*some new variables are created*)
      let
        val concl' = replace_bound_var_by_free_var concl bounds
      in
      (*FIXME: horrible hackish method, but seems somehow to work. The difference is in the way
      sledgehammer reconstructs: without an empty dependency, the skolemization is not done at all.
      But if there is, a new step is added:
         {fix sk ....}
         hence "..sk.."
         thus "(if ..)"
      last step does not work: the step before is buggy. Without the proof work.*)
        mk_node id veriT_tmp_skolemize (if null prems then [mk_string_id (~num_of_steps - id)]
          else prems) concl' []
      end
  else
    st

(*remove alpha conversion step, that just renames the variables*)
fun remove_alpha_conversion _ [] = []
  | remove_alpha_conversion replace_table (VeriT_Node {id, rule, prems, concl, bounds} :: steps) =
    let
      fun correct_dependency prems =
        map (fn x => perhaps (Symtab.lookup replace_table) x) prems
      fun find_predecessor prem = perhaps (Symtab.lookup replace_table) prem
    in
      if rule = veriT_alpha_conv then
        remove_alpha_conversion (Symtab.update (mk_string_id id, find_predecessor (hd prems))
          replace_table) steps
      else
        VeriT_Node {id = id, rule = rule, prems = correct_dependency prems,
          concl = concl, bounds = bounds} :: remove_alpha_conversion replace_table steps
    end

fun correct_veriT_steps steps =
  steps
  |> map (correct_veriT_step (1 + length steps) steps)
  |> remove_alpha_conversion Symtab.empty

(* overall proof parser *)
fun parse typs funs lines ctxt =
  let
    val smtlib2_lines_without_at =
      remove_all_at (map SMTLIB2.parse (seperate_into_steps lines))
    val (u, env) = apfst flat (fold_map (fn l => fn cx => parse_proof_step (length lines) cx l)
                             smtlib2_lines_without_at (empty_context ctxt typs funs))
    val t = correct_veriT_steps u
    fun node_to_step (VeriT_Node {id, rule, prems, concl, bounds, ...}) =
      mk_step id rule prems concl bounds
   in
    (map node_to_step t, ctxt_of env)
  end

end;
