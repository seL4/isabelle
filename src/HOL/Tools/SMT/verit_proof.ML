(*  Title:      HOL/Tools/SMT/verit_proof.ML
    Author:     Mathias Fleury, ENS Rennes
    Author:     Sascha Boehme, TU Muenchen

VeriT proofs: parsing and abstract syntax tree.
*)

signature VERIT_PROOF =
sig
  (*proofs*)
  datatype veriT_step = VeriT_Step of {
    id: string,
    rule: string,
    prems: string list,
    proof_ctxt: term list,
    concl: term,
    fixes: string list}

  datatype veriT_replay_node = VeriT_Replay_Node of {
    id: string,
    rule: string,
    args: term list,
    prems: string list,
    proof_ctxt: term list,
    concl: term,
    bounds: (string * typ) list,
    subproof: (string * typ) list * term list * veriT_replay_node list}

  (*proof parser*)
  val parse: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> veriT_step list * Proof.context
  val parse_replay: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> veriT_replay_node list * Proof.context

  val map_replay_prems: (string list -> string list) -> veriT_replay_node -> veriT_replay_node
  val veriT_step_prefix : string
  val veriT_input_rule: string
  val veriT_normalized_input_rule: string
  val veriT_la_generic_rule : string
  val veriT_rewrite_rule : string
  val veriT_simp_arith_rule : string
  val veriT_tmp_skolemize_rule : string
  val veriT_subproof_rule : string
  val veriT_local_input_rule : string
end;

structure VeriT_Proof: VERIT_PROOF =
struct

open SMTLIB_Proof

datatype raw_veriT_node = Raw_VeriT_Node of {
  id: string,
  rule: string,
  args: SMTLIB.tree,
  prems: string list,
  concl: SMTLIB.tree,
  subproof: raw_veriT_node list}

fun mk_raw_node id rule args prems concl subproof =
  Raw_VeriT_Node {id = id, rule = rule, args = args, prems = prems, concl = concl,
    subproof = subproof}

datatype veriT_node = VeriT_Node of {
  id: string,
  rule: string,
  prems: string list,
  proof_ctxt: term list,
  concl: term,
  bounds: string list}

fun mk_node id rule prems proof_ctxt concl bounds =
  VeriT_Node {id = id, rule = rule, prems = prems, proof_ctxt = proof_ctxt, concl = concl,
    bounds = bounds}

datatype veriT_replay_node = VeriT_Replay_Node of {
  id: string,
  rule: string,
  args: term list,
  prems: string list,
  proof_ctxt: term list,
  concl: term,
  bounds: (string * typ) list,
  subproof: (string * typ) list * term list * veriT_replay_node list}

fun mk_replay_node id rule args prems proof_ctxt concl bounds subproof =
  VeriT_Replay_Node {id = id, rule = rule, args = args, prems = prems, proof_ctxt = proof_ctxt,
    concl = concl, bounds = bounds, subproof = subproof}

datatype veriT_step = VeriT_Step of {
  id: string,
  rule: string,
  prems: string list,
  proof_ctxt: term list,
  concl: term,
  fixes: string list}

fun mk_step id rule prems proof_ctxt concl fixes =
  VeriT_Step {id = id, rule = rule, prems = prems, proof_ctxt = proof_ctxt, concl = concl,
    fixes = fixes}

val veriT_step_prefix = ".c"
val veriT_input_rule = "input"
val veriT_la_generic_rule = "la_generic"
val veriT_normalized_input_rule = "__normalized_input" (* arbitrary *)
val veriT_rewrite_rule = "__rewrite" (* arbitrary *)
val veriT_subproof_rule = "subproof"
val veriT_local_input_rule = "__local_input" (* arbitrary *)
val veriT_simp_arith_rule = "simp_arith"

(* Even the veriT developer do not know if the following rule can still appear in proofs: *)
val veriT_tmp_skolemize_rule = "tmp_skolemize"

(* proof parser *)

fun node_of p cx =
  ([], cx)
  ||>> `(with_fresh_names (term_of p))
  |>> snd

fun find_type_in_formula (Abs (v, T, u)) var_name =
    if String.isPrefix var_name v then SOME T else find_type_in_formula u var_name
  | find_type_in_formula (u $ v) var_name =
    (case find_type_in_formula u var_name of
      NONE => find_type_in_formula v var_name
    | some_T => some_T)
  | find_type_in_formula (Free(v, T)) var_name =
    if String.isPrefix var_name v then SOME T else NONE
  | find_type_in_formula _ _ = NONE

fun find_type_of_free_in_formula (Free (v, T) $ u) var_name =
    if String.isPrefix var_name v then SOME T else find_type_in_formula u var_name
  | find_type_of_free_in_formula (Abs (v, T, u)) var_name =
    if String.isPrefix var_name v then SOME T else find_type_in_formula u var_name
  | find_type_of_free_in_formula (u $ v) var_name =
    (case find_type_in_formula u var_name of
      NONE => find_type_in_formula v var_name
    | some_T => some_T)
  | find_type_of_free_in_formula _ _ = NONE

fun add_bound_variables_to_ctxt concl =
  fold (update_binding o
    (fn s => (s, Term (Free (s, the_default dummyT (find_type_in_formula concl s))))))


local

  fun remove_Sym (SMTLIB.Sym y) = y

  fun extract_symbols bds =
    bds
    |> map (fn SMTLIB.S [SMTLIB.Key _, SMTLIB.Sym x, SMTLIB.Sym y] => [x, y]
            | SMTLIB.S syms => map remove_Sym syms)
    |> flat

  fun extract_symbols_map bds =
    bds
    |> map (fn SMTLIB.S [SMTLIB.Key _, SMTLIB.Sym x, _] => [x]
            | SMTLIB.S syms =>  map remove_Sym syms)
    |> flat
in

fun bound_vars_by_rule "bind" (SMTLIB.S bds) = extract_symbols bds
  | bound_vars_by_rule "qnt_simplify" (SMTLIB.S bds) = extract_symbols_map bds
  | bound_vars_by_rule "sko_forall" (SMTLIB.S bds) = extract_symbols_map bds
  | bound_vars_by_rule "sko_ex" (SMTLIB.S bds) = extract_symbols_map bds
  | bound_vars_by_rule _ _ = []

fun global_bound_vars_by_rule _ _ = []

(* VeriT adds "?" before some variable. *)
fun remove_all_qm (SMTLIB.Sym v :: l) =
    SMTLIB.Sym (perhaps (try (unprefix "?")) v) :: remove_all_qm l
  | remove_all_qm (SMTLIB.S l :: l') = SMTLIB.S (remove_all_qm l) :: remove_all_qm l'
  | remove_all_qm (SMTLIB.Key v :: l) = SMTLIB.Key v :: remove_all_qm l
  | remove_all_qm (v :: l) = v :: remove_all_qm l
  | remove_all_qm [] = []

fun remove_all_qm2 (SMTLIB.Sym v) = SMTLIB.Sym (perhaps (try (unprefix "?")) v)
  | remove_all_qm2 (SMTLIB.S l) = SMTLIB.S (remove_all_qm l)
  | remove_all_qm2 (SMTLIB.Key v) = SMTLIB.Key v
  | remove_all_qm2 v = v

val parse_rule_and_args =
  let
    fun parse_rule_name (SMTLIB.Sym rule :: l) = (rule, l)
      | parse_rule_name l = (veriT_subproof_rule, l)
    fun parse_args (SMTLIB.Key "args" :: args :: l) = (remove_all_qm2 args, l)
      | parse_args l = (SMTLIB.S [], l)
  in
    parse_rule_name
    ##> parse_args
  end

end

fun parse_raw_proof_step (p :  SMTLIB.tree) : raw_veriT_node =
  let
    fun rotate_pair (a, (b, c)) = ((a, b), c)
    fun get_id (SMTLIB.S [SMTLIB.Sym "set", SMTLIB.Sym id, SMTLIB.S l]) = (id, l)
      | get_id t = raise Fail ("unrecognized VeriT proof " ^ \<^make_string> t)
    fun parse_source (SMTLIB.Key "clauses" :: SMTLIB.S source ::l) =
        (SOME (map (fn (SMTLIB.Sym id) => id) source), l)
      | parse_source l = (NONE, l)
    fun parse_subproof rule args id_of_father_step ((subproof_step as SMTLIB.S (SMTLIB.Sym "set" :: _)) :: l) =
        let
          val subproof_steps = parse_raw_proof_step subproof_step
        in
          apfst (curry (op ::) subproof_steps) (parse_subproof rule args id_of_father_step l)
        end
      | parse_subproof _ _  _ l = ([], l)

    fun parse_and_clausify_conclusion (SMTLIB.Key "conclusion" :: SMTLIB.S [] :: []) =
          SMTLIB.Sym "false"
      | parse_and_clausify_conclusion (SMTLIB.Key "conclusion" :: SMTLIB.S concl :: []) =
          (SMTLIB.S (remove_all_qm (SMTLIB.Sym "or" :: concl)))

    fun to_raw_node ((((((id, rule), args), prems), subproof), concl)) =
      (mk_raw_node id rule args (the_default [] prems) concl subproof)
  in
    (get_id
    ##> parse_rule_and_args
    #> rotate_pair
    #> rotate_pair
    ##> parse_source
    #> rotate_pair
    #> (fn ((((id, rule), args), prems), sub) =>
      ((((id, rule), args), prems), parse_subproof rule args id sub))
    #> rotate_pair
    ##> parse_and_clausify_conclusion
    #> to_raw_node)
    p
  end

fun proof_ctxt_of_rule "bind" t = t
  | proof_ctxt_of_rule "sko_forall" t = t
  | proof_ctxt_of_rule "sko_ex" t = t
  | proof_ctxt_of_rule "let" t = t
  | proof_ctxt_of_rule "qnt_simplify" t = t
  | proof_ctxt_of_rule _ _ = []

fun args_of_rule "forall_inst" t = t
  | args_of_rule _ _ = []

fun map_replay_prems f (VeriT_Replay_Node {id, rule, args, prems, proof_ctxt, concl, bounds,
      subproof = (bound, assms, subproof)}) =
  (VeriT_Replay_Node {id = id, rule = rule, args = args, prems = f prems, proof_ctxt = proof_ctxt,
    concl = concl, bounds = bounds, subproof = (bound, assms, map (map_replay_prems f) subproof)})

fun map_replay_id f (VeriT_Replay_Node {id, rule, args, prems, proof_ctxt, concl, bounds,
      subproof = (bound, assms, subproof)}) =
  (VeriT_Replay_Node {id = f id, rule = rule, args = args, prems = prems, proof_ctxt = proof_ctxt,
    concl = concl, bounds = bounds, subproof = (bound, assms, map (map_replay_id f) subproof)})

fun id_of_last_step prems =
  if null prems then []
  else
    let val VeriT_Replay_Node {id, ...} = List.last prems in [id] end

val extract_assumptions_from_subproof =
  let fun extract_assumptions_from_subproof (VeriT_Replay_Node {rule, concl, ...}) =
    if rule = veriT_local_input_rule then [concl] else []
  in
    map extract_assumptions_from_subproof
    #> flat
  end

fun normalized_rule_name id rule =
  (case (rule = veriT_input_rule, can (unprefix SMTLIB_Interface.assert_prefix) id) of
    (true, true) => veriT_normalized_input_rule
  | (true, _) => veriT_local_input_rule
  | _ => rule)

fun is_assm_repetition id rule =
  rule = veriT_input_rule andalso can (unprefix SMTLIB_Interface.assert_prefix) id

fun postprocess_proof ctxt step =
  let fun postprocess (Raw_VeriT_Node {id = id, rule = rule, args = args,
     prems = prems, concl = concl, subproof = subproof}) cx =
    let
      val ((concl, bounds), cx') = node_of concl cx

      val bound_vars = bound_vars_by_rule rule args

      (* postprocess conclusion *)
      val new_global_bounds = global_bound_vars_by_rule rule args
      val concl = SMTLIB_Isar.unskolemize_names ctxt concl

      val _ = (SMT_Config.veriT_msg ctxt) (fn () => \<^print> ("id =", id, "concl =", concl))
      val _ = (SMT_Config.veriT_msg ctxt) (fn () => \<^print> ("id =", id, "cx' =", cx',
        "bound_vars =", bound_vars))
      val bound_vars = filter_out (member ((op =)) new_global_bounds) bound_vars
      val bound_tvars =
        map (fn s => (s, the (find_type_in_formula concl s))) bound_vars
      val subproof_cx = add_bound_variables_to_ctxt concl bound_vars cx
      val (p : veriT_replay_node list list, _) =
        fold_map postprocess subproof subproof_cx

      (* postprocess assms *)
      val SMTLIB.S stripped_args = args
      val sanitized_args =
        proof_ctxt_of_rule rule stripped_args
        |> map
            (fn SMTLIB.S [SMTLIB.Key "=", x, y] => SMTLIB.S [SMTLIB.Sym "=", x, y]
            | SMTLIB.S syms =>
                SMTLIB.S (SMTLIB.Sym "and" :: map (fn x => SMTLIB.S [SMTLIB.Sym "=", x, x]) syms)
            | x => x)
      val (termified_args, _) = fold_map node_of sanitized_args subproof_cx |> apfst (map fst)
      val normalized_args = map (SMTLIB_Isar.unskolemize_names ctxt) termified_args

      val subproof_assms = proof_ctxt_of_rule rule normalized_args

      (* postprocess arguments *)
      val rule_args = args_of_rule rule stripped_args
      val (termified_args, _) = fold_map term_of rule_args subproof_cx
      val normalized_args = map (SMTLIB_Isar.unskolemize_names ctxt) termified_args
      val rule_args = normalized_args

      (* fix subproof *)
      val p = flat p
      val p = map (map_replay_prems (map (curry (op ^) id))) p
      val p = map (map_replay_id (curry (op ^) id)) p

      val extra_assms2 =
        (if rule = veriT_subproof_rule then extract_assumptions_from_subproof p else [])

      (* fix step *)
      val bound_t =
        bounds
        |> map (fn s => (s, the_default dummyT (find_type_of_free_in_formula concl s)))
      val fixed_prems =
        (if null subproof then prems else map (curry (op ^) id) prems) @
        (if is_assm_repetition id rule then [id] else []) @
        id_of_last_step p
      val normalized_rule = normalized_rule_name id rule
      val step = mk_replay_node id normalized_rule rule_args fixed_prems subproof_assms concl
        bound_t (bound_tvars, subproof_assms @ extra_assms2, p)
    in
       ([step], cx')
    end
  in postprocess step end


(*subproofs are written on multiple lines: SMTLIB can not parse then, because parentheses are
unbalanced on each line*)
fun seperate_into_steps lines =
  let
    fun count ("(" :: l) n = count l (n + 1)
      | count (")" :: l) n = count l (n - 1)
      | count (_ :: l) n = count l n
      | count [] n = n
    fun seperate (line :: l) actual_lines m =
        let val n = count (raw_explode line) 0 in
          if m + n = 0 then
            [actual_lines ^ line] :: seperate l "" 0
          else
            seperate l (actual_lines ^ line) (m + n)
        end
      | seperate [] _ 0 = []
  in
    seperate lines "" 0
  end

fun unprefix_all_syms c (SMTLIB.Sym v :: l) =
    SMTLIB.Sym (perhaps (try (unprefix c)) v) :: unprefix_all_syms c l
  | unprefix_all_syms c (SMTLIB.S l :: l') = SMTLIB.S (unprefix_all_syms c l) :: unprefix_all_syms c l'
  | unprefix_all_syms c (SMTLIB.Key v :: l) = SMTLIB.Key v :: unprefix_all_syms c l
  | unprefix_all_syms c (v :: l) = v :: unprefix_all_syms c l
  | unprefix_all_syms _ [] = []

(* VeriT adds "@" before every variable. *)
val remove_all_ats = unprefix_all_syms "@"

val linearize_proof =
  let
    fun linearize (VeriT_Replay_Node {id = id, rule = rule, args = _, prems = prems,
        proof_ctxt = proof_ctxt, concl = concl, bounds = bounds, subproof = (_, _, subproof)}) =
      let
        fun mk_prop_of_term concl =
          concl |> fastype_of concl = \<^typ>\<open>bool\<close> ? curry (op $) \<^term>\<open>Trueprop\<close>
        fun remove_assumption_id assumption_id prems =
          filter_out (curry (op =) assumption_id) prems
        fun inline_assumption assumption assumption_id
            (VeriT_Node {id, rule, prems, proof_ctxt, concl, bounds}) =
          mk_node id rule (remove_assumption_id assumption_id prems) proof_ctxt
            (\<^const>\<open>Pure.imp\<close> $ mk_prop_of_term assumption $ mk_prop_of_term concl) bounds
        fun find_input_steps_and_inline [] = []
          | find_input_steps_and_inline
              (VeriT_Node {id = id', rule, prems, concl, bounds, ...} :: steps) =
            if rule = veriT_input_rule then
              find_input_steps_and_inline (map (inline_assumption concl id') steps)
            else
              mk_node (id') rule prems [] concl bounds :: find_input_steps_and_inline steps

        val subproof = flat (map linearize subproof)
        val subproof' = find_input_steps_and_inline subproof
      in
        subproof' @ [mk_node id rule prems proof_ctxt concl (map fst bounds)]
      end
  in linearize end

local
  fun import_proof_and_post_process typs funs lines ctxt =
    let
      val smtlib_lines_without_at =
      seperate_into_steps lines
      |> map SMTLIB.parse
      |> remove_all_ats
    in apfst flat (fold_map (fn l => postprocess_proof ctxt (parse_raw_proof_step l))
      smtlib_lines_without_at (empty_context ctxt typs funs)) end
in

fun parse typs funs lines ctxt =
  let
    val (u, env) = import_proof_and_post_process typs funs lines ctxt
    val t = flat (map linearize_proof u)
    fun node_to_step (VeriT_Node {id, rule, prems, concl, bounds, ...}) =
      mk_step id rule prems [] concl bounds
  in
    (map node_to_step t, ctxt_of env)
  end

fun parse_replay typs funs lines ctxt =
  let
    val (u, env) = import_proof_and_post_process typs funs lines ctxt
    val _ = (SMT_Config.veriT_msg ctxt) (fn () => \<^print> u)
  in
    (u, ctxt_of env)
  end
end

end;
