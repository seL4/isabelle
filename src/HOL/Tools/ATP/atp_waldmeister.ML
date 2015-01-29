(*  Title:      HOL/Tools/ATP/atp_waldmeister.ML
    Author:     Albert Steckermeier, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

exception FailureMessage of string

signature ATP_WALDMEISTER_SKOLEMIZER =
sig
  val skolemize : bool -> Proof.context -> term -> (Proof.context * (term list * term))
end;

signature ATP_WALDMEISTER_TYPE_ENCODER =
sig
  val encode_type : typ -> string
  val decode_type_string : string -> typ
  val encode_types : typ list -> string
  val decode_types : string -> typ list
  val encode_const : string * typ list -> string
  val decode_const : string -> string * typ list
end;

signature ATP_WALDMEISTER =
sig
  type 'a atp_problem = 'a ATP_Problem.atp_problem
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  type 'a atp_proof = 'a ATP_Proof.atp_proof
  type stature = ATP_Problem_Generate.stature
  type waldmeister_info =  (string * (term list * (term option * term))) list

  val waldmeister_skolemize_rule : string

  val generate_waldmeister_problem : Proof.context -> term list -> term ->
    ((string * stature) * term) list ->
    string atp_problem * string Symtab.table * (string * term) list * int Symtab.table *
    waldmeister_info
  val termify_waldmeister_proof : Proof.context -> string Symtab.table -> string atp_proof ->
    (term, string) atp_step list
  val introduce_waldmeister_skolems : waldmeister_info -> (term, string) atp_step list ->
    (term, string) atp_step list
end;

structure ATP_Waldmeister_Skolemizer : ATP_WALDMEISTER_SKOLEMIZER =
struct

open HOLogic

fun contains_quantor (Const (@{const_name Ex}, _) $ _) = true
  | contains_quantor (Const (@{const_name All}, _) $ _) = true
  | contains_quantor (t1 $ t2) = contains_quantor t1 orelse contains_quantor t2
  | contains_quantor _ = false

fun mk_fun_for_bvar ctxt1 ctxt2 arg_trms (bound_name, ty) =
  let
    val fun_type = (map type_of arg_trms) ---> ty
    val (fun_name, _) = singleton (Variable.variant_frees ctxt2 []) ("sko_" ^ bound_name,fun_type)
    val (_, ctxt1_new) = Variable.add_fixes [fun_name] ctxt1
    val (_, ctxt2_new) = Variable.add_fixes [fun_name] ctxt2
  in
    (Term.list_comb (Free (fun_name,fun_type), arg_trms), ctxt1_new, ctxt2_new)
  end

fun skolem_free ctxt1 ctxt2 vars (bound_name, ty, trm) =
  let
    val (fun_trm, ctxt1_new, ctxt2_new) =
      mk_fun_for_bvar ctxt1 ctxt2 (List.rev vars) (bound_name,ty)
  in
    (Term.subst_bounds ([fun_trm], trm), ctxt1_new, ctxt2_new)
  end

fun skolem_var ctxt (bound_name, ty, trm) =
  let
    val (var_name, _) = singleton (Variable.variant_frees ctxt []) (bound_name, ty)
    val (_, ctxt') = Variable.add_fixes [var_name] ctxt
    val var = Var ((var_name, 0), ty)
  in
   (Term.subst_bounds ([var], trm), ctxt', var)
  end

fun skolem_bound is_free ctxt1 ctxt2 spets vars x =
  if is_free then
    let
      val (trm', ctxt1', ctxt2') = skolem_free ctxt1 ctxt2 vars x
    in
      (ctxt1', ctxt2',spets, trm', vars)
    end
  else
    let
      val (trm', ctxt2', var) = skolem_var ctxt2 x
    in
      (ctxt1, ctxt2', spets, trm', var :: vars)
    end

fun skolemize' pos ctxt1 ctxt2 spets vars (Const (@{const_name Not}, _) $ trm') =
    let
      val (ctxt1', ctxt2', spets', trm'') = skolemize' (not pos) ctxt1 ctxt2 spets vars trm'
    in
      (ctxt1', ctxt2', map mk_not spets', mk_not trm'')
    end
  | skolemize' pos ctxt1 ctxt2 spets vars (trm as (Const (@{const_name HOL.eq}, t) $ a $ b)) =
    if t = @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"} andalso contains_quantor trm then
      skolemize' pos ctxt1 ctxt2 (trm :: spets) vars (mk_conj (mk_imp (a, b), mk_imp (b, a)))
    else
      (ctxt1, ctxt2, spets, trm)
  | skolemize' pos ctxt1 ctxt2 spets vars (trm as (Const (name, _) $ Abs x)) =
    if name = @{const_name Ex} orelse name = @{const_name All} then
      let
        val is_free =  (name = @{const_name Ex} andalso pos)
          orelse (name = @{const_name All} andalso not pos)
        val (ctxt1', ctxt2', spets', trm', vars') =
          skolem_bound is_free ctxt1 ctxt2 (if is_free then trm :: spets else spets) vars x
      in
        skolemize' pos ctxt1' ctxt2' spets' vars' trm'
      end
    else
      (ctxt1, ctxt2, spets, trm)
  | skolemize' pos ctxt1 ctxt2 spets vars ((c as Const (name, _)) $ a $ b) =
    if name = @{const_name conj} orelse name = @{const_name disj} orelse
       name = @{const_name implies} then
      let
        val pos_a = if name = @{const_name implies} then not pos else pos
        val (ctxt1', ctxt2', spets', a') = skolemize'  pos_a ctxt1 ctxt2 [] vars a
        val (ctxt1'', ctxt2'', spets'', b') = skolemize' pos ctxt1' ctxt2' [] vars b
      in
        (ctxt1'', ctxt2'',
         map (fn trm => c $ a' $ trm) spets'' @ map (fn trm => c $ trm $ b) spets' @ spets,
         c $ a' $ b')
      end
    else
      (ctxt1,ctxt2,spets,c $ a $ b)
  | skolemize' _ ctxt1 ctxt2 spets _ trm = (ctxt1, ctxt2, spets, trm)

  fun vars_of trm =
    rev (distinct (op =) (Term.fold_aterms (fn t as Var _ => cons t | _ => I) trm []));

  fun skolemize positve ctxt trm =
    let
      val (ctxt1, _, spets, skolemized_trm) = skolemize' positve ctxt ctxt [] (vars_of trm) trm
    in
        (ctxt1, (trm :: List.rev spets, skolemized_trm))
    end

end;

structure ATP_Waldmeister_Type_Encoder : ATP_WALDMEISTER_TYPE_ENCODER =
struct

val delimiter = ";"
val open_paranthesis = "["
val close_parathesis = "]"
val type_prefix = "Type"
val tfree_prefix = "TFree"
val tvar_prefix = "TVar"

val identifier_character = not o member (op =) [delimiter, open_paranthesis, close_parathesis]

fun encode_type (Type (name, types)) =
  type_prefix ^ open_paranthesis ^ name ^ delimiter ^
  (map encode_type types |> space_implode delimiter) ^ close_parathesis
| encode_type (TFree (name, sorts)) =
  tfree_prefix ^ open_paranthesis ^ name ^ delimiter ^ space_implode delimiter sorts ^
  close_parathesis
| encode_type (TVar ((name, i), sorts)) =
  tvar_prefix ^ open_paranthesis ^ open_paranthesis ^ name ^ delimiter ^ Int.toString i ^
  close_parathesis ^ delimiter ^ space_implode delimiter sorts ^ close_parathesis

fun encode_types types = space_implode delimiter (map encode_type types)

fun parse_identifier x =
  (Scan.many identifier_character >> implode) x

fun parse_star delim scanner x =
  (Scan.optional (scanner ::: Scan.repeat ($$ delim |-- scanner)) []) x

fun parse_type x = (Scan.this_string type_prefix |-- $$ open_paranthesis |-- parse_identifier --|
  $$ delimiter -- parse_star delimiter parse_any_type --| $$ close_parathesis >> Type) x
and parse_tfree x = (Scan.this_string tfree_prefix |-- $$ open_paranthesis |-- parse_identifier --|
  $$ delimiter -- parse_star delimiter parse_identifier --| $$ close_parathesis >> TFree) x
and parse_tvar x = (Scan.this_string tvar_prefix |-- $$ open_paranthesis |-- $$ open_paranthesis
  |-- parse_identifier --| $$ delimiter -- (parse_identifier >> (Int.fromString #> the)) --| $$
  close_parathesis --| $$ delimiter -- parse_star delimiter parse_identifier --|
  $$ close_parathesis >> TVar) x
and parse_any_type x = (parse_type || parse_tfree || parse_tvar) x

fun parse_types x = parse_star delimiter parse_any_type x

fun decode_type_string s = Scan.finite Symbol.stopper
  (Scan.error (!! (fn _ => raise FailureMessage ("unrecognized type encoding" ^
  quote s)) parse_type))  (Symbol.explode s) |> fst

fun decode_types s = Scan.finite Symbol.stopper
  (Scan.error (!! (fn _ => raise FailureMessage ("unrecognized type encoding" ^
  quote s))) parse_types) (Symbol.explode s) |> fst

fun encode_const (name,tys) = name ^ delimiter ^ encode_types tys

fun parse_const s = (parse_identifier --| $$ delimiter -- parse_types) s

fun decode_const s = Scan.finite Symbol.stopper
  (Scan.error (!! (fn _ => raise FailureMessage ("unrecognized const encoding" ^
  quote s))) parse_const) (Symbol.explode s) |> fst

end;

structure ATP_Waldmeister (*** : ATP_WALDMEISTER  *) =
struct

open ATP_Util
open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct
open ATP_Waldmeister_Skolemizer
open ATP_Waldmeister_Type_Encoder
open HOLogic

type ('a, 'b) atp_term = ('a, 'b) ATP_Problem.atp_term
type atp_connective = ATP_Problem.atp_connective
type ('a, 'b, 'c, 'd) atp_formula = ('a, 'b, 'c, 'd) ATP_Problem.atp_formula
type atp_format = ATP_Problem.atp_format
type atp_formula_role = ATP_Problem.atp_formula_role
type 'a atp_problem = 'a ATP_Problem.atp_problem
type waldmeister_info =  (string * (term list * (term option * term))) list

val const_prefix = #"c"
val var_prefix = #"V"
val free_prefix = #"v"
val conjecture_condition_name = "condition"
val waldmeister_equals = "eq"
val waldmeister_true = "true"
val waldmeister_false = "false"
val waldmeister_skolemize_rule = "waldmeister_skolemize"
val lam_lift_waldmeister_prefix = "lambda_wm"
val waldmeister_apply = "wm_apply"

val factsN = "Relevant facts"
val helpersN = "Helper facts"
val conjN = "Conjecture"
val conj_identifier = conjecture_prefix ^ "0"

val WM_ERROR_MSG = "Waldmeister problem generator failed: "

(*
  Some utilitary functions for translation.
*)

fun gen_ascii_tuple str = (str, ascii_of str)

fun mk_eq_true (trm as (Const (@{const_name HOL.eq}, _) $ _ $ _)) = (NONE,trm)
  | mk_eq_true trm = (SOME trm,HOLogic.mk_eq (trm, @{term True}))

val is_lambda_name = String.isPrefix lam_lifted_poly_prefix

fun lookup table k =
  List.find (fn (key, _) => key = k) table

fun dest_list' (f $ t) =
  let
    val (function, trms) = dest_list' f
  in
    (function, t :: trms)
  end
  | dest_list' t = (t,[]);

fun dest_list trm = dest_list' trm ||> List.rev

fun list_update x [] = [x]
  | list_update (a,b) ((c,d) :: xs) =
  if a = c andalso b < d then
    (a,b) :: xs
  else
    (c,d) :: list_update (a,b) xs

(*
  Hiding partial applications in terms
*)

fun map_minimal_app' info (trm :: trms) =
    map_minimal_app' (minimal_app' info trm) trms
  | map_minimal_app' info _ = info

and minimal_app' info (trm as _ $ _) =
  let
    val (function, trms) = dest_list trm
    val info' = map_minimal_app' info trms
  in
    case function of
      (Const _) => list_update (function, length trms) info' |
      (Free _) => list_update (function, length trms) info' |
      _ => info
  end
  | minimal_app' info (trm as Const _) =
   list_update (trm, 0) info
  | minimal_app' info (trm as Free _) =
   list_update (trm, 0) info
  | minimal_app' info _ = info;

fun map_minimal_app trms = map_minimal_app' [] trms

fun mk_waldmeister_app function [] = function
  | mk_waldmeister_app function (a :: args) =
    let
      val funT = type_of function
      val argT = type_of a
      val resT = dest_funT funT |> snd
      val newT = funT --> argT --> resT
    in
      mk_waldmeister_app (Const (waldmeister_apply ^ "," ^
        encode_types [resT, argT], newT) $ function $ a) args
    end

fun hide_partial_applications info (trm as (_ $ _)) =
  let
    val (function, trms) = dest_list trm
    val trms' = map (hide_partial_applications info) trms
  in
    case function of
    Var _ =>  mk_waldmeister_app function trms' |
    _ =>
      let
        val min_args = lookup info function |> the |> snd
        val args0 = List.take (trms',min_args)
        val args1 = List.drop (trms',min_args)
        val function' = list_comb (function,args0)
      in
        mk_waldmeister_app function' args1
      end
  end
  | hide_partial_applications _ t = t;

fun remove_waldmeister_app ((c as Const (name, _)) $ x $ y) =
  if String.isPrefix waldmeister_apply name then
    remove_waldmeister_app x $ remove_waldmeister_app y
  else
    c $ remove_waldmeister_app x $ remove_waldmeister_app y
  | remove_waldmeister_app (x $ y) = remove_waldmeister_app x $ remove_waldmeister_app y
  | remove_waldmeister_app x = x

(*
  Translation from Isabelle terms to ATP terms.
*)

fun trm_to_atp'' thy (Const (x, ty)) args =
    let
      val ty_args = if is_lambda_name x orelse String.isPrefix waldmeister_apply x then
        [] else Sign.const_typargs thy (x, ty)
    in
      [ATerm ((gen_ascii_tuple (String.str const_prefix ^ encode_const (x, ty_args)), []), args)]
    end
  | trm_to_atp'' _ (Free (x, _)) args =
    [ATerm ((gen_ascii_tuple (String.str free_prefix ^ x), []), args)]
  | trm_to_atp'' _ (Var ((x, _), _)) args =
    [ATerm ((gen_ascii_tuple (String.str var_prefix ^ x), []), args)]
  | trm_to_atp'' thy (trm1 $ trm2) args = trm_to_atp'' thy trm1 (trm_to_atp'' thy trm2 [] @ args)
  | trm_to_atp'' _ _ _ = raise FailureMessage (WM_ERROR_MSG ^ "Unexpected term")

fun trm_to_atp' thy trm = trm_to_atp'' thy trm [] |> hd

fun eq_trm_to_atp thy (Const (@{const_name HOL.eq}, _) $ lhs $ rhs) =
    ATerm ((("equal", "equal"), []), [trm_to_atp' thy lhs, trm_to_atp' thy rhs])
  | eq_trm_to_atp _ _ = raise FailureMessage (WM_ERROR_MSG ^ "Non-eq term")

(* Translation from ATP terms to Isabelle terms. *)

fun construct_term thy (name, args) =
  let
    val prefix = String.sub (name, 0)
    val encoded_name = String.extract(name, 1, NONE)
    fun dummy_fun_type () = replicate (length args) dummyT ---> dummyT
  in
    if prefix = const_prefix then
      let
        val (const_name, ty_args) = if String.isPrefix waldmeister_apply encoded_name then
          (waldmeister_apply, []) else decode_const encoded_name
        val const_trans_name =
          if is_lambda_name const_name then
            lam_lift_waldmeister_prefix ^ (* ?? *)
            String.extract(const_name, size lam_lifted_poly_prefix, NONE)
          else
            const_name
      in
        Const (const_trans_name,
          if is_lambda_name const_name orelse String.isPrefix waldmeister_apply const_name then
            dummyT
          else
            Sign.const_instance thy (const_name, ty_args))
      end
    else if prefix = free_prefix then
      Free (encoded_name, dummy_fun_type ())
    else if Char.isUpper prefix then
      Var ((name, 0), dummy_fun_type ())
      (* Use name instead of encoded_name because Waldmeister renames free variables. *)
    else if name = waldmeister_equals then
      (case args of
        [_, _] => eq_const dummyT
      | _ => raise FailureMessage
        (WM_ERROR_MSG ^ "waldmeister equals needs 2 arguments but has " ^
         Int.toString (length args)))
    else if name = waldmeister_true then
      @{term True}
    else if name = waldmeister_false then
      @{term False}
    else
      raise FailureMessage
        (WM_ERROR_MSG ^ "Unknown name prefix when parsing Waldmeister proof: name = " ^ name)
  end

and atp_to_trm' thy (ATerm ((name,_), args)) =
    (case args of
      [] => construct_term thy (name, args)
     | _ => Term.list_comb (construct_term thy (name, args), map (atp_to_trm' thy) args))
     | atp_to_trm' _ _ = raise FailureMessage (WM_ERROR_MSG ^ "atp_to_trm' expects ATerm")

fun atp_to_trm thy (ATerm (("equal", _), [lhs, rhs])) =
    mk_eq (atp_to_trm' thy lhs, atp_to_trm' thy rhs)
  | atp_to_trm _ (ATerm (("$true", _), _)) = @{term True}
  | atp_to_trm _ _ = raise FailureMessage (WM_ERROR_MSG ^ "atp_to_trm expects ATerm")

fun formula_to_trm thy (AAtom aterm) = aterm |> atp_to_trm thy
  | formula_to_trm thy (AConn (ANot, [aterm])) =
    mk_not (formula_to_trm thy aterm)
  | formula_to_trm _ _ =
    raise FailureMessage (WM_ERROR_MSG ^ "formula_to_trm expects AAtom or AConn")

(* Abstract translation *)

fun mk_formula prefix_name name atype aterm =
  Formula ((prefix_name ^ ascii_of name, name), atype, AAtom aterm, NONE, [])

fun problem_lines_of_fact thy prefix (s, (_, (_, t))) =
  mk_formula (prefix ^ "0_") s Axiom (eq_trm_to_atp thy t)

fun make_nice problem = nice_atp_problem true CNF problem

fun mk_conjecture aterm =
  let
    val formula = mk_anot (AAtom aterm)
  in
    Formula ((conj_identifier, ""), Hypothesis, formula, NONE, [])
  end

fun generate_waldmeister_problem ctxt hyps_t0 concl_t0 facts0 =
  let
    val thy = Proof_Context.theory_of ctxt

    val preproc = Object_Logic.atomize_term thy

    val conditions = map preproc hyps_t0
    val consequence = preproc concl_t0
    val facts = map (apsnd preproc #> apfst fst) facts0 : (string * term) list

    fun map_ctxt' _ ctxt [] ys = (ctxt, ys)
      | map_ctxt' f ctxt (x :: xs) ys =
        let
          val (ctxt', x') = f ctxt x
        in
          map_ctxt' f ctxt' xs (x' :: ys)
        end

    fun map_ctxt f ctxt xs = map_ctxt' f ctxt xs []

    fun skolemize_fact ctxt (name, trm) =
      let
        val (ctxt', (steps, trm')) = skolemize true ctxt trm
      in
        (ctxt', (name, (steps, trm')))
      end

    fun name_list' _ [] _ = []
      | name_list' prefix (x :: xs) i = (prefix ^ Int.toString i, x) :: name_list' prefix xs (i + 1)

    fun name_list prefix xs = name_list' prefix xs 0

    (* Skolemization, hiding lambdas and translating formulas to equations *)
    val (ctxt', sko_facts) = map_ctxt skolemize_fact ctxt facts
    val (ctxt'', sko_conditions) = map_ctxt (skolemize true) ctxt' conditions

    val post_skolem = do_cheaply_conceal_lambdas []

    val sko_eq_facts0 = map (apsnd (apsnd (mk_eq_true #> apsnd post_skolem))) sko_facts
    val sko_eq_conditions0 = map (apsnd (mk_eq_true #> apsnd post_skolem)) sko_conditions
      |> name_list conjecture_condition_name
    val (_, eq_conseq as (_, (non_eq_consequence0, eq_consequence0))) =
      skolemize false ctxt'' consequence |> apsnd (apsnd (mk_eq_true #> apsnd post_skolem))

    val sko_eq_info =
      (((conj_identifier, eq_conseq) :: sko_eq_conditions0)
      @ map (apfst (fn name => fact_prefix ^ "0_" ^ name)) sko_eq_facts0)

    (* Translation of partial function applications *)
    val fun_app_info = map_minimal_app (map (snd o snd o snd) sko_eq_info)

    fun hide_partial_apps_in_last (x, (y, (z, term))) =
      (x, (y, (z, hide_partial_applications fun_app_info term)))

    val sko_eq_facts = map hide_partial_apps_in_last sko_eq_facts0
    val sko_eq_conditions = map hide_partial_apps_in_last sko_eq_conditions0
    val eq_consequence = hide_partial_applications fun_app_info eq_consequence0

    (* Problem creation *)
    val fact_lines = map (problem_lines_of_fact thy fact_prefix) sko_eq_facts
    val condition_lines =
      map (fn (name, (_, (_, trm))) =>
        mk_formula fact_prefix name Hypothesis (eq_trm_to_atp thy trm)) sko_eq_conditions
    val axiom_lines = fact_lines @ condition_lines

    val conj_line = mk_conjecture (eq_trm_to_atp thy eq_consequence)

    val helper_lemmas_needed = exists (snd #> snd #> fst #> is_some) sko_eq_facts
      orelse exists (snd #> snd #> fst #> is_some) sko_eq_conditions orelse
      is_some non_eq_consequence0

    val helper_lines =
      if helper_lemmas_needed then
        [(helpersN,
          @{thms waldmeister_fol}
          |> map (fn th => (("", (Global, General)), preproc (prop_of th)))
          |> map (fn ((s, _) ,t) => mk_formula helper_prefix s Axiom (eq_trm_to_atp thy t)))]
      else
        []

    val problem = (factsN, axiom_lines) :: helper_lines @ [(conjN, [conj_line])]

    val (nice_problem, pool) = make_nice problem
  in
    (nice_problem, Option.map snd pool |> the_default Symtab.empty, [], Symtab.empty, sko_eq_info)
  end

fun termify_line ctxt (name, role, u, rule, deps) =
  let
    val thy = Proof_Context.theory_of ctxt
    val t = u |> formula_to_trm thy |> remove_waldmeister_app
      |> singleton (infer_formulas_types ctxt)
      |> HOLogic.mk_Trueprop
  in
    (name, role, t, rule, deps)
  end

fun termify_waldmeister_proof ctxt pool =
  nasty_atp_proof pool
  #> map (termify_line ctxt)
  #> repair_waldmeister_endgame

fun get_skolem_info info names = case map (lookup info) names |> List.find is_some of
  SOME x => x |
  NONE => NONE

fun fix_name name =
  if String.isPrefix fact_prefix name andalso String.isSuffix "_J" name then
    String.extract(name, size fact_prefix + 2,NONE) |> unascii_of |>
    (fn x => fact_prefix ^ "0_" ^ x)
  else
    name

fun skolemization_steps info
  (proof_step as ((waldmeister_name, isabelle_names), _, trm, rule, _)) =
  case get_skolem_info info (map fix_name isabelle_names) of
    NONE => [proof_step] |
    SOME (_, ([], _)) => [proof_step] |
    SOME (_, (step :: steps,_)) =>
      let
        val raw_trm = dest_Trueprop trm
        val is_narrowing = raw_trm = @{term "True = False"} orelse raw_trm = @{term "False = True"}
        val is_conjecture = String.isPrefix "1.0.0.0" waldmeister_name andalso not is_narrowing
      in
        if is_narrowing then
          [proof_step]
        else
          let
            fun mk_steps _ [] = []
              | mk_steps i (x :: xs) = (((waldmeister_name ^ "_" ^  Int.toString i),[]),
                Plain, mk_Trueprop ((is_conjecture ? mk_not) x), waldmeister_skolemize_rule,
                [(waldmeister_name ^ "_" ^  Int.toString (i-1),
                    if i = 1 then isabelle_names else [])])
                :: mk_steps (i+1) xs

            val first_step = ((waldmeister_name ^ "_0", isabelle_names), Unknown,
                mk_Trueprop ((is_conjecture ? mk_not) step), rule, [])

            val sub_steps =  mk_steps 1 steps

            val skolem_steps = first_step :: sub_steps
            val num_of_steps = length skolem_steps
          in
            (skolem_steps @
            [((waldmeister_name, []), Unknown, trm, waldmeister_skolemize_rule,
            [(waldmeister_name ^ "_" ^ Int.toString (num_of_steps - 1),
                if num_of_steps = 1 then isabelle_names else [])])])
          end
      end

fun introduce_waldmeister_skolems info proof_steps = proof_steps
      |> maps (skolemization_steps info)
end;
