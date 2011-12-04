(*  Title:      HOL/Tools/Predicate_Compile/code_prolog.ML
    Author:     Lukas Bulwahn, TU Muenchen

Prototype of an code generator for logic programming languages
(a.k.a. Prolog).
*)

signature CODE_PROLOG =
sig
  datatype prolog_system = SWI_PROLOG | YAP
  type code_options =
    {ensure_groundness : bool,
     limit_globally : int option,
     limited_types : (typ * int) list,
     limited_predicates : (string list * int) list,
     replacing : ((string * string) * string) list,
     manual_reorder : ((string * int) * int list) list}
  val set_ensure_groundness : code_options -> code_options
  val map_limit_predicates : ((string list * int) list -> (string list * int) list)
    -> code_options -> code_options
  val code_options_of : theory -> code_options 
  val map_code_options : (code_options -> code_options) -> theory -> theory
  
  datatype arith_op = Plus | Minus
  datatype prol_term = Var of string | Cons of string | AppF of string * prol_term list
    | Number of int | ArithOp of arith_op * prol_term list;
  datatype prem = Conj of prem list
    | Rel of string * prol_term list | NotRel of string * prol_term list
    | Eq of prol_term * prol_term | NotEq of prol_term * prol_term
    | ArithEq of prol_term * prol_term | NotArithEq of prol_term * prol_term
    | Ground of string * typ;

  type clause = ((string * prol_term list) * prem);
  type logic_program = clause list;
  type constant_table = (string * string) list
  
  val generate : Predicate_Compile_Aux.mode option * bool ->
    Proof.context -> string -> (logic_program * constant_table)
  val write_program : logic_program -> string
  val run : (Time.time * prolog_system) -> logic_program -> (string * prol_term list) ->
    string list -> int option -> prol_term list list
  
  val active : bool Config.T
  val test_goals :
    Proof.context -> bool -> (string * typ) list -> (term * term list) list ->
      Quickcheck.result list

  val trace : bool Unsynchronized.ref
  
  val replace : ((string * string) * string) -> logic_program -> logic_program
end;

structure Code_Prolog : CODE_PROLOG =
struct

(* diagnostic tracing *)

val trace = Unsynchronized.ref false

fun tracing s = if !trace then Output.tracing s else () 

(* code generation options *)


type code_options =
  {ensure_groundness : bool,
   limit_globally : int option,
   limited_types : (typ * int) list,
   limited_predicates : (string list * int) list,
   replacing : ((string * string) * string) list,
   manual_reorder : ((string * int) * int list) list}


fun set_ensure_groundness {ensure_groundness, limit_globally, limited_types, limited_predicates,
  replacing, manual_reorder} =
  {ensure_groundness = true, limit_globally = limit_globally, limited_types = limited_types,
   limited_predicates = limited_predicates, replacing = replacing,
   manual_reorder = manual_reorder}

fun map_limit_predicates f {ensure_groundness, limit_globally, limited_types, limited_predicates,
  replacing, manual_reorder} =
  {ensure_groundness = ensure_groundness, limit_globally = limit_globally, limited_types = limited_types,
   limited_predicates = f limited_predicates, replacing = replacing,
   manual_reorder = manual_reorder}

fun merge_global_limit (NONE, NONE) = NONE
  | merge_global_limit (NONE, SOME n) = SOME n
  | merge_global_limit (SOME n, NONE) = SOME n
  | merge_global_limit (SOME n, SOME m) = SOME (Int.max (n, m))  (* FIXME odd merge *)
   
structure Options = Theory_Data
(
  type T = code_options
  val empty = {ensure_groundness = false, limit_globally = NONE,
    limited_types = [], limited_predicates = [], replacing = [], manual_reorder = []}
  val extend = I;
  fun merge
    ({ensure_groundness = ensure_groundness1, limit_globally = limit_globally1,
      limited_types = limited_types1, limited_predicates = limited_predicates1,
      replacing = replacing1, manual_reorder = manual_reorder1},
     {ensure_groundness = ensure_groundness2, limit_globally = limit_globally2,
      limited_types = limited_types2, limited_predicates = limited_predicates2,
      replacing = replacing2, manual_reorder = manual_reorder2}) =
    {ensure_groundness = ensure_groundness1 orelse ensure_groundness2 (* FIXME odd merge *),
     limit_globally = merge_global_limit (limit_globally1, limit_globally2),
     limited_types = AList.merge (op =) (K true) (limited_types1, limited_types2),
     limited_predicates = AList.merge (op =) (K true) (limited_predicates1, limited_predicates2),
     manual_reorder = AList.merge (op =) (K true) (manual_reorder1, manual_reorder2),
     replacing = Library.merge (op =) (replacing1, replacing2)};
);

val code_options_of = Options.get

val map_code_options = Options.map

(* system configuration *)

datatype prolog_system = SWI_PROLOG | YAP

fun string_of_system SWI_PROLOG = "swiprolog"
  | string_of_system YAP = "yap"

type system_configuration = {timeout : Time.time, prolog_system : prolog_system}
                                                
structure System_Config = Generic_Data
(
  type T = system_configuration
  val empty = {timeout = seconds 10.0, prolog_system = SWI_PROLOG}
  val extend = I;
  fun merge (a, _) = a
)

(* general string functions *)

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o raw_explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o raw_explode;

(* internal program representation *)

datatype arith_op = Plus | Minus

datatype prol_term = Var of string | Cons of string | AppF of string * prol_term list
  | Number of int | ArithOp of arith_op * prol_term list;

fun dest_Var (Var v) = v

fun add_vars (Var v) = insert (op =) v
  | add_vars (ArithOp (_, ts)) = fold add_vars ts
  | add_vars (AppF (_, ts)) = fold add_vars ts
  | add_vars _ = I

fun map_vars f (Var v) = Var (f v)
  | map_vars f (ArithOp (opr, ts)) = ArithOp (opr, map (map_vars f) ts)
  | map_vars f (AppF (fs, ts)) = AppF (fs, map (map_vars f) ts)
  | map_vars f t = t
  
fun maybe_AppF (c, []) = Cons c
  | maybe_AppF (c, xs) = AppF (c, xs)

fun is_Var (Var _) = true
  | is_Var _ = false

fun is_arith_term (Var _) = true
  | is_arith_term (Number _) = true
  | is_arith_term (ArithOp (_, operands)) = forall is_arith_term operands
  | is_arith_term _ = false

fun string_of_prol_term (Var s) = "Var " ^ s
  | string_of_prol_term (Cons s) = "Cons " ^ s
  | string_of_prol_term (AppF (f, args)) = f ^ "(" ^ commas (map string_of_prol_term args) ^ ")" 
  | string_of_prol_term (Number n) = "Number " ^ string_of_int n

datatype prem = Conj of prem list
  | Rel of string * prol_term list | NotRel of string * prol_term list
  | Eq of prol_term * prol_term | NotEq of prol_term * prol_term
  | ArithEq of prol_term * prol_term | NotArithEq of prol_term * prol_term
  | Ground of string * typ;

fun dest_Rel (Rel (c, ts)) = (c, ts)

fun map_term_prem f (Conj prems) = Conj (map (map_term_prem f) prems)
  | map_term_prem f (Rel (r, ts)) = Rel (r, map f ts)
  | map_term_prem f (NotRel (r, ts)) = NotRel (r, map f ts)
  | map_term_prem f (Eq (l, r)) = Eq (f l, f r)
  | map_term_prem f (NotEq (l, r)) = NotEq (f l, f r)
  | map_term_prem f (ArithEq (l, r)) = ArithEq (f l, f r)
  | map_term_prem f (NotArithEq (l, r)) = NotArithEq (f l, f r)
  | map_term_prem f (Ground (v, T)) = Ground (dest_Var (f (Var v)), T)

fun fold_prem_terms f (Conj prems) = fold (fold_prem_terms f) prems
  | fold_prem_terms f (Rel (_, ts)) = fold f ts
  | fold_prem_terms f (NotRel (_, ts)) = fold f ts
  | fold_prem_terms f (Eq (l, r)) = f l #> f r
  | fold_prem_terms f (NotEq (l, r)) = f l #> f r
  | fold_prem_terms f (ArithEq (l, r)) = f l #> f r
  | fold_prem_terms f (NotArithEq (l, r)) = f l #> f r
  | fold_prem_terms f (Ground (v, T)) = f (Var v)
  
type clause = ((string * prol_term list) * prem);

type logic_program = clause list;
 
(* translation from introduction rules to internal representation *)

fun mk_conform f empty avoid name =
  let
    fun dest_Char (Symbol.Char c) = c
    val name' = space_implode "" (map (dest_Char o Symbol.decode)
      (filter (fn s => Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s)
        (Symbol.explode name)))
    val name'' = f (if name' = "" then empty else name')
  in if member (op =) avoid name'' then singleton (Name.variant_list avoid) name'' else name'' end

(** constant table **)

type constant_table = (string * string) list

fun declare_consts consts constant_table =
  let
    fun update' c table =
      if AList.defined (op =) table c then table else
        let
          val c' = mk_conform first_lower "pred" (map snd table) (Long_Name.base_name c)
        in
          AList.update (op =) (c, c') table
        end
  in
    fold update' consts constant_table
  end
  
fun translate_const constant_table c =
  case AList.lookup (op =) constant_table c of
    SOME c' => c'
  | NONE => error ("No such constant: " ^ c)

fun inv_lookup _ [] _ = NONE
  | inv_lookup eq ((key, value)::xs) value' =
      if eq (value', value) then SOME key
      else inv_lookup eq xs value';

fun restore_const constant_table c =
  case inv_lookup (op =) constant_table c of
    SOME c' => c'
  | NONE => error ("No constant corresponding to "  ^ c)

(** translation of terms, literals, premises, and clauses **)

fun translate_arith_const @{const_name "Groups.plus_class.plus"} = SOME Plus
  | translate_arith_const @{const_name "Groups.minus_class.minus"} = SOME Minus
  | translate_arith_const _ = NONE

fun mk_nat_term constant_table n =
  let
    val zero = translate_const constant_table @{const_name "Groups.zero_class.zero"}
    val Suc = translate_const constant_table @{const_name "Suc"}
  in funpow n (fn t => AppF (Suc, [t])) (Cons zero) end

fun translate_term ctxt constant_table t =
  case try HOLogic.dest_number t of
    SOME (@{typ "int"}, n) => Number n
  | SOME (@{typ "nat"}, n) => mk_nat_term constant_table n
  | NONE =>
      (case strip_comb t of
        (Free (v, T), []) => Var v 
      | (Const (c, _), []) => Cons (translate_const constant_table c)
      | (Const (c, _), args) =>
        (case translate_arith_const c of
          SOME aop => ArithOp (aop, map (translate_term ctxt constant_table) args)
        | NONE =>                                                             
            AppF (translate_const constant_table c, map (translate_term ctxt constant_table) args))
      | _ => error ("illegal term for translation: " ^ Syntax.string_of_term ctxt t))

fun translate_literal ctxt constant_table t =
  case strip_comb t of
    (Const (@{const_name HOL.eq}, _), [l, r]) =>
      let
        val l' = translate_term ctxt constant_table l
        val r' = translate_term ctxt constant_table r
      in
        (if is_Var l' andalso is_arith_term r' andalso not (is_Var r') then ArithEq else Eq) (l', r')
      end
  | (Const (c, _), args) =>
      Rel (translate_const constant_table c, map (translate_term ctxt constant_table) args)
  | _ => error ("illegal literal for translation: " ^ Syntax.string_of_term ctxt t)

fun NegRel_of (Rel lit) = NotRel lit
  | NegRel_of (Eq eq) = NotEq eq
  | NegRel_of (ArithEq eq) = NotArithEq eq

fun mk_groundness_prems t = map Ground (Term.add_frees t [])
  
fun translate_prem ensure_groundness ctxt constant_table t =  
    case try HOLogic.dest_not t of
      SOME t =>
        if ensure_groundness then
          Conj (mk_groundness_prems t @ [NegRel_of (translate_literal ctxt constant_table t)])
        else
          NegRel_of (translate_literal ctxt constant_table t)
    | NONE => translate_literal ctxt constant_table t
    
fun imp_prems_conv cv ct =
  case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => Conv.combination_conv (Conv.arg_conv cv) (imp_prems_conv cv) ct
  | _ => Conv.all_conv ct

fun Trueprop_conv cv ct =
  case Thm.term_of ct of
    Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv cv ct  
  | _ => raise Fail "Trueprop_conv"

fun preprocess_intro thy rule =
  Conv.fconv_rule
    (imp_prems_conv
      (Trueprop_conv (Conv.try_conv (Conv.rewr_conv @{thm Predicate.eq_is_eq}))))
    (Thm.transfer thy rule)

fun translate_intros ensure_groundness ctxt gr const constant_table =
  let
    val intros = map (preprocess_intro (Proof_Context.theory_of ctxt)) (Graph.get_node gr const)
    val (intros', ctxt') = Variable.import_terms true (map prop_of intros) ctxt
    val constant_table' = declare_consts (fold Term.add_const_names intros' []) constant_table
    fun translate_intro intro =
      let
        val head = HOLogic.dest_Trueprop (Logic.strip_imp_concl intro)
        val prems = map HOLogic.dest_Trueprop (Logic.strip_imp_prems intro)
        val prems' = Conj (map (translate_prem ensure_groundness ctxt' constant_table') prems)
        val clause = (dest_Rel (translate_literal ctxt' constant_table' head), prems')
      in clause end
  in
    (map translate_intro intros', constant_table')
  end

fun depending_preds_of (key, intros) =
  fold Term.add_const_names (map Thm.prop_of intros) []

fun add_edges edges_of key G =
  let
    fun extend' key (G, visited) = 
      case try (Graph.get_node G) key of
          SOME v =>
            let
              val new_edges = filter (fn k => is_some (try (Graph.get_node G) k)) (edges_of (key, v))
              val (G', visited') = fold extend'
                (subtract (op =) (key :: visited) new_edges) (G, key :: visited)
            in
              (fold (Graph.add_edge o (pair key)) new_edges G', visited')
            end
        | NONE => (G, visited)
  in
    fst (extend' key (G, []))
  end

fun print_intros ctxt gr consts =
  tracing (cat_lines (map (fn const =>
    "Constant " ^ const ^ "has intros:\n" ^
    cat_lines (map (Display.string_of_thm ctxt) (Graph.get_node gr const))) consts))

(* translation of moded predicates *)

(** generating graph of moded predicates **)

(* could be moved to Predicate_Compile_Core *)
fun requires_modes polarity cls =
  let
    fun req_mode_of pol (t, derivation) =
      (case fst (strip_comb t) of
        Const (c, _) => SOME (c, (pol, Predicate_Compile_Core.head_mode_of derivation))
      | _ => NONE)
    fun req (Predicate_Compile_Aux.Prem t, derivation) = req_mode_of polarity (t, derivation)
      | req (Predicate_Compile_Aux.Negprem t, derivation) = req_mode_of (not polarity) (t, derivation)
      | req _ = NONE
  in      
    maps (fn (_, prems) => map_filter req prems) cls
  end
 
structure Mode_Graph = Graph(type key = string * (bool * Predicate_Compile_Aux.mode)
  val ord = prod_ord fast_string_ord (prod_ord bool_ord Predicate_Compile_Aux.mode_ord));

fun mk_moded_clauses_graph ctxt scc gr =
  let
    val options = Predicate_Compile_Aux.default_options
    val mode_analysis_options =
      {use_generators = true, reorder_premises = true, infer_pos_and_neg_modes = true}
    fun infer prednames (gr, (pos_modes, neg_modes, random)) =
      let
        val (lookup_modes, lookup_neg_modes, needs_random) =
          ((fn s => the (AList.lookup (op =) pos_modes s)),
           (fn s => the (AList.lookup (op =) neg_modes s)),
           (fn s => member (op =) (the (AList.lookup (op =) random s))))
        val (preds, all_vs, param_vs, all_modes, clauses) =
          Predicate_Compile_Core.prepare_intrs options ctxt prednames
            (maps (Core_Data.intros_of ctxt) prednames)
        val ((moded_clauses, random'), _) =
          Mode_Inference.infer_modes mode_analysis_options options 
            (lookup_modes, lookup_neg_modes, needs_random) ctxt preds all_modes param_vs clauses
        val modes = map (fn (p, mps) => (p, map fst mps)) moded_clauses
        val pos_modes' = map (apsnd (map_filter (fn (true, m) => SOME m | _ => NONE))) modes
        val neg_modes' = map (apsnd (map_filter (fn (false, m) => SOME m | _ => NONE))) modes
        val _ = tracing ("Inferred modes:\n" ^
          cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
            (fn (p, m) => Predicate_Compile_Aux.string_of_mode m ^ (if p then "pos" else "neg")) ms)) modes))
        val gr' = gr
          |> fold (fn (p, mps) => fold (fn (mode, cls) =>
                Mode_Graph.new_node ((p, mode), cls)) mps)
            moded_clauses
          |> fold (fn (p, mps) => fold (fn (mode, cls) => fold (fn req =>
              Mode_Graph.add_edge ((p, mode), req)) (requires_modes (fst mode) cls)) mps)
            moded_clauses
      in
        (gr', (AList.merge (op =) (op =) (pos_modes, pos_modes'),
          AList.merge (op =) (op =) (neg_modes, neg_modes'),
          AList.merge (op =) (op =) (random, random')))
      end
  in  
    fst (fold infer (rev scc) (Mode_Graph.empty, ([], [], []))) 
  end

fun declare_moded_predicate moded_preds table =
  let
    fun update' (p as (pred, (pol, mode))) table =
      if AList.defined (op =) table p then table else
        let
          val name = Long_Name.base_name pred ^ (if pol then "p" else "n")
            ^ Predicate_Compile_Aux.ascii_string_of_mode mode
          val p' = mk_conform first_lower "pred" (map snd table) name
        in
          AList.update (op =) (p, p') table
        end
  in
    fold update' moded_preds table
  end

fun mk_program ctxt moded_gr moded_preds (prog, (moded_pred_table, constant_table)) =
  let
    val moded_pred_table' = declare_moded_predicate moded_preds moded_pred_table
    fun mk_literal pol derivation constant_table' t =
      let
        val (p, args) = strip_comb t
        val mode = Predicate_Compile_Core.head_mode_of derivation 
        val name = fst (dest_Const p)
        
        val p' = the (AList.lookup (op =) moded_pred_table' (name, (pol, mode)))
        val args' = map (translate_term ctxt constant_table') args
      in
        Rel (p', args')
      end
    fun mk_prem pol (indprem, derivation) constant_table =
      case indprem of
        Predicate_Compile_Aux.Generator (s, T) => (Ground (s, T), constant_table)
      | _ =>
        declare_consts (Term.add_const_names (Predicate_Compile_Aux.dest_indprem indprem) []) constant_table
        |> (fn constant_table' =>
          (case indprem of Predicate_Compile_Aux.Negprem t =>
            NegRel_of (mk_literal (not pol) derivation constant_table' t)
          | _ =>
            mk_literal pol derivation constant_table' (Predicate_Compile_Aux.dest_indprem indprem), constant_table'))
    fun mk_clause pred_name pol (ts, prems) (prog, constant_table) =
    let
      val constant_table' = declare_consts (fold Term.add_const_names ts []) constant_table
      val args = map (translate_term ctxt constant_table') ts
      val (prems', constant_table'') = fold_map (mk_prem pol) prems constant_table'
    in
      (((pred_name, args), Conj prems') :: prog, constant_table'')
    end
    fun mk_clauses (pred, mode as (pol, _)) =
      let
        val clauses = Mode_Graph.get_node moded_gr (pred, mode)
        val pred_name = the (AList.lookup (op =) moded_pred_table' (pred, mode))
      in
        fold (mk_clause pred_name pol) clauses
      end
  in
    apsnd (pair moded_pred_table') (fold mk_clauses moded_preds (prog, constant_table))
  end

fun generate (use_modes, ensure_groundness) ctxt const =
  let 
    fun strong_conn_of gr keys =
      Graph.strong_conn (Graph.subgraph (member (op =) (Graph.all_succs gr keys)) gr)
    val gr = Core_Data.intros_graph_of ctxt
    val gr' = add_edges depending_preds_of const gr
    val scc = strong_conn_of gr' [const]
    val initial_constant_table = 
      declare_consts [@{const_name "Groups.zero_class.zero"}, @{const_name "Suc"}] []
  in
    case use_modes of
      SOME mode =>
        let
          val moded_gr = mk_moded_clauses_graph ctxt scc gr
          val moded_gr' = Mode_Graph.subgraph
            (member (op =) (Mode_Graph.all_succs moded_gr [(const, (true, mode))])) moded_gr
          val scc = Mode_Graph.strong_conn moded_gr' 
        in
          apfst rev (apsnd snd
            (fold (mk_program ctxt moded_gr') (rev scc) ([], ([], initial_constant_table))))
        end
      | NONE =>
        let 
          val _ = print_intros ctxt gr (flat scc)
          val constant_table = declare_consts (flat scc) initial_constant_table
        in
          apfst flat (fold_map (translate_intros ensure_groundness ctxt gr) (flat scc) constant_table)
        end
  end
  
(* implementation for fully enumerating predicates and
  for size-limited predicates for enumerating the values of a datatype upto a specific size *)

fun add_ground_typ (Conj prems) = fold add_ground_typ prems
  | add_ground_typ (Ground (_, T)) = insert (op =) T
  | add_ground_typ _ = I

fun mk_relname (Type (Tcon, Targs)) =
  first_lower (Long_Name.base_name Tcon) ^ space_implode "_" (map mk_relname Targs)
  | mk_relname _ = raise Fail "unexpected type"

fun mk_lim_relname T = "lim_" ^  mk_relname T

(* This is copied from "pat_completeness.ML" *)
fun inst_constrs_of thy (T as Type (name, _)) =
  map (fn (Cn,CT) =>
    Envir.subst_term_types (Sign.typ_match thy (body_type CT, T) Vartab.empty) (Const (Cn, CT)))
    (the (Datatype.get_constrs thy name))
  | inst_constrs_of thy T = raise TYPE ("inst_constrs_of", [T], [])

fun is_recursive_constr T (Const (constr_name, T')) = member (op =) (binder_types T') T
  
fun mk_ground_impl ctxt limited_types (T as Type (Tcon, Targs)) (seen, constant_table) =
  if member (op =) seen T then ([], (seen, constant_table))
  else
    let
      val (limited, size) = case AList.lookup (op =) limited_types T of
        SOME s => (true, s)
      | NONE => (false, 0)      
      val rel_name = (if limited then mk_lim_relname else mk_relname) T
      fun mk_impl (Const (constr_name, cT), recursive) (seen, constant_table) =
        let
          val constant_table' = declare_consts [constr_name] constant_table
          val Ts = binder_types cT
          val (rec_clauses, (seen', constant_table'')) =
            fold_map (mk_ground_impl ctxt limited_types) Ts (seen, constant_table')
          val vars = map (fn i => Var ("x" ^ string_of_int i)) (1 upto (length Ts))
          val lim_var =
            if limited then
              if recursive then [AppF ("suc", [Var "Lim"])]              
              else [Var "Lim"]
            else [] 
          fun mk_prem v T' =
            if limited andalso T' = T then Rel (mk_lim_relname T', [Var "Lim", v])
            else Rel (mk_relname T', [v])
          val clause =
            ((rel_name, lim_var @ [maybe_AppF (translate_const constant_table'' constr_name, vars)]),
             Conj (map2 mk_prem vars Ts))
        in
          (clause :: flat rec_clauses, (seen', constant_table''))
        end
      val constrs = inst_constrs_of (Proof_Context.theory_of ctxt) T
      val constrs' = (constrs ~~ map (is_recursive_constr T) constrs)
        |> (fn cs => filter_out snd cs @ filter snd cs)
      val (clauses, constant_table') =
        apfst flat (fold_map mk_impl constrs' (T :: seen, constant_table))
      val size_term = funpow size (fn t => AppF ("suc", [t])) (Cons "zero")
    in
      ((if limited then
        cons ((mk_relname T, [Var "x"]), Rel (mk_lim_relname T, [size_term, Var "x"]))
      else I) clauses, constant_table')
    end
 | mk_ground_impl ctxt _ T (seen, constant_table) =
   raise Fail ("unexpected type :" ^ Syntax.string_of_typ ctxt T)

fun replace_ground (Conj prems) = Conj (map replace_ground prems)
  | replace_ground (Ground (x, T)) =
    Rel (mk_relname T, [Var x])  
  | replace_ground p = p
  
fun add_ground_predicates ctxt limited_types (p, constant_table) =
  let
    val ground_typs = fold (add_ground_typ o snd) p []
    val (grs, (_, constant_table')) = fold_map (mk_ground_impl ctxt limited_types) ground_typs ([], constant_table)
    val p' = map (apsnd replace_ground) p
  in
    ((flat grs) @ p', constant_table')
  end

(* make depth-limited version of predicate *)

fun mk_lim_rel_name rel_name = "lim_" ^ rel_name

fun mk_depth_limited rel_names ((rel_name, ts), prem) =
  let
    fun has_positive_recursive_prems (Conj prems) = exists has_positive_recursive_prems prems
      | has_positive_recursive_prems (Rel (rel, ts)) = member (op =) rel_names rel
      | has_positive_recursive_prems _ = false
    fun mk_lim_prem (Conj prems) = Conj (map mk_lim_prem prems)
      | mk_lim_prem (p as Rel (rel, ts)) =
        if member (op =) rel_names rel then Rel (mk_lim_rel_name rel, Var "Lim" :: ts) else p
      | mk_lim_prem p = p
  in
    if has_positive_recursive_prems prem then
      ((mk_lim_rel_name rel_name, (AppF ("suc", [Var "Lim"]))  :: ts), mk_lim_prem prem)
    else
      ((mk_lim_rel_name rel_name, (Var "Lim") :: ts), prem)
  end

fun nat_term_of n = funpow n (fn t => AppF ("suc", [t])) (Cons "zero")

fun add_limited_predicates limited_predicates (p, constant_table) =
  let                                     
    fun add (rel_names, limit) p = 
      let
        val clauses = filter (fn ((rel, _), _) => member (op =) rel_names rel) p
        val clauses' = map (mk_depth_limited rel_names) clauses
        fun mk_entry_clause rel_name =
          let
            val nargs = length (snd (fst
              (the (find_first (fn ((rel, _), _) => rel = rel_name) clauses))))
            val vars = map (fn i => Var ("x" ^ string_of_int i)) (1 upto nargs)        
          in
            (("limited_" ^ rel_name, vars), Rel ("lim_" ^ rel_name, nat_term_of limit :: vars))
          end
      in (p @ (map mk_entry_clause rel_names) @ clauses') end
  in
    (fold add limited_predicates p, constant_table)
  end


(* replace predicates in clauses *)

(* replace (A, B, C) p = replace A by B in clauses of C *)
fun replace ((from, to), location) p =
  let
    fun replace_prem (Conj prems) = Conj (map replace_prem prems)
      | replace_prem (r as Rel (rel, ts)) =
          if rel = from then Rel (to, ts) else r
      | replace_prem r = r
  in
    map (fn ((rel, args), prem) => ((rel, args), (if rel = location then replace_prem else I) prem)) p
  end

  
(* reorder manually : reorder premises of ith clause of predicate p by a permutation perm *)

fun reorder_manually reorder p =
  let
    fun reorder' (clause as ((rel, args), prem)) seen =
      let
        val seen' = AList.map_default (op =) (rel, 0) (fn x => x + 1) seen
        val i = the (AList.lookup (op =) seen' rel)
        val perm = AList.lookup (op =) reorder (rel, i)
        val prem' = (case perm of 
          SOME p => (case prem of Conj prems => Conj (map (nth prems) p) | _ => prem)
        | NONE => prem)
      in (((rel, args), prem'), seen') end
  in
    fst (fold_map reorder' p [])
  end

(* rename variables to prolog-friendly names *)

fun rename_vars_term renaming = map_vars (fn v => the (AList.lookup (op =) renaming v))

fun rename_vars_prem renaming = map_term_prem (rename_vars_term renaming)

fun is_prolog_conform v =
  forall (fn s => Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s) (Symbol.explode v)
  
fun mk_renaming v renaming =
  (v, mk_conform first_upper "Var" (map snd renaming) v) :: renaming

fun rename_vars_clause ((rel, args), prem) =
  let
    val vars = fold_prem_terms add_vars prem (fold add_vars args [])
    val renaming = fold mk_renaming vars []
  in ((rel, map (rename_vars_term renaming) args), rename_vars_prem renaming prem) end
  
val rename_vars_program = map rename_vars_clause

(* limit computation globally by some threshold *)

fun limit_globally ctxt limit const_name (p, constant_table) =
  let
    val rel_names = fold (fn ((r, _), _) => insert (op =) r) p []
    val p' = map (mk_depth_limited rel_names) p
    val rel_name = translate_const constant_table const_name
    val nargs = length (snd (fst
      (the (find_first (fn ((rel, _), _) => rel = rel_name) p))))
    val vars = map (fn i => Var ("x" ^ string_of_int i)) (1 upto nargs)
    val entry_clause = ((rel_name, vars), Rel ("lim_" ^ rel_name, nat_term_of limit :: vars))
    val p'' = filter_out (fn ((rel, _), _) => rel = rel_name) p
  in
    (entry_clause :: p' @ p'', constant_table)
  end

(* post processing of generated prolog program *)

fun post_process ctxt options const_name (p, constant_table) =
  (p, constant_table)
  |> (case #limit_globally options of
        SOME limit => limit_globally ctxt limit const_name
      | NONE => I)
  |> (if #ensure_groundness options then
        add_ground_predicates ctxt (#limited_types options)
      else I)
  |> tap (fn _ => tracing "Adding limited predicates...")
  |> add_limited_predicates (#limited_predicates options)
  |> tap (fn _ => tracing "Replacing predicates...")
  |> apfst (fold replace (#replacing options))
  |> apfst (reorder_manually (#manual_reorder options))
  |> apfst rename_vars_program

(* code printer *)

fun write_arith_op Plus = "+"
  | write_arith_op Minus = "-"

fun write_term (Var v) = v
  | write_term (Cons c) = c
  | write_term (AppF (f, args)) = f ^ "(" ^ space_implode ", " (map write_term args) ^ ")"
  | write_term (ArithOp (oper, [a1, a2])) = write_term a1 ^ " " ^ write_arith_op oper ^ " " ^ write_term a2
  | write_term (Number n) = string_of_int n

fun write_rel (pred, args) =
  pred ^ "(" ^ space_implode ", " (map write_term args) ^ ")" 

fun write_prem (Conj prems) = space_implode ", " (map write_prem prems)
  | write_prem (Rel p) = write_rel p  
  | write_prem (NotRel p) = "not(" ^ write_rel p ^ ")"
  | write_prem (Eq (l, r)) = write_term l ^ " = " ^ write_term r
  | write_prem (NotEq (l, r)) = write_term l ^ " \\= " ^ write_term r
  | write_prem (ArithEq (l, r)) = write_term l ^ " is " ^ write_term r
  | write_prem (NotArithEq (l, r)) = write_term l ^ " =\\= " ^ write_term r
  | write_prem _ = raise Fail "Not a valid prolog premise"

fun write_clause (head, prem) =
  write_rel head ^ (if prem = Conj [] then "." else " :- " ^ write_prem prem ^ ".")

fun write_program p =
  cat_lines (map write_clause p) 

(* query templates *)

(** query and prelude for swi-prolog **)

fun swi_prolog_query_first (rel, args) vnames =
  "eval :- once("  ^ rel ^ "(" ^ space_implode ", " (map write_term args) ^ ")),\n" ^
  "writef('" ^ space_implode ";" (map (fn v => v ^ " = %w") vnames) ^
  "\\n', [" ^ space_implode ", " vnames ^ "]).\n"
  
fun swi_prolog_query_firstn n (rel, args) vnames =
  "eval :- findnsols(" ^ string_of_int n ^ ", (" ^ space_implode ", " vnames ^ "), " ^
    rel ^ "(" ^ space_implode ", " (map write_term args) ^ "), Sols), writelist(Sols).\n" ^
    "writelist([]).\n" ^
    "writelist([(" ^ space_implode ", " vnames ^ ")|SolutionTail]) :- " ^
    "writef('" ^ space_implode ";" (map (fn v => v ^ " = %w") vnames) ^
    "\\n', [" ^ space_implode ", " vnames ^ "]), writelist(SolutionTail).\n"
  
val swi_prolog_prelude =
  "#!/usr/bin/swipl -q -t main -f\n\n" ^  (* FIXME hardwired executable!? *)
  ":- use_module(library('dialect/ciao/aggregates')).\n" ^
  ":- style_check(-singleton).\n" ^
  ":- style_check(-discontiguous).\n" ^
  ":- style_check(-atom).\n\n" ^
  "main :- catch(eval, E, (print_message(error, E), fail)), halt.\n" ^
  "main :- halt(1).\n"

(** query and prelude for yap **)

fun yap_query_first (rel, args) vnames =
  "eval :- once(" ^ rel ^ "(" ^ space_implode ", " (map write_term args) ^ ")),\n" ^
  "format('" ^ space_implode ";" (map (fn v => v ^ " = ~w") vnames) ^
  "\\n', [" ^ space_implode ", " vnames ^ "]).\n"

val yap_prelude =
  "#!/usr/bin/yap -L\n\n" ^
  ":- initialization(eval).\n"

(* system-dependent query, prelude and invocation *)

fun query system nsols = 
  case system of
    SWI_PROLOG =>
      (case nsols of NONE => swi_prolog_query_first | SOME n => swi_prolog_query_firstn n)
  | YAP =>
      case nsols of NONE => yap_query_first | SOME n =>
        error "No support for querying multiple solutions in the prolog system yap"

fun prelude system =
  case system of SWI_PROLOG => swi_prolog_prelude | YAP => yap_prelude

fun invoke system file =
  let
    val (env_var, cmd) =
      (case system of
        SWI_PROLOG => ("ISABELLE_SWIPL", "\"$ISABELLE_SWIPL\" -f ")
      | YAP => ("ISABELLE_YAP", "\"$ISABELLE_YAP\" -L "))
  in
    if getenv env_var = "" then
      (warning (env_var ^ " not set; could not execute code for " ^ string_of_system system); "")
    else fst (Isabelle_System.bash_output (cmd ^ File.shell_path file))
  end


(* parsing prolog solution *)

val scan_number =
  Scan.many1 Symbol.is_ascii_digit

val scan_atom =
  Scan.many1 (fn s => Symbol.is_ascii_lower s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s)

val scan_var =
  Scan.many1
    (fn s => Symbol.is_ascii_upper s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s)

val scan_ident =
  Scan.repeat (Scan.one
    (fn s => Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s))

fun dest_Char (Symbol.Char s) = s

val string_of = implode o map (dest_Char o Symbol.decode)

val is_atom_ident = forall Symbol.is_ascii_lower

val is_var_ident =
  forall (fn s => Symbol.is_ascii_upper s orelse Symbol.is_ascii_digit s orelse Symbol.is_ascii_quasi s)

fun int_of_symbol_list xs = fold (fn x => fn s => s * 10 + (ord x - ord "0")) xs 0

fun scan_terms xs = (((scan_term --| $$ ",") ::: scan_terms)
  || (scan_term >> single)) xs
and scan_term xs =
  ((scan_number >> (Number o int_of_symbol_list))
  || (scan_var >> (Var o string_of))
  || ((scan_atom -- ($$ "(" |-- scan_terms --| $$ ")"))
    >> (fn (f, ts) => AppF (string_of f, ts)))
  || (scan_atom >> (Cons o string_of))) xs

val parse_term = fst o Scan.finite Symbol.stopper
    (Scan.error (!! (fn _ => raise Fail "parsing prolog output failed")) scan_term)
  o raw_explode
  
fun parse_solutions sol =
  let
    fun dest_eq s = case space_explode "=" s of
        (l :: r :: []) => parse_term (unprefix " " r)
      | _ => raise Fail "unexpected equation in prolog output"
    fun parse_solution s = map dest_eq (space_explode ";" s)
    val sols = case space_explode "\n" sol of [] => [] | s => fst (split_last s)  
  in
    map parse_solution sols
  end 
  
(* calling external interpreter and getting results *)

fun run (timeout, system) p (query_rel, args) vnames nsols =
  let
    val renaming = fold mk_renaming (fold add_vars args vnames) [] 
    val vnames' = map (fn v => the (AList.lookup (op =) renaming v)) vnames
    val args' = map (rename_vars_term renaming) args
    val prog = prelude system ^ query system nsols (query_rel, args') vnames' ^ write_program p
    val _ = tracing ("Generated prolog program:\n" ^ prog)
    val solution = TimeLimit.timeLimit timeout (fn prog =>
      Isabelle_System.with_tmp_file "prolog_file" "" (fn prolog_file =>
        (File.write prolog_file prog; invoke system prolog_file))) prog
    val _ = tracing ("Prolog returned solution(s):\n" ^ solution)
    val tss = parse_solutions solution
  in
    tss
  end

(* restoring types in terms *)

fun restore_term ctxt constant_table (Var s, T) = Free (s, T)
  | restore_term ctxt constant_table (Number n, @{typ "int"}) = HOLogic.mk_number @{typ "int"} n
  | restore_term ctxt constant_table (Number n, _) = raise (Fail "unexpected type for number") 
  | restore_term ctxt constant_table (Cons s, T) = Const (restore_const constant_table s, T)
  | restore_term ctxt constant_table (AppF (f, args), T) =
    let
      val thy = Proof_Context.theory_of ctxt
      val c = restore_const constant_table f
      val cT = Sign.the_const_type thy c
      val (argsT, resT) = strip_type cT
      val subst = Sign.typ_match thy (resT, T) Vartab.empty
      val argsT' = map (Envir.subst_type subst) argsT
    in
      list_comb (Const (c, Envir.subst_type subst cT),
        map (restore_term ctxt constant_table) (args ~~ argsT'))
    end

    
(* restore numerals in natural numbers *)

fun restore_nat_numerals t =
  if fastype_of t = @{typ nat} andalso is_some (try HOLogic.dest_nat t) then
    HOLogic.mk_number @{typ nat} (HOLogic.dest_nat t)
  else
    (case t of
        t1 $ t2 => restore_nat_numerals t1 $ restore_nat_numerals t2
      | t => t)
  
(* values command *)

val preprocess_options = Predicate_Compile_Aux.Options {
  expected_modes = NONE,
  proposed_modes = [],
  proposed_names = [],
  show_steps = false,
  show_intermediate_results = false,
  show_proof_trace = false,
  show_modes = false,
  show_mode_inference = false,
  show_compilation = false,
  show_caught_failures = false,
  show_invalid_clauses = false,
  skip_proof = true,
  no_topmost_reordering = false,
  function_flattening = true,
  specialise = false,
  fail_safe_function_flattening = false,
  no_higher_order_predicate = [],
  inductify = false,
  detect_switches = true,
  smart_depth_limiting = true,
  compilation = Predicate_Compile_Aux.Pred
}

fun values ctxt soln t_compr =
  let
    val options = code_options_of (Proof_Context.theory_of ctxt)
    val split = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term ctxt t_compr);
    val (body, Ts, fp) = HOLogic.strip_psplits split;
    val output_names = Name.variant_list (Term.add_free_names body [])
      (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
    val output_frees = rev (map2 (curry Free) output_names Ts)
    val body = subst_bounds (output_frees, body)
    val (pred as Const (name, T), all_args) =
      case strip_comb body of
        (Const (name, T), all_args) => (Const (name, T), all_args)
      | (head, _) => error ("Not a constant: " ^ Syntax.string_of_term ctxt head)
    val _ = tracing "Preprocessing specification..."
    val T = Sign.the_const_type (Proof_Context.theory_of ctxt) name
    val t = Const (name, T)
    val thy' =
      Theory.copy (Proof_Context.theory_of ctxt)
      |> Predicate_Compile.preprocess preprocess_options t
    val ctxt' = Proof_Context.init_global thy'
    val _ = tracing "Generating prolog program..."
    val (p, constant_table) = generate (NONE, #ensure_groundness options) ctxt' name (* FIXME *)
      |> post_process ctxt' options name
    val constant_table' = declare_consts (fold Term.add_const_names all_args []) constant_table
    val args' = map (translate_term ctxt constant_table') all_args
    val _ = tracing "Running prolog program..."
    val system_config = System_Config.get (Context.Proof ctxt)
    val tss = run (#timeout system_config, #prolog_system system_config)
      p (translate_const constant_table' name, args') output_names soln
    val _ = tracing "Restoring terms..."
    val empty = Const("Orderings.bot_class.bot", fastype_of t_compr)
    fun mk_insert x S =
      Const (@{const_name "Set.insert"}, fastype_of x --> fastype_of S --> fastype_of S) $ x $ S 
    fun mk_set_compr in_insert [] xs =
       rev ((Free ("dots", fastype_of t_compr)) ::  (* FIXME proper name!? *)
        (if null in_insert then xs else (fold mk_insert in_insert empty) :: xs))
      | mk_set_compr in_insert (t :: ts) xs =
        let
          val frees = Term.add_frees t []
        in
          if null frees then
            mk_set_compr (t :: in_insert) ts xs
          else
            let
              val uu as (uuN, uuT) = singleton (Variable.variant_frees ctxt' [t]) ("uu", fastype_of t)
              val set_compr =
                HOLogic.mk_Collect (uuN, uuT, fold (fn (s, T) => fn t => HOLogic.mk_exists (s, T, t))
                  frees (HOLogic.mk_conj (HOLogic.mk_eq (Free uu, t), @{term "True"})))
            in
              mk_set_compr [] ts
                (set_compr :: (if null in_insert then xs else (fold mk_insert in_insert empty) :: xs))  
            end
        end
  in
      foldl1 (HOLogic.mk_binop @{const_name sup}) (mk_set_compr []
        (map (fn ts => HOLogic.mk_tuple 
          (map (restore_nat_numerals o restore_term ctxt' constant_table) (ts ~~ Ts))) tss) [])
  end

fun values_cmd print_modes soln raw_t state =
  let
    val ctxt = Toplevel.context_of state
    val t = Syntax.read_term ctxt raw_t
    val t' = values ctxt soln t
    val ty' = Term.type_of t'
    val ctxt' = Variable.auto_fixes t' ctxt
    val _ = tracing "Printing terms..."
    val p = Print_Mode.with_modes print_modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;


(* renewing the values command for Prolog queries *)

val opt_print_modes =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.xname --| Parse.$$$ ")")) [];

val _ = Outer_Syntax.improper_command "values" "enumerate and print comprehensions" Keyword.diag
  (opt_print_modes -- Scan.optional (Parse.nat >> SOME) NONE -- Parse.term
   >> (fn ((print_modes, soln), t) => Toplevel.keep
        (values_cmd print_modes soln t))); (*FIXME does not preserve the previous functionality*)

(* quickcheck generator *)

(* FIXME: a small clone of Predicate_Compile_Quickcheck - maybe refactor out commons *)

val active = Attrib.setup_config_bool @{binding quickcheck_prolog_active} (K true);

fun test_term ctxt (t, eval_terms) =
  let
    val t' = fold_rev absfree (Term.add_frees t []) t
    val options = code_options_of (Proof_Context.theory_of ctxt)
    val thy = Theory.copy (Proof_Context.theory_of ctxt)
    val ((((full_constname, constT), vs'), intro), thy1) =
      Predicate_Compile_Aux.define_quickcheck_predicate t' thy
    val thy2 = Context.theory_map (Predicate_Compile_Alternative_Defs.add_thm intro) thy1
    val thy3 = Predicate_Compile.preprocess preprocess_options (Const (full_constname, constT)) thy2
    val ctxt' = Proof_Context.init_global thy3
    val _ = tracing "Generating prolog program..."
    val (p, constant_table) = generate (NONE, true) ctxt' full_constname
      |> post_process ctxt' (set_ensure_groundness options) full_constname
    val _ = tracing "Running prolog program..."
    val system_config = System_Config.get (Context.Proof ctxt)
    val tss = run (#timeout system_config, #prolog_system system_config)
      p (translate_const constant_table full_constname, map (Var o fst) vs') (map fst vs') (SOME 1)
    val _ = tracing "Restoring terms..."
    val counterexample =
      case tss of
        [ts] => SOME (map (restore_term ctxt' constant_table) (ts ~~ map snd vs'))
      | _ => NONE
  in
    Quickcheck.Result
      {counterexample = Option.map (pair true o curry (op ~~) (Term.add_free_names t [])) counterexample,
       evaluation_terms = Option.map (K []) counterexample, timings = [], reports = []}
  end;

fun test_goals ctxt _ insts goals =
  let
    val correct_inst_goals = Quickcheck_Common.instantiate_goals ctxt insts goals
  in
    Quickcheck_Common.collect_results (test_term ctxt) (maps (map snd) correct_inst_goals) []
  end
  
  
end;
