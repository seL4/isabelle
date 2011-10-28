(*  Title:      HOL/Tools/Predicate_Compile/mode_inference.ML
    Author:     Lukas Bulwahn, TU Muenchen

Mode inference for the predicate compiler.
*)

signature MODE_INFERENCE =
sig
  type mode = Predicate_Compile_Aux.mode
  
  (* options *)
  type mode_analysis_options =
  {use_generators : bool,
  reorder_premises : bool,
  infer_pos_and_neg_modes : bool}
  
  (* mode operation *)
  val all_input_of : typ -> mode
  (* mode derivation and operations *)
  datatype mode_derivation = Mode_App of mode_derivation * mode_derivation | Context of mode
    | Mode_Pair of mode_derivation * mode_derivation | Term of mode

  val head_mode_of : mode_derivation -> mode
  val param_derivations_of : mode_derivation -> mode_derivation list
  val collect_context_modes : mode_derivation -> mode list
  
  type moded_clause = term list * (Predicate_Compile_Aux.indprem * mode_derivation) list
  type 'a pred_mode_table = (string * ((bool * mode) * 'a) list) list
 
  (* mode inference operations *)
  val all_derivations_of :
    Proof.context -> (string * mode list) list -> string list -> term
      -> (mode_derivation * string list) list
  (* TODO: move all_modes creation to infer_modes *) 
  val infer_modes : 
    mode_analysis_options -> Predicate_Compile_Aux.options ->
     (string -> mode list) * (string -> mode list)
       * (string -> mode -> bool) -> Proof.context -> (string * typ) list ->
      (string * mode list) list ->
      string list -> (string * (Term.term list * Predicate_Compile_Aux.indprem list) list) list ->
      ((moded_clause list pred_mode_table * (string * mode list) list) * string list)
  
  (* mode and term operations -- to be moved to Predicate_Compile_Aux *) 
  val collect_non_invertible_subterms :
    Proof.context -> term -> string list * term list ->  (term * (string list * term list))
  val is_all_input : mode -> bool
  val term_vs : term -> string list
  val terms_vs : term list -> string list
  
end;

structure Mode_Inference : MODE_INFERENCE =
struct

open Predicate_Compile_Aux;
open Core_Data;

(* derivation trees for modes of premises *)

datatype mode_derivation = Mode_App of mode_derivation * mode_derivation | Context of mode
  | Mode_Pair of mode_derivation * mode_derivation | Term of mode

fun string_of_derivation (Mode_App (m1, m2)) =
  "App (" ^ string_of_derivation m1 ^ ", " ^ string_of_derivation m2 ^ ")"
  | string_of_derivation (Mode_Pair (m1, m2)) =
  "Pair (" ^ string_of_derivation m1 ^ ", " ^ string_of_derivation m2 ^ ")"
  | string_of_derivation (Term m) = "Term (" ^ string_of_mode m ^ ")"
  | string_of_derivation (Context m) = "Context (" ^ string_of_mode m ^ ")"

fun strip_mode_derivation deriv =
  let
    fun strip (Mode_App (deriv1, deriv2)) ds = strip deriv1 (deriv2 :: ds)
      | strip deriv ds = (deriv, ds)
  in
    strip deriv []
  end

fun mode_of (Context m) = m
  | mode_of (Term m) = m
  | mode_of (Mode_App (d1, d2)) =
    (case mode_of d1 of Fun (m, m') =>
        (if eq_mode (m, mode_of d2) then m' else raise Fail "mode_of: derivation has mismatching modes")
      | _ => raise Fail "mode_of: derivation has a non-functional mode")
  | mode_of (Mode_Pair (d1, d2)) =
    Pair (mode_of d1, mode_of d2)

fun head_mode_of deriv = mode_of (fst (strip_mode_derivation deriv))

fun param_derivations_of deriv =
  let
    val (_, argument_derivs) = strip_mode_derivation deriv
    fun param_derivation (Mode_Pair (m1, m2)) =
        param_derivation m1 @ param_derivation m2
      | param_derivation (Term _) = []
      | param_derivation m = [m]
  in
    maps param_derivation argument_derivs
  end

fun collect_context_modes (Mode_App (m1, m2)) =
      collect_context_modes m1 @ collect_context_modes m2
  | collect_context_modes (Mode_Pair (m1, m2)) =
      collect_context_modes m1 @ collect_context_modes m2
  | collect_context_modes (Context m) = [m]
  | collect_context_modes (Term _) = []

type moded_clause = term list * (Predicate_Compile_Aux.indprem * mode_derivation) list
type 'a pred_mode_table = (string * ((bool * mode) * 'a) list) list


(** string_of functions **)

fun string_of_prem ctxt (Prem t) =
    (Syntax.string_of_term ctxt t) ^ "(premise)"
  | string_of_prem ctxt (Negprem t) =
    (Syntax.string_of_term ctxt (HOLogic.mk_not t)) ^ "(negative premise)"
  | string_of_prem ctxt (Sidecond t) =
    (Syntax.string_of_term ctxt t) ^ "(sidecondition)"
  | string_of_prem ctxt _ = raise Fail "string_of_prem: unexpected input"

fun string_of_clause ctxt pred (ts, prems) =
  (space_implode " --> "
  (map (string_of_prem ctxt) prems)) ^ " --> " ^ pred ^ " "
   ^ (space_implode " " (map (Syntax.string_of_term ctxt) ts))

type mode_analysis_options =
  {use_generators : bool,
  reorder_premises : bool,
  infer_pos_and_neg_modes : bool}

fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (Tname, _, cs)) => map (apsnd (rpair Tname o length)) cs) o #descr o snd)
      (Symtab.dest (Datatype.get_all thy)));
    fun check t = (case strip_comb t of
        (Free _, []) => true
      | (Const (s, T), ts) => (case (AList.lookup (op =) cnstrs s, body_type T) of
            (SOME (i, Tname), Type (Tname', _)) =>
              length ts = i andalso Tname = Tname' andalso forall check ts
          | _ => false)
      | _ => false)
  in check end;

(*** check if a type is an equality type (i.e. doesn't contain fun)
  FIXME this is only an approximation ***)
fun is_eqT (Type (s, Ts)) = s <> "fun" andalso forall is_eqT Ts
  | is_eqT _ = true;

fun term_vs tm = fold_aterms (fn Free (x, T) => cons x | _ => I) tm [];
val terms_vs = distinct (op =) o maps term_vs;

(** collect all Frees in a term (with duplicates!) **)
fun term_vTs tm =
  fold_aterms (fn Free xT => cons xT | _ => I) tm [];

fun print_failed_mode options thy modes p (pol, m) rs is =
  if show_mode_inference options then
    let
      val _ = tracing ("Clauses " ^ commas (map (fn i => string_of_int (i + 1)) is) ^ " of " ^
        p ^ " violates mode " ^ string_of_mode m)
    in () end
  else ()

fun error_of p (pol, m) is =
  "  Clauses " ^ commas (map (fn i => string_of_int (i + 1)) is) ^ " of " ^
        p ^ " violates mode " ^ string_of_mode m

fun is_all_input mode =
  let
    fun is_all_input' (Fun _) = true
      | is_all_input' (Pair (m1, m2)) = is_all_input' m1 andalso is_all_input' m2
      | is_all_input' Input = true
      | is_all_input' Output = false
  in
    forall is_all_input' (strip_fun_mode mode)
  end

fun all_input_of T =
  let
    val (Ts, U) = strip_type T
    fun input_of (Type (@{type_name Product_Type.prod}, [T1, T2])) = Pair (input_of T1, input_of T2)
      | input_of _ = Input
  in
    if U = HOLogic.boolT then
      fold_rev (curry Fun) (map input_of Ts) Bool
    else
      raise Fail "all_input_of: not a predicate"
  end

fun find_least ord xs =
  let
    fun find' x y = (case y of NONE => SOME x | SOME y' => if ord (x, y') = LESS then SOME x else y) 
  in
    fold find' xs NONE
  end
  
fun term_vs tm = fold_aterms (fn Free (x, T) => cons x | _ => I) tm [];
val terms_vs = distinct (op =) o maps term_vs;

fun input_mode T =
  let
    val (Ts, U) = strip_type T
  in
    fold_rev (curry Fun) (map (K Input) Ts) Input
  end

fun output_mode T =
  let
    val (Ts, U) = strip_type T
  in
    fold_rev (curry Fun) (map (K Output) Ts) Output
  end

fun is_invertible_function ctxt (Const (f, _)) = is_constr ctxt f
  | is_invertible_function ctxt _ = false

fun non_invertible_subterms ctxt (t as Free _) = []
  | non_invertible_subterms ctxt t = 
  let
    val (f, args) = strip_comb t
  in
    if is_invertible_function ctxt f then
      maps (non_invertible_subterms ctxt) args
    else
      [t]
  end

fun collect_non_invertible_subterms ctxt (f as Free _) (names, eqs) = (f, (names, eqs))
  | collect_non_invertible_subterms ctxt t (names, eqs) =
    case (strip_comb t) of (f, args) =>
      if is_invertible_function ctxt f then
          let
            val (args', (names', eqs')) =
              fold_map (collect_non_invertible_subterms ctxt) args (names, eqs)
          in
            (list_comb (f, args'), (names', eqs'))
          end
        else
          let
            val s = singleton (Name.variant_list names) "x"
            val v = Free (s, fastype_of t)
          in
            (v, (s :: names, HOLogic.mk_eq (v, t) :: eqs))
          end
(*
  if is_constrt thy t then (t, (names, eqs)) else
    let
      val s = singleton (Name.variant_list names) "x"
      val v = Free (s, fastype_of t)
    in (v, (s::names, HOLogic.mk_eq (v, t)::eqs)) end;
*)

fun is_possible_output ctxt vs t =
  forall
    (fn t => is_eqT (fastype_of t) andalso forall (member (op =) vs) (term_vs t))
      (non_invertible_subterms ctxt t)
  andalso
    (forall (is_eqT o snd)
      (inter (fn ((f', _), f) => f = f') vs (Term.add_frees t [])))

fun vars_of_destructable_term ctxt (Free (x, _)) = [x]
  | vars_of_destructable_term ctxt t =
  let
    val (f, args) = strip_comb t
  in
    if is_invertible_function ctxt f then
      maps (vars_of_destructable_term ctxt) args
    else
      []
  end

fun is_constructable vs t = forall (member (op =) vs) (term_vs t)

fun missing_vars vs t = subtract (op =) vs (term_vs t)

fun output_terms (Const (@{const_name Pair}, _) $ t1 $ t2, Mode_Pair (d1, d2)) =
    output_terms (t1, d1)  @ output_terms (t2, d2)
  | output_terms (t1 $ t2, Mode_App (d1, d2)) =
    output_terms (t1, d1)  @ output_terms (t2, d2)
  | output_terms (t, Term Output) = [t]
  | output_terms _ = []

fun lookup_mode modes (Const (s, T)) =
   (case (AList.lookup (op =) modes s) of
      SOME ms => SOME (map (fn m => (Context m, [])) ms)
    | NONE => NONE)
  | lookup_mode modes (Free (x, _)) =
    (case (AList.lookup (op =) modes x) of
      SOME ms => SOME (map (fn m => (Context m , [])) ms)
    | NONE => NONE)

fun derivations_of (ctxt : Proof.context) modes vs (Const (@{const_name Pair}, _) $ t1 $ t2) (Pair (m1, m2)) =
    map_product
      (fn (m1, mvars1) => fn (m2, mvars2) => (Mode_Pair (m1, m2), union (op =) mvars1 mvars2))
        (derivations_of ctxt modes vs t1 m1) (derivations_of ctxt modes vs t2 m2)
  | derivations_of ctxt modes vs t (m as Fun _) =
    (*let
      val (p, args) = strip_comb t
    in
      (case lookup_mode modes p of
        SOME ms => map_filter (fn (Context m, []) => let
          val ms = strip_fun_mode m
          val (argms, restms) = chop (length args) ms
          val m' = fold_rev (curry Fun) restms Bool
        in
          if forall (fn m => eq_mode (Input, m)) argms andalso eq_mode (m', mode) then
            SOME (fold (curry Mode_App) (map Term argms) (Context m), missing_vars vs t)
          else NONE
        end) ms
      | NONE => (if is_all_input mode then [(Context mode, [])] else []))
    end*)
    (case try (all_derivations_of ctxt modes vs) t  of
      SOME derivs =>
        filter (fn (d, mvars) => eq_mode (mode_of d, m) andalso null (output_terms (t, d))) derivs
    | NONE => (if is_all_input m then [(Context m, [])] else []))
  | derivations_of ctxt modes vs t m =
    if eq_mode (m, Input) then
      [(Term Input, missing_vars vs t)]
    else if eq_mode (m, Output) then
      (if is_possible_output ctxt vs t then [(Term Output, [])] else [])
    else []
and all_derivations_of ctxt modes vs (Const (@{const_name Pair}, _) $ t1 $ t2) =
  let
    val derivs1 = all_derivations_of ctxt modes vs t1
    val derivs2 = all_derivations_of ctxt modes vs t2
  in
    map_product
      (fn (m1, mvars1) => fn (m2, mvars2) => (Mode_Pair (m1, m2), union (op =) mvars1 mvars2))
        derivs1 derivs2
  end
  | all_derivations_of ctxt modes vs (t1 $ t2) =
  let
    val derivs1 = all_derivations_of ctxt modes vs t1
  in
    maps (fn (d1, mvars1) =>
      case mode_of d1 of
        Fun (m', _) => map (fn (d2, mvars2) =>
          (Mode_App (d1, d2), union (op =) mvars1 mvars2)) (derivations_of ctxt modes vs t2 m')
        | _ => raise Fail "all_derivations_of: derivation has an unexpected non-functional mode") derivs1
  end
  | all_derivations_of _ modes vs (Const (s, T)) = the (lookup_mode modes (Const (s, T)))
  | all_derivations_of _ modes vs (Free (x, T)) = the (lookup_mode modes (Free (x, T)))
  | all_derivations_of _ modes vs _ = raise Fail "all_derivations_of: unexpected term"

fun rev_option_ord ord (NONE, NONE) = EQUAL
  | rev_option_ord ord (NONE, SOME _) = GREATER
  | rev_option_ord ord (SOME _, NONE) = LESS
  | rev_option_ord ord (SOME x, SOME y) = ord (x, y)

fun random_mode_in_deriv modes t deriv =
  case try dest_Const (fst (strip_comb t)) of
    SOME (s, _) =>
      (case AList.lookup (op =) modes s of
        SOME ms =>
          (case AList.lookup (op =) (map (fn ((p, m), r) => (m, r)) ms) (head_mode_of deriv) of
            SOME r => r
          | NONE => false)
      | NONE => false)
  | NONE => false

fun number_of_output_positions mode =
  let
    val args = strip_fun_mode mode
    fun contains_output (Fun _) = false
      | contains_output Input = false
      | contains_output Output = true
      | contains_output (Pair (m1, m2)) = contains_output m1 orelse contains_output m2
  in
    length (filter contains_output args)
  end

fun lex_ord ord1 ord2 (x, x') =
  case ord1 (x, x') of
    EQUAL => ord2 (x, x')
  | ord => ord

fun lexl_ord [] (x, x') = EQUAL
  | lexl_ord (ord :: ords') (x, x') =
    case ord (x, x') of
      EQUAL => lexl_ord ords' (x, x')
    | ord => ord

fun deriv_ord' ctxt pol pred modes t1 t2 ((deriv1, mvars1), (deriv2, mvars2)) =
  let
    (* prefer functional modes if it is a function *)
    fun fun_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      let
        fun is_functional t mode =
          case try (fst o dest_Const o fst o strip_comb) t of
            NONE => false
          | SOME c => is_some (alternative_compilation_of ctxt c mode)
      in
        case (is_functional t1 (head_mode_of deriv1), is_functional t2 (head_mode_of deriv2)) of
          (true, true) => EQUAL
        | (true, false) => LESS
        | (false, true) => GREATER
        | (false, false) => EQUAL
      end
    (* prefer modes without requirement for generating random values *)
    fun mvars_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (length mvars1, length mvars2)
    (* prefer non-random modes *)
    fun random_mode_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (if random_mode_in_deriv modes t1 deriv1 then 1 else 0,
               if random_mode_in_deriv modes t2 deriv2 then 1 else 0)
    (* prefer modes with more input and less output *)
    fun output_mode_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (number_of_output_positions (head_mode_of deriv1),
        number_of_output_positions (head_mode_of deriv2))
    (* prefer recursive calls *)
    fun is_rec_premise t =
      case fst (strip_comb t) of Const (c, T) => c = pred | _ => false
    fun recursive_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (if is_rec_premise t1 then 0 else 1,
        if is_rec_premise t2 then 0 else 1)
    val ord = lexl_ord [mvars_ord, fun_ord, random_mode_ord, output_mode_ord, recursive_ord]
  in
    ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2))
  end

fun deriv_ord ctxt pol pred modes t = deriv_ord' ctxt pol pred modes t t

fun premise_ord thy pol pred modes ((prem1, a1), (prem2, a2)) =
  rev_option_ord (deriv_ord' thy pol pred modes (dest_indprem prem1) (dest_indprem prem2)) (a1, a2)

fun print_mode_list modes =
  tracing ("modes: " ^ (commas (map (fn (s, ms) => s ^ ": " ^
    commas (map (fn (m, r) => string_of_mode m ^ (if r then " random " else " not ")) ms)) modes)))

fun select_mode_prem (mode_analysis_options : mode_analysis_options) (ctxt : Proof.context) pred
  pol (modes, (pos_modes, neg_modes)) vs ps =
  let
    fun choose_mode_of_prem (Prem t) =
          find_least (deriv_ord ctxt pol pred modes t) (all_derivations_of ctxt pos_modes vs t)
      | choose_mode_of_prem (Sidecond t) = SOME (Context Bool, missing_vars vs t)
      | choose_mode_of_prem (Negprem t) = find_least (deriv_ord ctxt (not pol) pred modes t)
          (filter (fn (d, missing_vars) => is_all_input (head_mode_of d))
             (all_derivations_of ctxt neg_modes vs t))
      | choose_mode_of_prem p = raise Fail ("choose_mode_of_prem: unexpected premise " ^ string_of_prem ctxt p)
  in
    if #reorder_premises mode_analysis_options then
      find_least (premise_ord ctxt pol pred modes) (ps ~~ map choose_mode_of_prem ps)
    else
      SOME (hd ps, choose_mode_of_prem (hd ps))
  end

fun check_mode_clause' (mode_analysis_options : mode_analysis_options) ctxt pred param_vs (modes :
  (string * ((bool * mode) * bool) list) list) ((pol, mode) : bool * mode) (ts, ps) =
  let
    val vTs = distinct (op =) (fold Term.add_frees (map dest_indprem ps) (fold Term.add_frees ts []))
    val modes' = modes @ (param_vs ~~ map (fn x => [((true, x), false), ((false, x), false)]) (ho_arg_modes_of mode))
    fun retrieve_modes_of_pol pol = map (fn (s, ms) =>
      (s, map_filter (fn ((p, m), r) => if p = pol then SOME m else NONE | _ => NONE) ms))
    val (pos_modes', neg_modes') =
      if #infer_pos_and_neg_modes mode_analysis_options then
        (retrieve_modes_of_pol pol modes', retrieve_modes_of_pol (not pol) modes')
      else
        let
          val modes = map (fn (s, ms) => (s, map (fn ((p, m), r) => m) ms)) modes'
        in (modes, modes) end
    val (in_ts, out_ts) = split_mode mode ts
    val in_vs = union (op =) param_vs (maps (vars_of_destructable_term ctxt) in_ts)
    val out_vs = terms_vs out_ts
    fun known_vs_after p vs = (case p of
        Prem t => union (op =) vs (term_vs t)
      | Sidecond t => union (op =) vs (term_vs t)
      | Negprem t => union (op =) vs (term_vs t)
      | _ => raise Fail "unexpected premise")
    fun check_mode_prems acc_ps rnd vs [] = SOME (acc_ps, vs, rnd)
      | check_mode_prems acc_ps rnd vs ps =
        (case
          (select_mode_prem mode_analysis_options ctxt pred pol (modes', (pos_modes', neg_modes')) vs ps) of
          SOME (p, SOME (deriv, [])) => check_mode_prems ((p, deriv) :: acc_ps) rnd
            (known_vs_after p vs) (filter_out (equal p) ps)
        | SOME (p, SOME (deriv, missing_vars)) =>
          if #use_generators mode_analysis_options andalso pol then
            check_mode_prems ((p, deriv) :: (map
              (fn v => (Generator (v, the (AList.lookup (op =) vTs v)), Term Output))
                (distinct (op =) missing_vars))
                @ acc_ps) true (known_vs_after p vs) (filter_out (equal p) ps)
          else NONE
        | SOME (p, NONE) => NONE
        | NONE => NONE)
  in
    case check_mode_prems [] false in_vs ps of
      NONE => NONE
    | SOME (acc_ps, vs, rnd) =>
      if forall (is_constructable vs) (in_ts @ out_ts) then
        SOME (ts, rev acc_ps, rnd)
      else
        if #use_generators mode_analysis_options andalso pol then
          let
             val generators = map
              (fn v => (Generator (v, the (AList.lookup (op =) vTs v)), Term Output))
                (subtract (op =) vs (terms_vs (in_ts @ out_ts)))
          in
            SOME (ts, rev (generators @ acc_ps), true)
          end
        else
          NONE
  end

datatype result = Success of bool | Error of string

fun check_modes_pred' mode_analysis_options options thy param_vs clauses modes (p, (ms : ((bool * mode) * bool) list)) =
  let
    fun split xs =
      let
        fun split' [] (ys, zs) = (rev ys, rev zs)
          | split' ((m, Error z) :: xs) (ys, zs) = split' xs (ys, z :: zs)
          | split' (((m : bool * mode), Success rnd) :: xs) (ys, zs) = split' xs ((m, rnd) :: ys, zs)
       in
         split' xs ([], [])
       end
    val rs = these (AList.lookup (op =) clauses p)
    fun check_mode m =
      let
        val res = cond_timeit false "work part of check_mode for one mode" (fn _ => 
          map (check_mode_clause' mode_analysis_options thy p param_vs modes m) rs)
      in
        cond_timeit false "aux part of check_mode for one mode" (fn _ => 
        case find_indices is_none res of
          [] => Success (exists (fn SOME (_, _, true) => true | _ => false) res)
        | is => (print_failed_mode options thy modes p m rs is; Error (error_of p m is)))
      end
    val _ = if show_mode_inference options then
        tracing ("checking " ^ string_of_int (length ms) ^ " modes ...")
      else ()
    val res = cond_timeit false "check_mode" (fn _ => map (fn (m, _) => (m, check_mode m)) ms)
    val (ms', errors) = split res
  in
    ((p, (ms' : ((bool * mode) * bool) list)), errors)
  end;

fun get_modes_pred' mode_analysis_options thy param_vs clauses modes (p, ms) =
  let
    val rs = these (AList.lookup (op =) clauses p)
  in
    (p, map (fn (m, rnd) =>
      (m, map
        ((fn (ts, ps, rnd) => (ts, ps)) o the o
          check_mode_clause' mode_analysis_options thy p param_vs modes m) rs)) ms)
  end;

fun fixp f (x : (string * ((bool * mode) * bool) list) list) =
  let val y = f x
  in if x = y then x else fixp f y end;

fun fixp_with_state f (x : (string * ((bool * mode) * bool) list) list, state) =
  let
    val (y, state') = f (x, state)
  in
    if x = y then (y, state') else fixp_with_state f (y, state')
  end

fun string_of_ext_mode ((pol, mode), rnd) =
  string_of_mode mode ^ "(" ^ (if pol then "pos" else "neg") ^ ", "
  ^ (if rnd then "rnd" else "nornd") ^ ")"

fun print_extra_modes options modes =
  if show_mode_inference options then
    tracing ("Modes of inferred predicates: " ^
      cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map string_of_ext_mode ms)) modes))
  else ()

fun infer_modes mode_analysis_options options (lookup_mode, lookup_neg_mode, needs_random) ctxt
  preds all_modes param_vs clauses =
  let
    fun appair f (x1, x2) (y1, y2) = (f x1 y1, f x2 y2)
    fun add_needs_random s (false, m) = ((false, m), false)
      | add_needs_random s (true, m) = ((true, m), needs_random s m)
    fun add_polarity_and_random_bit s b ms = map (fn m => add_needs_random s (b, m)) ms
    val prednames = map fst preds
    (* extramodes contains all modes of all constants, should we only use the necessary ones
       - what is the impact on performance? *)
    fun predname_of (Prem t) =
        (case try dest_Const (fst (strip_comb t)) of SOME (c, _) => insert (op =) c | NONE => I)
      | predname_of (Negprem t) =
        (case try dest_Const (fst (strip_comb t)) of SOME (c, _) => insert (op =) c | NONE => I)
      | predname_of _ = I
    val relevant_prednames = fold (fn (_, clauses') =>
      fold (fn (_, ps) => fold Term.add_const_names (map dest_indprem ps)) clauses') clauses []
      |> filter_out (fn name => member (op =) prednames name)
    val extra_modes =
      if #infer_pos_and_neg_modes mode_analysis_options then
        let
          val pos_extra_modes =
            map_filter (fn name => Option.map (pair name) (try lookup_mode name))
            relevant_prednames
          val neg_extra_modes =
            map_filter (fn name => Option.map (pair name) (try lookup_neg_mode name))
              relevant_prednames
        in
          map (fn (s, ms) => (s, (add_polarity_and_random_bit s true ms)
                @ add_polarity_and_random_bit s false (the (AList.lookup (op =) neg_extra_modes s))))
            pos_extra_modes
        end
      else
        map (fn (s, ms) => (s, (add_polarity_and_random_bit s true ms)))
          (map_filter (fn name => Option.map (pair name) (try lookup_mode name))
            relevant_prednames)
    val _ = print_extra_modes options extra_modes
    val start_modes =
      if #infer_pos_and_neg_modes mode_analysis_options then
        map (fn (s, ms) => (s, map (fn m => ((true, m), false)) ms @
          (map (fn m => ((false, m), false)) ms))) all_modes
      else
        map (fn (s, ms) => (s, map (fn m => ((true, m), false)) ms)) all_modes
    fun iteration modes = map
      (check_modes_pred' mode_analysis_options options ctxt param_vs clauses
        (modes @ extra_modes)) modes
    val ((modes : (string * ((bool * mode) * bool) list) list), errors) =
      cond_timeit false "Fixpount computation of mode analysis" (fn () =>
      if show_invalid_clauses options then
        fixp_with_state (fn (modes, errors) =>
          let
            val (modes', new_errors) = split_list (iteration modes)
          in (modes', errors @ flat new_errors) end) (start_modes, [])
        else
          (fixp (fn modes => map fst (iteration modes)) start_modes, []))
    val moded_clauses = map (get_modes_pred' mode_analysis_options ctxt param_vs clauses
      (modes @ extra_modes)) modes
    val need_random = fold (fn (s, ms) => if member (op =) (map fst preds) s then
      cons (s, (map_filter (fn ((true, m), true) => SOME m | _ => NONE) ms)) else I)
      modes []
  in
    ((moded_clauses, need_random), errors)
  end;

end;