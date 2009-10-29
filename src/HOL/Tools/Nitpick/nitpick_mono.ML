(*  Title:      HOL/Nitpick/Tools/nitpick_mono.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009

Monotonicity predicate for higher-order logic.
*)

signature NITPICK_MONO =
sig
  type extended_context = Nitpick_HOL.extended_context

  val formulas_monotonic :
    extended_context -> typ -> term list -> term list -> term -> bool
end;

structure Nitpick_Mono : NITPICK_MONO =
struct

open Nitpick_Util
open Nitpick_HOL

type var = int

datatype sign = Pos | Neg
datatype sign_atom = S of sign | V of var

type literal = var * sign

datatype ctype =
  CAlpha |
  CFun of ctype * sign_atom * ctype |
  CPair of ctype * ctype |
  CType of string * ctype list |
  CRec of string * typ list

type cdata =
  {ext_ctxt: extended_context,
   alpha_T: typ,
   max_fresh: int Unsynchronized.ref,
   datatype_cache: ((string * typ list) * ctype) list Unsynchronized.ref,
   constr_cache: (styp * ctype) list Unsynchronized.ref}

exception CTYPE of string * ctype list

(* string -> unit *)
fun print_g (s : string) = ()

(* var -> string *)
val string_for_var = signed_string_of_int
(* string -> var list -> string *)
fun string_for_vars sep [] = "0\<^bsub>" ^ sep ^ "\<^esub>"
  | string_for_vars sep xs = space_implode sep (map string_for_var xs)
fun subscript_string_for_vars sep xs =
  if null xs then "" else "\<^bsub>" ^ string_for_vars sep xs ^ "\<^esub>"

(* sign -> string *)
fun string_for_sign Pos = "+"
  | string_for_sign Neg = "-"

(* sign -> sign -> sign *)
fun xor sn1 sn2 = if sn1 = sn2 then Pos else Neg
(* sign -> sign *)
val negate = xor Neg

(* sign_atom -> string *)
fun string_for_sign_atom (S sn) = string_for_sign sn
  | string_for_sign_atom (V j) = string_for_var j

(* literal -> string *)
fun string_for_literal (x, sn) = string_for_var x ^ " = " ^ string_for_sign sn

val bool_C = CType (@{type_name bool}, [])

(* ctype -> bool *)
fun is_CRec (CRec _) = true
  | is_CRec _ = false

val no_prec = 100
val prec_CFun = 1
val prec_CPair = 2

(* tuple_set -> int *)
fun precedence_of_ctype (CFun _) = prec_CFun
  | precedence_of_ctype (CPair _) = prec_CPair
  | precedence_of_ctype _ = no_prec

(* ctype -> string *)
val string_for_ctype =
  let
    (* int -> ctype -> string *)
    fun aux outer_prec C =
      let
        val prec = precedence_of_ctype C
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then "(" else "") ^
        (case C of
           CAlpha => "\<alpha>"
         | CFun (C1, a, C2) =>
           aux (prec + 1) C1 ^ " \<Rightarrow>\<^bsup>" ^
           string_for_sign_atom a ^ "\<^esup> " ^ aux prec C2
         | CPair (C1, C2) => aux (prec + 1) C1 ^ " \<times> " ^ aux prec C2
         | CType (s, []) =>
           if s mem [@{type_name prop}, @{type_name bool}] then "o" else s
         | CType (s, Cs) => "(" ^ commas (map (aux 0) Cs) ^ ") " ^ s
         | CRec (s, _) => "[" ^ s ^ "]") ^
        (if need_parens then ")" else "")
      end
  in aux 0 end

(* ctype -> ctype list *)
fun flatten_ctype (CPair (C1, C2)) = maps flatten_ctype [C1, C2]
  | flatten_ctype (CType (_, Cs)) = maps flatten_ctype Cs
  | flatten_ctype C = [C]

(* extended_context -> typ -> cdata *)
fun initial_cdata ext_ctxt alpha_T =
  ({ext_ctxt = ext_ctxt, alpha_T = alpha_T, max_fresh = Unsynchronized.ref 0,
    datatype_cache = Unsynchronized.ref [],
    constr_cache = Unsynchronized.ref []} : cdata)

(* typ -> typ -> bool *)
fun could_exist_alpha_subtype alpha_T (T as Type (_, Ts)) =
    T = alpha_T orelse (not (is_fp_iterator_type T)
                        andalso exists (could_exist_alpha_subtype alpha_T) Ts)
  | could_exist_alpha_subtype alpha_T T = (T = alpha_T)
(* theory -> typ -> typ -> bool *)
fun could_exist_alpha_sub_ctype _ (alpha_T as TFree _) =
    could_exist_alpha_subtype alpha_T
  | could_exist_alpha_sub_ctype thy alpha_T = equal alpha_T orf is_datatype thy

(* ctype -> bool *)
fun exists_alpha_sub_ctype CAlpha = true
  | exists_alpha_sub_ctype (CFun (C1, _, C2)) =
    exists exists_alpha_sub_ctype [C1, C2]
  | exists_alpha_sub_ctype (CPair (C1, C2)) =
    exists exists_alpha_sub_ctype [C1, C2]
  | exists_alpha_sub_ctype (CType (_, Cs)) = exists exists_alpha_sub_ctype Cs
  | exists_alpha_sub_ctype (CRec _) = true

(* ctype -> bool *)
fun exists_alpha_sub_ctype_fresh CAlpha = true
  | exists_alpha_sub_ctype_fresh (CFun (_, V _, _)) = true
  | exists_alpha_sub_ctype_fresh (CFun (_, _, C2)) =
    exists_alpha_sub_ctype_fresh C2
  | exists_alpha_sub_ctype_fresh (CPair (C1, C2)) =
    exists exists_alpha_sub_ctype_fresh [C1, C2]
  | exists_alpha_sub_ctype_fresh (CType (_, Cs)) =
    exists exists_alpha_sub_ctype_fresh Cs
  | exists_alpha_sub_ctype_fresh (CRec _) = true

(* string * typ list -> ctype list -> ctype *)
fun constr_ctype_for_binders z Cs =
  fold_rev (fn C => curry3 CFun C (S Neg)) Cs (CRec z)

(* ((string * typ list) * ctype) list -> ctype list -> ctype -> ctype *)
fun repair_ctype _ _ CAlpha = CAlpha
  | repair_ctype cache seen (CFun (C1, a, C2)) =
    CFun (repair_ctype cache seen C1, a, repair_ctype cache seen C2)
  | repair_ctype cache seen (CPair Cp) =
    CPair (pairself (repair_ctype cache seen) Cp)
  | repair_ctype cache seen (CType (s, Cs)) =
    CType (s, maps (flatten_ctype o repair_ctype cache seen) Cs)
  | repair_ctype cache seen (CRec (z as (s, _))) =
    case AList.lookup (op =) cache z |> the of
      CRec _ => CType (s, [])
    | C => if C mem seen then CType (s, [])
           else repair_ctype cache (C :: seen) C

(* ((string * typ list) * ctype) list Unsynchronized.ref -> unit *)
fun repair_datatype_cache cache =
  let
    (* (string * typ list) * ctype -> unit *)
    fun repair_one (z, C) =
      Unsynchronized.change cache
          (AList.update (op =) (z, repair_ctype (!cache) [] C))
  in List.app repair_one (rev (!cache)) end

(* (typ * ctype) list -> (styp * ctype) list Unsynchronized.ref -> unit *)
fun repair_constr_cache dtype_cache constr_cache =
  let
    (* styp * ctype -> unit *)
    fun repair_one (x, C) =
      Unsynchronized.change constr_cache
          (AList.update (op =) (x, repair_ctype dtype_cache [] C))
  in List.app repair_one (!constr_cache) end

(* cdata -> typ -> ctype *)
fun fresh_ctype_for_type ({ext_ctxt as {thy, ...}, alpha_T, max_fresh,
                           datatype_cache, constr_cache, ...} : cdata) =
  let
    (* typ -> typ -> ctype *)
    fun do_fun T1 T2 =
      let
        val C1 = do_type T1
        val C2 = do_type T2
        val a = if is_boolean_type (body_type T2)
                   andalso exists_alpha_sub_ctype_fresh C1 then
                  V (Unsynchronized.inc max_fresh)
                else
                  S Neg
      in CFun (C1, a, C2) end
    (* typ -> ctype *)
    and do_type T =
      if T = alpha_T then
        CAlpha
      else case T of
        Type ("fun", [T1, T2]) => do_fun T1 T2
      | Type (@{type_name fun_box}, [T1, T2]) => do_fun T1 T2
      | Type ("*", [T1, T2]) => CPair (pairself do_type (T1, T2))
      | Type (z as (s, _)) =>
        if could_exist_alpha_sub_ctype thy alpha_T T then
          case AList.lookup (op =) (!datatype_cache) z of
            SOME C => C
          | NONE =>
            let
              val _ = Unsynchronized.change datatype_cache (cons (z, CRec z))
              val xs = datatype_constrs thy T
              val (all_Cs, constr_Cs) =
                fold_rev (fn (_, T') => fn (all_Cs, constr_Cs) =>
                             let
                               val binder_Cs = map do_type (binder_types T')
                               val new_Cs = filter exists_alpha_sub_ctype_fresh
                                                   binder_Cs
                               val constr_C = constr_ctype_for_binders z
                                                                       binder_Cs
                             in
                               (union (op =) new_Cs all_Cs,
                                constr_C :: constr_Cs)
                             end)
                         xs ([], [])
              val C = CType (s, all_Cs)
              val _ = Unsynchronized.change datatype_cache
                          (AList.update (op =) (z, C))
              val _ = Unsynchronized.change constr_cache
                          (append (xs ~~ constr_Cs))
            in
              if forall (not o is_CRec o snd) (!datatype_cache) then
                (repair_datatype_cache datatype_cache;
                 repair_constr_cache (!datatype_cache) constr_cache;
                 AList.lookup (op =) (!datatype_cache) z |> the)
              else
                C
            end
        else
          CType (s, [])
      | _ => CType (Refute.string_of_typ T, [])
  in do_type end

(* ctype -> ctype list *)
fun prodC_factors (CPair (C1, C2)) = maps prodC_factors [C1, C2]
  | prodC_factors C = [C]
(* ctype -> ctype list * ctype *)
fun curried_strip_ctype (CFun (C1, S Neg, C2)) =
    curried_strip_ctype C2 |>> append (prodC_factors C1)
  | curried_strip_ctype C = ([], C)
(* string -> ctype -> ctype *)
fun sel_ctype_from_constr_ctype s C =
  let val (arg_Cs, dataC) = curried_strip_ctype C in
    CFun (dataC, S Neg,
          case sel_no_from_name s of ~1 => bool_C | n => nth arg_Cs n)
  end

(* cdata -> styp -> ctype *)
fun ctype_for_constr (cdata as {ext_ctxt as {thy, ...}, alpha_T, constr_cache,
                                ...}) (x as (_, T)) =
  if could_exist_alpha_sub_ctype thy alpha_T T then
    case AList.lookup (op =) (!constr_cache) x of
      SOME C => C
    | NONE => (fresh_ctype_for_type cdata (body_type T);
               AList.lookup (op =) (!constr_cache) x |> the)
  else
    fresh_ctype_for_type cdata T
fun ctype_for_sel (cdata as {ext_ctxt, ...}) (x as (s, _)) =
  x |> boxed_constr_for_sel ext_ctxt |> ctype_for_constr cdata
    |> sel_ctype_from_constr_ctype s

(* literal list -> ctype -> ctype *)
fun instantiate_ctype lits =
  let
    (* ctype -> ctype *)
    fun aux CAlpha = CAlpha
      | aux (CFun (C1, V x, C2)) =
        let
          val a = case AList.lookup (op =) lits x of
                    SOME sn => S sn
                  | NONE => V x
        in CFun (aux C1, a, aux C2) end
      | aux (CFun (C1, a, C2)) = CFun (aux C1, a, aux C2)
      | aux (CPair Cp) = CPair (pairself aux Cp)
      | aux (CType (s, Cs)) = CType (s, map aux Cs)
      | aux (CRec z) = CRec z
  in aux end

datatype comp_op = Eq | Leq

type comp = sign_atom * sign_atom * comp_op * var list
type sign_expr = literal list

datatype constraint_set =
  UnsolvableCSet |
  CSet of literal list * comp list * sign_expr list

(* comp_op -> string *)
fun string_for_comp_op Eq = "="
  | string_for_comp_op Leq = "\<le>"

(* sign_expr -> string *)
fun string_for_sign_expr [] = "\<bot>"
  | string_for_sign_expr lits =
    space_implode " \<or> " (map string_for_literal lits)

(* constraint_set *)
val slack = CSet ([], [], [])

(* literal -> literal list option -> literal list option *)
fun do_literal _ NONE = NONE
  | do_literal (x, sn) (SOME lits) =
    case AList.lookup (op =) lits x of
      SOME sn' => if sn = sn' then SOME lits else NONE
    | NONE => SOME ((x, sn) :: lits)

(* comp_op -> var list -> sign_atom -> sign_atom -> literal list * comp list
   -> (literal list * comp list) option *)
fun do_sign_atom_comp Eq [] a1 a2 (accum as (lits, comps)) =
    (case (a1, a2) of
       (S sn1, S sn2) => if sn1 = sn2 then SOME accum else NONE
     | (V x1, S sn2) =>
       Option.map (rpair comps) (do_literal (x1, sn2) (SOME lits))
     | (V _, V _) => SOME (lits, insert (op =) (a1, a2, Eq, []) comps)
     | _ => do_sign_atom_comp Eq [] a2 a1 accum)
  | do_sign_atom_comp Leq [] a1 a2 (accum as (lits, comps)) =
    (case (a1, a2) of
       (_, S Neg) => SOME accum
     | (S Pos, _) => SOME accum
     | (S Neg, S Pos) => NONE
     | (V _, V _) => SOME (lits, insert (op =) (a1, a2, Leq, []) comps)
     | _ => do_sign_atom_comp Eq [] a1 a2 accum)
  | do_sign_atom_comp cmp xs a1 a2 (accum as (lits, comps)) =
    SOME (lits, insert (op =) (a1, a2, cmp, xs) comps)

(* comp -> var list -> ctype -> ctype -> (literal list * comp list) option
   -> (literal list * comp list) option *)
fun do_ctype_comp _ _ _ _ NONE = NONE
  | do_ctype_comp _ _ CAlpha CAlpha accum = accum
  | do_ctype_comp Eq xs (CFun (C11, a1, C12)) (CFun (C21, a2, C22))
                  (SOME accum) =
     accum |> do_sign_atom_comp Eq xs a1 a2 |> do_ctype_comp Eq xs C11 C21
           |> do_ctype_comp Eq xs C12 C22
  | do_ctype_comp Leq xs (CFun (C11, a1, C12)) (CFun (C21, a2, C22))
                  (SOME accum) =
    (if exists_alpha_sub_ctype C11 then
       accum |> do_sign_atom_comp Leq xs a1 a2
             |> do_ctype_comp Leq xs C21 C11
             |> (case a2 of
                   S Neg => I
                 | S Pos => do_ctype_comp Leq xs C11 C21
                 | V x => do_ctype_comp Leq (x :: xs) C11 C21)
     else
       SOME accum)
    |> do_ctype_comp Leq xs C12 C22
  | do_ctype_comp cmp xs (C1 as CPair (C11, C12)) (C2 as CPair (C21, C22))
                  accum =
    (accum |> fold (uncurry (do_ctype_comp cmp xs)) [(C11, C21), (C12, C22)]
     handle Library.UnequalLengths =>
            raise CTYPE ("Nitpick_Mono.do_ctype_comp", [C1, C2]))
  | do_ctype_comp cmp xs (CType _) (CType _) accum =
    accum (* no need to compare them thanks to the cache *)
  | do_ctype_comp _ _ C1 C2 _ =
    raise CTYPE ("Nitpick_Mono.do_ctype_comp", [C1, C2])

(* comp_op -> ctype -> ctype -> constraint_set -> constraint_set *)
fun add_ctype_comp _ _ _ UnsolvableCSet = UnsolvableCSet
  | add_ctype_comp cmp C1 C2 (CSet (lits, comps, sexps)) =
    (print_g ("*** Add " ^ string_for_ctype C1 ^ " " ^ string_for_comp_op cmp ^
              " " ^ string_for_ctype C2);
     case do_ctype_comp cmp [] C1 C2 (SOME (lits, comps)) of
       NONE => (print_g "**** Unsolvable"; UnsolvableCSet)
     | SOME (lits, comps) => CSet (lits, comps, sexps))

(* ctype -> ctype -> constraint_set -> constraint_set *)
val add_ctypes_equal = add_ctype_comp Eq
val add_is_sub_ctype = add_ctype_comp Leq

(* sign -> sign_expr -> ctype -> (literal list * sign_expr list) option
   -> (literal list * sign_expr list) option *)
fun do_notin_ctype_fv _ _ _ NONE = NONE
  | do_notin_ctype_fv Neg _ CAlpha accum = accum
  | do_notin_ctype_fv Pos [] CAlpha _ = NONE
  | do_notin_ctype_fv Pos [(x, sn)] CAlpha (SOME (lits, sexps)) =
    SOME lits |> do_literal (x, sn) |> Option.map (rpair sexps)
  | do_notin_ctype_fv Pos sexp CAlpha (SOME (lits, sexps)) =
    SOME (lits, insert (op =) sexp sexps)
  | do_notin_ctype_fv sn sexp (CFun (C1, S sn', C2)) accum =
    accum |> (if sn' = Pos andalso sn = Pos then do_notin_ctype_fv Pos sexp C1
              else I)
          |> (if sn' = Neg orelse sn = Pos then do_notin_ctype_fv Neg sexp C1
              else I)
          |> do_notin_ctype_fv sn sexp C2
  | do_notin_ctype_fv Pos sexp (CFun (C1, V x, C2)) accum =
    accum |> (case do_literal (x, Neg) (SOME sexp) of
                NONE => I
              | SOME sexp' => do_notin_ctype_fv Pos sexp' C1)
          |> do_notin_ctype_fv Neg sexp C1
          |> do_notin_ctype_fv Pos sexp C2
  | do_notin_ctype_fv Neg sexp (CFun (C1, V x, C2)) accum =
    accum |> (case do_literal (x, Pos) (SOME sexp) of
                NONE => I
              | SOME sexp' => do_notin_ctype_fv Pos sexp' C1)
          |> do_notin_ctype_fv Neg sexp C2
  | do_notin_ctype_fv sn sexp (CPair (C1, C2)) accum =
    accum |> fold (do_notin_ctype_fv sn sexp) [C1, C2]
  | do_notin_ctype_fv sn sexp (CType (_, Cs)) accum =
    accum |> fold (do_notin_ctype_fv sn sexp) Cs
  | do_notin_ctype_fv _ _ C _ =
    raise CTYPE ("Nitpick_Mono.do_notin_ctype_fv", [C])

(* sign -> ctype -> constraint_set -> constraint_set *)
fun add_notin_ctype_fv _ _ UnsolvableCSet = UnsolvableCSet
  | add_notin_ctype_fv sn C (CSet (lits, comps, sexps)) =
    (print_g ("*** Add " ^ string_for_ctype C ^ " is right-" ^
              (case sn of Neg => "unique" | Pos => "total") ^ ".");
     case do_notin_ctype_fv sn [] C (SOME (lits, sexps)) of
       NONE => (print_g "**** Unsolvable"; UnsolvableCSet)
     | SOME (lits, sexps) => CSet (lits, comps, sexps))

(* ctype -> constraint_set -> constraint_set *)
val add_ctype_is_right_unique = add_notin_ctype_fv Neg
val add_ctype_is_right_total = add_notin_ctype_fv Pos

(* constraint_set -> constraint_set -> constraint_set *)
fun unite (CSet (lits1, comps1, sexps1)) (CSet (lits2, comps2, sexps2)) =
    (case SOME lits1 |> fold do_literal lits2 of
       NONE => (print_g "**** Unsolvable"; UnsolvableCSet)
     | SOME lits => CSet (lits, comps1 @ comps2, sexps1 @ sexps2))
  | unite _ _ = UnsolvableCSet

(* sign -> bool *)
fun bool_from_sign Pos = false
  | bool_from_sign Neg = true
(* bool -> sign *)
fun sign_from_bool false = Pos
  | sign_from_bool true = Neg

(* literal -> PropLogic.prop_formula *)
fun prop_for_literal (x, sn) =
  (not (bool_from_sign sn) ? PropLogic.Not) (PropLogic.BoolVar x)
(* sign_atom -> PropLogic.prop_formula *)
fun prop_for_sign_atom_eq (S sn', sn) =
    if sn = sn' then PropLogic.True else PropLogic.False
  | prop_for_sign_atom_eq (V x, sn) = prop_for_literal (x, sn)
(* sign_expr -> PropLogic.prop_formula *)
fun prop_for_sign_expr xs = PropLogic.exists (map prop_for_literal xs)
(* var list -> sign -> PropLogic.prop_formula *)
fun prop_for_exists_eq xs sn =
  PropLogic.exists (map (fn x => prop_for_literal (x, sn)) xs)
(* comp -> PropLogic.prop_formula *)
fun prop_for_comp (a1, a2, Eq, []) =
    PropLogic.SAnd (prop_for_comp (a1, a2, Leq, []),
                    prop_for_comp (a2, a1, Leq, []))
  | prop_for_comp (a1, a2, Leq, []) =
    PropLogic.SOr (prop_for_sign_atom_eq (a1, Pos),
                   prop_for_sign_atom_eq (a2, Neg))
  | prop_for_comp (a1, a2, cmp, xs) =
    PropLogic.SOr (prop_for_exists_eq xs Neg, prop_for_comp (a1, a2, cmp, []))

(* var -> (int -> bool option) -> literal list -> literal list *)
fun literals_from_assignments max_var asgns lits =
  fold (fn x => fn accum =>
           if AList.defined (op =) lits x then
             accum
           else case asgns x of
             SOME b => (x, sign_from_bool b) :: accum
           | NONE => accum) (max_var downto 1) lits

(* literal list -> sign_atom -> sign option *)
fun lookup_sign_atom _ (S sn) = SOME sn
  | lookup_sign_atom lit (V x) = AList.lookup (op =) lit x

(* comp -> string *)
fun string_for_comp (a1, a2, cmp, xs) =
  string_for_sign_atom a1 ^ " " ^ string_for_comp_op cmp ^
  subscript_string_for_vars " \<and> " xs ^ " " ^ string_for_sign_atom a2

(* literal list -> comp list -> sign_expr list -> unit *)
fun print_problem lits comps sexps =
  print_g ("*** Problem:\n" ^ cat_lines (map string_for_literal lits @
                                         map string_for_comp comps @
                                         map string_for_sign_expr sexps))

(* literal list -> unit *)
fun print_solution lits =
  let val (pos, neg) = List.partition (equal Pos o snd) lits in
    print_g ("*** Solution:\n" ^
             "+: " ^ commas (map (string_for_var o fst) pos) ^ "\n" ^
             "-: " ^ commas (map (string_for_var o fst) neg))
  end

(* var -> constraint_set -> literal list list option *)
fun solve _ UnsolvableCSet = (print_g "*** Problem: Unsolvable"; NONE)
  | solve max_var (CSet (lits, comps, sexps)) =
    let
      val _ = print_problem lits comps sexps
      val prop = PropLogic.all (map prop_for_literal lits @
                                map prop_for_comp comps @
                                map prop_for_sign_expr sexps)
    in
      case SatSolver.invoke_solver "dpll" prop of
        SatSolver.SATISFIABLE asgns =>
        SOME (literals_from_assignments max_var asgns lits
              |> tap print_solution)
      | _ => NONE
    end

(* var -> constraint_set -> bool *)
val is_solvable = is_some oo solve

type ctype_schema = ctype * constraint_set
type ctype_context =
  {bounds: ctype list,
   frees: (styp * ctype) list,
   consts: (styp * ctype_schema) list}

type accumulator = ctype_context * constraint_set

val initial_gamma = {bounds = [], frees = [], consts = []}
val unsolvable_accum = (initial_gamma, UnsolvableCSet)

(* ctype -> ctype_context -> ctype_context *)
fun push_bound C {bounds, frees, consts} =
  {bounds = C :: bounds, frees = frees, consts = consts}
(* ctype_context -> ctype_context *)
fun pop_bound {bounds, frees, consts} =
  {bounds = tl bounds, frees = frees, consts = consts}
  handle List.Empty => initial_gamma

(* cdata -> term -> accumulator -> ctype * accumulator *)
fun consider_term (cdata as {ext_ctxt as {ctxt, thy, def_table, ...}, alpha_T,
                             max_fresh, ...}) =
  let
    (* typ -> ctype *)
    val ctype_for = fresh_ctype_for_type cdata
    (* ctype -> ctype *)
    fun pos_set_ctype_for_dom C =
      CFun (C, S (if exists_alpha_sub_ctype C then Pos else Neg), bool_C)
    (* typ -> accumulator -> ctype * accumulator *)
    fun do_quantifier T (gamma, cset) =
      let
        val abs_C = ctype_for (domain_type (domain_type T))
        val body_C = ctype_for (range_type T)
      in
        (CFun (CFun (abs_C, S Neg, body_C), S Neg, body_C),
         (gamma, cset |> add_ctype_is_right_total abs_C))
      end
    fun do_equals T (gamma, cset) =
      let val C = ctype_for (domain_type T) in
        (CFun (C, S Neg, CFun (C, S Neg, ctype_for (nth_range_type 2 T))),
         (gamma, cset |> add_ctype_is_right_unique C))
      end
    fun do_robust_set_operation T (gamma, cset) =
      let
        val set_T = domain_type T
        val C1 = ctype_for set_T
        val C2 = ctype_for set_T
        val C3 = ctype_for set_T
      in
        (CFun (C1, S Neg, CFun (C2, S Neg, C3)),
         (gamma, cset |> add_is_sub_ctype C1 C3 |> add_is_sub_ctype C2 C3))
      end
    fun do_fragile_set_operation T (gamma, cset) =
      let
        val set_T = domain_type T
        val set_C = ctype_for set_T
        (* typ -> ctype *)
        fun custom_ctype_for (T as Type ("fun", [T1, T2])) =
            if T = set_T then set_C
            else CFun (custom_ctype_for T1, S Neg, custom_ctype_for T2)
          | custom_ctype_for T = ctype_for T
      in
        (custom_ctype_for T, (gamma, cset |> add_ctype_is_right_unique set_C))
      end
    (* typ -> accumulator -> ctype * accumulator *)
    fun do_pair_constr T accum =
      case ctype_for (nth_range_type 2 T) of
        C as CPair (a_C, b_C) =>
        (CFun (a_C, S Neg, CFun (b_C, S Neg, C)), accum)
      | C => raise CTYPE ("Nitpick_Mono.consider_term.do_pair_constr", [C])
    (* int -> typ -> accumulator -> ctype * accumulator *)
    fun do_nth_pair_sel n T =
      case ctype_for (domain_type T) of
        C as CPair (a_C, b_C) =>
        pair (CFun (C, S Neg, if n = 0 then a_C else b_C))
      | C => raise CTYPE ("Nitpick_Mono.consider_term.do_nth_pair_sel", [C])
    val unsolvable = (CType ("unsolvable", []), unsolvable_accum)
    (* typ -> term -> accumulator -> ctype * accumulator *)
    fun do_bounded_quantifier abs_T bound_t body_t accum =
      let
        val abs_C = ctype_for abs_T
        val (bound_C, accum) = accum |>> push_bound abs_C |> do_term bound_t
        val expected_bound_C = pos_set_ctype_for_dom abs_C
      in
        accum ||> add_ctypes_equal expected_bound_C bound_C |> do_term body_t
              ||> apfst pop_bound
      end
    (* term -> accumulator -> ctype * accumulator *)
    and do_term _ (_, UnsolvableCSet) = unsolvable
      | do_term t (accum as (gamma as {bounds, frees, consts}, cset)) =
        (case t of
           Const (x as (s, T)) =>
           (case AList.lookup (op =) consts x of
              SOME (C, cset') => (C, (gamma, cset |> unite cset'))
            | NONE =>
              if not (could_exist_alpha_subtype alpha_T T) then
                (ctype_for T, accum)
              else case s of
                @{const_name all} => do_quantifier T accum
              | @{const_name "=="} => do_equals T accum
              | @{const_name All} => do_quantifier T accum
              | @{const_name Ex} => do_quantifier T accum
              | @{const_name "op ="} => do_equals T accum
              | @{const_name The} => (print_g "*** The"; unsolvable)
              | @{const_name Eps} => (print_g "*** Eps"; unsolvable)
              | @{const_name If} =>
                do_robust_set_operation (range_type T) accum
                |>> curry3 CFun bool_C (S Neg)
              | @{const_name Pair} => do_pair_constr T accum
              | @{const_name fst} => do_nth_pair_sel 0 T accum
              | @{const_name snd} => do_nth_pair_sel 1 T accum 
              | @{const_name Id} =>
                (CFun (ctype_for (domain_type T), S Neg, bool_C), accum)
              | @{const_name insert} =>
                let
                  val set_T = domain_type (range_type T)
                  val C1 = ctype_for (domain_type set_T)
                  val C1' = pos_set_ctype_for_dom C1
                  val C2 = ctype_for set_T
                  val C3 = ctype_for set_T
                in
                  (CFun (C1, S Neg, CFun (C2, S Neg, C3)),
                   (gamma, cset |> add_ctype_is_right_unique C1
                                |> add_is_sub_ctype C1' C3
                                |> add_is_sub_ctype C2 C3))
                end
              | @{const_name converse} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  (* typ -> ctype *)
                  fun ctype_for_set T =
                    CFun (ctype_for (domain_type T), V x, bool_C)
                  val ab_set_C = domain_type T |> ctype_for_set
                  val ba_set_C = range_type T |> ctype_for_set
                in (CFun (ab_set_C, S Neg, ba_set_C), accum) end
              | @{const_name trancl} => do_fragile_set_operation T accum
              | @{const_name rtrancl} => (print_g "*** rtrancl"; unsolvable)
              | @{const_name lower_semilattice_fun_inst.inf_fun} =>
                do_robust_set_operation T accum
              | @{const_name upper_semilattice_fun_inst.sup_fun} =>
                do_robust_set_operation T accum
              | @{const_name finite} =>
                let val C1 = ctype_for (domain_type (domain_type T)) in
                  (CFun (pos_set_ctype_for_dom C1, S Neg, bool_C), accum)
                end
              | @{const_name rel_comp} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  (* typ -> ctype *)
                  fun ctype_for_set T =
                    CFun (ctype_for (domain_type T), V x, bool_C)
                  val bc_set_C = domain_type T |> ctype_for_set
                  val ab_set_C = domain_type (range_type T) |> ctype_for_set
                  val ac_set_C = nth_range_type 2 T |> ctype_for_set
                in
                  (CFun (bc_set_C, S Neg, CFun (ab_set_C, S Neg, ac_set_C)),
                   accum)
                end
              | @{const_name image} =>
                let
                  val a_C = ctype_for (domain_type (domain_type T))
                  val b_C = ctype_for (range_type (domain_type T))
                in
                  (CFun (CFun (a_C, S Neg, b_C), S Neg,
                         CFun (pos_set_ctype_for_dom a_C, S Neg,
                               pos_set_ctype_for_dom b_C)), accum)
                end
              | @{const_name Sigma} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  (* typ -> ctype *)
                  fun ctype_for_set T =
                    CFun (ctype_for (domain_type T), V x, bool_C)
                  val a_set_T = domain_type T
                  val a_C = ctype_for (domain_type a_set_T)
                  val b_set_C = ctype_for_set (range_type (domain_type
                                                               (range_type T)))
                  val a_set_C = ctype_for_set a_set_T
                  val a_to_b_set_C = CFun (a_C, S Neg, b_set_C)
                  val ab_set_C = ctype_for_set (nth_range_type 2 T)
                in
                  (CFun (a_set_C, S Neg, CFun (a_to_b_set_C, S Neg, ab_set_C)),
                   accum)
                end
              | @{const_name minus_fun_inst.minus_fun} =>
                let
                  val set_T = domain_type T
                  val left_set_C = ctype_for set_T
                  val right_set_C = ctype_for set_T
                in
                  (CFun (left_set_C, S Neg,
                         CFun (right_set_C, S Neg, left_set_C)),
                   (gamma, cset |> add_ctype_is_right_unique right_set_C
                                |> add_is_sub_ctype right_set_C left_set_C))
                end
              | @{const_name ord_fun_inst.less_eq_fun} =>
                do_fragile_set_operation T accum
              | @{const_name Tha} =>
                let
                  val a_C = ctype_for (domain_type (domain_type T))
                  val a_set_C = pos_set_ctype_for_dom a_C
                in (CFun (a_set_C, S Neg, a_C), accum) end
              | @{const_name FunBox} =>
                let val dom_C = ctype_for (domain_type T) in
                  (CFun (dom_C, S Neg, dom_C), accum)
                end
              | _ => if is_sel s then
                       if constr_name_for_sel_like s = @{const_name FunBox} then
                         let val dom_C = ctype_for (domain_type T) in
                           (CFun (dom_C, S Neg, dom_C), accum)
                         end
                       else
                         (ctype_for_sel cdata x, accum)
                     else if is_constr thy x then
                       (ctype_for_constr cdata x, accum)
                     else if is_built_in_const true x then
                       case def_of_const thy def_table x of
                         SOME t' => do_term t' accum
                       | NONE => (print_g ("*** built-in " ^ s); unsolvable)
                     else
                       (ctype_for T, accum))
         | Free (x as (_, T)) =>
           (case AList.lookup (op =) frees x of
              SOME C => (C, accum)
            | NONE =>
              let val C = ctype_for T in
                (C, ({bounds = bounds, frees = (x, C) :: frees,
                      consts = consts}, cset))
              end)
         | Var _ => (print_g "*** Var"; unsolvable)
         | Bound j => (nth bounds j, accum)
         | Abs (_, T, @{const False}) => (ctype_for (T --> bool_T), accum)
         | Abs (s, T, t') =>
           let
             val C = ctype_for T
             val (C', accum) = do_term t' (accum |>> push_bound C)
           in (CFun (C, S Neg, C'), accum |>> pop_bound) end
         | Const (@{const_name All}, _)
           $ Abs (_, T', @{const "op -->"} $ (t1 $ Bound 0) $ t2) =>
           do_bounded_quantifier T' t1 t2 accum
         | Const (@{const_name Ex}, _)
           $ Abs (_, T', @{const "op &"} $ (t1 $ Bound 0) $ t2) =>
           do_bounded_quantifier T' t1 t2 accum
         | Const (@{const_name Let}, _) $ t1 $ t2 =>
           do_term (betapply (t2, t1)) accum
         | t1 $ t2 =>
           let
             val (C1, accum) = do_term t1 accum
             val (C2, accum) = do_term t2 accum
           in
             case accum of
               (_, UnsolvableCSet) => unsolvable
             | _ => case C1 of
                      CFun (C11, _, C12) =>
                      (C12, accum ||> add_is_sub_ctype C2 C11)
                    | _ => raise CTYPE ("Nitpick_Mono.consider_term.do_term \
                                        \(op $)", [C1])
           end)
        |> tap (fn (C, _) =>
                   print_g ("  \<Gamma> \<turnstile> " ^
                            Syntax.string_of_term ctxt t ^ " : " ^
                            string_for_ctype C))
  in do_term end

(* cdata -> sign -> term -> accumulator -> accumulator *)
fun consider_general_formula (cdata as {ext_ctxt as {ctxt, ...}, ...}) =
  let
    (* typ -> ctype *)
    val ctype_for = fresh_ctype_for_type cdata
    (* term -> accumulator -> accumulator *)
    val do_term = snd oo consider_term cdata
    (* sign -> term -> accumulator -> accumulator *)
    fun do_formula _ _ (_, UnsolvableCSet) = unsolvable_accum
      | do_formula sn t (accum as (gamma as {bounds, frees, consts}, cset)) =
        let
          (* term -> accumulator -> accumulator *)
          val do_co_formula = do_formula sn
          val do_contra_formula = do_formula (negate sn)
          (* string -> typ -> term -> accumulator *)
          fun do_quantifier quant_s abs_T body_t =
            let
              val abs_C = ctype_for abs_T
              val side_cond = ((sn = Neg) = (quant_s = @{const_name Ex}))
              val cset = cset |> side_cond ? add_ctype_is_right_total abs_C
            in
              (gamma |> push_bound abs_C, cset) |> do_co_formula body_t
                                                |>> pop_bound
            end
          (* typ -> term -> accumulator *)
          fun do_bounded_quantifier abs_T body_t =
            accum |>> push_bound (ctype_for abs_T) |> do_co_formula body_t
                  |>> pop_bound
          (* term -> term -> accumulator *)
          fun do_equals t1 t2 =
            case sn of
              Pos => do_term t accum
            | Neg => fold do_term [t1, t2] accum
        in
          case t of
            Const (s0 as @{const_name all}, _) $ Abs (_, T1, t1) =>
            do_quantifier s0 T1 t1
          | Const (@{const_name "=="}, _) $ t1 $ t2 => do_equals t1 t2
          | @{const "==>"} $ t1 $ t2 =>
            accum |> do_contra_formula t1 |> do_co_formula t2
          | @{const Trueprop} $ t1 => do_co_formula t1 accum
          | @{const Not} $ t1 => do_contra_formula t1 accum
          | Const (@{const_name All}, _)
            $ Abs (_, T1, t1 as @{const "op -->"} $ (_ $ Bound 0) $ _) =>
            do_bounded_quantifier T1 t1
          | Const (s0 as @{const_name All}, _) $ Abs (_, T1, t1) =>
            do_quantifier s0 T1 t1
          | Const (@{const_name Ex}, _)
            $ Abs (_, T1, t1 as @{const "op &"} $ (_ $ Bound 0) $ _) =>
            do_bounded_quantifier T1 t1
          | Const (s0 as @{const_name Ex}, _) $ Abs (_, T1, t1) =>
            do_quantifier s0 T1 t1
          | Const (@{const_name "op ="}, _) $ t1 $ t2 => do_equals t1 t2
          | @{const "op &"} $ t1 $ t2 =>
            accum |> do_co_formula t1 |> do_co_formula t2
          | @{const "op |"} $ t1 $ t2 =>
            accum |> do_co_formula t1 |> do_co_formula t2
          | @{const "op -->"} $ t1 $ t2 =>
            accum |> do_contra_formula t1 |> do_co_formula t2
          | Const (@{const_name If}, _) $ t1 $ t2 $ t3 =>
            accum |> do_term t1 |> fold do_co_formula [t2, t3]
          | Const (@{const_name Let}, _) $ t1 $ t2 =>
            do_co_formula (betapply (t2, t1)) accum
          | _ => do_term t accum
        end
        |> tap (fn _ => print_g ("\<Gamma> \<turnstile> " ^
                                 Syntax.string_of_term ctxt t ^
                                 " : o\<^sup>" ^ string_for_sign sn))
  in do_formula end

(* The harmless axiom optimization below is somewhat too aggressive in the face
   of (rather peculiar) user-defined axioms. *)
val harmless_consts =
  [@{const_name ord_class.less}, @{const_name ord_class.less_eq}]
val bounteous_consts = [@{const_name bisim}]

(* term -> bool *)
fun is_harmless_axiom t =
  Term.add_consts t [] |> filter_out (is_built_in_const true)
  |> (forall (member (op =) harmless_consts o original_name o fst)
      orf exists (member (op =) bounteous_consts o fst))

(* cdata -> sign -> term -> accumulator -> accumulator *)
fun consider_nondefinitional_axiom cdata sn t =
  not (is_harmless_axiom t) ? consider_general_formula cdata sn t

(* cdata -> term -> accumulator -> accumulator *)
fun consider_definitional_axiom (cdata as {ext_ctxt as {thy, ...}, ...}) t =
  if not (is_constr_pattern_formula thy t) then
    consider_nondefinitional_axiom cdata Pos t
  else if is_harmless_axiom t then
    I
  else
    let
      (* term -> accumulator -> accumulator *)
      val do_term = consider_term cdata
      (* typ -> term -> accumulator -> accumulator *)
      fun do_all abs_T body_t accum =
        let val abs_C = fresh_ctype_for_type cdata abs_T in
          accum |>> push_bound abs_C |> do_formula body_t |>> pop_bound
        end
      (* term -> term -> accumulator -> accumulator *)
      and do_implies t1 t2 = do_term t1 #> snd #> do_formula t2
      and do_equals t1 t2 accum =
        let
          val (C1, accum) = do_term t1 accum
          val (C2, accum) = do_term t2 accum
        in accum ||> add_ctypes_equal C1 C2 end
      (* term -> accumulator -> accumulator *)
      and do_formula _ (_, UnsolvableCSet) = unsolvable_accum
        | do_formula t accum =
          case t of
            Const (@{const_name all}, _) $ Abs (_, T1, t1) => do_all T1 t1 accum
          | @{const Trueprop} $ t1 => do_formula t1 accum
          | Const (@{const_name "=="}, _) $ t1 $ t2 => do_equals t1 t2 accum
          | @{const "==>"} $ t1 $ t2 => do_implies t1 t2 accum
          | @{const Pure.conjunction} $ t1 $ t2 =>
            accum |> do_formula t1 |> do_formula t2
          | Const (@{const_name All}, _) $ Abs (_, T1, t1) => do_all T1 t1 accum
          | Const (@{const_name "op ="}, _) $ t1 $ t2 => do_equals t1 t2 accum
          | @{const "op &"} $ t1 $ t2 => accum |> do_formula t1 |> do_formula t2
          | @{const "op -->"} $ t1 $ t2 => do_implies t1 t2 accum
          | _ => raise TERM ("Nitpick_Mono.consider_definitional_axiom.\
                             \do_formula", [t])
    in do_formula t end

(* Proof.context -> literal list -> term -> ctype -> string *)
fun string_for_ctype_of_term ctxt lits t C =
  Syntax.string_of_term ctxt t ^ " : " ^
  string_for_ctype (instantiate_ctype lits C)

(* theory -> literal list -> ctype_context -> unit *)
fun print_ctype_context ctxt lits ({frees, consts, ...} : ctype_context) =
  map (fn (x, C) => string_for_ctype_of_term ctxt lits (Free x) C) frees @
  map (fn (x, (C, _)) => string_for_ctype_of_term ctxt lits (Const x) C) consts
  |> cat_lines |> print_g

(* extended_context -> typ -> term list -> term list -> term -> bool *)
fun formulas_monotonic (ext_ctxt as {ctxt, ...}) alpha_T def_ts nondef_ts
                       core_t =
  let
    val _ = print_g ("****** " ^ string_for_ctype CAlpha ^ " is " ^
                     Syntax.string_of_typ ctxt alpha_T)
    val cdata as {max_fresh, ...} = initial_cdata ext_ctxt alpha_T
    val (gamma, cset) =
      (initial_gamma, slack)
      |> fold (consider_definitional_axiom cdata) def_ts
      |> fold (consider_nondefinitional_axiom cdata Pos) nondef_ts
      |> consider_general_formula cdata Pos core_t
  in
    case solve (!max_fresh) cset of
      SOME lits => (print_ctype_context ctxt lits gamma; true)
    | _ => false
  end
  handle CTYPE (loc, Cs) => raise BAD (loc, commas (map string_for_ctype Cs))

end;
