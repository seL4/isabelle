(*  Title:      HOL/Tools/Nitpick/nitpick_mono.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009, 2010

Monotonicity inference for higher-order logic.
*)

signature NITPICK_MONO =
sig
  type hol_context = Nitpick_HOL.hol_context

  val trace : bool Unsynchronized.ref
  val formulas_monotonic :
    hol_context -> bool -> typ -> term list * term list -> bool
  val finitize_funs :
    hol_context -> bool -> (typ option * bool option) list -> typ
    -> term list * term list -> term list * term list
end;

structure Nitpick_Mono : NITPICK_MONO =
struct

open Nitpick_Util
open Nitpick_HOL

type var = int

datatype sign = Plus | Minus
datatype sign_atom = S of sign | V of var

type literal = var * sign

datatype mtyp =
  MAlpha |
  MFun of mtyp * sign_atom * mtyp |
  MPair of mtyp * mtyp |
  MType of string * mtyp list |
  MRec of string * typ list

datatype mterm =
  MRaw of term * mtyp |
  MAbs of string * typ * mtyp * sign_atom * mterm |
  MApp of mterm * mterm

type mdata =
  {hol_ctxt: hol_context,
   binarize: bool,
   alpha_T: typ,
   no_harmless: bool,
   max_fresh: int Unsynchronized.ref,
   datatype_mcache: ((string * typ list) * mtyp) list Unsynchronized.ref,
   constr_mcache: (styp * mtyp) list Unsynchronized.ref}

exception UNSOLVABLE of unit
exception MTYPE of string * mtyp list * typ list
exception MTERM of string * mterm list

val trace = Unsynchronized.ref false
fun trace_msg msg = if !trace then tracing (msg ()) else ()

val string_for_var = signed_string_of_int
fun string_for_vars sep [] = "0\<^bsub>" ^ sep ^ "\<^esub>"
  | string_for_vars sep xs = space_implode sep (map string_for_var xs)
fun subscript_string_for_vars sep xs =
  if null xs then "" else "\<^bsub>" ^ string_for_vars sep xs ^ "\<^esub>"

fun string_for_sign Plus = "+"
  | string_for_sign Minus = "-"

fun xor sn1 sn2 = if sn1 = sn2 then Plus else Minus
val negate = xor Minus

fun string_for_sign_atom (S sn) = string_for_sign sn
  | string_for_sign_atom (V x) = string_for_var x

fun string_for_literal (x, sn) = string_for_var x ^ " = " ^ string_for_sign sn

val bool_M = MType (@{type_name bool}, [])
val dummy_M = MType (nitpick_prefix ^ "dummy", [])

fun is_MRec (MRec _) = true
  | is_MRec _ = false
fun dest_MFun (MFun z) = z
  | dest_MFun M = raise MTYPE ("Nitpick_Mono.dest_MFun", [M], [])

val no_prec = 100

fun precedence_of_mtype (MFun _) = 1
  | precedence_of_mtype (MPair _) = 2
  | precedence_of_mtype _ = no_prec

val string_for_mtype =
  let
    fun aux outer_prec M =
      let
        val prec = precedence_of_mtype M
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then "(" else "") ^
        (if M = dummy_M then
           "_"
         else case M of
             MAlpha => "\<alpha>"
           | MFun (M1, a, M2) =>
             aux (prec + 1) M1 ^ " \<Rightarrow>\<^bsup>" ^
             string_for_sign_atom a ^ "\<^esup> " ^ aux prec M2
           | MPair (M1, M2) => aux (prec + 1) M1 ^ " \<times> " ^ aux prec M2
           | MType (s, []) =>
             if s = @{type_name prop} orelse s = @{type_name bool} then "o"
             else s
           | MType (s, Ms) => "(" ^ commas (map (aux 0) Ms) ^ ") " ^ s
           | MRec (s, _) => "[" ^ s ^ "]") ^
        (if need_parens then ")" else "")
      end
  in aux 0 end

fun flatten_mtype (MPair (M1, M2)) = maps flatten_mtype [M1, M2]
  | flatten_mtype (MType (_, Ms)) = maps flatten_mtype Ms
  | flatten_mtype M = [M]

fun precedence_of_mterm (MRaw _) = no_prec
  | precedence_of_mterm (MAbs _) = 1
  | precedence_of_mterm (MApp _) = 2

fun string_for_mterm ctxt =
  let
    fun mtype_annotation M = "\<^bsup>" ^ string_for_mtype M ^ "\<^esup>"
    fun aux outer_prec m =
      let
        val prec = precedence_of_mterm m
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then "(" else "") ^
        (case m of
           MRaw (t, M) => Syntax.string_of_term ctxt t ^ mtype_annotation M
         | MAbs (s, _, M, a, m) =>
           "\<lambda>" ^ s ^ mtype_annotation M ^ ".\<^bsup>" ^
           string_for_sign_atom a ^ "\<^esup> " ^ aux prec m
         | MApp (m1, m2) => aux prec m1 ^ " " ^ aux (prec + 1) m2) ^
        (if need_parens then ")" else "")
      end
  in aux 0 end

fun mtype_of_mterm (MRaw (_, M)) = M
  | mtype_of_mterm (MAbs (_, _, M, a, m)) = MFun (M, a, mtype_of_mterm m)
  | mtype_of_mterm (MApp (m1, _)) =
    case mtype_of_mterm m1 of
      MFun (_, _, M12) => M12
    | M1 => raise MTYPE ("Nitpick_Mono.mtype_of_mterm", [M1], [])

fun strip_mcomb (MApp (m1, m2)) = strip_mcomb m1 ||> (fn ms => append ms [m2])
  | strip_mcomb m = (m, [])

fun initial_mdata hol_ctxt binarize no_harmless alpha_T =
  ({hol_ctxt = hol_ctxt, binarize = binarize, alpha_T = alpha_T,
    no_harmless = no_harmless, max_fresh = Unsynchronized.ref 0,
    datatype_mcache = Unsynchronized.ref [],
    constr_mcache = Unsynchronized.ref []} : mdata)

fun could_exist_alpha_subtype alpha_T (T as Type (_, Ts)) =
    T = alpha_T orelse (not (is_fp_iterator_type T) andalso
                        exists (could_exist_alpha_subtype alpha_T) Ts)
  | could_exist_alpha_subtype alpha_T T = (T = alpha_T)
fun could_exist_alpha_sub_mtype _ (alpha_T as TFree _) T =
    could_exist_alpha_subtype alpha_T T
  | could_exist_alpha_sub_mtype ctxt alpha_T T =
    (T = alpha_T orelse is_datatype ctxt [(NONE, true)] T)

fun exists_alpha_sub_mtype MAlpha = true
  | exists_alpha_sub_mtype (MFun (M1, _, M2)) =
    exists exists_alpha_sub_mtype [M1, M2]
  | exists_alpha_sub_mtype (MPair (M1, M2)) =
    exists exists_alpha_sub_mtype [M1, M2]
  | exists_alpha_sub_mtype (MType (_, Ms)) = exists exists_alpha_sub_mtype Ms
  | exists_alpha_sub_mtype (MRec _) = true

fun exists_alpha_sub_mtype_fresh MAlpha = true
  | exists_alpha_sub_mtype_fresh (MFun (_, V _, _)) = true
  | exists_alpha_sub_mtype_fresh (MFun (_, _, M2)) =
    exists_alpha_sub_mtype_fresh M2
  | exists_alpha_sub_mtype_fresh (MPair (M1, M2)) =
    exists exists_alpha_sub_mtype_fresh [M1, M2]
  | exists_alpha_sub_mtype_fresh (MType (_, Ms)) =
    exists exists_alpha_sub_mtype_fresh Ms
  | exists_alpha_sub_mtype_fresh (MRec _) = true

fun constr_mtype_for_binders z Ms =
  fold_rev (fn M => curry3 MFun M (S Minus)) Ms (MRec z)

fun repair_mtype _ _ MAlpha = MAlpha
  | repair_mtype cache seen (MFun (M1, a, M2)) =
    MFun (repair_mtype cache seen M1, a, repair_mtype cache seen M2)
  | repair_mtype cache seen (MPair Mp) =
    MPair (pairself (repair_mtype cache seen) Mp)
  | repair_mtype cache seen (MType (s, Ms)) =
    MType (s, maps (flatten_mtype o repair_mtype cache seen) Ms)
  | repair_mtype cache seen (MRec (z as (s, _))) =
    case AList.lookup (op =) cache z |> the of
      MRec _ => MType (s, [])
    | M => if member (op =) seen M then MType (s, [])
           else repair_mtype cache (M :: seen) M

fun repair_datatype_mcache cache =
  let
    fun repair_one (z, M) =
      Unsynchronized.change cache
          (AList.update (op =) (z, repair_mtype (!cache) [] M))
  in List.app repair_one (rev (!cache)) end

fun repair_constr_mcache dtype_cache constr_mcache =
  let
    fun repair_one (x, M) =
      Unsynchronized.change constr_mcache
          (AList.update (op =) (x, repair_mtype dtype_cache [] M))
  in List.app repair_one (!constr_mcache) end

fun is_fin_fun_supported_type @{typ prop} = true
  | is_fin_fun_supported_type @{typ bool} = true
  | is_fin_fun_supported_type (Type (@{type_name option}, _)) = true
  | is_fin_fun_supported_type _ = false
fun fin_fun_body _ _ (t as @{term False}) = SOME t
  | fin_fun_body _ _ (t as Const (@{const_name None}, _)) = SOME t
  | fin_fun_body dom_T ran_T
                 ((t0 as Const (@{const_name If}, _))
                  $ (t1 as Const (@{const_name HOL.eq}, _) $ Bound 0 $ t1')
                  $ t2 $ t3) =
    (if loose_bvar1 (t1', 0) then
       NONE
     else case fin_fun_body dom_T ran_T t3 of
       NONE => NONE
     | SOME t3 =>
       SOME (t0 $ (Const (@{const_name is_unknown}, dom_T --> bool_T) $ t1')
                $ (Const (@{const_name unknown}, ran_T)) $ (t0 $ t1 $ t2 $ t3)))
  | fin_fun_body _ _ _ = NONE

fun fresh_mfun_for_fun_type (mdata as {max_fresh, ...} : mdata) all_minus
                            T1 T2 =
  let
    val M1 = fresh_mtype_for_type mdata all_minus T1
    val M2 = fresh_mtype_for_type mdata all_minus T2
    val a = if not all_minus andalso exists_alpha_sub_mtype_fresh M1 andalso
               is_fin_fun_supported_type (body_type T2) then
              V (Unsynchronized.inc max_fresh)
            else
              S Minus
  in (M1, a, M2) end
and fresh_mtype_for_type (mdata as {hol_ctxt as {ctxt, ...}, binarize, alpha_T,
                                    datatype_mcache, constr_mcache, ...})
                         all_minus =
  let
    fun do_type T =
      if T = alpha_T then
        MAlpha
      else case T of
        Type (@{type_name fun}, [T1, T2]) =>
        MFun (fresh_mfun_for_fun_type mdata false T1 T2)
      | Type (@{type_name prod}, [T1, T2]) => MPair (pairself do_type (T1, T2))
      | Type (z as (s, _)) =>
        if could_exist_alpha_sub_mtype ctxt alpha_T T then
          case AList.lookup (op =) (!datatype_mcache) z of
            SOME M => M
          | NONE =>
            let
              val _ = Unsynchronized.change datatype_mcache (cons (z, MRec z))
              val xs = binarized_and_boxed_datatype_constrs hol_ctxt binarize T
              val (all_Ms, constr_Ms) =
                fold_rev (fn (_, T') => fn (all_Ms, constr_Ms) =>
                             let
                               val binder_Ms = map do_type (binder_types T')
                               val new_Ms = filter exists_alpha_sub_mtype_fresh
                                                   binder_Ms
                               val constr_M = constr_mtype_for_binders z
                                                                       binder_Ms
                             in
                               (union (op =) new_Ms all_Ms,
                                constr_M :: constr_Ms)
                             end)
                         xs ([], [])
              val M = MType (s, all_Ms)
              val _ = Unsynchronized.change datatype_mcache
                          (AList.update (op =) (z, M))
              val _ = Unsynchronized.change constr_mcache
                          (append (xs ~~ constr_Ms))
            in
              if forall (not o is_MRec o snd) (!datatype_mcache) then
                (repair_datatype_mcache datatype_mcache;
                 repair_constr_mcache (!datatype_mcache) constr_mcache;
                 AList.lookup (op =) (!datatype_mcache) z |> the)
              else
                M
            end
        else
          MType (s, [])
      | _ => MType (simple_string_of_typ T, [])
  in do_type end

fun prodM_factors (MPair (M1, M2)) = maps prodM_factors [M1, M2]
  | prodM_factors M = [M]
fun curried_strip_mtype (MFun (M1, _, M2)) =
    curried_strip_mtype M2 |>> append (prodM_factors M1)
  | curried_strip_mtype M = ([], M)
fun sel_mtype_from_constr_mtype s M =
  let val (arg_Ms, dataM) = curried_strip_mtype M in
    MFun (dataM, S Minus,
          case sel_no_from_name s of ~1 => bool_M | n => nth arg_Ms n)
  end

fun mtype_for_constr (mdata as {hol_ctxt = {ctxt, ...}, alpha_T, constr_mcache,
                                ...}) (x as (_, T)) =
  if could_exist_alpha_sub_mtype ctxt alpha_T T then
    case AList.lookup (op =) (!constr_mcache) x of
      SOME M => M
    | NONE => if T = alpha_T then
                let val M = fresh_mtype_for_type mdata false T in
                  (Unsynchronized.change constr_mcache (cons (x, M)); M)
                end
              else
                (fresh_mtype_for_type mdata false (body_type T);
                 AList.lookup (op =) (!constr_mcache) x |> the)
  else
    fresh_mtype_for_type mdata false T
fun mtype_for_sel (mdata as {hol_ctxt, binarize, ...}) (x as (s, _)) =
  x |> binarized_and_boxed_constr_for_sel hol_ctxt binarize
    |> mtype_for_constr mdata |> sel_mtype_from_constr_mtype s

fun resolve_sign_atom lits (V x) =
    x |> AList.lookup (op =) lits |> Option.map S |> the_default (V x)
  | resolve_sign_atom _ a = a
fun resolve_mtype lits =
  let
    fun aux MAlpha = MAlpha
      | aux (MFun (M1, a, M2)) = MFun (aux M1, resolve_sign_atom lits a, aux M2)
      | aux (MPair Mp) = MPair (pairself aux Mp)
      | aux (MType (s, Ms)) = MType (s, map aux Ms)
      | aux (MRec z) = MRec z
  in aux end

datatype comp_op = Eq | Leq

type comp = sign_atom * sign_atom * comp_op * var list
type sign_expr = literal list

type constraint_set = literal list * comp list * sign_expr list

fun string_for_comp_op Eq = "="
  | string_for_comp_op Leq = "\<le>"

fun string_for_sign_expr [] = "\<bot>"
  | string_for_sign_expr lits =
    space_implode " \<or> " (map string_for_literal lits)

fun do_literal _ NONE = NONE
  | do_literal (x, sn) (SOME lits) =
    case AList.lookup (op =) lits x of
      SOME sn' => if sn = sn' then SOME lits else NONE
    | NONE => SOME ((x, sn) :: lits)

fun do_sign_atom_comp Eq [] a1 a2 (accum as (lits, comps)) =
    (case (a1, a2) of
       (S sn1, S sn2) => if sn1 = sn2 then SOME accum else NONE
     | (V x1, S sn2) =>
       Option.map (rpair comps) (do_literal (x1, sn2) (SOME lits))
     | (V _, V _) => SOME (lits, insert (op =) (a1, a2, Eq, []) comps)
     | _ => do_sign_atom_comp Eq [] a2 a1 accum)
  | do_sign_atom_comp Leq [] a1 a2 (accum as (lits, comps)) =
    (case (a1, a2) of
       (_, S Minus) => SOME accum
     | (S Plus, _) => SOME accum
     | (S Minus, S Plus) => NONE
     | (V _, V _) => SOME (lits, insert (op =) (a1, a2, Leq, []) comps)
     | _ => do_sign_atom_comp Eq [] a1 a2 accum)
  | do_sign_atom_comp cmp xs a1 a2 (lits, comps) =
    SOME (lits, insert (op =) (a1, a2, cmp, xs) comps)

fun do_mtype_comp _ _ _ _ NONE = NONE
  | do_mtype_comp _ _ MAlpha MAlpha accum = accum
  | do_mtype_comp Eq xs (MFun (M11, a1, M12)) (MFun (M21, a2, M22))
                  (SOME accum) =
     accum |> do_sign_atom_comp Eq xs a1 a2 |> do_mtype_comp Eq xs M11 M21
           |> do_mtype_comp Eq xs M12 M22
  | do_mtype_comp Leq xs (MFun (M11, a1, M12)) (MFun (M21, a2, M22))
                  (SOME accum) =
    (if exists_alpha_sub_mtype M11 then
       accum |> do_sign_atom_comp Leq xs a1 a2
             |> do_mtype_comp Leq xs M21 M11
             |> (case a2 of
                   S Minus => I
                 | S Plus => do_mtype_comp Leq xs M11 M21
                 | V x => do_mtype_comp Leq (x :: xs) M11 M21)
     else
       SOME accum)
    |> do_mtype_comp Leq xs M12 M22
  | do_mtype_comp cmp xs (M1 as MPair (M11, M12)) (M2 as MPair (M21, M22))
                  accum =
    (accum |> fold (uncurry (do_mtype_comp cmp xs)) [(M11, M21), (M12, M22)]
     handle Library.UnequalLengths =>
            raise MTYPE ("Nitpick_Mono.do_mtype_comp", [M1, M2], []))
  | do_mtype_comp _ _ (MType _) (MType _) accum =
    accum (* no need to compare them thanks to the cache *)
  | do_mtype_comp cmp _ M1 M2 _ =
    raise MTYPE ("Nitpick_Mono.do_mtype_comp (" ^ string_for_comp_op cmp ^ ")",
                 [M1, M2], [])

fun add_mtype_comp cmp M1 M2 ((lits, comps, sexps) : constraint_set) =
    (trace_msg (fn () => "*** Add " ^ string_for_mtype M1 ^ " " ^
                         string_for_comp_op cmp ^ " " ^ string_for_mtype M2);
     case do_mtype_comp cmp [] M1 M2 (SOME (lits, comps)) of
       NONE => (trace_msg (K "**** Unsolvable"); raise UNSOLVABLE ())
     | SOME (lits, comps) => (lits, comps, sexps))

val add_mtypes_equal = add_mtype_comp Eq
val add_is_sub_mtype = add_mtype_comp Leq

fun do_notin_mtype_fv _ _ _ NONE = NONE
  | do_notin_mtype_fv Minus _ MAlpha accum = accum
  | do_notin_mtype_fv Plus [] MAlpha _ = NONE
  | do_notin_mtype_fv Plus [(x, sn)] MAlpha (SOME (lits, sexps)) =
    SOME lits |> do_literal (x, sn) |> Option.map (rpair sexps)
  | do_notin_mtype_fv Plus sexp MAlpha (SOME (lits, sexps)) =
    SOME (lits, insert (op =) sexp sexps)
  | do_notin_mtype_fv sn sexp (MFun (M1, S sn', M2)) accum =
    accum |> (if sn' = Plus andalso sn = Plus then
                do_notin_mtype_fv Plus sexp M1
              else
                I)
          |> (if sn' = Minus orelse sn = Plus then
                do_notin_mtype_fv Minus sexp M1
              else
                I)
          |> do_notin_mtype_fv sn sexp M2
  | do_notin_mtype_fv Plus sexp (MFun (M1, V x, M2)) accum =
    accum |> (case do_literal (x, Minus) (SOME sexp) of
                NONE => I
              | SOME sexp' => do_notin_mtype_fv Plus sexp' M1)
          |> do_notin_mtype_fv Minus sexp M1
          |> do_notin_mtype_fv Plus sexp M2
  | do_notin_mtype_fv Minus sexp (MFun (M1, V x, M2)) accum =
    accum |> (case do_literal (x, Plus) (SOME sexp) of
                NONE => I
              | SOME sexp' => do_notin_mtype_fv Plus sexp' M1)
          |> do_notin_mtype_fv Minus sexp M2
  | do_notin_mtype_fv sn sexp (MPair (M1, M2)) accum =
    accum |> fold (do_notin_mtype_fv sn sexp) [M1, M2]
  | do_notin_mtype_fv sn sexp (MType (_, Ms)) accum =
    accum |> fold (do_notin_mtype_fv sn sexp) Ms
  | do_notin_mtype_fv _ _ M _ =
    raise MTYPE ("Nitpick_Mono.do_notin_mtype_fv", [M], [])

fun add_notin_mtype_fv sn M ((lits, comps, sexps) : constraint_set) =
    (trace_msg (fn () => "*** Add " ^ string_for_mtype M ^ " is " ^
                         (case sn of Minus => "concrete" | Plus => "complete") ^
                         ".");
     case do_notin_mtype_fv sn [] M (SOME (lits, sexps)) of
       NONE => (trace_msg (K "**** Unsolvable"); raise UNSOLVABLE ())
     | SOME (lits, sexps) => (lits, comps, sexps))

val add_mtype_is_concrete = add_notin_mtype_fv Minus
val add_mtype_is_complete = add_notin_mtype_fv Plus

val bool_from_minus = true

fun bool_from_sign Plus = not bool_from_minus
  | bool_from_sign Minus = bool_from_minus
fun sign_from_bool b = if b = bool_from_minus then Minus else Plus

fun prop_for_literal (x, sn) =
  (not (bool_from_sign sn) ? PropLogic.Not) (PropLogic.BoolVar x)
fun prop_for_sign_atom_eq (S sn', sn) =
    if sn = sn' then PropLogic.True else PropLogic.False
  | prop_for_sign_atom_eq (V x, sn) = prop_for_literal (x, sn)
fun prop_for_sign_expr xs = PropLogic.exists (map prop_for_literal xs)
fun prop_for_exists_eq xs sn =
  PropLogic.exists (map (fn x => prop_for_literal (x, sn)) xs)
fun prop_for_comp (a1, a2, Eq, []) =
    PropLogic.SAnd (prop_for_comp (a1, a2, Leq, []),
                    prop_for_comp (a2, a1, Leq, []))
  | prop_for_comp (a1, a2, Leq, []) =
    PropLogic.SOr (prop_for_sign_atom_eq (a1, Plus),
                   prop_for_sign_atom_eq (a2, Minus))
  | prop_for_comp (a1, a2, cmp, xs) =
    PropLogic.SOr (prop_for_exists_eq xs Minus, prop_for_comp (a1, a2, cmp, []))

fun literals_from_assignments max_var assigns lits =
  fold (fn x => fn accum =>
           if AList.defined (op =) lits x then
             accum
           else case assigns x of
             SOME b => (x, sign_from_bool b) :: accum
           | NONE => accum) (max_var downto 1) lits

fun string_for_comp (a1, a2, cmp, xs) =
  string_for_sign_atom a1 ^ " " ^ string_for_comp_op cmp ^
  subscript_string_for_vars " \<and> " xs ^ " " ^ string_for_sign_atom a2

fun print_problem lits comps sexps =
  trace_msg (fn () => "*** Problem:\n" ^
                      cat_lines (map string_for_literal lits @
                                 map string_for_comp comps @
                                 map string_for_sign_expr sexps))

fun print_solution lits =
  let val (pos, neg) = List.partition (curry (op =) Plus o snd) lits in
    trace_msg (fn () => "*** Solution:\n" ^
                        "+: " ^ commas (map (string_for_var o fst) pos) ^ "\n" ^
                        "-: " ^ commas (map (string_for_var o fst) neg))
  end

fun solve max_var (lits, comps, sexps) =
    let
      fun do_assigns assigns =
        SOME (literals_from_assignments max_var assigns lits
              |> tap print_solution)
      val _ = print_problem lits comps sexps
      val prop = PropLogic.all (map prop_for_literal lits @
                                map prop_for_comp comps @
                                map prop_for_sign_expr sexps)
      val default_val = bool_from_sign Minus
    in
      if PropLogic.eval (K default_val) prop then
        do_assigns (K (SOME default_val))
      else
        let
          (* use the first ML solver (to avoid startup overhead) *)
          val solvers = !SatSolver.solvers
                        |> filter (member (op =) ["dptsat", "dpll"] o fst)
        in
          case snd (hd solvers) prop of
            SatSolver.SATISFIABLE assigns => do_assigns assigns
          | _ => NONE
        end
    end

type mtype_schema = mtyp * constraint_set
type mtype_context =
  {bound_Ts: typ list,
   bound_Ms: mtyp list,
   frees: (styp * mtyp) list,
   consts: (styp * mtyp) list}

type accumulator = mtype_context * constraint_set

val initial_gamma = {bound_Ts = [], bound_Ms = [], frees = [], consts = []}

fun push_bound T M {bound_Ts, bound_Ms, frees, consts} =
  {bound_Ts = T :: bound_Ts, bound_Ms = M :: bound_Ms, frees = frees,
   consts = consts}
fun pop_bound {bound_Ts, bound_Ms, frees, consts} =
  {bound_Ts = tl bound_Ts, bound_Ms = tl bound_Ms, frees = frees,
   consts = consts}
  handle List.Empty => initial_gamma (* FIXME: needed? *)

fun consider_term (mdata as {hol_ctxt as {thy, ctxt, stds, fast_descrs,
                                          def_table, ...},
                             alpha_T, max_fresh, ...}) =
  let
    fun is_enough_eta_expanded t =
      case strip_comb t of
        (Const x, ts) =>
        the_default 0 (arity_of_built_in_const thy stds fast_descrs x)
        <= length ts
      | _ => true
    val mtype_for = fresh_mtype_for_type mdata false
    fun plus_set_mtype_for_dom M =
      MFun (M, S (if exists_alpha_sub_mtype M then Plus else Minus), bool_M)
    fun do_all T (gamma, cset) =
      let
        val abs_M = mtype_for (domain_type (domain_type T))
        val body_M = mtype_for (body_type T)
      in
        (MFun (MFun (abs_M, S Minus, body_M), S Minus, body_M),
         (gamma, cset |> add_mtype_is_complete abs_M))
      end
    fun do_equals T (gamma, cset) =
      let val M = mtype_for (domain_type T) in
        (MFun (M, S Minus, MFun (M, V (Unsynchronized.inc max_fresh),
                                 mtype_for (nth_range_type 2 T))),
         (gamma, cset |> add_mtype_is_concrete M))
      end
    fun do_robust_set_operation T (gamma, cset) =
      let
        val set_T = domain_type T
        val M1 = mtype_for set_T
        val M2 = mtype_for set_T
        val M3 = mtype_for set_T
      in
        (MFun (M1, S Minus, MFun (M2, S Minus, M3)),
         (gamma, cset |> add_is_sub_mtype M1 M3 |> add_is_sub_mtype M2 M3))
      end
    fun do_fragile_set_operation T (gamma, cset) =
      let
        val set_T = domain_type T
        val set_M = mtype_for set_T
        fun custom_mtype_for (T as Type (@{type_name fun}, [T1, T2])) =
            if T = set_T then set_M
            else MFun (custom_mtype_for T1, S Minus, custom_mtype_for T2)
          | custom_mtype_for T = mtype_for T
      in
        (custom_mtype_for T, (gamma, cset |> add_mtype_is_concrete set_M))
      end
    fun do_pair_constr T accum =
      case mtype_for (nth_range_type 2 T) of
        M as MPair (a_M, b_M) =>
        (MFun (a_M, S Minus, MFun (b_M, S Minus, M)), accum)
      | M => raise MTYPE ("Nitpick_Mono.consider_term.do_pair_constr", [M], [])
    fun do_nth_pair_sel n T =
      case mtype_for (domain_type T) of
        M as MPair (a_M, b_M) =>
        pair (MFun (M, S Minus, if n = 0 then a_M else b_M))
      | M => raise MTYPE ("Nitpick_Mono.consider_term.do_nth_pair_sel", [M], [])
    fun do_bounded_quantifier t0 abs_s abs_T connective_t bound_t body_t accum =
      let
        val abs_M = mtype_for abs_T
        val (bound_m, accum) =
          accum |>> push_bound abs_T abs_M |> do_term bound_t
        val expected_bound_M = plus_set_mtype_for_dom abs_M
        val (body_m, accum) =
          accum ||> add_mtypes_equal expected_bound_M (mtype_of_mterm bound_m)
                |> do_term body_t ||> apfst pop_bound
        val bound_M = mtype_of_mterm bound_m
        val (M1, a, M2) = dest_MFun bound_M
      in
        (MApp (MRaw (t0, MFun (bound_M, S Minus, bool_M)),
               MAbs (abs_s, abs_T, M1, a,
                     MApp (MApp (MRaw (connective_t,
                                       mtype_for (fastype_of connective_t)),
                                 MApp (bound_m, MRaw (Bound 0, M1))),
                           body_m))), accum)
      end
    and do_term t (accum as (gamma as {bound_Ts, bound_Ms, frees, consts},
                             cset)) =
        (trace_msg (fn () => "  \<Gamma> \<turnstile> " ^
                             Syntax.string_of_term ctxt t ^ " : _?");
         case t of
           Const (x as (s, T)) =>
           (case AList.lookup (op =) consts x of
              SOME M => (M, accum)
            | NONE =>
              if not (could_exist_alpha_subtype alpha_T T) then
                (mtype_for T, accum)
              else case s of
                @{const_name all} => do_all T accum
              | @{const_name "=="} => do_equals T accum
              | @{const_name All} => do_all T accum
              | @{const_name Ex} =>
                let val set_T = domain_type T in
                  do_term (Abs (Name.uu, set_T,
                                @{const Not} $ (HOLogic.mk_eq
                                    (Abs (Name.uu, domain_type set_T,
                                          @{const False}),
                                     Bound 0)))) accum
                  |>> mtype_of_mterm
                end
              | @{const_name HOL.eq} => do_equals T accum
              | @{const_name The} =>
                (trace_msg (K "*** The"); raise UNSOLVABLE ())
              | @{const_name Eps} =>
                (trace_msg (K "*** Eps"); raise UNSOLVABLE ())
              | @{const_name If} =>
                do_robust_set_operation (range_type T) accum
                |>> curry3 MFun bool_M (S Minus)
              | @{const_name Pair} => do_pair_constr T accum
              | @{const_name fst} => do_nth_pair_sel 0 T accum
              | @{const_name snd} => do_nth_pair_sel 1 T accum 
              | @{const_name Id} =>
                (MFun (mtype_for (domain_type T), S Minus, bool_M), accum)
              | @{const_name converse} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  fun mtype_for_set T =
                    MFun (mtype_for (domain_type T), V x, bool_M)
                  val ab_set_M = domain_type T |> mtype_for_set
                  val ba_set_M = range_type T |> mtype_for_set
                in (MFun (ab_set_M, S Minus, ba_set_M), accum) end
              | @{const_name trancl} => do_fragile_set_operation T accum
              | @{const_name rel_comp} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  fun mtype_for_set T =
                    MFun (mtype_for (domain_type T), V x, bool_M)
                  val bc_set_M = domain_type T |> mtype_for_set
                  val ab_set_M = domain_type (range_type T) |> mtype_for_set
                  val ac_set_M = nth_range_type 2 T |> mtype_for_set
                in
                  (MFun (bc_set_M, S Minus, MFun (ab_set_M, S Minus, ac_set_M)),
                   accum)
                end
              | @{const_name image} =>
                let
                  val a_M = mtype_for (domain_type (domain_type T))
                  val b_M = mtype_for (range_type (domain_type T))
                in
                  (MFun (MFun (a_M, S Minus, b_M), S Minus,
                         MFun (plus_set_mtype_for_dom a_M, S Minus,
                               plus_set_mtype_for_dom b_M)), accum)
                end
              | @{const_name finite} =>
                let val M1 = mtype_for (domain_type (domain_type T)) in
                  (MFun (plus_set_mtype_for_dom M1, S Minus, bool_M), accum)
                end
              | @{const_name Sigma} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  fun mtype_for_set T =
                    MFun (mtype_for (domain_type T), V x, bool_M)
                  val a_set_T = domain_type T
                  val a_M = mtype_for (domain_type a_set_T)
                  val b_set_M = mtype_for_set (range_type (domain_type
                                                               (range_type T)))
                  val a_set_M = mtype_for_set a_set_T
                  val a_to_b_set_M = MFun (a_M, S Minus, b_set_M)
                  val ab_set_M = mtype_for_set (nth_range_type 2 T)
                in
                  (MFun (a_set_M, S Minus,
                         MFun (a_to_b_set_M, S Minus, ab_set_M)), accum)
                end
              | _ =>
                if s = @{const_name safe_The} orelse
                   s = @{const_name safe_Eps} then
                  let
                    val a_set_M = mtype_for (domain_type T)
                    val a_M = dest_MFun a_set_M |> #1
                  in (MFun (a_set_M, S Minus, a_M), accum) end
                else if s = @{const_name ord_class.less_eq} andalso
                        is_set_type (domain_type T) then
                  do_fragile_set_operation T accum
                else if is_sel s then
                  (mtype_for_sel mdata x, accum)
                else if is_constr ctxt stds x then
                  (mtype_for_constr mdata x, accum)
                else if is_built_in_const thy stds fast_descrs x then
                  (fresh_mtype_for_type mdata true T, accum)
                else
                  let val M = mtype_for T in
                    (M, ({bound_Ts = bound_Ts, bound_Ms = bound_Ms,
                          frees = frees, consts = (x, M) :: consts}, cset))
                  end) |>> curry MRaw t
         | Free (x as (_, T)) =>
           (case AList.lookup (op =) frees x of
              SOME M => (M, accum)
            | NONE =>
              let val M = mtype_for T in
                (M, ({bound_Ts = bound_Ts, bound_Ms = bound_Ms,
                      frees = (x, M) :: frees, consts = consts}, cset))
              end) |>> curry MRaw t
         | Var _ => (trace_msg (K "*** Var"); raise UNSOLVABLE ())
         | Bound j => (MRaw (t, nth bound_Ms j), accum)
         | Abs (s, T, t') =>
           (case fin_fun_body T (fastype_of1 (T :: bound_Ts, t')) t' of
              SOME t' =>
              let
                val M = mtype_for T
                val a = V (Unsynchronized.inc max_fresh)
                val (m', accum) = do_term t' (accum |>> push_bound T M)
              in (MAbs (s, T, M, a, m'), accum |>> pop_bound) end
            | NONE =>
              ((case t' of
                  t1' $ Bound 0 =>
                  if not (loose_bvar1 (t1', 0)) andalso
                     is_enough_eta_expanded t1' then
                    do_term (incr_boundvars ~1 t1') accum
                  else
                    raise SAME ()
                | (t11 as Const (@{const_name HOL.eq}, _)) $ Bound 0 $ t13 =>
                  if not (loose_bvar1 (t13, 0)) then
                    do_term (incr_boundvars ~1 (t11 $ t13)) accum
                  else
                    raise SAME ()
                | _ => raise SAME ())
               handle SAME () =>
                      let
                        val M = mtype_for T
                        val (m', accum) = do_term t' (accum |>> push_bound T M)
                      in
                        (MAbs (s, T, M, S Minus, m'), accum |>> pop_bound)
                      end))
         | (t0 as Const (@{const_name All}, _))
           $ Abs (s', T', (t10 as @{const HOL.implies}) $ (t11 $ Bound 0) $ t12) =>
           do_bounded_quantifier t0 s' T' t10 t11 t12 accum
         | (t0 as Const (@{const_name Ex}, _))
           $ Abs (s', T', (t10 as @{const HOL.conj}) $ (t11 $ Bound 0) $ t12) =>
           do_bounded_quantifier t0 s' T' t10 t11 t12 accum
         | Const (@{const_name Let}, _) $ t1 $ t2 =>
           do_term (betapply (t2, t1)) accum
         | t1 $ t2 =>
           let
             val (m1, accum) = do_term t1 accum
             val (m2, accum) = do_term t2 accum
           in
             let
               val T11 = domain_type (fastype_of1 (bound_Ts, t1))
               val T2 = fastype_of1 (bound_Ts, t2)
               val M11 = mtype_of_mterm m1 |> dest_MFun |> #1
               val M2 = mtype_of_mterm m2
             in (MApp (m1, m2), accum ||> add_is_sub_mtype M2 M11) end
           end)
        |> tap (fn (m, _) => trace_msg (fn () => "  \<Gamma> \<turnstile> " ^
                                                 string_for_mterm ctxt m))
  in do_term end

fun force_minus_funs 0 _ = I
  | force_minus_funs n (M as MFun (M1, _, M2)) =
    add_mtypes_equal M (MFun (M1, S Minus, M2))
    #> force_minus_funs (n - 1) M2
  | force_minus_funs _ M =
    raise MTYPE ("Nitpick_Mono.force_minus_funs", [M], [])
fun consider_general_equals mdata def (x as (_, T)) t1 t2 accum =
  let
    val (m1, accum) = consider_term mdata t1 accum
    val (m2, accum) = consider_term mdata t2 accum
    val M1 = mtype_of_mterm m1
    val M2 = mtype_of_mterm m2
    val accum = accum ||> add_mtypes_equal M1 M2
    val body_M = fresh_mtype_for_type mdata false (nth_range_type 2 T)
    val m = MApp (MApp (MRaw (Const x,
                MFun (M1, S Minus, MFun (M2, S Minus, body_M))), m1), m2)
  in
    (m, if def then
          let val (head_m, arg_ms) = strip_mcomb m1 in
            accum ||> force_minus_funs (length arg_ms) (mtype_of_mterm head_m)
          end
        else
          accum)
  end

fun consider_general_formula (mdata as {hol_ctxt = {ctxt, ...}, ...}) =
  let
    val mtype_for = fresh_mtype_for_type mdata false
    val do_term = consider_term mdata
    fun do_formula sn t accum =
        let
          fun do_quantifier (quant_x as (quant_s, _)) abs_s abs_T body_t =
            let
              val abs_M = mtype_for abs_T
              val side_cond = ((sn = Minus) = (quant_s = @{const_name Ex}))
              val (body_m, accum) =
                accum ||> side_cond ? add_mtype_is_complete abs_M
                      |>> push_bound abs_T abs_M |> do_formula sn body_t
              val body_M = mtype_of_mterm body_m
            in
              (MApp (MRaw (Const quant_x,
                           MFun (MFun (abs_M, S Minus, body_M), S Minus,
                                 body_M)),
                     MAbs (abs_s, abs_T, abs_M, S Minus, body_m)),
               accum |>> pop_bound)
            end
          fun do_equals x t1 t2 =
            case sn of
              Plus => do_term t accum
            | Minus => consider_general_equals mdata false x t1 t2 accum
        in
          (trace_msg (fn () => "  \<Gamma> \<turnstile> " ^
                               Syntax.string_of_term ctxt t ^ " : o\<^sup>" ^
                               string_for_sign sn ^ "?");
           case t of
             Const (x as (@{const_name all}, _)) $ Abs (s1, T1, t1) =>
             do_quantifier x s1 T1 t1
           | Const (x as (@{const_name "=="}, _)) $ t1 $ t2 => do_equals x t1 t2
           | @{const Trueprop} $ t1 =>
             let val (m1, accum) = do_formula sn t1 accum in
               (MApp (MRaw (@{const Trueprop}, mtype_for (bool_T --> prop_T)),
                      m1), accum)
             end
           | @{const Not} $ t1 =>
             let val (m1, accum) = do_formula (negate sn) t1 accum in
               (MApp (MRaw (@{const Not}, mtype_for (bool_T --> bool_T)), m1),
                accum)
             end
           | Const (x as (@{const_name All}, _)) $ Abs (s1, T1, t1) =>
             do_quantifier x s1 T1 t1
           | Const (x0 as (s0 as @{const_name Ex}, T0))
             $ (t1 as Abs (s1, T1, t1')) =>
             (case sn of
                Plus => do_quantifier x0 s1 T1 t1'
              | Minus =>
                (* FIXME: Move elsewhere *)
                do_term (@{const Not}
                         $ (HOLogic.eq_const (domain_type T0) $ t1
                            $ Abs (Name.uu, T1, @{const False}))) accum)
           | Const (x as (@{const_name HOL.eq}, _)) $ t1 $ t2 =>
             do_equals x t1 t2
           | Const (@{const_name Let}, _) $ t1 $ t2 =>
             do_formula sn (betapply (t2, t1)) accum
           | (t0 as Const (s0, _)) $ t1 $ t2 =>
             if s0 = @{const_name "==>"} orelse
                s0 = @{const_name Pure.conjunction} orelse
                s0 = @{const_name HOL.conj} orelse
                s0 = @{const_name HOL.disj} orelse
                s0 = @{const_name HOL.implies} then
               let
                 val impl = (s0 = @{const_name "==>"} orelse
                             s0 = @{const_name HOL.implies})
                 val (m1, accum) = do_formula (sn |> impl ? negate) t1 accum
                 val (m2, accum) = do_formula sn t2 accum
               in
                 (MApp (MApp (MRaw (t0, mtype_for (fastype_of t0)), m1), m2),
                  accum)
               end 
             else
               do_term t accum
           | _ => do_term t accum)
        end
        |> tap (fn (m, _) =>
                   trace_msg (fn () => "\<Gamma> \<turnstile> " ^
                                       string_for_mterm ctxt m ^ " : o\<^sup>" ^
                                       string_for_sign sn))
  in do_formula end

(* The harmless axiom optimization below is somewhat too aggressive in the face
   of (rather peculiar) user-defined axioms. *)
val harmless_consts =
  [@{const_name ord_class.less}, @{const_name ord_class.less_eq}]
val bounteous_consts = [@{const_name bisim}]

fun is_harmless_axiom ({no_harmless = true, ...} : mdata) _ = false
  | is_harmless_axiom {hol_ctxt = {thy, stds, fast_descrs, ...}, ...} t =
    Term.add_consts t []
    |> filter_out (is_built_in_const thy stds fast_descrs)
    |> (forall (member (op =) harmless_consts o original_name o fst) orf
        exists (member (op =) bounteous_consts o fst))

fun consider_nondefinitional_axiom mdata t =
  if is_harmless_axiom mdata t then pair (MRaw (t, dummy_M))
  else consider_general_formula mdata Plus t

fun consider_definitional_axiom (mdata as {hol_ctxt = {ctxt, ...}, ...}) t =
  if not (is_constr_pattern_formula ctxt t) then
    consider_nondefinitional_axiom mdata t
  else if is_harmless_axiom mdata t then
    pair (MRaw (t, dummy_M))
  else
    let
      val mtype_for = fresh_mtype_for_type mdata false
      val do_term = consider_term mdata
      fun do_all quant_t abs_s abs_T body_t accum =
        let
          val abs_M = mtype_for abs_T
          val (body_m, accum) =
            accum |>> push_bound abs_T abs_M |> do_formula body_t
          val body_M = mtype_of_mterm body_m
        in
          (MApp (MRaw (quant_t,
                       MFun (MFun (abs_M, S Minus, body_M), S Minus, body_M)),
                 MAbs (abs_s, abs_T, abs_M, S Minus, body_m)),
           accum |>> pop_bound)
        end
      and do_conjunction t0 t1 t2 accum =
        let
          val (m1, accum) = do_formula t1 accum
          val (m2, accum) = do_formula t2 accum
        in
          (MApp (MApp (MRaw (t0, mtype_for (fastype_of t0)), m1), m2), accum)
        end
      and do_implies t0 t1 t2 accum =
        let
          val (m1, accum) = do_term t1 accum
          val (m2, accum) = do_formula t2 accum
        in
          (MApp (MApp (MRaw (t0, mtype_for (fastype_of t0)), m1), m2), accum)
        end
      and do_formula t accum =
          case t of
            (t0 as Const (@{const_name all}, _)) $ Abs (s1, T1, t1) =>
            do_all t0 s1 T1 t1 accum
          | @{const Trueprop} $ t1 =>
            let val (m1, accum) = do_formula t1 accum in
              (MApp (MRaw (@{const Trueprop}, mtype_for (bool_T --> prop_T)),
                     m1), accum)
            end
          | Const (x as (@{const_name "=="}, _)) $ t1 $ t2 =>
            consider_general_equals mdata true x t1 t2 accum
          | (t0 as @{const "==>"}) $ t1 $ t2 => do_implies t0 t1 t2 accum
          | (t0 as @{const Pure.conjunction}) $ t1 $ t2 =>
            do_conjunction t0 t1 t2 accum
          | (t0 as Const (@{const_name All}, _)) $ Abs (s0, T1, t1) =>
            do_all t0 s0 T1 t1 accum
          | Const (x as (@{const_name HOL.eq}, _)) $ t1 $ t2 =>
            consider_general_equals mdata true x t1 t2 accum
          | (t0 as @{const HOL.conj}) $ t1 $ t2 => do_conjunction t0 t1 t2 accum
          | (t0 as @{const HOL.implies}) $ t1 $ t2 => do_implies t0 t1 t2 accum
          | _ => raise TERM ("Nitpick_Mono.consider_definitional_axiom.\
                             \do_formula", [t])
    in do_formula t end

fun string_for_mtype_of_term ctxt lits t M =
  Syntax.string_of_term ctxt t ^ " : " ^ string_for_mtype (resolve_mtype lits M)

fun print_mtype_context ctxt lits ({frees, consts, ...} : mtype_context) =
  trace_msg (fn () =>
      map (fn (x, M) => string_for_mtype_of_term ctxt lits (Free x) M) frees @
      map (fn (x, M) => string_for_mtype_of_term ctxt lits (Const x) M) consts
      |> cat_lines)

fun amass f t (ms, accum) =
  let val (m, accum) = f t accum in (m :: ms, accum) end

fun infer which no_harmless (hol_ctxt as {ctxt, ...}) binarize alpha_T
          (nondef_ts, def_ts) =
  let
    val _ = trace_msg (fn () => "****** " ^ which ^ " analysis: " ^
                                string_for_mtype MAlpha ^ " is " ^
                                Syntax.string_of_typ ctxt alpha_T)
    val mdata as {max_fresh, constr_mcache, ...} =
      initial_mdata hol_ctxt binarize no_harmless alpha_T
    val accum = (initial_gamma, ([], [], []))
    val (nondef_ms, accum) =
      ([], accum) |> amass (consider_general_formula mdata Plus) (hd nondef_ts)
                  |> fold (amass (consider_nondefinitional_axiom mdata))
                          (tl nondef_ts)
    val (def_ms, (gamma, cset)) =
      ([], accum) |> fold (amass (consider_definitional_axiom mdata)) def_ts
  in
    case solve (!max_fresh) cset of
      SOME lits => (print_mtype_context ctxt lits gamma;
                    SOME (lits, (nondef_ms, def_ms), !constr_mcache))
    | _ => NONE
  end
  handle UNSOLVABLE () => NONE
       | MTYPE (loc, Ms, Ts) =>
         raise BAD (loc, commas (map string_for_mtype Ms @
                                 map (Syntax.string_of_typ ctxt) Ts))
       | MTERM (loc, ms) =>
         raise BAD (loc, commas (map (string_for_mterm ctxt) ms))

val formulas_monotonic = is_some oooo infer "Monotonicity" false

fun fin_fun_constr T1 T2 =
  (@{const_name FinFun}, (T1 --> T2) --> Type (@{type_name fin_fun}, [T1, T2]))

fun finitize_funs (hol_ctxt as {thy, ctxt, stds, fast_descrs, constr_cache,
                                ...})
                  binarize finitizes alpha_T tsp =
  case infer "Finiteness" true hol_ctxt binarize alpha_T tsp of
    SOME (lits, msp, constr_mtypes) =>
    if forall (curry (op =) Minus o snd) lits then
      tsp
    else
      let
        fun should_finitize T a =
          case triple_lookup (type_match thy) finitizes T of
            SOME (SOME false) => false
          | _ => resolve_sign_atom lits a = S Plus
        fun type_from_mtype T M =
          case (M, T) of
            (MAlpha, _) => T
          | (MFun (M1, a, M2), Type (@{type_name fun}, Ts)) =>
            Type (if should_finitize T a then @{type_name fin_fun}
                  else @{type_name fun}, map2 type_from_mtype Ts [M1, M2])
          | (MPair (M1, M2), Type (@{type_name prod}, Ts)) =>
            Type (@{type_name prod}, map2 type_from_mtype Ts [M1, M2])
          | (MType _, _) => T
          | _ => raise MTYPE ("Nitpick_Mono.finitize_funs.type_from_mtype",
                              [M], [T])
        fun finitize_constr (x as (s, T)) =
          (s, case AList.lookup (op =) constr_mtypes x of
                SOME M => type_from_mtype T M
              | NONE => T)
        fun term_from_mterm new_Ts old_Ts m =
          case m of
            MRaw (t, M) =>
            let
              val T = fastype_of1 (old_Ts, t)
              val T' = type_from_mtype T M
            in
              case t of
                Const (x as (s, _)) =>
                if s = @{const_name finite} then
                  case domain_type T' of
                    set_T' as Type (@{type_name fin_fun}, _) =>
                    Abs (Name.uu, set_T', @{const True})
                  | _ => Const (s, T')
                else if s = @{const_name "=="} orelse
                        s = @{const_name HOL.eq} then
                  let
                    val T =
                      case T' of
                        Type (_, [T1, Type (_, [T2, T3])]) =>
                        T1 --> T2 --> T3
                      | _ => raise TYPE ("Nitpick_Mono.finitize_funs.\
                                         \term_from_mterm", [T, T'], [])
                  in coerce_term hol_ctxt new_Ts T' T (Const (s, T)) end
                else if is_built_in_const thy stds fast_descrs x then
                  coerce_term hol_ctxt new_Ts T' T t
                else if is_constr ctxt stds x then
                  Const (finitize_constr x)
                else if is_sel s then
                  let
                    val n = sel_no_from_name s
                    val x' =
                      x |> binarized_and_boxed_constr_for_sel hol_ctxt binarize
                        |> finitize_constr
                    val x'' =
                      binarized_and_boxed_nth_sel_for_constr hol_ctxt binarize
                                                             x' n
                  in Const x'' end
                else
                  Const (s, T')
              | Free (s, T) => Free (s, type_from_mtype T M)
              | Bound _ => t
              | _ => raise MTERM ("Nitpick_Mono.finitize_funs.term_from_mterm",
                                  [m])
            end
          | MApp (m1, m2) =>
            let
              val (t1, t2) = pairself (term_from_mterm new_Ts old_Ts) (m1, m2)
              val (T1, T2) = pairself (curry fastype_of1 new_Ts) (t1, t2)
              val (t1', T2') =
                case T1 of
                  Type (s, [T11, T12]) => 
                  (if s = @{type_name fin_fun} then
                     select_nth_constr_arg ctxt stds (fin_fun_constr T11 T12) t1
                                           0 (T11 --> T12)
                   else
                     t1, T11)
                | _ => raise TYPE ("Nitpick_Mono.finitize_funs.term_from_mterm",
                                   [T1], [])
            in betapply (t1', coerce_term hol_ctxt new_Ts T2' T2 t2) end
          | MAbs (s, old_T, M, a, m') =>
            let
              val new_T = type_from_mtype old_T M
              val t' = term_from_mterm (new_T :: new_Ts) (old_T :: old_Ts) m'
              val T' = fastype_of1 (new_T :: new_Ts, t')
            in
              Abs (s, new_T, t')
              |> should_finitize (new_T --> T') a
                 ? construct_value ctxt stds (fin_fun_constr new_T T') o single
            end
      in
        Unsynchronized.change constr_cache (map (apsnd (map finitize_constr)));
        pairself (map (term_from_mterm [] [])) msp
      end
  | NONE => tsp

end;
