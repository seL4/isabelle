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
end;

structure Nitpick_Mono : NITPICK_MONO =
struct

open Nitpick_Util
open Nitpick_HOL

datatype sign = Plus | Minus

type var = int

datatype annotation = Gen | New | Fls | Tru
datatype annotation_atom = A of annotation | V of var

type assign_literal = var * (sign * annotation)

datatype mtyp =
  MAlpha |
  MFun of mtyp * annotation_atom * mtyp |
  MPair of mtyp * mtyp |
  MType of string * mtyp list |
  MRec of string * typ list

type mdata =
  {hol_ctxt: hol_context,
   binarize: bool,
   alpha_T: typ,
   max_fresh: int Unsynchronized.ref,
   datatype_mcache: ((string * typ list) * mtyp) list Unsynchronized.ref,
   constr_mcache: (styp * mtyp) list Unsynchronized.ref}

exception UNSOLVABLE of unit
exception MTYPE of string * mtyp list * typ list

val trace = Unsynchronized.ref false
fun trace_msg msg = if !trace then tracing (msg ()) else ()

fun string_for_sign Plus = "+"
  | string_for_sign Minus = "-"

fun negate_sign Plus = Minus
  | negate_sign Minus = Plus

val string_for_var = signed_string_of_int
fun string_for_vars sep [] = "0\<^bsub>" ^ sep ^ "\<^esub>"
  | string_for_vars sep xs = space_implode sep (map string_for_var xs)
fun subscript_string_for_vars sep xs =
  if null xs then "" else "\<^bsub>" ^ string_for_vars sep xs ^ "\<^esub>"

fun string_for_annotation Gen = "G"
  | string_for_annotation New = "N"
  | string_for_annotation Fls = "F"
  | string_for_annotation Tru = "T"

fun string_for_annotation_atom (A a) = string_for_annotation a
  | string_for_annotation_atom (V x) = string_for_var x

fun string_for_assign_literal (x, (sn, a)) =
  string_for_var x ^ (case sn of Plus => " = " | Minus => " \<noteq> ") ^
  string_for_annotation a

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
           | MFun (M1, aa, M2) =>
             aux (prec + 1) M1 ^ " \<Rightarrow>\<^bsup>" ^
             string_for_annotation_atom aa ^ "\<^esup> " ^ aux prec M2
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

fun initial_mdata hol_ctxt binarize alpha_T =
  ({hol_ctxt = hol_ctxt, binarize = binarize, alpha_T = alpha_T,
    max_fresh = Unsynchronized.ref 0, datatype_mcache = Unsynchronized.ref [],
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
  fold_rev (fn M => curry3 MFun M (A Gen)) Ms (MRec z)

fun repair_mtype _ _ MAlpha = MAlpha
  | repair_mtype cache seen (MFun (M1, aa, M2)) =
    MFun (repair_mtype cache seen M1, aa, repair_mtype cache seen M2)
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

(* TODO: clean this up *)
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

(* FIXME: make sure well-annotated *)

fun fresh_mfun_for_fun_type (mdata as {max_fresh, ...} : mdata) all_minus
                            T1 T2 =
  let
    val M1 = fresh_mtype_for_type mdata all_minus T1
    val M2 = fresh_mtype_for_type mdata all_minus T2
    val aa = if not all_minus andalso exists_alpha_sub_mtype_fresh M1 andalso
                is_fin_fun_supported_type (body_type T2) then
               V (Unsynchronized.inc max_fresh)
             else
               A Gen
  in (M1, aa, M2) end
and fresh_mtype_for_type (mdata as {hol_ctxt as {ctxt, ...}, binarize, alpha_T,
                                    datatype_mcache, constr_mcache, ...})
                         all_minus =
  let
    fun do_type T =
      if T = alpha_T then
        MAlpha
      else case T of
        Type (@{type_name fun}, [T1, T2]) =>
        MFun (fresh_mfun_for_fun_type mdata all_minus T1 T2)
      | Type (@{type_name prod}, [T1, T2]) => MPair (pairself do_type (T1, T2))
      | Type (@{type_name set}, [T']) => do_type (T' --> bool_T)
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

val ground_and_sole_base_constrs = []
(* FIXME: [@{const_name Nil}, @{const_name None}], cf. lists_empty *)

fun prodM_factors (MPair (M1, M2)) = maps prodM_factors [M1, M2]
  | prodM_factors M = [M]
fun curried_strip_mtype (MFun (M1, _, M2)) =
    curried_strip_mtype M2 |>> append (prodM_factors M1)
  | curried_strip_mtype M = ([], M)
fun sel_mtype_from_constr_mtype s M =
  let
    val (arg_Ms, dataM) = curried_strip_mtype M
    val a = if member (op =) ground_and_sole_base_constrs
                             (constr_name_for_sel_like s) then
              Fls
            else
              Gen
  in
    MFun (dataM, A a,
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

fun resolve_annotation_atom asgs (V x) =
    x |> AList.lookup (op =) asgs |> Option.map A |> the_default (V x)
  | resolve_annotation_atom _ aa = aa
fun resolve_mtype asgs =
  let
    fun aux MAlpha = MAlpha
      | aux (MFun (M1, aa, M2)) =
        MFun (aux M1, resolve_annotation_atom asgs aa, aux M2)
      | aux (MPair Mp) = MPair (pairself aux Mp)
      | aux (MType (s, Ms)) = MType (s, map aux Ms)
      | aux (MRec z) = MRec z
  in aux end

datatype comp_op = Eq | Neq | Leq

type comp = annotation_atom * annotation_atom * comp_op * var list
type assign_clause = assign_literal list

type constraint_set = comp list * assign_clause list

fun string_for_comp_op Eq = "="
  | string_for_comp_op Neq = "\<noteq>"
  | string_for_comp_op Leq = "\<le>"

fun string_for_comp (aa1, aa2, cmp, xs) =
  string_for_annotation_atom aa1 ^ " " ^ string_for_comp_op cmp ^
  subscript_string_for_vars " \<and> " xs ^ " " ^ string_for_annotation_atom aa2

fun string_for_assign_clause NONE = "\<top>"
  | string_for_assign_clause (SOME []) = "\<bot>"
  | string_for_assign_clause (SOME asgs) =
    space_implode " \<or> " (map string_for_assign_literal asgs)

fun add_assign_literal (x, (sn, a)) clauses =
  if exists (fn [(x', (sn', a'))] =>
                x = x' andalso ((sn = sn' andalso a <> a') orelse
                                (sn <> sn' andalso a = a'))
              | _ => false) clauses then
    NONE
  else
    SOME ([(x, (sn, a))] :: clauses)

fun add_assign_disjunct _ NONE = NONE
  | add_assign_disjunct asg (SOME asgs) = SOME (insert (op =) asg asgs)

fun add_assign_clause NONE = I
  | add_assign_clause (SOME clause) = insert (op =) clause

fun annotation_comp Eq a1 a2 = (a1 = a2)
  | annotation_comp Neq a1 a2 = (a1 <> a2)
  | annotation_comp Leq a1 a2 = (a1 = a2 orelse a2 = Gen)

fun sign_for_comp_op Eq = Plus
  | sign_for_comp_op Neq = Minus
  | sign_for_comp_op Leq = raise BAD ("sign_for_comp_op", "unexpected \"Leq\"")

fun do_annotation_atom_comp Leq [] aa1 aa2 (cset as (comps, clauses)) =
    (case (aa1, aa2) of
       (A a1, A a2) => if annotation_comp Leq a1 a2 then SOME cset else NONE
     | _ => SOME (insert (op =) (aa1, aa2, Leq, []) comps, clauses))
  | do_annotation_atom_comp cmp [] aa1 aa2 (cset as (comps, clauses)) =
    (case (aa1, aa2) of
       (A a1, A a2) => if annotation_comp cmp a1 a2 then SOME cset else NONE
     | (V x1, A a2) =>
       clauses |> add_assign_literal (x1, (sign_for_comp_op cmp, a2))
               |> Option.map (pair comps)
     | (A _, V _) => do_annotation_atom_comp cmp [] aa2 aa1 cset
     | (V _, V _) => SOME (insert (op =) (aa1, aa2, cmp, []) comps, clauses))
  | do_annotation_atom_comp cmp xs aa1 aa2 (comps, clauses) =
    SOME (insert (op =) (aa1, aa2, cmp, xs) comps, clauses)

fun add_annotation_atom_comp cmp xs aa1 aa2 (comps, clauses) =
  (trace_msg (fn () => "*** Add " ^ string_for_comp (aa1, aa2, cmp, xs));
   case do_annotation_atom_comp cmp xs aa1 aa2 (comps, clauses) of
     NONE => (trace_msg (K "**** Unsolvable"); raise UNSOLVABLE ())
   | SOME cset => cset)

fun do_mtype_comp _ _ _ _ NONE = NONE
  | do_mtype_comp _ _ MAlpha MAlpha cset = cset
  | do_mtype_comp Eq xs (MFun (M11, aa1, M12)) (MFun (M21, aa2, M22))
                  (SOME cset) =
    cset |> do_annotation_atom_comp Eq xs aa1 aa2
         |> do_mtype_comp Eq xs M11 M21 |> do_mtype_comp Eq xs M12 M22
  | do_mtype_comp Leq xs (MFun (M11, aa1, M12)) (MFun (M21, aa2, M22))
                  (SOME cset) =
    (if exists_alpha_sub_mtype M11 then
       cset |> do_annotation_atom_comp Leq xs aa1 aa2
            |> do_mtype_comp Leq xs M21 M11
            |> (case aa2 of
                  A Gen => I
                | A _ => do_mtype_comp Leq xs M11 M21
                | V x => do_mtype_comp Leq (x :: xs) M11 M21)
     else
       SOME cset)
    |> do_mtype_comp Leq xs M12 M22
  | do_mtype_comp cmp xs (M1 as MPair (M11, M12)) (M2 as MPair (M21, M22))
                  cset =
    (cset |> fold (uncurry (do_mtype_comp cmp xs)) [(M11, M21), (M12, M22)]
     handle ListPair.UnequalLengths =>
            raise MTYPE ("Nitpick_Mono.do_mtype_comp", [M1, M2], []))
  | do_mtype_comp _ _ (MType _) (MType _) cset =
    cset (* no need to compare them thanks to the cache *)
  | do_mtype_comp cmp _ M1 M2 _ =
    raise MTYPE ("Nitpick_Mono.do_mtype_comp (" ^ string_for_comp_op cmp ^ ")",
                 [M1, M2], [])

fun add_mtype_comp cmp M1 M2 cset =
  (trace_msg (fn () => "*** Add " ^ string_for_mtype M1 ^ " " ^
                       string_for_comp_op cmp ^ " " ^ string_for_mtype M2);
   case SOME cset |> do_mtype_comp cmp [] M1 M2 of
     NONE => (trace_msg (K "**** Unsolvable"); raise UNSOLVABLE ())
   | SOME cset => cset)

val add_mtypes_equal = add_mtype_comp Eq
val add_is_sub_mtype = add_mtype_comp Leq

fun do_notin_mtype_fv _ _ _ NONE = NONE
  | do_notin_mtype_fv Minus _ MAlpha cset = cset
  | do_notin_mtype_fv Plus [] MAlpha _ = NONE
  | do_notin_mtype_fv Plus [asg] MAlpha (SOME clauses) =
    clauses |> add_assign_literal asg
  | do_notin_mtype_fv Plus unless MAlpha (SOME clauses) =
    SOME (insert (op =) unless clauses)
  | do_notin_mtype_fv sn unless (MFun (M1, A a, M2)) cset =
    cset |> (if a <> Gen andalso sn = Plus then do_notin_mtype_fv Plus unless M1
             else I)
         |> (if a = Gen orelse sn = Plus then do_notin_mtype_fv Minus unless M1
             else I)
         |> do_notin_mtype_fv sn unless M2
  | do_notin_mtype_fv Plus unless (MFun (M1, V x, M2)) cset =
    cset |> (case add_assign_disjunct (x, (Plus, Gen)) (SOME unless) of
               NONE => I
             | SOME unless' => do_notin_mtype_fv Plus unless' M1)
         |> do_notin_mtype_fv Minus unless M1
         |> do_notin_mtype_fv Plus unless M2
  | do_notin_mtype_fv Minus unless (MFun (M1, V x, M2)) cset =
    cset |> (case fold (fn a => add_assign_disjunct (x, (Plus, a))) [Fls, Tru]
                       (SOME unless) of
               NONE => I
             | SOME unless' => do_notin_mtype_fv Plus unless' M1)
         |> do_notin_mtype_fv Minus unless M2
  | do_notin_mtype_fv sn unless (MPair (M1, M2)) cset =
    cset |> fold (do_notin_mtype_fv sn unless) [M1, M2]
  | do_notin_mtype_fv sn unless (MType (_, Ms)) cset =
    cset |> fold (do_notin_mtype_fv sn unless) Ms
 | do_notin_mtype_fv _ _ M _ =
   raise MTYPE ("Nitpick_Mono.do_notin_mtype_fv", [M], [])

fun add_notin_mtype_fv sn unless M (comps, clauses) =
  (trace_msg (fn () => "*** Add " ^ string_for_mtype M ^ " is " ^
                       (case sn of Minus => "concrete" | Plus => "complete"));
   case SOME clauses |> do_notin_mtype_fv sn unless M of
     NONE => (trace_msg (K "**** Unsolvable"); raise UNSOLVABLE ())
   | SOME clauses => (comps, clauses))

fun add_mtype_is_concrete x y z = add_notin_mtype_fv Minus x y z
fun add_mtype_is_complete x y z = add_notin_mtype_fv Plus x y z

val bool_table =
  [(Gen, (false, false)),
   (New, (false, true)),
   (Fls, (true, false)),
   (Tru, (true, true))]

fun fst_var n = 2 * n
fun snd_var n = 2 * n + 1

val bools_from_annotation = AList.lookup (op =) bool_table #> the
val annotation_from_bools = AList.find (op =) bool_table #> the_single

fun prop_for_bool b = if b then Prop_Logic.True else Prop_Logic.False
fun prop_for_bool_var_equality (v1, v2) =
  Prop_Logic.SAnd (Prop_Logic.SOr (Prop_Logic.BoolVar v1,
                                   Prop_Logic.SNot (Prop_Logic.BoolVar v2)),
                   Prop_Logic.SOr (Prop_Logic.SNot (Prop_Logic.BoolVar v1),
                                   Prop_Logic.BoolVar v2))
fun prop_for_assign (x, a) =
  let val (b1, b2) = bools_from_annotation a in
    Prop_Logic.SAnd (Prop_Logic.BoolVar (fst_var x) |> not b1 ? Prop_Logic.SNot,
                     Prop_Logic.BoolVar (snd_var x) |> not b2 ? Prop_Logic.SNot)
  end
fun prop_for_assign_literal (x, (Plus, a)) = prop_for_assign (x, a)
  | prop_for_assign_literal (x, (Minus, a)) =
    Prop_Logic.SNot (prop_for_assign (x, a))
fun prop_for_atom_assign (A a', a) = prop_for_bool (a = a')
  | prop_for_atom_assign (V x, a) = prop_for_assign_literal (x, (Plus, a))
fun prop_for_atom_equality (aa1, A a2) = prop_for_atom_assign (aa1, a2)
  | prop_for_atom_equality (A a1, aa2) = prop_for_atom_assign (aa2, a1)
  | prop_for_atom_equality (V x1, V x2) =
    Prop_Logic.SAnd (prop_for_bool_var_equality (pairself fst_var (x1, x2)),
             prop_for_bool_var_equality (pairself snd_var (x1, x2)))
val prop_for_assign_clause = Prop_Logic.exists o map prop_for_assign_literal
fun prop_for_exists_var_assign_literal xs a =
  Prop_Logic.exists (map (fn x => prop_for_assign_literal (x, (Plus, a))) xs)
fun prop_for_comp (aa1, aa2, Eq, []) =
    Prop_Logic.SAnd (prop_for_comp (aa1, aa2, Leq, []),
             prop_for_comp (aa2, aa1, Leq, []))
  | prop_for_comp (aa1, aa2, Neq, []) =
    Prop_Logic.SNot (prop_for_comp (aa1, aa2, Eq, []))
  | prop_for_comp (aa1, aa2, Leq, []) =
    Prop_Logic.SOr (prop_for_atom_equality (aa1, aa2),
                    prop_for_atom_assign (aa2, Gen))
  | prop_for_comp (aa1, aa2, cmp, xs) =
    Prop_Logic.SOr (prop_for_exists_var_assign_literal xs Gen,
            prop_for_comp (aa1, aa2, cmp, []))

fun extract_assigns max_var assigns asgs =
  fold (fn x => fn accum =>
           if AList.defined (op =) asgs x then
             accum
           else case (fst_var x, snd_var x) |> pairself assigns of
             (NONE, NONE) => accum
           | bp => (x, annotation_from_bools (pairself (the_default false) bp))
                   :: accum)
       (max_var downto 1) asgs

fun print_problem comps clauses =
  trace_msg (fn () => "*** Problem:\n" ^
                      cat_lines (map string_for_comp comps @
                                 map (string_for_assign_clause o SOME) clauses))

fun print_solution asgs =
  trace_msg (fn () => "*** Solution:\n" ^
      (asgs
       |> map swap
       |> AList.group (op =)
       |> map (fn (a, xs) => string_for_annotation a ^ ": " ^
                             string_for_vars ", " (sort int_ord xs))
       |> space_implode "\n"))

(* The ML solver timeout should correspond more or less to the overhead of
   invoking an external prover. *)
val ml_solver_timeout = SOME (seconds 0.02)

fun solve tac_timeout max_var (comps, clauses) =
  let
    val asgs =
      map_filter (fn [(x, (Plus, a))] => SOME (x, a) | _ => NONE) clauses
    fun do_assigns assigns =
      SOME (extract_assigns max_var assigns asgs |> tap print_solution)
    val _ = print_problem comps clauses
    val prop =
      Prop_Logic.all (map prop_for_comp comps @
                      map prop_for_assign_clause clauses)
  in
    if Prop_Logic.eval (K false) prop then
      do_assigns (K (SOME false))
    else if Prop_Logic.eval (K true) prop then
      do_assigns (K (SOME true))
    else
      let
        (* use the first ML solver (to avoid startup overhead) *)
        val (ml_solvers, nonml_solvers) =
          !SatSolver.solvers
          |> List.partition (member (op =) ["dptsat", "dpll"] o fst)
        val res =
          if null nonml_solvers then
            time_limit tac_timeout (snd (hd ml_solvers)) prop
          else
            time_limit ml_solver_timeout (snd (hd ml_solvers)) prop
            handle TimeLimit.TimeOut =>
                   time_limit tac_timeout (SatSolver.invoke_solver "auto") prop
      in
        case res of
          SatSolver.SATISFIABLE assigns => do_assigns assigns
        | _ => (trace_msg (K "*** Unsolvable"); NONE)
      end
      handle TimeLimit.TimeOut => (trace_msg (K "*** Timed out"); NONE)
  end

type mcontext =
  {bound_Ts: typ list,
   bound_Ms: mtyp list,
   frame: (int * annotation_atom) list,
   frees: (styp * mtyp) list,
   consts: (styp * mtyp) list}

fun string_for_bound ctxt Ms (j, aa) =
  Syntax.string_of_term ctxt (Bound (length Ms - j - 1)) ^ " :\<^bsup>" ^
  string_for_annotation_atom aa ^ "\<^esup> " ^
  string_for_mtype (nth Ms (length Ms - j - 1))
fun string_for_free relevant_frees ((s, _), M) =
  if member (op =) relevant_frees s then SOME (s ^ " : " ^ string_for_mtype M)
  else NONE
fun string_for_mcontext ctxt t ({bound_Ms, frame, frees, ...} : mcontext) =
  (map_filter (string_for_free (Term.add_free_names t [])) frees @
   map (string_for_bound ctxt bound_Ms) frame)
  |> commas |> enclose "[" "]"

val initial_gamma =
  {bound_Ts = [], bound_Ms = [], frame = [], frees = [], consts = []}

fun push_bound aa T M {bound_Ts, bound_Ms, frame, frees, consts} =
  {bound_Ts = T :: bound_Ts, bound_Ms = M :: bound_Ms,
   frame = frame @ [(length bound_Ts, aa)], frees = frees, consts = consts}
fun pop_bound {bound_Ts, bound_Ms, frame, frees, consts} =
  {bound_Ts = tl bound_Ts, bound_Ms = tl bound_Ms,
   frame = frame |> filter_out (fn (j, _) => j = length bound_Ts - 1),
   frees = frees, consts = consts}
  handle List.Empty => initial_gamma (* FIXME: needed? *)

fun set_frame frame ({bound_Ts, bound_Ms, frees, consts, ...} : mcontext) =
  {bound_Ts = bound_Ts, bound_Ms = bound_Ms, frame = frame, frees = frees,
   consts = consts}

fun add_comp_frame aa cmp = fold (add_annotation_atom_comp cmp [] aa o snd)

fun add_bound_frame j frame =
  let
    val (new_frame, gen_frame) = List.partition (curry (op =) j o fst) frame
  in
    add_comp_frame (A New) Leq new_frame
    #> add_comp_frame (A Gen) Eq gen_frame
  end

fun fresh_frame ({max_fresh, ...} : mdata) fls tru =
  map (apsnd (fn aa =>
                 case (aa, fls, tru) of
                   (A Fls, SOME a, _) => A a
                 | (A Tru, _, SOME a) => A a
                 | (A Gen, _, _) => A Gen
                 | _ => V (Unsynchronized.inc max_fresh)))

fun conj_clauses res_aa aa1 aa2 =
  [[(aa1, (Neq, Tru)), (aa2, (Neq, Tru)), (res_aa, (Eq, Tru))],
   [(aa1, (Neq, Fls)), (res_aa, (Eq, Fls))],
   [(aa2, (Neq, Fls)), (res_aa, (Eq, Fls))],
   [(aa1, (Neq, Gen)), (aa2, (Eq, Fls)), (res_aa, (Eq, Gen))],
   [(aa1, (Neq, New)), (aa2, (Eq, Fls)), (res_aa, (Eq, Gen))],
   [(aa1, (Eq, Fls)), (aa2, (Neq, Gen)), (res_aa, (Eq, Gen))],
   [(aa1, (Eq, Fls)), (aa2, (Neq, New)), (res_aa, (Eq, Gen))]]

fun disj_clauses res_aa aa1 aa2 =
  [[(aa1, (Neq, Tru)), (res_aa, (Eq, Tru))],
   [(aa2, (Neq, Tru)), (res_aa, (Eq, Tru))],
   [(aa1, (Neq, Fls)), (aa2, (Neq, Fls)), (res_aa, (Eq, Fls))],
   [(aa1, (Neq, Gen)), (aa2, (Eq, Tru)), (res_aa, (Eq, Gen))],
   [(aa1, (Neq, New)), (aa2, (Eq, Tru)), (res_aa, (Eq, Gen))],
   [(aa1, (Eq, Tru)), (aa2, (Neq, Gen)), (res_aa, (Eq, Gen))],
   [(aa1, (Eq, Tru)), (aa2, (Neq, New)), (res_aa, (Eq, Gen))]]

fun imp_clauses res_aa aa1 aa2 =
  [[(aa1, (Neq, Fls)), (res_aa, (Eq, Tru))],
   [(aa2, (Neq, Tru)), (res_aa, (Eq, Tru))],
   [(aa1, (Neq, Tru)), (aa2, (Neq, Fls)), (res_aa, (Eq, Fls))],
   [(aa1, (Neq, Gen)), (aa2, (Eq, Tru)), (res_aa, (Eq, Gen))],
   [(aa1, (Neq, New)), (aa2, (Eq, Tru)), (res_aa, (Eq, Gen))],
   [(aa1, (Eq, Fls)), (aa2, (Neq, Gen)), (res_aa, (Eq, Gen))],
   [(aa1, (Eq, Fls)), (aa2, (Neq, New)), (res_aa, (Eq, Gen))]]

val meta_conj_spec = ("\<and>", conj_clauses)
val meta_imp_spec = ("\<implies>", imp_clauses)
val conj_spec = ("\<and>", conj_clauses)
val disj_spec = ("\<or>", disj_clauses)
val imp_spec = ("\<implies>", imp_clauses)

fun add_annotation_clause_from_quasi_clause _ NONE = NONE
  | add_annotation_clause_from_quasi_clause [] accum = accum
  | add_annotation_clause_from_quasi_clause ((aa, (cmp, a)) :: rest) accum =
    case aa of
      A a' => if annotation_comp cmp a' a then NONE
              else add_annotation_clause_from_quasi_clause rest accum
    | V x => add_annotation_clause_from_quasi_clause rest accum
             |> Option.map (cons (x, (sign_for_comp_op cmp, a)))

fun assign_clause_from_quasi_clause unless =
  add_annotation_clause_from_quasi_clause unless (SOME [])

fun add_connective_var conn mk_quasi_clauses res_aa aa1 aa2 =
  (trace_msg (fn () => "*** Add " ^ string_for_annotation_atom res_aa ^ " = " ^
                       string_for_annotation_atom aa1 ^ " " ^ conn ^ " " ^
                       string_for_annotation_atom aa2);
   fold (add_assign_clause o assign_clause_from_quasi_clause)
        (mk_quasi_clauses res_aa aa1 aa2))
fun add_connective_frames conn mk_quasi_clauses res_frame frame1 frame2 =
  fold I (map3 (fn (_, res_aa) => fn (_, aa1) => fn (_, aa2) =>
                   add_connective_var conn mk_quasi_clauses res_aa aa1 aa2)
               res_frame frame1 frame2)

fun kill_unused_in_frame is_in (accum as ({frame, ...} : mcontext, _)) =
  let val (used_frame, unused_frame) = List.partition is_in frame in
    accum |>> set_frame used_frame
          ||> add_comp_frame (A Gen) Eq unused_frame
  end

fun split_frame is_in_fun (gamma as {frame, ...} : mcontext, cset) =
  let
    fun bubble fun_frame arg_frame [] cset =
        ((rev fun_frame, rev arg_frame), cset)
      | bubble fun_frame arg_frame ((bound as (_, aa)) :: rest) cset =
        if is_in_fun bound then
          bubble (bound :: fun_frame) arg_frame rest
                 (cset |> add_comp_frame aa Leq arg_frame)
        else
          bubble fun_frame (bound :: arg_frame) rest cset
  in cset |> bubble [] [] frame ||> pair gamma end

fun add_annotation_atom_comp_alt _ (A Gen) _ _ = I
  | add_annotation_atom_comp_alt _ (A _) _ _ =
    (trace_msg (K "*** Expected G"); raise UNSOLVABLE ())
  | add_annotation_atom_comp_alt cmp (V x) aa1 aa2 =
    add_annotation_atom_comp cmp [x] aa1 aa2

fun add_arg_order1 ((_, aa), (_, prev_aa)) = I
  add_annotation_atom_comp_alt Neq prev_aa (A Gen) aa
fun add_app1 fun_aa ((_, res_aa), (_, arg_aa)) = I
  let
    val clause = [(arg_aa, (Eq, New)), (res_aa, (Eq, Gen))]
                 |> assign_clause_from_quasi_clause
  in
    trace_msg (fn () => "*** Add " ^ string_for_assign_clause clause);
    apsnd (add_assign_clause clause)
    #> add_annotation_atom_comp_alt Leq arg_aa fun_aa res_aa
  end
fun add_app _ [] [] = I
  | add_app fun_aa res_frame arg_frame =
    add_comp_frame (A New) Leq arg_frame
    #> fold add_arg_order1 (tl arg_frame ~~ (fst (split_last arg_frame)))
    #> fold (add_app1 fun_aa) (res_frame ~~ arg_frame)

fun consider_connective mdata (conn, mk_quasi_clauses) do_t1 do_t2
                        (accum as ({frame, ...}, _)) =
  let
    val frame1 = fresh_frame mdata (SOME Tru) NONE frame
    val frame2 = fresh_frame mdata (SOME Fls) NONE frame
  in
    accum |>> set_frame frame1 |> do_t1
          |>> set_frame frame2 |> do_t2
          |>> set_frame frame
          ||> apsnd (add_connective_frames conn mk_quasi_clauses frame frame1
                                           frame2)
  end

fun consider_term (mdata as {hol_ctxt = {thy, ctxt, stds, ...}, alpha_T,
                             max_fresh, ...}) =
  let
    fun is_enough_eta_expanded t =
      case strip_comb t of
        (Const x, ts) => the_default 0 (arity_of_built_in_const thy stds x)
        <= length ts
      | _ => true
    val mtype_for = fresh_mtype_for_type mdata false
    fun mtype_for_set x T = MFun (mtype_for (pseudo_domain_type T), V x, bool_M)
    fun do_all T (gamma, cset) =
      let
        val abs_M = mtype_for (domain_type (domain_type T))
        val x = Unsynchronized.inc max_fresh
        val body_M = mtype_for (body_type T)
      in
        (MFun (MFun (abs_M, V x, body_M), A Gen, body_M),
         (gamma, cset |> add_mtype_is_complete [(x, (Plus, Tru))] abs_M))
      end
    fun do_equals T (gamma, cset) =
      let
        val M = mtype_for (domain_type T)
        val x = Unsynchronized.inc max_fresh
      in
        (MFun (M, A Gen, MFun (M, V x, mtype_for (nth_range_type 2 T))),
         (gamma, cset |> add_mtype_is_concrete [] M
                      |> add_annotation_atom_comp Leq [] (A Fls) (V x)))
      end
    fun do_robust_set_operation T (gamma, cset) =
      let
        val set_T = domain_type T
        val M1 = mtype_for set_T
        val M2 = mtype_for set_T
        val M3 = mtype_for set_T
      in
        (MFun (M1, A Gen, MFun (M2, A Gen, M3)),
         (gamma, cset |> add_is_sub_mtype M1 M3 |> add_is_sub_mtype M2 M3))
      end
    fun do_fragile_set_operation T (gamma, cset) =
      let
        val set_T = domain_type T
        val set_M = mtype_for set_T
        fun custom_mtype_for (T as Type (@{type_name fun}, [T1, T2])) =
            if T = set_T then set_M
            else MFun (custom_mtype_for T1, A Gen, custom_mtype_for T2)
          | custom_mtype_for (Type (@{type_name set}, [T'])) =
            custom_mtype_for (T' --> bool_T)
          | custom_mtype_for T = mtype_for T
      in
        (custom_mtype_for T, (gamma, cset |> add_mtype_is_concrete [] set_M))
      end
    fun do_pair_constr T accum =
      case mtype_for (nth_range_type 2 T) of
        M as MPair (a_M, b_M) =>
        (MFun (a_M, A Gen, MFun (b_M, A Gen, M)), accum)
      | M => raise MTYPE ("Nitpick_Mono.consider_term.do_pair_constr", [M], [])
    fun do_nth_pair_sel n T =
      case mtype_for (domain_type T) of
        M as MPair (a_M, b_M) =>
        pair (MFun (M, A Gen, if n = 0 then a_M else b_M))
      | M => raise MTYPE ("Nitpick_Mono.consider_term.do_nth_pair_sel", [M], [])
    and do_connect spec t1 t2 accum =
      (bool_M, consider_connective mdata spec (snd o do_term t1)
                                   (snd o do_term t2) accum)
    and do_term t
            (accum as (gamma as {bound_Ts, bound_Ms, frame, frees, consts},
                       cset)) =
      (trace_msg (fn () => "  " ^ string_for_mcontext ctxt t gamma ^
                           " \<turnstile> " ^ Syntax.string_of_term ctxt t ^
                           " : _?");
       case t of
         @{const False} => (bool_M, accum ||> add_comp_frame (A Fls) Leq frame)
       | Const (@{const_name None}, T) =>
         (mtype_for T, accum ||> add_comp_frame (A Fls) Leq frame)
       | @{const True} => (bool_M, accum ||> add_comp_frame (A Tru) Leq frame)
       | (t0 as Const (@{const_name HOL.eq}, _)) $ Bound 0 $ t2 =>
         (* hack to exploit symmetry of equality when typing "insert" *)
         (if t2 = Bound 0 then do_term @{term True}
          else do_term (t0 $ t2 $ Bound 0)) accum
       | Const (x as (s, T)) =>
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
              end
            | @{const_name HOL.eq} => do_equals T accum
            | @{const_name The} =>
              (trace_msg (K "*** The"); raise UNSOLVABLE ())
            | @{const_name Eps} =>
              (trace_msg (K "*** Eps"); raise UNSOLVABLE ())
            | @{const_name If} =>
              do_robust_set_operation (range_type T) accum
              |>> curry3 MFun bool_M (A Gen)
            | @{const_name Pair} => do_pair_constr T accum
            | @{const_name fst} => do_nth_pair_sel 0 T accum
            | @{const_name snd} => do_nth_pair_sel 1 T accum
            | @{const_name Id} =>
              (MFun (mtype_for (elem_type T), A Gen, bool_M), accum)
            | @{const_name converse} =>
              let
                val x = Unsynchronized.inc max_fresh
                val ab_set_M = domain_type T |> mtype_for_set x
                val ba_set_M = range_type T |> mtype_for_set x
              in
                (MFun (ab_set_M, A Gen, ba_set_M),
                 accum ||> add_annotation_atom_comp Neq [] (V x) (A New))
              end
            | @{const_name trancl} => do_fragile_set_operation T accum
            | @{const_name rel_comp} =>
              let
                val x = Unsynchronized.inc max_fresh
                val bc_set_M = domain_type T |> mtype_for_set x
                val ab_set_M = domain_type (range_type T) |> mtype_for_set x
                val ac_set_M = nth_range_type 2 T |> mtype_for_set x
              in
                (MFun (bc_set_M, A Gen, MFun (ab_set_M, A Gen, ac_set_M)),
                 accum ||> add_annotation_atom_comp Neq [] (V x) (A New))
              end
            | @{const_name finite} =>
              let
                val M1 = mtype_for (elem_type (domain_type T))
                val a = if exists_alpha_sub_mtype M1 then Fls else Gen
              in (MFun (MFun (M1, A a, bool_M), A Gen, bool_M), accum) end
            | @{const_name prod} =>
              let
                val x = Unsynchronized.inc max_fresh
                val a_set_M = domain_type T |> mtype_for_set x
                val b_set_M =
                  range_type (domain_type (range_type T)) |> mtype_for_set x
                val ab_set_M = nth_range_type 2 T |> mtype_for_set x
              in
                (MFun (a_set_M, A Gen, MFun (b_set_M, A Gen, ab_set_M)),
                 accum ||> add_annotation_atom_comp Neq [] (V x) (A New))
              end
            | _ =>
              if s = @{const_name safe_The} then
                let
                  val a_set_M = mtype_for (domain_type T)
                  val a_M = dest_MFun a_set_M |> #1
                in (MFun (a_set_M, A Gen, a_M), accum) end
              else if s = @{const_name ord_class.less_eq} andalso
                      is_set_like_type (domain_type T) then
                do_fragile_set_operation T accum
              else if is_sel s then
                (mtype_for_sel mdata x, accum)
              else if is_constr ctxt stds x then
                (mtype_for_constr mdata x, accum)
              else if is_built_in_const thy stds x then
                (fresh_mtype_for_type mdata true T, accum)
              else
                let val M = mtype_for T in
                  (M, ({bound_Ts = bound_Ts, bound_Ms = bound_Ms, frame = frame,
                        frees = frees, consts = (x, M) :: consts}, cset))
                end)
           ||> apsnd (add_comp_frame (A Gen) Eq frame)
         | Free (x as (_, T)) =>
           (case AList.lookup (op =) frees x of
              SOME M => (M, accum)
            | NONE =>
              let val M = mtype_for T in
                (M, ({bound_Ts = bound_Ts, bound_Ms = bound_Ms, frame = frame,
                      frees = (x, M) :: frees, consts = consts}, cset))
              end)
           ||> apsnd (add_comp_frame (A Gen) Eq frame)
         | Var _ => (trace_msg (K "*** Var"); raise UNSOLVABLE ())
         | Bound j =>
           (nth bound_Ms j,
            accum ||> add_bound_frame (length bound_Ts - j - 1) frame)
         | Abs (_, T, t') =>
           (case fin_fun_body T (fastype_of1 (T :: bound_Ts, t')) t' of
              SOME t' =>
              let
                val M = mtype_for T
                val x = Unsynchronized.inc max_fresh
                val (M', accum) = do_term t' (accum |>> push_bound (V x) T M)
              in
                (MFun (M, V x, M'),
                 accum |>> pop_bound
                       ||> add_annotation_atom_comp Leq [] (A Fls) (V x))
              end
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
                        val x = Unsynchronized.inc max_fresh
                        val (M', accum) =
                          do_term t' (accum |>> push_bound (V x) T M)
                      in (MFun (M, V x, M'), accum |>> pop_bound) end))
         | @{const Not} $ t1 => do_connect imp_spec t1 @{const False} accum
         | @{const conj} $ t1 $ t2 => do_connect conj_spec t1 t2 accum
         | @{const disj} $ t1 $ t2 => do_connect disj_spec t1 t2 accum
         | @{const implies} $ t1 $ t2 => do_connect imp_spec t1 t2 accum
         | Const (@{const_name Let}, _) $ t1 $ t2 =>
           do_term (betapply (t2, t1)) accum
         | t1 $ t2 =>
           let
             fun is_in t (j, _) = loose_bvar1 (t, length bound_Ts - j - 1)
             val accum as ({frame, ...}, _) =
               accum |> kill_unused_in_frame (is_in t)
             val ((frame1a, frame1b), accum) = accum |> split_frame (is_in t1)
             val frame2a = frame1a |> map (apsnd (K (A Gen)))
             val frame2b =
               frame1b |> map (apsnd (fn _ => V (Unsynchronized.inc max_fresh)))
             val frame2 = frame2a @ frame2b
             val (M1, accum) = accum |>> set_frame frame1a |> do_term t1
             val (M2, accum) = accum |>> set_frame frame2 |> do_term t2
           in
             let
               val (M11, aa, M12) = M1 |> dest_MFun
             in
               (M12, accum |>> set_frame frame
                           ||> add_is_sub_mtype M2 M11
                           ||> add_app aa frame1b frame2b)
             end
           end)
        |> tap (fn (M, (gamma, _)) =>
                   trace_msg (fn () => "  " ^ string_for_mcontext ctxt t gamma ^
                                       " \<turnstile> " ^
                                       Syntax.string_of_term ctxt t ^ " : " ^
                                       string_for_mtype M))
  in do_term end

fun force_gen_funs 0 _ = I
  | force_gen_funs n (M as MFun (M1, _, M2)) =
    add_mtypes_equal M (MFun (M1, A Gen, M2)) #> force_gen_funs (n - 1) M2
  | force_gen_funs _ M = raise MTYPE ("Nitpick_Mono.force_gen_funs", [M], [])
fun consider_general_equals mdata def t1 t2 accum =
  let
    val (M1, accum) = consider_term mdata t1 accum
    val (M2, accum) = consider_term mdata t2 accum
    val accum = accum ||> add_mtypes_equal M1 M2
  in
    if def then
      let
        val (head1, args1) = strip_comb t1
        val (head_M1, accum) = consider_term mdata head1 accum
      in accum ||> force_gen_funs (length args1) head_M1 end
    else
      accum
  end

fun consider_general_formula (mdata as {hol_ctxt = {ctxt, ...}, max_fresh,
                                        ...}) =
  let
    val mtype_for = fresh_mtype_for_type mdata false
    val do_term = snd oo consider_term mdata
    fun do_formula sn t (accum as (gamma, _)) =
      let
        fun do_quantifier quant_s abs_T body_t =
          let
            val abs_M = mtype_for abs_T
            val x = Unsynchronized.inc max_fresh
            val side_cond = ((sn = Minus) = (quant_s = @{const_name Ex}))
            fun ann () = if quant_s = @{const_name Ex} then Fls else Tru
          in
            accum ||> side_cond
                      ? add_mtype_is_complete [(x, (Plus, ann ()))] abs_M
                  |>> push_bound (V x) abs_T abs_M
                  |> do_formula sn body_t
                  |>> pop_bound
          end
        fun do_connect spec neg1 t1 t2 =
          consider_connective mdata spec
              (do_formula (sn |> neg1 ? negate_sign) t1) (do_formula sn t2)
        fun do_equals t1 t2 =
          case sn of
            Plus => do_term t accum
          | Minus => consider_general_equals mdata false t1 t2 accum
      in
        trace_msg (fn () => "  " ^ string_for_mcontext ctxt t gamma ^
                            " \<turnstile> " ^ Syntax.string_of_term ctxt t ^
                            " : o\<^sup>" ^ string_for_sign sn ^ "?");
        case t of
          Const (s as @{const_name all}, _) $ Abs (_, T1, t1) =>
          do_quantifier s T1 t1
        | Const (@{const_name "=="}, _) $ t1 $ t2 => do_equals t1 t2
        | @{const Trueprop} $ t1 => do_formula sn t1 accum
        | Const (s as @{const_name All}, _) $ Abs (_, T1, t1) =>
          do_quantifier s T1 t1
        | Const (s as @{const_name Ex}, T0) $ (t1 as Abs (_, T1, t1')) =>
          (case sn of
             Plus => do_quantifier s T1 t1'
           | Minus =>
             (* FIXME: Needed? *)
             do_term (@{const Not}
                      $ (HOLogic.eq_const (domain_type T0) $ t1
                         $ Abs (Name.uu, T1, @{const False}))) accum)
        | Const (@{const_name HOL.eq}, _) $ t1 $ t2 => do_equals t1 t2
        | Const (@{const_name Let}, _) $ t1 $ t2 =>
          do_formula sn (betapply (t2, t1)) accum
        | @{const Pure.conjunction} $ t1 $ t2 =>
          do_connect meta_conj_spec false t1 t2 accum
        | @{const "==>"} $ t1 $ t2 => do_connect meta_imp_spec true t1 t2 accum
        | @{const Not} $ t1 => do_connect imp_spec true t1 @{const False} accum
        | @{const conj} $ t1 $ t2 => do_connect conj_spec false t1 t2 accum
        | @{const disj} $ t1 $ t2 => do_connect disj_spec false t1 t2 accum
        | @{const implies} $ t1 $ t2 => do_connect imp_spec true t1 t2 accum
        | _ => do_term t accum
      end
      |> tap (fn (gamma, _) =>
                 trace_msg (fn () => string_for_mcontext ctxt t gamma ^
                                     " \<turnstile> " ^
                                     Syntax.string_of_term ctxt t ^
                                     " : o\<^sup>" ^ string_for_sign sn))
  in do_formula end

(* The harmless axiom optimization below is somewhat too aggressive in the face
   of (rather peculiar) user-defined axioms. *)
val harmless_consts =
  [@{const_name ord_class.less}, @{const_name ord_class.less_eq}]
val bounteous_consts = [@{const_name bisim}]

fun is_harmless_axiom ({hol_ctxt = {thy, stds, ...}, ...} : mdata) t =
    Term.add_consts t []
    |> filter_out (is_built_in_const thy stds)
    |> (forall (member (op =) harmless_consts o original_name o fst) orf
        exists (member (op =) bounteous_consts o fst))

fun consider_nondefinitional_axiom mdata t =
  if is_harmless_axiom mdata t then I
  else consider_general_formula mdata Plus t

fun consider_definitional_axiom (mdata as {hol_ctxt = {ctxt, ...}, ...} : mdata) t =
  if not (is_constr_pattern_formula ctxt t) then
    consider_nondefinitional_axiom mdata t
  else if is_harmless_axiom mdata t then
    I
  else
    let
      val mtype_for = fresh_mtype_for_type mdata false
      val do_term = snd oo consider_term mdata
      fun do_all abs_T body_t accum =
        accum |>> push_bound (A Gen) abs_T (mtype_for abs_T)
              |> do_formula body_t
              |>> pop_bound
      and do_implies t1 t2 = do_term t1 #> do_formula t2
      and do_formula t accum =
        case t of
          Const (@{const_name all}, _) $ Abs (_, T1, t1) => do_all T1 t1 accum
        | @{const Trueprop} $ t1 => do_formula t1 accum
        | Const (@{const_name "=="}, _) $ t1 $ t2 =>
          consider_general_equals mdata true t1 t2 accum
        | @{const "==>"} $ t1 $ t2 => do_implies t1 t2 accum
        | @{const Pure.conjunction} $ t1 $ t2 =>
          fold (do_formula) [t1, t2] accum
        | Const (@{const_name All}, _) $ Abs (_, T1, t1) => do_all T1 t1 accum
        | Const (@{const_name HOL.eq}, _) $ t1 $ t2 =>
          consider_general_equals mdata true t1 t2 accum
        | @{const conj} $ t1 $ t2 => fold (do_formula) [t1, t2] accum
        | @{const implies} $ t1 $ t2 => do_implies t1 t2 accum
        | _ => raise TERM ("Nitpick_Mono.consider_definitional_axiom.\
                           \do_formula", [t])
    in do_formula t end

fun string_for_mtype_of_term ctxt asgs t M =
  Syntax.string_of_term ctxt t ^ " : " ^ string_for_mtype (resolve_mtype asgs M)

fun print_mcontext ctxt asgs ({frees, consts, ...} : mcontext) =
  trace_msg (fn () =>
      map (fn (x, M) => string_for_mtype_of_term ctxt asgs (Free x) M) frees @
      map (fn (x, M) => string_for_mtype_of_term ctxt asgs (Const x) M) consts
      |> cat_lines)

fun formulas_monotonic (hol_ctxt as {ctxt, tac_timeout, ...}) binarize alpha_T
                       (nondef_ts, def_ts) =
  let
    val _ = trace_msg (fn () => "****** Monotonicity analysis: " ^
                                string_for_mtype MAlpha ^ " is " ^
                                Syntax.string_of_typ ctxt alpha_T)
    val mdata as {max_fresh, ...} = initial_mdata hol_ctxt binarize alpha_T
    val (gamma, cset) =
      (initial_gamma, ([], []))
      |> consider_general_formula mdata Plus (hd nondef_ts)
      |> fold (consider_nondefinitional_axiom mdata) (tl nondef_ts)
      |> fold (consider_definitional_axiom mdata) def_ts
  in
    case solve tac_timeout (!max_fresh) cset of
      SOME asgs => (print_mcontext ctxt asgs gamma; true)
    | _ => false
  end
  handle UNSOLVABLE () => false
       | MTYPE (loc, Ms, Ts) =>
         raise BAD (loc, commas (map string_for_mtype Ms @
                                 map (Syntax.string_of_typ ctxt) Ts))

end;
