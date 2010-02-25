(*  Title:      HOL/Tools/Nitpick/nitpick_mono.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009, 2010

Monotonicity inference for higher-order logic.
*)

signature NITPICK_MONO =
sig
  type hol_context = Nitpick_HOL.hol_context

  val formulas_monotonic :
    hol_context -> bool -> typ -> term list * term list * term -> bool
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
  MAtom of term * mtyp |
  MAbs of string * typ * mtyp * sign_atom * mterm |
  MApp of mterm * mterm

type mdata =
  {hol_ctxt: hol_context,
   binarize: bool,
   alpha_T: typ,
   max_fresh: int Unsynchronized.ref,
   datatype_cache: ((string * typ list) * mtyp) list Unsynchronized.ref,
   constr_cache: (styp * mtyp) list Unsynchronized.ref}

exception MTYPE of string * mtyp list

(* string -> unit *)
fun print_g (_ : string) = ()

(* var -> string *)
val string_for_var = signed_string_of_int
(* string -> var list -> string *)
fun string_for_vars sep [] = "0\<^bsub>" ^ sep ^ "\<^esub>"
  | string_for_vars sep xs = space_implode sep (map string_for_var xs)
fun subscript_string_for_vars sep xs =
  if null xs then "" else "\<^bsub>" ^ string_for_vars sep xs ^ "\<^esub>"

(* sign -> string *)
fun string_for_sign Plus = "+"
  | string_for_sign Minus = "-"

(* sign -> sign -> sign *)
fun xor sn1 sn2 = if sn1 = sn2 then Plus else Minus
(* sign -> sign *)
val negate = xor Minus

(* sign_atom -> string *)
fun string_for_sign_atom (S sn) = string_for_sign sn
  | string_for_sign_atom (V j) = string_for_var j

(* literal -> string *)
fun string_for_literal (x, sn) = string_for_var x ^ " = " ^ string_for_sign sn

val bool_M = MType (@{type_name bool}, [])
val irrelevant_M = MType (nitpick_prefix ^ "irrelevant", [])

(* mtyp -> bool *)
fun is_MRec (MRec _) = true
  | is_MRec _ = false
(* mtyp -> mtyp * sign_atom * mtyp *)
fun dest_MFun (MFun z) = z
  | dest_MFun M = raise MTYPE ("Nitpick_Mono.dest_MFun", [M])

val no_prec = 100

(* mtyp -> int *)
fun precedence_of_mtype (MFun _) = 1
  | precedence_of_mtype (MPair _) = 2
  | precedence_of_mtype _ = no_prec

(* mtyp -> string *)
val string_for_mtype =
  let
    (* int -> mtyp -> string *)
    fun aux outer_prec M =
      let
        val prec = precedence_of_mtype M
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then "(" else "") ^
        (case M of
           MAlpha => "\<alpha>"
         | MFun (M1, a, M2) =>
           aux (prec + 1) M1 ^ " \<Rightarrow>\<^bsup>" ^
           string_for_sign_atom a ^ "\<^esup> " ^ aux prec M2
         | MPair (M1, M2) => aux (prec + 1) M1 ^ " \<times> " ^ aux prec M2
         | MType (s, []) =>
           if s = @{type_name prop} orelse s = @{type_name bool} then "o" else s
         | MType (s, Ms) => "(" ^ commas (map (aux 0) Ms) ^ ") " ^ s
         | MRec (s, _) => "[" ^ s ^ "]") ^
        (if need_parens then ")" else "")
      end
  in aux 0 end

(* mtyp -> mtyp list *)
fun flatten_mtype (MPair (M1, M2)) = maps flatten_mtype [M1, M2]
  | flatten_mtype (MType (_, Ms)) = maps flatten_mtype Ms
  | flatten_mtype M = [M]

(* mterm -> bool *)
fun precedence_of_mterm (MAtom _) = no_prec
  | precedence_of_mterm (MAbs _) = 1
  | precedence_of_mterm (MApp _) = 2

(* Proof.context -> mterm -> string *)
fun string_for_mterm ctxt =
  let
    (* mtype -> string *)
    fun mtype_annotation M = "\<^bsup>" ^ string_for_mtype M ^ "\<^esup>"
    (* int -> mterm -> string *)
    fun aux outer_prec m =
      let
        val prec = precedence_of_mterm m
        val need_parens = (prec < outer_prec)
      in
        (if need_parens then "(" else "") ^
        (case m of
           MAtom (t, M) => Syntax.string_of_term ctxt t ^ mtype_annotation M
         | MAbs (s, _, M, a, m) =>
           "\<lambda>" ^ s ^ mtype_annotation M ^ ".\<^bsup>" ^
           string_for_sign_atom a ^ "\<^esup> " ^ aux prec m
         | MApp (m1, m2) => aux prec m1 ^ " " ^ aux (prec + 1) m2) ^
        (if need_parens then ")" else "")
      end
  in aux 0 end

(* mterm -> mtyp *)
fun mtype_of_mterm (MAtom (_, M)) = M
  | mtype_of_mterm (MAbs (_, _, M, a, m)) = MFun (M, a, mtype_of_mterm m)
  | mtype_of_mterm (MApp (m1, _)) =
    case mtype_of_mterm m1 of
      MFun (_, _, M12) => M12
    | M1 => raise MTYPE ("Nitpick_Mono.mtype_of_mterm", [M1])

(* hol_context -> bool -> typ -> mdata *)
fun initial_mdata hol_ctxt binarize alpha_T =
  ({hol_ctxt = hol_ctxt, binarize = binarize, alpha_T = alpha_T,
    max_fresh = Unsynchronized.ref 0, datatype_cache = Unsynchronized.ref [],
    constr_cache = Unsynchronized.ref []} : mdata)

(* typ -> typ -> bool *)
fun could_exist_alpha_subtype alpha_T (T as Type (_, Ts)) =
    T = alpha_T orelse (not (is_fp_iterator_type T) andalso
                        exists (could_exist_alpha_subtype alpha_T) Ts)
  | could_exist_alpha_subtype alpha_T T = (T = alpha_T)
(* theory -> typ -> typ -> bool *)
fun could_exist_alpha_sub_mtype _ (alpha_T as TFree _) T =
    could_exist_alpha_subtype alpha_T T
  | could_exist_alpha_sub_mtype thy alpha_T T =
    (T = alpha_T orelse is_datatype thy [(NONE, true)] T)

(* mtyp -> bool *)
fun exists_alpha_sub_mtype MAlpha = true
  | exists_alpha_sub_mtype (MFun (M1, _, M2)) =
    exists exists_alpha_sub_mtype [M1, M2]
  | exists_alpha_sub_mtype (MPair (M1, M2)) =
    exists exists_alpha_sub_mtype [M1, M2]
  | exists_alpha_sub_mtype (MType (_, Ms)) = exists exists_alpha_sub_mtype Ms
  | exists_alpha_sub_mtype (MRec _) = true

(* mtyp -> bool *)
fun exists_alpha_sub_mtype_fresh MAlpha = true
  | exists_alpha_sub_mtype_fresh (MFun (_, V _, _)) = true
  | exists_alpha_sub_mtype_fresh (MFun (_, _, M2)) =
    exists_alpha_sub_mtype_fresh M2
  | exists_alpha_sub_mtype_fresh (MPair (M1, M2)) =
    exists exists_alpha_sub_mtype_fresh [M1, M2]
  | exists_alpha_sub_mtype_fresh (MType (_, Ms)) =
    exists exists_alpha_sub_mtype_fresh Ms
  | exists_alpha_sub_mtype_fresh (MRec _) = true

(* string * typ list -> mtyp list -> mtyp *)
fun constr_mtype_for_binders z Ms =
  fold_rev (fn M => curry3 MFun M (S Minus)) Ms (MRec z)

(* ((string * typ list) * mtyp) list -> mtyp list -> mtyp -> mtyp *)
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

(* ((string * typ list) * mtyp) list Unsynchronized.ref -> unit *)
fun repair_datatype_cache cache =
  let
    (* (string * typ list) * mtyp -> unit *)
    fun repair_one (z, M) =
      Unsynchronized.change cache
          (AList.update (op =) (z, repair_mtype (!cache) [] M))
  in List.app repair_one (rev (!cache)) end

(* (typ * mtyp) list -> (styp * mtyp) list Unsynchronized.ref -> unit *)
fun repair_constr_cache dtype_cache constr_cache =
  let
    (* styp * mtyp -> unit *)
    fun repair_one (x, M) =
      Unsynchronized.change constr_cache
          (AList.update (op =) (x, repair_mtype dtype_cache [] M))
  in List.app repair_one (!constr_cache) end

(* mdata -> typ -> typ -> mtyp * sign_atom * mtyp *)
fun fresh_mfun_for_fun_type (mdata as {max_fresh, ...} : mdata) T1 T2 =
  let
    val M1 = fresh_mtype_for_type mdata T1
    val M2 = fresh_mtype_for_type mdata T2
    val a = if is_boolean_type (body_type T2) andalso
               exists_alpha_sub_mtype_fresh M1 then
              V (Unsynchronized.inc max_fresh)
            else
              S Minus
  in (M1, a, M2) end
(* mdata -> typ -> mtyp *)
and fresh_mtype_for_type (mdata as {hol_ctxt as {thy, ...}, binarize, alpha_T,
                                    datatype_cache, constr_cache, ...}) =
  let
    (* typ -> typ -> mtyp *)
    val do_fun = MFun oo fresh_mfun_for_fun_type mdata
    (* typ -> mtyp *)
    fun do_type T =
      if T = alpha_T then
        MAlpha
      else case T of
        Type ("fun", [T1, T2]) => do_fun T1 T2
      | Type (@{type_name fun_box}, [T1, T2]) => do_fun T1 T2
      | Type ("*", [T1, T2]) => MPair (pairself do_type (T1, T2))
      | Type (z as (s, _)) =>
        if could_exist_alpha_sub_mtype thy alpha_T T then
          case AList.lookup (op =) (!datatype_cache) z of
            SOME M => M
          | NONE =>
            let
              val _ = Unsynchronized.change datatype_cache (cons (z, MRec z))
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
              val _ = Unsynchronized.change datatype_cache
                          (AList.update (op =) (z, M))
              val _ = Unsynchronized.change constr_cache
                          (append (xs ~~ constr_Ms))
            in
              if forall (not o is_MRec o snd) (!datatype_cache) then
                (repair_datatype_cache datatype_cache;
                 repair_constr_cache (!datatype_cache) constr_cache;
                 AList.lookup (op =) (!datatype_cache) z |> the)
              else
                M
            end
        else
          MType (s, [])
      | _ => MType (Refute.string_of_typ T, [])
  in do_type end

(* mtyp -> mtyp list *)
fun prodM_factors (MPair (M1, M2)) = maps prodM_factors [M1, M2]
  | prodM_factors M = [M]
(* mtyp -> mtyp list * mtyp *)
fun curried_strip_mtype (MFun (M1, S Minus, M2)) =
    curried_strip_mtype M2 |>> append (prodM_factors M1)
  | curried_strip_mtype M = ([], M)
(* string -> mtyp -> mtyp *)
fun sel_mtype_from_constr_mtype s M =
  let val (arg_Ms, dataM) = curried_strip_mtype M in
    MFun (dataM, S Minus,
          case sel_no_from_name s of ~1 => bool_M | n => nth arg_Ms n)
  end

(* mdata -> styp -> mtyp *)
fun mtype_for_constr (mdata as {hol_ctxt = {thy, ...}, alpha_T, constr_cache,
                                ...}) (x as (_, T)) =
  if could_exist_alpha_sub_mtype thy alpha_T T then
    case AList.lookup (op =) (!constr_cache) x of
      SOME M => M
    | NONE => if T = alpha_T then
                let val M = fresh_mtype_for_type mdata T in
                  (Unsynchronized.change constr_cache (cons (x, M)); M)
                end
              else
                (fresh_mtype_for_type mdata (body_type T);
                 AList.lookup (op =) (!constr_cache) x |> the)
  else
    fresh_mtype_for_type mdata T
fun mtype_for_sel (mdata as {hol_ctxt, binarize, ...}) (x as (s, _)) =
  x |> binarized_and_boxed_constr_for_sel hol_ctxt binarize
    |> mtype_for_constr mdata |> sel_mtype_from_constr_mtype s

(* literal list -> mtyp -> mtyp *)
fun instantiate_mtype lits =
  let
    (* mtyp -> mtyp *)
    fun aux MAlpha = MAlpha
      | aux (MFun (M1, V x, M2)) =
        let
          val a = case AList.lookup (op =) lits x of
                    SOME sn => S sn
                  | NONE => V x
        in MFun (aux M1, a, aux M2) end
      | aux (MFun (M1, a, M2)) = MFun (aux M1, a, aux M2)
      | aux (MPair Mp) = MPair (pairself aux Mp)
      | aux (MType (s, Ms)) = MType (s, map aux Ms)
      | aux (MRec z) = MRec z
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
       (_, S Minus) => SOME accum
     | (S Plus, _) => SOME accum
     | (S Minus, S Plus) => NONE
     | (V _, V _) => SOME (lits, insert (op =) (a1, a2, Leq, []) comps)
     | _ => do_sign_atom_comp Eq [] a1 a2 accum)
  | do_sign_atom_comp cmp xs a1 a2 (lits, comps) =
    SOME (lits, insert (op =) (a1, a2, cmp, xs) comps)

(* comp -> var list -> mtyp -> mtyp -> (literal list * comp list) option
   -> (literal list * comp list) option *)
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
            raise MTYPE ("Nitpick_Mono.do_mtype_comp", [M1, M2]))
  | do_mtype_comp _ _ (MType _) (MType _) accum =
    accum (* no need to compare them thanks to the cache *)
  | do_mtype_comp _ _ M1 M2 _ =
    raise MTYPE ("Nitpick_Mono.do_mtype_comp", [M1, M2])

(* comp_op -> mtyp -> mtyp -> constraint_set -> constraint_set *)
fun add_mtype_comp _ _ _ UnsolvableCSet = UnsolvableCSet
  | add_mtype_comp cmp M1 M2 (CSet (lits, comps, sexps)) =
    (print_g ("*** Add " ^ string_for_mtype M1 ^ " " ^ string_for_comp_op cmp ^
              " " ^ string_for_mtype M2);
     case do_mtype_comp cmp [] M1 M2 (SOME (lits, comps)) of
       NONE => (print_g "**** Unsolvable"; UnsolvableCSet)
     | SOME (lits, comps) => CSet (lits, comps, sexps))

(* mtyp -> mtyp -> constraint_set -> constraint_set *)
val add_mtypes_equal = add_mtype_comp Eq
val add_is_sub_mtype = add_mtype_comp Leq

(* sign -> sign_expr -> mtyp -> (literal list * sign_expr list) option
   -> (literal list * sign_expr list) option *)
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
    raise MTYPE ("Nitpick_Mono.do_notin_mtype_fv", [M])

(* sign -> mtyp -> constraint_set -> constraint_set *)
fun add_notin_mtype_fv _ _ UnsolvableCSet = UnsolvableCSet
  | add_notin_mtype_fv sn M (CSet (lits, comps, sexps)) =
    (print_g ("*** Add " ^ string_for_mtype M ^ " is right-" ^
              (case sn of Minus => "unique" | Plus => "total") ^ ".");
     case do_notin_mtype_fv sn [] M (SOME (lits, sexps)) of
       NONE => (print_g "**** Unsolvable"; UnsolvableCSet)
     | SOME (lits, sexps) => CSet (lits, comps, sexps))

(* mtyp -> constraint_set -> constraint_set *)
val add_mtype_is_right_unique = add_notin_mtype_fv Minus
val add_mtype_is_right_total = add_notin_mtype_fv Plus

val bool_from_minus = true

(* sign -> bool *)
fun bool_from_sign Plus = not bool_from_minus
  | bool_from_sign Minus = bool_from_minus
(* bool -> sign *)
fun sign_from_bool b = if b = bool_from_minus then Minus else Plus

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
    PropLogic.SOr (prop_for_sign_atom_eq (a1, Plus),
                   prop_for_sign_atom_eq (a2, Minus))
  | prop_for_comp (a1, a2, cmp, xs) =
    PropLogic.SOr (prop_for_exists_eq xs Minus, prop_for_comp (a1, a2, cmp, []))

(* var -> (int -> bool option) -> literal list -> literal list *)
fun literals_from_assignments max_var assigns lits =
  fold (fn x => fn accum =>
           if AList.defined (op =) lits x then
             accum
           else case assigns x of
             SOME b => (x, sign_from_bool b) :: accum
           | NONE => accum) (max_var downto 1) lits

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
  let val (pos, neg) = List.partition (curry (op =) Plus o snd) lits in
    print_g ("*** Solution:\n" ^
             "+: " ^ commas (map (string_for_var o fst) pos) ^ "\n" ^
             "-: " ^ commas (map (string_for_var o fst) neg))
  end

(* var -> constraint_set -> literal list option *)
fun solve _ UnsolvableCSet = (print_g "*** Problem: Unsolvable"; NONE)
  | solve max_var (CSet (lits, comps, sexps)) =
    let
      val _ = print_problem lits comps sexps
      val prop = PropLogic.all (map prop_for_literal lits @
                                map prop_for_comp comps @
                                map prop_for_sign_expr sexps)
      (* use the first ML solver (to avoid startup overhead) *)
      val solvers = !SatSolver.solvers
                    |> filter (member (op =) ["dptsat", "dpll"] o fst)
    in
      case snd (hd solvers) prop of
        SatSolver.SATISFIABLE assigns =>
        SOME (literals_from_assignments max_var assigns lits
              |> tap print_solution)
      | _ => NONE
    end

type mtype_schema = mtyp * constraint_set
type mtype_context =
  {bounds: mtyp list,
   frees: (styp * mtyp) list,
   consts: (styp * mtyp) list}

type accumulator = mtype_context * constraint_set

val initial_gamma = {bounds = [], frees = [], consts = []}
val unsolvable_accum = (initial_gamma, UnsolvableCSet)

(* mtyp -> mtype_context -> mtype_context *)
fun push_bound M {bounds, frees, consts} =
  {bounds = M :: bounds, frees = frees, consts = consts}
(* mtype_context -> mtype_context *)
fun pop_bound {bounds, frees, consts} =
  {bounds = tl bounds, frees = frees, consts = consts}
  handle List.Empty => initial_gamma

(* mdata -> term -> accumulator -> mterm * accumulator *)
fun consider_term (mdata as {hol_ctxt = {thy, ctxt, stds, fast_descrs,
                                         def_table, ...},
                             alpha_T, max_fresh, ...}) =
  let
    (* typ -> typ -> mtyp * sign_atom * mtyp *)
    val mfun_for = fresh_mfun_for_fun_type mdata
    (* typ -> mtyp *)
    val mtype_for = fresh_mtype_for_type mdata
    (* mtyp -> mtyp *)
    fun pos_set_mtype_for_dom M =
      MFun (M, S (if exists_alpha_sub_mtype M then Plus else Minus), bool_M)
    (* typ -> accumulator -> mterm * accumulator *)
    fun do_all T (gamma, cset) =
      let
        val abs_M = mtype_for (domain_type (domain_type T))
        val body_M = mtype_for (range_type T)
      in
        (MFun (MFun (abs_M, S Minus, body_M), S Minus, body_M),
         (gamma, cset |> add_mtype_is_right_total abs_M))
      end
    fun do_equals T (gamma, cset) =
      let val M = mtype_for (domain_type T) in
        (MFun (M, S Minus, MFun (M, V (Unsynchronized.inc max_fresh),
                                 mtype_for (nth_range_type 2 T))),
         (gamma, cset |> add_mtype_is_right_unique M))
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
        (* typ -> mtyp *)
        fun custom_mtype_for (T as Type ("fun", [T1, T2])) =
            if T = set_T then set_M
            else MFun (custom_mtype_for T1, S Minus, custom_mtype_for T2)
          | custom_mtype_for T = mtype_for T
      in
        (custom_mtype_for T, (gamma, cset |> add_mtype_is_right_unique set_M))
      end
    (* typ -> accumulator -> mtyp * accumulator *)
    fun do_pair_constr T accum =
      case mtype_for (nth_range_type 2 T) of
        M as MPair (a_M, b_M) =>
        (MFun (a_M, S Minus, MFun (b_M, S Minus, M)), accum)
      | M => raise MTYPE ("Nitpick_Mono.consider_term.do_pair_constr", [M])
    (* int -> typ -> accumulator -> mtyp * accumulator *)
    fun do_nth_pair_sel n T =
      case mtype_for (domain_type T) of
        M as MPair (a_M, b_M) =>
        pair (MFun (M, S Minus, if n = 0 then a_M else b_M))
      | M => raise MTYPE ("Nitpick_Mono.consider_term.do_nth_pair_sel", [M])
    (* mtyp * accumulator *)
    val mtype_unsolvable = (irrelevant_M, unsolvable_accum)
    (* term -> mterm * accumulator *)
    fun mterm_unsolvable t = (MAtom (t, irrelevant_M), unsolvable_accum)
    (* term -> string -> typ -> term -> term -> term -> accumulator
       -> mterm * accumulator *)
    fun do_bounded_quantifier t0 abs_s abs_T connective_t bound_t body_t accum =
      let
        val abs_M = mtype_for abs_T
        val (bound_m, accum) = accum |>> push_bound abs_M |> do_term bound_t
        val expected_bound_M = pos_set_mtype_for_dom abs_M
        val (body_m, accum) =
          accum ||> add_mtypes_equal expected_bound_M (mtype_of_mterm bound_m)
                |> do_term body_t ||> apfst pop_bound
        val bound_M = mtype_of_mterm bound_m
        val (M1, a, M2) = dest_MFun bound_M
      in
        (MApp (MAtom (t0, MFun (bound_M, S Minus, bool_M)),
               MAbs (abs_s, abs_T, M1, a,
                     MApp (MApp (MAtom (connective_t, irrelevant_M),
                                 MApp (bound_m, MAtom (Bound 0, M1))),
                           body_m))), accum)
      end
    (* term -> accumulator -> mterm * accumulator *)
    and do_term t (_, UnsolvableCSet) = mterm_unsolvable t
      | do_term t (accum as (gamma as {bounds, frees, consts}, cset)) =
        (case t of
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
                do_term (@{const Not}
                         $ (HOLogic.eq_const (domain_type T)
                            $ Abs (Name.uu, T, @{const False}))) accum
                |>> mtype_of_mterm
              | @{const_name "op ="} => do_equals T accum
              | @{const_name The} => (print_g "*** The"; mtype_unsolvable)
              | @{const_name Eps} => (print_g "*** Eps"; mtype_unsolvable)
              | @{const_name If} =>
                do_robust_set_operation (range_type T) accum
                |>> curry3 MFun bool_M (S Minus)
              | @{const_name Pair} => do_pair_constr T accum
              | @{const_name fst} => do_nth_pair_sel 0 T accum
              | @{const_name snd} => do_nth_pair_sel 1 T accum 
              | @{const_name Id} =>
                (MFun (mtype_for (domain_type T), S Minus, bool_M), accum)
              | @{const_name insert} =>
                let
                  val set_T = domain_type (range_type T)
                  val M1 = mtype_for (domain_type set_T)
                  val M1' = pos_set_mtype_for_dom M1
                  val M2 = mtype_for set_T
                  val M3 = mtype_for set_T
                in
                  (MFun (M1, S Minus, MFun (M2, S Minus, M3)),
                   (gamma, cset |> add_mtype_is_right_unique M1
                                |> add_is_sub_mtype M1' M3
                                |> add_is_sub_mtype M2 M3))
                end
              | @{const_name converse} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  (* typ -> mtyp *)
                  fun mtype_for_set T =
                    MFun (mtype_for (domain_type T), V x, bool_M)
                  val ab_set_M = domain_type T |> mtype_for_set
                  val ba_set_M = range_type T |> mtype_for_set
                in (MFun (ab_set_M, S Minus, ba_set_M), accum) end
              | @{const_name trancl} => do_fragile_set_operation T accum
              | @{const_name rtrancl} =>
                (print_g "*** rtrancl"; mtype_unsolvable)
              | @{const_name finite} =>
                let val M1 = mtype_for (domain_type (domain_type T)) in
                  (MFun (pos_set_mtype_for_dom M1, S Minus, bool_M), accum)
                end
              | @{const_name rel_comp} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  (* typ -> mtyp *)
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
                         MFun (pos_set_mtype_for_dom a_M, S Minus,
                               pos_set_mtype_for_dom b_M)), accum)
                end
              | @{const_name Sigma} =>
                let
                  val x = Unsynchronized.inc max_fresh
                  (* typ -> mtyp *)
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
              | @{const_name Tha} =>
                let
                  val a_M = mtype_for (domain_type (domain_type T))
                  val a_set_M = pos_set_mtype_for_dom a_M
                in (MFun (a_set_M, S Minus, a_M), accum) end
              | @{const_name FunBox} =>
                let val dom_M = mtype_for (domain_type T) in
                  (MFun (dom_M, S Minus, dom_M), accum)
                end
              | _ =>
                if s = @{const_name minus_class.minus} andalso
                   is_set_type (domain_type T) then
                  let
                    val set_T = domain_type T
                    val left_set_M = mtype_for set_T
                    val right_set_M = mtype_for set_T
                  in
                    (MFun (left_set_M, S Minus,
                           MFun (right_set_M, S Minus, left_set_M)),
                     (gamma, cset |> add_mtype_is_right_unique right_set_M
                                  |> add_is_sub_mtype right_set_M left_set_M))
                  end
                else if s = @{const_name ord_class.less_eq} andalso
                        is_set_type (domain_type T) then
                  do_fragile_set_operation T accum
                else if (s = @{const_name semilattice_inf_class.inf} orelse
                         s = @{const_name semilattice_sup_class.sup}) andalso
                        is_set_type (domain_type T) then
                  do_robust_set_operation T accum
                else if is_sel s then
                  if constr_name_for_sel_like s = @{const_name FunBox} then
                    let val dom_M = mtype_for (domain_type T) in
                      (MFun (dom_M, S Minus, dom_M), accum)
                    end
                  else
                    (mtype_for_sel mdata x, accum)
                else if is_constr thy stds x then
                  (mtype_for_constr mdata x, accum)
                else if is_built_in_const thy stds fast_descrs x then
                  case def_of_const thy def_table x of
                    SOME t' => do_term t' accum |>> mtype_of_mterm
                  | NONE => (print_g ("*** built-in " ^ s); mtype_unsolvable)
                else
                  let val M = mtype_for T in
                    (M, ({bounds = bounds, frees = frees,
                          consts = (x, M) :: consts}, cset))
                  end) |>> curry MAtom t
         | Free (x as (_, T)) =>
           (case AList.lookup (op =) frees x of
              SOME M => (M, accum)
            | NONE =>
              let val M = mtype_for T in
                (M, ({bounds = bounds, frees = (x, M) :: frees,
                      consts = consts}, cset))
              end) |>> curry MAtom t
         | Var _ => (print_g "*** Var"; mterm_unsolvable t)
         | Bound j => (MAtom (t, nth bounds j), accum)
         | Abs (s, T, t' as @{const False}) =>
           let val (M1, a, M2) = mfun_for T bool_T in
             (MAbs (s, T, M1, a, MAtom (t', M2)), accum)
           end
         | Abs (s, T, t') =>
           ((case t' of
               t1' $ Bound 0 =>
               if not (loose_bvar1 (t1', 0)) then
                 do_term (incr_boundvars ~1 t1') accum
               else
                 raise SAME ()
             | _ => raise SAME ())
            handle SAME () =>
                   let
                     val M = mtype_for T
                     val (m', accum) = do_term t' (accum |>> push_bound M)
                   in (MAbs (s, T, M, S Minus, m'), accum |>> pop_bound) end)
         | (t0 as Const (@{const_name All}, _))
           $ Abs (s', T', (t10 as @{const "op -->"}) $ (t11 $ Bound 0) $ t12) =>
           do_bounded_quantifier t0 s' T' t10 t11 t12 accum
         | (t0 as Const (@{const_name Ex}, _))
           $ Abs (s', T', (t10 as @{const "op &"}) $ (t11 $ Bound 0) $ t12) =>
           do_bounded_quantifier t0 s' T' t10 t11 t12 accum
         | Const (@{const_name Let}, _) $ t1 $ t2 =>
           do_term (betapply (t2, t1)) accum
         | t1 $ t2 =>
           let
             val (m1, accum) = do_term t1 accum
             val (m2, accum) = do_term t2 accum
           in
             case accum of
               (_, UnsolvableCSet) => mterm_unsolvable t
             | _ => (MApp (m1, m2), accum)
           end)
        |> tap (fn (m, _) => print_g ("  \<Gamma> \<turnstile> " ^
                                      string_for_mterm ctxt m))
  in do_term end

(* mdata -> sign -> term -> accumulator -> accumulator *)
fun consider_general_formula (mdata as {hol_ctxt = {ctxt, ...}, ...}) =
  let
    (* typ -> mtyp *)
    val mtype_for = fresh_mtype_for_type mdata
    (* term -> accumulator -> mtyp * accumulator *)
    val do_term = apfst mtype_of_mterm oo consider_term mdata
    (* sign -> term -> accumulator -> accumulator *)
    fun do_formula _ _ (_, UnsolvableCSet) = unsolvable_accum
      | do_formula sn t (accum as (gamma, cset)) =
        let
          (* term -> accumulator -> accumulator *)
          val do_co_formula = do_formula sn
          val do_contra_formula = do_formula (negate sn)
          (* string -> typ -> term -> accumulator *)
          fun do_quantifier quant_s abs_T body_t =
            let
              val abs_M = mtype_for abs_T
              val side_cond = ((sn = Minus) = (quant_s = @{const_name Ex}))
              val cset = cset |> side_cond ? add_mtype_is_right_total abs_M
            in
              (gamma |> push_bound abs_M, cset)
              |> do_co_formula body_t |>> pop_bound
            end
          (* typ -> term -> accumulator *)
          fun do_bounded_quantifier abs_T body_t =
            accum |>> push_bound (mtype_for abs_T) |> do_co_formula body_t
                  |>> pop_bound
          (* term -> term -> accumulator *)
          fun do_equals t1 t2 =
            case sn of
              Plus => do_term t accum |> snd
            | Minus => let
                         val (M1, accum) = do_term t1 accum
                         val (M2, accum) = do_term t2 accum
                       in accum ||> add_mtypes_equal M1 M2 end
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
          | Const (s0 as @{const_name Ex}, T0) $ (t1 as Abs (_, T1, t1')) =>
            (case sn of
               Plus => do_quantifier s0 T1 t1'
             | Minus =>
               do_term (@{const Not}
                        $ (HOLogic.eq_const (domain_type T0) $ t1
                           $ Abs (Name.uu, T1, @{const False}))) accum |> snd)
          | Const (@{const_name "op ="}, _) $ t1 $ t2 => do_equals t1 t2
          | @{const "op &"} $ t1 $ t2 =>
            accum |> do_co_formula t1 |> do_co_formula t2
          | @{const "op |"} $ t1 $ t2 =>
            accum |> do_co_formula t1 |> do_co_formula t2
          | @{const "op -->"} $ t1 $ t2 =>
            accum |> do_contra_formula t1 |> do_co_formula t2
          | Const (@{const_name If}, _) $ t1 $ t2 $ t3 =>
            accum |> do_term t1 |> snd |> fold do_co_formula [t2, t3]
          | Const (@{const_name Let}, _) $ t1 $ t2 =>
            do_co_formula (betapply (t2, t1)) accum
          | _ => do_term t accum |> snd
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
fun is_harmless_axiom ({thy, stds, fast_descrs, ...} : hol_context) t =
  Term.add_consts t []
  |> filter_out (is_built_in_const thy stds fast_descrs)
  |> (forall (member (op =) harmless_consts o original_name o fst)
      orf exists (member (op =) bounteous_consts o fst))

(* mdata -> sign -> term -> accumulator -> accumulator *)
fun consider_nondefinitional_axiom (mdata as {hol_ctxt, ...}) sn t =
  not (is_harmless_axiom hol_ctxt t) ? consider_general_formula mdata sn t

(* mdata -> term -> accumulator -> accumulator *)
fun consider_definitional_axiom (mdata as {hol_ctxt as {thy, ...}, ...}) t =
  if not (is_constr_pattern_formula thy t) then
    consider_nondefinitional_axiom mdata Plus t
  else if is_harmless_axiom hol_ctxt t then
    I
  else
    let
      (* term -> accumulator -> mtyp * accumulator *)
      val do_term = apfst mtype_of_mterm oo consider_term mdata
      (* typ -> term -> accumulator -> accumulator *)
      fun do_all abs_T body_t accum =
        let val abs_M = fresh_mtype_for_type mdata abs_T in
          accum |>> push_bound abs_M |> do_formula body_t |>> pop_bound
        end
      (* term -> term -> accumulator -> accumulator *)
      and do_implies t1 t2 = do_term t1 #> snd #> do_formula t2
      and do_equals t1 t2 accum =
        let
          val (M1, accum) = do_term t1 accum
          val (M2, accum) = do_term t2 accum
        in accum ||> add_mtypes_equal M1 M2 end
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

(* Proof.context -> literal list -> term -> mtyp -> string *)
fun string_for_mtype_of_term ctxt lits t M =
  Syntax.string_of_term ctxt t ^ " : " ^
  string_for_mtype (instantiate_mtype lits M)

(* theory -> literal list -> mtype_context -> unit *)
fun print_mtype_context ctxt lits ({frees, consts, ...} : mtype_context) =
  map (fn (x, M) => string_for_mtype_of_term ctxt lits (Free x) M) frees @
  map (fn (x, M) => string_for_mtype_of_term ctxt lits (Const x) M) consts
  |> cat_lines |> print_g

(* hol_context -> bool -> typ -> term list * term list * term -> bool *)
fun formulas_monotonic (hol_ctxt as {ctxt, ...}) binarize alpha_T
                       (def_ts, nondef_ts, core_t) =
  let
    val _ = print_g ("****** Monotonicity analysis: " ^
                     string_for_mtype MAlpha ^ " is " ^
                     Syntax.string_of_typ ctxt alpha_T)
    val mdata as {max_fresh, constr_cache, ...} =
      initial_mdata hol_ctxt binarize alpha_T
    val (gamma as {frees, consts, ...}, cset) =
      (initial_gamma, slack)
      |> fold (consider_definitional_axiom mdata) def_ts
      |> fold (consider_nondefinitional_axiom mdata Plus) nondef_ts
      |> consider_general_formula mdata Plus core_t
  in
    case solve (!max_fresh) cset of
      SOME lits => (print_mtype_context ctxt lits gamma; true)
    | _ => false
  end
  handle MTYPE (loc, Ms) => raise BAD (loc, commas (map string_for_mtype Ms))

end;
