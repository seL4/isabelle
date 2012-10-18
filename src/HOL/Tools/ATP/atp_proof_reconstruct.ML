(*  Title:      HOL/Tools/ATP/atp_proof_reconstruct.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Basic proof reconstruction from ATP proofs.
*)

signature ATP_PROOF_RECONSTRUCT =
sig
  type ('a, 'b) ho_term = ('a, 'b) ATP_Problem.ho_term
  type ('a, 'b, 'c, 'd) formula = ('a, 'b, 'c, 'd) ATP_Problem.formula

  val metisN : string
  val full_typesN : string
  val partial_typesN : string
  val no_typesN : string
  val really_full_type_enc : string
  val full_type_enc : string
  val partial_type_enc : string
  val no_type_enc : string
  val full_type_encs : string list
  val partial_type_encs : string list
  val metis_default_lam_trans : string
  val metis_call : string -> string -> string
  val unalias_type_enc : string -> string list
  val forall_of : term -> term -> term
  val term_from_atp :
    Proof.context -> bool -> int Symtab.table -> typ option ->
    (string, string) ho_term -> term
  val prop_from_atp :
    Proof.context -> bool -> int Symtab.table ->
    (string, string, (string, string) ho_term, string) formula -> term
end;

structure ATP_Proof_Reconstruct : ATP_PROOF_RECONSTRUCT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate

val metisN = "metis"

val full_typesN = "full_types"
val partial_typesN = "partial_types"
val no_typesN = "no_types"

val really_full_type_enc = "mono_tags"
val full_type_enc = "poly_guards_query"
val partial_type_enc = "poly_args"
val no_type_enc = "erased"

val full_type_encs = [full_type_enc, really_full_type_enc]
val partial_type_encs = partial_type_enc :: full_type_encs

val type_enc_aliases =
  [(full_typesN, full_type_encs),
   (partial_typesN, partial_type_encs),
   (no_typesN, [no_type_enc])]

fun unalias_type_enc s =
  AList.lookup (op =) type_enc_aliases s |> the_default [s]

val metis_default_lam_trans = combsN

fun metis_call type_enc lam_trans =
  let
    val type_enc =
      case AList.find (fn (enc, encs) => enc = hd encs) type_enc_aliases
                      type_enc of
        [alias] => alias
      | _ => type_enc
    val opts = [] |> type_enc <> partial_typesN ? cons type_enc
                  |> lam_trans <> metis_default_lam_trans ? cons lam_trans
  in metisN ^ (if null opts then "" else " (" ^ commas opts ^ ")") end

fun forall_of v t = HOLogic.all_const (fastype_of v) $ lambda v t
fun exists_of v t = HOLogic.exists_const (fastype_of v) $ lambda v t

fun make_tfree ctxt w =
  let val ww = "'" ^ w in
    TFree (ww, the_default HOLogic.typeS (Variable.def_sort ctxt (ww, ~1)))
  end

exception HO_TERM of (string, string) ho_term list
exception FORMULA of
    (string, string, (string, string) ho_term, string) formula list
exception SAME of unit

(* Type variables are given the basic sort "HOL.type". Some will later be
   constrained by information from type literals, or by type inference. *)
fun typ_from_atp ctxt (u as ATerm ((a, _), us)) =
  let val Ts = map (typ_from_atp ctxt) us in
    case unprefix_and_unascii type_const_prefix a of
      SOME b => Type (invert_const b, Ts)
    | NONE =>
      if not (null us) then
        raise HO_TERM [u]  (* only "tconst"s have type arguments *)
      else case unprefix_and_unascii tfree_prefix a of
        SOME b => make_tfree ctxt b
      | NONE =>
        (* Could be an Isabelle variable or a variable from the ATP, say "X1"
           or "_5018". Sometimes variables from the ATP are indistinguishable
           from Isabelle variables, which forces us to use a type parameter in
           all cases. *)
        (a |> perhaps (unprefix_and_unascii tvar_prefix), HOLogic.typeS)
        |> Type_Infer.param 0
  end

(* Type class literal applied to a type. Returns triple of polarity, class,
   type. *)
fun type_constraint_from_term ctxt (u as ATerm ((a, _), us)) =
  case (unprefix_and_unascii class_prefix a, map (typ_from_atp ctxt) us) of
    (SOME b, [T]) => (b, T)
  | _ => raise HO_TERM [u]

(* Accumulate type constraints in a formula: negative type literals. *)
fun add_var (key, z)  = Vartab.map_default (key, []) (cons z)
fun add_type_constraint false (cl, TFree (a ,_)) = add_var ((a, ~1), cl)
  | add_type_constraint false (cl, TVar (ix, _)) = add_var (ix, cl)
  | add_type_constraint _ _ = I

fun repair_variable_name f s =
  let
    fun subscript_name s n = s ^ nat_subscript n
    val s = String.map f s
  in
    case space_explode "_" s of
      [_] => (case take_suffix Char.isDigit (String.explode s) of
                (cs1 as _ :: _, cs2 as _ :: _) =>
                subscript_name (String.implode cs1)
                               (the (Int.fromString (String.implode cs2)))
              | (_, _) => s)
    | [s1, s2] => (case Int.fromString s2 of
                     SOME n => subscript_name s1 n
                   | NONE => s)
    | _ => s
  end

(* The number of type arguments of a constant, zero if it's monomorphic. For
   (instances of) Skolem pseudoconstants, this information is encoded in the
   constant name. *)
fun num_type_args thy s =
  if String.isPrefix skolem_const_prefix s then
    s |> Long_Name.explode |> List.last |> Int.fromString |> the
  else if String.isPrefix lam_lifted_prefix s then
    if String.isPrefix lam_lifted_poly_prefix s then 2 else 0
  else
    (s, Sign.the_const_type thy s) |> Sign.const_typargs thy |> length

fun slack_fastype_of t = fastype_of t handle TERM _ => HOLogic.typeT

(* First-order translation. No types are known for variables. "HOLogic.typeT"
   should allow them to be inferred. *)
fun term_from_atp ctxt textual sym_tab =
  let
    val thy = Proof_Context.theory_of ctxt
    (* For Metis, we use 1 rather than 0 because variable references in clauses
       may otherwise conflict with variable constraints in the goal. At least,
       type inference often fails otherwise. See also "axiom_inference" in
       "Metis_Reconstruct". *)
    val var_index = if textual then 0 else 1
    fun do_term extra_ts opt_T u =
      case u of
        ATerm ((s, _), us) =>
        if String.isPrefix native_type_prefix s then
          @{const True} (* ignore TPTP type information *)
        else if s = tptp_equal then
          let val ts = map (do_term [] NONE) us in
            if textual andalso length ts = 2 andalso
              hd ts aconv List.last ts then
              (* Vampire is keen on producing these. *)
              @{const True}
            else
              list_comb (Const (@{const_name HOL.eq}, HOLogic.typeT), ts)
          end
        else case unprefix_and_unascii const_prefix s of
          SOME s' =>
          let
            val ((s', s''), mangled_us) =
              s' |> unmangled_const |>> `invert_const
          in
            if s' = type_tag_name then
              case mangled_us @ us of
                [typ_u, term_u] =>
                do_term extra_ts (SOME (typ_from_atp ctxt typ_u)) term_u
              | _ => raise HO_TERM us
            else if s' = predicator_name then
              do_term [] (SOME @{typ bool}) (hd us)
            else if s' = app_op_name then
              let val extra_t = do_term [] NONE (List.last us) in
                do_term (extra_t :: extra_ts)
                        (case opt_T of
                           SOME T => SOME (slack_fastype_of extra_t --> T)
                         | NONE => NONE)
                        (nth us (length us - 2))
              end
            else if s' = type_guard_name then
              @{const True} (* ignore type predicates *)
            else
              let
                val new_skolem = String.isPrefix new_skolem_const_prefix s''
                val num_ty_args =
                  length us - the_default 0 (Symtab.lookup sym_tab s)
                val (type_us, term_us) =
                  chop num_ty_args us |>> append mangled_us
                val term_ts = map (do_term [] NONE) term_us
                val T =
                  (if not (null type_us) andalso
                      num_type_args thy s' = length type_us then
                     let val Ts = type_us |> map (typ_from_atp ctxt) in
                       if new_skolem then
                         SOME (Type_Infer.paramify_vars (tl Ts ---> hd Ts))
                       else if textual then
                         try (Sign.const_instance thy) (s', Ts)
                       else
                         NONE
                     end
                   else
                     NONE)
                  |> (fn SOME T => T
                       | NONE => map slack_fastype_of term_ts --->
                                 (case opt_T of
                                    SOME T => T
                                  | NONE => HOLogic.typeT))
                val t =
                  if new_skolem then
                    Var ((new_skolem_var_name_from_const s'', var_index), T)
                  else
                    Const (unproxify_const s', T)
              in list_comb (t, term_ts @ extra_ts) end
          end
        | NONE => (* a free or schematic variable *)
          let
            val term_ts = map (do_term [] NONE) us
            val ts = term_ts @ extra_ts
            val T =
              case opt_T of
                SOME T => map slack_fastype_of term_ts ---> T
              | NONE => map slack_fastype_of ts ---> HOLogic.typeT
            val t =
              case unprefix_and_unascii fixed_var_prefix s of
                SOME s => Free (s, T)
              | NONE =>
                case unprefix_and_unascii schematic_var_prefix s of
                  SOME s => Var ((s, var_index), T)
                | NONE =>
                  Var ((s |> textual ? repair_variable_name Char.toLower,
                        var_index), T)
          in list_comb (t, ts) end
  in do_term [] end

fun term_from_atom ctxt textual sym_tab pos (u as ATerm ((s, _), _)) =
  if String.isPrefix class_prefix s then
    add_type_constraint pos (type_constraint_from_term ctxt u)
    #> pair @{const True}
  else
    pair (term_from_atp ctxt textual sym_tab (SOME @{typ bool}) u)

(* Update schematic type variables with detected sort constraints. It's not
   totally clear whether this code is necessary. *)
fun repair_tvar_sorts (t, tvar_tab) =
  let
    fun do_type (Type (a, Ts)) = Type (a, map do_type Ts)
      | do_type (TVar (xi, s)) =
        TVar (xi, the_default s (Vartab.lookup tvar_tab xi))
      | do_type (TFree z) = TFree z
    fun do_term (Const (a, T)) = Const (a, do_type T)
      | do_term (Free (a, T)) = Free (a, do_type T)
      | do_term (Var (xi, T)) = Var (xi, do_type T)
      | do_term (t as Bound _) = t
      | do_term (Abs (a, T, t)) = Abs (a, do_type T, do_term t)
      | do_term (t1 $ t2) = do_term t1 $ do_term t2
  in t |> not (Vartab.is_empty tvar_tab) ? do_term end

fun quantify_over_var quant_of var_s t =
  let
    val vars = [] |> Term.add_vars t |> filter (fn ((s, _), _) => s = var_s)
                  |> map Var
  in fold_rev quant_of vars t end

(* Interpret an ATP formula as a HOL term, extracting sort constraints as they
   appear in the formula. *)
fun prop_from_atp ctxt textual sym_tab phi =
  let
    fun do_formula pos phi =
      case phi of
        AQuant (_, [], phi) => do_formula pos phi
      | AQuant (q, (s, _) :: xs, phi') =>
        do_formula pos (AQuant (q, xs, phi'))
        (* FIXME: TFF *)
        #>> quantify_over_var
              (case q of AForall => forall_of | AExists => exists_of)
              (s |> textual ? repair_variable_name Char.toLower)
      | AConn (ANot, [phi']) => do_formula (not pos) phi' #>> s_not
      | AConn (c, [phi1, phi2]) =>
        do_formula (pos |> c = AImplies ? not) phi1
        ##>> do_formula pos phi2
        #>> (case c of
               AAnd => s_conj
             | AOr => s_disj
             | AImplies => s_imp
             | AIff => s_iff
             | ANot => raise Fail "impossible connective")
      | AAtom tm => term_from_atom ctxt textual sym_tab pos tm
      | _ => raise FORMULA [phi]
  in repair_tvar_sorts (do_formula true phi Vartab.empty) end

end;
