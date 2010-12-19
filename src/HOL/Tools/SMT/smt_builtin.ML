(*  Title:      HOL/Tools/SMT/smt_builtin.ML
    Author:     Sascha Boehme, TU Muenchen

Tables of types and terms directly supported by SMT solvers.
*)

signature SMT_BUILTIN =
sig
  (*built-in types*)
  val add_builtin_typ: SMT_Utils.class ->
    typ * (typ -> string option) * (typ -> int -> string option) ->
    Context.generic -> Context.generic
  val add_builtin_typ_ext: typ * (typ -> bool) -> Context.generic ->
    Context.generic
  val builtin_typ: Proof.context -> typ -> string option
  val is_builtin_typ: Proof.context -> typ -> bool
  val is_builtin_typ_ext: Proof.context -> typ -> bool

  (*built-in numbers*)
  val builtin_num: Proof.context -> term -> (string * typ) option
  val is_builtin_num: Proof.context -> term -> bool
  val is_builtin_num_ext: Proof.context -> term -> bool

  (*built-in functions*)
  type 'a bfun = Proof.context -> typ -> term list -> 'a
  val add_builtin_fun: SMT_Utils.class ->
    (string * typ) * (((string * int) * typ) * term list * typ) option bfun ->
    Context.generic -> Context.generic
  val add_builtin_fun': SMT_Utils.class -> term * string -> Context.generic ->
    Context.generic
  val add_builtin_fun_ext: (string * typ) * bool bfun -> Context.generic ->
    Context.generic
  val add_builtin_fun_ext': string * typ -> Context.generic -> Context.generic
  val add_builtin_fun_ext'': string -> Context.generic -> Context.generic
  val builtin_fun: Proof.context -> string * typ -> term list ->
    (((string * int) * typ) * term list * typ) option
  val is_builtin_fun: Proof.context -> string * typ -> term list -> bool
  val is_builtin_fun_ext: Proof.context -> string * typ -> term list -> bool
  val is_builtin_ext: Proof.context -> string * typ -> term list -> bool
end

structure SMT_Builtin: SMT_BUILTIN =
struct

structure U = SMT_Utils
structure C = SMT_Config


(* built-in tables *)

datatype ('a, 'b) kind = Ext of 'a | Int of 'b

type ('a, 'b) ttab = ((typ * ('a, 'b) kind) Ord_List.T) U.dict 

fun typ_ord ((T, _), (U, _)) =
  let
    fun tord (TVar _, Type _) = GREATER
      | tord (Type _, TVar _) = LESS
      | tord (Type (n, Ts), Type (m, Us)) =
          if n = m then list_ord tord (Ts, Us)
          else Term_Ord.typ_ord (T, U)
      | tord TU = Term_Ord.typ_ord TU
  in tord (T, U) end

fun insert_ttab cs T f =
  U.dict_map_default (cs, [])
    (Ord_List.insert typ_ord (perhaps (try Logic.varifyT_global) T, f))

fun merge_ttab ttabp =
  U.dict_merge (uncurry (Ord_List.union typ_ord) o swap) ttabp

fun lookup_ttab ctxt ttab T =
  let fun match (U, _) = Sign.typ_instance (ProofContext.theory_of ctxt) (T, U)
  in
    get_first (find_first match) (U.dict_lookup ttab (C.solver_class_of ctxt))
  end

type ('a, 'b) btab = ('a, 'b) ttab Symtab.table

fun insert_btab cs n T f =
  Symtab.map_default (n, []) (insert_ttab cs T f)

fun merge_btab btabp = Symtab.join (K merge_ttab) btabp

fun lookup_btab ctxt btab (n, T) =
  (case Symtab.lookup btab n of
    NONE => NONE
  | SOME ttab => lookup_ttab ctxt ttab T)


(* built-in types *)

structure Builtin_Types = Generic_Data
(
  type T =
    (typ -> bool, (typ -> string option) * (typ -> int -> string option)) ttab
  val empty = []
  val extend = I
  val merge = merge_ttab
)

fun add_builtin_typ cs (T, f, g) =
  Builtin_Types.map (insert_ttab cs T (Int (f, g)))

fun add_builtin_typ_ext (T, f) =
  Builtin_Types.map (insert_ttab U.basicC T (Ext f))

fun lookup_builtin_typ ctxt =
  lookup_ttab ctxt (Builtin_Types.get (Context.Proof ctxt))

fun builtin_typ ctxt T =
  (case lookup_builtin_typ ctxt T of
    SOME (_, Int (f, _)) => f T
  | _ => NONE) 

fun is_builtin_typ ctxt T = is_some (builtin_typ ctxt T)

fun is_builtin_typ_ext ctxt T =
  (case lookup_builtin_typ ctxt T of
    SOME (_, Int (f, _)) => is_some (f T)
  | SOME (_, Ext f) => f T
  | NONE => false)


(* built-in numbers *)

fun builtin_num ctxt t =
  (case try HOLogic.dest_number t of
    NONE => NONE
  | SOME (T, i) =>
      (case lookup_builtin_typ ctxt T of
        SOME (_, Int (_, g)) => g T i |> Option.map (rpair T)
      | _ => NONE))

val is_builtin_num = is_some oo builtin_num

fun is_builtin_num_ext ctxt t =
  (case try HOLogic.dest_number t of
    NONE => false
  | SOME (T, _) => is_builtin_typ_ext ctxt T)


(* built-in functions *)

type 'a bfun = Proof.context -> typ -> term list -> 'a

structure Builtin_Funcs = Generic_Data
(
  type T =
    (bool bfun, (((string * int) * typ) * term list * typ) option bfun) btab
  val empty = Symtab.empty
  val extend = I
  val merge = merge_btab
)

fun add_builtin_fun cs ((n, T), f) =
  Builtin_Funcs.map (insert_btab cs n T (Int f))

fun add_builtin_fun' cs (t, n) =
  let
    val T = Term.fastype_of t
    fun bfun _ U ts = SOME (((n, length (Term.binder_types T)), U), ts, T)
  in add_builtin_fun cs (Term.dest_Const t, bfun) end

fun add_builtin_fun_ext ((n, T), f) =
  Builtin_Funcs.map (insert_btab U.basicC n T (Ext f))

fun add_builtin_fun_ext' c =
  add_builtin_fun_ext (c, fn _ => fn _ => fn _ => true)

fun add_builtin_fun_ext'' n context =
  let val thy = Context.theory_of context
  in add_builtin_fun_ext' (n, Sign.the_const_type thy n) context end

fun lookup_builtin_fun ctxt =
  lookup_btab ctxt (Builtin_Funcs.get (Context.Proof ctxt))

fun builtin_fun ctxt (c as (_, T)) ts =
  (case lookup_builtin_fun ctxt c of
    SOME (_, Int f) => f ctxt T ts
  | _ => NONE)

fun is_builtin_fun ctxt c ts = is_some (builtin_fun ctxt c ts)

fun is_builtin_fun_ext ctxt (c as (_, T)) ts =
  (case lookup_builtin_fun ctxt c of
    SOME (_, Int f) => is_some (f ctxt T ts)
  | SOME (_, Ext f) => f ctxt T ts
  | NONE => false)

fun is_builtin_ext ctxt c ts =
  is_builtin_num_ext ctxt (Term.list_comb (Const c, ts)) orelse 
  is_builtin_fun_ext ctxt c ts

end
