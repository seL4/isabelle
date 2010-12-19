(*  Title:      HOL/Tools/SMT/smtlib_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to SMT solvers based on the SMT-LIB format.
*)

signature SMTLIB_INTERFACE =
sig
  val smtlibC: SMT_Utils.class
  val add_logic: int * (term list -> string option) -> Context.generic ->
    Context.generic
  val translate_config: Proof.context -> SMT_Translate.config
  val setup: theory -> theory
end

structure SMTLIB_Interface: SMTLIB_INTERFACE =
struct

structure U = SMT_Utils
structure B = SMT_Builtin
structure N = SMT_Normalize
structure T = SMT_Translate

val smtlibC = ["smtlib"]


(* builtins *)

local
  fun int_num _ i = SOME (string_of_int i)

  fun is_linear [t] = U.is_number t
    | is_linear [t, u] = U.is_number t orelse U.is_number u
    | is_linear _ = false

  fun times _ T ts = if is_linear ts then SOME ((("*", 2), T), ts, T) else NONE

  fun distinct _ (Type (_, [Type (_, [T]), _])) [t] =
        (case try HOLogic.dest_list t of
          SOME (ts as _ :: _) =>
            let
              fun mkT U = replicate (length ts) U ---> @{typ bool}
              val U = mkT T and U' = mkT (TVar (("'a", 0), @{sort type}))
            in SOME ((("distinct", length ts), U), ts, U') end
        | _ => NONE)
    | distinct _ _ _ = NONE
in

val setup_builtins =
  B.add_builtin_typ smtlibC (@{typ int}, K (SOME "Int"), int_num) #>
  fold (B.add_builtin_fun' smtlibC) [
    (@{const True}, "true"),
    (@{const False}, "false"),
    (@{const Not}, "not"),
    (@{const HOL.conj}, "and"),
    (@{const HOL.disj}, "or"),
    (@{const HOL.implies}, "implies"),
    (@{const HOL.eq (bool)}, "iff"),
    (@{const HOL.eq ('a)}, "="),
    (@{const If (bool)}, "if_then_else"),
    (@{const If ('a)}, "ite"),
    (@{const less (int)}, "<"),
    (@{const less_eq (int)}, "<="),
    (@{const uminus (int)}, "~"),
    (@{const plus (int)}, "+"),
    (@{const minus (int)}, "-") ] #>
  B.add_builtin_fun smtlibC (Term.dest_Const @{const times (int)}, times) #>
  B.add_builtin_fun smtlibC (Term.dest_Const @{const distinct ('a)}, distinct)

end


(* serialization *)

(** header **)

fun fst_int_ord ((i1, _), (i2, _)) = int_ord (i1, i2)

structure Logics = Generic_Data
(
  type T = (int * (term list -> string option)) list
  val empty = []
  val extend = I
  fun merge (bs1, bs2) = Ord_List.union fst_int_ord bs2 bs1
)

fun add_logic pf = Logics.map (Ord_List.insert fst_int_ord pf)

fun choose_logic ctxt ts =
  let
    fun choose [] = "AUFLIA"
      | choose ((_, f) :: fs) = (case f ts of SOME s => s | NONE => choose fs)
  in [":logic " ^ choose (Logics.get (Context.Proof ctxt))] end


(** serialization **)

val add = Buffer.add
fun sep f = add " " #> f
fun enclose l r f = sep (add l #> f #> add r)
val par = enclose "(" ")"
fun app n f = (fn [] => sep (add n) | xs => par (add n #> fold f xs))
fun line f = f #> add "\n"

fun var i = add "?v" #> add (string_of_int i)

fun sterm l (T.SVar i) = sep (var (l - i - 1))
  | sterm l (T.SApp (n, ts)) = app n (sterm l) ts
  | sterm _ (T.SLet _) = raise Fail "SMT-LIB: unsupported let expression"
  | sterm l (T.SQua (q, ss, ps, w, t)) =
      let
        val quant = add o (fn T.SForall => "forall" | T.SExists => "exists")
        val vs = map_index (apfst (Integer.add l)) ss
        fun var_decl (i, s) = par (var i #> sep (add s))
        val sub = sterm (l + length ss)
        fun pat kind ts = sep (add kind #> enclose "{" " }" (fold sub ts))
        fun pats (T.SPat ts) = pat ":pat" ts
          | pats (T.SNoPat ts) = pat ":nopat" ts
        fun weight NONE = I
          | weight (SOME i) =
              sep (add ":weight { " #> add (string_of_int i) #> add " }")
      in
        par (quant q #> fold var_decl vs #> sub t #> fold pats ps #> weight w)
      end

fun ssort sorts = sort fast_string_ord sorts
fun fsort funcs = sort (prod_ord fast_string_ord (K EQUAL)) funcs

fun sdatatypes decls =
  let
    fun con (n, []) = add n
      | con (n, sels) = par (add n #>
          fold (fn (n, s) => sep (par (add n #> sep (add s)))) sels)
    fun dtyp (n, decl) = add n #> fold (sep o con) decl
  in line (add ":datatypes " #> par (fold (par o dtyp) decls)) end

fun serialize comments {header, sorts, dtyps, funcs} ts =
  Buffer.empty
  |> line (add "(benchmark Isabelle")
  |> line (add ":status unknown")
  |> fold (line o add) header
  |> length sorts > 0 ?
       line (add ":extrasorts" #> par (fold (sep o add) (ssort sorts)))
  |> fold sdatatypes dtyps
  |> length funcs > 0 ? (
       line (add ":extrafuns" #> add " (") #>
       fold (fn (f, (ss, s)) =>
         line (sep (app f (sep o add) (ss @ [s])))) (fsort funcs) #>
       line (add ")"))
  |> fold (fn t => line (add ":assumption" #> sterm 0 t)) ts
  |> line (add ":formula true)")
  |> fold (fn str => line (add "; " #> add str)) comments
  |> Buffer.content


(* interface *)

fun translate_config ctxt = {
  prefixes = {
    sort_prefix = "S",
    func_prefix = "f"},
  header = choose_logic ctxt,
  is_fol = true,
  has_datatypes = false,
  serialize = serialize}

val setup = Context.theory_map (
  setup_builtins #>
  T.add_config (smtlibC, translate_config))

end
