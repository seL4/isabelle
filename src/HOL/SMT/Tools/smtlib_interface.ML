(*  Title:      HOL/SMT/Tools/smtlib_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to SMT solvers based on the SMT-LIB format.
*)

signature SMTLIB_INTERFACE =
sig
  val interface: string list -> SMT_Translate.config
end

structure SMTLIB_Interface: SMTLIB_INTERFACE =
struct

structure T = SMT_Translate

fun dest_binT T =
  (case T of
    Type (@{type_name "Numeral_Type.num0"}, _) => 0
  | Type (@{type_name "Numeral_Type.num1"}, _) => 1
  | Type (@{type_name "Numeral_Type.bit0"}, [T]) => 2 * dest_binT T
  | Type (@{type_name "Numeral_Type.bit1"}, [T]) => 1 + 2 * dest_binT T
  | _ => raise TYPE ("dest_binT", [T], []))

fun dest_wordT (Type (@{type_name word}, [T])) = dest_binT T
  | dest_wordT T = raise TYPE ("dest_wordT", [T], [])



(* builtins *)

fun index1 n i = n ^ "[" ^ string_of_int i ^ "]"
fun index2 n i j = n ^ "[" ^ string_of_int i ^ ":" ^ string_of_int j ^ "]"

fun builtin_typ @{typ int} = SOME "Int"
  | builtin_typ @{typ real} = SOME "Real"
  | builtin_typ (Type (@{type_name word}, [T])) =
      Option.map (index1 "BitVec") (try dest_binT T)
  | builtin_typ _ = NONE

fun builtin_num @{typ int} i = SOME (string_of_int i)
  | builtin_num @{typ real} i = SOME (string_of_int i ^ ".0")
  | builtin_num (Type (@{type_name word}, [T])) i =
      Option.map (index1 ("bv" ^ string_of_int i)) (try dest_binT T)
  | builtin_num _ _ = NONE

val is_propT = (fn @{typ prop} => true | _ => false)
fun is_connT T = Term.strip_type T |> (fn (Us, U) => forall is_propT (U :: Us))
fun is_predT T = is_propT (Term.body_type T)

fun just c ts = SOME (c, ts)

val is_arith_type = member (op =) [@{typ int}, @{typ real}] o Term.domain_type

fun fixed_bvT (Ts, T) x =
  if forall (can dest_wordT) (T :: Ts) then SOME x else NONE

fun if_fixed_bvT' T = fixed_bvT ([], Term.domain_type T)
fun if_fixed_bvT T = curry (fixed_bvT ([], Term.domain_type T))
fun if_full_fixed_bvT T = curry (fixed_bvT (Term.strip_type T))

fun dest_word_funT (Type ("fun", [T, U])) = (dest_wordT T, dest_wordT U)
  | dest_word_funT T = raise TYPE ("dest_word_funT", [T], [])
fun dest_nat (@{term nat} $ n :: ts) = (snd (HOLogic.dest_number n), ts)
  | dest_nat ts = raise TERM ("dest_nat", ts)
fun dest_nat_word_funT (T, ts) =
  (dest_word_funT (Term.range_type T), dest_nat ts)

fun bv_extend n T ts =
  (case try dest_word_funT T of
    SOME (i, j) => if j-i >= 0 then SOME (index1 n (j-i), ts) else NONE
  | _ => NONE)

fun bv_rotate n T ts =
  try dest_nat ts
  |> Option.map (fn (i, ts') => (index1 n i, ts'))

fun bv_extract n T ts =
  try dest_nat_word_funT (T, ts)
  |> Option.map (fn ((_, i), (lb, ts')) => (index2 n (i + lb - 1) lb, ts'))


fun conn @{const_name True} = SOME "true"
  | conn @{const_name False} = SOME "false"
  | conn @{const_name Not} = SOME "not"
  | conn @{const_name "op &"} = SOME "and"
  | conn @{const_name "op |"} = SOME "or"
  | conn @{const_name "op -->"} = SOME "implies"
  | conn @{const_name "op ="} = SOME "iff"
  | conn @{const_name If} = SOME "if_then_else"
  | conn _ = NONE

fun pred @{const_name distinct} _ = SOME "distinct"
  | pred @{const_name "op ="} _ = SOME "="
  | pred @{const_name term_eq} _ = SOME "="
  | pred @{const_name less} T =
      if is_arith_type T then SOME "<"
      else if_fixed_bvT' T "bvult"
  | pred @{const_name less_eq} T =
      if is_arith_type T then SOME "<="
      else if_fixed_bvT' T "bvule"
  | pred @{const_name word_sless} T = if_fixed_bvT' T "bvslt"
  | pred @{const_name word_sle} T = if_fixed_bvT' T "bvsle"
  | pred _ _ = NONE

fun func @{const_name If} _ = just "ite"
  | func @{const_name uminus} T =
      if is_arith_type T then just "~"
      else if_fixed_bvT T "bvneg"
  | func @{const_name plus} T = 
      if is_arith_type T then just "+"
      else if_fixed_bvT T "bvadd"
  | func @{const_name minus} T =
      if is_arith_type T then just "-"
      else if_fixed_bvT T "bvsub"
  | func @{const_name times} T = 
      if is_arith_type T then just "*"
      else if_fixed_bvT T "bvmul"
  | func @{const_name bitNOT} T = if_fixed_bvT T "bvnot"
  | func @{const_name bitAND} T = if_fixed_bvT T "bvand"
  | func @{const_name bitOR} T = if_fixed_bvT T "bvor"
  | func @{const_name bitXOR} T = if_fixed_bvT T "bvxor"
  | func @{const_name div} T = if_fixed_bvT T "bvudiv"
  | func @{const_name mod} T = if_fixed_bvT T "bvurem"
  | func @{const_name sdiv} T = if_fixed_bvT T "bvsdiv"
  | func @{const_name smod} T = if_fixed_bvT T "bvsmod"
  | func @{const_name srem} T = if_fixed_bvT T "bvsrem"
  | func @{const_name word_cat} T = if_full_fixed_bvT T "concat"
  | func @{const_name bv_shl} T = if_full_fixed_bvT T "bvshl"
  | func @{const_name bv_lshr} T = if_full_fixed_bvT T "bvlshr"
  | func @{const_name bv_ashr} T = if_full_fixed_bvT T "bvashr"
  | func @{const_name slice} T = bv_extract "extract" T
  | func @{const_name ucast} T = bv_extend "zero_extend" T
  | func @{const_name scast} T = bv_extend "sign_extend" T
  | func @{const_name word_rotl} T = bv_rotate "rotate_left" T
  | func @{const_name word_rotr} T = bv_rotate "rotate_right" T
  | func _ _ = K NONE

fun is_builtin_conn (n, T) = is_connT T andalso is_some (conn n)
fun is_builtin_pred (n, T) = is_predT T andalso is_some (pred n T)

fun builtin_fun (n, T) ts =
  if is_connT T then conn n |> Option.map (rpair ts)
  else if is_predT T then pred n T |> Option.map (rpair ts)
  else func n T ts



(* serialization *)

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
  | sterm l (T.SQua (q, ss, ps, t)) =
      let
        val quant = add o (fn T.SForall => "forall" | T.SExists => "exists")
        val vs = map_index (apfst (Integer.add l)) ss
        fun var_decl (i, s) = par (var i #> sep (add s))
        val sub = sterm (l + length ss)
        fun pat kind ts = sep (add kind #> enclose "{" " }" (fold sub ts))
        fun pats (T.SPat ts) = pat ":pat" ts
          | pats (T.SNoPat ts) = pat ":nopat" ts
      in par (quant q #> fold var_decl vs #> sub t #> fold pats ps) end

fun choose_logic theories =
  if member (op =) theories T.Bitvector then "QF_AUFBV"
  else if member (op =) theories T.Real then "AUFLIRA"
  else "AUFLIA"

fun serialize comments {theories, sorts, funcs} ts =
  Buffer.empty
  |> line (add "(benchmark Isabelle")
  |> line (add ":status unknown")
  |> line (add ":logic " #> add (choose_logic theories))
  |> length sorts > 0 ?
       line (add ":extrasorts" #> par (fold (sep o add) sorts))
  |> length funcs > 0 ? (
       line (add ":extrafuns" #> add " (") #>
       fold (fn (f, (ss, s)) =>
         line (sep (app f (sep o add) (ss @ [s])))) funcs #>
       line (add ")"))
  |> fold (fn t => line (add ":assumption" #> sterm 0 t)) ts
  |> line (add ":formula true)")
  |> fold (fn str => line (add "; " #> add str)) comments
  |> Buffer.content



(* interface *)

fun interface comments = {
  prefixes = {
    sort_prefix = "S",
    func_prefix = "f"},
  strict = SOME {
    is_builtin_conn = is_builtin_conn,
    is_builtin_pred = is_builtin_pred,
    is_builtin_distinct = true},
  builtins = {
    builtin_typ = builtin_typ,
    builtin_num = builtin_num,
    builtin_fun = builtin_fun},
  serialize = serialize comments}

end
