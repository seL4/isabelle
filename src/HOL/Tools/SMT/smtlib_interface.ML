(*  Title:      HOL/Tools/SMT/smtlib_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to SMT solvers based on the SMT-LIB format.
*)

signature SMTLIB_INTERFACE =
sig
  type builtins = {
    builtin_typ: typ -> string option,
    builtin_num: typ -> int -> string option,
    builtin_func: string * typ -> term list -> (string * term list) option,
    builtin_pred: string * typ -> term list -> (string * term list) option,
    is_builtin_pred: string -> typ -> bool }
  val add_builtins: builtins -> Context.generic -> Context.generic
  val add_logic: (term list -> string option) -> Context.generic ->
    Context.generic
  val interface: SMT_Solver.interface
end

structure SMTLIB_Interface: SMTLIB_INTERFACE =
struct

structure N = SMT_Normalize
structure T = SMT_Translate



(** facts about uninterpreted constants **)

infix 2 ??
fun (ex ?? f) thms = if exists (ex o Thm.prop_of) thms then f thms else thms


(* pairs *)

val pair_rules = [@{thm fst_conv}, @{thm snd_conv}, @{thm pair_collapse}]

val pair_type = (fn Type (@{type_name Product_Type.prod}, _) => true | _ => false)
val exists_pair_type = Term.exists_type (Term.exists_subtype pair_type)

val add_pair_rules = exists_pair_type ?? append pair_rules


(* function update *)

val fun_upd_rules = [@{thm fun_upd_same}, @{thm fun_upd_apply}]

val is_fun_upd = (fn Const (@{const_name fun_upd}, _) => true | _ => false)
val exists_fun_upd = Term.exists_subterm is_fun_upd

val add_fun_upd_rules = exists_fun_upd ?? append fun_upd_rules


(* abs/min/max *)

val exists_abs_min_max = Term.exists_subterm (fn
    Const (@{const_name abs}, _) => true
  | Const (@{const_name min}, _) => true
  | Const (@{const_name max}, _) => true
  | _ => false)

val unfold_abs_conv = Conv.rewr_conv (mk_meta_eq @{thm abs_if})
val unfold_min_conv = Conv.rewr_conv (mk_meta_eq @{thm min_def})
val unfold_max_conv = Conv.rewr_conv (mk_meta_eq @{thm max_def})

fun expand_conv cv = N.eta_expand_conv (K cv)
fun expand2_conv cv = N.eta_expand_conv (N.eta_expand_conv (K cv))

fun unfold_def_conv ctxt ct =
  (case Thm.term_of ct of
    Const (@{const_name abs}, _) $ _ => unfold_abs_conv
  | Const (@{const_name abs}, _) => expand_conv unfold_abs_conv ctxt
  | Const (@{const_name min}, _) $ _ $ _ => unfold_min_conv
  | Const (@{const_name min}, _) $ _ => expand_conv unfold_min_conv ctxt
  | Const (@{const_name min}, _) => expand2_conv unfold_min_conv ctxt
  | Const (@{const_name max}, _) $ _ $ _ => unfold_max_conv
  | Const (@{const_name max}, _) $ _ => expand_conv unfold_max_conv ctxt
  | Const (@{const_name max}, _) => expand2_conv unfold_max_conv ctxt
  | _ => Conv.all_conv) ct

fun unfold_abs_min_max_defs ctxt thm =
  if exists_abs_min_max (Thm.prop_of thm)
  then Conv.fconv_rule (Conv.top_conv unfold_def_conv ctxt) thm
  else thm


(* include additional facts *)

fun extra_norm thms ctxt =
  thms
  |> add_pair_rules
  |> add_fun_upd_rules
  |> map (unfold_abs_min_max_defs ctxt)
  |> rpair ctxt



(** builtins **)

(* additional builtins *)

type builtins = {
  builtin_typ: typ -> string option,
  builtin_num: typ -> int -> string option,
  builtin_func: string * typ -> term list -> (string * term list) option,
  builtin_pred: string * typ -> term list -> (string * term list) option,
  is_builtin_pred: string -> typ -> bool }

fun chained _ [] = NONE
  | chained f (b :: bs) = (case f b of SOME y => SOME y | NONE => chained f bs)

fun chained' _ [] = false
  | chained' f (b :: bs) = f b orelse chained' f bs

fun chained_builtin_typ bs T =
  chained (fn {builtin_typ, ...} : builtins => builtin_typ T) bs

fun chained_builtin_num bs T i =
  chained (fn {builtin_num, ...} : builtins => builtin_num T i) bs

fun chained_builtin_func bs c ts =
  chained (fn {builtin_func, ...} : builtins => builtin_func c ts) bs

fun chained_builtin_pred bs c ts =
  chained (fn {builtin_pred, ...} : builtins => builtin_pred c ts) bs

fun chained_is_builtin_pred bs n T =
  chained' (fn {is_builtin_pred, ...} : builtins => is_builtin_pred n T) bs

fun fst_int_ord ((s1, _), (s2, _)) = int_ord (s1, s2)

structure Builtins = Generic_Data
(
  type T = (int * builtins) list
  val empty = []
  val extend = I
  fun merge (bs1, bs2) = OrdList.union fst_int_ord bs2 bs1
)

fun add_builtins bs = Builtins.map (OrdList.insert fst_int_ord (serial (), bs))

fun get_builtins ctxt = map snd (Builtins.get (Context.Proof ctxt))


(* basic builtins combined with additional builtins *)

fun builtin_typ _ @{typ int} = SOME "Int"
  | builtin_typ ctxt T = chained_builtin_typ (get_builtins ctxt) T

fun builtin_num _ @{typ int} i = SOME (string_of_int i)
  | builtin_num ctxt T i = chained_builtin_num (get_builtins ctxt) T i

fun if_int_type T n =
  (case try Term.domain_type T of
    SOME @{typ int} => SOME n
  | _ => NONE)

fun conn @{const_name True} = SOME "true"
  | conn @{const_name False} = SOME "false"
  | conn @{const_name Not} = SOME "not"
  | conn @{const_name HOL.conj} = SOME "and"
  | conn @{const_name HOL.disj} = SOME "or"
  | conn @{const_name HOL.implies} = SOME "implies"
  | conn @{const_name HOL.eq} = SOME "iff"
  | conn @{const_name If} = SOME "if_then_else"
  | conn _ = NONE

fun pred @{const_name distinct} _ = SOME "distinct"
  | pred @{const_name HOL.eq} _ = SOME "="
  | pred @{const_name term_eq} _ = SOME "="
  | pred @{const_name less} T = if_int_type T "<"
  | pred @{const_name less_eq} T = if_int_type T "<="
  | pred _ _ = NONE

fun func @{const_name If} _ = SOME "ite"
  | func @{const_name uminus} T = if_int_type T "~"
  | func @{const_name plus} T = if_int_type T "+"
  | func @{const_name minus} T = if_int_type T "-"
  | func @{const_name times} T = if_int_type T "*"
  | func _ _ = NONE

val is_propT = (fn @{typ prop} => true | _ => false)
fun is_connT T = Term.strip_type T |> (fn (Us, U) => forall is_propT (U :: Us))
fun is_predT T = is_propT (Term.body_type T)

fun is_builtin_conn (n, T) = is_connT T andalso is_some (conn n)
fun is_builtin_pred ctxt (n, T) = is_predT T andalso
  (is_some (pred n T) orelse chained_is_builtin_pred (get_builtins ctxt) n T)

fun builtin_fun ctxt (c as (n, T)) ts =
  let
    val builtin_func' = chained_builtin_func (get_builtins ctxt)
    val builtin_pred' = chained_builtin_pred (get_builtins ctxt)
  in
    if is_connT T then conn n |> Option.map (rpair ts)
    else if is_predT T then
      (case pred n T of SOME c' => SOME (c', ts) | NONE => builtin_pred' c ts)
    else 
      (case func n T of SOME c' => SOME (c', ts) | NONE => builtin_func' c ts)
  end



(** serialization **)

(* header *)

structure Logics = Generic_Data
(
  type T = (int * (term list -> string option)) list
  val empty = []
  val extend = I
  fun merge (bs1, bs2) = OrdList.union fst_int_ord bs2 bs1
)

fun add_logic l = Logics.map (OrdList.insert fst_int_ord (serial (), l))

fun choose_logic ctxt ts =
  let
    fun choose [] = "AUFLIA"
      | choose ((_, l) :: ls) = (case l ts of SOME s => s | NONE => choose ls)
  in [":logic " ^ choose (rev (Logics.get (Context.Proof ctxt)))] end


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

fun ssort sorts = sort fast_string_ord sorts
fun fsort funcs = sort (prod_ord fast_string_ord (K EQUAL)) funcs

fun serialize comments {header, sorts, funcs} ts =
  Buffer.empty
  |> line (add "(benchmark Isabelle")
  |> line (add ":status unknown")
  |> fold (line o add) header
  |> length sorts > 0 ?
       line (add ":extrasorts" #> par (fold (sep o add) (ssort sorts)))
  |> length funcs > 0 ? (
       line (add ":extrafuns" #> add " (") #>
       fold (fn (f, (ss, s)) =>
         line (sep (app f (sep o add) (ss @ [s])))) (fsort funcs) #>
       line (add ")"))
  |> fold (fn t => line (add ":assumption" #> sterm 0 t)) ts
  |> line (add ":formula true)")
  |> fold (fn str => line (add "; " #> add str)) comments
  |> Buffer.content



(** interfaces **)

val interface = {
  extra_norm = extra_norm,
  translate = {
    prefixes = {
      sort_prefix = "S",
      func_prefix = "f"},
    header = choose_logic,
    strict = SOME {
      is_builtin_conn = is_builtin_conn,
      is_builtin_pred = is_builtin_pred,
      is_builtin_distinct = true},
    builtins = {
      builtin_typ = builtin_typ,
      builtin_num = builtin_num,
      builtin_fun = builtin_fun},
    serialize = serialize}}

end
