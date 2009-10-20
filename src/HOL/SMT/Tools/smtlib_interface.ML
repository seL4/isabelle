(*  Title:      HOL/SMT/Tools/smtlib_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to SMT solvers based on the SMT-LIB format.
*)

signature SMTLIB_INTERFACE =
sig
  val basic_builtins: SMT_Translate.builtins
  val default_attributes: string list
  val gen_interface: SMT_Translate.builtins -> string list ->
    SMT_Solver.interface
  val interface: SMT_Solver.interface
end

structure SMTLIB_Interface: SMTLIB_INTERFACE =
struct

structure T = SMT_Translate


(* built-in types, functions and predicates *)

val builtin_typ = (fn
    @{typ int} => SOME "Int"
  | @{typ real} => SOME "Real"
  | _ => NONE)

val builtin_num = (fn
    (i, @{typ int}) => SOME (string_of_int i)
  | (i, @{typ real}) => SOME (string_of_int i ^ ".0")
  | _ => NONE)

val builtin_funcs = T.builtin_make [
  (@{term If}, "ite"),
  (@{term "uminus :: int => _"}, "~"),
  (@{term "plus :: int => _"}, "+"),
  (@{term "minus :: int => _"}, "-"),
  (@{term "times :: int => _"}, "*"),
  (@{term "uminus :: real => _"}, "~"),
  (@{term "plus :: real => _"}, "+"),
  (@{term "minus :: real => _"}, "-"),
  (@{term "times :: real => _"}, "*") ]

val builtin_preds = T.builtin_make [
  (@{term True}, "true"),
  (@{term False}, "false"),
  (@{term Not}, "not"),
  (@{term "op &"}, "and"),
  (@{term "op |"}, "or"),
  (@{term "op -->"}, "implies"),
  (@{term "op iff"}, "iff"),
  (@{term If}, "if_then_else"),
  (@{term distinct}, "distinct"),
  (@{term "op ="}, "="),
  (@{term "op < :: int => _"}, "<"),
  (@{term "op <= :: int => _"}, "<="),
  (@{term "op < :: real => _"}, "<"),
  (@{term "op <= :: real => _"}, "<=") ]


(* serialization *)

fun wr s stream = (TextIO.output (stream, s); stream)
fun wr_line f = f #> wr "\n"

fun sep f = wr " " #> f
fun par f = sep (wr "(" #> f #> wr ")")

fun wr1 s = sep (wr s)
fun wrn f n = (fn [] => wr1 n | ts => par (wr n #> fold f ts))
fun ins s f = (fn [] => I | x::xs => f x #> fold (fn x => wr1 s #> f x) xs)

val term_marker = "__term"
val formula_marker = "__form"
fun dest_marker (T.SApp ("__term", [t])) = SOME (true, t)
  | dest_marker (T.SApp ("__form", [t])) = SOME (false, t)
  | dest_marker _ = NONE

val tvar = prefix "?"
val fvar = prefix "$"

fun wr_expr loc env t =
  (case t of
    T.SVar i => wr1 (nth env i)
  | T.SApp (n, ts) =>
      (case dest_marker t of
        SOME (loc', t') => wr_expr loc' env t'
      | NONE => wrn (wr_expr loc env) n ts)
  | T.SLet ((v, _), t1, t2) =>
      if loc then raise TERM ("SMTLIB: let expression in term", [])
      else
        let
          val (loc', t1') = the (dest_marker t1)
          val (kind, v') = if loc' then ("let", tvar v)  else ("flet", fvar v)
        in
          par (wr kind #> par (wr v' #> wr_expr loc' env t1') #>
            wr_expr loc (v' :: env) t2)
        end
  | T.SQuant (q, vs, ps, b) =>
      let
        val wr_quant = wr o (fn T.SForall => "forall" | T.SExists => "exists")
        fun wr_var (n, s) = par (wr (tvar n) #> wr1 s)

        val wre = wr_expr loc (map (tvar o fst) (rev vs) @ env)

        fun wrp s ts = wr1 (":" ^ s ^ "{") #> ins "," wre ts #> wr1 "}"
        fun wr_pat (T.SPat ts) = wrp "pat" ts
          | wr_pat (T.SNoPat ts) = wrp "nopat" ts
      in par (wr_quant q #> fold wr_var vs #> wre b #> fold wr_pat ps) end)

fun serialize attributes ({typs, funs, preds} : T.sign) ts stream =
  let
    fun wr_decl (n, Ts) = wr_line (sep (par (wr n #> fold wr1 Ts)))
  in
    stream
    |> wr_line (wr "(benchmark Isabelle")
    |> fold (wr_line o wr) attributes
    |> length typs > 0 ?
         wr_line (wr ":extrasorts" #> par (fold wr1 typs))
    |> length funs > 0 ? (
         wr_line (wr ":extrafuns (") #>
         fold (wr_decl o apsnd (fn (Ts, T) => Ts @ [T])) funs #>
         wr_line (wr " )"))
    |> length preds > 0 ? (
         wr_line (wr ":extrapreds (") #>
         fold wr_decl preds #>
         wr_line (wr " )"))
    |> fold (fn t => wr ":assumption" #> wr_line (wr_expr false [] t)) ts
    |> wr_line (wr ":formula true")
    |> wr_line (wr ")")
    |> K ()
  end


(* SMT solver interface using the SMT-LIB input format *)

val basic_builtins = {
  builtin_typ = builtin_typ,
  builtin_num = builtin_num,
  builtin_fun = (fn true => builtin_funcs | false => builtin_preds) }

val default_attributes = [":logic AUFLIRA", ":status unknown"]

fun gen_interface builtins attributes = {
  normalize = [
    SMT_Normalize.RewriteTrivialLets,
    SMT_Normalize.RewriteNegativeNumerals,
    SMT_Normalize.RewriteNaturalNumbers,
    SMT_Normalize.AddAbsMinMaxRules,
    SMT_Normalize.AddPairRules,
    SMT_Normalize.AddFunUpdRules ],
  translate = {
    strict = true,
    prefixes = {
      var_prefix = "x",
      typ_prefix = "T",
      fun_prefix = "uf_",
      pred_prefix = "up_" },
    markers = {
      term_marker = term_marker,
      formula_marker = formula_marker },
    builtins = builtins,
    serialize = serialize attributes }}

val interface = gen_interface basic_builtins default_attributes

end
