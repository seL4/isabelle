(*  Title:      HOL/Tools/SMT/smtlib_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to SMT solvers based on the SMT-LIB format.
*)

signature SMTLIB_INTERFACE =
sig
  val smtlibC: SMT_Config.class
  val add_logic: int * (term list -> string option) -> Context.generic ->
    Context.generic
  val interface: SMT_Solver.interface
  val setup: theory -> theory
end

structure SMTLIB_Interface: SMTLIB_INTERFACE =
struct

structure B = SMT_Builtin
structure N = SMT_Normalize
structure T = SMT_Translate

val smtlibC = ["smtlib"]



(* facts about uninterpreted constants *)

infix 2 ??
fun (ex ?? f) irules = irules |> exists (ex o Thm.prop_of o snd) irules ? f


(** pairs **)

val pair_rules = [@{thm fst_conv}, @{thm snd_conv}, @{thm pair_collapse}]

val pair_type = (fn Type (@{type_name Product_Type.prod}, _) => true | _ => false)
val exists_pair_type = Term.exists_type (Term.exists_subtype pair_type)

val add_pair_rules = exists_pair_type ?? append (map (pair ~1) pair_rules)


(** function update **)

val fun_upd_rules = [@{thm fun_upd_same}, @{thm fun_upd_apply}]

val is_fun_upd = (fn Const (@{const_name fun_upd}, _) => true | _ => false)
val exists_fun_upd = Term.exists_subterm is_fun_upd

val add_fun_upd_rules = exists_fun_upd ?? append (map (pair ~1) fun_upd_rules)


(** abs/min/max **)

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


(** include additional facts **)

fun extra_norm has_datatypes irules ctxt =
  irules
  |> not has_datatypes ? add_pair_rules
  |> add_fun_upd_rules
  |> map (apsnd (unfold_abs_min_max_defs ctxt))
  |> rpair ctxt



(* builtins *)

local
  fun int_num _ i = SOME (string_of_int i)

  fun distinct _ _ [t] =
        (case try HOLogic.dest_list t of
          SOME (ts as _ :: _) => SOME ("distinct", ts)
        | _ => NONE)
    | distinct _ _ _ = NONE
in

val setup_builtins =
  B.add_builtin_typ smtlibC (@{typ int}, K (SOME "Int"), int_num) #>
  fold (B.add_builtin_fun' smtlibC) [
    (@{const True}, "true"),
    (@{const False}, "false"),
 (* FIXME: we do not test if these constants are fully applied! *)
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
    (@{const minus (int)}, "-"),
    (@{const times (int)}, "*") ] #>
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

val interface = {
  class = smtlibC,
  extra_norm = extra_norm,
  translate = {
    prefixes = {
      sort_prefix = "S",
      func_prefix = "f"},
    header = choose_logic,
    is_fol = true,
    has_datatypes = false,
    serialize = serialize}}

val setup = Context.theory_map setup_builtins

end
