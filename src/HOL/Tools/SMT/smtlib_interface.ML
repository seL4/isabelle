(*  Title:      HOL/Tools/SMT/smtlib_interface.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Interface to SMT solvers based on the SMT-LIB 2 format.
*)

signature SMTLIB_INTERFACE =
sig
  val smtlibC: SMT_Util.class
  val hosmtlibC: SMT_Util.class
  val add_logic: int * (term list -> string option) -> Context.generic -> Context.generic
  val translate_config: SMT_Util.order -> Proof.context -> SMT_Translate.config
  val assert_name_of_index: int -> string
  val assert_index_of_name: string -> int
  val assert_prefix : string
end;

structure SMTLIB_Interface: SMTLIB_INTERFACE =
struct

val hoC = ["ho"]

val smtlibC = ["smtlib"]   (* SMT-LIB 2 *)
val hosmtlibC = smtlibC @ hoC   (* possibly SMT-LIB 3 *)


(* builtins *)

local
  fun int_num _ i = SOME (string_of_int i)

  fun is_linear [t] = SMT_Util.is_number t
    | is_linear [t, u] = SMT_Util.is_number t orelse SMT_Util.is_number u
    | is_linear _ = false

  fun times _ _ ts =
    let val mk = Term.list_comb o pair \<^Const>\<open>times \<^Type>\<open>int\<close>\<close>
    in if is_linear ts then SOME ("*", 2, ts, mk) else NONE end
in

val setup_builtins =
  SMT_Builtin.add_builtin_typ hosmtlibC
    (\<^typ>\<open>'a => 'b\<close>, fn Type (\<^type_name>\<open>fun\<close>, Ts) => SOME ("->", Ts), K (K NONE)) #>
  fold (SMT_Builtin.add_builtin_typ smtlibC) [
    (\<^typ>\<open>bool\<close>, K (SOME ("Bool", [])), K (K NONE)),
    (\<^typ>\<open>int\<close>, K (SOME ("Int", [])), int_num)] #>
  fold (SMT_Builtin.add_builtin_fun' smtlibC) [
    (\<^Const>\<open>True\<close>, "true"),
    (\<^Const>\<open>False\<close>, "false"),
    (\<^Const>\<open>Not\<close>, "not"),
    (\<^Const>\<open>conj\<close>, "and"),
    (\<^Const>\<open>disj\<close>, "or"),
    (\<^Const>\<open>implies\<close>, "=>"),
    (\<^Const>\<open>HOL.eq \<^typ>\<open>'a\<close>\<close>, "="),
    (\<^Const>\<open>If \<^typ>\<open>'a\<close>\<close>, "ite"),
    (\<^Const>\<open>less \<^Type>\<open>int\<close>\<close>, "<"),
    (\<^Const>\<open>less_eq \<^Type>\<open>int\<close>\<close>, "<="),
    (\<^Const>\<open>uminus \<^Type>\<open>int\<close>\<close>, "-"),
    (\<^Const>\<open>plus \<^Type>\<open>int\<close>\<close>, "+"),
    (\<^Const>\<open>minus \<^Type>\<open>int\<close>\<close>, "-")] #>
  SMT_Builtin.add_builtin_fun smtlibC
    (Term.dest_Const \<^Const>\<open>times \<^Type>\<open>int\<close>\<close>, times)

end


(* serialization *)

(** logic **)

fun fst_int_ord ((i1, _), (i2, _)) = int_ord (i1, i2)

structure Logics = Generic_Data
(
  type T = (int * (term list -> string option)) list
  val empty = []
  val extend = I
  fun merge data = Ord_List.merge fst_int_ord data
)

fun add_logic pf = Logics.map (Ord_List.insert fst_int_ord pf)

fun choose_logic ctxt ts =
  let
    fun choose [] = "AUFLIA"
      | choose ((_, f) :: fs) = (case f ts of SOME s => s | NONE => choose fs)
  in
    (case choose (Logics.get (Context.Proof ctxt)) of
      "" => "" (* for default Z3 logic, a subset of everything *)
    | logic => "(set-logic " ^ logic ^ ")\n")
  end


(** serialization **)

fun var i = "?v" ^ string_of_int i

fun tree_of_sterm l (SMT_Translate.SVar (i, [])) = SMTLIB.Sym (var (l - i - 1))
  | tree_of_sterm l (SMT_Translate.SVar (i, ts)) =
      SMTLIB.S (SMTLIB.Sym (var (l - i - 1)) :: map (tree_of_sterm l) ts)
  | tree_of_sterm _ (SMT_Translate.SConst (n, [])) = SMTLIB.Sym n
  | tree_of_sterm l (SMT_Translate.SConst (n, ts)) =
      SMTLIB.S (SMTLIB.Sym n :: map (tree_of_sterm l) ts)
  | tree_of_sterm l (SMT_Translate.SQua (q, ss, pats, t)) =
      let
        val l' = l + length ss

        fun quant_name SMT_Translate.SForall = "forall"
          | quant_name SMT_Translate.SExists = "exists"

        fun gen_trees_of_pat keyword ps =
          [SMTLIB.Key keyword, SMTLIB.S (map (tree_of_sterm l') ps)]
        fun trees_of_pat (SMT_Translate.SPat ps) = gen_trees_of_pat "pattern" ps
          | trees_of_pat (SMT_Translate.SNoPat ps) = gen_trees_of_pat "no-pattern" ps
        fun tree_of_pats [] t = t
          | tree_of_pats pats t = SMTLIB.S (SMTLIB.Sym "!" :: t :: maps trees_of_pat pats)

        val vs = map_index (fn (i, ty) =>
          SMTLIB.S [SMTLIB.Sym (var (l + i)), SMTLIB.Sym ty]) ss

        val body = t
          |> tree_of_sterm l'
          |> tree_of_pats pats
      in
        SMTLIB.S [SMTLIB.Sym (quant_name q), SMTLIB.S vs, body]
      end


fun sctrarg (sel, typ) = "(" ^ sel ^ " " ^ typ ^ ")"
fun sctr (name, args) = enclose "(" ")" (space_implode " " (name :: map sctrarg args))
fun sdatatype (name, ctrs) = enclose "(" ")" (space_implode " " (name :: map sctr ctrs))

fun string_of_fun (f, (ss, s)) = f ^ " (" ^ space_implode " " ss ^ ") " ^ s

fun named_sterm s t = SMTLIB.S [SMTLIB.Sym "!", t, SMTLIB.Key "named", SMTLIB.Sym s]

val assert_prefix = "a"

fun assert_name_of_index i = assert_prefix ^ string_of_int i
fun assert_index_of_name s = the_default ~1 (Int.fromString (unprefix assert_prefix s))

fun sdtyp (fp, dtyps) =
  Buffer.add (enclose ("(declare-" ^ BNF_FP_Util.co_prefix fp ^ "datatypes () (") "))\n"
    (space_implode "\n  " (map sdatatype dtyps)))

fun serialize smt_options comments {logic, sorts, dtyps, funcs} ts =
  let
    val unsat_core = member (op =) smt_options (":produce-unsat-cores", "true")
  in
    Buffer.empty
    |> fold (Buffer.add o enclose "; " "\n") comments
    |> fold (fn (k, v) => Buffer.add ("(set-option " ^ k ^ " " ^ v ^ ")\n")) smt_options
    |> Buffer.add logic
    |> fold (Buffer.add o enclose "(declare-sort " " 0)\n") (sort fast_string_ord sorts)
    |> fold sdtyp (AList.coalesce (op =) dtyps)
    |> fold (Buffer.add o enclose "(declare-fun " ")\n" o string_of_fun)
        (sort (fast_string_ord o apply2 fst) funcs)
    |> fold (fn (i, t) => Buffer.add (enclose "(assert " ")\n"
        (SMTLIB.str_of (named_sterm (assert_name_of_index i) (tree_of_sterm 0 t))))) (map_index I ts)
    |> Buffer.add "(check-sat)\n"
    |> Buffer.add (if unsat_core then "(get-unsat-core)\n" else "(get-proof)\n")
    |> Buffer.content
  end

(* interface *)

fun translate_config order ctxt = {
  order = order,
  logic = choose_logic ctxt,
  fp_kinds = [],
  serialize = serialize}

val _ = Theory.setup (Context.theory_map
  (setup_builtins #>
   SMT_Translate.add_config (smtlibC, translate_config SMT_Util.First_Order) #>
   SMT_Translate.add_config (hosmtlibC, translate_config SMT_Util.Higher_Order)))

end;
