(*  Title:      HOL/Tools/SMT2/smtlib2_interface.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Interface to SMT solvers based on the SMT-LIB 2 format.
*)

signature SMTLIB2_INTERFACE =
sig
  val smtlib2C: SMT2_Util.class
  val add_logic: int * (term list -> string option) -> Context.generic -> Context.generic
  val translate_config: Proof.context -> SMT2_Translate.config
  val assert_index_of_name: string -> int
end

structure SMTLIB2_Interface: SMTLIB2_INTERFACE =
struct

val smtlib2C = ["smtlib2"]


(* builtins *)

local
  fun int_num _ i = SOME (string_of_int i)

  fun is_linear [t] = SMT2_Util.is_number t
    | is_linear [t, u] = SMT2_Util.is_number t orelse SMT2_Util.is_number u
    | is_linear _ = false

  fun times _ _ ts =
    let val mk = Term.list_comb o pair @{const times (int)}
    in if is_linear ts then SOME ("*", 2, ts, mk) else NONE end
in

val setup_builtins =
  fold (SMT2_Builtin.add_builtin_typ smtlib2C) [
    (@{typ bool}, K (SOME "Bool"), K (K NONE)),
    (@{typ int}, K (SOME "Int"), int_num)] #>
  fold (SMT2_Builtin.add_builtin_fun' smtlib2C) [
    (@{const True}, "true"),
    (@{const False}, "false"),
    (@{const Not}, "not"),
    (@{const HOL.conj}, "and"),
    (@{const HOL.disj}, "or"),
    (@{const HOL.implies}, "=>"),
    (@{const HOL.eq ('a)}, "="),
    (@{const If ('a)}, "ite"),
    (@{const less (int)}, "<"),
    (@{const less_eq (int)}, "<="),
    (@{const uminus (int)}, "~"),
    (@{const plus (int)}, "+"),
    (@{const minus (int)}, "-")] #>
  SMT2_Builtin.add_builtin_fun smtlib2C
    (Term.dest_Const @{const times (int)}, times)

end


(* serialization *)

(** header **)

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
  in "(set-logic " ^ choose (Logics.get (Context.Proof ctxt)) ^ ")\n" end


(** serialization **)

fun var i = "?v" ^ string_of_int i

fun tree_of_sterm l (SMT2_Translate.SVar i) = SMTLIB2.Sym (var (l - i - 1))
  | tree_of_sterm _ (SMT2_Translate.SApp (n, [])) = SMTLIB2.Sym n
  | tree_of_sterm l (SMT2_Translate.SApp (n, ts)) =
      SMTLIB2.S (SMTLIB2.Sym n :: map (tree_of_sterm l) ts)
  | tree_of_sterm _ (SMT2_Translate.SLet _) =
      raise Fail "SMT-LIB: unsupported let expression"
  | tree_of_sterm l (SMT2_Translate.SQua (q, ss, pats, t)) =
      let
        val l' = l + length ss

        fun quant_name SMT2_Translate.SForall = "forall"
          | quant_name SMT2_Translate.SExists = "exists"

        fun gen_trees_of_pat keyword ps =
          [SMTLIB2.Key keyword, (case map (tree_of_sterm l') ps of [t] => t | ts => SMTLIB2.S ts)]
        fun trees_of_pat (SMT2_Translate.SPat ps) = gen_trees_of_pat "pattern" ps
          | trees_of_pat (SMT2_Translate.SNoPat ps) = gen_trees_of_pat "no-pattern" ps
        fun tree_of_pats [] t = t
          | tree_of_pats pats t = SMTLIB2.S (SMTLIB2.Sym "!" :: t :: maps trees_of_pat pats)

        val vs = map_index (fn (i, ty) =>
          SMTLIB2.S [SMTLIB2.Sym (var (l + i)), SMTLIB2.Sym ty]) ss

        val body = t
          |> tree_of_sterm l'
          |> tree_of_pats pats
      in
        SMTLIB2.S [SMTLIB2.Sym (quant_name q), SMTLIB2.S vs, body]
      end


fun sctrarg (sel, typ) = "(" ^ sel ^ " " ^ typ ^ ")"
fun sctr (name, args) = enclose "(" ")" (space_implode " " (name :: map sctrarg args))
fun sdatatype (name, ctrs) = enclose "(" ")" (space_implode " " (name :: map sctr ctrs))

fun string_of_fun (f, (ss, s)) = f ^ " (" ^ space_implode " " ss ^ ") " ^ s

fun named_sterm s t = SMTLIB2.S [SMTLIB2.Sym "!", t, SMTLIB2.Key "named", SMTLIB2.Sym s]

val assert_prefix = "a"

fun assert_name_of_index i = assert_prefix ^ string_of_int i
fun assert_index_of_name s = the_default ~1 (Int.fromString (unprefix assert_prefix s))

fun serialize comments {header, sorts, dtyps, funcs} ts =
  Buffer.empty
  |> fold (Buffer.add o enclose "; " "\n") comments
  |> Buffer.add "(set-option :produce-proofs true)\n"
  |> Buffer.add header
  |> fold (Buffer.add o enclose "(declare-sort " " 0)\n") (sort fast_string_ord sorts)
  |> (if null dtyps then I
    else Buffer.add (enclose "(declare-datatypes () (" "))\n"
      (space_implode "\n  " (maps (map sdatatype) dtyps))))
  |> fold (Buffer.add o enclose "(declare-fun " ")\n" o string_of_fun)
       (sort (fast_string_ord o pairself fst) funcs)
  |> fold (fn (i, t) => Buffer.add (enclose "(assert " ")\n"
      (SMTLIB2.str_of (named_sterm (assert_name_of_index i) (tree_of_sterm 0 t)))))
    (map_index I ts)
  |> Buffer.add "(check-sat)\n(get-proof)\n"
  |> Buffer.content

(* interface *)

fun translate_config ctxt = {
  header = choose_logic ctxt,
  has_datatypes = false,
  serialize = serialize}

val _ = Theory.setup (Context.theory_map
  (setup_builtins #>
   SMT2_Translate.add_config (smtlib2C, translate_config)))

end
