(*  Title:      HOL/HOLCF/Tools/cont_consts.ML
    Author:     Tobias Mayr
    Author:     David von Oheimb
    Author:     Makarius

HOLCF version of 'consts' command: handle continuous function types in mixfix
syntax.
*)

signature CONT_CONSTS =
sig
  val add_consts: (binding * typ * mixfix) list -> theory -> theory
  val add_consts_cmd: (binding * string * mixfix) list -> theory -> theory
end

structure Cont_Consts: CONT_CONSTS =
struct

fun count_cfun \<^Type>\<open>cfun _ B\<close> = count_cfun B + 1
  | count_cfun _ = 0

fun change_cfun 0 T = T
  | change_cfun n \<^Type>\<open>cfun A B\<close> = \<^Type>\<open>fun A \<open>change_cfun (n - 1) B\<close>\<close>
  | change_cfun _ T = raise TYPE ("cont_consts: change_cfun", [T], [])

fun gen_add_consts prep_typ raw_decls thy =
  let
    val thy_ctxt = Proof_Context.init_global thy

    fun is_cont_const (_, _, NoSyn) = false
      | is_cont_const (_, _, Binder _) = false
      | is_cont_const (b, T, mx) =
          let
            val n = Mixfix.mixfix_args thy_ctxt mx handle ERROR msg =>
              cat_error msg ("in mixfix annotation for " ^ Binding.print b)
          in count_cfun T >= n end

    fun transform (b, T, mx) =
      let
        val c = Sign.full_name thy b
        val c1 = Lexicon.mark_syntax c
        val c2 = Lexicon.mark_const c
        val xs = Name.invent Name.context "xa" (Mixfix.mixfix_args thy_ctxt mx)
        val trans_rules =
          Syntax.Parse_Print_Rule
            (Ast.mk_appl (Ast.Constant c1) (map Ast.Variable xs),
              fold (fn x => fn t =>
                  Ast.mk_appl (Ast.Constant \<^const_syntax>\<open>Rep_cfun\<close>) [t, Ast.Variable x])
                xs (Ast.Constant c2)) ::
          (if Mixfix.is_infix mx then [Syntax.Parse_Rule (Ast.Constant c1, Ast.Constant c2)] else [])
      in ((b, T, NoSyn), (c1, change_cfun (length xs) T, mx), trans_rules) end

    val decls = map (fn (b, T, mx) => (b, prep_typ thy T, mx)) raw_decls
    val (cont_decls, normal_decls) = List.partition is_cont_const decls
    val transformed_decls = map transform cont_decls
  in
    thy
    |> Sign.add_consts (normal_decls @ map #1 transformed_decls)
    |> Sign.syntax_global true Syntax.mode_default (map #2 transformed_decls)
    |> Sign.add_trrules (maps #3 transformed_decls)
  end

val add_consts = gen_add_consts Sign.certify_typ
val add_consts_cmd = gen_add_consts Syntax.read_typ_global

end
