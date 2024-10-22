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

(* type cfun *)

fun count_cfun \<^Type>\<open>cfun _ B\<close> = count_cfun B + 1
  | count_cfun _ = 0

fun change_cfun 0 T = T
  | change_cfun n \<^Type>\<open>cfun A B\<close> = \<^Type>\<open>fun A \<open>change_cfun (n - 1) B\<close>\<close>
  | change_cfun _ T = raise TYPE ("cont_consts: change_arrow", [T], [])


(* translations *)

fun trans_rules name2 name1 n mx =
  let
    val xs = Name.invent Name.context "xa" n
    val extra_parse_rule = Syntax.Parse_Rule (Ast.Constant name2, Ast.Constant name1)
  in
    [Syntax.Parse_Print_Rule
      (Ast.mk_appl (Ast.Constant name2) (map Ast.Variable xs),
        fold (fn x => fn t =>
            Ast.mk_appl (Ast.Constant \<^const_syntax>\<open>Rep_cfun\<close>) [t, Ast.Variable x])
          xs (Ast.Constant name1))] @
    (case mx of
      Infix _ => [extra_parse_rule]
    | Infixl _ => [extra_parse_rule]
    | Infixr _ => [extra_parse_rule]
    | _ => [])
  end


(* add_consts *)

fun gen_add_consts prep_typ raw_decls thy =
  let
    val thy_ctxt = Proof_Context.init_global thy

    fun is_cont_const (_, _, NoSyn) = false
      | is_cont_const (_, _, Binder _) = false    (* FIXME ? *)
      | is_cont_const (c, T, mx) =
          let
            val n = Mixfix.mixfix_args thy_ctxt mx handle ERROR msg =>
              cat_error msg ("in mixfix annotation for " ^ Binding.print c)
          in count_cfun T >= n end

    fun transform (c, T, mx) =
      let
        fun syntax b = Lexicon.mark_const (Sign.full_bname thy b)
        val c1 = Binding.name_of c
        val c2 = c1 ^ "_cont_syntax"
        val n = Mixfix.mixfix_args thy_ctxt mx
      in
        ((c, T, NoSyn),
          (Binding.name c2, change_cfun n T, mx),
          trans_rules (syntax c2) (syntax c1) n mx)
      end

    val decls = map (fn (c, T, mx) => (c, prep_typ thy T, mx)) raw_decls
    val (cont_decls, normal_decls) = List.partition is_cont_const decls
    val transformed_decls = map transform cont_decls
  in
    thy
    |> Sign.add_consts (normal_decls @ map #1 transformed_decls @ map #2 transformed_decls)
    |> Sign.add_trrules (maps #3 transformed_decls)
  end

val add_consts = gen_add_consts Sign.certify_typ
val add_consts_cmd = gen_add_consts Syntax.read_typ_global

end
