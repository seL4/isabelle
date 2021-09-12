(*  Title:      HOL/HOLCF/Tools/cont_consts.ML
    Author:     Tobias Mayr, David von Oheimb, and Markus Wenzel

HOLCF version of consts: handle continuous function types in mixfix
syntax.
*)

signature CONT_CONSTS =
sig
  val add_consts: (binding * typ * mixfix) list -> theory -> theory
  val add_consts_cmd: (binding * string * mixfix) list -> theory -> theory
end

structure Cont_Consts: CONT_CONSTS =
struct


(* misc utils *)

fun change_arrow 0 T = T
  | change_arrow n (Type (_, [S, T])) = \<^Type>\<open>fun S \<open>change_arrow (n - 1) T\<close>\<close>
  | change_arrow _ T = raise TYPE ("cont_consts: change_arrow", [T], [])

fun trans_rules name2 name1 n mx =
  let
    val vnames = Name.invent Name.context "a" n
    val extra_parse_rule = Syntax.Parse_Rule (Ast.Constant name2, Ast.Constant name1)
  in
    [Syntax.Parse_Print_Rule
      (Ast.mk_appl (Ast.Constant name2) (map Ast.Variable vnames),
        fold (fn a => fn t =>
            Ast.mk_appl (Ast.Constant \<^const_syntax>\<open>Rep_cfun\<close>) [t, Ast.Variable a])
          vnames (Ast.Constant name1))] @
    (case mx of
      Infix _ => [extra_parse_rule]
    | Infixl _ => [extra_parse_rule]
    | Infixr _ => [extra_parse_rule]
    | _ => [])
  end


(* transforming infix/mixfix declarations of constants with type ...->...
   a declaration of such a constant is transformed to a normal declaration with
   an internal name, the same type, and nofix. Additionally, a purely syntactic
   declaration with the original name, type ...=>..., and the original mixfix
   is generated and connected to the other declaration via some translation.
*)
fun transform thy (c, T, mx) =
  let
    fun syntax b = Lexicon.mark_const (Sign.full_bname thy b)
    val c1 = Binding.name_of c
    val c2 = c1 ^ "_cont_syntax"
    val n = Mixfix.mixfix_args mx
  in
    ((c, T, NoSyn),
      (Binding.name c2, change_arrow n T, mx),
      trans_rules (syntax c2) (syntax c1) n mx)
  end

fun cfun_arity (Type (n, [_, T])) = if n = \<^type_name>\<open>cfun\<close> then 1 + cfun_arity T else 0
  | cfun_arity _ = 0

fun is_contconst (_, _, NoSyn) = false
  | is_contconst (_, _, Binder _) = false    (* FIXME ? *)
  | is_contconst (c, T, mx) =
      let
        val n = Mixfix.mixfix_args mx handle ERROR msg =>
          cat_error msg ("in mixfix annotation for " ^ Binding.print c)
      in cfun_arity T >= n end


(* add_consts *)

local

fun gen_add_consts prep_typ raw_decls thy =
  let
    val decls = map (fn (c, T, mx) => (c, prep_typ thy T, mx)) raw_decls
    val (contconst_decls, normal_decls) = List.partition is_contconst decls
    val transformed_decls = map (transform thy) contconst_decls
  in
    thy
    |> Sign.add_consts (normal_decls @ map #1 transformed_decls @ map #2 transformed_decls)
    |> Sign.add_trrules (maps #3 transformed_decls)
  end

in

val add_consts = gen_add_consts Sign.certify_typ
val add_consts_cmd = gen_add_consts Syntax.read_typ_global

end

end
