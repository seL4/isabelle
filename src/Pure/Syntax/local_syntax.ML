(*  Title:      Pure/Syntax/local_syntax.ML
    Author:     Makarius

Local syntax depending on theory syntax, with special support for
implicit structure references.
*)

signature LOCAL_SYNTAX =
sig
  type T
  val syntax_of: T -> Syntax.syntax
  val init: theory -> T
  val rebuild: Proof.context -> T -> T
  datatype kind = Type | Const | Fixed
  val add_syntax: Proof.context -> (kind * (string * typ * mixfix)) list ->
    T -> {structs: string list, fixes: string list} option * T
  val syntax_deps: Proof.context -> (string * string list) list -> T -> T
  val translations: Proof.context -> bool -> Ast.ast Syntax.trrule list -> T -> T
  val set_mode: Syntax.mode -> T -> T
  val restore_mode: T -> T -> T
  val update_modesyntax: Proof.context -> bool -> Syntax.mode ->
    (kind * (string * typ * mixfix)) list ->
    T -> {structs: string list, fixes: string list} option * T
end;

structure Local_Syntax: LOCAL_SYNTAX =
struct

(* datatype T *)

type local_mixfix =
  {name: string, is_fixed: bool} *
  ({is_type: bool, add: bool, mode: Syntax.mode} * (string * typ * mixfix));

datatype T = Syntax of
 {thy_syntax: Syntax.syntax,
  local_syntax: Syntax.syntax,
  mode: Syntax.mode,
  mixfixes: local_mixfix list,
  consts: (string * string list) list,
  translations: (bool * Ast.ast Syntax.trrule list) list};

fun make_syntax (thy_syntax, local_syntax, mode, mixfixes, consts, translations) =
  Syntax {thy_syntax = thy_syntax, local_syntax = local_syntax, mode = mode,
    mixfixes = mixfixes, consts = consts, translations = translations};

fun map_syntax f (Syntax {thy_syntax, local_syntax, mode, mixfixes, consts, translations}) =
  make_syntax (f (thy_syntax, local_syntax, mode, mixfixes, consts, translations));

fun is_consistent ctxt (Syntax {thy_syntax, ...}) =
  Syntax.eq_syntax (Sign.syntax_of (Proof_Context.theory_of ctxt), thy_syntax);

fun syntax_of (Syntax {local_syntax, ...}) = local_syntax;


(* build syntax *)

fun build_syntax ctxt mode mixfixes consts translations =
  let
    val thy = Proof_Context.theory_of ctxt;
    val thy_syntax = Sign.syntax_of thy;
    fun update_gram ({is_type = true, add, mode}, decls) =
          Syntax.update_type_gram ctxt add mode decls
      | update_gram ({is_type = false, add, mode}, decls) =
          Syntax.update_const_gram ctxt add (Sign.logical_types thy) mode decls;

    val local_syntax = thy_syntax
      |> fold update_gram (AList.coalesce (op =) (rev (map snd mixfixes)))
      |> Syntax.update_consts ctxt consts
      |> fold_rev (uncurry (Syntax.update_trrules ctxt)) translations;
  in make_syntax (thy_syntax, local_syntax, mode, mixfixes, consts, translations) end;

fun init thy =
  let val thy_syntax = Sign.syntax_of thy
  in make_syntax (thy_syntax, thy_syntax, Syntax.mode_default, [], [], []) end;

fun rebuild ctxt (syntax as Syntax {mode, mixfixes, consts, translations, ...}) =
  if is_consistent ctxt syntax then syntax
  else build_syntax ctxt mode mixfixes consts translations;


(* mixfix declarations *)

datatype kind = Type | Const | Fixed;

local

fun prep_mixfix _ _ (_, (_, _, Structure _)) = (NONE: local_mixfix option)
  | prep_mixfix add mode (Type, decl as (x, _, _)) =
      SOME ({name = x, is_fixed = false}, ({is_type = true, add = add, mode = mode}, decl))
  | prep_mixfix add mode (Const, decl as (x, _, _)) =
      SOME ({name = x, is_fixed = false}, ({is_type = false, add = add, mode = mode}, decl))
  | prep_mixfix add mode (Fixed, (x, T, mx)) =
      SOME (({name = x, is_fixed = true},
        ({is_type = false, add = add, mode = mode}, (Lexicon.mark_fixed x, T, mx))));

fun prep_struct (Fixed, (c, _, Structure _)) = SOME c
  | prep_struct (_, (c, _, Structure _)) = error ("Bad structure mixfix declaration for " ^ quote c)
  | prep_struct _ = NONE;

in

fun update_syntax ctxt add raw_decls (syntax as (Syntax {mode, mixfixes, consts, translations, ...})) =
  (case filter_out (Mixfix.is_empty o #3 o #2) raw_decls of
    [] => (NONE, syntax)
  | decls =>
      let
        val new_mixfixes = map_filter (prep_mixfix add mode) decls;
        val new_structs = map_filter prep_struct decls;
        val mixfixes' = rev new_mixfixes @ mixfixes;

        val idents = Syntax_Trans.get_idents ctxt;
        val idents' =
          {structs =
            if add then #structs idents @ new_structs
            else subtract (op =) new_structs (#structs idents),
           fixes = fold (fn ({name = x, is_fixed = true}, _) => cons x | _ => I) mixfixes' []};

        val syntax' = build_syntax ctxt mode mixfixes' consts translations;
      in (if idents = idents' then NONE else SOME idents', syntax') end);

fun add_syntax ctxt = update_syntax ctxt true;

end;


(* translations *)

fun syntax_deps ctxt args (Syntax {mode, mixfixes, consts, translations, ...}) =
  build_syntax ctxt mode mixfixes (args @ consts) translations;

fun translations ctxt add args (Syntax {mode, mixfixes, consts, translations, ...}) =
 (Sign.check_translations ctxt args;
  build_syntax ctxt mode mixfixes consts ((add, args) :: translations));


(* syntax mode *)

fun set_mode mode = map_syntax (fn (thy_syntax, local_syntax, _, mixfixes, consts, translations) =>
  (thy_syntax, local_syntax, mode, mixfixes, consts, translations));

fun restore_mode (Syntax {mode, ...}) = set_mode mode;

fun update_modesyntax ctxt add mode args syntax =
  syntax |> set_mode mode |> update_syntax ctxt add args ||> restore_mode syntax;

end;
