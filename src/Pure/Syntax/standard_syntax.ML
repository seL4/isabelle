(*  Title:      Pure/Syntax/standard_syntax.ML
    Author:     Makarius

Standard implementation of inner syntax operations.
*)

structure Standard_Syntax: sig end =
struct

fun parse_failed ctxt pos msg kind =
  cat_error msg ("Failed to parse " ^ kind ^
    Markup.markup Markup.report (Context_Position.reported_text ctxt pos Markup.bad ""));

fun parse_sort ctxt text =
  let
    val (syms, pos) = Syntax.parse_token ctxt Markup.sort text;
    val S =
      Syntax.standard_parse_sort ctxt (ProofContext.type_context ctxt)
          (ProofContext.syn_of ctxt) (syms, pos)
        handle ERROR msg => parse_failed ctxt pos msg "sort";
  in Type.minimize_sort (ProofContext.tsig_of ctxt) S end;

fun parse_typ ctxt text =
  let
    val (syms, pos) = Syntax.parse_token ctxt Markup.typ text;
    val T =
      Syntax.standard_parse_typ ctxt (ProofContext.type_context ctxt)
          (ProofContext.syn_of ctxt) (ProofContext.get_sort ctxt) (syms, pos)
        handle ERROR msg => parse_failed ctxt pos msg "type";
  in T end;

fun parse_term T ctxt text =
  let
    val (T', _) = Type_Infer.paramify_dummies T 0;
    val (markup, kind) =
      if T' = propT then (Markup.prop, "proposition") else (Markup.term, "term");
    val (syms, pos) = Syntax.parse_token ctxt markup text;

    val default_root = Config.get ctxt Syntax.default_root;
    val root =
      (case T' of
        Type (c, _) =>
          if c <> "prop" andalso Type.is_logtype (ProofContext.tsig_of ctxt) c
          then default_root else c
      | _ => default_root);

    fun check t = (Syntax.check_term ctxt (Type.constraint T' t); Exn.Result t)
      handle exn as ERROR _ => Exn.Exn exn;
    val t =
      Syntax.standard_parse_term check ctxt
        (ProofContext.type_context ctxt) (ProofContext.term_context ctxt)
        (ProofContext.syn_of ctxt) root (syms, pos)
      handle ERROR msg => parse_failed ctxt pos msg kind;
  in t end;


fun unparse_sort ctxt =
  Syntax.standard_unparse_sort {extern_class = Type.extern_class (ProofContext.tsig_of ctxt)}
    ctxt (ProofContext.syn_of ctxt);

fun unparse_typ ctxt =
  let
    val tsig = ProofContext.tsig_of ctxt;
    val extern = {extern_class = Type.extern_class tsig, extern_type = Type.extern_type tsig};
  in Syntax.standard_unparse_typ extern ctxt (ProofContext.syn_of ctxt) end;

fun unparse_term ctxt =
  let
    val tsig = ProofContext.tsig_of ctxt;
    val syntax = ProofContext.syntax_of ctxt;
    val consts = ProofContext.consts_of ctxt;
    val extern =
     {extern_class = Type.extern_class tsig,
      extern_type = Type.extern_type tsig,
      extern_const = Consts.extern consts};
  in
    Syntax.standard_unparse_term (Local_Syntax.idents_of syntax) extern ctxt
      (Local_Syntax.syn_of syntax) (not (Pure_Thy.old_appl_syntax (ProofContext.theory_of ctxt)))
  end;


val _ = Syntax.install_operations
  {parse_sort = parse_sort,
   parse_typ = parse_typ,
   parse_term = parse_term dummyT,
   parse_prop = parse_term propT,
   unparse_sort = unparse_sort,
   unparse_typ = unparse_typ,
   unparse_term = unparse_term};

end;
