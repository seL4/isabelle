(*  Title:      Pure/Tools/codegen_serializer.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol") to
target languages (like ML or Haskell).
*)

signature CODEGEN_SERIALIZER =
sig
  type 'a pretty_syntax;
  type serializer = 
      string list list
      -> OuterParse.token list ->
      ((string -> string option)
        * (string -> CodegenThingol.itype pretty_syntax option)
        * (string -> CodegenThingol.iexpr pretty_syntax option)
      -> string list option
      -> CodegenThingol.module -> unit)
      * OuterParse.token list;
  val parse_syntax: (string -> 'b -> 'a * 'b) -> OuterParse.token list ->
    ('b -> 'a pretty_syntax * 'b) * OuterParse.token list;
  val parse_targetdef: string -> CodegenThingol.prim list;
  val pretty_list: string -> string -> int * string -> CodegenThingol.iexpr pretty_syntax;
  val serializers: {
    ml: string * (string * string * (string -> bool) -> serializer),
    haskell: string * (string list -> serializer)
  }
end;

structure CodegenSerializer: CODEGEN_SERIALIZER =
struct

open CodegenThingol;
infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 3 `|->;
infixr 3 `|-->;


(** generic serialization **)

(* precedences *)

datatype lrx = L | R | X;

datatype fixity =
    BR
  | NOBR
  | INFX of (int * lrx);

datatype 'a mixfix =
    Arg of fixity
  | Ignore
  | Pretty of Pretty.T
  | Quote of 'a;

type 'a pretty_syntax = (int * int) * (fixity -> (fixity -> 'a -> Pretty.T)
  -> 'a list -> Pretty.T);

fun eval_lrx L L = false
  | eval_lrx R R = false
  | eval_lrx _ _ = true;

fun eval_fxy NOBR _ = false
  | eval_fxy _ BR = true
  | eval_fxy _ NOBR = false
  | eval_fxy (INFX (pr, lr)) (INFX (pr_ctxt, lr_ctxt)) =
      pr < pr_ctxt
      orelse pr = pr_ctxt
        andalso eval_lrx lr lr_ctxt
  | eval_fxy _ (INFX _) = false;

val str = setmp print_mode [] Pretty.str;

fun gen_brackify _ [p] = p
  | gen_brackify true (ps as _::_) = Pretty.enclose "(" ")" ps
  | gen_brackify false (ps as _::_) = Pretty.block ps;

fun brackify fxy_ctxt ps =
  gen_brackify (eval_fxy BR fxy_ctxt) (Pretty.breaks ps);

fun brackify_infix infx fxy_ctxt ps =
  gen_brackify (eval_fxy (INFX infx) fxy_ctxt) (Pretty.breaks ps);

fun from_app mk_app from_expr const_syntax fxy (c, es) =
  let
    fun mk NONE es =
          brackify fxy (mk_app c es)
      | mk (SOME ((i, k), pr)) es =
          let
            val (es1, es2) = splitAt (k, es);
          in
            brackify fxy (pr fxy from_expr es1 :: map (from_expr BR) es2)
          end;
  in mk (const_syntax c) es end;

val _ : (string -> iexpr list -> Pretty.T list)
                 -> (fixity -> iexpr -> Pretty.T)
                    -> (string
                        -> ((int * int)
                            * (fixity
                               -> (fixity -> iexpr -> Pretty.T)
                                  -> iexpr list -> Pretty.T)) option)
                       -> fixity -> string * iexpr list -> Pretty.T = from_app;

fun fillin_mixfix fxy_this ms fxy_ctxt pr args =
  let
    fun fillin [] [] =
         []
      | fillin (Arg fxy :: ms) (a :: args) =
          pr fxy a :: fillin ms args
      | fillin (Ignore :: ms) args =
          fillin ms args
      | fillin (Pretty p :: ms) args =
          p :: fillin ms args
      | fillin (Quote q :: ms) args =
          pr BR q :: fillin ms args;
  in gen_brackify (eval_fxy fxy_this fxy_ctxt) (fillin ms args) end;


(* user-defined syntax *)

val (atomK, infixK, infixlK, infixrK) =
  ("target_atom", "infix", "infixl", "infixr");
val _ = OuterSyntax.add_keywords [atomK, infixK, infixlK, infixrK];

fun parse_infix (fixity as INFX (i, x)) s =
  let
    val l = case x of L => fixity
                    | _ => INFX (i, X);
    val r = case x of R => fixity
                    | _ => INFX (i, X);
  in
    pair [Arg l, (Pretty o Pretty.brk) 1, (Pretty o str) s, (Pretty o Pretty.brk) 1, Arg r]
  end;

fun parse_mixfix reader s ctxt =
  let
    fun sym s = Scan.lift ($$ s);
    fun lift_reader ctxt s =
      ctxt
      |> reader s
      |-> (fn x => pair (Quote x));
    val sym_any = Scan.lift (Scan.one Symbol.not_eof);
    val parse = Scan.repeat (
         (sym "_" -- sym "_" >> K (Arg NOBR))
      || (sym "_" >> K (Arg BR))
      || (sym "?" >> K Ignore)
      || (sym "/" |-- Scan.repeat (sym " ") >> (Pretty o Pretty.brk o length))
      || Scan.depend (fn ctxt => $$ "{" |-- $$ "*" |-- Scan.repeat1
           (   $$ "'" |-- Scan.one Symbol.not_eof
            || Scan.unless ($$ "*" -- $$ "}") (Scan.one Symbol.not_eof)) --|
         $$ "*" --| $$ "}" >> (implode #> lift_reader ctxt #> swap))
      || (Scan.repeat1
           (   sym "'" |-- sym_any
            || Scan.unless (sym "_" || sym "?" || sym "/" || sym "{" |-- sym "*")
                 sym_any) >> (Pretty o str o implode)));
  in case Scan.finite' Symbol.stopper parse (ctxt, Symbol.explode s)
   of (p, (ctxt, [])) => (p, ctxt)
    | _ => error ("Malformed mixfix annotation: " ^ quote s)
  end;

fun parse_nonatomic_mixfix reader s ctxt =
  case parse_mixfix reader s ctxt
   of ([Pretty _], _) =>
        error ("mixfix contains just one pretty element; either declare as "
          ^ quote atomK ^ " or consider adding a break")
    | x => x;

fun parse_syntax_proto reader = OuterParse.$$$ "(" |-- (
       OuterParse.$$$ infixK  |-- OuterParse.nat
        >> (fn i => (parse_infix (INFX (i, X)), INFX (i, X)))
    || OuterParse.$$$ infixlK |-- OuterParse.nat
        >> (fn i => (parse_infix (INFX (i, L)), INFX (i, L)))
    || OuterParse.$$$ infixrK |-- OuterParse.nat
        >> (fn i => (parse_infix (INFX (i, R)), INFX (i, R)))
    || OuterParse.$$$ atomK |-- pair (parse_mixfix reader, NOBR)
    || pair (parse_nonatomic_mixfix reader, BR)
  ) -- OuterParse.string --| OuterParse.$$$ ")" >> (fn ((p, fxy), s) => (p s, fxy));

fun parse_syntax reader =
  let
    fun is_arg (Arg _) = true
      | is_arg Ignore = true
      | is_arg _ = false;
    fun mk fixity mfx =
      let
        val i = length (List.filter is_arg mfx)
      in ((i, i), fillin_mixfix fixity mfx) end;
  in
    parse_syntax_proto reader
    #-> (fn (mfx_reader, fixity) : ('Z -> 'Y mixfix list * 'Z) * fixity =>
      pair (mfx_reader #-> (fn mfx => pair (mk fixity mfx)))
    )
  end;

fun newline_correct s =
  s
  |> Symbol.strip_blanks
  |> space_explode "\n"
  |> map (implode o (fn [] => []
                      | (" "::xs) => xs
                      | xs => xs) o explode)
  |> space_implode "\n";

fun parse_targetdef s =
  case Scan.finite Symbol.stopper (Scan.repeat (
         ($$ "`" |-- $$ "`" >> (CodegenThingol.Pretty o str))
      || ($$ "`" |-- Scan.repeat1 (Scan.unless ($$ "`") (Scan.one Symbol.not_eof))
            --| $$ "`" >> (fn ["_"] => Name | s => error ("malformed antiquote: " ^ implode s)))
      || Scan.repeat1
           (Scan.unless ($$ "`") (Scan.one Symbol.not_eof)) >> (CodegenThingol.Pretty o str o implode)
    )) (Symbol.explode s)
   of (p, []) => p
    | (p, ss) => error ("Malformed definition: " ^ quote s ^ " - " ^ commas ss);


(* abstract serializer *)

type serializer = 
    string list list
    -> OuterParse.token list ->
    ((string -> string option)
      * (string -> itype pretty_syntax option)
      * (string -> iexpr pretty_syntax option)
    -> string list option
    -> module -> unit)
    * OuterParse.token list;

fun abstract_serializer (target, nspgrp) name_root (from_defs, from_module, validator, postproc)
    postprocess preprocess (class_syntax, tyco_syntax, const_syntax)
    select module =
  let
    fun pretty_of_prim resolv (name, primdef) =
      let
        fun pr (CodegenThingol.Pretty p) = p
          | pr Name = (str o resolv) name;
      in case AList.lookup (op = : string * string -> bool) primdef target
       of NONE => error ("no primitive definition for " ^ quote name)
        | SOME ps => (case map pr ps
           of [] => NONE
            | ps => (SOME o Pretty.block) ps)
      end;
    fun from_module' imps ((name_qual, name), defs) =
      from_module imps ((name_qual, name), defs) |> postprocess name_qual;
  in
    module
    |> debug 3 (fn _ => "selecting submodule...")
    |> (if is_some select then (partof o the) select else I)
    |> tap (Pretty.writeln o pretty_deps)
    |> debug 3 (fn _ => "preprocessing...")
    |> preprocess
    |> debug 3 (fn _ => "serializing...")
    |> serialize (from_defs (pretty_of_prim, (class_syntax : string -> string option, tyco_syntax, const_syntax)))
         from_module' validator postproc nspgrp name_root
    |> K ()
  end;

fun abstract_validator keywords name =
  let
    fun replace_invalid c =
      if (Char.isAlphaNum o the o Char.fromString) c orelse c = "'"
      andalso not (NameSpace.separator = c)
      then c
      else "_"
    fun suffix_it name =
      name
      |> member (op =) keywords ? suffix "'"
      |> (fn name' => if name = name' then name else suffix_it name')
  in
    name
    |> translate_string replace_invalid
    |> suffix_it
    |> (fn name' => if name = name' then NONE else SOME name')
  end;

fun write_file mkdir path p = (
    if mkdir
      then
        File.mkdir (Path.dir path)
      else ();
      File.write path (Pretty.output p ^ "\n");
      p
  );

fun mk_module_file postprocess_module ext path name p =
  let
    val prfx = Path.dir path;
    val name' = case name
     of "" => Path.base path
      | _ => (Path.ext ext o Path.unpack o implode o separate "/" o NameSpace.unpack) name;
  in
    p
    |> write_file true (Path.append prfx name')
    |> postprocess_module name
  end;

fun parse_single_file serializer =
  OuterParse.path
  >> (fn path => serializer
        (fn "" => write_file false path #> K NONE
          | _ => SOME));

fun parse_multi_file postprocess_module ext serializer =
  OuterParse.path
  >> (fn path => (serializer o mk_module_file postprocess_module ext) path);

fun parse_internal serializer =
  OuterParse.name
  >> (fn "-" => serializer
        (fn "" => (fn p => (use_text Context.ml_output false (Pretty.output p); NONE))
          | _ => SOME)
       | _ => Scan.fail ());


(* list serializer *)

fun pretty_list thingol_nil thingol_cons (target_pred, target_cons) =
  let
    fun dest_cons (IApp (IApp (IConst ((c, _), _), e1), e2)) =
          if c = thingol_cons
          then SOME (e1, e2)
          else NONE
      | dest_cons  _ = NONE;
    fun pretty_default fxy pr e1 e2 =
      brackify_infix (target_pred, R) fxy [
        pr (INFX (target_pred, X)) e1,
        str target_cons,
        pr (INFX (target_pred, R)) e2
      ];
    fun pretty_compact fxy pr [e1, e2] =
      case unfoldr dest_cons e2
       of (es, IConst ((c, _), _)) =>
            if c = thingol_nil
            then Pretty.enum "," "[" "]" (map (pr NOBR) (e1::es))
            else pretty_default fxy pr e1 e2
        | _ => pretty_default fxy pr e1 e2;
  in ((2, 2), pretty_compact) end;



(** ML serializer **)

local

fun ml_from_defs (is_cons, needs_type)
    (from_prim, (_, tyco_syntax, const_syntax)) resolv defs =
  let
    fun chunk_defs ps =
      let
        val (p_init, p_last) = split_last ps
      in
        Pretty.chunks (p_init @ [Pretty.block ([p_last, str ";"])])
      end;
    val ml_from_label =
      resolv
      #> NameSpace.base
      #> translate_string (fn "_" => "__" | "." => "_" | c => c)
      #> str;
    fun ml_from_label' l =
      Pretty.block [str "#", ml_from_label l];
    fun ml_from_lookup fxy [] p =
          p
      | ml_from_lookup fxy [l] p =
          brackify fxy [
            ml_from_label' l,
            p
          ]
      | ml_from_lookup fxy ls p =
          brackify fxy [
            Pretty.enum " o" "(" ")" (map ml_from_label' ls),
            p
          ];
    fun ml_from_sortlookup fxy ls =
      let
        fun from_classlookup fxy (Instance (inst, lss)) =
              brackify fxy (
                (str o resolv) inst
                :: map (ml_from_sortlookup BR) lss
              )
          | from_classlookup fxy (Lookup (classes, (v, ~1))) =
              ml_from_lookup BR classes (str v)
          | from_classlookup fxy (Lookup (classes, (v, i))) =
              ml_from_lookup BR (string_of_int (i+1) :: classes) (str v)
      in case ls
       of [l] => from_classlookup fxy l
        | ls => (Pretty.list "(" ")" o map (from_classlookup NOBR)) ls
      end;
    val ml_from_label =
      resolv
      #> NameSpace.base
      #> translate_string (fn "_" => "__" | "." => "_" | c => c)
      #> str;
    fun ml_from_tycoexpr fxy (tyco, tys) =
      let
        val tyco' = (str o resolv) tyco
      in case map (ml_from_type BR) tys
       of [] => tyco'
        | [p] => Pretty.block [p, Pretty.brk 1, tyco']
        | (ps as _::_) => Pretty.block [Pretty.list "(" ")" ps, Pretty.brk 1, tyco']
      end
    and ml_from_type fxy (IType (tycoexpr as (tyco, tys))) =
          (case tyco_syntax tyco
           of NONE => ml_from_tycoexpr fxy (tyco, tys)
            | SOME ((i, k), pr) =>
                if not (i <= length tys andalso length tys <= k)
                then error ("number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " to " ^ string_of_int k
                  ^ " expected")
                else pr fxy ml_from_type tys)
      | ml_from_type fxy (IFun (t1, t2)) =
          let
            val brackify = gen_brackify
              (case fxy
                of BR => false
                 | _ => eval_fxy (INFX (1, R)) fxy) o Pretty.breaks;
          in
            brackify [
              ml_from_type (INFX (1, X)) t1,
              str "->",
              ml_from_type (INFX (1, R)) t2
            ]
          end
      | ml_from_type _ (IVarT (v, _)) =
          str ("'" ^ v);
    fun ml_from_expr fxy (e as IApp (e1, e2)) =
          (case unfold_const_app e
           of SOME x => ml_from_app fxy x
            | NONE =>
                brackify fxy [
                  ml_from_expr NOBR e1,
                  ml_from_expr BR e2
                ])
      | ml_from_expr fxy (e as IConst x) =
          ml_from_app fxy (x, [])
      | ml_from_expr fxy (IVarE (v, ty)) =
          if needs_type ty
            then
              Pretty.enclose "(" ")" [
                str v,
                str ":",
                ml_from_type NOBR ty
              ]
            else
              str v
      | ml_from_expr fxy (IAbs ((v, _), e)) =
          brackify fxy [
            str ("fn " ^ v ^ " =>"),
            ml_from_expr NOBR e
          ]
      | ml_from_expr fxy (e as ICase (_, [_])) =
          let
            val (ps, e) = unfold_let e;
            fun mk_val (p, e) = Pretty.block [
                str "val ",
                ml_from_expr fxy p,
                str " =",
                Pretty.brk 1,
                ml_from_expr NOBR e,
                str ";"
              ]
          in Pretty.chunks [
            [str ("let"), Pretty.fbrk, map mk_val ps |> Pretty.chunks] |> Pretty.block,
            [str ("in"), Pretty.fbrk, ml_from_expr NOBR e] |> Pretty.block,
            str ("end")
          ] end
      | ml_from_expr fxy (ICase (e, c::cs)) =
          let
            fun mk_clause definer (p, e) =
              Pretty.block [
                str definer,
                ml_from_expr NOBR p,
                str " =>",
                Pretty.brk 1,
                ml_from_expr NOBR e
              ]
          in brackify fxy (
            str "case"
            :: ml_from_expr NOBR e
            :: mk_clause "of " c
            :: map (mk_clause "| ") cs
          ) end
      | ml_from_expr _ e =
          error ("dubious expression: " ^ (Pretty.output o pretty_iexpr) e)
    and ml_mk_app f es =
      if is_cons f andalso length es > 1
      then
        [(str o resolv) f, Pretty.enum " *" "(" ")" (map (ml_from_expr BR) es)]
      else
        (str o resolv) f :: map (ml_from_expr BR) es
    and ml_from_app fxy (((c, _), lss), es) =
      case map (ml_from_sortlookup BR) lss
       of [] =>
            from_app ml_mk_app ml_from_expr const_syntax fxy (c, es)
        | lss =>
            brackify fxy (
              (str o resolv) c
              :: (lss
              @ map (ml_from_expr BR) es)
            );
    fun ml_from_funs (defs as def::defs_tl) =
      let
        fun mk_definer [] = "val"
          | mk_definer _ = "fun";
        fun check_args (_, Fun ((pats, _)::_, _)) NONE =
              SOME (mk_definer pats)
          | check_args (_, Fun ((pats, _)::_, _)) (SOME definer) =
              if mk_definer pats = definer
              then SOME definer
              else error ("mixing simultaneous vals and funs not implemented")
          | check_args _ _ =
              error ("function definition block containing other definitions than functions")
        fun mk_fun definer (name, Fun (eqs as eq::eq_tl, (sortctxt, ty))) =
          let
            val shift = if null eq_tl then I else map (Pretty.block o single);
            fun mk_eq definer (pats, expr) =
              (Pretty.block o Pretty.breaks) (
                [str definer, (str o resolv) name]
                @ (if null pats
                   then [str ":", ml_from_type NOBR ty]
                   else map (str o fst) sortctxt @ map (ml_from_expr BR) pats)
                @ [str "=", ml_from_expr NOBR expr]
              )
          in
            (Pretty.block o Pretty.fbreaks o shift) (
              mk_eq definer eq
              :: map (mk_eq "|") eq_tl
            )
          end;
      in
        chunk_defs (
          mk_fun (the (fold check_args defs NONE)) def
          :: map (mk_fun "and") defs_tl
        ) |> SOME
      end;
    fun ml_from_datatypes defs =
      let
        val defs' = List.mapPartial
          (fn (name, Datatype info) => SOME (name, info)
            | (name, Datatypecons _) => NONE
            | (name, def) => error ("datatype block containing illegal def: "
                ^ (Pretty.output o pretty_def) def)
          ) defs
        fun mk_cons (co, []) =
              str (resolv co)
          | mk_cons (co, tys) =
              Pretty.block (
                str (resolv co)
                :: str " of"
                :: Pretty.brk 1
                :: separate (Pretty.block [str " *", Pretty.brk 1])
                     (map (ml_from_type NOBR) tys)
              )
        fun mk_datatype definer (t, ((vs, cs), _)) =
          (Pretty.block o Pretty.breaks) (
            str definer
            :: ml_from_tycoexpr NOBR (t, map IVarT vs)
            :: str "="
            :: separate (str "|") (map mk_cons cs)
          )
      in
        case defs'
         of (def::defs_tl) =>
            chunk_defs (
              mk_datatype "datatype" def
              :: map (mk_datatype "and ") defs_tl
            ) |> SOME
          | _ => NONE
      end
    fun ml_from_def (name, Undef) =
          error ("empty definition during serialization: " ^ quote name)
      | ml_from_def (name, Prim prim) =
          from_prim resolv (name, prim)
      | ml_from_def (name, Typesyn (vs, ty)) =
        (map (fn (vname, []) => () | _ =>
            error "can't serialize sort constrained type declaration to ML") vs;
          Pretty.block [
            str "type ",
            ml_from_tycoexpr NOBR (name, map IVarT vs),
            str " =",
            Pretty.brk 1,
            ml_from_type NOBR ty,
            str ";"
            ]
          ) |> SOME
      | ml_from_def (name, Class ((supclasses, (v, membrs)), _)) =
          let
            val pv = str ("'" ^ v);
            fun from_supclass class =
              Pretty.block [
                ml_from_label class,
                str ":",
                Pretty.brk 1,
                pv,
                Pretty.brk 1,
                (str o resolv) class
              ]
            fun from_membr (m, (_, ty)) =
              Pretty.block [
                ml_from_label m,
                str ":",
                Pretty.brk 1,
                ml_from_type NOBR ty
              ]
          in
            Pretty.block [
              str "type",
              Pretty.brk 1,
              pv,
              Pretty.brk 1,
              (str o resolv) name,
              Pretty.brk 1,
              str "=",
              Pretty.brk 1,
              Pretty.enum "," "{" "};" (
                map from_supclass supclasses @ map from_membr membrs
              )
            ] |> SOME
          end
      | ml_from_def (_, Classmember _) =
          NONE
      | ml_from_def (name, Classinst (((class, (tyco, arity)), suparities), memdefs)) =
          let
            val definer = if null arity then "val" else "fun"
            fun from_supclass (supclass, lss) =
              (Pretty.block o Pretty.breaks) (
                ml_from_label supclass
                :: str "="
                :: map (ml_from_sortlookup NOBR) lss
              );
            fun from_memdef (m, def) =
              ((the o ml_from_funs) [(m, Fun def)], Pretty.block [
                ml_from_label m,
                Pretty.brk 1,
                str "=",
                Pretty.brk 1,
                (str o resolv) m
              ]);
            fun mk_memdefs supclassexprs [] =
                  Pretty.enum "," "{" "};" (
                    supclassexprs
                  )
              | mk_memdefs supclassexprs memdefs =
                  let
                    val (defs, assigns) = (split_list o map from_memdef) memdefs;
                  in
                    Pretty.chunks [
                      [str ("let"), Pretty.fbrk, defs |> Pretty.chunks]
                        |> Pretty.block,
                      [str ("in "), Pretty.enum "," "{" "};" (supclassexprs @ assigns)]
                        |> Pretty.block
                    ] 
                  end;
          in
            Pretty.block [
              (Pretty.block o Pretty.breaks) (
                str definer
                :: (str o resolv) name
                :: map (str o fst) arity
              ),
              Pretty.brk 1,
              str "=",
              Pretty.brk 1,
              mk_memdefs (map from_supclass suparities) memdefs
            ] |> SOME
          end;
  in case defs
   of (_, Fun _)::_ => ml_from_funs defs
    | (_, Datatypecons _)::_ => ml_from_datatypes defs
    | (_, Datatype _)::_ => ml_from_datatypes defs
    | [def] => ml_from_def def
  end;

in

fun ml_from_thingol target (nsp_dtcon, nsp_class, is_int_tyco) nspgrp =
  let
    val reserved_ml = ThmDatabase.ml_reserved @ [
      "bool", "int", "list", "true", "false", "o"
    ];
    fun ml_from_module _ ((_, name), ps) =
      Pretty.chunks ([
        str ("structure " ^ name ^ " = "),
        str "struct",
        str ""
      ] @ separate (str "") ps @ [
        str "",
        str ("end; (* struct " ^ name ^ " *)")
      ]);
    fun needs_type (IType (tyco, _)) =
          has_nsp tyco nsp_class
          orelse is_int_tyco tyco
      | needs_type _ =
          false;
    fun is_cons c = has_nsp c nsp_dtcon;
    val serializer = abstract_serializer (target, nspgrp)
      "ROOT" (ml_from_defs (is_cons, needs_type), ml_from_module,
        abstract_validator reserved_ml, snd);
    fun eta_expander module const_syntax s =
      case const_syntax s
       of SOME ((i, _), _) => i
        | _ => if has_nsp s nsp_dtcon
               then case get_def module s
                of Datatypecons dtname => case get_def module dtname
                of Datatype ((_, cs), _) =>
                  let val l = AList.lookup (op =) cs s |> the |> length
                  in if l >= 2 then l else 0 end
                else 0;
    fun preprocess const_syntax module =
      module
      |> tap (Pretty.writeln o pretty_deps)
      |> debug 3 (fn _ => "eta-expanding...")
      |> eta_expand (eta_expander module const_syntax)
      |> debug 3 (fn _ => "eta-expanding polydefs...")
      |> eta_expand_poly
      |> debug 3 (fn _ => "unclashing expression/type variables...")
      |> unclash_vars_tvars;
    val parse_multi =
      OuterParse.name
      #-> (fn "dir" => 
               parse_multi_file
                 (K o SOME o str o suffix ";" o prefix "val _ = use "
                  o quote o suffix ".ML" o translate_string (fn "." => "/" | s => s)) "ML" serializer
            | _ => Scan.fail ());
  in
    (parse_multi
     || parse_internal serializer
     || parse_single_file serializer)
    >> (fn seri => fn (class_syntax, tyco_syntax, const_syntax) => seri 
         (preprocess const_syntax) (class_syntax, tyco_syntax, const_syntax))
  end;

end; (* local *)

local

fun hs_from_defs with_typs (from_prim, (class_syntax, tyco_syntax, const_syntax))
    resolv defs =
  let
    fun hs_from_sctxt vs =
      let
        fun from_class cls =
          class_syntax cls
          |> the_default (resolv cls)
        fun from_sctxt [] = str ""
          | from_sctxt vs =
              vs
              |> map (fn (v, cls) => str (from_class cls ^ " " ^ v))
              |> Pretty.enum "," "(" ")"
              |> (fn p => Pretty.block [p, str " => "])
      in 
        vs
        |> map (fn (v, sort) => map (pair v) sort)
        |> Library.flat
        |> from_sctxt
      end;
    fun hs_from_tycoexpr fxy (tyco, tys) =
      brackify fxy ((str o resolv) tyco :: map (hs_from_type BR) tys)
    and hs_from_type fxy (IType (tycoexpr as (tyco, tys))) =
          (case tyco_syntax tyco
           of NONE =>
                hs_from_tycoexpr fxy tycoexpr
            | SOME ((i, k), pr) =>
                if not (i <= length tys andalso length tys <= k)
                then error ("number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " to " ^ string_of_int k
                  ^ " expected")
                else pr fxy hs_from_type tys)
      | hs_from_type fxy (IFun (t1, t2)) =
          brackify_infix (1, R) fxy [
            hs_from_type (INFX (1, X)) t1,
            str "->",
            hs_from_type (INFX (1, R)) t2
          ]
      | hs_from_type fxy (IVarT (v, _)) =
          str v;
    fun hs_from_sctxt_tycoexpr (sctxt, tycoexpr) =
      Pretty.block [hs_from_sctxt sctxt, hs_from_tycoexpr NOBR tycoexpr]
    fun hs_from_sctxt_type (sctxt, ty) =
      Pretty.block [hs_from_sctxt sctxt, hs_from_type NOBR ty]
    fun hs_from_expr fxy (e as IApp (e1, e2)) =
          (case unfold_const_app e
           of SOME x => hs_from_app fxy x
            | _ =>
                brackify fxy [
                  hs_from_expr NOBR e1,
                  hs_from_expr BR e2
                ])
      | hs_from_expr fxy (e as IConst x) =
          hs_from_app fxy (x, [])
      | hs_from_expr fxy (IVarE (v, _)) =
          str v
      | hs_from_expr fxy (e as IAbs _) =
          let
            val (vs, body) = unfold_abs e
          in
            brackify fxy (
              str "\\"
              :: map (str o fst) vs @ [
              str "->",
              hs_from_expr NOBR body
            ])
          end
      | hs_from_expr fxy (e as ICase (_, [_])) =
          let
            val (ps, body) = unfold_let e;
            fun mk_bind (p, e) = Pretty.block [
                hs_from_expr BR p,
                str " =",
                Pretty.brk 1,
                hs_from_expr NOBR e
              ];
          in Pretty.chunks [
            [str ("let"), Pretty.fbrk, map mk_bind ps |> Pretty.chunks] |> Pretty.block,
            [str ("in "), hs_from_expr NOBR body] |> Pretty.block
          ] end
      | hs_from_expr fxy (ICase (e, cs)) =
          let
            fun mk_clause (p, e) =
              Pretty.block [
                hs_from_expr NOBR p,
                str " ->",
                Pretty.brk 1,
                hs_from_expr NOBR e
              ]
          in Pretty.block [
            str "case",
            Pretty.brk 1,
            hs_from_expr NOBR e,
            Pretty.brk 1,
            str "of",
            Pretty.fbrk,
            (Pretty.chunks o map mk_clause) cs
          ] end
    and hs_mk_app c es =
      (str o resolv) c :: map (hs_from_expr BR) es
    and hs_from_app fxy (((c, _), ls), es) =
      from_app hs_mk_app hs_from_expr const_syntax fxy (c, es);
    fun hs_from_funeqs (name, eqs) =
      let
        fun from_eq name (args, rhs) =
          Pretty.block [
            (str o resolv) name,
            Pretty.block (map (fn p => Pretty.block [Pretty.brk 1, hs_from_expr BR p]) args),
            Pretty.brk 1,
            str ("="),
            Pretty.brk 1,
            hs_from_expr NOBR rhs
          ]
      in Pretty.chunks (map (from_eq name) eqs) end;
    fun hs_from_def (name, Undef) =
          error ("empty statement during serialization: " ^ quote name)
      | hs_from_def (name, Prim prim) =
          from_prim resolv (name, prim)
      | hs_from_def (name, Fun (eqs, (sctxt, ty))) =
          let
            val body = hs_from_funeqs (name, eqs);
          in if with_typs then
            Pretty.chunks [
              Pretty.block [
                (str o suffix " ::" o resolv) name,
                Pretty.brk 1,
                hs_from_sctxt_type (sctxt, ty)
              ],
              body
            ] |> SOME
          else SOME body end
      | hs_from_def (name, Typesyn (vs, ty)) =
          Pretty.block [
            str "type ",
            hs_from_sctxt_tycoexpr (vs, (name, map IVarT vs)),
            str " =",
            Pretty.brk 1,
            hs_from_sctxt_type ([], ty)
          ] |> SOME
      | hs_from_def (name, Datatype ((vs, constrs), _)) =
          let
            fun mk_cons (co, tys) =
              (Pretty.block o Pretty.breaks) (
                (str o resolv) co
                :: map (hs_from_type NOBR) tys
              )
          in
            Pretty.block ((
              str "data "
              :: hs_from_sctxt_type (vs, IType (name, map IVarT vs))
              :: str " ="
              :: Pretty.brk 1
              :: separate (Pretty.block [Pretty.brk 1, str "| "]) (map mk_cons constrs)
            ) @ [
              Pretty.brk 1,
              str "deriving Show"
            ])
          end |> SOME
      | hs_from_def (_, Datatypecons _) =
          NONE
      | hs_from_def (name, Class ((supclasss, (v, membrs)), _)) =
          let
            fun mk_member (m, (sctxt, ty)) =
              Pretty.block [
                str (resolv m ^ " ::"),
                Pretty.brk 1,
                hs_from_sctxt_type (sctxt, ty)
              ]
          in
            Pretty.block [
              str "class ",
              hs_from_sctxt (map (fn class => (v, [class])) supclasss),
              str (resolv name ^ " " ^ v),
              str " where",
              Pretty.fbrk,
              Pretty.chunks (map mk_member membrs)
            ] |> SOME
          end
      | hs_from_def (name, Classmember _) =
          NONE
      | hs_from_def (_, Classinst (((clsname, (tyco, arity)), _), memdefs)) = 
          Pretty.block [
            str "instance ",
            hs_from_sctxt_tycoexpr (arity, (clsname, map (IVarT o rpair [] o fst) arity)),
            str " ",
            hs_from_sctxt_tycoexpr (arity, (tyco, map (IVarT o rpair [] o fst) arity)),
            str " where",
            Pretty.fbrk,
            Pretty.chunks (map (fn (m, (eqs, _)) => hs_from_funeqs (m, eqs)) memdefs)
          ] |> SOME
  in
    case List.mapPartial (fn (name, def) => hs_from_def (name, def)) defs
     of [] => NONE
      | l => (SOME o Pretty.chunks o separate (str "")) l
  end;

in

fun hs_from_thingol target nsps_upper nspgrp =
  let
    val reserved_hs = [
      "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
      "import", "default", "forall", "let", "in", "class", "qualified", "data",
      "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
    ] @ [
      "Bool", "fst", "snd", "Integer", "True", "False", "negate"
    ];
    fun hs_from_module imps ((_, name), ps) =
      (Pretty.block o Pretty.fbreaks) (
          str ("module " ^ name ^ " where")
      :: map (str o prefix "import qualified ") imps @ [
          str "",
          Pretty.chunks (separate (str "") ps)
      ]);
    fun postproc (shallow, n) =
      let
        fun ch_first f = String.implode o nth_map 0 f o String.explode;
      in if member (op =) nsps_upper shallow
        then ch_first Char.toUpper n
        else ch_first Char.toLower n
      end;
    fun serializer with_typs = abstract_serializer (target, nspgrp)
      "Main" (hs_from_defs with_typs, hs_from_module, abstract_validator reserved_hs, postproc);
    fun eta_expander const_syntax c =
      const_syntax c
      |> Option.map (fst o fst)
      |> the_default 0;
    fun preprocess const_syntax module =
      module
      |> tap (Pretty.writeln o pretty_deps)
      |> debug 3 (fn _ => "eta-expanding...")
      |> eta_expand (eta_expander const_syntax)
  in
    (Scan.optional (OuterParse.name >> (fn "no_typs" => false | s => Scan.fail_with (fn _ => "illegal flag: " ^ quote s) true)) true
    #-> (fn with_typs => parse_multi_file ((K o K) NONE) "hs" (serializer with_typs)))
    >> (fn (seri) => fn (class_syntax, tyco_syntax, const_syntax) => seri 
         (preprocess const_syntax) (class_syntax, tyco_syntax, const_syntax))
  end;

end; (* local *)


(** lookup record **)

val serializers =
  let
    fun seri s f = (s, f s);
  in {
    ml = seri "ml" ml_from_thingol,
    haskell = seri "haskell" hs_from_thingol
  } end;

end; (* struct *)
