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
  val parse_syntax: ('b -> int) -> (string -> 'b -> 'a * 'b) -> OuterParse.token list ->
    ('b -> 'a pretty_syntax * 'b) * OuterParse.token list;
  val parse_targetdef: string -> CodegenThingol.prim list;
  val pretty_list: string -> string -> int * string -> CodegenThingol.iexpr pretty_syntax;
  val serializers: {
    ml: string * (string * string * (string -> bool) -> serializer),
    haskell: string * (string list -> serializer)
  };
  val mk_flat_ml_resolver: string list -> string -> string;
  val ml_fun_datatype: string * string * (string -> bool)
    -> ((string -> CodegenThingol.itype pretty_syntax option)
        * (string -> CodegenThingol.iexpr pretty_syntax option))
    -> (string -> string)
    -> ((string * CodegenThingol.funn) list -> Pretty.T)
        * ((string * CodegenThingol.datatyp) list -> Pretty.T);
end;

structure CodegenSerializer: CODEGEN_SERIALIZER =
struct

open BasicCodegenThingol;
val debug_msg = CodegenThingol.debug_msg;

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

fun from_app mk_app from_expr const_syntax fxy (const as (c, _), es) =
  case (const_syntax c)
   of NONE => brackify fxy (mk_app c es)
    | SOME ((i, k), pr) =>
        if i <= length es
          then case chop k es of (es1, es2) =>
            brackify fxy (pr fxy from_expr es1 :: map (from_expr BR) es2)
          else from_expr fxy (CodegenThingol.eta_expand (const, es) i);

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
          pr BR q :: fillin ms args
      | fillin [] _ =
          error ("inconsistent mixfix: too many arguments")
      | fillin _ [] =
          error ("inconsistent mixfix: too less arguments");
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

fun parse_syntax no_args reader =
  let
    fun is_arg (Arg _) = true
      | is_arg Ignore = true
      | is_arg _ = false;
    fun mk fixity mfx ctxt =
      let
        val i = (length o List.filter is_arg) mfx;
        val _ = if i > no_args ctxt then error "too many arguments in codegen syntax" else ();
      in (((i, i), fillin_mixfix fixity mfx), ctxt) end;
  in
    parse_syntax_proto reader
    #-> (fn (mfx_reader, fixity) =>
      pair (mfx_reader #-> (fn mfx => mk fixity mfx))
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
            --| $$ "`" >> (fn ["_"] => CodegenThingol.Name | s => error ("malformed antiquote: " ^ implode s)))
      || Scan.repeat1
           (Scan.unless ($$ "`") (Scan.one Symbol.not_eof)) >> (CodegenThingol.Pretty o str o implode)
    )) ((Symbol.explode o Symbol.strip_blanks) s)
   of (p, []) => p
    | (p, ss) => error ("Malformed definition: " ^ quote s ^ " - " ^ commas ss);


(* generic abstract serializer *)

type serializer = 
    string list list
    -> OuterParse.token list ->
    ((string -> string option)
      * (string -> itype pretty_syntax option)
      * (string -> iexpr pretty_syntax option)
    -> string list option
    -> CodegenThingol.module -> unit)
    * OuterParse.token list;

fun abstract_serializer (target, nspgrp) name_root (from_defs, from_module, validator, postproc)
    postprocess (class_syntax, tyco_syntax, const_syntax)
    select module =
  let
    fun pretty_of_prim resolv (name, primdef) =
      let
        fun pr (CodegenThingol.Pretty p) = p
          | pr CodegenThingol.Name = (str o resolv) name;
      in case AList.lookup (op = : string * string -> bool) primdef target
       of NONE => error ("no primitive definition for " ^ quote name)
        | SOME ps => (case map pr ps
           of [] => NONE
            | ps => (SOME o Pretty.block) ps)
      end;
    fun from_module' resolv imps ((name_qual, name), defs) =
      from_module resolv imps ((name_qual, name), defs)
      |> postprocess (resolv name_qual);
  in
    module
    |> debug_msg (fn _ => "selecting submodule...")
    |> (if is_some select then (CodegenThingol.project_module o the) select else I)
    |> debug_msg (fn _ => "serializing...")
    |> CodegenThingol.serialize (from_defs (pretty_of_prim, (class_syntax : string -> string option, tyco_syntax, const_syntax)))
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

fun constructive_fun (name, (eqs, ty)) =
  let
    fun check_eq (eq as (lhs, rhs)) =
      if forall CodegenThingol.is_pat lhs
      then SOME eq
      else (warning ("in function " ^ quote name ^ ", throwing away one "
        ^ "non-executable function clause"); NONE)
  in case map_filter check_eq eqs
   of [] => error ("in function " ^ quote name ^ ", no"
        ^ "executable function clauses found")
    | eqs => (name, (eqs, ty))
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
    fun dest_cons (IConst (c, _) `$ e1 `$ e2) =
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
      case CodegenThingol.unfoldr dest_cons e2
       of (es, IConst (c, _)) =>
            if c = thingol_nil
            then Pretty.enum "," "[" "]" (map (pr NOBR) (e1::es))
            else pretty_default fxy pr e1 e2
        | _ => pretty_default fxy pr e1 e2;
  in ((2, 2), pretty_compact) end;



(** ML serializer **)

local

val reserved_ml = ThmDatabase.ml_reserved @ [
  "bool", "int", "list", "unit", "option", "true", "false", "not", "None", "Some", "o"
];

structure NameMangler = NameManglerFun (
  type ctxt = string list;
  type src = string;
  val ord = string_ord;
  fun mk reserved_ml (name, 0) =
        (CodegenTheorems.proper_name o NameSpace.base) name
    | mk reserved_ml (name, i) =
        (CodegenTheorems.proper_name o NameSpace.base) name ^ replicate_string i "'";
  fun is_valid (reserved_ml : string list) = not o member (op =) reserved_ml;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such definition name: " ^ quote dst);
);

fun ml_expr_seri (is_cons, needs_type) (tyco_syntax, const_syntax) resolv =
  let
    val ml_from_label =
      str o translate_string (fn "_" => "__" | "." => "_" | c => c)
        o NameSpace.base o resolv;
    fun ml_from_tyvar (v, sort) =
      let
        fun mk_class v class =
          str (prefix "'" v ^ " " ^ resolv class);
      in
        Pretty.block [
          str "(",
          str v,
          str ":",
          case sort
           of [] => str "unit"
            | [class] => mk_class v class
            | _ => Pretty.enum " *" "" "" (map (mk_class v) sort),
          str ")"
        ]
      end;
    fun ml_from_sortlookup fxy lss =
      let
        fun from_label l =
          Pretty.block [str "#",
            if (is_some o Int.fromString) l then str l
            else ml_from_label l
          ];
        fun from_lookup fxy [] p = p
          | from_lookup fxy [l] p =
              brackify fxy [
                from_label l,
                p
              ]
          | from_lookup fxy ls p =
              brackify fxy [
                Pretty.enum " o" "(" ")" (map from_label ls),
                p
              ];
        fun from_classlookup fxy (Instance (inst, lss)) =
              brackify fxy (
                (str o resolv) inst
                :: map (ml_from_sortlookup BR) lss
              )
          | from_classlookup fxy (Lookup (classes, (v, ~1))) =
              from_lookup BR classes (str v)
          | from_classlookup fxy (Lookup (classes, (v, i))) =
              from_lookup BR (string_of_int (i+1) :: classes) (str v)
      in case lss
       of [] => str "()"
        | [ls] => from_classlookup fxy ls
        | lss => (Pretty.list "(" ")" o map (from_classlookup NOBR)) lss
      end;
    fun ml_from_tycoexpr fxy (tyco, tys) =
      let
        val tyco' = (str o resolv) tyco
      in case map (ml_from_type BR) tys
       of [] => tyco'
        | [p] => Pretty.block [p, Pretty.brk 1, tyco']
        | (ps as _::_) => Pretty.block [Pretty.list "(" ")" ps, Pretty.brk 1, tyco']
      end
    and ml_from_type fxy (tycoexpr as tyco `%% tys) =
          (case tyco_syntax tyco
           of NONE => ml_from_tycoexpr fxy (tyco, tys)
            | SOME ((i, k), pr) =>
                if not (i <= length tys andalso length tys <= k)
                then error ("number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " to " ^ string_of_int k
                  ^ " expected")
                else pr fxy ml_from_type tys)
      | ml_from_type fxy (t1 `-> t2) =
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
      | ml_from_type fxy (ITyVar v) =
          str ("'" ^ v);
    fun typify ty p =
      let
        fun needs_type_t (tyco `%% tys) =
            needs_type tyco
            orelse exists needs_type_t tys
        | needs_type_t (ITyVar _) =
            false
        | needs_type_t (ty1 `-> ty2) =
            needs_type_t ty1 orelse needs_type_t ty2;
      in if needs_type_t ty
        then
          Pretty.enclose "(" ")" [
            p,
            str ":",
            ml_from_type NOBR ty
          ]
        else p
      end;
    fun ml_from_expr fxy (e as IConst x) =
          ml_from_app fxy (x, [])
      | ml_from_expr fxy (IVar v) =
          str v
      | ml_from_expr fxy (e as e1 `$ e2) =
          (case CodegenThingol.unfold_const_app e
           of SOME x => ml_from_app fxy x
            | NONE =>
                brackify fxy [
                  ml_from_expr NOBR e1,
                  ml_from_expr BR e2
                ])
      | ml_from_expr fxy ((v, ty) `|-> e) =
          brackify BR [
            str "fn",
            typify ty (str v),
            str "=>",
            ml_from_expr NOBR e
          ]
      | ml_from_expr fxy (INum (n, _)) =
          brackify BR [
            (str o IntInf.toString) n,
            str ":IntInf.int"
          ]
      | ml_from_expr _ (IChar (c, _)) =
          (str o prefix "#" o quote)
            (let val i = (Char.ord o the o Char.fromString) c
              in if i < 32 
                then prefix "\\" c
                else c
              end)
      | ml_from_expr fxy (IAbs (((ve, vty), be), _)) =
          brackify BR [
            str "fn",
            typify vty (ml_from_expr NOBR ve),
            str "=>",
            ml_from_expr NOBR be
          ]
      | ml_from_expr fxy (e as ICase ((_, [_]), _)) =
          let
            val (ves, be) = CodegenThingol.unfold_let e;
            fun mk_val ((ve, vty), se) = Pretty.block [
                (Pretty.block o Pretty.breaks) [
                  str "val",
                  typify vty (ml_from_expr NOBR ve),
                  str "=",
                  ml_from_expr NOBR se
                ],
                str ";"
              ];
          in Pretty.chunks [
            [str ("let"), Pretty.fbrk, map mk_val ves |> Pretty.chunks] |> Pretty.block,
            [str ("in"), Pretty.fbrk, ml_from_expr NOBR be] |> Pretty.block,
            str ("end")
          ] end
      | ml_from_expr fxy (ICase (((de, dty), bse::bses), _)) =
          let
            fun mk_clause definer (se, be) =
              (Pretty.block o Pretty.breaks) [
                str definer,
                ml_from_expr NOBR se,
                str "=>",
                ml_from_expr NOBR be
              ]
          in brackify fxy (
            str "(case"
            :: typify dty (ml_from_expr NOBR de)
            :: mk_clause "of" bse
            :: map (mk_clause "|") bses
            @ [str ")"]
          ) end
      | ml_from_expr _ e =
          error ("dubious expression: " ^ (Pretty.output o CodegenThingol.pretty_iexpr) e)
    and ml_mk_app f es =
      if is_cons f andalso length es > 1 then
        [(str o resolv) f, Pretty.enum "," "(" ")" (map (ml_from_expr BR) es)]
      else
        (str o resolv) f :: map (ml_from_expr BR) es
    and ml_from_app fxy (app_expr as ((c, (lss, ty)), es)) =
      case map (ml_from_sortlookup BR) lss
       of [] =>
            from_app ml_mk_app ml_from_expr const_syntax fxy app_expr
        | lss =>
            brackify fxy (
              (str o resolv) c
              :: (lss
              @ map (ml_from_expr BR) es)
            );
  in (ml_from_label, ml_from_tyvar, ml_from_sortlookup, ml_from_tycoexpr, ml_from_type, typify, ml_from_expr) end;

fun ml_fun_datatyp (is_cons, needs_type) (tyco_syntax, const_syntax) resolv =
  let
    val (ml_from_label, ml_from_tyvar, ml_from_sortlookup, ml_from_tycoexpr, ml_from_type, typify, ml_from_expr) =
      ml_expr_seri (is_cons, needs_type) (tyco_syntax, const_syntax) resolv;
    fun chunk_defs ps =
      let
        val (p_init, p_last) = split_last ps
      in
        Pretty.chunks (p_init @ [Pretty.block ([p_last, str ";"])])
      end;
    fun eta_expand_poly_fun (funn as (_, (_::_, _))) =
          funn
      | eta_expand_poly_fun (funn as (eqs, sctxt_ty as (_, ty))) =
          let
            fun no_eta (_::_, _) = I
              | no_eta (_, _ `|-> _) = I
              | no_eta (_, IAbs (_, _)) = I
              | no_eta ([], e) = K false;
            fun has_tyvars (_ `%% tys) =
                  exists has_tyvars tys
              | has_tyvars (ITyVar _) =
                  true
              | has_tyvars (ty1 `-> ty2) =
                  has_tyvars ty1 orelse has_tyvars ty2;
          in if (null o fst o CodegenThingol.unfold_fun) ty
              orelse (not o has_tyvars) ty
              orelse fold no_eta eqs true
            then funn
            else (map (fn ([], rhs) => ([IVar "x"], rhs `$ IVar "x")) eqs, sctxt_ty)
          end;
    fun ml_from_funs (defs as def::defs_tl) =
      let
        fun mk_definer [] [] = "val"
          | mk_definer _ _ = "fun";
        fun check_args (_, ((pats, _)::_, (sortctxt, _))) NONE =
              SOME (mk_definer pats sortctxt)
          | check_args (_, ((pats, _)::_, (sortctxt, _))) (SOME definer) =
              if mk_definer pats sortctxt = definer
              then SOME definer
              else error ("mixing simultaneous vals and funs not implemented");
        fun mk_fun definer (name, (eqs as eq::eq_tl, (sortctxt, ty))) =
          let
            val shift = if null eq_tl then I else
              map (Pretty.block o single o Pretty.block o single);
            fun mk_arg e ty =
              ml_from_expr BR e
              |> typify ty
            fun mk_eq definer (pats, expr) =
              (Pretty.block o Pretty.breaks) (
                [str definer, (str o resolv) name]
                @ (if null pats andalso null sortctxt
                   then [str ":", ml_from_type NOBR ty]
                   else
                     map ml_from_tyvar sortctxt
                     @ map2 mk_arg pats
                         ((curry Library.take (length pats) o fst o CodegenThingol.unfold_fun) ty))
                @ [str "=", ml_from_expr NOBR expr]
              )
          in
            (Pretty.block o Pretty.fbreaks o shift) (
              mk_eq definer eq
              :: map (mk_eq "|") eq_tl
            )
          end;
        val def' :: defs' = map (apsnd eta_expand_poly_fun o constructive_fun) defs
      in
        chunk_defs (
          (mk_fun (the (fold check_args defs NONE))) def'
          :: map (mk_fun "and") defs'
        )
      end;
    fun ml_from_datatypes (defs as (def::defs_tl)) =
      let
        fun mk_cons (co, []) =
              str (resolv co)
          | mk_cons (co, tys) =
              Pretty.block [
                str (resolv co),
                str " of",
                Pretty.brk 1,
                Pretty.enum " *" "" "" (map (ml_from_type NOBR) tys)
              ]
        fun mk_datatype definer (t, (vs, cs)) =
          (Pretty.block o Pretty.breaks) (
            str definer
            :: ml_from_tycoexpr NOBR (t, map (ITyVar o fst) vs)
            :: str "="
            :: separate (str "|") (map mk_cons cs)
          )
      in
        chunk_defs (
          mk_datatype "datatype" def
          :: map (mk_datatype "and") defs_tl
        )
      end;
  in (ml_from_funs, ml_from_datatypes) end;

fun ml_from_defs (is_cons, needs_type)
    (from_prim, (_, tyco_syntax, const_syntax)) resolver prefix defs =
  let
    val resolv = resolver prefix;
    val (ml_from_label, ml_from_tyvar, ml_from_sortlookup, ml_from_tycoexpr, ml_from_type, typify, ml_from_expr) =
      ml_expr_seri (is_cons, needs_type) (tyco_syntax, const_syntax) resolv;
    val (ml_from_funs, ml_from_datatypes) =
      ml_fun_datatyp (is_cons, needs_type) (tyco_syntax, const_syntax) resolv;
    val filter_datatype =
      map_filter
        (fn (name, CodegenThingol.Datatype info) => SOME (name, info)
          | (name, CodegenThingol.Datatypecons _) => NONE
          | (name, def) => error ("datatype block containing illegal def: "
                ^ (Pretty.output o CodegenThingol.pretty_def) def));
    fun filter_class defs = 
      case map_filter
        (fn (name, CodegenThingol.Class info) => SOME (name, info)
          | (name, CodegenThingol.Classmember _) => NONE
          | (name, def) => error ("class block containing illegal def: "
                ^ (Pretty.output o CodegenThingol.pretty_def) def)) defs
       of [class] => class
        | _ => error ("class block without class: " ^ (commas o map (quote o fst)) defs)
    fun ml_from_class (name, (supclasses, (v, membrs))) =
      let
        fun from_supclass class =
          Pretty.block [
            ml_from_label class,
            str ":",
            Pretty.brk 1,
            str ("'" ^ v),
            Pretty.brk 1,
            (str o resolv) class
          ];
        fun from_membr (m, (_, ty)) =
          Pretty.block [
            ml_from_label m,
            str ":",
            Pretty.brk 1,
            ml_from_type NOBR ty
          ];
        fun from_membr_fun (m, _) =
          (Pretty.block o Pretty.breaks) [
            str "fun",
            (str o resolv) m, 
            Pretty.enclose "(" ")" [str (v ^ ":'" ^ v ^ " " ^ resolv name)],
            str "=",
            Pretty.block [str "#", ml_from_label m],
            str (v ^ ";")
          ];
      in
        Pretty.chunks (
          (Pretty.block o Pretty.breaks) [
            str "type",
            str ("'" ^ v),
            (str o resolv) name,
            str "=",
            Pretty.enum "," "{" "};" (
              map from_supclass supclasses @ map from_membr membrs
            )
          ]
        :: map from_membr_fun membrs)
      end
    fun ml_from_def (name, CodegenThingol.Undef) =
          error ("empty definition during serialization: " ^ quote name)
      | ml_from_def (name, CodegenThingol.Prim prim) =
          from_prim resolv (name, prim)
      | ml_from_def (name, CodegenThingol.Typesyn (vs, ty)) =
        (map (fn (vname, []) => () | _ =>
            error "can't serialize sort constrained type declaration to ML") vs;
          Pretty.block [
            str "type ",
            ml_from_tycoexpr NOBR (name, map (ITyVar o fst) vs),
            str " =",
            Pretty.brk 1,
            ml_from_type NOBR ty,
            str ";"
            ]
          ) |> SOME
      | ml_from_def (name, CodegenThingol.Classinst (((class, (tyco, arity)), suparities), memdefs)) =
          let
            val definer = if null arity then "val" else "fun"
            fun from_supclass (supclass, (supinst, lss)) =
              (Pretty.block o Pretty.breaks) (
                ml_from_label supclass
                :: str "="
                :: (str o resolv) supinst
                :: (if null lss andalso (not o null) arity
                     then [str "()"]
                     else map (ml_from_sortlookup NOBR) lss)
              );
            fun from_memdef (m, ((m', def), lss)) =
              (ml_from_funs [(m', def)], (Pretty.block o Pretty.breaks) (
                ml_from_label m
                :: str "="
                :: (str o resolv) m'
                :: map (ml_from_sortlookup NOBR) lss
              ));
            fun mk_corp rhs =
              (Pretty.block o Pretty.breaks) (
                str definer
                :: (str o resolv) name
                :: map ml_from_tyvar arity
                @ [str "=", rhs]
              );
            fun mk_memdefs supclassexprs [] =
                  Pretty.enum "," "{" "};" (
                    supclassexprs
                  ) |> mk_corp
              | mk_memdefs supclassexprs memdefs =
                  let
                    val (defs, assigns) = (split_list o map from_memdef) memdefs;
                  in
                    Pretty.chunks [
                      Pretty.block [
                        str "local",
                        Pretty.fbrk,
                        Pretty.chunks defs
                      ],
                      Pretty.block [str "in", Pretty.brk 1,
                        (mk_corp o Pretty.block o Pretty.breaks) [
                          Pretty.enum "," "{" "}" (supclassexprs @ assigns),
                          str ":",
                          ml_from_tycoexpr NOBR (class, [tyco `%% map (ITyVar o fst) arity])
                        ]
                      ],
                      str "end; (* instance *)"
                    ]
                  end;
          in
            mk_memdefs (map from_supclass suparities) memdefs |> SOME
          end
      | ml_from_def (name, CodegenThingol.Classinstmember) = NONE;
  in case defs
   of (_, CodegenThingol.Fun _)::_ => (SOME o ml_from_funs o map (fn (name, CodegenThingol.Fun info) => (name, info))) defs
    | (_, CodegenThingol.Datatypecons _)::_ => (SOME o ml_from_datatypes o filter_datatype) defs
    | (_, CodegenThingol.Datatype _)::_ => (SOME o ml_from_datatypes o filter_datatype) defs
    | (_, CodegenThingol.Class _)::_ => (SOME o ml_from_class o filter_class) defs
    | (_, CodegenThingol.Classmember _)::_ => (SOME o ml_from_class o filter_class) defs
    | [def] => ml_from_def def
    | defs => error ("illegal mutual dependencies: " ^ (commas o map fst) defs)
  end;

fun ml_annotators (nsp_dtcon, nsp_class, is_int_tyco) =
  let
    fun needs_type tyco =
      CodegenThingol.has_nsp tyco nsp_class
      orelse is_int_tyco tyco;
    fun is_cons c = CodegenThingol.has_nsp c nsp_dtcon;
  in (is_cons, needs_type) end;

in

fun ml_from_thingol target (nsp_dtcon, nsp_class, is_int_tyco) nspgrp =
  let
    fun ml_from_module resolv _ ((_, name), ps) =
      Pretty.chunks ([
        str ("structure " ^ name ^ " = "),
        str "struct",
        str ""
      ] @ separate (str "") ps @ [
        str "",
        str ("end; (* struct " ^ name ^ " *)")
      ]);
    val (is_cons, needs_type) = ml_annotators (nsp_dtcon, nsp_class, is_int_tyco);
    val serializer = abstract_serializer (target, nspgrp)
      "ROOT" (ml_from_defs (is_cons, needs_type), ml_from_module,
        abstract_validator reserved_ml, snd);
    fun eta_expander module const_syntax s =
      case const_syntax s
       of SOME ((i, _), _) => i
        | _ => if CodegenThingol.has_nsp s nsp_dtcon
               then case CodegenThingol.get_def module s
                of CodegenThingol.Datatypecons dtname =>
                  case CodegenThingol.get_def module dtname
                of CodegenThingol.Datatype (_, cs) =>
                  let val l = AList.lookup (op =) cs s |> the |> length
                  in if l >= 2 then l else 0 end
                else 0;
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
         (class_syntax, tyco_syntax, const_syntax))
  end;

fun mk_flat_ml_resolver names =
  let
    val mangler =
      NameMangler.empty
      |> fold_map (NameMangler.declare reserved_ml) names
      |-> (fn _ => I)
  in NameMangler.get reserved_ml mangler end;

fun ml_fun_datatype (nsp_dtcon, nsp_class, is_int_tyco) =
  ml_fun_datatyp (ml_annotators (nsp_dtcon, nsp_class, is_int_tyco));

end; (* local *)

local

fun hs_from_defs with_typs (from_prim, (class_syntax, tyco_syntax, const_syntax))
    resolver prefix defs =
  let
    val resolv = resolver "";
    val resolv_here = resolver prefix;
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
        |> flat
        |> from_sctxt
      end;
    fun hs_from_tycoexpr fxy (tyco, tys) =
      brackify fxy (str tyco :: map (hs_from_type BR) tys)
    and hs_from_type fxy (tycoexpr as tyco `%% tys) =
          (case tyco_syntax tyco
           of NONE =>
                hs_from_tycoexpr fxy (resolv tyco, tys)
            | SOME ((i, k), pr) =>
                if not (i <= length tys andalso length tys <= k)
                then error ("number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " to " ^ string_of_int k
                  ^ " expected")
                else pr fxy hs_from_type tys)
      | hs_from_type fxy (t1 `-> t2) =
          brackify_infix (1, R) fxy [
            hs_from_type (INFX (1, X)) t1,
            str "->",
            hs_from_type (INFX (1, R)) t2
          ]
      | hs_from_type fxy (ITyVar v) =
          str v;
    fun hs_from_sctxt_tycoexpr (sctxt, tycoexpr) =
      Pretty.block [hs_from_sctxt sctxt, hs_from_tycoexpr NOBR tycoexpr]
    fun hs_from_sctxt_type (sctxt, ty) =
      Pretty.block [hs_from_sctxt sctxt, hs_from_type NOBR ty]
    fun hs_from_expr fxy (e as IConst x) =
          hs_from_app fxy (x, [])
      | hs_from_expr fxy (e as (e1 `$ e2)) =
          (case CodegenThingol.unfold_const_app e
           of SOME x => hs_from_app fxy x
            | _ =>
                brackify fxy [
                  hs_from_expr NOBR e1,
                  hs_from_expr BR e2
                ])
      | hs_from_expr fxy (IVar v) =
          (str o String.implode o nth_map 0 Char.toLower o String.explode) v
      | hs_from_expr fxy (e as _ `|-> _) =
          let
            val (es, e) = CodegenThingol.unfold_abs e
          in
            brackify BR (
              str "\\"
              :: map (hs_from_expr BR o fst) es @ [
              str "->",
              hs_from_expr NOBR e
            ])
          end
      | hs_from_expr fxy (INum (n, _)) =
          (str o IntInf.toString) n
      | hs_from_expr fxy (IChar (c, _)) =
          (str o enclose "'" "'")
            (let val i = (Char.ord o the o Char.fromString) c
              in if i < 32 
                then Library.prefix "\\" c
                else c
              end)
      | hs_from_expr fxy (e as IAbs _) =
          let
            val (es, e) = CodegenThingol.unfold_abs e
          in
            brackify BR (
              str "\\"
              :: map (hs_from_expr BR o fst) es @ [
              str "->",
              hs_from_expr NOBR e
            ])
          end
      | hs_from_expr fxy (e as ICase ((_, [_]), _)) =
          let
            val (ps, body) = CodegenThingol.unfold_let e;
            fun mk_bind ((p, _), e) = (Pretty.block o Pretty.breaks) [
                hs_from_expr BR p,
                str "=",
                hs_from_expr NOBR e
              ];
          in Pretty.chunks [
            [str ("let"), Pretty.fbrk, map mk_bind ps |> Pretty.chunks] |> Pretty.block,
            [str ("in "), hs_from_expr NOBR body] |> Pretty.block
          ] end
      | hs_from_expr fxy (ICase (((de, _), bses), _)) =
          let
            fun mk_clause (se, be) =
              (Pretty.block o Pretty.breaks) [
                hs_from_expr NOBR se,
                str "->",
                hs_from_expr NOBR be
              ]
          in Pretty.block [
            str "case",
            Pretty.brk 1,
            hs_from_expr NOBR de,
            Pretty.brk 1,
            str "of",
            Pretty.fbrk,
            (Pretty.chunks o map mk_clause) bses
          ] end
    and hs_mk_app c es =
      (str o resolv) c :: map (hs_from_expr BR) es
    and hs_from_app fxy =
      from_app hs_mk_app hs_from_expr const_syntax fxy
    fun hs_from_funeqs (def as (name, _)) =
      let
        fun from_eq (args, rhs) =
          Pretty.block [
            (str o resolv_here) name,
            Pretty.block (map (fn p => Pretty.block [Pretty.brk 1, hs_from_expr BR p]) args),
            Pretty.brk 1,
            str ("="),
            Pretty.brk 1,
            hs_from_expr NOBR rhs
          ]
      in Pretty.chunks ((map from_eq o fst o snd o constructive_fun) def) end;
    fun hs_from_def (name, CodegenThingol.Undef) =
          error ("empty statement during serialization: " ^ quote name)
      | hs_from_def (name, CodegenThingol.Prim prim) =
          from_prim resolv_here (name, prim)
      | hs_from_def (name, CodegenThingol.Fun (def as (_, (sctxt, ty)))) =
          let
            val body = hs_from_funeqs (name, def);
          in if with_typs then
            Pretty.chunks [
              Pretty.block [
                (str o suffix " ::" o resolv_here) name,
                Pretty.brk 1,
                hs_from_sctxt_type (sctxt, ty)
              ],
              body
            ] |> SOME
          else SOME body end
      | hs_from_def (name, CodegenThingol.Typesyn (sctxt, ty)) =
          Pretty.block [
            str "type ",
            hs_from_sctxt_tycoexpr (sctxt, (resolv_here name, map (ITyVar o fst) sctxt)),
            str " =",
            Pretty.brk 1,
            hs_from_sctxt_type ([], ty)
          ] |> SOME
      | hs_from_def (name, CodegenThingol.Datatype (sctxt, constrs)) =
          let
            fun mk_cons (co, tys) =
              (Pretty.block o Pretty.breaks) (
                (str o resolv_here) co
                :: map (hs_from_type BR) tys
              )
          in
            (Pretty.block o Pretty.breaks) [
              str "data",
              hs_from_sctxt_tycoexpr (sctxt, (resolv_here name, map (ITyVar o fst) sctxt)),
              Pretty.block (separate (Pretty.block [Pretty.brk 1, str "| "]) (map mk_cons constrs))
            ]
          end |> SOME
      | hs_from_def (_, CodegenThingol.Datatypecons _) =
          NONE
      | hs_from_def (name, CodegenThingol.Class (supclasss, (v, membrs))) =
          let
            fun mk_member (m, (sctxt, ty)) =
              Pretty.block [
                str (resolv_here m ^ " ::"),
                Pretty.brk 1,
                hs_from_sctxt_type (sctxt, ty)
              ]
          in
            Pretty.block [
              str "class ",
              hs_from_sctxt [(v, supclasss)],
              str (resolv_here name ^ " " ^ v),
              str " where",
              Pretty.fbrk,
              Pretty.chunks (map mk_member membrs)
            ] |> SOME
          end
      | hs_from_def (_, CodegenThingol.Classmember _) =
          NONE
      | hs_from_def (_, CodegenThingol.Classinst (((clsname, (tyco, arity)), _), memdefs)) = 
          Pretty.block [
            str "instance ",
            hs_from_sctxt arity,
            str (resolv clsname ^ " "),
            hs_from_type BR (tyco `%% map (ITyVar o fst) arity),
            str " where",
            Pretty.fbrk,
            Pretty.chunks (map (fn (m, ((_, (eqs, ty)), _)) => hs_from_funeqs (m, (eqs, ty))) memdefs)
          ] |> SOME
      | hs_from_def (_, CodegenThingol.Classinstmember) =
          NONE
  in
    case map_filter (fn (name, def) => hs_from_def (name, def)) defs
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
      "Bool", "Integer", "Maybe", "True", "False", "Nothing", "Just", "not", "negate"
    ];
    fun hs_from_module resolv imps ((_, name), ps) =
      (Pretty.chunks) (
        str ("module " ^ name ^ " where")
        :: map (str o prefix "import qualified ") imps @ (
          str ""
          :: separate (str "") ps
      ));
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
  in
    (Scan.optional (OuterParse.name >> (fn "no_typs" => false | s => Scan.fail_with (fn _ => "illegal flag: " ^ quote s) true)) true
    #-> (fn with_typs => parse_multi_file ((K o K) NONE) "hs" (serializer with_typs)))
    >> (fn (seri) => fn (class_syntax, tyco_syntax, const_syntax) => seri 
         (class_syntax, tyco_syntax, const_syntax))
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
