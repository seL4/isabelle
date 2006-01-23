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
      ((string -> CodegenThingol.itype pretty_syntax option)
        * (string -> CodegenThingol.iexpr pretty_syntax option)
      -> string
      -> string list option
      -> CodegenThingol.module -> unit)
      * OuterParse.token list;
  val parse_syntax: (string -> 'b -> 'a * 'b) -> OuterParse.token list ->
    ('b -> 'a pretty_syntax * 'b) * OuterParse.token list;
  val parse_targetdef: (string -> string) -> string -> string;
  val pretty_list: string -> string -> int * string -> CodegenThingol.iexpr pretty_syntax;
  val serializers: {
    ml: string * (string * string * string -> serializer),
    haskell: string * (string -> serializer)
  }
end;

structure CodegenSerializer: CODEGEN_SERIALIZER =
struct

open CodegenThingolOp;
infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 5 `|->;
infixr 5 `|-->;

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

type 'a pretty_syntax = (int * int) * (fixity -> (fixity -> 'a -> Pretty.T) -> 'a list -> Pretty.T);

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

fun from_app mk_app from_expr const_syntax fxy (f, es) =
  let
    fun mk NONE es =
          brackify fxy (mk_app f es)
      | mk (SOME ((i, k), pr)) es =
          let
            val (es1, es2) = splitAt (i, es);
          in
            brackify fxy (pr fxy from_expr es1 :: map (from_expr BR) es2)
          end;
  in mk (const_syntax f) es end;

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
   of ([Pretty _], _) => error ("mixfix contains just one pretty element; either declare as " ^ quote "atom" ^ " or consider adding a break")
    | x => x;

fun parse_syntax_proto reader = OuterParse.$$$ "(" |-- (
       OuterParse.$$$ infixK  |-- OuterParse.nat >> (fn i => (parse_infix (INFX (i, X)), INFX (i, X)))
    || OuterParse.$$$ infixlK |-- OuterParse.nat >> (fn i => (parse_infix (INFX (i, L)), INFX (i, L)))
    || OuterParse.$$$ infixrK |-- OuterParse.nat >> (fn i => (parse_infix (INFX (i, R)), INFX (i, R)))
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

fun parse_named_quote resolv s =
  case Scan.finite Symbol.stopper (Scan.repeat (
         ($$ "`" |-- $$ "`")
      || ($$ "`" |-- Scan.repeat1 (Scan.unless ($$ "`") (Scan.one Symbol.not_eof))
            --| $$ "`" >> (resolv o implode))
      || Scan.repeat1
           (Scan.unless ($$ "`") (Scan.one Symbol.not_eof)) >> implode
    ) >> implode) (Symbol.explode s)
   of (p, []) => p
    | (p, ss) => error ("Malformed definition: " ^ quote p ^ " - " ^ commas ss);

fun parse_targetdef resolv = parse_named_quote resolv o newline_correct;


(* abstract serializer *)

type serializer = 
    string list list
    -> OuterParse.token list ->
    ((string -> CodegenThingol.itype pretty_syntax option)
      * (string -> CodegenThingol.iexpr pretty_syntax option)
    -> string
    -> string list option
    -> CodegenThingol.module -> unit)
    * OuterParse.token list;

fun abstract_serializer (target, nspgrp) (from_defs, from_module, validator)
  postprocess preprocess (tyco_syntax, const_syntax) name_root select module =
  let
    fun from_prim (name, prim) =
      case AList.lookup (op = : string * string -> bool) prim target
       of NONE => error ("no primitive definition for " ^ quote name)
        | SOME p => p;
  in
    module
    |> debug 3 (fn _ => "selecting submodule...")
    |> (if is_some select then (partof o the) select else I)
    |> tap (Pretty.writeln o pretty_deps)
    |> debug 3 (fn _ => "preprocessing...")
    |> preprocess
    |> debug 3 (fn _ => "serializing...")
    |> serialize (from_defs (from_prim, (tyco_syntax, const_syntax)))
         from_module validator nspgrp name_root
    |> postprocess
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

fun parse_single_file serializer =
  OuterParse.name
  >> (fn path => serializer (fn p => File.write (Path.unpack path) (Pretty.output p ^ "\n")));

fun parse_internal serializer =
  OuterParse.name
  >> (fn "-" => serializer (fn p => use_text Context.ml_output false (Pretty.output p))
       | _ => Scan.fail ());


(* list serializer *)

fun pretty_list thingol_nil thingol_cons (target_pred, target_cons) =
  let
    fun dest_cons (IApp (IApp (IConst (c, _), e1), e2)) =
          if (writeln (c ^ " - " ^ thingol_cons); c = thingol_cons)
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
       of (es, IConst (c, _)) => (writeln (string_of_int (length es));
            if c = thingol_nil
            then Pretty.gen_list "," "[" "]" (map (pr NOBR) (e1::es))
            else pretty_default fxy pr e1 e2)
        | _ => pretty_default fxy pr e1 e2;
  in ((2, 2), pretty_compact) end;



(** ML serializer **)

local

fun ml_from_defs (is_cons, needs_type)
  (from_prim, (tyco_syntax, const_syntax)) resolv defs =
  let
    fun chunk_defs ps =
      let
        val (p_init, p_last) = split_last ps
      in
        Pretty.chunks (p_init @ [Pretty.block ([p_last, str ";"])])
    end;
    fun ml_from_label s =
      let
        val s' = NameSpace.unpack s;
      in
        NameSpace.pack (Library.drop (length s' - 2, s'))
        |> translate_string (fn "_" => "__" | "." => "_" | c => c)
      end;
    fun ml_from_type fxy (IType (tyco, tys)) =
          (case tyco_syntax tyco
           of NONE =>
                let
                  val f' = (str o resolv) tyco
                in case map (ml_from_type BR) tys
                 of [] => f'
                  | [p] => Pretty.block [p, Pretty.brk 1, f']
                  | (ps as _::_) => Pretty.block [Pretty.list "(" ")" ps, Pretty.brk 1, f']
                end
            | SOME ((i, k), pr) =>
                if not (i <= length tys andalso length tys <= k)
                then error ("number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, " ^ string_of_int i ^ " to " ^ string_of_int k
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
      | ml_from_type _ (IVarT (v, [])) =
          str ("'" ^ v)
      | ml_from_type _ (IVarT (_, sort)) =
          "cannot serialize sort constrained type variable to ML: " ^ commas sort |> error
      | ml_from_type _ (IDictT fs) =
          Pretty.gen_list "," "{" "}" (
            map (fn (f, ty) =>
              Pretty.block [str (ml_from_label f ^ ": "), ml_from_type NOBR ty]) fs
          );
    fun ml_from_pat fxy (ICons ((f, ps), ty)) =
          (case const_syntax f
           of NONE => if length ps <= 1
                then
                  ps
                  |> map (ml_from_pat BR)
                  |> cons ((str o resolv) f)
                  |> brackify fxy
                else
                  ps
                  |> map (ml_from_pat BR)
                  |> Pretty.gen_list "," "(" ")"
                  |> single
                  |> cons ((str o resolv) f)
                  |> brackify fxy
            | SOME ((i, k), pr) =>
                if not (i <= length ps andalso length ps <= k)
                then error ("number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) ps ^ " given, " ^ string_of_int i ^ " to " ^ string_of_int k
                  ^ " expected")
                else pr fxy ml_from_expr (map iexpr_of_ipat ps))
      | ml_from_pat fxy (IVarP (v, ty)) =
          if needs_type ty
          then
            brackify fxy [
              str v,
              str ":",
              ml_from_type NOBR ty
            ]
          else
            str v
    and ml_from_expr fxy (e as IApp (e1, e2)) =
          (case (unfold_app e)
           of (e as (IConst (f, _)), es) =>
                ml_from_app fxy (f, es)
            | _ =>
                brackify fxy [
                  ml_from_expr NOBR e1,
                  ml_from_expr BR e2
                ])
      | ml_from_expr fxy (e as IConst (f, _)) =
          ml_from_app fxy (f, [])
      | ml_from_expr fxy (IVarE (v, _)) =
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
                ml_from_pat fxy p,
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
                ml_from_pat NOBR p,
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
      | ml_from_expr fxy (IInst _) =
          error "cannot serialize poly instant to ML"
      | ml_from_expr fxy (IDictE fs) =
          Pretty.gen_list "," "{" "}" (
            map (fn (f, e) =>
              Pretty.block [str (ml_from_label f ^ " = "), ml_from_expr NOBR e]) fs
          )
      | ml_from_expr fxy (ILookup ([], v)) =
          str v
      | ml_from_expr fxy (ILookup ([l], v)) =
          brackify fxy [
            str ("#" ^ (ml_from_label l)),
            str v
          ]
      | ml_from_expr fxy (ILookup (ls, v)) =
          brackify fxy [
            str ("("
              ^ (ls |> map ((fn s => "#" ^ s) o ml_from_label) |> foldr1 (fn (l, e) => l ^ " o " ^ e))
              ^ ")"),
            str v
          ]
      | ml_from_expr _ e =
          error ("dubious expression: " ^ (Pretty.output o pretty_iexpr) e)
    and ml_mk_app f es =
      if is_cons f andalso length es > 1
      then
        [(str o resolv) f, Pretty.gen_list " *" "(" ")" (map (ml_from_expr BR) es)]
      else
        (str o resolv) f :: map (ml_from_expr BR) es
    and ml_from_app fxy =
      from_app ml_mk_app ml_from_expr const_syntax fxy;
    fun ml_from_funs (ds as d::ds_tl) =
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
        val definer = the (fold check_args ds NONE);
        fun mk_eq definer f ty (pats, expr) =
          let
            val lhs = [str (definer ^ " " ^ f)]
                       @ (if null pats
                          then [str ":", ml_from_type NOBR ty]
                          else map (ml_from_pat BR) pats)
            val rhs = [str "=", ml_from_expr NOBR expr]
          in
            Pretty.block (separate (Pretty.brk 1) (lhs @ rhs))
          end
        fun mk_fun definer (f, Fun (eqs as eq::eq_tl, (_, ty))) =
          let
            val (pats_hd::pats_tl) = (fst o split_list) eqs;
            val shift = if null eq_tl then I else map (Pretty.block o single);
          in (Pretty.block o Pretty.fbreaks o shift) (
               mk_eq definer f ty eq
               :: map (mk_eq "|" f ty) eq_tl
             )
          end;
      in
        chunk_defs (
          mk_fun definer d
          :: map (mk_fun "and") ds_tl
        ) |> SOME
      end;
    fun ml_from_datatypes defs =
      let
        val defs' = List.mapPartial
          (fn (name, Datatype info) => SOME (name, info)
            | (name, Datatypecons _) => NONE
            | (name, def) => error ("datatype block containing illegal def: " ^ (Pretty.output o pretty_def) def)
          ) defs
        fun mk_cons (co, []) =
              str (resolv co)
          | mk_cons (co, tys) =
              Pretty.block (
                str (resolv co)
                :: str " of"
                :: Pretty.brk 1
                :: separate (Pretty.block [str " *", Pretty.brk 1]) (map (ml_from_type NOBR) tys)
              )
        fun mk_datatype definer (t, ((vs, cs), _)) =
          Pretty.block (
            str definer
            :: ml_from_type NOBR (t `%% map IVarT vs)
            :: str " ="
            :: Pretty.brk 1
            :: separate (Pretty.block [Pretty.brk 1, str "| "]) (map mk_cons cs)
          )
      in
        case defs'
         of d::ds_tl =>
            chunk_defs (
              mk_datatype "datatype " d
              :: map (mk_datatype "and ") ds_tl
            ) |> SOME
          | _ => NONE
      end
    fun ml_from_def (name, Undef) =
          error ("empty definition during serialization: " ^ quote name)
      | ml_from_def (name, Prim prim) =
          from_prim (name, prim)
      | ml_from_def (name, Typesyn (vs, ty)) =
        (map (fn (vname, []) => () | _ => error "can't serialize sort constrained type declaration to ML") vs;
          Pretty.block [
            str "type ",
            ml_from_type NOBR (name `%% map IVarT vs),
            str " =",
            Pretty.brk 1,
            ml_from_type NOBR ty,
            str ";"
            ]
          ) |> SOME
      | ml_from_def (name, Class _) =
          error ("can't serialize class declaration " ^ quote name ^ " to ML")
      | ml_from_def (_, Classmember _) =
          NONE
      | ml_from_def (name, Classinst _) =
          error ("can't serialize instance declaration " ^ quote name ^ " to ML")
  in (writeln ("ML defs " ^ (commas o map fst) defs); case defs
   of (_, Fun _)::_ => ml_from_funs defs
    | (_, Datatypecons _)::_ => ml_from_datatypes defs
    | (_, Datatype _)::_ => ml_from_datatypes defs
    | [def] => ml_from_def def)
  end;

in

fun ml_from_thingol target (nsp_dtcon, nsp_class, int_tyco) nspgrp =
  let
    val reserved_ml = ThmDatabase.ml_reserved @ [
      "bool", "int", "list", "true", "false"
    ];
    fun ml_from_module _ (name, ps) =
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
          orelse tyco = int_tyco
      | needs_type (IDictT _) =
          true
      | needs_type _ =
          false;
    fun is_cons c = has_nsp c nsp_dtcon;
    val serializer = abstract_serializer (target, nspgrp)
      (ml_from_defs (is_cons, needs_type), ml_from_module, abstract_validator reserved_ml);
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
      |> debug 3 (fn _ => "eliminating classes...")
      |> eliminate_classes;
  in
    (parse_single_file serializer
    || parse_internal serializer)
    >> (fn seri => fn (tyco_syntax, const_syntax) => seri 
         (preprocess const_syntax) (tyco_syntax, const_syntax))
  end;

end; (* local *)

local

fun hs_from_defs is_cons (from_prim, (tyco_syntax, const_syntax)) resolv defs =
  let
    fun upper_first s =
      let
        val (pr, b) = split_last (NameSpace.unpack s);
        val (c::cs) = String.explode b;
      in NameSpace.pack (pr @ [String.implode (Char.toUpper c :: cs)]) end;
    fun lower_first s =
      let
        val (pr, b) = split_last (NameSpace.unpack s);
        val (c::cs) = String.explode b;
      in NameSpace.pack (pr @ [String.implode (Char.toLower c :: cs)]) end;
    val resolv = fn s =>
      let
        val (prfix, base) = (split_last o NameSpace.unpack o resolv) s
      in
        NameSpace.pack (map upper_first prfix @ [base])
      end;
    fun resolv_const f =
      if NameSpace.is_qualified f
      then
        if is_cons f
        then (upper_first o resolv) f
        else (lower_first o resolv) f
      else
        f;
    fun hs_from_sctxt vs =
      let
        fun from_sctxt [] = str ""
          | from_sctxt vs =
              vs
              |> map (fn (v, cls) => str ((upper_first o resolv) cls ^ " " ^ lower_first v))
              |> Pretty.gen_list "," "(" ")"
              |> (fn p => Pretty.block [p, str " => "])
      in 
        vs
        |> map (fn (v, sort) => map (pair v) sort)
        |> Library.flat
        |> from_sctxt
      end;
    fun hs_from_type fxy ty =
      let
        fun from_itype fxy (IType (tyco, tys)) sctxt =
              (case tyco_syntax tyco
               of NONE =>
                    sctxt
                    |> fold_map (from_itype BR) tys
                    |-> (fn tyargs => pair (brackify fxy ((str o upper_first o resolv) tyco :: tyargs)))
                | SOME ((i, k), pr) =>
                    if not (i <= length tys andalso length tys <= k)
                    then error ("number of argument mismatch in customary serialization: "
                      ^ (string_of_int o length) tys ^ " given, " ^ string_of_int i ^ " to " ^ string_of_int k
                      ^ " expected")
                    else (pr fxy hs_from_type tys, sctxt))
          | from_itype fxy (IFun (t1, t2)) sctxt =
              sctxt
              |> from_itype (INFX (1, X)) t1
              ||>> from_itype (INFX (1, R)) t2
              |-> (fn (p1, p2) => pair (
                    brackify_infix (1, R) fxy [
                      p1,
                      str "->",
                      p2
                    ]
                  ))
          | from_itype fxy (IVarT (v, [])) sctxt =
              sctxt
              |> pair ((str o lower_first) v)
          | from_itype fxy (IVarT (v, sort)) sctxt =
              sctxt
              |> AList.default (op =) (v, [])
              |> AList.map_entry (op =) v (fold (insert (op =)) sort)
              |> pair ((str o lower_first) v)
          | from_itype fxy (IDictT _) _ =
              error "cannot serialize dictionary type to hs"
      in
        []
        |> from_itype fxy ty
        ||> hs_from_sctxt
        |> (fn (pty, pctxt) => Pretty.block [pctxt, pty])
      end;
    fun hs_from_pat fxy (ICons ((f, ps), _)) =
          (case const_syntax f
           of NONE =>
                ps
                |> map (hs_from_pat BR)
                |> cons ((str o resolv_const) f)
                |> brackify fxy
            | SOME ((i, k), pr) =>
                if not (i <= length ps andalso length ps <= k)
                then error ("number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) ps ^ " given, " ^ string_of_int i ^ " to " ^ string_of_int k
                  ^ " expected")
                else pr fxy hs_from_expr (map iexpr_of_ipat ps))
      | hs_from_pat fxy (IVarP (v, _)) =
          (str o lower_first) v
    and hs_from_expr fxy (e as IApp (e1, e2)) =
          (case (unfold_app e)
           of (e as (IConst (f, _)), es) =>
                hs_from_app fxy (f, es)
            | _ =>
                brackify fxy [
                  hs_from_expr NOBR e1,
                  hs_from_expr BR e2
                ])
      | hs_from_expr fxy (e as IConst (f, _)) =
          hs_from_app fxy (f, [])
      | hs_from_expr fxy (IVarE (v, _)) =
          (str o lower_first) v
      | hs_from_expr fxy (e as IAbs _) =
          let
            val (vs, body) = unfold_abs e
          in
            brackify fxy (
              str "\\"
              :: map (str o lower_first o fst) vs @ [
              str "->",
              hs_from_expr NOBR body
            ])
          end
      | hs_from_expr fxy (e as ICase (_, [_])) =
          let
            val (ps, body) = unfold_let e;
            fun mk_bind (p, e) = Pretty.block [
                hs_from_pat BR p,
                str " =",
                Pretty.brk 1,
                hs_from_expr NOBR e
              ];
          in Pretty.chunks [
            [str ("let"), Pretty.fbrk, map mk_bind ps |> Pretty.chunks] |> Pretty.block,
            [str ("in "), hs_from_expr NOBR body] |> Pretty.block
          ] end
      | hs_from_expr fxy (ICase (e, c::cs)) =
          let
            fun mk_clause definer (p, e) =
              Pretty.block [
                str definer,
                hs_from_pat NOBR p,
                str " ->",
                Pretty.brk 1,
                hs_from_expr NOBR e
              ]
          in brackify fxy (
            str "case"
            :: hs_from_expr NOBR e
            :: mk_clause "of " c
            :: map (mk_clause "| ") cs
          ) end
      | hs_from_expr fxy (IInst (e, _)) =
          hs_from_expr fxy e
      | hs_from_expr fxy (IDictE _) =
          error "cannot serialize dictionary expression to hs"
      | hs_from_expr fxy (ILookup _) =
          error "cannot serialize lookup expression to hs"
    and hs_mk_app f es =
      (str o resolv_const) f :: map (hs_from_expr BR) es
    and hs_from_app fxy =
      from_app hs_mk_app hs_from_expr const_syntax fxy;
    fun hs_from_def (name, Undef) =
          error ("empty statement during serialization: " ^ quote name)
      | hs_from_def (name, Prim prim) =
          from_prim (name, prim)
      | hs_from_def (name, Fun (eqs, (_, ty))) =
          let
            fun from_eq name (args, rhs) =
              Pretty.block [
                str (lower_first name),
                Pretty.block (map (fn p => Pretty.block [Pretty.brk 1, hs_from_pat BR p]) args),
                Pretty.brk 1,
                str ("="),
                Pretty.brk 1,
                hs_from_expr NOBR rhs
              ]
          in
            Pretty.chunks [
              Pretty.block [
                str (lower_first name ^ " ::"),
                Pretty.brk 1,
                hs_from_type NOBR ty
              ],
              Pretty.chunks (map (from_eq name) eqs)
            ] |> SOME
          end
      | hs_from_def (name, Typesyn (vs, ty)) =
          Pretty.block [
            str "type ",
            hs_from_sctxt vs,
            str (upper_first name),
            Pretty.block (map (fn (v, _) => str (" " ^ (lower_first) v)) vs),
            str " =",
            Pretty.brk 1,
            hs_from_type NOBR ty
          ] |> SOME
      | hs_from_def (name, Datatype ((vars, constrs), _)) =
          let
            fun mk_cons (co, tys) =
              (Pretty.block o Pretty.breaks) (
                str ((upper_first o resolv) co)
                :: map (hs_from_type NOBR) tys
              )
          in
            Pretty.block (
              str "data "
              :: hs_from_sctxt vars
              :: str (upper_first name)
              :: Pretty.block (map (fn (v, _) => str (" " ^ (lower_first) v)) vars)
              :: str " ="
              :: Pretty.brk 1
              :: separate (Pretty.block [Pretty.brk 1, str "| "]) (map mk_cons constrs)
            )
          end |> SOME
      | hs_from_def (_, Datatypecons _) =
          NONE
      | hs_from_def (name, Class ((supclasss, (v, membrs)), _)) =
          let
            fun mk_member (m, (_, ty)) =
              Pretty.block [
                str (resolv m ^ " ::"),
                Pretty.brk 1,
                hs_from_type NOBR ty
              ]
          in
            Pretty.block [
              str "class ",
              hs_from_sctxt (map (fn class => (v, [class])) supclasss),
              str ((upper_first name) ^ " " ^ v),
              str " where",
              Pretty.fbrk,
              Pretty.chunks (map mk_member membrs)
            ] |> SOME
          end
      | hs_from_def (name, Classmember _) =
          NONE
      | hs_from_def (_, Classinst ((clsname, (tyco, arity)), memdefs)) = 
          Pretty.block [
            str "instance ",
            hs_from_sctxt arity,
            str ((upper_first o resolv) clsname),
            str " ",
            hs_from_type NOBR (IType (tyco, (map (IVarT o rpair [] o fst)) arity)),
            str " where",
            Pretty.fbrk,
            Pretty.chunks (map (fn (m, funn) => hs_from_def (m, Fun funn) |> the) memdefs)
          ] |> SOME
  in
    case List.mapPartial (fn (name, def) => hs_from_def (name, def)) defs
     of [] => NONE
      | l => (SOME o Pretty.chunks o separate (str "")) l
  end;

in

fun hs_from_thingol target nsp_dtcon nspgrp =
  let
    val reserved_hs = [
      "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
      "import", "default", "forall", "let", "in", "class", "qualified", "data",
      "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
    ] @ [
      "Bool", "fst", "snd", "Integer", "True", "False", "negate"
    ];
    fun upper_first s =
      let
        val (pr, b) = split_last (NameSpace.unpack s);
        val (c::cs) = String.explode b;
      in NameSpace.pack (pr @ [String.implode (Char.toUpper c :: cs)]) end;
    fun hs_from_module _ (name, ps) =
      Pretty.block [
          str ("module " ^ (upper_first name) ^ " where"),
          Pretty.fbrk,
          Pretty.fbrk,
          Pretty.chunks (separate (str "") ps)
      ];
    fun is_cons c = has_nsp c nsp_dtcon;
    val serializer = abstract_serializer (target, nspgrp)
      (hs_from_defs is_cons, hs_from_module, abstract_validator reserved_hs);
    fun eta_expander const_syntax c =
      const_syntax c
      |> Option.map (fst o fst)
      |> the_default 0;
    fun preprocess const_syntax module =
      module
      |> tap (Pretty.writeln o pretty_deps)
      |> debug 3 (fn _ => "eta-expanding...")
      |> eta_expand (eta_expander const_syntax);
  in
    parse_single_file serializer
    >> (fn seri => fn (tyco_syntax, const_syntax) => seri 
         (preprocess const_syntax) (tyco_syntax, const_syntax))
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
