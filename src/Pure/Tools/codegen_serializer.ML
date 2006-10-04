(*  Title:      Pure/Tools/codegen_serializer.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol") to
target languages (like SML or Haskell).
*)

signature CODEGEN_SERIALIZER =
sig
  include BASIC_CODEGEN_THINGOL;
  val parse_serializer: string
    -> OuterParse.token list
        -> (theory -> string list option -> CodegenThingol.module -> unit)
             * OuterParse.token list
  val eval_verbose: bool ref;
  val eval_term: theory ->
    (string * 'a option ref) * CodegenThingol.iterm -> CodegenThingol.module
    -> 'a;
  val mk_flat_ml_resolver: string list -> string -> string;
  val ml_fun_datatype:
    theory -> (string -> string)
    -> ((string * ((iterm list * iterm) list * CodegenThingol.typscheme)) list -> Pretty.T)
        * ((string * ((vname * sort) list * (string * itype list) list)) list -> Pretty.T);
  val const_has_serialization: theory -> string list -> string -> bool;
  val tyco_has_serialization: theory -> string list -> string -> bool;
  val check_serializer: string -> unit;
  val add_syntax_class:
    string -> string -> string * (string * string) list  -> theory -> theory;
  val add_syntax_inst: string -> (string * string) -> theory -> theory;
  val parse_syntax_tyco: (theory
           -> CodegenConsts.const list * (string * typ) list
              -> string
                 -> CodegenNames.tyco
                    -> typ list -> CodegenThingol.itype list)
          -> Symtab.key
             -> xstring
                -> OuterParse.token list
                   -> (theory -> theory) * OuterParse.token list;
  val parse_syntax_const: (theory
           -> CodegenConsts.const list * (string * typ) list
              -> string
                 -> CodegenNames.const
                    -> term list -> CodegenThingol.iterm list)
          -> Symtab.key
             -> string
                -> OuterParse.token list
                   -> (theory -> theory) * OuterParse.token list;
  val add_pretty_list: string -> string -> string -> (Pretty.T list -> Pretty.T)
   -> ((string -> string) * (string -> string)) option -> int * string
   -> theory -> theory;
  val add_pretty_ml_string: string -> string -> string -> string
   -> (string -> string) -> (string -> string) -> string -> theory -> theory;
  val add_undefined: string -> string -> string -> theory -> theory;
end;

structure CodegenSerializer: CODEGEN_SERIALIZER =
struct

open BasicCodegenThingol;
val tracing = CodegenThingol.tracing;

(** precedences **)

datatype lrx = L | R | X;

datatype fixity =
    BR
  | NOBR
  | INFX of (int * lrx);

type 'a pretty_syntax = int * (fixity -> (fixity -> 'a -> Pretty.T)
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

fun gen_brackify _ [p] = p
  | gen_brackify true (ps as _::_) = Pretty.enclose "(" ")" ps
  | gen_brackify false (ps as _::_) = Pretty.block ps;

fun brackify fxy_ctxt ps =
  gen_brackify (eval_fxy BR fxy_ctxt) (Pretty.breaks ps);

fun brackify_infix infx fxy_ctxt ps =
  gen_brackify (eval_fxy (INFX infx) fxy_ctxt) (Pretty.breaks ps);

fun from_app mk_app from_expr const_syntax fxy (const as (c, (_, ty)), es) =
  case const_syntax c
   of NONE => brackify fxy (mk_app c es)
    | SOME (i, pr) =>
        let
          val k = if i < 0 then (length o fst o CodegenThingol.unfold_fun) ty else i
        in if k <= length es
          then case chop i es of (es1, es2) =>
            brackify fxy (pr fxy from_expr es1 :: map (from_expr BR) es2)
          else from_expr fxy (CodegenThingol.eta_expand (const, es) i)
        end;


(** user-defined syntax **)

(* theory data *)

type target_data = {
  syntax_class: ((string * (string -> string option)) * stamp) Symtab.table,
  syntax_inst: unit Symtab.table,
  syntax_tyco: (itype pretty_syntax * stamp) Symtab.table,
  syntax_const: (iterm pretty_syntax * stamp) Symtab.table
};

fun merge_target_data
  ({ syntax_class = syntax_class1, syntax_inst = syntax_inst1,
       syntax_tyco = syntax_tyco1, syntax_const = syntax_const1 },
   { syntax_class = syntax_class2, syntax_inst = syntax_inst2,
       syntax_tyco = syntax_tyco2, syntax_const = syntax_const2 }) =
  { syntax_class = Symtab.merge (eq_snd (op =)) (syntax_class1, syntax_class2),
    syntax_inst = Symtab.merge (op =) (syntax_inst1, syntax_inst2),
    syntax_tyco = Symtab.merge (eq_snd (op =)) (syntax_tyco1, syntax_tyco2),
    syntax_const = Symtab.merge (eq_snd (op =)) (syntax_const1, syntax_const2) } : target_data;

structure CodegenSerializerData = TheoryDataFun
(struct
  val name = "Pure/codegen_serializer";
  type T = target_data Symtab.table;
  val empty =
      Symtab.empty
      |> fold (fn target =>
           Symtab.update (target,
             { syntax_class = Symtab.empty, syntax_inst = Symtab.empty,
               syntax_tyco = Symtab.empty, syntax_const = Symtab.empty })
         ) ["SML", "Haskell"] : T;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.join (K merge_target_data);
  fun print _ _ = ();
end);

fun has_serialization f thy targets name =
  forall (
    is_some o (fn tab => Symtab.lookup tab name) o f o the
      o (Symtab.lookup ((CodegenSerializerData.get) thy))
  ) targets;

val tyco_has_serialization = has_serialization #syntax_tyco;
val const_has_serialization = has_serialization #syntax_const;

fun serialize thy seri target cs =
  let
    val data = CodegenSerializerData.get thy;
    val target_data =
      (the oo Symtab.lookup) data target;
    val syntax_class = #syntax_class target_data;
    val syntax_inst = #syntax_inst target_data;
    val syntax_tyco = #syntax_tyco target_data;
    val syntax_const = #syntax_const target_data;
    fun fun_of syntax = (Option.map fst oo Symtab.lookup) syntax;
  in
    seri (fun_of syntax_class, fun_of syntax_tyco, fun_of syntax_const)
      (Symtab.keys syntax_class @ Symtab.keys syntax_inst
         @ Symtab.keys syntax_tyco @ Symtab.keys syntax_const, cs)
  end;

val _ = Context.add_setup CodegenSerializerData.init;

val (atomK, infixK, infixlK, infixrK) =
  ("target_atom", "infix", "infixl", "infixr");
val _ = OuterSyntax.add_keywords [atomK, infixK, infixlK, infixrK];


(* syntax parser *)

val str = setmp print_mode [] Pretty.str;

datatype 'a mixfix =
    Arg of fixity
  | Pretty of Pretty.T
  | Quote of 'a;

fun fillin_mixfix fxy_this ms fxy_ctxt pr args =
  let
    fun fillin [] [] =
          []
      | fillin (Arg fxy :: ms) (a :: args) =
          pr fxy a :: fillin ms args
      | fillin (Pretty p :: ms) args =
          p :: fillin ms args
      | fillin (Quote q :: ms) args =
          pr BR q :: fillin ms args
      | fillin [] _ =
          error ("Inconsistent mixfix: too many arguments")
      | fillin _ [] =
          error ("Inconsistent mixfix: too less arguments");
  in gen_brackify (eval_fxy fxy_this fxy_ctxt) (fillin ms args) end;

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

fun parse_syntax num_args reader =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    fun parse_nonatomic s ctxt =
      case parse_mixfix reader s ctxt
       of ([Pretty _], _) =>
            error ("Mixfix contains just one pretty element; either declare as "
              ^ quote atomK ^ " or consider adding a break")
        | x => x;
    val parse = (
           OuterParse.$$$ infixK  |-- OuterParse.nat
            >> (fn i => (parse_infix (INFX (i, X)), INFX (i, X)))
        || OuterParse.$$$ infixlK |-- OuterParse.nat
            >> (fn i => (parse_infix (INFX (i, L)), INFX (i, L)))
        || OuterParse.$$$ infixrK |-- OuterParse.nat
            >> (fn i => (parse_infix (INFX (i, R)), INFX (i, R)))
        || OuterParse.$$$ atomK |-- pair (parse_mixfix reader, NOBR)
        || pair (parse_nonatomic, BR)
      ) -- OuterParse.string >> (fn ((p, fxy), s) => (p s, fxy));
    fun mk fixity mfx ctxt =
      let
        val i = (length o List.filter is_arg) mfx;
        val _ = if i > num_args ctxt then error "Too many arguments in code syntax" else ();
      in ((i, fillin_mixfix fixity mfx), ctxt) end;
  in
    parse
    #-> (fn (mfx_reader, fixity) =>
      pair (mfx_reader #-> (fn mfx => (mk fixity mfx)))
    )
  end;



(** generic abstract serializer **)

val nsp_module = CodegenNames.nsp_module;
val nsp_class = CodegenNames.nsp_class;
val nsp_tyco = CodegenNames.nsp_tyco;
val nsp_inst = CodegenNames.nsp_inst;
val nsp_fun = CodegenNames.nsp_fun;
val nsp_classop = CodegenNames.nsp_classop;
val nsp_dtco = CodegenNames.nsp_dtco;
val nsp_eval = CodegenNames.nsp_eval;

fun abstract_serializer (target, nspgrp) name_root (from_defs, from_module, validator, postproc)
    postprocess (class_syntax, tyco_syntax, const_syntax)
    (drop: string list, select) code =
  let
    fun from_module' resolv imps ((name_qual, name), defs) =
      from_module resolv imps ((name_qual, name), defs)
      |> postprocess (resolv name_qual);
  in
    code
    |> tracing (fn _ => "dropping shadowed defintions...")
    |> CodegenThingol.delete_garbage drop
    |> tracing (fn _ => "projecting...")
    |> (if is_some select then (CodegenThingol.project_module o the) select else I)
    |> tracing (fn _ => "serializing...")
    |> CodegenThingol.serialize (from_defs (class_syntax, tyco_syntax, const_syntax))
         from_module' validator postproc nspgrp name_root
    |> K ()
  end;

fun abstract_validator keywords name =
  let
    fun replace_invalid c =  (*FIXME*)
      if Symbol.is_ascii_letter c orelse Symbol.is_ascii_digit c orelse c = "'"
      andalso not (NameSpace.separator = c)
      then c
      else "_"
    fun suffix_it name=
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

fun parse_stdout serializer =
  OuterParse.name
  >> (fn "_" => serializer
        (fn "" => (fn p => (Pretty.writeln p; NONE))
          | _ => SOME)
       | _ => Scan.fail ());

fun constructive_fun (name, (eqs, ty)) =
  let
    val is_cons = CodegenNames.has_nsp CodegenNames.nsp_dtco;
    fun check_eq (eq as (lhs, rhs)) =
      if forall (CodegenThingol.is_pat is_cons) lhs
      then SOME eq
      else (warning ("In function " ^ quote name ^ ", throwing away one "
        ^ "non-executable function clause"); NONE)
  in case map_filter check_eq eqs
   of [] => error ("In function " ^ quote name ^ ", no "
        ^ "executable function clauses found")
    | eqs => (name, (eqs, ty))
  end;

fun make_ctxt names = (fold (fn name => Symtab.update_new (name, name)) names Symtab.empty,
  Name.make_context names);

fun intro_ctxt names (namemap, namectxt) =
  let
    val (names', namectxt') = Name.variants names namectxt;
    val namemap' = fold2 (curry Symtab.update) names names' namemap;
  in (namemap', namectxt') end;

fun lookup_ctxt (namemap, _) name = case Symtab.lookup namemap name
 of SOME name' => name'
  | NONE => error ("invalid name in context: " ^ quote name);



(** generic list and string serializers **)

fun implode_list c_nil c_cons e =
  let
    fun dest_cons (IConst (c, _) `$ e1 `$ e2) =
          if c = c_cons
          then SOME (e1, e2)
          else NONE
      | dest_cons  _ = NONE;
    val (es, e') = CodegenThingol.unfoldr dest_cons e;
  in case e'
   of IConst (c, _) => if c = c_nil then SOME es else NONE
    | _ => NONE
  end;

fun implode_string mk_char mk_string es =
  if forall (fn IChar _ => true | _ => false) es
  then (SOME o str o mk_string o implode o map (fn IChar (c, _) => mk_char c)) es
  else NONE;

fun pretty_ml_string c_nil c_cons mk_char mk_string target_implode =
  let
    fun pretty fxy pr [e] =
      case implode_list c_nil c_cons e
       of SOME es => (case implode_string mk_char mk_string es
           of SOME p => p
            | NONE => Pretty.block [str target_implode, Pretty.brk 1, pr BR e])
        | NONE => Pretty.block [str target_implode, Pretty.brk 1, pr BR e]
  in (1, pretty) end;

fun pretty_list c_nil c_cons mk_list mk_char_string (target_fxy, target_cons) =
  let
    fun default fxy pr e1 e2 =
      brackify_infix (target_fxy, R) fxy [
        pr (INFX (target_fxy, X)) e1,
        str target_cons,
        pr (INFX (target_fxy, R)) e2
      ];
    fun pretty fxy pr [e1, e2] =
      case Option.map (cons e1) (implode_list c_nil c_cons e2)
       of SOME es =>
            (case mk_char_string
             of SOME (mk_char, mk_string) =>
                  (case implode_string mk_char mk_string es
                   of SOME p => p
                    | NONE => mk_list (map (pr NOBR) es))
              | NONE => mk_list (map (pr NOBR) es))
        | NONE => default fxy pr e1 e2;
  in (2, pretty) end;



(** ML serializer **)

local

val reserved_ml' = [
  "bool", "int", "list", "unit", "option", "true", "false", "not", "NONE", "SOME",
  "o", "string", "char", "String", "Term"
];

fun ml_expr_seri (tyco_syntax, const_syntax) resolv =
  let
    val is_cons = CodegenNames.has_nsp CodegenNames.nsp_dtco;
    fun first_upper s =
      implode (nth_map 0 (Symbol.to_ascii_upper) (explode s));
    fun ml_from_dictvar v = 
      first_upper v ^ "_";
    val ml_from_label =
      str o translate_string (fn "." => "__" | c => c);
    fun ml_from_tyvar (v, []) =
          str "()"
      | ml_from_tyvar (v, sort) =
          let
            fun mk_class class =
              str (prefix "'" v ^ " " ^ resolv class);
          in
            Pretty.block [
              str "(",
              (str o ml_from_dictvar) v,
              str ":",
              case sort
               of [class] => mk_class class
                | _ => Pretty.enum " *" "" "" (map mk_class sort),
            str ")"
            ]
          end;
    fun ml_from_insts fxy lss =
      let
        fun from_label l =
          Pretty.block [str "#",
            if (is_some o Int.fromString) l then str l
            else ml_from_label l
          ];
        fun from_lookup fxy [] p =
              p
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
        fun from_inst fxy (Instance (inst, lss)) =
              brackify fxy (
                (str o resolv) inst
                :: map (ml_from_insts BR) lss
              )
          | from_inst fxy (Context (classes, (v, ~1))) =
              from_lookup BR classes
                ((str o ml_from_dictvar) v)
          | from_inst fxy (Context (classes, (v, i))) =
              from_lookup BR (classes @ [string_of_int (i+1)])
                ((str o ml_from_dictvar) v)
      in case lss
       of [] => str "()"
        | [ls] => from_inst fxy ls
        | lss => (Pretty.list "(" ")" o map (from_inst NOBR)) lss
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
            | SOME (i, pr) =>
                if not (i = length tys)
                then error ("Number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " expected")
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
    fun ml_from_expr var_ctxt fxy (e as IConst x) =
          ml_from_app var_ctxt fxy (x, [])
      | ml_from_expr var_ctxt fxy (IVar v) =
          str (lookup_ctxt var_ctxt v)
      | ml_from_expr var_ctxt fxy (e as e1 `$ e2) =
          (case CodegenThingol.unfold_const_app e
           of SOME x => ml_from_app var_ctxt fxy x
            | NONE =>
                brackify fxy [
                  ml_from_expr var_ctxt NOBR e1,
                  ml_from_expr var_ctxt BR e2
                ])
      | ml_from_expr var_ctxt fxy (e as _ `|-> _) =
          let
            val (es, e') = CodegenThingol.unfold_abs e;
            val vs = fold CodegenThingol.add_varnames (map fst es) [];
            val var_ctxt' = intro_ctxt vs var_ctxt;
            fun mk_abs (e, ty) = (Pretty.block o Pretty.breaks) [
                str "fn",
                ml_from_expr var_ctxt' NOBR e,
                str "=>"
              ];
          in brackify BR (map mk_abs es @ [ml_from_expr var_ctxt' NOBR e']) end
      | ml_from_expr var_ctxt fxy (INum (n, _)) =
          brackify BR [
            (str o IntInf.toString) n,
            str ":",
            str "IntInf.int"
          ]
      | ml_from_expr var_ctxt _ (IChar (c, _)) =
          (str o prefix "#" o quote)
            (let val i = ord c
              in if i < 32
                then prefix "\\" (string_of_int i)
                else c
              end)
      | ml_from_expr var_ctxt fxy (e as ICase ((_, [_]), _)) =
          let
            val (ves, be) = CodegenThingol.unfold_let e;
            fun mk_val ((ve, vty), se) var_ctxt =
              let
                val vs = CodegenThingol.add_varnames ve [];
                val var_ctxt' = intro_ctxt vs var_ctxt;
              in
                (Pretty.block [
                  (Pretty.block o Pretty.breaks) [
                    str "val",
                    ml_from_expr var_ctxt' NOBR ve,
                    str "=",
                    ml_from_expr var_ctxt NOBR se
                  ],
                  str ";"
                ], var_ctxt')
              end
            val (binds, var_ctxt') = fold_map mk_val ves var_ctxt;
          in Pretty.chunks [
            [str ("let"), Pretty.fbrk, binds |> Pretty.chunks] |> Pretty.block,
            [str ("in"), Pretty.fbrk, ml_from_expr var_ctxt' NOBR be] |> Pretty.block,
            str ("end")
          ] end
      | ml_from_expr var_ctxt fxy (ICase (((de, dty), bse::bses), _)) =
          let
            fun mk_clause definer (se, be) =
              let
                val vs = CodegenThingol.add_varnames se [];
                val var_ctxt' = intro_ctxt vs var_ctxt;
              in
                (Pretty.block o Pretty.breaks) [
                  str definer,
                  ml_from_expr var_ctxt' NOBR se,
                  str "=>",
                  ml_from_expr var_ctxt' NOBR be
                ]
              end
          in brackify fxy (
            str "(case"
            :: ml_from_expr var_ctxt NOBR de
            :: mk_clause "of" bse
            :: map (mk_clause "|") bses
            @ [str ")"]
          ) end
      | ml_from_expr var_ctxt _ e =
          error ("Dubious expression: " ^ (Pretty.output o CodegenThingol.pretty_iterm) e)
    and ml_mk_app var_ctxt f es =
      if is_cons f andalso length es > 1 then
        [(str o resolv) f, Pretty.enum "," "(" ")" (map (ml_from_expr var_ctxt BR) es)]
      else
        (str o resolv) f :: map (ml_from_expr var_ctxt BR) es
    and ml_from_app var_ctxt fxy (app_expr as ((c, (lss, ty)), es)) =
      case if is_cons c then [] else (map (ml_from_insts BR) o filter_out null) lss
       of [] =>
            from_app (ml_mk_app var_ctxt) (ml_from_expr var_ctxt) const_syntax fxy app_expr
        | lss =>
            if (is_none o const_syntax) c then
              brackify fxy (
                (str o resolv) c
                :: (lss
                @ map (ml_from_expr var_ctxt BR) es)
              )
            else error ("Can't apply user defined serialization for function expecting dicitonaries: " ^ quote c)
  in (ml_from_dictvar, ml_from_label, ml_from_tyvar, ml_from_insts,
    ml_from_tycoexpr, ml_from_type, ml_from_expr) end;

fun ml_fun_datatype init_ctxt (tyco_syntax, const_syntax) resolv =
  let
    val is_cons = CodegenNames.has_nsp CodegenNames.nsp_dtco;
    val (ml_from_dictvar, ml_from_label, ml_from_tyvar, ml_from_insts, ml_from_tycoexpr, ml_from_type, ml_from_expr) =
      ml_expr_seri (tyco_syntax, const_syntax) resolv;
    fun chunk_defs ps =
      let
        val (p_init, p_last) = split_last ps
      in
        Pretty.chunks (p_init @ [Pretty.block ([p_last, str ";"])])
      end;
    fun eta_expand_poly_fun (funn as (_, (_::_, _))) =
          funn
      | eta_expand_poly_fun (funn as (eqs, tysm as (_, ty))) =
          let
            fun no_eta (_::_, _) = I
              | no_eta (_, _ `|-> _) = I
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
            else (map (fn ([], rhs) => ([IVar "x"], rhs `$ IVar "x")) eqs, tysm)
          end;
    fun ml_from_funs (defs as def::defs_tl) =
      let
        fun mk_definer [] [] = "val"
          | mk_definer (_::_) _ = "fun"
          | mk_definer [] vs = if (null o filter_out (null o snd)) vs then "val" else "fun";
        fun check_args (_, ((pats, _)::_, (vs, _))) NONE =
              SOME (mk_definer pats vs)
          | check_args (_, ((pats, _)::_, (vs, _))) (SOME definer) =
              if mk_definer pats vs = definer
              then SOME definer
              else error ("Mixing simultaneous vals and funs not implemented");
        fun mk_fun definer (name, (eqs as eq::eq_tl, (raw_vs, ty))) =
          let
            val vs = filter_out (null o snd) raw_vs;
            val shift = if null eq_tl then I else
              map (Pretty.block o single o Pretty.block o single);
            fun mk_eq definer (pats, expr) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o resolv) c) (fold CodegenThingol.add_constnames (expr :: pats) []);
                val vars = fold CodegenThingol.add_unbound_varnames (expr :: pats) [];
                val var_ctxt = init_ctxt
                  |> intro_ctxt consts
                  |> intro_ctxt vars;
              in
                (Pretty.block o Pretty.breaks) (
                  [str definer, (str o resolv) name]
                  @ (if null pats andalso null vs
                       andalso not (ty = ITyVar "_")(*for evaluation*)
                     then [str ":", ml_from_type NOBR ty]
                     else
                       map ml_from_tyvar vs
                       @ map (ml_from_expr var_ctxt BR) pats)
               @ [str "=", ml_from_expr var_ctxt NOBR expr]
                )
              end
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
                Pretty.enum " *" "" "" (map (ml_from_type (INFX (2, L))) tys)
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

fun ml_from_defs init_ctxt
    (_, tyco_syntax, const_syntax) resolver prefx defs =
  let
    val resolv = resolver prefx;
    val (ml_from_dictvar, ml_from_label, ml_from_tyvar, ml_from_insts, ml_from_tycoexpr, ml_from_type, ml_from_expr) =
      ml_expr_seri (tyco_syntax, const_syntax) resolv;
    val (ml_from_funs, ml_from_datatypes) =
      ml_fun_datatype init_ctxt (tyco_syntax, const_syntax) resolv;
    val filter_datatype =
      map_filter
        (fn (name, CodegenThingol.Datatype info) => SOME (name, info)
          | (name, CodegenThingol.Datatypecons _) => NONE
          | (name, def) => error ("Datatype block containing illegal def: "
                ^ (Pretty.output o CodegenThingol.pretty_def) def));
    fun filter_class defs =
      case map_filter
        (fn (name, CodegenThingol.Class info) => SOME (name, info)
          | (name, CodegenThingol.Classmember _) => NONE
          | (name, def) => error ("Class block containing illegal def: "
                ^ (Pretty.output o CodegenThingol.pretty_def) def)) defs
       of [class] => class
        | _ => error ("Class block without class: " ^ (commas o map (quote o fst)) defs)
    fun ml_from_class (name, (supclasses, (v, membrs))) =
      let
        val w = ml_from_dictvar v;
        fun from_supclass class =
          Pretty.block [
            ml_from_label class,
            str ":",
            Pretty.brk 1,
            str ("'" ^ v),
            Pretty.brk 1,
            (str o resolv) class
          ];
        fun from_membr (m, ty) =
          Pretty.block [
            (ml_from_label o suffix "_" o NameSpace.base) m,
            str ":",
            Pretty.brk 1,
            ml_from_type NOBR ty
          ];
        fun from_membr_fun (m, _) =
          (Pretty.block o Pretty.breaks) [
            str "fun",
            (str o resolv) m,
            Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ resolv name)],
            str "=",
            Pretty.block [str "#", (ml_from_label o suffix "_" o NameSpace.base) m],
            str (w ^ ";")
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
    fun ml_from_def (name, CodegenThingol.Typesyn (vs, ty)) =
        (map (fn (vname, []) => () | _ =>
            error "Can't serialize sort constrained type declaration to ML") vs;
          Pretty.block [
            str "type ",
            ml_from_tycoexpr NOBR (name, map (ITyVar o fst) vs),
            str " =",
            Pretty.brk 1,
            ml_from_type NOBR ty,
            str ";"
            ]
       ) |> SOME
      | ml_from_def (name, CodegenThingol.Classinst ((class, (tyco, arity)), (suparities, memdefs))) =
          let
            val definer = if null arity then "val" else "fun"
            fun from_supclass (supclass, (supinst, lss)) =
              (Pretty.block o Pretty.breaks) [
                ml_from_label supclass,
                str "=",
                ml_from_insts NOBR [Instance (supinst, lss)]
              ];
            fun from_memdef (m, e) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o resolv) c) (CodegenThingol.add_constnames e []);
                val var_ctxt = init_ctxt
                  |> intro_ctxt consts;
              in
                (Pretty.block o Pretty.breaks) [
                  (ml_from_label o suffix "_" o NameSpace.base) m,
                  str "=",
                  ml_from_expr var_ctxt NOBR e
                ]
              end;
            fun mk_corp rhs =
              (Pretty.block o Pretty.breaks) (
                str definer
                :: (str o resolv) name
                :: map ml_from_tyvar arity
                @ [str "=", rhs]
              );
            fun mk_memdefs supclassexprs memdefs =
              (mk_corp o Pretty.block o Pretty.breaks) [
                Pretty.enum "," "{" "}" (supclassexprs @ memdefs),
                str ":",
                ml_from_tycoexpr NOBR (class, [tyco `%% map (ITyVar o fst) arity])
              ];
          in
            mk_memdefs (map from_supclass suparities) (map from_memdef memdefs) |> SOME
          end
      | ml_from_def (name, def) = error ("Illegal definition for " ^ quote name ^ ": " ^
          (Pretty.output o CodegenThingol.pretty_def) def);
  in case defs
   of (_, CodegenThingol.Fun _)::_ => ((*writeln "FUN";*) (SOME o ml_from_funs o map (fn (name, CodegenThingol.Fun info) => (name, info))) defs)
    | (_, CodegenThingol.Datatypecons _)::_ => ((*writeln "DTCO";*) (SOME o ml_from_datatypes o filter_datatype) defs)
    | (_, CodegenThingol.Datatype _)::_ => ((*writeln "DT";*) (SOME o ml_from_datatypes o filter_datatype) defs)
    | (_, CodegenThingol.Class _)::_ => (SOME o ml_from_class o filter_class) defs
    | (_, CodegenThingol.Classmember _)::_ => (SOME o ml_from_class o filter_class) defs
    | [def] => ml_from_def def
    | defs => error ("Illegal mutual dependencies: " ^ (commas o map fst) defs)
  end;

fun ml_serializer root_name target nspgrp =
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
    fun postproc (shallow, n) =
      let
        fun ch_first f = String.implode o nth_map 0 f o String.explode;
      in if shallow = CodegenNames.nsp_dtco
        then ch_first Char.toUpper n
        else n
      end;
  in abstract_serializer (target, nspgrp)
    root_name (ml_from_defs (make_ctxt ((ThmDatabase.ml_reserved @ reserved_ml'))), ml_from_module,
     abstract_validator (ThmDatabase.ml_reserved @ reserved_ml'), postproc) end;

in

val ml_fun_datatype = fn thy =>
  let
    val target = "SML";
    val data = CodegenSerializerData.get thy;
    val target_data =
      (the oo Symtab.lookup) data target;
    val syntax_tyco = #syntax_tyco target_data;
    val syntax_const = #syntax_const target_data;
    fun fun_of syntax = (Option.map fst oo Symtab.lookup) syntax;
  in ml_fun_datatype (make_ctxt (ThmDatabase.ml_reserved @ reserved_ml')) (fun_of syntax_tyco, fun_of syntax_const) end;

fun ml_from_thingol target =
  let
    val serializer = ml_serializer "ROOT" target [[nsp_module], [nsp_class, nsp_tyco],
      [nsp_fun, nsp_dtco, nsp_class, nsp_classop, nsp_inst]]
    val parse_multi =
      OuterParse.name
      #-> (fn "dir" =>
               parse_multi_file
                 (K o SOME o str o suffix ";" o prefix "val _ = use "
                  o quote o suffix ".ML" o translate_string (fn "." => "/" | s => s)) "ML" serializer
            | _ => Scan.fail ());
  in
    parse_multi
    || parse_internal serializer
    || parse_stdout serializer
    || parse_single_file serializer
  end;

val eval_verbose = ref false;

fun eval_term thy ((ref_name, reff), e) code =
  let
    val (val_name, code') = CodegenThingol.add_eval_def (nsp_eval, e) code;
    val struct_name = "EVAL";
    fun output p = if !eval_verbose then (Pretty.writeln p; Pretty.output p)
      else Pretty.output p;
    val target = "SML";
    val data = CodegenSerializerData.get thy;
    val target_data =
      (the oo Symtab.lookup) data target;
    val syntax_tyco = #syntax_tyco target_data;
    val syntax_const = #syntax_const target_data;
    fun fun_of syntax = (Option.map fst oo Symtab.lookup) syntax;
    val serializer = ml_serializer struct_name "SML" [[nsp_module], [nsp_class, nsp_tyco],
      [nsp_fun, nsp_dtco, nsp_class, nsp_classop, nsp_inst], [nsp_eval]]
      (fn "" => (fn p => (use_text Context.ml_output (!eval_verbose) (output p); NONE))
        | _ => SOME) (K NONE, fun_of syntax_tyco, fun_of syntax_const)
        ((Symtab.keys (#syntax_tyco target_data) @ Symtab.keys (#syntax_const target_data)), SOME [NameSpace.pack [nsp_eval, val_name]]);
    val _ = serializer code';
    val val_name_struct = NameSpace.append struct_name val_name;
    val _ = reff := NONE;
    val _ = use_text Context.ml_output (!eval_verbose) ("val _ = (" ^ ref_name ^ " := SOME (" ^ val_name_struct ^ "))");
  in case !reff
   of NONE => error ("Could not retrieve value of ML reference " ^ quote ref_name
        ^ " (reference probably has been shadowed)")
    | SOME value => value
  end;

structure NameMangler = NameManglerFun (
  type ctxt = string list;
  type src = string;
  val ord = string_ord;
  fun mk reserved_ml (name, i) =
    (Symbol.alphanum o NameSpace.base) name ^ replicate_string i "'";
  fun is_valid (reserved_ml : string list) = not o member (op =) reserved_ml;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("No such definition name: " ^ quote dst);
);

fun mk_flat_ml_resolver names =
  let
    val mangler =
      NameMangler.empty
      |> fold_map (NameMangler.declare (ThmDatabase.ml_reserved @ reserved_ml')) names
      |-> (fn _ => I)
  in NameMangler.get (ThmDatabase.ml_reserved @ reserved_ml') mangler end;

end; (* local *)


(** haskell serializer **)

local

fun hs_from_defs init_ctxt (class_syntax, tyco_syntax, const_syntax)
    resolver prefix defs =
  let
    val is_cons = CodegenNames.has_nsp CodegenNames.nsp_dtco;
    val resolv = resolver "";
    val resolv_here = resolver prefix;
    fun hs_from_class cls = case class_syntax cls
     of NONE => resolv cls
      | SOME (cls, _) => cls;
    fun hs_from_classop_name cls clsop = case class_syntax cls
     of NONE => NameSpace.base clsop
      | SOME (_, classop_syntax) => case classop_syntax clsop
         of NONE => NameSpace.base clsop
          | SOME clsop => clsop;
    fun hs_from_typparms tyvar_ctxt vs =
      let
        fun from_typparms [] = str ""
          | from_typparms vs =
              vs
              |> map (fn (v, cls) => str
                  (hs_from_class cls ^ " " ^ lookup_ctxt tyvar_ctxt v))
              |> Pretty.enum "," "(" ")"
              |> (fn p => Pretty.block [p, str " => "])
      in
        vs
        |> maps (fn (v, sort) => map (pair v) sort)
        |> from_typparms
      end;
    fun hs_from_tycoexpr tyvar_ctxt fxy (tyco, tys) =
      brackify fxy (str tyco :: map (hs_from_type tyvar_ctxt BR) tys)
    and hs_from_type tyvar_ctxt fxy (tycoexpr as tyco `%% tys) =
          (case tyco_syntax tyco
           of NONE =>
                hs_from_tycoexpr tyvar_ctxt fxy (resolv tyco, tys)
            | SOME (i, pr) =>
                if not (i = length tys)
                then error ("Number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " expected")
                else pr fxy (hs_from_type tyvar_ctxt) tys)
      | hs_from_type tyvar_ctxt fxy (t1 `-> t2) =
          brackify_infix (1, R) fxy [
            hs_from_type tyvar_ctxt (INFX (1, X)) t1,
            str "->",
            hs_from_type tyvar_ctxt (INFX (1, R)) t2
          ]
      | hs_from_type tyvar_ctxt fxy (ITyVar v) =
          str (lookup_ctxt tyvar_ctxt v);
    fun hs_from_typparms_tycoexpr tyvar_ctxt (vs, tycoexpr) =
      Pretty.block [hs_from_typparms tyvar_ctxt vs, hs_from_tycoexpr tyvar_ctxt NOBR tycoexpr]
    fun hs_from_typparms_type tyvar_ctxt (vs, ty) =
      Pretty.block [hs_from_typparms tyvar_ctxt vs, hs_from_type tyvar_ctxt NOBR ty]
    fun hs_from_expr var_ctxt fxy (e as IConst x) =
          hs_from_app var_ctxt fxy (x, [])
      | hs_from_expr var_ctxt fxy (e as (e1 `$ e2)) =
          (case CodegenThingol.unfold_const_app e
           of SOME x => hs_from_app var_ctxt fxy x
            | _ =>
                brackify fxy [
                  hs_from_expr var_ctxt NOBR e1,
                  hs_from_expr var_ctxt BR e2
                ])
      | hs_from_expr var_ctxt fxy (IVar v) =
          str (lookup_ctxt var_ctxt v)
      | hs_from_expr var_ctxt fxy (e as _ `|-> _) =
          let
            val (es, e) = CodegenThingol.unfold_abs e;
            val vs = fold CodegenThingol.add_varnames (map fst es) [];
            val var_ctxt' = intro_ctxt vs var_ctxt;
          in
            brackify BR (
              str "\\"
              :: map (hs_from_expr var_ctxt' BR o fst) es @ [
              str "->",
              hs_from_expr var_ctxt' NOBR e
            ])
          end
      | hs_from_expr var_ctxt fxy (INum (n, _)) =
          if n > 0 then
            (str o IntInf.toString) n
          else
            brackify BR [(str o Library.prefix "-" o IntInf.toString o IntInf.~) n]
      | hs_from_expr var_ctxt fxy (IChar (c, _)) =
          (str o enclose "'" "'")
            (let val i = (Char.ord o the o Char.fromString) c
              in if i < 32
                then Library.prefix "\\" (string_of_int i)
                else c
              end)
      | hs_from_expr var_ctxt fxy (e as ICase ((_, [_]), _)) =
          let
            val (ps, body) = CodegenThingol.unfold_let e;
            fun mk_bind ((p, _), e) var_ctxt =
              let
                val vs = CodegenThingol.add_varnames p [];
                val var_ctxt' = intro_ctxt vs var_ctxt;
              in
                ((Pretty.block o Pretty.breaks) [
                  hs_from_expr var_ctxt' BR p,
                  str "=",
                  hs_from_expr var_ctxt NOBR e
                ], var_ctxt')
              end;
            val (binds, var_ctxt') = fold_map mk_bind ps var_ctxt;
          in Pretty.chunks [
            [str ("let"), Pretty.fbrk, binds |> Pretty.chunks] |> Pretty.block,
            [str ("in "), hs_from_expr var_ctxt' NOBR body] |> Pretty.block
          ] end
      | hs_from_expr var_ctxt fxy (ICase (((de, _), bses), _)) =
          let
            fun mk_clause (se, be) =
              let
                val vs = CodegenThingol.add_varnames se [];
                val var_ctxt' = intro_ctxt vs var_ctxt;
              in
                (Pretty.block o Pretty.breaks) [
                  hs_from_expr var_ctxt' NOBR se,
                  str "->",
                  hs_from_expr var_ctxt' NOBR be
                ]
              end
          in Pretty.enclose "(" ")" [
            str "case",
            Pretty.brk 1,
            hs_from_expr var_ctxt NOBR de,
            Pretty.brk 1,
            str "of",
            Pretty.fbrk,
            (Pretty.chunks o map mk_clause) bses
          ] end
    and hs_mk_app var_ctxt c es =
      (str o resolv) c :: map (hs_from_expr var_ctxt BR) es
    and hs_from_app var_ctxt fxy =
      from_app (hs_mk_app var_ctxt) (hs_from_expr var_ctxt) const_syntax fxy
    fun hs_from_def (name, CodegenThingol.Fun (def as (eqs, (vs, ty)))) =
          let
            fun from_eq (args, rhs) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o resolv) c) (fold CodegenThingol.add_constnames (rhs :: args) []);
                val vars = fold CodegenThingol.add_unbound_varnames (rhs :: args) [];
                val var_ctxt = init_ctxt
                  |> intro_ctxt consts
                  |> intro_ctxt vars;
              in
                (Pretty.block o Pretty.breaks) (
                  (str o resolv_here) name
                  :: map (hs_from_expr var_ctxt BR) args
                  @ [str "=", hs_from_expr var_ctxt NOBR rhs]
                )
              end;
            val tyvar_ctxt = intro_ctxt (map fst vs) init_ctxt;
          in
            Pretty.chunks (
              Pretty.block [
                (str o suffix " ::" o resolv_here) name,
                Pretty.brk 1,
                hs_from_typparms_type tyvar_ctxt (vs, ty)
              ]
              :: (map from_eq o fst o snd o constructive_fun) (name, def)
            ) |> SOME
          end
      | hs_from_def (name, CodegenThingol.Typesyn (vs, ty)) =
          let
            val tyvar_ctxt = intro_ctxt (map fst vs) init_ctxt;
          in
            (Pretty.block o Pretty.breaks) [
              str "type",
              hs_from_typparms_tycoexpr tyvar_ctxt (vs, (resolv_here name, map (ITyVar o fst) vs)),
              str "=",
              hs_from_typparms_type tyvar_ctxt ([], ty)
            ] |> SOME
          end
      | hs_from_def (name, CodegenThingol.Datatype (vs, [(co, [ty])])) =
          let
            val tyvar_ctxt = intro_ctxt (map fst vs) init_ctxt;
          in
            (Pretty.block o Pretty.breaks) [
              str "newtype",
              hs_from_typparms_tycoexpr tyvar_ctxt (vs, (resolv_here name, map (ITyVar o fst) vs)),
              str "=",
              (str o resolv_here) co,
              hs_from_type tyvar_ctxt BR ty
            ] |> SOME
          end
      | hs_from_def (name, CodegenThingol.Datatype (vs, constr :: constrs)) =
          let
            val tyvar_ctxt = intro_ctxt (map fst vs) init_ctxt;
            fun mk_cons (co, tys) =
              (Pretty.block o Pretty.breaks) (
                (str o resolv_here) co
                :: map (hs_from_type tyvar_ctxt BR) tys
              )
          in
            (Pretty.block o Pretty.breaks) (
              str "data"
              :: hs_from_typparms_tycoexpr tyvar_ctxt (vs, (resolv_here name, map (ITyVar o fst) vs))
              :: str "="
              :: mk_cons constr
              :: map ((fn p => Pretty.block [str "| ", p]) o mk_cons) constrs
            )
          end |> SOME
      | hs_from_def (_, CodegenThingol.Datatypecons _) =
          NONE
      | hs_from_def (name, CodegenThingol.Class (supclasss, (v, membrs))) =
          let
            val tyvar_ctxt = intro_ctxt [v] init_ctxt;
            fun mk_member (m, ty) =
              Pretty.block [
                str (resolv_here m ^ " ::"),
                Pretty.brk 1,
                hs_from_type tyvar_ctxt NOBR ty
              ]
          in
            Pretty.block [
              str "class ",
              hs_from_typparms tyvar_ctxt [(v, supclasss)],
              str (resolv_here name ^ " " ^ v),
              str " where",
              Pretty.fbrk,
              Pretty.chunks (map mk_member membrs)
            ] |> SOME
          end
      | hs_from_def (_, CodegenThingol.Classmember _) =
          NONE
      | hs_from_def (_, CodegenThingol.Classinst ((clsname, (tyco, vs)), (_, memdefs))) =
          let
            val tyvar_ctxt = intro_ctxt (map fst vs) init_ctxt;
          in
            Pretty.block [
              str "instance ",
              hs_from_typparms tyvar_ctxt vs,
              str (hs_from_class clsname ^ " "),
              hs_from_type tyvar_ctxt BR (tyco `%% map (ITyVar o fst) vs),
              str " where",
              Pretty.fbrk,
              Pretty.chunks (map (fn (m, e) =>
                let
                  val consts = map_filter
                    (fn c => if (is_some o const_syntax) c
                      then NONE else (SOME o NameSpace.base o resolv) c) (CodegenThingol.add_constnames e []);
                  val var_ctxt = init_ctxt
                    |> intro_ctxt consts;
                in
                  (Pretty.block o Pretty.breaks) [
                    (str o hs_from_classop_name clsname) m,
                    str "=",
                    hs_from_expr var_ctxt NOBR e
                  ]
                end
              ) memdefs)
            ] |> SOME
          end
  in
    case map_filter (fn (name, def) => hs_from_def (name, def)) defs
     of [] => NONE
      | l => (SOME o Pretty.chunks o separate (str "")) l
  end;

in

fun hs_from_thingol target =
  let
    val reserved_hs = [
      "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
      "import", "default", "forall", "let", "in", "class", "qualified", "data",
      "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
    ] @ [
      "Bool", "Integer", "Maybe", "True", "False", "Nothing", "Just", "not", "negate",
      "String", "Char"
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
      in if member (op =) [nsp_module, nsp_class, nsp_tyco, nsp_dtco] shallow
        then ch_first Char.toUpper n
        else ch_first Char.toLower n
      end;
    val serializer = abstract_serializer (target, [[nsp_module],
      [nsp_class], [nsp_tyco], [nsp_fun, nsp_classop], [nsp_dtco], [nsp_inst]])
      "Main" (hs_from_defs (make_ctxt reserved_hs), hs_from_module, abstract_validator reserved_hs, postproc);
  in
    parse_multi_file ((K o K) NONE) "hs" serializer
  end;

end; (* local *)



(** lookup table **)

val serializers =
  Symtab.empty
  |> fold (fn (name, f) => Symtab.update_new (name, f name))
       [("SML", ml_from_thingol), ("Haskell", hs_from_thingol)];

fun check_serializer target =
  case Symtab.lookup serializers target
   of SOME seri => ()
    | NONE => error ("Unknown code target language: " ^ quote target);

fun parse_serializer target =
  case Symtab.lookup serializers target
   of SOME seri => seri >> (fn seri' => fn thy => serialize thy seri' target)
    | NONE => Scan.fail_with (fn _ => "Unknown code target language: " ^ quote target) ();

fun map_target_data target f =
  let
    val _ = check_serializer target;
  in
    CodegenSerializerData.map (
      (Symtab.map_entry target (fn { syntax_class, syntax_inst, syntax_tyco, syntax_const } =>
          let
            val (syntax_class, syntax_inst, syntax_tyco, syntax_const) =
              f (syntax_class, syntax_inst, syntax_tyco, syntax_const)
          in {
            syntax_class = syntax_class,
            syntax_inst = syntax_inst,
            syntax_tyco = syntax_tyco,
            syntax_const = syntax_const } : target_data
          end
      ))
    )
  end;


(** target syntax interfaces **)

local

fun gen_add_syntax_class prep_class prep_const target raw_class (syntax, raw_ops) thy =
  let
    val cls = prep_class thy raw_class
    val class = CodegenNames.class thy cls;
    fun mk_classop (c, _) = case AxClass.class_of_param thy c
     of SOME class' => if cls = class' then c
          else error ("Not a class operation for class " ^ quote class ^ ": " ^ quote c)
      | NONE => error ("Not a class operation: " ^ quote c)
    val ops = (map o apfst) (mk_classop o prep_const thy) raw_ops;
    val syntax_ops = AList.lookup (op =) ops;
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
        (syntax_class |> Symtab.update (class,
          ((syntax, syntax_ops), stamp ())),
            syntax_inst, syntax_tyco, syntax_const))
  end;

fun gen_add_syntax_inst prep_class prep_tyco target (raw_tyco, raw_class) thy =
  let
    val inst = CodegenNames.instance thy (prep_class thy raw_class, prep_tyco thy raw_tyco);
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
        (syntax_class, syntax_inst |> Symtab.update (inst, ()),
          syntax_tyco, syntax_const))
  end;

fun gen_add_syntax_tyco prep_tyco raw_tyco target syntax thy =
  let
    val tyco = (CodegenNames.tyco thy o prep_tyco thy) raw_tyco;
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
         (syntax_class, syntax_inst, syntax_tyco
            |> Symtab.update (tyco, (syntax, stamp ())), syntax_const))
  end;

fun gen_add_syntax_const prep_const raw_c target syntax thy =
  let
    val c' = prep_const thy raw_c;
    val c'' = CodegenNames.const thy c';
  in
    thy
    |> map_target_data target (fn (syntax_class, syntax_inst, syntax_tyco, syntax_const) =>
         (syntax_class, syntax_inst, syntax_tyco, syntax_const
            |> Symtab.update (c'', (syntax, stamp ()))))
  end;

fun read_type thy raw_tyco =
  let
    val tyco = Sign.intern_type thy raw_tyco;
    val _ = if Sign.declared_tyname thy tyco then ()
      else error ("No such type constructor: " ^ quote raw_tyco);
  in tyco end;

fun idfs_of_const_names thy cs =
  let
    val cs' = AList.make (fn c => Sign.the_const_type thy c) cs;
    val cs'' = map (CodegenConsts.norm_of_typ thy) cs';
  in AList.make (CodegenNames.const thy) cs'' end;

fun read_quote reader consts_of target get_init gen raw_it thy =
  let
    val it = reader thy raw_it;
    val cs = consts_of thy it;
  in
    gen thy cs target (get_init thy) [it]
    |> (fn [it'] => (it', thy))
  end;

fun parse_quote num_of reader consts_of target get_init gen adder =
  parse_syntax num_of
    (read_quote reader consts_of target get_init gen)
  #-> (fn modifier => pair (modifier #-> adder target));

in

val add_syntax_class = gen_add_syntax_class ClassPackage.read_class CodegenConsts.read_const;
val add_syntax_inst = gen_add_syntax_inst ClassPackage.read_class read_type;

fun parse_syntax_tyco generate target raw_tyco  =
  let
    fun intern thy = read_type thy raw_tyco;
    fun num_of thy = Sign.arity_number thy (intern thy);
    fun idf_of thy = CodegenNames.tyco thy (intern thy);
    fun read_typ thy =
      Sign.read_typ (thy, K NONE);
  in
    parse_quote num_of read_typ ((K o K) ([], [])) target idf_of generate
      (gen_add_syntax_tyco read_type raw_tyco)
  end;

fun parse_syntax_const generate target raw_const =
  let
    fun intern thy = CodegenConsts.read_const thy raw_const;
    fun num_of thy = (length o fst o strip_type o Sign.the_const_type thy o fst o intern) thy;
    fun idf_of thy = (CodegenNames.const thy o intern) thy;
  in
    parse_quote num_of Sign.read_term CodegenConsts.consts_of target idf_of generate
      (gen_add_syntax_const CodegenConsts.read_const raw_const)
  end;

fun add_pretty_list target nill cons mk_list mk_char_string target_cons thy =
  let
    val [(_, nil''), (cons', cons'')] = idfs_of_const_names thy [nill, cons];
    val pr = pretty_list nil'' cons'' mk_list mk_char_string target_cons;
  in
    thy
    |> gen_add_syntax_const (K I) cons' target pr
  end;

fun add_pretty_ml_string target nill cons str mk_char mk_string target_implode thy =
  let
    val [(_, nil''), (_, cons''), (str', _)] = idfs_of_const_names thy [nill, cons, str];
    val pr = pretty_ml_string nil'' cons'' mk_char mk_string target_implode;
  in
    thy
    |> gen_add_syntax_const (K I) str' target pr
  end;

fun add_undefined target undef target_undefined thy =
  let
    val [(undef', _)] = idfs_of_const_names thy [undef];
    fun pretty _ _ _ = str target_undefined;
  in
    thy
    |> gen_add_syntax_const (K I) undef' target (~1, pretty)
  end;

end; (*local*)

end; (* struct *)
